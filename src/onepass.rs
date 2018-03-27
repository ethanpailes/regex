/*!
A one-pass regex tells us that there are no non-deterministic branches
in the regex which means that the "NFA" really is a DFA. This provides
a few nice properties that we can leverage.

    1. The potential exponential blowup from converting an NFA to a DFA
       via the subset construction goes away. The exponential blowup
       comes from compound states, which are a result of non-determinism.
       This means that we don't need to muck about with dynamic DFA
       construction an caching.
    2. There are no compound states so, we can implement captures with
       a DFA. The reason that a general DFA can't handle captures is
       that you don't know what to do when the DFA reaches a compound
       state which includes one capturing state, but also other states.
       This means that the DFA is potentially in either a capturing
       NFA state or some other NFA state. For a one-pass regex there
       will never be a compound state for the DFA, so captures can
       be implemented right in the DFA.
*/

use std::fmt;
use analisys;
use syntax::hir::Hir;
use prog::{Program, Inst};
use re_trait::Slot;

// flip to true for debugging
const TRACE: bool = true;
macro_rules! trace {
    ($($tts:tt)*) => {
        if TRACE {
            println!($($tts)*);
        }
    }
}

/// A OnePass DFA.
#[derive(Debug)]
pub struct OnePass {
    /// The table.
    table: Vec<StatePtr>,
    /// The stride.
    num_byte_classes: usize,
    /// The byte classes of this regex.
    byte_classes: Vec<u8>,
    /// The starting state.
    start_state: StatePtr,
    /// True if the regex is anchored at the end.
    is_anchored_end: bool,
    /// True if the regex is anchored at the start.
    is_anchored_start: bool,
}

impl fmt::Display for OnePass {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        try!(writeln!(f, "START: {}\n", st_str(self.start_state)));

        for i in 0..(self.table.len() / self.num_byte_classes) {
            let addr = format!("{:x}", i * self.num_byte_classes);
            let trans_start = i * self.num_byte_classes;
            let trans_end = (i+1) * self.num_byte_classes;
            let trans = &self.table[trans_start..trans_end];
            try!(Self::fmt_line(addr, trans, f));
        }

        Ok(())
    }
}

impl OnePass {

    /// Execute the one-pass DFA, populating the list of capture slots
    /// as you go.
    ///
    /// TODO: ask @burntsushi about doing the right thing WRT regexsets
    ///       here.
    pub fn exec(&self, slots: &mut [Slot], text: &[u8], mut at: usize) -> bool {
        trace!("execing on '{:?}'\n{}", text, self);

        if self.is_anchored_start {
            match self.exec_(slots, text, at) {
                OnePassMatch::Match => true,
                OnePassMatch::NoMatch(_) => false,
            }
        } else {
            loop {
                match self.exec_(slots, text, at) {
                    OnePassMatch::Match => return true,
                    OnePassMatch::NoMatch(last) => {
                        // TODO: this will probably dominate the runtime
                        //       cost. I need a [^fset]* prefix machine
                        //       to make this a bit more bearable.
                        for s in slots.iter_mut() {
                            *s = None;
                        }
                        at = last + 1;
                    }
                }

                if at >= text.len() {
                    break;
                }
            }

            false
        }
    }


    /// Execute the one-pass DFA, populating the list of capture slots
    /// as you go.
    ///
    /// Returns Match if there is a match and NoMatch(final string pointer)
    /// otherwise.
    ///
    /// TODO: ask @burntsushi about doing the right thing WRT regexsets
    ///       here.
    #[inline]
    fn exec_(
        &self,
        slots: &mut [Slot],
        text: &[u8],
        mut at: usize
    ) -> OnePassMatch {

        let mut state_ptr = self.start_state;
        while at < text.len() {
            debug_assert!(state_ptr != STATE_POISON);
            let byte_class = self.byte_classes[text[at] as usize] as usize;
            trace!("::exec loop st={} at={} bc={}",
                        st_str(state_ptr), at, byte_class);

            if state_ptr & STATE_SPECIAL == 0 {
                state_ptr = self.table[state_ptr as usize + byte_class];
            } else if state_ptr == STATE_DEAD {
                return OnePassMatch::NoMatch(at);
            } else if state_ptr == STATE_MATCH {
                if self.is_anchored_end {
                    return OnePassMatch::Match;
                }
            } else {
                while state_ptr & STATE_SAVE != 0 {
                    // No state should ever have both the SAVE and MATCH
                    // flags set.
                    debug_assert!(state_ptr & STATE_MATCH == 0);

                    let state_idx = (state_ptr & STATE_MAX) as usize;

                    // the second save entry is filled with the save slots
                    // that we need to fill.
                    let slot_idx = self.table[state_idx + self.num_byte_classes];
                    slots[slot_idx as usize] = Some(at);

                    state_ptr = self.table[state_idx + byte_class];
                }
            }

            at += 1;
        }

        // set the byte class to be EOF
        let byte_class = self.num_byte_classes - 1;
        trace!("::exec eof st={} bc={}", st_str(state_ptr), byte_class);
        if state_ptr & STATE_SPECIAL == 0 {
            state_ptr = self.table[state_ptr as usize + byte_class];
        } else {
            while state_ptr & STATE_SAVE != 0 {
                trace!("::exec eof save");
                // No state should ever have both the SAVE and MATCH
                // flags set.
                debug_assert!(state_ptr & STATE_MATCH == 0);

                let state_idx = (state_ptr & STATE_MAX) as usize;

                // the second save entry is filled with the save slots
                // that we need to fill.
                let slot_idx = self.table[state_idx + self.num_byte_classes];
                slots[slot_idx as usize] = Some(at);

                state_ptr = self.table[state_idx + byte_class];
            }
        }

        if state_ptr == STATE_MATCH {
            OnePassMatch::Match
        } else {
            OnePassMatch::NoMatch(at)
        }
    }

    fn fmt_line(
        addr: String,
        trans: &[StatePtr],
        f: &mut fmt::Formatter,
    ) -> Result<(), fmt::Error> {
        try!(writeln!(f, "{}: {}", addr,
                trans.iter().enumerate()
                     .map(|(i, x)| format!("{}/{}", i, st_str(*x)))
                     .collect::<Vec<String>>()
                     .join(" | ")));
        Ok(())
    }
}

enum OnePassMatch {
    Match,
    NoMatch(usize),
}

/// Compiler for a OnePass DFA
pub struct OnePassCompiler<'r> {
    onepass: OnePass,
    // hir: &'r Hir,
    prog: &'r Program,
}

impl<'r> OnePassCompiler<'r> {
    /// Create a new OnePassCompiler for a given Hir.
    /// Collect some metadata from the compiled program.
    pub fn new(hirs: &[Hir], prog: &'r Program) -> Result<Self, OnePassError> {
        if hirs.len() != 1 {
            return Err(OnePassError::RegexSetUnsupported);
        }

        if ! analisys::is_one_pass(&hirs[0]) {
            return Err(OnePassError::NotOnePass);
        }

        Ok(OnePassCompiler {
            onepass: OnePass {
                table: vec![],
                num_byte_classes: (prog.byte_classes[255] as usize) + 1,
                byte_classes: prog.byte_classes.clone(),
                start_state: 0,
                is_anchored_end: prog.is_anchored_end,
                is_anchored_start: prog.is_anchored_start,
            },
            prog: prog,
        })
    }

    /// Attempt to compile the regex to a OnePass DFA
    pub fn compile(mut self) -> Result<OnePass, OnePassError> {
        let p = try!(self.inst_patch(0));

        // all paths should end up pointing to a match instruction
        debug_assert!(p.holes.len() == 0);
        self.onepass.start_state = p.single_entry_point().unwrap();

        Ok(self.onepass)
    }

    // TODO: I think I need to memoise this to avoid infinite loops
    /// For now we use direct recursive style
    fn inst_patch(&mut self, inst_idx: usize) -> Result<Patch, OnePassError> {
        match &self.prog[inst_idx] {
            &Inst::Match(_) => {
                // A match has no transition table. It exists only as
                // match pointers in the transition tables of other states.
                Ok(Patch {
                    entry: EntryPoint(vec![STATE_MATCH;
                                           self.onepass.num_byte_classes]),
                    holes: vec![],
                    flags: STATE_MATCH,
                })
            }
            &Inst::Save(ref inst) => {
                let p = self.save_patch(inst.slot);
                let next_p = try!(self.inst_patch(inst.goto));

                Ok(self.forward_patch(p, next_p))
            }
            &Inst::EmptyLook(ref inst) => {
                // TODO: unimplimented for now
                self.inst_patch(inst.goto)
            }
            &Inst::Bytes(ref inst) => {
                let byte_class =
                    self.onepass.byte_classes[inst.start as usize] as usize;
                let p = self.byte_class_patch(byte_class);
                let next_p = try!(self.inst_patch(inst.goto));
                Ok(self.fuse_patch(p, next_p))
            }
            &Inst::Split(ref inst) => {
                Ok(try!(self.inst_patch(inst.goto1))
                    .or(try!(self.inst_patch(inst.goto2))))
            }
            &Inst::Char(_) | &Inst::Ranges(_) => unreachable!(),
        }
    }

    //
    // Patch Methods
    //

    fn save_patch(&mut self, slot: usize) -> Patch {
        // all of the entry points to a save patch come from its children
        let entry = vec![STATE_POISON; self.onepass.num_byte_classes];
        let addr = self.onepass.table.len();
        self.onepass.table.extend(
            vec![STATE_DEAD; self.onepass.num_byte_classes]);
        self.onepass.table.extend(
            vec![slot as StatePtr; self.onepass.num_byte_classes]);

        Patch {
            entry: EntryPoint(entry),
            holes: vec![Hole(addr)],
            flags: STATE_SAVE,
        }
    }

    fn byte_class_patch(&mut self, byte_class: usize) -> Patch {
        let addr = self.onepass.table.len();
        let mut entry = vec![STATE_POISON; self.onepass.num_byte_classes];
        entry[byte_class] = addr as StatePtr;

        self.onepass.table.extend(
            vec![STATE_DEAD; self.onepass.num_byte_classes]);

        Patch {
            entry: EntryPoint(entry),
            holes: vec![Hole(addr)],
            flags: 0,
        }
    }

    /// Fuse two patches together so that they must occur sequentially.
    fn fuse_patch(&mut self, p1: Patch, p2: Patch) -> Patch {
        for &Hole(ts_start) in p1.holes.iter() {
            let ts_end = ts_start + self.onepass.num_byte_classes;
            let ts = &mut self.onepass.table[ts_start..ts_end];

            ts.iter_mut().enumerate().for_each(|(i, t)| {
                if p2.entry.0[i] != STATE_POISON {
                    *t = p2.entry.0[i] | p2.flags;
                }
            })
        }

        Patch {
            entry: p1.entry,
            holes: p2.holes,
            flags: p1.flags,
        }
    }

    /// Just like fuse_patch, except that the EntryPoints from p2 are
    /// copied over to p1 so that anything that would enter p2 also
    /// enters the new patch
    fn forward_patch(&mut self, mut p1: Patch, p2: Patch) -> Patch {
        for (i, e) in p2.entry.0.iter().enumerate() {
            if *e != STATE_POISON {
                // TODO: this needs to be the address of p1 rather
                // than the targets for p2.
                p1.entry.0[i] = *e;
            }
        }

        self.fuse_patch(p1, p2)
    }
}


/// The beginning of a transition table that needs to be
/// patched to point to an EntryPoint.
#[derive(Eq, PartialEq)]
struct Hole(usize);

/// A mapping from byte classes to state pointers which
/// indicate compiled states.
struct EntryPoint(Vec<StatePtr>);

struct Patch {
    entry: EntryPoint,
    holes: Vec<Hole>,
    /// Flags to apply to the entry point pointers when fusing the patch
    flags: StatePtr,
}

impl Patch {
    /// Combine two patches with a branch between them.
    fn or(mut self, mut p: Patch) -> Patch {
        debug_assert!({
            let mut entries_intersect = false;
            'LOOP: for (i, e1) in self.entry.0.iter().enumerate() {
                if *e1 == STATE_DEAD {
                    continue;
                }
                for (j, e2) in p.entry.0.iter().enumerate() {
                    if *e2 == STATE_DEAD {
                        continue;
                    }
                    if i != j && *e1 == *e2 {
                        entries_intersect = true;
                        break 'LOOP;
                    }
                }
            }
            ! entries_intersect
        });

        // We have to collapse the flags onto the EntryPoints of
        // the patches now so that they can be differentiated.
        for e in self.entry.0.iter_mut() {
            *e = *e | self.flags;
        }
        self.flags = 0;
        for e in p.entry.0.iter_mut() {
            *e = *e | p.flags;
        }

        for (i, e2) in p.entry.0.iter().enumerate() {
            if *e2 == STATE_POISON {
                continue;
            }

            self.entry.0[i] = *e2;
        }
        self.holes.extend(p.holes);

        self
    }

    fn single_entry_point(&self) -> Option<StatePtr> {
        let mut ep = STATE_POISON;;
        for e in self.entry.0.iter() {
            if *e != STATE_POISON {
                if ep == STATE_POISON {
                    return None;
                } else {
                    ep = *e;
                }
            }
        }

        Some(ep | self.flags)
    }
}


#[derive(Debug)]
pub enum OnePassError {
    /// This program can't be executed as a one-pass regex.
    NotOnePass,
    /// There are too many instructions to deal with.
    TooBig,
    /// We don't yet support unicode OnePass execution.
    HasUnicode,
    /// We don't yet support regex sets.
    RegexSetUnsupported,
    /// Hints that destructuring should not be exhaustive.
    ///
    /// This enum may grow additional variants, so this makes sure clients
    /// don't count on exhaustive matching. (Otherwise, adding a new variant
    /// could break existing code.)
    #[doc(hidden)]
    __Nonexhaustive,
}


/*
/// A OnePass DFA.
#[derive(Debug)]
pub struct OnePassCompiler<'a> {
    onepass: OnePass,
    /// A table mapping instruction indicies to compiled state
    /// pointers.
    ///
    /// If a state has not yet been compiled,
    /// then compiled[inst_idx] == STATE_POISON
    compiled: Vec<StatePtr>,
    /// A mapping from yet-to-be-compiled instruction indicies
    /// to indicies into the transition table that want to point
    /// to them.
    holes: HashMap<usize, Vec<usize>>,
    /// A mapping from yet-to-be-compiled instruction indicies
    /// to state transition tables that need to be forwarded to
    /// the given save state.
    ///
    /// The logic for filling in a save hole is slightly different
    /// from the logic for filling in a standard hole, which is
    /// why they are kept in different tables.
    save_holes: HashMap<usize, Vec<usize>>,
    needs_save_patch: HashSet<usize>,
    /// A table mapping holes (both standard and save) to their contain states.
    hole_states: Vec<usize>,
    /// The program to be compiled.
    prog: &'a Program,
}

impl<'a> OnePassCompiler<'a> {
    /// Create a new OnePassCompiler to compile the given program
    pub fn new(prog: &'a Program) -> Self {
        OnePassCompiler {
            onepass: OnePass {
                table: vec![],
                num_byte_classes: (prog.byte_classes[255] as usize) + 1,
                byte_classes: prog.byte_classes.clone(),
                start_state: 0,
                is_anchored_end: prog.is_anchored_end,
                is_anchored_start: prog.is_anchored_start,
            },
            compiled: vec![STATE_POISON; prog.len()],
            holes: HashMap::new(),
            save_holes: HashMap::new(),
            needs_save_patch: HashSet::new(),
            hole_states: Vec::with_capacity(prog.len()),
            prog: prog,
        }
    }

    // TODO: what is with that trailing dead state??? It doesn't seem to
    // impact correctness.
    //
    // I think I need to put a leading /[^fset]* / if we are not anchored
    // at the start
    //
    /// Attempt to compile a regex into a one-pass DFA
    pub fn compile(mut self) -> Result<OnePass, OnePassError> {
        trace!("OnePassCompiler::compile\n{:?}", self.prog);
        try!(Self::check_can_exec(self.prog));
        // OnePassCompilers are single use
        debug_assert!(self.holes.len() == 0);
        debug_assert!(self.save_holes.len() == 0);

        // start the ball rolling
        self.emit_transitions(0);
        self.onepass.start_state = self.compiled[0];

        while self.holes.len() > 0 || self.save_holes.len() > 0 {
            trace!("::compile loop holes={:?} save_holes={:?}",
                        self.holes, self.save_holes);

            let hs = self.holes.keys().map(|x| *x).collect::<Vec<_>>();
            for k in hs.into_iter() {
                self.emit_transitions(k);
            }

            let hs = self.save_holes.keys().map(|x| *x).collect::<Vec<_>>();
            for k in hs.into_iter() {
                self.emit_transitions(k);
            }
        }
        // TODO: can there be a cyclic set of save holes?

        Ok(self.onepass)
    }

    /// Emit the transition table for the state represented by the
    /// given instruction
    fn emit_transitions(&mut self, inst_idx: usize) {
        trace!("::emit_transitions inst_idx={}", inst_idx);
        if self.compiled[inst_idx] != STATE_POISON {
            // don't double compile anything
            // TODO: assert instead?
            let p = self.compiled[inst_idx];
            self.patch_hole(inst_idx, p);
            return;
        }

        let mut p = self.onepass.table.len() as StatePtr;
        let mut transitions = vec![STATE_DEAD; self.onepass.num_byte_classes];
        self.hole_states.extend(vec![0; self.onepass.num_byte_classes]);

        let mut resume = match &self.prog[inst_idx] {
            &Inst::Match(_) => {
                trace!("::emit_transitions match state");
                p = STATE_MATCH;
                vec![] // no kids
            }
            &Inst::Save(ref inst) => {
                p |= STATE_SAVE;
                vec![inst.goto]
            }
            &Inst::EmptyLook(ref inst) => vec![inst.goto],
            &Inst::Bytes(ref inst) => vec![inst.goto],
            &Inst::Split(ref inst) => vec![inst.goto1, inst.goto2],
            &Inst::Char(_) | &Inst::Ranges(_) => unreachable!(),
        };

        while let Some(child_idx) = resume.pop() {
            match &self.prog[child_idx] {
                &Inst::Match(_) => {
                    // match instructions had better be only children
                    // in a one-pass regex
                    debug_assert!(
                        transitions.iter().all(|to| *to == STATE_DEAD));

                    for i in 0..transitions.len() {
                        self.transition_to(
                            inst_idx, &mut transitions, i, child_idx);
                    }
                    break;
                }
                &Inst::Save(_) => {
                    self.transition_to_save(
                        inst_idx, &mut transitions, p, child_idx);
                }
                &Inst::Split(ref inst) => {
                    // We flip the priority here so that higher priority
                    // saves will overwrite lower priority saves.
                    resume.push(inst.goto1);
                    resume.push(inst.goto2);
                }
                &Inst::EmptyLook(ref inst) => {
                    // TODO: emptylook
                    resume.push(inst.goto);
                }
                &Inst::Bytes(ref inst) => {
                    let byte_class =
                        self.onepass.byte_classes[inst.start as usize] as usize;
                    self.transition_to(
                        inst_idx, &mut transitions, byte_class, child_idx);
                }
                &Inst::Char(_) | &Inst::Ranges(_) => unreachable!(),
            }
        }

        self.onepass.table.extend(transitions);

        if let &Inst::Save(ref inst) = &self.prog[inst_idx] {
            self.onepass.table.extend(
                vec![inst.slot as StatePtr; self.onepass.num_byte_classes]);
            self.hole_states.extend(vec![0; self.onepass.num_byte_classes]);
        }

        self.patch_hole(inst_idx, p);
    }

    /// Patch any holes which want to point to `inst_idx` with `sp`
    /// and updates self.compiled to include the new state.
    ///
    /// patch_holes is idempotent.
    fn patch_hole(&mut self, inst_idx: usize, sp: StatePtr) {
        trace!("::patch_hole inst_idx={} sp={}",
                    inst_idx, st_str(sp));
        debug_assert!(sp != STATE_POISON);

        if self.compiled[inst_idx] != STATE_POISON {
            debug_assert!(self.compiled[inst_idx] == sp);
        } else {
            self.compiled[inst_idx] = sp;
        }

        match &self.prog[inst_idx] {
            &Inst::Save(_) => self.patch_save_hole(inst_idx, sp),
            _ => self.patch_standard_hole(inst_idx, sp),
        }
    }

    fn patch_standard_hole(&mut self, inst_idx: usize, sp: StatePtr) {
        match self.holes.remove(&inst_idx) {
            None => (),
            Some(hs) => {
                for h in hs.into_iter() {
                    self.onepass.table[h] = sp;

                    self.try_patch_defered_save_hole(h);
                }
            }
        }
    }

    fn patch_save_hole(&mut self, inst_idx: usize, sp: StatePtr) {
        trace!("::patch_save_hole inst_idx={} sp={} save_holes={:?} needs_sp={:?}",
                    inst_idx, st_str(sp), self.save_holes, self.needs_save_patch);

        let transition_idx = (sp & STATE_MAX) as usize;

        let save_contains_holes = self.needs_save_patch.contains(&transition_idx)
            || (inst_idx..(inst_idx+self.onepass.num_byte_classes)).any(|i|
                    self.holes.contains_key(&i));

        let s = Vec::from(self.transition_table_of(sp));

        if !save_contains_holes {
            match self.save_holes.remove(&inst_idx) {
                None => (),
                Some(hs) => {
                    for h in hs.into_iter() {
                        {
                            self.needs_save_patch.remove(&h);
                            let from =
                                self.transition_table_of_mut(h as StatePtr);
                            Self::forward_to_save(from, &s, sp);
                        }

                        self.try_patch_defered_save_hole(h);
                    }
                }
            }
        }
    }

    fn add_save_hole(&mut self, from_inst_idx: usize, to_transition_idx: usize) {
        self.save_holes.entry(to_transition_idx)
            .or_insert(vec![]).push(from_inst_idx);
        self.needs_save_patch.insert(from_inst_idx);
    }

    /// After we have just patched `hole`, it might have made a save
    /// hole fillable that was not previously fillable.
    ///
    fn try_patch_defered_save_hole(&mut self, hole: usize) {
        let holy_state = self.hole_states[hole];
        let holy_ptr = self.compiled[holy_state];
        trace!("::try_patch_defered_save_hole holy_state={} holy_ptr={}",
                    holy_state, st_str(holy_ptr));
        if holy_ptr != STATE_POISON
            && self.save_holes.contains_key(&holy_state) {
            self.patch_hole(holy_state, holy_ptr);
        }
    }

    /// Add an edge flowing from `from` to `to`.
    ///
    /// `transitions` is a slice into the global transition table
    /// representing the transitions for the next state to be pushed
    /// to the global table.
    ///
    /// `from` is a byte class index within `transitions`
    ///
    /// `to` is the index of the instruction which corrisponds to the
    /// target state.
    fn transition_to(
        &mut self,
        inst_idx: usize,
        transitions: &mut [StatePtr],
        from: usize,
        to: usize,
    ) {
        if self.compiled[to] != STATE_POISON {
            transitions[from] = self.compiled[to];
        } else {
            transitions[from] = STATE_POISON;
            let hole = self.onepass.table.len() + from;
            self.holes.entry(to).or_insert(vec![]).push(hole);
            self.hole_states[hole] = inst_idx;
        }
    }

    /// Add an edge from `from` to `to` where `to` is a save state.
    ///
    /// `from` is the slice of the global transition table corresponding
    /// to the state that wants to transition to the save state.
    ///
    /// `from_ptr` is the pointer that will point to `from` once `from`
    /// has been pushed to the global transition table. We need this
    /// in order to construct a save hole.
    ///
    /// `to` is the index of the save instruction that we wish to transition
    /// to.
    ///
    /// Save states are somewhat special. When a state sees a save
    /// instruction among its children, it must transition to it,
    /// but there is no obvious byte class to use for doing so.
    /// Instead, it must transition to the save state on any byte
    /// class that the save state will not die on. If the save
    /// state had already been compiled, this is easy. We just
    /// look up the transitions for the save state and copy
    /// them over. On the other hand, if the save state has
    /// yet to be compiled, we have to defer this action though
    /// the use of a save hole.
    fn transition_to_save(
        &mut self,
        inst_idx: usize,
        // the transitions to forward to the given save instruction
        from: &mut [StatePtr],
        // the pointer forward_transitions will have once it is pushed
        from_ptr: StatePtr,
        // the save instruction to forward to
        to: usize,
    ) {
        trace!("::transition_to_save from={} to={}", st_str(from_ptr), to);

        let from_idx = (from_ptr & STATE_MAX) as usize;
        debug_assert!(from_idx % self.onepass.num_byte_classes == 0);

        if self.compiled[to] != STATE_POISON {
            // We could probably avoid an allocation with split_at_mut,
            // but that seems a bit extra
            let s_ts = Vec::from(self.transition_table_of(self.compiled[to]));
            Self::forward_to_save(from, &s_ts, self.compiled[to]);
        } else {
            self.add_save_hole(from_idx, to);
            self.hole_states[from_idx] = inst_idx;
        }
    }

    /// Forward a state to a given save state.
    fn forward_to_save(
        transitions: &mut [StatePtr],
        save_transitions: &[StatePtr],
        // the pointer to the save transition table
        save_ptr: StatePtr,
    ) {
        debug_assert!(save_ptr & STATE_SAVE != 0);

        for (i, t) in transitions.iter_mut().enumerate() {
            if save_transitions[i] != STATE_DEAD {
                *t = save_ptr;
            }
        }
    }

    /// returns the subslice into the global transition table that
    /// is relevant to the given state
    fn transition_table_of(&self, st: StatePtr) -> &[StatePtr] {
        let start = (st & STATE_MAX) as usize;
        debug_assert!(start % self.onepass.num_byte_classes == 0);
        let end = start + self.onepass.num_byte_classes;
        &self.onepass.table[start..end]
    }

    /// returns the subslice into the global transition table that
    /// is relevant to the given state
    fn transition_table_of_mut(&mut self, st: StatePtr) -> &mut [StatePtr] {
        let start = (st & STATE_MAX) as usize;
        debug_assert!(start % self.onepass.num_byte_classes == 0);
        let end = start + self.onepass.num_byte_classes;
        &mut self.onepass.table[start..end]
    }

    /// Check if we can execute this program.
    ///
    /// This is basically the same check as the one for the normal DFA,
    /// except that it also makes sure that the is_one_pass flag is set.
    ///
    /// For now we don't support unicode, but adding unicode support is
    /// theoretically straightforward. We just need to generate a little
    /// mini DFA for each unicode char and splice it in to the DFA here.
    fn check_can_exec(insts: &Program) -> Result<(), OnePassError> {
        use prog::Inst::*;
        // If for some reason we manage to allocate a regex program with more
        // than i32::MAX instructions, then we can't execute the DFA because we
        // use 32 bit instruction pointer deltas for memory savings.
        // If i32::MAX is the largest positive delta,
        // then -i32::MAX == i32::MIN + 1 is the largest negative delta,
        // and we are OK to use 32 bits.
        if insts.dfa_size_limit == 0 || insts.len() > ::std::i32::MAX as usize {
            Err(OnePassError::TooBig)
        } else if ! insts.is_one_pass {
            Err(OnePassError::NotOnePass)
        } else {
            for inst in insts {
                match *inst {
                    Char(_) | Ranges(_) => return Err(OnePassError::HasUnicode),
                    EmptyLook(_) | Match(_) | Save(_) | Split(_) | Bytes(_) => {}
                }
            }
            Ok(())
        }
    }

}
*/

type StatePtr = u32;

fn st_str(st: StatePtr) -> String {
    if st == STATE_DEAD {
        "D".to_string()
    } else if st == STATE_POISON {
        "P".to_string()
    } else {
        if st & STATE_SAVE != 0 {
            format!("({:x})", st & STATE_MAX)
        } else if st & STATE_MATCH != 0 {
            "M".to_string()
        } else {
            format!("{:x}", st & STATE_MAX)
        }
    }
}

/// The CAP_SAVE state means that the DFA should save the current
/// string pointer in a capture slot indicated by the first entry
/// in its transition table.
///
/// Save instructions take up two transition table
/// entries. The first entry indicates the save slot,
/// while the second contains the actual transitions.
/// A save state does not increment the string pointer,
/// but just forwards control to the next state.
const STATE_SAVE: StatePtr = 1 << 31;

/// A dead state means that the state has been computed and it is known that
/// once it is entered, no future match can ever occur.
///
/// It is not valid to dereference STATE_DEAD.
const STATE_DEAD: StatePtr = STATE_SAVE + 1;

/// A poison state is used to fill in the transition table in places where
/// it would not make sense to have a real state pointer.
///
/// This is a valid poison value because both the SAVE and MATCH flags
/// cannot be set at the same time.
///
/// It is not valid to dereference STATE_POISON.
const STATE_POISON: StatePtr = !0;

/// A match state means that the regex has successfully matched.
///
/// It is not valid to dereference STATE_MATCH. We use a header
/// bitflag anyway to facilitate special case checking.
const STATE_MATCH: StatePtr = 1 << 30;

/// The maximum state pointer. This is useful to mask out the "valid" state
/// pointer from a state with the "start" or "match" bits set.
///
/// It doesn't make sense to use this with unknown, dead or quit state
/// pointers, since those pointers are sentinels and never have their lower
/// bits set to anything meaningful.
const STATE_MAX: StatePtr = STATE_MATCH - 1;

/// STATE_SPECIAL is a bitmask useful for checking if we are dealing
/// with a special case, or if we can keep chugging away at the inner
/// loop.
const STATE_SPECIAL: StatePtr = STATE_MATCH | STATE_SAVE;
