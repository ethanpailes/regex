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

use std::collections::HashMap;

use std::fmt;
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


#[derive(Debug)]
pub enum OnePassError {
    /// This program can't be executed as a one-pass regex.
    NotOnePass,
    /// There are too many instructions to deal with.
    TooBig,
    /// We don't yet support unicode OnePass execution.
    HasUnicode,
    /// Hints that destructuring should not be exhaustive.
    ///
    /// This enum may grow additional variants, so this makes sure clients
    /// don't count on exhaustive matching. (Otherwise, adding a new variant
    /// could break existing code.)
    #[doc(hidden)]
    __Nonexhaustive,
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
            trace!("::exec loop st={} bc={}", st_str(state_ptr), byte_class);

            if state_ptr & STATE_SPECIAL == 0 {
                state_ptr = self.table[state_ptr as usize + byte_class];
            } else if state_ptr == STATE_DEAD {
                return OnePassMatch::NoMatch(at);
            } else if state_ptr & STATE_SAVE != 0 {
                // No state should ever have both the SAVE and MATCH
                // flags set.
                debug_assert!(state_ptr & STATE_MATCH == 0);

                let state_idx = (state_ptr & STATE_MAX) as usize;

                // the second save entry is filled with the save slots
                // that we need to fill.
                let slot_idx = self.table[state_idx + self.num_byte_classes];
                slots[slot_idx as usize] = Some(at);

                state_ptr = self.table[state_idx + byte_class];
                continue;
            } else if state_ptr == STATE_MATCH {
                if self.is_anchored_end {
                    return OnePassMatch::Match;
                }
            }

            at += 1;
        }

        // set the byte class to be EOF
        let byte_class = self.num_byte_classes - 1;
        loop {
            trace!("::exec eof st={} bc={}", st_str(state_ptr), byte_class);

            if state_ptr & STATE_SPECIAL == 0 {
                state_ptr = self.table[state_ptr as usize + byte_class];
            } else if state_ptr & STATE_SAVE != 0 {
                // No state should ever have both the SAVE and MATCH
                // flags set.
                debug_assert!(state_ptr & STATE_MATCH == 0);

                let state_idx = (state_ptr & STATE_MAX) as usize;

                // the second save entry is filled with the save slots
                // that we need to fill.
                let slot_idx = self.table[state_idx + self.num_byte_classes];
                slots[slot_idx as usize] = Some(at);

                state_ptr = self.table[state_idx + byte_class];
                continue;
            }

            break;
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
            compiled: vec![STATE_POISON; prog.insts.len()],
            holes: HashMap::new(),
            save_holes: HashMap::new(),
            prog: prog,
        }
    }

    // TODO: what is with that trailing dead state??? It doesn't seem to
    // impact correctness.
    //
    // I think I need to put a leading /[^fset]*/ if we are not anchored
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
            trace!("holes={:?} save_holes={:?}", self.holes, self.save_holes);

            let hs = self.holes.keys().map(|x| *x).collect::<Vec<_>>();
            for k in hs.into_iter() {
                self.emit_transitions(k);
            }

            let hs = self.save_holes.keys().map(|x| *x).collect::<Vec<_>>();
            for k in hs.into_iter() {
                self.emit_transitions(k);
            }
        }

        Ok(self.onepass)
    }

    /// Emit the transition table for the state represented by the
    /// given instruction
    fn emit_transitions(&mut self, inst_idx: usize) {
        trace!("::emit_transitions inst_idx={}", inst_idx);
        if self.compiled[inst_idx] != STATE_POISON {
            return;
        }

        let mut p = self.onepass.table.len() as StatePtr;
        let mut transitions = vec![STATE_DEAD; self.onepass.num_byte_classes];

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
            &Inst::Split(ref inst) => vec![inst.goto2, inst.goto1],
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
                        self.transition_to(&mut transitions, i, child_idx);
                    }
                    break;
                }
                &Inst::Save(_) => {
                    self.transition_to_save(
                        &mut transitions, p, child_idx);
                }
                &Inst::Split(ref inst) => {
                    resume.push(inst.goto2);
                    resume.push(inst.goto1);
                }
                &Inst::EmptyLook(ref inst) => {
                    // TODO: emptylook
                    resume.push(inst.goto);
                }
                &Inst::Bytes(ref inst) => {
                    let byte_class =
                        self.onepass.byte_classes[inst.start as usize] as usize;
                    self.transition_to(&mut transitions, byte_class, child_idx);
                }
                &Inst::Char(_) | &Inst::Ranges(_) => unreachable!(),
            }
        }

        self.onepass.table.extend(transitions);

        if let &Inst::Save(ref inst) = &self.prog[inst_idx] {
            self.onepass.table.extend(
                vec![inst.slot as StatePtr; self.onepass.num_byte_classes]);
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

                    let holy_state = h / self.onepass.num_byte_classes;
                    trace!("h={} holy_state={}", h, holy_state);
                    let holy_ptr = self.compiled[holy_state];
                    debug_assert!(holy_ptr != STATE_POISON);
                    self.patch_hole(holy_state, holy_ptr);
                }
            }
        }
    }

    fn patch_save_hole(&mut self, inst_idx: usize, sp: StatePtr) {
        let save_idx = (sp & STATE_MAX) as usize;
        let save_contains_holes = self.save_holes.contains_key(&save_idx)
            || (save_idx..(save_idx+self.onepass.num_byte_classes)).any(|i|
                    self.holes.contains_key(&i));

        if !save_contains_holes {
            match self.save_holes.remove(&inst_idx) {
                None => (),
                Some(hs) => {
                    for h in hs.into_iter() {
                        trace!("::patch_save_hole h={}", h);
                        {
                            let s = Vec::from(self.transition_table_of(sp));
                            let from =
                                self.transition_table_of_mut(h as StatePtr);
                            Self::forward_to_save(from, &s, sp);
                        }

                        let holy_state = h / self.onepass.num_byte_classes;
                        let holy_ptr = self.compiled[holy_state];
                        trace!("holy_state={}", holy_state);
                        self.patch_hole(holy_state, holy_ptr);
                    }
                }
            }
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
        transitions: &mut [StatePtr],
        from: usize,
        to: usize,
    ) {
        if self.compiled[to] != STATE_POISON {
            transitions[from] = self.compiled[to];
        } else {
            transitions[from] = STATE_POISON;
            self.holes.entry(to).or_insert(vec![])
                      .push(self.onepass.table.len() + from);
        }
    }

    /// Add an edge from `from` to `to` where `to` is a save state.
    ///
    /// `from` is the slice of the global transition table corresponding
    /// to the state that wants to transition to the save state.
    ///
    /// `from_idx` is the index that will point to `from` once `from`
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
        // the transitions to forward to the given save instruction
        from: &mut [StatePtr],
        // the index forward_transitions will have once it is pushed
        from_idx: StatePtr,
        // the save instruction to forward to
        to: usize,
    ) {
        let from_idx = (from_idx & STATE_MAX) as usize;
        debug_assert!(from_idx % self.onepass.num_byte_classes == 0);

        if self.compiled[to] != STATE_POISON {
            // We could probably avoid an allocation with split_at_mut,
            // but that seems a bit extra
            let s_ts = Vec::from(self.transition_table_of(self.compiled[to]));
            Self::forward_to_save(from, &s_ts, self.compiled[to]);
        } else {
            self.save_holes.entry(to).or_insert(vec![]).push(from_idx);
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
                // overlaps mean it is not one-pass
                debug_assert!(*t == STATE_DEAD);

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
