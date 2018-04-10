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
use prog::{Program, Inst};
use re_trait::Slot; use std::collections::{HashMap, HashSet};

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
#[derive(Debug, Clone)]
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
        try!(writeln!(f, "is_anchored_start: {}", self.is_anchored_start));
        try!(writeln!(f, "is_anchored_end: {}", self.is_anchored_end));
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
    /// TODO(ethan): ask @burntsushi about doing the right thing WRT regexsets
    ///       here.
    pub fn exec(&self, slots: &mut [Slot], text: &[u8], mut at: usize) -> bool {
        trace!("execing on '{:?}'\n{}", text, self);

        if self.is_anchored_start {
            self.exec_(text, at, slots)
        } else {
            // We are forced to just try every starting index.
            // This is noticeably more painful than it is for a
            // standard DFA because we must clear the capture slots.
            //
            // To try to cut down on the cost of zeroing the capture
            // groups, we implement a very simple FSM that just
            // repeatedly tests to see if the very first DFA
            // state could make progress.
            loop {
                trace!("NoMatch new_at={} text.len()={}", at + 1, text.len());
                if self.exec_(text, at, slots) {
                    return true;
                }

                for s in slots.iter_mut() {
                    *s = None;
                }

                at = self.exec_prefix(text, at + 1);
                if at > text.len() {
                    return false;
                }
            }
        }
    }

    /// Given the input and a position in the input, return next
    /// position where a match will actually make one character
    /// of progress.
    fn exec_prefix(&self, text: &[u8], mut at: usize) -> usize {
        while at < text.len() {
            let byte_class = self.byte_classes[text[at] as usize] as usize;
            if self.table[byte_class] != STATE_DEAD {
                break;
            }
            at += 1;
        }

        at
    }

    /// Execute the one-pass DFA, populating the list of capture slots
    /// as you go.
    ///
    /// Returns true if there is a match and false otherwise.
    #[inline]
    fn exec_(
        &self,
        text: &[u8],
        mut at: usize,
        slots: &mut [Slot]
    ) -> bool {
        let mut state_ptr = self.start_state;
        trace!("::exec_ st={}", st_str(state_ptr));

        while at < text.len() {
            debug_assert!(state_ptr != STATE_POISON);
            let byte_class = self.byte_classes[text[at] as usize] as usize;
            trace!("::exec_ loop st={} at={} bc={} byte={}",
                        st_str(state_ptr), at, byte_class, text[at]);

            if state_ptr & STATE_SPECIAL == 0 {
                // No need to mask because no flags are set.
                state_ptr = self.table[state_ptr as usize + byte_class];
            } else if state_ptr == STATE_DEAD {
                return false;
            } else if state_ptr & STATE_SAVE != 0 {
                // No state should ever have both the SAVE and MATCH
                // flags set.
                debug_assert!(state_ptr & STATE_MATCH == 0);

                let state_idx = (state_ptr & STATE_MAX) as usize;

                // the second table entry is filled with the save slots
                // that we need to fill.
                let slot_idx = self.table[state_idx + self.num_byte_classes];
                slots[slot_idx as usize] = Some(at);

                state_ptr = self.table[state_idx + byte_class];
            } else if state_ptr == STATE_MATCH {
                return !self.is_anchored_end;
            } else {
                unreachable!();
            }

            // TODO(ethan):perf get rid of this branch
            if state_ptr & STATE_SPECIAL == 0 {
                at += 1;
            }
        }

        // set the byte class to be EOF
        let byte_class = self.num_byte_classes - 1;
        trace!("::exec eof st={} at={} bc={}", st_str(state_ptr), at, byte_class);
        if state_ptr & STATE_SPECIAL == 0 {
            state_ptr = self.table[state_ptr as usize + byte_class];
        }

        while state_ptr & STATE_SAVE != 0 {
            trace!("::exec eof save");
            debug_assert!(state_ptr & STATE_MATCH == 0);

            let state_idx = (state_ptr & STATE_MAX) as usize;
            let slot_idx = self.table[state_idx + self.num_byte_classes];
            slots[slot_idx as usize] = Some(at);

            state_ptr = self.table[state_idx + byte_class];
        }

        state_ptr == STATE_MATCH
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

/// Compiler for a OnePass DFA
pub struct OnePassCompiler<'r> {
    onepass: OnePass,
    prog: &'r Program,

    /// A mapping from instruction indicies to their transitions
    transitions: Vec<Option<TransitionTable>>,

    forwards: Forwards,
}

// A mapping from byte classes to target states annotated
// with transition priority. An intermediary representation.
struct TransitionTable(Vec<Transition>);
#[derive(Debug, Clone)]
struct Transition {
    tgt: TransitionTarget,
    priority: usize,
}
#[derive(Debug, Clone, Eq, PartialEq)]
enum TransitionTarget {
    Die,
    Match,
    Inst(usize),
    Save(usize),
}

/// A mapping from target states to lists of (source state, priority) pairs.
///
/// The directionality here is a little counter intuitive, because we
/// are trying to copy the transitions over from the targets to the
/// sources.
///
/// Use hash sets rather than arrays because I expect the mapping
/// to be sparse.
///
/// TODO(ethan):yakshaving there are more clones that I am comfortable with here.
#[derive(Debug, Clone)]
struct Forwards {
    jobs: Vec<Forward>,
    e_out: HashMap<usize, Vec<usize>>,
    e_in: HashMap<usize, Vec<usize>>,

    inst_froms: HashMap<usize, Vec<usize>>,
    inst_tos: HashMap<usize, Vec<usize>>,

    /// We really care about the root set, but it is much easier to
    /// keep track of its inverse in an online way.
    not_root_set: HashSet<usize>,
}

impl Forwards {
    pub fn new() -> Self {
        Forwards {
            jobs: vec![],
            e_out: HashMap::new(),
            e_in: HashMap::new(),

            inst_froms: HashMap::new(),
            inst_tos: HashMap::new(),

            not_root_set: HashSet::new(),
        }
    }

    pub fn forward(&mut self, from: usize, to: usize, priority: usize) {
        trace!("::forward from={} to={}", from, to);

        let fidx = self.jobs.len();
        self.jobs.push(Forward {
            from: from,
            to: to,
            priority: priority,
        });
        
        self.inst_froms.entry(from).or_insert(vec![]).push(fidx);
        self.inst_tos.entry(to).or_insert(vec![]).push(fidx);

        match self.inst_froms.get(&to) {
            Some(dependancies) => {
                trace!("dependancies = {:?}", dependancies);
                for dep in dependancies.iter() {
                    Self::edge(
                        &mut self.e_out, &mut self.e_in,
                        &mut self.not_root_set, *dep, fidx);
                }
            }
            None => {}
        }

        match self.inst_tos.get(&from) {
            Some(dependants) => {
                for dep in dependants.iter() {
                    Self::edge(
                        &mut self.e_out, &mut self.e_in,
                        &mut self.not_root_set, fidx, *dep);
                }
            }
            None => {}
        }
    }

    // An associated function to please the borrow checker. gross.
    fn edge(
        e_out: &mut HashMap<usize, Vec<usize>>,
        e_in: &mut HashMap<usize, Vec<usize>>,
        not_root_set: &mut HashSet<usize>,
        out_node: usize,
        in_node: usize
    ) {
        e_out.entry(out_node).or_insert(vec![]).push(in_node);
        e_in.entry(in_node).or_insert(vec![]).push(out_node);
        not_root_set.insert(in_node);
    }

    pub fn into_iter_topo(self) -> Topo {
        let mut root_set = vec![];
        for n in 0..self.jobs.len() {
            if ! self.not_root_set.contains(&n) {
                root_set.push(n);
            }
        }

        trace!("::into_iter_topo jobs={:?}", self.jobs);
        trace!("::into_iter_topo e_out={:?}", self.e_out);
        trace!("::into_iter_topo e_in={:?}", self.e_in);
        trace!("::into_iter_topo root_set={:?}", root_set);

        Topo {
            jobs: self.jobs,
            e_out: self.e_out,
            e_in: self.e_in,
            root_set: root_set,
        }
    }
}
#[derive(Debug, Clone)]
struct Forward {
    from: usize,
    to: usize,
    priority: usize,
}

/// An iterator that returns forwarding directives in topological order
/// using Kahn's Algorithm.
struct Topo {
    jobs: Vec<Forward>,
    e_out: HashMap<usize, Vec<usize>>,
    e_in: HashMap<usize, Vec<usize>>,
    root_set: Vec<usize>,
}

impl Iterator for Topo {
    type Item = Result<Forward, OnePassError>;
    fn next(&mut self) -> Option<Result<Forward, OnePassError>> {
        if let Some(next_job) = self.root_set.pop() {
            let tgts = self.e_out.get(&next_job).unwrap_or(&vec![]).clone();
            for tgt in tgts.iter() {
                self.rm_edge(next_job, *tgt);

                // If tgt has no incoming edges, add it to the root set.
                if ! self.e_in.get(tgt).is_some() {
                    self.root_set.push(*tgt);
                }
            }

            Some(Ok(self.jobs[next_job].clone()))
        } else {
            if self.e_out.len() != 0 || self.e_in.len() != 0 {
                Some(Err(OnePassError::ForwardingCycle))
            } else {
                None
            }
        }
    }
}

impl Topo {
    fn rm_edge(&mut self, node_out: usize, node_in: usize) {
        let mut rm = false;
        match self.e_out.get_mut(&node_out) {
            Some(tgts) => {
                let in_pos = tgts.iter().position(|t| *t == node_in);
                match in_pos {
                    Some(p) => { tgts.remove(p); },
                    None => debug_assert!(false),
                }

                if tgts.len() == 0 {
                    rm = true;
                }
            }
            None => debug_assert!(false),
        }
        if rm {
            self.e_out.remove(&node_out);
        }

        rm = false;
        match self.e_in.get_mut(&node_in) {
            Some(tgts) => {
                let out_pos = tgts.iter().position(|t| *t == node_out);
                match out_pos {
                    Some(p) => { tgts.remove(p); },
                    None => debug_assert!(false),
                }

                if tgts.len() == 0 {
                    rm = true;
                }
            }
            None => debug_assert!(false),
        }
        if rm {
            self.e_in.remove(&node_in);
        }
    }
}


impl<'r> OnePassCompiler<'r> {
    /// Create a new OnePassCompiler for a given Hir.
    /// Collect some metadata from the compiled program.
    pub fn new(prog: &'r Program) -> Result<Self, OnePassError> {
        if ! prog.is_one_pass {
            return Err(OnePassError::NotOnePass);
        }

        trace!("new compiler for:\n{:?}", prog);
        for inst in prog {
            match inst {
                &Inst::Char(_) | &Inst::Ranges(_) =>
                    return Err(OnePassError::HasUnicode),
                _ => (),
            }
        }

        Ok(OnePassCompiler {
            onepass: OnePass {
                table: vec![],
                num_byte_classes: (prog.byte_classes[255] as usize) + 2,
                byte_classes: prog.byte_classes.clone(),
                start_state: 0,
                is_anchored_end: prog.is_anchored_end,
                is_anchored_start: prog.is_anchored_start,
            },
            prog: prog,
            transitions: {
                let mut x = Vec::new();
                for _ in 0..prog.len() {
                    x.push(None);
                }
                x
            },
            forwards: Forwards::new(),
        })
    }

    /// Attempt to compile the regex to a OnePass DFA
    pub fn compile(mut self) -> Result<OnePass, OnePassError> {
        // Compute the prioritized transition tables for all of the
        // instructions which get states.
        let mut state_edge = vec![0];
        while let Some(i) = state_edge.pop() {
            state_edge.extend(try!(self.inst_trans(i)));
        }

        // Solve the dependency relationships between all the
        // forwarding directives that were emitted by inst_trans.
        try!(self.solve_forwards());

        // Now emit the transitions in a form that we can actually
        // execute.
        self.emit_transitions();
        self.onepass.start_state = 0 | STATE_SAVE;

        Ok(self.onepass)
    }

    fn inst_trans(
        &mut self,
        inst_idx: usize
    ) -> Result<Vec<usize>, OnePassError> {
        trace!("::inst_trans inst_idx={}", inst_idx);

        if self.transitions[inst_idx].is_some() {
            return Ok(vec![]);
        }

        // Iterate over the children, visiting lower priority
        // children first.
        let mut resume = match &self.prog[inst_idx] {
            &Inst::Save(ref inst) => vec![inst.goto],
            &Inst::EmptyLook(ref inst) => vec![inst.goto],
            &Inst::Bytes(ref inst) => vec![inst.goto],
            &Inst::Split(ref inst) => vec![inst.goto1, inst.goto2],
            &Inst::Match(_) => return Ok(vec![]), // no kids
            &Inst::Ranges(_) | &Inst::Char(_) => unreachable!(),
        };

        let mut trans = TransitionTable(
            vec![Transition { tgt: TransitionTarget::Die, priority: 0 };
                 self.onepass.num_byte_classes]);

        // Start at 1 priority because everything is higher priority than
        // the initial list of `TransitionTarget::Die` pointers.
        let mut priority = 1;

        let mut children = vec![];
        while let Some(child_idx) = resume.pop() {
            match &self.prog[child_idx] {
                &Inst::Save(_) => {
                    self.forward(inst_idx, child_idx, priority);
                    children.push(child_idx);
                }
                &Inst::EmptyLook(ref inst) => {
                    // TODO: impl
                    resume.push(inst.goto);
                }
                &Inst::Bytes(ref inst) => {
                    for byte in inst.start..(inst.end + 1) {
                        let bc = self.onepass.byte_classes[byte as usize];
                        trans.0[bc as usize] = Transition {
                            tgt: TransitionTarget::Inst(child_idx),
                            priority: priority
                        };
                    }
                    children.push(child_idx);
                }
                &Inst::Split(ref inst) => {
                    resume.push(inst.goto1);
                    resume.push(inst.goto2);
                }
                &Inst::Match(_) => {
                    for t in trans.0.iter_mut() {
                        *t = Transition {
                            tgt: TransitionTarget::Match,
                            priority: priority
                        };
                    }
                }
                &Inst::Ranges(_) | &Inst::Char(_) => unreachable!(),
            }
            priority += 1;
        }

        self.transitions[inst_idx] = Some(trans);

        Ok(children)
    }

    fn forward(&mut self, from: usize, to: usize, priority: usize) {
        self.forwards.forward(from, to, priority);
    }

    fn solve_forwards(&mut self) -> Result<(), OnePassError> {
        // TODO(ethan):yakshaving drop the clone
        for fwd in self.forwards.clone().into_iter_topo() {
            let fwd = try!(fwd);
            debug_assert!(fwd.from != fwd.to);

            let tgt = match &self.prog[fwd.to] {
                &Inst::Save(_) => TransitionTarget::Save(fwd.to),
                _ => TransitionTarget::Inst(fwd.to),
            };

            let (from_ts, to_ts) = if fwd.from < fwd.to {
                let (stub, tail) = self.transitions.split_at_mut(fwd.to);
                (&mut stub[fwd.from], &mut tail[0])
            } else {
                let (stub, tail) = self.transitions.split_at_mut(fwd.from);
                (&mut tail[0], &mut stub[fwd.to])
            };

            let (from_ts, to_ts) = match (from_ts, to_ts) {
                (&mut Some(ref mut from_ts), &mut Some(ref to_ts)) => {
                    (from_ts, to_ts)
                }
                _ => unreachable!("forwards must be between real nodes."),
            };

            // now shuffle the transitions from `to` to `from`.
            for (to_t, from_t) in to_ts.0.iter().zip(from_ts.0.iter_mut()) {
                if to_t.tgt == TransitionTarget::Die {
                    continue;
                }
                if from_t.priority > fwd.priority {
                    continue;
                }

                // we should never encounter equal priorities
                debug_assert!(from_t.priority != fwd.priority);

                *from_t = Transition {
                    tgt: tgt.clone(),
                    priority: fwd.priority,
                };
            }
        }

        Ok(())
    }

    fn emit_transitions(&mut self) {
        let mut state_starts = Vec::with_capacity(self.prog.len());
        let mut off = 0;
        for inst_idx in 0..self.prog.len() {
            state_starts.push(off);
            if self.transitions[inst_idx].is_some() {
                off += self.onepass.num_byte_classes;

                match &self.prog[inst_idx] {
                    &Inst::Save(_) => {
                        off += self.onepass.num_byte_classes;
                    }
                    _ => {}
                }
            }
        }

        for inst_idx in 0..self.prog.len() {
            let mut trans = vec![];
            match &self.transitions[inst_idx] {
                &None => continue,
                &Some(ref ttab) => {
                    for t in ttab.0.iter() {
                        trans.push(match t.tgt {
                            TransitionTarget::Match => STATE_MATCH,
                            TransitionTarget::Die => STATE_DEAD,
                            TransitionTarget::Inst(i) =>
                                state_starts[i] as StatePtr,
                            TransitionTarget::Save(i) =>
                                (state_starts[i] as StatePtr) | STATE_SAVE,
                        });
                    }
                }
            }

            self.onepass.table.extend(trans);

            // emit save annotations if the instruction is a save instruction
            match &self.prog[inst_idx] {
                &Inst::Save(ref inst) =>
                    self.onepass.table.extend(
                        vec![inst.slot as StatePtr;
                             self.onepass.num_byte_classes]),
                _ => {}
            }
        }
    }
}

#[derive(Debug)]
pub enum OnePassError {
    /// This program can't be executed as a one-pass regex.
    NotOnePass,
    /// This program contains a cycle of instructions that consume
    /// no input. Right now we can't handle that, but this restriction
    /// may be lifted in the future.
    ForwardingCycle,
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

/// A match state means that the regex has successfully matched.
///
/// It is not valid to dereference STATE_MATCH. We use a header
/// bitflag anyway to facilitate special case checking.
const STATE_MATCH: StatePtr = 1 << 30;

/// A dead state means that the state has been computed and it is known that
/// once it is entered, no future match can ever occur.
///
/// It is not valid to dereference STATE_DEAD.
const STATE_DEAD: StatePtr = STATE_MATCH + 1;

/// A poison state is used to fill in the transition table in places where
/// it would not make sense to have a real state pointer.
///
/// This is a valid poison value because both the SAVE and MATCH flags
/// cannot be set at the same time.
///
/// It is not valid to dereference STATE_POISON.
const STATE_POISON: StatePtr = !0;

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
