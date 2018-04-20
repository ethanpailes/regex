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
use std::collections::{HashMap, HashSet};
use prog::{Program, Inst, EmptyLook};
use literals::LiteralSearcher;
use re_trait::Slot;
use input::{ByteInput, Input};

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
    /// The prefixes.
    ///
    /// TODO(ethan):yakshaving this should probably be borrowed.
    prefixes: LiteralSearcher,
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
            at == 0 && self.exec_(text, at, slots)
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
                trace!("OnePass::exec trying to match at={} text.len()={}",
                        at, text.len());
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
        trace!("::exec_prefix at={} text.len()={}", at, text.len());
        if at < text.len() && !self.prefixes.is_empty() {
            at = at + self.prefixes
                .find(&text[at..])
                .map(|(s, _)| s)
                .unwrap_or(text.len());
        } else {
            while at < text.len() {
                let byte_class = self.byte_classes[text[at] as usize] as usize;
                if self.table[byte_class] != STATE_DEAD {
                    break;
                }
                at += 1;
            }
        }

        trace!("::exec_prefix next-chance={}", at);

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
        // We re-use the NFA input machinery for empty looks. We are
        // really going to work directly on the byte slice though.
        let input = ByteInput::new(text, false);

        let mut state_ptr = self.start_state;

        //
        // The inner loop of the onepass DFA.
        //
        // We bend over backwards to make sure that the inner loop
        // logically looks like:
        // 
        // while at < text.len():
        //    state_ptr = self.transitions[state_ptr + text[at]]
        //    at += 1
        //
        // As usual, this is a horrible lie. The onepass DFA steals
        // the byteclass compression trick from the lazy DFA, so there
        // is an extra layer of indirection. Any special flags need to
        // be handled, so we also need to check the STATE_SPECIAL mask
        // at every step. Finally, we use a backstop instead of the
        // actual text.len() to check when it is time to break out of
        // the loop to facilitate loop unrolling, and to avoid an
        // extra branch around when it is time to increment at.
        let step_size = 1;
        let backstop = text.len().checked_sub(step_size).unwrap_or(0);
        while at < backstop {
            if state_ptr & STATE_SPECIAL == 0 {
                // This is a weird looking place to increment at.
                // The reason we do so has to do with the odd
                // representation of a DFA that we've chosen.
                // Let's dump the simplest possible regex to unpack
                // that.
                //
                // ```text
                // > cd regex-debug
                // > cargo run -- --onepass compile 'a'
                // is_anchored_start: false
                // is_anchored_end: false
                // START: (0)
                //
                // 0: 0/D | 1/8 | 2/D | 3/D
                // 4: 0/0 | 1/0 | 2/P | 3/P
                // 8: 0/(c) | 1/(c) | 2/(c) | 3/(c)
                // c: 0/M | 1/M | 2/M | 3/M
                // 10: 0/0 | 1/1 | 2/P | 3/P
                // ```
                //
                // Our initial state is denoted (0) because it's transition
                // table lives at self.table[0] and because it is a
                // saving state. This means that it does not correspond
                // to the consumption of any input, yet its transition
                // table is derived from its child states. In this
                // case its only child state is 8. When we transition
                // to state 8, the assertion that the first byte be
                // 97 has already passed. Then we can't just increment
                // at after every input consuming state, as you might
                // think at first. The assertions associated with a state
                // really get checked right before we enter it, so the
                // right thing to do is to increment at only when we
                // enter an input consuming state.
                //
                // One might be concerned that this will cause us to
                // skip over the very first byte, but we are saved by
                // the fact that the first instruction is always a save
                // instruction.
                at += 1;
                let byte_class = self.byte_class(text, at);

                trace!("::exec_ loop-byte st={} at={} bc={} byte={}",
                        st_str(state_ptr), at, byte_class, text[at]);

                // No need to mask because there are no flags.
                state_ptr = self.follow(state_ptr as usize, byte_class);
            } else if state_ptr == STATE_DEAD {
                trace!("::exec_ loop-dead");
                return false;
            } else if state_ptr & STATE_ACTION != 0 {
                let byte_class = self.byte_class(text, at);
                trace!("::exec_ loop-act st={} at={} bc={} byte={}",
                        st_str(state_ptr), at, byte_class, text[at]);
                state_ptr = self.act(input, at, slots, state_ptr, byte_class);
            } else if state_ptr == STATE_MATCH {
                return !self.is_anchored_end;
            } else {
                unreachable!();
            }
        }

        //
        // Drain the input after the backstop.
        //

        // First, bump the at pointer if we just passed a byte test.
        if state_ptr & STATE_SPECIAL == 0 {
            at += 1;
        }
        while at < text.len() {
            let byte_class = self.byte_class(text, at);

            if state_ptr & STATE_SPECIAL == 0 {
                trace!("::exec_ drain-byte st={} at={} bc={} byte={}",
                        st_str(state_ptr), at, byte_class, text[at]);

                // No need to mask because no flags are set.
                state_ptr = self.follow(state_ptr as usize, byte_class);
            } else if state_ptr == STATE_DEAD {
                trace!("::exec_ drain-dead");
                return false;
            } else if state_ptr & STATE_ACTION != 0 {
                let byte_class = self.byte_class(text, at);
                trace!("::exec_ drain-act st={} at={} bc={} byte={}",
                        st_str(state_ptr), at, byte_class, text[at]);
                state_ptr = self.act(input, at, slots, state_ptr, byte_class);
            } else if state_ptr == STATE_MATCH {
                return !self.is_anchored_end;
            } else {
                unreachable!();
            }

            // We incur the cost of this extra branch in the drain
            // loop because we need to make sure that we won't fly
            // off the end of the string.
            if state_ptr & STATE_SPECIAL == 0 {
                at += 1;
            }
        }

        //
        // Execute one last step in the magic EOF byte class
        //

        // Set the byte class to be EOF
        let byte_class = self.num_byte_classes - 1;
        trace!("::exec eof st={} at={} bc={}", st_str(state_ptr), at, byte_class);
        if state_ptr & STATE_SPECIAL == 0 {
            state_ptr = self.table[state_ptr as usize + byte_class];
        }

        // Finally, drain any actions
        while state_ptr & STATE_ACTION != 0 {
            trace!("::exec eof act");
            state_ptr = self.act(input, at, slots, state_ptr, byte_class);
        }

        // All of that was only valid if we end up in a matching state.
        state_ptr == STATE_MATCH
    }

    #[inline]
    fn act<I: Input>(
        &self,
        input: I,
        at: usize,
        slots: &mut [Slot],
        state_ptr: StatePtr,
        byte_class: usize,
    ) -> StatePtr {
        // We had better have been called with a state that actually
        // needs to be acted on.
        debug_assert!(state_ptr & STATE_ACTION != 0);
        // No state should have both flags set.
        debug_assert!(state_ptr & STATE_MATCH == 0);

        let state_idx = (state_ptr & STATE_MAX) as usize;
        let action_type = self.table[state_idx + self.num_byte_classes];

        if action_type == Action::Save as StatePtr {
            let slot_idx = self.table[state_idx + self.num_byte_classes + 1];
            trace!("::act saving slot {}", slot_idx);
            slots[slot_idx as usize] = Some(at);

            self.follow(state_idx, byte_class)
        } else {
            let iat = input.at(at);
            let look = match action_type {
                x if x == Action::StartLine as StatePtr => EmptyLook::StartLine,
                x if x == Action::EndLine as StatePtr => EmptyLook::EndLine,
                x if x == Action::StartText as StatePtr => EmptyLook::StartText,
                x if x == Action::EndText as StatePtr => EmptyLook::EndText,
                x if x == Action::WordBoundary as StatePtr =>
                    EmptyLook::WordBoundary,
                x if x == Action::NotWordBoundary as StatePtr =>
                    EmptyLook::NotWordBoundary,
                x if x == Action::WordBoundaryAscii as StatePtr =>
                    EmptyLook::WordBoundaryAscii,
                x if x == Action::NotWordBoundaryAscii as StatePtr =>
                    EmptyLook::NotWordBoundaryAscii,
                _ => unreachable!("Bad action flag."),
            };

            trace!("::act look={:?}", look);

            if input.is_empty_match(iat, look) {
                self.follow(state_idx, byte_class)
            } else {
                STATE_DEAD
            }
        }

    }
    
    #[inline]
    fn byte_class(&self, text: &[u8], at: usize) -> usize {
        self.byte_classes[text[at] as usize] as usize
    }

    #[inline]
    fn follow(&self, state_idx: usize, byte_class: usize) -> StatePtr {
        self.table[state_idx + byte_class]
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
    BytesInst(usize),
    ActionInst(usize),
}

/// A (hopefully) DAG of forwarding jobs.
///
/// TODO(ethan):yakshaving there are more clones than I am comfortable
///                        with here.
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
            return Err(OnePassError::HasNondeterminism);
        }

        if prog.is_regexset() {
            return Err(OnePassError::RegexSetUnsupported);
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
                prefixes: prog.prefixes.clone(),
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
        self.onepass.start_state = 0 | STATE_ACTION;

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
                &Inst::EmptyLook(_) | &Inst::Save(_) => {
                    self.forward(inst_idx, child_idx, priority);
                    children.push(child_idx);
                }
                &Inst::Bytes(ref inst) => {
                    for byte in inst.start..(inst.end + 1) {
                        let bc = self.onepass.byte_classes[byte as usize];
                        trans.0[bc as usize] = Transition {
                            tgt: TransitionTarget::BytesInst(child_idx),
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
                &Inst::EmptyLook(_) | &Inst::Save(_) =>
                    TransitionTarget::ActionInst(fwd.to),
                _ =>
                    TransitionTarget::BytesInst(fwd.to),
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

    // Once all the per-instruction transition tables have been worked
    // out, we can bake them into the single flat transition table we
    // are going to use for the actual DFA.
    fn emit_transitions(&mut self) {
        // pre-compute the state indicies
        let mut state_starts = Vec::with_capacity(self.prog.len());
        let mut off = 0;
        for inst_idx in 0..self.prog.len() {
            state_starts.push(off);
            if self.transitions[inst_idx].is_some() {
                off += self.onepass.num_byte_classes;

                match &self.prog[inst_idx] {
                    &Inst::EmptyLook(_) | &Inst::Save(_) => {
                        off += self.onepass.num_byte_classes;
                    }
                    _ => {}
                }
            }
        }

        for inst_idx in 0..self.prog.len() {
            let mut trans = Vec::with_capacity(
                state_starts[state_starts.len() - 1]
                + self.onepass.num_byte_classes);

            match &self.transitions[inst_idx] {
                &None => continue,
                &Some(ref ttab) => {
                    for t in ttab.0.iter() {
                        trans.push(match t.tgt {
                            TransitionTarget::Match => STATE_MATCH,
                            TransitionTarget::Die => STATE_DEAD,
                            TransitionTarget::BytesInst(i) =>
                                state_starts[i] as StatePtr,
                            TransitionTarget::ActionInst(i) =>
                                (state_starts[i] as StatePtr) | STATE_ACTION,
                        });
                    }
                }
            }

            self.onepass.table.extend(trans);

            // emit all the right window dressing for the action
            match &self.prog[inst_idx] {
                &Inst::Save(ref inst) => {
                    debug_assert!(self.onepass.num_byte_classes >= 2);

                    let mut save_args = vec![
                        Action::Save as StatePtr,
                        inst.slot as StatePtr];
                    save_args.extend(vec![STATE_POISON;
                        self.onepass.num_byte_classes - 2]);
                    self.onepass.table.extend(save_args);
                }
                &Inst::EmptyLook(ref inst) => {
                    let mut el_args = vec![self.empty_look_action(inst.look)];
                    el_args.extend(vec![STATE_POISON;
                        self.onepass.num_byte_classes - 1]);
                    self.onepass.table.extend(el_args);
                }
                _ => {}
            }
        }
    }

    fn empty_look_action(&self, el: EmptyLook) -> StatePtr {
        match el {
            EmptyLook::StartLine => Action::StartLine as StatePtr,
            EmptyLook::EndLine => Action::EndLine as StatePtr,
            EmptyLook::StartText => Action::StartText as StatePtr,
            EmptyLook::EndText => Action::EndText as StatePtr,
            EmptyLook::WordBoundary => Action::WordBoundary as StatePtr,
            EmptyLook::NotWordBoundary => Action::NotWordBoundary as StatePtr,
            EmptyLook::WordBoundaryAscii => Action::WordBoundaryAscii as StatePtr,
            EmptyLook::NotWordBoundaryAscii =>
                Action::NotWordBoundaryAscii as StatePtr,
        }
    }
}

#[derive(Debug)]
pub enum OnePassError {
    /// This program can't be executed as a one-pass regex.
    HasNondeterminism,
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
    } else {
        if st == STATE_POISON {
            "P".to_string()
        } else if st & STATE_ACTION != 0 {
            format!("({:x})", st & STATE_MAX)
        } else if st & STATE_MATCH != 0 {
            "M".to_string()
        } else {
            format!("{:x}", st & STATE_MAX)
        }
    }
}

/// The ACTION state means that the DFA needs to take some
/// action that will be specified by the first two StatePtrs
/// in a special transition table entry just below the transition
/// table for the ACTION state. An ACTION might include checking
/// some zero-width assertion about the input, or it might include
/// saving a value to a capture slots.
const STATE_ACTION: StatePtr = 1 << 31;

/// An action which might need to be taken for a special state.
enum Action {
    Save,
    StartLine,
    EndLine,
    StartText,
    EndText,
    WordBoundary,
    NotWordBoundary,
    WordBoundaryAscii,
    NotWordBoundaryAscii,
}

/// A match state means that the regex has successfully matched.
///
/// It is not valid to dereference STATE_MATCH. We use a header
/// bitflag anyway to facilitate special case checking.
const STATE_MATCH: StatePtr = 1 << 30;

/// POISON is a state pointer that should never be touched.
/// We use it to pad invalid argument slots to ACTION states.
const STATE_POISON: StatePtr = !0;

/// A dead state means that the state has been computed and it is known that
/// once it is entered, no future match can ever occur.
///
/// It is not valid to dereference STATE_DEAD.
const STATE_DEAD: StatePtr = STATE_MATCH + 1;

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
const STATE_SPECIAL: StatePtr = STATE_MATCH | STATE_ACTION;
