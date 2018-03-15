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

use std::collections::HashSet;

use std::fmt;

use prog::{Program, Inst};

/// A OnePass DFA.
#[derive(Debug)]
pub struct OnePass {
    /// The table.
    table: Vec<StatePtr>,
    /// The stride.
    num_byte_classes: usize,
    /// The starting state.
    start_state: StatePtr,
}

impl fmt::Display for OnePass {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        for i in 0..(self.table.len() / self.num_byte_classes) {
            fn st_str(st: StatePtr) -> String {
                if st == STATE_DEAD {
                    "D".to_string()
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

            let trans_start = i * self.num_byte_classes;
            let trans_end = (i+1) * self.num_byte_classes;
            let trans = &self.table[trans_start..trans_end];
            try!(writeln!(f, "{}: {}", 
                    if trans_start as StatePtr == self.start_state {
                        format!("START {:x}", trans_start)
                    } else {
                        format!("{:x}", trans_start)
                    },
                    trans.iter().enumerate()
                         .map(|(i, x)| format!("{}/{}", i, st_str(*x)))
                         .collect::<Vec<String>>()
                         .join(" | ")));
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
    /// Attempt to compile a regex into a one-pass DFA
    pub fn compile(prog: &Program) -> Result<Self, OnePassError> {
        try!(Self::check_can_exec(prog));

        let mut dfa = OnePass {
            table: vec![],
            num_byte_classes: (prog.byte_classes[255] as usize + 1) + 1,
            start_state: 0,
        };

        let mut transitions = vec![STATE_DEAD; dfa.num_byte_classes];
        dfa.build_transition_table(prog, 0, &mut transitions);
        dfa.start_state = dfa.table.len() as StatePtr;
        dfa.table.extend(transitions);

        Ok(dfa)
    }

    fn build_transition_table(
        &mut self,
        prog: &Program,
        start: usize,
        transitions: &mut [StatePtr],
    ) {
        debug_assert!(transitions.len() == self.num_byte_classes);

        let mut resume = match &prog[start] {
            &Inst::Match(_) => vec![], // no kids
            &Inst::Save(ref inst) => vec![inst.goto],
            &Inst::Split(ref inst) => vec![inst.goto2, inst.goto1],
            &Inst::EmptyLook(ref inst) => vec![inst.goto],
            &Inst::Char(ref inst) => vec![inst.goto],
            &Inst::Ranges(ref inst) => vec![inst.goto],
            &Inst::Bytes(ref inst) => vec![inst.goto],
        };

        let mut seen = HashSet::new();
        seen.insert(start);

        while let Some(inst_idx) = resume.pop() {
            if seen.contains(&inst_idx) {
                return;
            }
            seen.insert(inst_idx);

            match &prog[inst_idx] {
                &Inst::Match(_) => {
                    // A match instruction must be an only child.
                    let p = STATE_MATCH | self.table.len() as StatePtr;
                    self.table.extend(vec![STATE_DEAD; self.num_byte_classes]);
                    transitions.iter_mut().for_each(|t| *t = p);
                }
                &Inst::Save(ref inst) => {
                    let mut save_transitions =
                        vec![STATE_DEAD; self.num_byte_classes];
                    self.build_transition_table(
                        prog, inst.goto, &mut save_transitions);

                    // TODO: test with just one byte class

                    // Save instructions take up two transition table
                    // entries. The first entry indicates the save slot,
                    // while the second contains the actual transitions.
                    // We need to route any transitions which would be
                    // happening in the save subtree though this entry
                    // in the table.
                    let p = STATE_SAVE | self.table.len() as StatePtr;
                    self.table.extend(
                        vec![inst.slot as u32; self.num_byte_classes]);
                    for (i, st) in save_transitions.iter().enumerate() {
                        if *st != STATE_DEAD {
                            transitions[i] = p;
                        }
                    }
                    self.table.extend(save_transitions);
                }
                &Inst::Split(ref inst) => {
                    resume.push(inst.goto2);
                    resume.push(inst.goto1);
                }
                &Inst::EmptyLook(ref inst) => {
                    // This is definitly doable with an intermediary state,
                    // but the normal DFA does something with flags that
                    // I should probably ask @burntsushi about.
                    // For now, we just skip them.
                    //
                    // TODO: emptylook
                    resume.push(inst.goto);
                }
                &Inst::Bytes(ref inst) => {
                    let mut bytes_transitions =
                        vec![STATE_DEAD; self.num_byte_classes];
                    self.build_transition_table(
                        prog, inst.goto, &mut bytes_transitions);

                    let p = self.table.len() as StatePtr;
                    self.table.extend(bytes_transitions);

                    let byte_class = prog.byte_classes[inst.start as usize];
                    transitions[byte_class as usize] = p;
                }
                &Inst::Char(_) | &Inst::Ranges(_) => unreachable!(),
            }
        }
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

/// The CAP_SAVE state means that the DFA should save the current
/// string pointer in a capture slot indicated by the first entry
/// in its transition table. The DFA always transitions to the next
/// state in the state table.
const STATE_SAVE: StatePtr = 1 << 31;

/// A dead state means that the state has been computed and it is known that
/// once it is entered, no future match can ever occur.
///
/// It is not valid to dereference STATE_DEAD.
const STATE_DEAD: StatePtr = STATE_SAVE + 1;

/*
/// A quit state means that the DFA came across some input that it doesn't
/// know how to process correctly. The DFA should quit and another matching
/// engine should be run in its place.
///
/// It is not valid to dereference STATE_QUIT.
const STATE_QUIT: StatePtr = STATE_DEAD + 1;
*/

/// A match state means that the regex has successfully matched.
///
/// Note that match states have their lower bits set to a state pointer.
const STATE_MATCH: StatePtr = 1 << 30;

/// The maximum state pointer. This is useful to mask out the "valid" state
/// pointer from a state with the "start" or "match" bits set.
///
/// It doesn't make sense to use this with unknown, dead or quit state
/// pointers, since those pointers are sentinels and never have their lower
/// bits set to anything meaningful.
const STATE_MAX: StatePtr = STATE_MATCH - 1;
