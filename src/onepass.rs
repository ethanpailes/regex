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

use prog::Program;

struct OnePass {
    /// The table.
    table: Vec<StatePtr>,
    /// The stride.
    num_byte_classes: usize,
    /// The start states
    start_states: Vec<StatePtr>,
}

enum OnePassError {
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
    pub fn compile(prog: &Program) -> Result<Self, OnePassError> {
        try!(Self::check_can_exec(prog));

        let mut dfa = OnePass {
            table: vec![],
            num_byte_classes: (prog.byte_classes[255] as usize + 1) + 1,
            start_states: vec![],
        };

        for inst in prog {
            match inst {
                &Match(slot) => {
                }
                /*
    Match(usize),
    /// Save causes the program to save the current location of the input in
    /// the slot indicated by InstSave.
    Save(InstSave),
    /// Split causes the program to diverge to one of two paths in the
    /// program, preferring goto1 in InstSplit.
    Split(InstSplit),
    /// EmptyLook represents a zero-width assertion in a regex program. A
    /// zero-width assertion does not consume any of the input text.
    EmptyLook(InstEmptyLook),
    /// Char requires the regex program to match the character in InstChar at
    /// the current position in the input.
    Char(InstChar),
    /// Ranges requires the regex program to match the character at the current
    /// position in the input with one of the ranges specified in InstRanges.
    Ranges(InstRanges),
    /// Bytes is like Ranges, except it expresses a single byte range. It is
    /// used in conjunction with Split instructions to implement multi-byte
    /// character classes.
    Bytes(InstBytes),
    */

            }
        }

        Err(OnePassError::TooBig)
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

/// The CAP_START state means that the DFA should save the current
/// string pointer in a capture slot indicated by the first entry
/// in its transition table. The DFA always transitions to the next
/// state in the state table.
const STATE_CAP_START: StatePtr = 1 << 31;

/// The CAP_END state means that the DFA should save the current
/// string pointer in a capture slot indicated by the first entry
/// in its transition table. The DFA always transitions to the next
/// state in the state table.
const STATE_CAP_END: StatePtr = 1 << 30;

/// A dead state means that the state has been computed and it is known that
/// once it is entered, no future match can ever occur.
///
/// It is not valid to dereference STATE_DEAD.
const STATE_DEAD: StatePtr = STATE_CAP_END + 1;

/// A quit state means that the DFA came across some input that it doesn't
/// know how to process correctly. The DFA should quit and another matching
/// engine should be run in its place.
///
/// It is not valid to dereference STATE_QUIT.
const STATE_QUIT: StatePtr = STATE_DEAD + 1;

/// A start state is a state that the DFA can start in.
///
/// Note that start states have their lower bits set to a state pointer.
const STATE_START: StatePtr = 1 << 29;

/// A match state means that the regex has successfully matched.
///
/// Note that match states have their lower bits set to a state pointer.
const STATE_MATCH: StatePtr = 1 << 28;

/// The maximum state pointer. This is useful to mask out the "valid" state
/// pointer from a state with the "start" or "match" bits set.
///
/// It doesn't make sense to use this with unknown, dead or quit state
/// pointers, since those pointers are sentinels and never have their lower
/// bits set to anything meaningful.
const STATE_MAX: StatePtr = STATE_MATCH - 1;
