extern crate char_iter;

use std::collections::{HashMap, HashSet};
use std::cmp::Ordering;
use std::fmt;
use std::ops::Deref;
use std::mem;
use std::slice;
use std::sync::Arc;

use input::Char;
use literals::LiteralSearcher;

// Flip to true for debugging
const TRACE: bool = false;
macro_rules! trace {
    ($($tts:tt)*) => {
        if TRACE {
            println!($($tts)*);
        }
    }
}

#[cfg(test)]
use exec::{ExecBuilder, Exec};

/// `InstPtr` represents the index of an instruction in a regex program.
pub type InstPtr = usize;

/// Program is a sequence of instructions and various facts about thos
/// instructions.
#[derive(Clone)]
pub struct Program {
    /// A sequence of instructions that represents an NFA.
    pub insts: Vec<Inst>,
    /// A sequence of skip instructions representing the Skip NFA.
    pub skip_insts: Vec<SkipInst>,
    /// Pointers to each Match instruction in the sequence.
    ///
    /// This is always length 1 unless this program represents a regex set.
    pub matches: Vec<InstPtr>,
    /// The ordered sequence of all capture groups extracted from the AST.
    /// Unnamed groups are `None`.
    pub captures: Vec<Option<String>>,
    /// Pointers to all named capture groups into `captures`.
    pub capture_name_idx: Arc<HashMap<String, usize>>,
    /// A pointer to the start instruction. This can vary depending on how
    /// the program was compiled. For example, programs for use with the DFA
    /// engine have a `.*?` inserted at the beginning of unanchored regular
    /// expressions. The actual starting point of the program is after the
    /// `.*?`.
    pub start: InstPtr,
    /// A pointer to the start of the skip instructions. See above.
    pub skip_start: InstPtr,
    /// A set of equivalence classes for discriminating bytes in the compiled
    /// program.
    pub byte_classes: Vec<u8>,
    /// When true, this program can only match valid UTF-8.
    pub only_utf8: bool,
    /// When true, this program uses byte range instructions instead of Unicode
    /// range instructions.
    pub is_bytes: bool,
    /// When true, the program is compiled for DFA matching. For example, this
    /// implies `is_bytes` and also inserts a preceding `.*?` for unanchored
    /// regexes.
    pub is_dfa: bool,
    /// When true, the program matches text in reverse (for use only in the
    /// DFA).
    pub is_reverse: bool,
    /// Whether the regex must match from the start of the input.
    pub is_anchored_start: bool,
    /// Whether the regex must match at the end of the input.
    pub is_anchored_end: bool,
    /// Whether this program contains a Unicode word boundary instruction.
    pub has_unicode_word_boundary: bool,
    /// A possibly empty machine for very quickly matching prefix literals.
    pub prefixes: LiteralSearcher,
    /// True if the program has skip instructions.
    pub has_skip_insts: bool,
    /// A limit on the size of the cache that the DFA is allowed to use while
    /// matching.
    ///
    /// The cache limit specifies approximately how much space we're willing to
    /// give to the state cache. Once the state cache exceeds the size, it is
    /// wiped and all states must be re-computed.
    ///
    /// Note that this value does not impact correctness. It can be set to 0
    /// and the DFA will run just fine. (It will only ever store exactly one
    /// state in the cache, and will likely run very slowly, but it will work.)
    ///
    /// Also note that this limit is *per thread of execution*. That is,
    /// if the same regex is used to search text across multiple threads
    /// simultaneously, then the DFA cache is not shared. Instead, copies are
    /// made.
    pub dfa_size_limit: usize,
}

impl Program {
    /// Creates an empty instruction sequence. Fields are given default
    /// values.
    pub fn new() -> Self {
        Program {
            insts: vec![],
            skip_insts: vec![],
            matches: vec![],
            captures: vec![],
            capture_name_idx: Arc::new(HashMap::new()),
            start: 0,
            skip_start: 0,
            byte_classes: vec![0; 256],
            only_utf8: true,
            is_bytes: false,
            is_dfa: false,
            is_reverse: false,
            is_anchored_start: false,
            is_anchored_end: false,
            has_unicode_word_boundary: false,
            prefixes: LiteralSearcher::empty(),
            has_skip_insts: false,
            dfa_size_limit: 2 * (1<<20),
        }
    }

    /// If pc is an index to a no-op instruction (like Save), then return the
    /// next pc that is not a no-op instruction.
    pub fn skip(&self, mut pc: usize) -> usize {
        loop {
            match self[pc] {
                Inst::Save(ref i) => pc = i.goto,
                _ => return pc,
            }
        }
    }

    /// An iterator over the direct non-noop decedents of the instruction
    /// at the given pc.
    pub fn children(&self, pc: usize) -> InstChildren {
        InstChildren::new(self.insts.as_slice(), pc)
    }

    /// Decides the question L(self) `intersect` L(other) == emptyset.
    ///
    /// This question is key to deciding when it is ligitimate to
    /// perform the LiteralScan optimization.
    ///
    /// We just do DFS over the intersect automita of the two regex
    pub fn intersection_is_empty(lhs: &Self, rhs: &Self) -> bool {
        use self::Inst::*;

        if TRACE {
            trace!("");
            trace!("====================== LHS ========================");
            for (i, inst) in lhs.insts.iter().enumerate() {
                trace!("{:04}: {:?}", i, inst);
            }
            trace!("==================== END LHS ======================");
            trace!("");
            trace!("");
            trace!("");
            trace!("====================== RHS ========================");
            for (i, inst) in rhs.insts.iter().enumerate() {
                trace!("{:04}: {:?}", i, inst);
            }
            trace!("==================== END RHS ======================");
        }

        let inter_children = |st: IntersectState| {
            IntersectInstChildren::new(
                    lhs.insts.as_slice(), st.st1,
                    rhs.insts.as_slice(), st.st2)
        };

        let is_match = |st: &IntersectState| {
            let m = match lhs.insts[st.st1] {
                Match(_) => {
                    match rhs.insts[st.st2] {
                        Match(_) => true,
                        _ => false,
                    }
                }
                _ => false,
            };
            trace!("Program::intersection_is_empty::is_match {}", m);
            m
        };

        let mut stack: Vec<IntersectState> = vec![IntersectState {
            st1: lhs.start,
            st2: rhs.start,
        }];

        let mut seen = HashSet::new();

        while let Some(st) = stack.pop() {
            trace!("loop on state (st1={}, st2={})", st.st1, st.st2);
            if seen.contains(&st) {
                continue;
            }
            seen.insert(st.clone());

            // A matching state is reachable from the start,
            // so L(self) `intersect` L(other) /= emptyset
            if is_match(&st) {
                return false;
            }

            for c in inter_children(st) {
                trace!("pushing kid (st1={}, st2={})", c.st1, c.st2);
                stack.push(c);
            }
        }

        // No matter what input we are given, the intersection will
        // never accept.
        true
    }

    /// Return true if and only if an execution engine at instruction `pc` will
    /// always lead to a match.
    pub fn leads_to_match(&self, pc: usize) -> bool {
        if self.matches.len() > 1 {
            // If we have a regex set, then we have more than one ending
            // state, so leading to one of those states is generally
            // meaningless.
            return false;
        }
        match self[self.skip(pc)] {
            Inst::Match(_) => true,
            _ => false,
        }
    }

    /// Returns true if the current configuration demands that an implicit
    /// `.*?` be prepended to the instruction sequence.
    pub fn needs_dotstar(&self) -> bool {
        self.is_dfa && !self.is_reverse && !self.is_anchored_start
    }

    /// Returns true if this program uses Byte instructions instead of
    /// Char/Range instructions.
    pub fn uses_bytes(&self) -> bool {
        self.is_bytes || self.is_dfa
    }

    /// Returns true if this program exclusively matches valid UTF-8 bytes.
    ///
    /// That is, if an invalid UTF-8 byte is seen, then no match is possible.
    pub fn only_utf8(&self) -> bool {
        self.only_utf8
    }

    /// Return the approximate heap usage of this instruction sequence in
    /// bytes.
    pub fn approximate_size(&self) -> usize {
        // The only instruction that uses heap space is Ranges (for
        // Unicode codepoint programs) to store non-overlapping codepoint
        // ranges. To keep this operation constant time, we ignore them.
        (self.len() * mem::size_of::<Inst>())
        + (self.matches.len() * mem::size_of::<InstPtr>())
        + (self.captures.len() * mem::size_of::<Option<String>>())
        + (self.capture_name_idx.len() *
           (mem::size_of::<String>() + mem::size_of::<usize>()))
        + (self.byte_classes.len() * mem::size_of::<u8>())
        + self.prefixes.approximate_size()
    }

    fn fmt_standard(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::Inst::*;

        try!(write!(f, "=============== STANDARD PROGRAM =================\n"));

        for (pc, inst) in self.iter().enumerate() {
            match *inst {
                Match(slot) => {
                    try!(write!(f, "{:04} Match({:?})", pc, slot))
                }
                Save(ref inst) => {
                    let s = format!("{:04} Save({})", pc, inst.slot);
                    try!(write!(f, "{}", Self::fmt_with_goto(pc, inst.goto, s)));
                }
                Split(ref inst) => {
                    try!(write!(f, "{:04} Split({}, {})",
                                pc, inst.goto1, inst.goto2));
                }
                EmptyLook(ref inst) => {
                    let s = format!("{:?}", inst.look);
                    try!(write!(f, "{:04} {}",
                                pc, Self::fmt_with_goto(pc, inst.goto, s)));
                }
                Char(ref inst) => {
                    let s = format!("{:?}", inst.c);
                    try!(write!(f, "{:04} {}",
                                pc, Self::fmt_with_goto(pc, inst.goto, s)));
                }
                Ranges(ref inst) => {
                    let ranges = inst.ranges
                        .iter()
                        .map(|r| format!("{:?}-{:?}", r.0, r.1))
                        .collect::<Vec<String>>()
                        .join(", ");
                    try!(write!(f, "{:04} {}",
                                pc, Self::fmt_with_goto(pc, inst.goto, ranges)));
                }
                Bytes(ref inst) => {
                    let s = format!(
                        "Bytes({}, {})",
                        Self::fmt_visible_byte(inst.start),
                        Self::fmt_visible_byte(inst.end));
                    try!(write!(f, "{:04} {}",
                                pc, Self::fmt_with_goto(pc, inst.goto, s)));
                }
            }
            if pc == self.start {
                try!(write!(f, " (start)"));
            }
            try!(write!(f, "\n"));
        }
        Ok(())
    }

    fn fmt_skip(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::SkipInst::*;

        try!(write!(f, "================= SKIP PROGRAM ===================\n"));

        for (pc, inst) in self.skip_insts.iter().enumerate() {
            match *inst {
                SkipMatch(slot) => {
                    try!(write!(f, "{:04} Match({:?})", pc, slot))
                }
                SkipSave(ref inst) => {
                    let s = format!("{:04} Save({})", pc, inst.slot);
                    try!(write!(f, "{}", Self::fmt_with_goto(pc, inst.goto, s)));
                }
                SkipSplit(ref inst) => {
                    try!(write!(f, "{:04} Split({}, {})",
                                pc, inst.goto1, inst.goto2));
                }
                SkipByte(ref inst) => {
                    let s = format!("{:?} (Byte({:?}))",
                                        inst.c as char, inst.c);
                    try!(write!(f, "{:04} {}",
                                pc, Self::fmt_with_goto(pc, inst.goto, s)));
                }
                SkipBytes(ref inst) => {
                    let s = format!(
                        "Bytes({}, {})",
                        Self::fmt_visible_byte(inst.start),
                        Self::fmt_visible_byte(inst.end));
                    try!(write!(f, "{:04} {}",
                                pc, Self::fmt_with_goto(pc, inst.goto, s)));
                }
                SkipEmptyLook(ref inst) => {
                    let s = format!("{:?}", inst.look);
                    try!(write!(f, "{:04} {}",
                                pc, Self::fmt_with_goto(pc, inst.goto, s)));
                }
                SkipSkip(ref inst) => {
                    let s = format!("Skip({})", inst.skip);
                    try!(write!(f, "{:04} {}", pc,
                                Self::fmt_with_goto(pc, inst.goto, s)));
                }
                SkipScanLiteral(ref inst) => {
                    let s = format!("Scan{}({})",
                        if inst.start { "Start" } else { "End" },
                        inst.literal);
                    try!(write!(f, "{:04} {}", pc,
                                Self::fmt_with_goto(pc, inst.goto, s)));
                }
            }

            if pc == self.start {
                try!(write!(f, " (start)"));
            }

            try!(write!(f, "\n"));
        }
        Ok(())
    }

    fn fmt_with_goto(cur: usize, goto: usize, fmtd: String) -> String {
        if goto == cur + 1 {
            fmtd
        } else {
            format!("{} (goto: {})", fmtd, goto)
        }
    }

    fn fmt_visible_byte(b: u8) -> String {
        use std::ascii::escape_default;
        let escaped = escape_default(b).collect::<Vec<u8>>();
        String::from_utf8_lossy(&escaped).into_owned()
    }

}

impl Deref for Program {
    type Target = [Inst];

    fn deref(&self) -> &Self::Target {
        &*self.insts
    }
}

impl fmt::Debug for Program {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.has_skip_insts {
            self.fmt_skip(f)
        } else {
            self.fmt_standard(f)
        }
    }
}

impl<'a> IntoIterator for &'a Program {
    type Item = &'a Inst;
    type IntoIter = slice::Iter<'a, Inst>;
    fn into_iter(self) -> Self::IntoIter { self.iter() }
}

/// InstChildren implements a resumable DFS on program states.
#[derive(Clone, Debug)]
pub struct InstChildren<'p> {
    /// A stack recording our position in the DFS.
    branches: Vec<usize>,
    /// The set of states that we have returned.
    seen: HashSet<usize>,
    /// The instructions we are iterating over.
    insts: &'p [Inst],
}

impl<'p> InstChildren<'p> {
    fn new(insts: &'p [Inst], start: usize) -> Self {
        trace!("InstChildren::new");
        let mut c = InstChildren {
            branches: vec![],
            seen: HashSet::new(),
            insts: insts,
        };
        c.find_next(start);
        c
    }

    /// Given a start point, follow goto pointers until we
    /// reach a leaf value, leaving a trail of breadcrumbs
    /// in `branches` to handle split points.
    ///
    /// INVARIANT: `from` has already been returned from the iterator
    ///             or is the origin state.
    fn find_next(&mut self, from: usize) {
        trace!("InstChildren::find_next from={} branches={:?}",
                from, self.branches);
        use self::Inst::*;

        let mut i = match self.insts[from] {
            // Save's don't exist in the logical version of the NFA 
            // that we are working with here. Skip em.
            Save(ref inst) => inst.goto,

            // We actually do have to deal with split and emptylook
            Split(_) => from,
            EmptyLook(_) => from,

            // don't start at `from` so that we can actually make it
            // out of input consuming states
            Char(ref inst) => inst.goto,
            Ranges(ref inst) => inst.goto,
            Bytes(ref inst) => inst.goto,

            // It's a match. There are no outgoing edges.
            Match(_) => return,
        };

        loop {
            trace!("InstChildren::find_next loop inst={} branches={:?}",
                        i, self.branches);
            match self.insts[i] {
                Save(ref inst) => i = inst.goto,
                Split(ref inst) => {
                    self.branches.push(inst.goto2);
                    i = inst.goto1;
                }
                EmptyLook(ref inst) => {
                    // It's not totally obvious that the seen set is
                    // correct on the face of it. What if two different
                    // nodes can reach an emptylook (same goes for
                    // input-consuming states actually)?
                    //
                    // I'm going to say that it is fine because history
                    // doesn't matter for this NFA. Thanks Russ Cox!
                    if self.seen.contains(&i) {
                        self.branches.push(i);
                        return;
                    } else {
                        self.branches.push(i);
                        self.seen.insert(i);
                        i = inst.goto;
                    }
                }
                _ => { // input consuming state
                    if self.seen.contains(&i) {
                        self.branches.pop().map(|resume| {
                            trace!("InstChildren::find_next contains resume={}",
                                    resume);
                            i = resume;
                        });
                    } else {
                        self.branches.push(i);
                        self.seen.insert(i);
                        return;
                    }
                }
            }
        }
    }
}

/// An iterator over the child instructions of a given instruction.
///
/// This will automatically follow Split and Save instructions, so
/// that it only returns instructions which might assert something
/// about the input.
impl<'p> Iterator for InstChildren<'p> {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        trace!("InstChildren::next branches={:?} seen={:?}",
                    self.branches, self.seen);
        let result = self.branches.pop();
        self.branches.pop().map(|from| self.find_next(from));
        result
    }
}

/// To take the interesction of two Regex we can construct
/// a new automita where each state is a tuple of the two
/// states of the input Regex. In our VM formulation of an
/// NFA, states are instruction indicies
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct IntersectState {
    st1: usize,
    st2: usize,
}

#[derive(Clone, Debug)]
struct IntersectInstChildren<'p> {
    i1: InstChildren<'p>,
    i1_current: Option<usize>,
    insts1: &'p [Inst],

    i2: InstChildren<'p>,
    i2_current: InstChildren<'p>,
    insts2: &'p [Inst],
}

impl<'p> IntersectInstChildren<'p> {
    fn new(
        insts1: &'p [Inst],
        st1: usize,
        insts2: &'p [Inst],
        st2: usize
    ) -> Self {
        trace!("IntersectInstChildren::new st1={} st2={}", st1, st2);
        let mut i1 = InstChildren::new(insts1, st1);
        let i2 = InstChildren::new(insts2, st2);
        let cur = i1.next();
        Self {
            i1: i1,
            i1_current: cur,
            insts1,
            i2: i2.clone(),
            i2_current: i2,
            insts2,
        }
    }
}

macro_rules! otry {
    ($e:expr) => {
        match $e {
            None => return None,
            Some(x) => x,
        }
    }
}

impl<'p> Iterator for IntersectInstChildren<'p> {
    type Item = IntersectState;

    fn next(&mut self) -> Option<Self::Item> {
        let st2 = match self.i2_current.next() {
            None => { // time to shuffle i1
                trace!("IntersectInstChildren::next time to reset i1");
                self.i1_current = self.i1.next();
                self.i2_current = self.i2.clone();

                // If the second iterator has no elements,
                // then we have no elements
                otry!(self.i2_current.next())
            }
            Some(i2_st) => i2_st,
        };

        // If we run off the end of the first iterator, we are done.
        let st1 = otry!(self.i1_current);

        trace!("IntersectInstChildren::next st1={} st2={}", st1, st2);

        // We want to gaurd against returning a state which can't
        // accept any charicter. For example consider the state:
        //
        // ```text
        // char a ; char b
        // ```
        //
        // Here if the input charicter is an 'a' then thread 2 will die,
        // but if the input charicter is a 'b' then thread 1 will die.
        // if Inst::has_intersecting_char(&self.insts1[st1], &self.insts2[st2]) {
        if self.insts_have_intersecting_char(st1, st2) {
            trace!("IntersectInstChildren::next terminal compound state");
            Some(IntersectState {
                st1: st1,
                st2: st2,
            })
        } else {
            trace!("IntersectInstChildren::next dead-end compound state");
            self.next()
        }

    }
}

impl<'p> IntersectInstChildren<'p> {

    fn insts_have_intersecting_char(&self, i1: usize, i2: usize) -> bool {
        match (&self.insts1[i1], &self.insts2[i2]) {
            // Char
            (&Inst::Char(ref c1), &Inst::Char(ref c2)) => c1.c == c2.c,
            (&Inst::Char(ref c), &Inst::Ranges(ref rs)) =>
                rs.matches(Char::from(c.c)),
            (&Inst::Char(_), &Inst::Bytes(_)) =>
                unreachable!("mixed unicode and byte regex."),

            // Ranges
            (&Inst::Ranges(ref rs), &Inst::Char(ref c)) =>
                rs.matches(Char::from(c.c)),
            (&Inst::Ranges(ref rs1), &Inst::Ranges(ref rs2)) =>
                rs1.intersects(rs2),
            (&Inst::Ranges(_), &Inst::Bytes(_)) =>
                unreachable!("mixed unicode and byte regex."),

            // Bytes
            (&Inst::Bytes(_), &Inst::Char(_)) =>
                unreachable!("mixed unicode and byte regex."),
            (&Inst::Bytes(_), &Inst::Ranges(_)) =>
                unreachable!("mixed unicode and byte regex."),
            (&Inst::Bytes(ref bs1), &Inst::Bytes(ref bs2)) =>
                bs1.intersects(bs2),

            // this one is kind of tricky so we punt to a dedicated method
            (_, &Inst::EmptyLook(ref el)) =>
                self.intersects_with_empty_look(&self.insts1, i1, el),
            (&Inst::EmptyLook(ref el), _) =>
                self.intersects_with_empty_look(&self.insts2, i2, el),

            // control nodes can always intersect
            (_, &Inst::Match(_)) => true,
            (_, &Inst::Save(_)) => true,
            (_, &Inst::Split(_)) => true,
            (&Inst::Match(_), _) => true,
            (&Inst::Save(_), _) => true,
            (&Inst::Split(_), _) => true,
        }
    }

    // True if the instruction at the given offset in the given list of
    // instructions intersects with the given empty look.
    fn intersects_with_empty_look(
        &self,
        insts: &[Inst],
        ip: usize,
        el: &InstEmptyLook
    ) -> bool {
        use syntax::is_word_char;

        let word_boundry = match el.look {
            // Conservativly just say start and end assertions intersect
            // with anything.
            EmptyLook::StartLine | EmptyLook::EndLine
            | EmptyLook::StartText | EmptyLook::EndText => return true,

            EmptyLook::WordBoundary => true,
            EmptyLook::WordBoundaryAscii => true,
            EmptyLook::NotWordBoundary => false,
            EmptyLook::NotWordBoundaryAscii => false,
        };

        fn contains_word_char(i: &Inst) -> Option<bool> {
            match i {
                &Inst::Char(ref inst) => {
                    Some(is_word_char(inst.c))
                }
                &Inst::Ranges(ref inst) => {
                    Some(inst.ranges.iter().any(|&(rstart, rend)|
                            char_iter::new(rstart, rend).any(is_word_char)))
                }
                &Inst::Bytes(ref inst) => {
                    Some((inst.start..inst.end)
                            .any(|b| is_word_char(b as char)))
                }

                // don't know
                &Inst::EmptyLook(_) | &Inst::Match(_)
                | &Inst::Save(_) | &Inst::Split(_) => None,
            }
        }

        fn contains_non_word_char(i: &Inst) -> Option<bool> {
            contains_word_char(i).map(|x| !x)
        }

        let prev = if ip == 0 { None } else {
            match &insts[ip - 1] {
                &Inst::Char(ref inst) => {
                    if inst.goto == ip {
                        Some(&insts[ip - 1])
                    } else {
                        None
                    }
                }
                &Inst::Ranges(ref inst) => {
                    if inst.goto == ip {
                        Some(&insts[ip - 1])
                    } else {
                        None
                    }
                }
                &Inst::Bytes(ref inst) => {
                    if inst.goto == ip {
                        Some(&insts[ip - 1])
                    } else {
                        None
                    }
                }

                _ => None,
            }
        };

        let prev_contains_word_char = prev.and_then(contains_word_char);
        let prev_contains_non_word_char = prev.and_then(contains_non_word_char);
        let curr_contains_word_char = contains_word_char(&insts[ip]);
        let curr_contains_non_word_char = contains_non_word_char(&insts[ip]);

        prev_contains_word_char.and_then(|p_wc|
            curr_contains_word_char.and_then(|c_wc|
                prev_contains_non_word_char.and_then(|p_nwc|
                    curr_contains_non_word_char.and_then(|c_nwc|
                        if word_boundry {
                            Some(p_wc != c_wc || p_nwc != c_nwc)
                        } else {
                            Some(p_wc == c_wc || p_nwc == c_nwc)
                        })))).unwrap_or(true)
    }
}

/// Inst is an instruction code in a Regex program.
///
/// Regrettably, a regex program either contains Unicode codepoint
/// instructions (Char and Ranges) or it contains byte instructions (Bytes).
/// A regex program can never contain both.
///
/// It would be worth investigating splitting this into two distinct types and
/// then figuring out how to make the matching engines polymorphic over those
/// types without sacrificing performance.
///
/// Other than the benefit of moving invariants into the type system, another
/// benefit is the decreased size. If we remove the `Char` and `Ranges`
/// instructions from the `Inst` enum, then its size shrinks from 40 bytes to
/// 24 bytes. (This is because of the removal of a `Vec` in the `Ranges`
/// variant.) Given that byte based machines are typically much bigger than
/// their Unicode analogues (because they can decode UTF-8 directly), this ends
/// up being a pretty significant savings.
#[derive(Clone, Debug)]
pub enum Inst {
    /// Match indicates that the program has reached a match state.
    ///
    /// The number in the match corresponds to the Nth logical regular
    /// expression in this program. This index is always 0 for normal regex
    /// programs. Values greater than 0 appear when compiling regex sets, and
    /// each match instruction gets its own unique value. The value corresponds
    /// to the Nth regex in the set.
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
}

// TODO(ethan): make this a config option to ExecBuilder
// The default value of 64 has been choosen by fairly
// haphazard benchmarking.
pub const RUN_QUEUE_RING_SIZE: usize = 64;

/// SkipInst is an instruction code in a Skip Regex program.
///
/// SkipInst mostly follows the pattern laid down by `prog.rs::Inst`
#[derive(Clone, Debug)]
pub enum SkipInst {
    /// Match indicates that the program has reached a match state.
    ///
    /// See prog.rs::Inst for more details.
    SkipMatch(usize),
    /// Save causes the program to save the current location of the input in
    /// the slot indicated by InstSave.
    SkipSave(InstSave),
    /// Split causes the program to diverge to one of two paths in the
    /// program, preferring goto1 in InstSplit.
    SkipSplit(InstSplit),

    /// See Char
    SkipByte(InstByte),

    /// See Ranges
    SkipBytes(InstBytes),

    /// See EmptyLook
    SkipEmptyLook(InstEmptyLook),

    /// Moves the current thread's string pointer forward by the
    /// given number of bytes
    SkipSkip(InstSkip),

    /// ScanLiteral tells the regex engine that it is safe to scan
    /// forward until it sees the given literal. This skip strategy
    /// is meant as an optimization to speed up kleene star (especially
    /// dotstars).
    SkipScanLiteral(InstScanLiteral),
}

/// Representation of the SkipByte instruction.
#[derive(Clone, Debug)]
pub struct InstByte {
    /// The next location to execute in the program if this instruction
    /// succeeds.
    pub goto: InstPtr,
    /// The character to test.
    pub c: u8,
}

/// Representation of the Skip instruction.
#[derive(Clone, Debug)]
pub struct InstSkip {
    /// The next location to execute in the program if this instruction
    /// succeeds.
    pub goto: InstPtr,
    /// The character to test.
    pub skip: usize,
}


/// Representation of the InstScanLiteral instruction.
#[derive(Clone, Debug)]
pub struct InstScanLiteral {
    /// The next location to execute in the program if this instruction
    /// succeeds.
    pub goto: InstPtr,
    /// The literal(s) to scan forward in the input for.
    pub literal: LiteralSearcher,
    /// A flag indicating if the engine should place the string
    /// pointer at the start of the literal or at the end. This
    /// allows us to handle the case where a terminating literal set
    /// is enclosed in a capture group.
    pub start: bool,
}


impl Inst {
    /// Returns true if and only if this is a match instruction.
    pub fn is_match(&self) -> bool {
        match *self {
            Inst::Match(_) => true,
            _ => false,
        }
    }
}

/// Representation of the Save instruction.
#[derive(Clone, Debug)]
pub struct InstSave {
    /// The next location to execute in the program.
    pub goto: InstPtr,
    /// The capture slot (there are two slots for every capture in a regex,
    /// including the zeroth capture for the entire match).
    pub slot: usize,
}

/// Representation of the Split instruction.
#[derive(Clone, Debug)]
pub struct InstSplit {
    /// The first instruction to try. A match resulting from following goto1
    /// has precedence over a match resulting from following goto2.
    pub goto1: InstPtr,
    /// The second instruction to try. A match resulting from following goto1
    /// has precedence over a match resulting from following goto2.
    pub goto2: InstPtr,
}

/// Representation of the `EmptyLook` instruction.
#[derive(Clone, Debug)]
pub struct InstEmptyLook {
    /// The next location to execute in the program if this instruction
    /// succeeds.
    pub goto: InstPtr,
    /// The type of zero-width assertion to check.
    pub look: EmptyLook,
}

/// The set of zero-width match instructions.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EmptyLook {
    /// Start of line or input.
    StartLine,
    /// End of line or input.
    EndLine,
    /// Start of input.
    StartText,
    /// End of input.
    EndText,
    /// Word character on one side and non-word character on other.
    WordBoundary,
    /// Word character on both sides or non-word character on both sides.
    NotWordBoundary,
    /// ASCII word boundary.
    WordBoundaryAscii,
    /// Not ASCII word boundary.
    NotWordBoundaryAscii,
}

/// Representation of the Char instruction.
#[derive(Clone, Debug)]
pub struct InstChar {
    /// The next location to execute in the program if this instruction
    /// succeeds.
    pub goto: InstPtr,
    /// The character to test.
    pub c: char,
}

/// Representation of the Ranges instruction.
#[derive(Clone, Debug)]
pub struct InstRanges {
    /// The next location to execute in the program if this instruction
    /// succeeds.
    pub goto: InstPtr,
    /// The set of Unicode scalar value ranges to test.
    pub ranges: Vec<(char, char)>,
}

impl InstRanges {
    /// Tests whether the given input character matches this instruction.
    pub fn matches(&self, c: Char) -> bool {
        // This speeds up the `match_class_unicode` benchmark by checking
        // some common cases quickly without binary search. e.g., Matching
        // a Unicode class on predominantly ASCII text.
        for r in self.ranges.iter().take(4) {
            if c < r.0 {
                return false;
            }
            if c <= r.1 {
                return true;
            }
        }
        self.ranges.binary_search_by(|r| {
            if r.1 < c {
                Ordering::Less
            } else if r.0 > c {
                Ordering::Greater
            } else {
                Ordering::Equal
            }
        }).is_ok()
    }

    /// Tests if two ranges could ever match at the same time.
    fn intersects(&self, r: &InstRanges) -> bool {
        let (shorter, longer) = if self.ranges.len() < r.ranges.len() {
            (self, r)
        } else {
            (r, self)
        };

        for &(start, end) in shorter.ranges.iter() {
            if longer.matches(Char::from(start))
                || longer.matches(Char::from(end)) {
                return true;
            }
        }

        false
    }

    /// Return the number of distinct characters represented by all of the
    /// ranges.
    pub fn num_chars(&self) -> usize {
        self.ranges.iter()
            .map(|&(s, e)| 1 + (e as u32) - (s as u32))
            .fold(0, |acc, len| acc + len)
            as usize
    }
}

/// Representation of the Bytes instruction.
#[derive(Clone, Debug)]
pub struct InstBytes {
    /// The next location to execute in the program if this instruction
    /// succeeds.
    pub goto: InstPtr,
    /// The start (inclusive) of this byte range.
    pub start: u8,
    /// The end (inclusive) of this byte range.
    pub end: u8,
}

impl InstBytes {
    /// Returns true if and only if the given byte is in this range.
    pub fn matches(&self, byte: u8) -> bool {
        self.start <= byte && byte <= self.end
    }

    fn intersects(&self, other: &InstBytes) -> bool {
        self.matches(other.start) || self.matches(other.end)
    }
}

#[cfg(test)]
mod tests {
    use super::{ExecBuilder, Exec};

    #[test]
    fn inter_null_different_lits() {
        let prog1 = ExecBuilder::new("foo").build().unwrap();
        let prog2 = ExecBuilder::new("bar").build().unwrap();

        // Nothing matches both /foo/ and /bar/
        assert!(Exec::intersection_is_empty(&prog1, &prog2));
    }

    #[test]
    fn inter_null_same_lits() {
        let prog1 = ExecBuilder::new("foo").build().unwrap();
        let prog2 = ExecBuilder::new("foo").build().unwrap();

        // "foo" `in` L(/foo/) `intersect` L(/foo/)
        assert!(! Exec::intersection_is_empty(&prog1, &prog2));
    }

    #[test]
    fn inter_null_lit_dotstar() {
        let prog1 = ExecBuilder::new("foo").build().unwrap();
        let prog2 = ExecBuilder::new(".*").build().unwrap();

        // "foo" `in` L(/foo/) `intersect` L(/.*/)
        assert!(! Exec::intersection_is_empty(&prog1, &prog2));
    }

    #[test]
    fn inter_null_fs_in_fstar() {
        let prog1 = ExecBuilder::new("ffff").build().unwrap();
        let prog2 = ExecBuilder::new("f*").build().unwrap();

        // "ffff" `in` L(/ffff/) `intersect` L(/f*/)
        assert!(! Exec::intersection_is_empty(&prog1, &prog2));
    }

    #[test]
    fn inter_null_union() {
        let prog1 = ExecBuilder::new("a|b").build().unwrap();
        let prog2 = ExecBuilder::new("b|c").build().unwrap();

        // "b" `in` L(/a|b/) `intersect` L(/b|c/)
        assert!(! Exec::intersection_is_empty(&prog1, &prog2));
    }

    #[test]
    fn inter_null_concat_union() {
        let prog1 = ExecBuilder::new("zz(?:a|b)").build().unwrap();
        let prog2 = ExecBuilder::new(".*(?:b|c)").build().unwrap();

        // "b" `in` L(/zz(?:a|b>/) `intersect` L(/.*(?:b|c)/)
        assert!(! Exec::intersection_is_empty(&prog1, &prog2));
    }

    #[test]
    fn inter_null_word_boundary() {
        let prog1 = ExecBuilder::new(r"\ba").build().unwrap();
        let prog2 = ExecBuilder::new(r"a").build().unwrap();
        let prog3 = ExecBuilder::new(r"b").build().unwrap();

        // "a" `in` L(/\ba/) `intersect` L(/a/)
        assert!(! Exec::intersection_is_empty(&prog1, &prog2));

        // L(/\ba/) `intersect` L(/b/) == emptyset
        assert!(Exec::intersection_is_empty(&prog1, &prog3));
    }

    #[test]
    fn inter_null_start_line() {
        let prog1 = ExecBuilder::new(r"^a").build().unwrap();
        let prog2 = ExecBuilder::new(r"a").build().unwrap();
        let prog3 = ExecBuilder::new(r"b").build().unwrap();

        // "a" `in` L(/\ba/) `intersect` L(/a/)
        assert!(! Exec::intersection_is_empty(&prog1, &prog2));

        // L(/\ba/) `intersect` L(/b/) == emptyset
        assert!(Exec::intersection_is_empty(&prog1, &prog3));
    }

    // TODO(ethan): quickcheck properties
}
