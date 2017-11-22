// Tuned Boyer-Moore { ufast w/memchr, fwd + g, md2 }
//
// Uses an unrolled, fast skip loop
// Checks for matches with a guard and a forward comparison loop
// Uses the md2 (mini Sunday delta2) shift rule

#[macro_use]
#[cfg(test)]
extern crate quickcheck;

extern crate memchr;

mod freqs;

// cribbed from rust-lang/regex
use freqs::BYTE_FREQUENCIES;

use memchr::{memchr};

/// The interface to string searching algorithms
pub trait StringSearcher {
    /// Create a new string searcher, performing whatever
    /// compilation steps are required.
    fn new(needle: &[u8]) -> Self;

    /// Find the pattern in `haystack`, returning the offset
    /// of the start of the first occurrence of the pattern
    /// in `haystack`.
    fn find(&self, haystack: &[u8]) -> Option<usize>;
}

/// An implementation of Tuned Boyer-Moore as laid out by
/// Andrew Hume and Daniel Sunday in "Fast String Searching".
/// O(n) in the size of the input.
///
/// Fast string searching algorithms come in many variations,
/// but they can generally be described in terms of three main
/// components.
///
/// The skip loop is where the string searcher wants to spend
/// as much time as possible. Exactly which character in the
/// pattern the skip loop examines varies from algorithm to
/// algorithm, but in the simplest case this loop repeated
/// looks at the last character in the pattern and jumps
/// forward in the input if it is not in the pattern.
/// Robert Boyer and J Moore called this the "fast" loop in
/// their original paper.
///
/// The match loop is responsible for actually examining the
/// whole potentially matching substring. In order to fail
/// faster, the match loop sometimes has a guard test attached.
/// The guard test uses frequency analysis of the different
/// characters in the pattern to choose the least frequency
/// occurring character and use it to find match failures
/// as quickly as possible.
///
/// The shift rule governs how the algorithm will shuffle its
/// test window in the event of a failure during the match loop.
/// Certain shift rules allow the worst-case run time of the
/// algorithm to be shown to be O(n) in the size of the input
/// rather than O(nm) in the size of the input and the size
/// of the pattern (as naive Boyer-Moore is).
///
/// "Fast String Searching", in addition to presenting a tuned
/// algorithm, provides a comprehensive taxonomy of the many
/// different flavors of string searchers. Under that taxonomy
/// TBM, the algorithm implemented here, uses an unrolled fast
/// skip loop with memchr fallback, a forward match loop with guard,
/// and the mini Sunday's delta shift rule. To unpack that you'll have to
/// read the paper.
#[derive(Clone, Debug)]
pub struct BoyerMooreSearcher {
    /// The pattern we are going to look for in the haystack.
    pattern: Vec<u8>,

    /// The skip table for the skip loop.
    ///
    /// Maps the character at the end of the input 
    /// to a shift.
    skip_table: Vec<usize>,

    /// The guard character (least frequently occurring char).
    guard: u8,
    /// The reverse-index of the guard character in the pattern.
    guard_reverse_idx: usize,

    /// Daniel Sunday's mini generalized delta2 shift table.
    ///
    /// We use a skip loop, so we only have to provide a shift
    /// for the skip char (last char). This is why it is a mini
    /// shift rule.
    md2_shift: usize,
}

impl StringSearcher for BoyerMooreSearcher {
    fn new(pattern: &[u8]) -> Self {
        debug_assert!(pattern.len() > 0);

        let (g, gi) = Self::select_guard(pattern);
        BoyerMooreSearcher {
            pattern: Vec::from(pattern),
            skip_table: Self::compile_skip_table(pattern),
            guard: g,
            guard_reverse_idx: gi,
            md2_shift: Self::compile_md2_shift(pattern),
        }
    }

    #[inline(always)] // for inlining across crates
    fn find(&self, haystack: &[u8]) -> Option<usize> {
        debug_assert!(haystack.len() >= self.pattern.len());

        let mut window_end = self.pattern.len() - 1;

        // I stole this from the GNU grep source. It is a way
        // to do correct loop unrolling without having to place
        // a crashpad of terminating charicters at the end in
        // the way described in the Fast String Searching paper.
        let num_unroll = 10;
        // 1 for the initial position, and 1 for the md2 shift
        let short_circut = (num_unroll + 2) * self.pattern.len();

        if haystack.len() > short_circut {
            // just 1 for the md2 shift
            let backstop = haystack.len() - ((num_unroll + 1) * self.pattern.len());
            loop {
                window_end = match self.skip_loop(haystack, window_end) {
                    Some(i) => i,
                    None => return None,
                };
                if window_end >= backstop {
                    break;
                }

                if self.check_match(haystack, window_end) {
                    return Some(window_end - (self.pattern.len() - 1));
                } else {
                    window_end += self.md2_shift;
                    continue;
                }
            }
        }

        // now process the input after the backstop
        while window_end < haystack.len() {
            let mut skip = self.skip_table[haystack[window_end] as usize];
            if skip == 0 {
                if self.check_match(haystack, window_end) {
                    return Some(window_end - (self.pattern.len() - 1));
                } else {
                    skip = self.md2_shift;
                }
            }
            window_end += skip;
        }

        None
    }
}

impl BoyerMooreSearcher {
    /// Check to see if there is a match at the given position
    #[inline]
    fn check_match(&self, haystack: &[u8], window_end: usize) -> bool {
        // guard test
        if haystack[window_end - self.guard_reverse_idx] != self.guard {
            return false;
        }

        // match loop
        let window_start = window_end - (self.pattern.len() - 1);
        for i in 0..self.pattern.len() {
            if self.pattern[i] != haystack[window_start + i] {
                return false;
            }
        }

        true
    }

    /// Skip forward according to the shift table.
    #[inline]
    fn skip_loop(&self,
        haystack: &[u8],
        mut window_end: usize
    ) -> Option<usize> {
        use std::mem;

        let window_end_snapshot = window_end;
        let skip_of = |we: usize| -> usize {
            /* This might make it faster, but I'm not convinced.
            unsafe {
                *self.skip_table.get_unchecked(
                    *haystack.get_unchecked(we) as usize)
            }
            */
            self.skip_table[haystack[we] as usize]
        };

        loop {
            let mut skip = skip_of(window_end); window_end += skip;
            skip = skip_of(window_end); window_end += skip;
            if skip != 0 {
                skip = skip_of(window_end); window_end += skip;
                skip = skip_of(window_end); window_end += skip;
                skip = skip_of(window_end); window_end += skip;
                if skip != 0 {
                    skip = skip_of(window_end); window_end += skip;
                    skip = skip_of(window_end); window_end += skip;
                    skip = skip_of(window_end); window_end += skip;
                    if skip != 0 {
                        skip = skip_of(window_end); window_end += skip;
                        skip = skip_of(window_end); window_end += skip;

                        // If ten iterations did not make at least 16 words
                        // worth of progress, we just fall back on memchr.
                        if window_end - window_end_snapshot >
                             16 * mem::size_of::<usize>() {
                            continue; // we made enough progress
                        } else {
                            window_end -= 1; // in case we are already there
                            match memchr(self.guard, &haystack[window_end..]) {
                                None => return None,
                                Some(g_idx) => {
                                    return Some(window_end + g_idx + self.guard_reverse_idx);
                                }
                            }
                        }
                    }
                }
            }

            return Some(window_end);
        }
    }

    /// Computer the ufast skip table
    fn compile_skip_table(pattern: &[u8]) -> Vec<usize> {
        let mut tab = vec![pattern.len(); 256];

        // For every char in the pattern, we write a skip
        // that will line us up with the rightmost occurrence.
        //
        // Note that the sentinel (0) is written by the last
        // loop iteration.
        for (i, c) in pattern.iter().enumerate() {
            tab[*c as usize] = (pattern.len() - 1) - i;
        }

        tab
    }

    /// Select the guard character based off of the precomputed
    /// frequency table.
    fn select_guard(pattern: &[u8]) -> (u8, usize) {
        fn freq_rank(b: u8) -> usize { BYTE_FREQUENCIES[b as usize] as usize }

        let mut rarest = pattern[0];
        let mut rarest_rev_idx = pattern.len() - 1;
        for (i, c) in pattern.iter().enumerate() {
            if freq_rank(*c) < freq_rank(rarest) {
                rarest = *c;
                rarest_rev_idx = (pattern.len() - 1) - i;
            }
        }

        (rarest, rarest_rev_idx)
    }

    /// If there is another occurrence of the skip
    /// char, shift to it, otherwise just shift to
    /// the next window.
    fn compile_md2_shift(pattern: &[u8]) -> usize {
        let shiftc = *pattern.last().unwrap();

        // For a pattern of length 1 we will never apply the
        // shift rule, so we use a poison value.
        if pattern.len() == 1 {
            return 0xDEADBEAF;
        }

        let mut i = pattern.len() - 2;
        while i > 0 {
            if pattern[i] == shiftc {
                return (pattern.len() - 1) - i;
            }
            i -= 1;
        }

        // The skip char never re-occurs in the pattern, so
        // we can just shift the whole window length.
        pattern.len() - 1
    }
}

/// memchr is really, really fast. This searcher uses the frequency
/// tricks from traditional fast string search algorithms to choose
/// good target characters, and then just lets memchr do its thing.
/// If your pattern is short, you probably want this guy.
pub struct MemchrSearcher {
    /// The pattern.
    pat: Vec<u8>,
    /// The number of Unicode characters in the pattern. This is useful for
    /// determining the effective length of a pattern when deciding which
    /// optimizations to perform. A trailing incomplete UTF-8 sequence counts
    /// as one character.
    char_len: usize,
    /// The rarest byte in the pattern, according to pre-computed frequency
    /// analysis.
    rare1: u8,
    /// The offset of the rarest byte in `pat`.
    rare1i: usize,
    /// The second rarest byte in the pattern, according to pre-computed
    /// frequency analysis. (This may be equivalent to the rarest byte.)
    ///
    /// The second rarest byte is used as a type of guard for quickly detecting
    /// a mismatch after memchr locates an instance of the rarest byte. This
    /// is a hedge against pathological cases where the pre-computed frequency
    /// analysis may be off. (But of course, does not prevent *all*
    /// pathological cases.)
    rare2: u8,
    /// The offset of the second rarest byte in `pat`.
    rare2i: usize,
}

impl StringSearcher for MemchrSearcher {
    fn new(pat: &[u8]) -> Self {
        fn freq_rank(b: u8) -> usize { BYTE_FREQUENCIES[b as usize] as usize }

        if pat.is_empty() {
            return Self::empty();
        }

        // Find the rarest two bytes. Try to make them distinct (but it's not
        // required).
        let mut rare1 = pat[0];
        let mut rare2 = pat[0];
        for b in pat[1..].iter().cloned() {
            if freq_rank(b) < freq_rank(rare1) {
                rare1 = b;
            }
        }
        for &b in pat.iter() {
            if rare1 == rare2 {
                rare2 = b
            } else if b != rare1 && freq_rank(b) < freq_rank(rare2) {
                rare2 = b;
            }
        }

        // And find the offsets of their last occurrences.
        let rare1i = pat.iter().rposition(|&b| b == rare1).unwrap();
        let rare2i = pat.iter().rposition(|&b| b == rare2).unwrap();

        let char_len = Self::char_len_lossy(&pat);
        Self {
            pat: Vec::from(pat),
            char_len: char_len,
            rare1: rare1,
            rare1i: rare1i,
            rare2: rare2,
            rare2i: rare2i,
        }
    }

    #[inline(always)] // reduces constant overhead
    fn find(&self, haystack: &[u8]) -> Option<usize> {
        let pat = &*self.pat;
        if haystack.len() < pat.len() || pat.is_empty() {
            return None;
        }
        let mut i = self.rare1i;
        while i < haystack.len() {
            i += match memchr(self.rare1, &haystack[i..]) {
                None => return None,
                Some(i) => i,
            };
            let start = i - self.rare1i;
            let end = start + pat.len();
            if end > haystack.len() {
                return None;
            }
            let aligned = &haystack[start..end];
            if aligned[self.rare2i] == self.rare2 && aligned == &*self.pat {
                return Some(start);
            }
            i += 1;
        }
        None
    }
}

impl MemchrSearcher {
    fn empty() -> Self {
        Self {
            pat: vec![],
            char_len: 0,
            rare1: 0,
            rare1i: 0,
            rare2: 0,
            rare2i: 0,
        }
    }

    fn char_len_lossy(bytes: &[u8]) -> usize {
        String::from_utf8_lossy(bytes).chars().count()
    }

    #[inline(always)] // reduces constant overhead
    pub fn is_suffix(&self, text: &[u8]) -> bool {
        if text.len() < self.len() {
            return false;
        }
        text[text.len() - self.len()..] == *self.pat
    }

    pub fn len(&self) -> usize {
        self.pat.len()
    }

    pub fn char_len(&self) -> usize {
        self.char_len
    }
}


#[cfg(test)]
mod tests {
    use super::{BoyerMooreSearcher, MemchrSearcher, StringSearcher};

    //
    // Unit tests
    //

    // The "hello, world" of string searching
    #[test]
    fn find_subs() {
        let searcher = BoyerMooreSearcher::new(b"pattern");
        let haystack = b"I keep seeing patterns in this text";
        assert_eq!(14, searcher.find(haystack).unwrap());
    }

    #[test]
    fn find_no_subs() {
        let searcher = BoyerMooreSearcher::new(b"pattern");
        let haystack = b"I keep seeing needles in this text";
        assert_eq!(None, searcher.find(haystack));
    }

    #[test]
    fn skip_reset_bug() {
        let haystack = vec![0, 0, 0, 0, 0, 1, 1, 0];
        let needle = vec![0, 1, 1, 0];

        let searcher = BoyerMooreSearcher::new(needle.as_slice());
        let offset = searcher.find(haystack.as_slice()).unwrap();
        assert_eq!(4, offset);
    }

    #[test]
    fn backstop_underflow_bug() {
        let haystack = vec![0, 0];
        let needle = vec![0, 0];

        let searcher = BoyerMooreSearcher::new(needle.as_slice());
        let offset = searcher.find(haystack.as_slice()).unwrap();
        assert_eq!(0, offset);
    }

    //
    // QuickCheck properties
    //

    use quickcheck::TestResult;

    fn naive_find(needle: &[u8], haystack: &[u8]) -> Option<usize> {
        assert!(needle.len() <= haystack.len());

        for i in 0..(haystack.len() - needle.len()) {
            if haystack[i] == needle[0]
                && &haystack[i..(i+needle.len())] == needle {
                return Some(i)
            }
        }

        None
    }

    quickcheck! {
        fn qc_equals_nieve_find(pile1: Vec<u8>, pile2: Vec<u8>) -> TestResult {
            if pile1.len() == 0 || pile2.len() == 0 {
                return TestResult::discard();
            }

            let (needle, haystack) = if pile1.len() < pile2.len() {
                (pile1.as_slice(), pile2.as_slice())
            } else {
                (pile2.as_slice(), pile1.as_slice())
            };
            
            let searcher = BoyerMooreSearcher::new(needle);
            TestResult::from_bool(
                searcher.find(haystack) == naive_find(needle, haystack))
        }

        fn qc_equals_memchr(pile1: Vec<u8>, pile2: Vec<u8>) -> TestResult {
            if pile1.len() == 0 || pile2.len() == 0 {
                return TestResult::discard();
            }

            let (needle, haystack) = if pile1.len() < pile2.len() {
                (pile1.as_slice(), pile2.as_slice())
            } else {
                (pile2.as_slice(), pile1.as_slice())
            };
            
            let searcher = BoyerMooreSearcher::new(needle);
            let memchr_searcher = MemchrSearcher::new(needle);
            TestResult::from_bool(
                searcher.find(haystack) == memchr_searcher.find(haystack))
        }

        fn qc_finds_trailing_needle(
            haystack_pre: Vec<u8>,
            needle: Vec<u8>
        ) -> TestResult {
            if needle.len() == 0 {
                return TestResult::discard();
            }

            let mut haystack = haystack_pre.clone();
            let searcher = BoyerMooreSearcher::new(needle.as_slice());

            if haystack.len() > needle.len() &&
                searcher.find(haystack.as_slice()).is_some() {
                return TestResult::discard();
            }

            haystack.extend(needle);

            TestResult::from_bool(
                searcher.find(haystack.as_slice())
                        .map(|x| x == haystack_pre.len())
                        .unwrap_or(false))
        }

        fn qc_finds_first(needle: Vec<u8>) -> TestResult {
            if needle.len() == 0 {
                return TestResult::discard();
            }

            let mut haystack = needle.clone();
            let searcher = BoyerMooreSearcher::new(needle.as_slice());
            haystack.extend(needle);

            TestResult::from_bool(
                searcher.find(haystack.as_slice())
                        .map(|x| x == 0)
                        .unwrap_or(false))
        }
    }
}
