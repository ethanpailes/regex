//
// File: `bench/src/captures.rs`
// Author: Ethan Pailes
//
// Benchmarks for parsing regex capture groups
//

extern crate regex;

use std::iter::repeat;
use test::Bencher;

// Inherit the configuration from `bench/src/bench.rs` (which uses
// include! to splice this file in).
use Regex;
use Text;


// A macro for constructing a regular expression. This is the only
// thing that needs to change when flipping through different
// implimentations for perf comparisons.
//
// The implimentation depends on what we want to test
#[cfg(feature = "captures-baseline-backtrack")]
macro_rules! regex {
    ($pattern:expr) => {{
        use regex::internal::ExecBuilder;
        ExecBuilder::new($pattern)
            .bounded_backtracking()
            .only_utf8(false)
            .build()
            .map(regex::bytes::Regex::from)
            .unwrap()
    }}
}

#[cfg(feature = "captures-baseline-pike")]
macro_rules! regex {
    ($pattern:expr) => {{
        use regex::internal::ExecBuilder;
        ExecBuilder::new($pattern)
            .nfa()
            .only_utf8(false)
            .build()
            .map(regex::bytes::Regex::from)
            .unwrap()
    }}
}

#[cfg(feature = "captures-skip-pike")]
macro_rules! regex {
    ($pattern:expr) => {{
        use regex::internal::ExecBuilder;
        ExecBuilder::new($pattern)
            .skip_pikevm()
            .only_utf8(false)
            .build()
            .map(regex::bytes::Regex::from)
            .unwrap()
    }}
}
#[cfg(feature = "captures-skip-backtrack")]
macro_rules! regex {
    ($pattern:expr) => {{
        use regex::internal::ExecBuilder;
        ExecBuilder::new($pattern)
            .skip_backtrack()
            .only_utf8(false)
            .build()
            .map(regex::bytes::Regex::from)
            .unwrap()
    }}
}

// I've noticed the first microbenchmark being rather slow, so
// this guy is just here to knock the ice off the cache when
// running the capture benchmarks using the `cap_` benchmark
// filter (`bench/run rust-bytes cap_`).
bench_captures!(cap_aaaaaaaa, regex!("aaaa(bbbb)cccc"), 1,
                String::from("aaaabbbbcccc"));

// expectation: moderate win for skipping
bench_captures!(cap_small, regex!("aaaa(bbbb)cccc"), 1,
                String::from("aaaabbbbcccc"));

// This is the strong point for skip regex. If we don't win here,
// something is seriously wrong.
//
// expectation: major iwn for skipping.
bench_captures!(cap_large,
    regex!(format!("{}(bbbb){}",
        repeat("aaaa").take(100).collect::<String>(),
        repeat("cccc").take(100).collect::<String>()).as_str()),
    1,
    format!("{}bbbb{}",
        repeat("aaaa").take(100).collect::<String>(),
        repeat("cccc").take(100).collect::<String>()));

// I think this guy is a more promising optimization.
//
// expectation: major win for ND scanning
bench_captures!(cap_leading_dotstar,
    regex!(".*(aaaa)"),
    1,
    format!("{}aaaa", repeat("b").take(1000).collect::<String>()));

// TODO: issue 8
// expectation: major win for direct scanning
bench_captures!(cap_leading_noncontaining_estar,
    regex!("a*because(why)not"),
    1,
    format!("{}becausewhynot", repeat("a").take(1000).collect::<String>()));

// TODO: issue 9
// expectation: modest win for skipping
bench_captures!(cap_repeated_alternates,
    regex!("(?:a|b)(?:c|d)(?:e|f)(?:g|h)(?:i|j)(?:k|l)(?:m|n)(?:o|p)(zz)"),
    1,
    "adehilmpzz".to_string());

// The goal here is to blow up the bitset on the bounded backtracker
// and make it perform poorly. The bitset usage is (regex-size * input-size),
// so a bigger regex really helps. We also use a repetition that can't
// be optimized.
//
// TODO: issue 11 
// expectation: modest win for skipping
bench_captures!(cap_really_big_noscan,
    regex!("a*(a|b|c|d|e|f|h|i|j|k|l|m|n|o|p|q|r|s|t|u|v)(?:w)y{1}x{2}z{3}"),
    1,
    format!("{}awyxxzzz", repeat("a").take(100000).collect::<String>()));

// The goal here is to see what happens for a pathological case.
//
// expectation: The backtracker won't do well (but the bounded backtracker
// should do fine).
bench_captures!(cap_pathological,
    regex!("(a?a?a?a?a?a?a?a?a?a?)aaaaaaaaaa"),
    1,
    "aaaaaaaaaa".to_string());

// Is this faster for the PikeVM than the backtracker because the
// PikeVM is breadth-first while the backtracker is depth-first?
bench_captures!( cap_quad_scan, regex!("(?:.*z|([az]*))b"), 1,
    format!("{}zab",
        repeat("a").take(10000).collect::<String>()));

bench_captures!(cap_first, regex!("(aaaa)(bbbbbb)*"), 2,
    format!("aaaa{}", repeat("bbbbbb").take(100).collect::<String>()));

// This guy is here to test my hypothesis that we are seeing a big
// win for skipping just because it lets us cut down on memory traffic
//
// expectation: very small win for skipping.
bench_captures!(cap_justone, regex!("(a)"), 1, "a".to_string());

// The intersecting branches here should force the skip compiler
// to emit code that is pretty equivalent to the standard engine.
//
// expectation: very similar perf
bench_captures!(cap_justtwo_branch, regex!("(ab|ac)"), 1, "ab".to_string());
