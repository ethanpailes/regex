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
            .bytes(true)
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
            .bytes(true)
            .build()
            .map(regex::bytes::Regex::from)
            .unwrap()
    }}
}

/////////////////////////////////////////////////////////////////////////
//
//                    Skip Pike Engine 
//
/////////////////////////////////////////////////////////////////////////

#[cfg(feature = "captures-skip-pike-none")]
macro_rules! regex {
    ($pattern:expr) => {{
        use regex::internal::ExecBuilder;
        ExecBuilder::new($pattern)
            .skip_pikevm()
            .skip_dotstar_term_opt(false)
            .skip_estar_term_opt(false)
            .skip_skip_lit_opt(false)
            .only_utf8(false)
            .build()
            .map(regex::bytes::Regex::from)
            .unwrap()
    }}
}

#[cfg(feature = "captures-skip-pike-ds")]
macro_rules! regex {
    ($pattern:expr) => {{
        use regex::internal::ExecBuilder;
        ExecBuilder::new($pattern)
            .skip_pikevm()
            .skip_estar_term_opt(false)
            .skip_skip_lit_opt(false)
            .only_utf8(false)
            .build()
            .map(regex::bytes::Regex::from)
            .unwrap()
    }}
}

#[cfg(feature = "captures-skip-pike-es")]
macro_rules! regex {
    ($pattern:expr) => {{
        use regex::internal::ExecBuilder;
        ExecBuilder::new($pattern)
            .skip_pikevm()
            .skip_dotstar_term_opt(false)
            .skip_skip_lit_opt(false)
            .only_utf8(false)
            .build()
            .map(regex::bytes::Regex::from)
            .unwrap()
    }}
}

#[cfg(feature = "captures-skip-pike-sl")]
macro_rules! regex {
    ($pattern:expr) => {{
        use regex::internal::ExecBuilder;
        ExecBuilder::new($pattern)
            .skip_pikevm()
            .skip_dotstar_term_opt(false)
            .skip_estar_term_opt(false)
            .only_utf8(false)
            .build()
            .map(regex::bytes::Regex::from)
            .unwrap()
    }}
}

#[cfg(feature = "captures-skip-pike-ds-es")]
macro_rules! regex {
    ($pattern:expr) => {{
        use regex::internal::ExecBuilder;
        ExecBuilder::new($pattern)
            .skip_pikevm()
            .skip_skip_lit_opt(false)
            .only_utf8(false)
            .build()
            .map(regex::bytes::Regex::from)
            .unwrap()
    }}
}

#[cfg(feature = "captures-skip-pike-ds-sl")]
macro_rules! regex {
    ($pattern:expr) => {{
        use regex::internal::ExecBuilder;
        ExecBuilder::new($pattern)
            .skip_pikevm()
            .skip_estar_term_opt(false)
            .only_utf8(false)
            .build()
            .map(regex::bytes::Regex::from)
            .unwrap()
    }}
}

#[cfg(feature = "captures-skip-pike-es-sl")]
macro_rules! regex {
    ($pattern:expr) => {{
        use regex::internal::ExecBuilder;
        ExecBuilder::new($pattern)
            .skip_pikevm()
            .skip_dotstar_term_opt(false)
            .only_utf8(false)
            .build()
            .map(regex::bytes::Regex::from)
            .unwrap()
    }}
}

#[cfg(feature = "captures-skip-pike-ds-es-sl")]
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

/////////////////////////////////////////////////////////////////////////
//
//                    Skip Backtrack Engine
//
/////////////////////////////////////////////////////////////////////////

#[cfg(feature = "captures-skip-backtrack-none")]
macro_rules! regex {
    ($pattern:expr) => {{
        use regex::internal::ExecBuilder;
        ExecBuilder::new($pattern)
            .skip_backtrack()
            .skip_estar_term_opt(false)
            .skip_dotstar_term_opt(false)
            .skip_skip_lit_opt(false)
            .only_utf8(false)
            .build()
            .map(regex::bytes::Regex::from)
            .unwrap()
    }}
}

#[cfg(feature = "captures-skip-backtrack-ds")]
macro_rules! regex {
    ($pattern:expr) => {{
        use regex::internal::ExecBuilder;
        ExecBuilder::new($pattern)
            .skip_backtrack()
            .skip_estar_term_opt(false)
            .skip_skip_lit_opt(false)
            .only_utf8(false)
            .build()
            .map(regex::bytes::Regex::from)
            .unwrap()
    }}
}

#[cfg(feature = "captures-skip-backtrack-es")]
macro_rules! regex {
    ($pattern:expr) => {{
        use regex::internal::ExecBuilder;
        ExecBuilder::new($pattern)
            .skip_backtrack()
            .skip_dotstar_term_opt(false)
            .skip_skip_lit_opt(false)
            .only_utf8(false)
            .build()
            .map(regex::bytes::Regex::from)
            .unwrap()
    }}
}

#[cfg(feature = "captures-skip-backtrack-sl")]
macro_rules! regex {
    ($pattern:expr) => {{
        use regex::internal::ExecBuilder;
        ExecBuilder::new($pattern)
            .skip_backtrack()
            .skip_estar_term_opt(false)
            .skip_dotstar_term_opt(false)
            .only_utf8(false)
            .build()
            .map(regex::bytes::Regex::from)
            .unwrap()
    }}
}

#[cfg(feature = "captures-skip-backtrack-ds-es")]
macro_rules! regex {
    ($pattern:expr) => {{
        use regex::internal::ExecBuilder;
        ExecBuilder::new($pattern)
            .skip_backtrack()
            .skip_skip_lit_opt(false)
            .only_utf8(false)
            .build()
            .map(regex::bytes::Regex::from)
            .unwrap()
    }}
}

#[cfg(feature = "captures-skip-backtrack-ds-sl")]
macro_rules! regex {
    ($pattern:expr) => {{
        use regex::internal::ExecBuilder;
        ExecBuilder::new($pattern)
            .skip_backtrack()
            .skip_estar_term_opt(false)
            .only_utf8(false)
            .build()
            .map(regex::bytes::Regex::from)
            .unwrap()
    }}
}

#[cfg(feature = "captures-skip-backtrack-es-sl")]
macro_rules! regex {
    ($pattern:expr) => {{
        use regex::internal::ExecBuilder;
        ExecBuilder::new($pattern)
            .skip_backtrack()
            .skip_dotstar_term_opt(false)
            .only_utf8(false)
            .build()
            .map(regex::bytes::Regex::from)
            .unwrap()
    }}
}

#[cfg(feature = "captures-skip-backtrack-ds-es-sl")]
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

/////////////////////////////////////////////////////////////////////////
//
//                    Skip Backtrack w/validation Engine
//
/////////////////////////////////////////////////////////////////////////

#[cfg(feature = "captures-skip-backtrack-validation")]
macro_rules! regex {
    ($pattern:expr) => {{
        use regex::internal::ExecBuilder;
        ExecBuilder::new($pattern)
            .skip_backtrack()
            .skip_validate(true)
            .only_utf8(false)
            .build()
            .map(regex::bytes::Regex::from)
            .unwrap()
    }}
}

/////////////////////////////////////////////////////////////////////////
//
//                             Benchmarks
//
/////////////////////////////////////////////////////////////////////////

// This is the strong point for skip regex. If we don't win here,
// something is seriously wrong.
//
// expectation: major win for skipping.
bench_captures!(cap_a_big_skip, 1,
    |scale| 
        regex!(format!(r"{}(bbbb){}",
            repeat("aaaa").take(scale).collect::<String>(),
            repeat("cccc").take(scale).collect::<String>()).as_str()),
    |scale| format!("{}bbbb{}",
                repeat("aaaa").take(scale).collect::<String>(),
                repeat("cccc").take(scale).collect::<String>()));

// I think this guy is a more promising optimization.
//
// expectation: major win for ND scanning
bench_captures!(cap_leading_dotstar, 1,
    |_| regex!(r".*(aaaa)"),
    |scale| format!("{}aaaa", repeat("b").take(scale).collect::<String>()));

bench_captures!(cap_dotstar_bounce, 1,
    |_| regex!(r".*(a)"),
    |scale| format!("{}", repeat("ca").take(scale).collect::<String>()));

// expectation: major win for direct scanning
bench_captures!(cap_leading_estar, 1,
    |_| regex!(r"a*foo(bar)"),
    |scale| format!("{}foobar", repeat("a").take(scale).collect::<String>()));

// expectation: modest win for skipping
bench_captures!(cap_repeated_alternates, 1,
    |_| regex!(r"(?:(?:a|bb)(?:c|dd)(?:e|ff)(?:g|hh)(?:i|jj)(?:k|ll)(?:m|nn)(?:o|pp))*(zz)"),
    |scale| format!("{}zz", repeat("acegikmo").take(scale).collect::<String>()));

// The goal here is to blow up the bitset on the bounded backtracker
// and make it perform poorly. The bitset usage is (regex-size * input-size),
// so a bigger regex really helps. We also use a repetition that can't
// be optimized.
//
// expectation: modest win for skipping
bench_captures!(cap_really_big_noscan, 1,
    |_| regex!(r"a*(a|b|c|d|e|f|h|i|j|k|l|m|n|o|p|q|r|s|t|u|v)(?:w)y{1}x{2}z{3}"),
    |scale| format!("{}awyxxzzz", repeat("a").take(scale).collect::<String>()));

// The goal here is to see what happens for a pathological case.
//
// expectation: The backtracker won't do well (but the bounded backtracker
// should do fine).
bench_captures!(cap_pathological, 1,
     |scale| regex!(format!(r"({}){}",
                 repeat("a?").take(scale / 1000).collect::<String>(),
                 repeat("a").take(scale / 1000).collect::<String>()).as_str()),
     |scale| repeat("a").take(scale / 1000).collect::<String>());

// TODO: this can't be testing what I want it to be testing
// bench_captures!(cap_quad_scan, 1,
//    |_| regex!("(?:.*z|([az]*))b"),
//    |scale| format!("{}zab", repeat("a").take(scale).collect::<String>()));

bench_captures!(cap_first, 2,
    |_| regex!("(aaaa)(bbbbbb)*"),
    |scale| format!("aaaa{}", repeat("bbbbbb").take(scale).collect::<String>()));

// This guy is here to test my hypothesis that we are seeing a big
// win for skipping just because it lets us cut down on memory traffic
//
// expectation: very small win for skipping.
bench_captures!(cap_justone, 1, |_| regex!("(a)"), |_| "a".to_string());

// The intersecting branches here should force the skip compiler
// to emit code that is pretty equivalent to the standard engine.
//
// expectation: very similar perf
bench_captures!(cap_no_opt, 1,
    |_| regex!(r"(ab|ac)*"),
    |scale| repeat("ab").take(scale).collect::<String>());

// expectation: the a+ trailing
bench_captures!(cap_aplus_trailing, 1,
    |_| regex!(r"(a+).*"),
    |scale| format!("{}{}",
        repeat("a").take(scale).collect::<String>(),
        repeat("b").take(scale).collect::<String>()));
