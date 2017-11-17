//
// File: `bench/src/captures.rs`
// Author: Ethan Pailes
//
// Benchmarks for parsing regex capture groups
//

use std::iter::repeat;
use test::Bencher;

// Inherit the configuration from `bench/src/bench.rs`
use Regex;
use Text;
use RegexBuilder;

macro_rules! bench_both {
    ($name_reg:ident, $name_skip:ident, $pattern:expr,
        $count:expr, $haystack:expr) => {
        bench_captures!($name_reg, Regex::new($pattern).unwrap(),
            $count, $haystack);
        bench_captures!($name_skip,
            RegexBuilder::new($pattern).skip_mode(true).build().unwrap(),
            $count, $haystack);
    }
}

// I've noticed the first microbenchmark being rather slow, so
// this guy is just here to knock the ice off the cache when
// running the capture benchmarks using the `cap_` benchmark
// filter (`bench/run rust-bytes cap_`).
bench_captures!(cap_aaaaaaaa, Regex::new("aaaa(bbbb)cccc").unwrap(), 1,
                String::from("aaaabbbbcccc"));

bench_both!(cap_reg_small, cap_skip_small, "aaaa(bbbb)cccc", 1,
                String::from("aaaabbbbcccc"));

// This is the strong point for skip regex. If we don't win here,
// something is seriously wrong.
bench_both!(cap_reg_large, cap_skip_large,
                format!("{}(bbbb){}",
                    repeat("aaaa").take(100).collect::<String>(),
                    repeat("cccc").take(100).collect::<String>()).as_str(),
                1,
                format!("{}bbbb{}",
                    repeat("aaaa").take(100).collect::<String>(),
                    repeat("cccc").take(100).collect::<String>()));


bench_both!(cap_reg_leading_dotstar, cap_skip_leading_dotstar,
                ".*(aaaa)", 1,
                format!("{}aaaa",
                        repeat("b").take(10).collect::<String>()));

// This guy has a very strange off-by-one error that I can't
// reproduce when I put it in a test.
/*
bench_both!(cap_first, cap_first_skip, "(aaaa)(bbbbbb)*", 1,
                format!("{}{}",
                        String::from("aaaa"),
                        repeat("bbbbbb").take(100).collect::<String>()));
                        */
