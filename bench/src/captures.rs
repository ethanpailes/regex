//
// File: `bench/src/captures.rs`
// Author: Ethan Pailes
//
// Benchmarks for parsing regex capture groups
//

use std::iter::repeat;
use test::Bencher;

use Regex;
use Text;
use regex::RegexBuilder;

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
// filter (`bench/run rust cap_`).
bench_captures!(cap_aaaaaaaa, Regex::new("aaaa(bbbb)cccc").unwrap(), 1,
                String::from("aaaabbbbcccc"));

// 360 / 440
//
// I suspect I'm loosing out on RunQueue overhead primarily.
bench_both!(cap_small, cap_small_skip, "aaaa(bbbb)cccc", 1,
                String::from("aaaabbbbcccc"));

// This guy has a very strange off-by-one error that I can't
// reproduce when I put it in a test.
bench_both!(cap_first, cap_first_skip, "(aaaa)(bbbbbb)*", 1,
                format!("{}{}",
                        String::from("aaaa"),
                        repeat("bbbbbb").take(100).collect::<String>()));
