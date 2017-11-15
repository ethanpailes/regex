//
// File: `bench/src/captures.rs`
// Author: Ethan Pailes
//
// Benchmarks for regex parsing
//

use test::Bencher;

// USAGE: bench_captures!(name, pattern, groups, haystack);
//
// CONTRACT:
//   Given:
//     ident, the desired benchmarking function name
//     pattern : ::Regex, the regular expression to be executed
//     groups : usize, the number of capture groups
//     haystack : String, the string to search
//   bench_captures will benchmark how fast re.captures() produces
//   the capture groups in question.
macro_rules! bench_captures {
    ($name:ident, $pattern:expr, $count:expr, $haystack:expr) => {

        #[cfg(feature = "re-rust")]
        #[bench]
        fn $name(b: &mut Bencher) {
            use std::sync::Mutex;

            lazy_static! {
                static ref RE: Mutex<Regex> = Mutex::new($pattern);
                static ref TEXT: Mutex<Text> = Mutex::new(text!($haystack));
            };
            let re = RE.lock().unwrap();
            let text = TEXT.lock().unwrap();
            b.bytes = text.len() as u64;
            b.iter(|| {
                match re.captures(&text) {
                    None => assert!(false, "no captures"),
                    Some(caps) => assert_eq!($count + 1, caps.len()),
                }
            });
        }
    }
}


