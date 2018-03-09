
extern crate regex;


macro_rules! skip_test {
    ($mod:ident, $make_regex:expr) => {
        mod $mod {
            use std::iter::repeat;

            use super::regex;
            use regex::internal::ExecBuilder;

            // This isn't required, but I don't want to be too abusive
            // in terms of code size.
            fn regex(r: &str) -> regex::bytes::Regex {
                $make_regex(r)
            }

            #[test]
            fn skip_lit() {
                let re = regex("aaaa");
                let caps = re.captures("aaaa".as_bytes()).unwrap();
                assert_eq!("aaaa".as_bytes(), &caps[0]);
            }

            // This is to sanity check the compiler's skip splitting logic.
            #[test]
            fn skip_longlit() {
                let it = repeat("a").take(100).collect::<String>();
                let re = regex(&it);
                let caps = re.captures(it.as_bytes()).unwrap();
                assert_eq!(it.as_bytes(), &caps[0]);
            }

            #[test]
            fn skip_cap() {
                let re = regex("aaaa(bbb)cc");
                let caps = re.captures(b"aaaabbbcc").unwrap();
                assert_eq!(b"aaaabbbcc", &caps[0]);
                assert_eq!(b"bbb", &caps[1]);
            }

            #[test]
            fn skip_branch() {
                let re = regex("aaa|(bbb)c|c");
                let caps = re.captures("aaa".as_bytes()).unwrap();
                assert_eq!(b"aaa", &caps[0]);

                let caps = re.captures("bbbc".as_bytes()).unwrap();
                assert_eq!(b"bbb", &caps[1]);
            }

            // TODO: "term1*term2" should just compile to scan(term2)
            
            // make sure we are handling the BranchType stuff around
            // repetitions correctly
            #[test]
            fn skip_repeat_branch_intersecting() {
                let re = regex("(?:aaaa)*b*(aa)");

                let caps = re.captures(b"aaaabbbbaa").unwrap();
                assert_eq!(b"aa", &caps[1]);
            }

            #[test]
            fn skip_repeat_branch_nonintersecting() {
                let re = regex("(bbbb)*c*(aa)aa");
                let caps = re.captures(b"bbbbaaaa").unwrap();
                assert_eq!(b"aa", &caps[2]);
            }

            #[test]
            fn skip_kleene_star_twoc() {
                let re = regex("c*c");
                let caps = re.captures("cc".as_bytes()).unwrap();
                assert_eq!(b"cc", &caps[0]);

                let caps = re.captures("ccc".as_bytes()).unwrap();
                assert_eq!(b"ccc", &caps[0]);
            }

            #[test]
            fn skip_kleene_star() {
                let re = regex("a*(bbb)c*c");
                let caps = re.captures("aaaaabbbccc".as_bytes()).unwrap();
                assert_eq!(b"aaaaabbbccc", &caps[0]);

                let caps = re.captures("bbbc".as_bytes()).unwrap();
                assert_eq!(b"bbb", &caps[1]);
            }

            #[test]
            fn skip_dotstar() {
                let re = regex(".*(a)");
                let haystack = format!("{}a", repeat("b").take(100).collect::<String>());
                let caps = re.captures(haystack.as_bytes()).unwrap();
                assert_eq!(haystack.as_bytes(), &caps[0]);
                assert_eq!(b"a", &caps[1]);
            }

            #[test]
            fn skip_leading_dotstar() {
                let re = regex(".*(aaaa)");
                let caps = re.captures(b"baaaa").unwrap();

                assert_eq!(b"aaaa", &caps[1]);
            }

            #[test]
            fn skip_kleene_star_twoc_lazy() {
                let re = regex("(c*?)c");
                let caps = re.captures(b"cc").unwrap();
                assert_eq!(b"c", &caps[1]);
            }

            #[test]
            fn skip_dotstar_compile_loop_bug() {
                regex(".*c");
            }

            #[test]
            fn skip_capture_repeat() {
                let re = regex("(?:a(b))*baz");
                let caps = re.captures(b"ababbaz").unwrap();
                assert_eq!(b"b", &caps[1]);
            }

            #[test]
            fn skip_branch_precidence() {
                let re = regex("a(.)|a(.)");
                let caps = re.captures(b"ax").unwrap();
                assert_eq!(b"x", &caps[1]);
            }

            #[test]
            fn skip_two_rep_caps() {
                let re = regex("(aaaa)(bbbbbb)*");
                let haystack = format!("{}{}",
                                  String::from("aaaa"),
                                  repeat("bbbbbb").take(100).collect::<String>());
                let caps = re.captures(haystack.as_bytes()).unwrap();
                println!("hslen={} caplen={}", haystack.len(), &caps[0].len());
                assert_eq!(haystack.as_bytes(), &caps[0]);
                assert_eq!("bbbbbb".as_bytes(), &caps[2]);
            }

            #[test]
            fn skip_astar_comma() {
                let re = regex("a*,(.).*");
                let caps = re.captures(b"a,foo,x").unwrap();
                assert_eq!(b"f", &caps[1]);
            }

            #[test]
            fn skip_branch_differentiation() {
                let re = regex("ab.(.)|ac(.).");
                let caps = re.captures(b"acxy").unwrap();
                assert_eq!(b"x", &caps[2]);
            }

            #[test]
            fn skip_multi_level_branch() {
                let re = regex("abc|def|(:?abr|bcn)");
                let caps = re.captures(b"abr").unwrap();
                assert_eq!(b"abr", &caps[0]);
            }

            #[test]
            fn skip_pathological() {
                let re = regex("(a?a?)aa");
                let caps = re.captures(b"aa").unwrap();
                assert_eq!(b"aa", &caps[0]);
            }

            #[test]
            fn skip_quad_scan() {
                let re = regex("(?:.*z|([az]*))b");
                let caps = re.captures(b"aaazab").unwrap();
                assert_eq!(b"aaaza", &caps[1]);
            }

            #[test]
            fn skip_start_end_text() {
                let re = regex("^a(b)a$");
                let caps = re.captures(b"aba").unwrap();
                assert_eq!(b"b", &caps[1]);
            }

            #[test]
            fn skip_word_boundary() {
                let re = regex(r"\b(test)\b.*");
                let caps = re.captures(b"test ing").unwrap();
                assert_eq!(b"test", &caps[1]);
            }

            #[test]
            fn skip_word_boundary2() {
                let re = regex(r" \b(test)\b.*");
                let caps = re.captures(b" test ing").unwrap();
                assert_eq!(b"test", &caps[1]);
            }

            #[test]
            fn skip_alternate_terminator() {
                let re = regex(r"a*(foo|bar)");
                let caps = re.captures(b"aaaaaaaafoo").unwrap();
                assert_eq!(b"foo", &caps[1]);
            }

            #[test]
            fn skip_idx_unwrapping_compiler_bug() {
                let _re = regex(r"(?:Chrome|CrMo|CriOS)/([.0-9]+)");
            }

            #[test]
            fn skip_trailing_dotstar_nocap() {
                let re = regex(r"blah(foo|bar)a[0-9].*");
                let caps = re.captures(b"blahbara4restof it").unwrap();
                assert_eq!(b"bar", &caps[1]);
            }

            #[test]
            fn skip_trailing_dotstar_cap() {
                let re = regex(r"blah(foo|bar)a[0-9](.*)");
                let caps = re.captures(b"blahbara4restof it").unwrap();
                assert_eq!(b"bar", &caps[1]);
                assert_eq!(b"restof it", &caps[2]);
            }

            #[test]
            fn skip_singleton_concat_literal_bug() {
                let re = regex(r"(a|b)y{1}");
                let caps = re.captures(b"ay").unwrap();
                assert_eq!(b"a", &caps[1]);
            }

        }
    }
}
