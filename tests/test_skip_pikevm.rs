
extern crate regex;

use std::iter::repeat;

// There is only one valid question to ask a Skip Regex:
//    Given that this entire haystack matches, what are the capture
//    groups?
// Nothing else is a reasonable question. Unfortunatly, the semantics
// of this question are not quite the same as the question posed by
// the .captures() method on ordinary regex, so we can't really reuse
// the existing tests.


macro_rules! spike_re {
    ($re:expr) => {{
        // use regex::internal::ExecBuilder;
        use regex::bytes::RegexBuilder;
        RegexBuilder::new($re).skip_mode(true).build().unwrap()
    }}
}

#[test]
fn spike_lit() {
    let re = spike_re!("aaaa");
    let caps = re.captures("aaaa".as_bytes()).unwrap();
    assert_eq!("aaaa".as_bytes(), &caps[0]);
}

// This is to sanity check the compiler's skip splitting logic.
#[test]
fn spike_longlit() {
    let re = spike_re!("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
    let caps = re.captures("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa".as_bytes())
                 .unwrap();
    assert_eq!("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa".as_bytes(), &caps[0]);
}

#[test]
fn spike_cap() {
    let re = spike_re!("aaaa(bbb)cc");
    let caps = re.captures("aaaabbbcc".as_bytes()).unwrap();
    assert_eq!("aaaabbbcc".as_bytes(), &caps[0]);
    assert_eq!("bbb".as_bytes(), &caps[1]);
}

#[test]
fn spike_branch() {
    let re = spike_re!("aaa|(bbb)c|c");
    let caps = re.captures("aaa".as_bytes()).unwrap();
    assert_eq!("aaa".as_bytes(), &caps[0]);

    let caps = re.captures("bbbc".as_bytes()).unwrap();
    assert_eq!("bbb".as_bytes(), &caps[1]);
}

#[test]
fn spike_kleene_star_twoc() {
    let re = spike_re!("c*c");
    let caps = re.captures("cc".as_bytes()).unwrap();
    assert_eq!("cc".as_bytes(), &caps[0]);

    let caps = re.captures("ccc".as_bytes()).unwrap();
    assert_eq!("ccc".as_bytes(), &caps[0]);
}

#[test]
fn spike_kleene_star_twoc_lazy() {
    let re = spike_re!("c*?c");
    let caps = re.captures("cc".as_bytes()).unwrap();
    assert_eq!("c".as_bytes(), &caps[0]);

    let caps = re.captures("ccc".as_bytes()).unwrap();
    assert_eq!("c".as_bytes(), &caps[0]);
}

#[test]
fn spike_kleene_star() {
    let re = spike_re!("a*(bbb)c*c");
    let caps = re.captures("aaaaabbbccc".as_bytes()).unwrap();
    assert_eq!("aaaaabbbccc".as_bytes(), &caps[0]);

    let caps = re.captures("bbbc".as_bytes()).unwrap();
    assert_eq!("bbb".as_bytes(), &caps[1]);
}

#[test]
fn spike_two_rep_caps() {
    let re = spike_re!("(aaaa)(bbbbbb)*");
    let haystack = format!("{}{}",
                      String::from("aaaa"),
                      repeat("bbbbbb").take(100).collect::<String>());
    let caps = re.captures(haystack.as_bytes()).unwrap();
    assert_eq!(haystack.as_bytes(), &caps[0]);
    assert_eq!("bbbbbb".as_bytes(), &caps[2]);
}
