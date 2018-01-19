
extern crate regex;

use std::iter::repeat;

#[test]
fn skip_lit() {
    let re = regex!("aaaa");
    let caps = re.captures("aaaa".as_bytes()).unwrap();
    assert_eq!("aaaa".as_bytes(), &caps[0]);
}

// This is to sanity check the compiler's skip splitting logic.
#[test]
fn skip_longlit() {
    let re = regex!("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
    let caps = re.captures("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa".as_bytes())
                 .unwrap();
    assert_eq!("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa".as_bytes(), &caps[0]);
}

#[test]
fn skip_cap() {
    let re = regex!("aaaa(bbb)cc");
    let caps = re.captures("aaaabbbcc".as_bytes()).unwrap();
    assert_eq!("aaaabbbcc".as_bytes(), &caps[0]);
    assert_eq!("bbb".as_bytes(), &caps[1]);
}

#[test]
fn skip_branch() {
    let re = regex!("aaa|(bbb)c|c");
    let caps = re.captures("aaa".as_bytes()).unwrap();
    assert_eq!("aaa".as_bytes(), &caps[0]);

    let caps = re.captures("bbbc".as_bytes()).unwrap();
    assert_eq!("bbb".as_bytes(), &caps[1]);
}

#[test]
fn skip_kleene_star_twoc() {
    let re = regex!("c*c");
    let caps = re.captures("cc".as_bytes()).unwrap();
    assert_eq!("cc".as_bytes(), &caps[0]);

    let caps = re.captures("ccc".as_bytes()).unwrap();
    assert_eq!("ccc".as_bytes(), &caps[0]);
}

#[test]
fn skip_kleene_star() {
    let re = regex!("a*(bbb)c*c");
    let caps = re.captures("aaaaabbbccc".as_bytes()).unwrap();
    assert_eq!("aaaaabbbccc".as_bytes(), &caps[0]);

    let caps = re.captures("bbbc".as_bytes()).unwrap();
    assert_eq!("bbb".as_bytes(), &caps[1]);
}

#[test]
fn skip_dotstar() {
    let re = regex!(".*(a)");
    let haystack = format!("{}a", repeat("b").take(100).collect::<String>());
    let caps = re.captures(haystack.as_bytes()).unwrap();
    assert_eq!(haystack.as_bytes(), &caps[0]);
    assert_eq!("a".as_bytes(), &caps[1]);
}

#[test]
fn skip_kleene_star_twoc_lazy() {
    let re = regex!("c*?c");
    let caps = re.captures("cc".as_bytes()).unwrap();
    assert_eq!("c".as_bytes(), &caps[0]);

    let caps = re.captures(b"cccc").unwrap();
    assert_eq!("c".as_bytes(), &caps[0]);
}

#[test]
fn skip_dotstar_compile_loop_bug() {
    regex!(".*c");
}


#[test]
fn skip_capture_repeat() {
    let re = regex!("(?:a(b))*baz");
    let caps = re.captures(b"ababbaz").unwrap();
    assert_eq!(b"b", &caps[1]);
}

#[test]
fn skip_branch_precidence() {
    let re = regex!("a(.)|a(.)");
    let caps = re.captures(b"ax").unwrap();
    assert_eq!(b"x", &caps[1]);
}

#[test]
fn skip_two_rep_caps() {
    let re = regex!("(aaaa)(bbbbbb)*");
    let haystack = format!("{}{}",
                      String::from("aaaa"),
                      repeat("bbbbbb").take(100).collect::<String>());
    let caps = re.captures(haystack.as_bytes()).unwrap();
    println!("hslen={} caplen={}", haystack.len(), &caps[0].len());
    assert_eq!(haystack.as_bytes(), &caps[0]);
    assert_eq!("bbbbbb".as_bytes(), &caps[2]);
}

//
// Backlog of tests that fail or pass when I don't understand why
//

// fails because of bad scan opt
#[test]
fn skip_astar_comma() {
    let re = regex!("a*,(.)");
    let caps = re.captures(b"a,foo,x").unwrap();
    assert_eq!(b"f", &caps[1]);
}

// failes because of bad branch position optimization
#[test]
fn skip_branch_differentiation() {
    let re = regex!("ab.(.)|ac(.).");
    let caps = re.captures(b"acxy").unwrap();
    assert_eq!(b"x", &caps[2]);
}
