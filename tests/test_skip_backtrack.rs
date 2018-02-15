
extern crate regex;

#[macro_use] mod skip;

skip_test!(regex_all_opt_validation, |re| {
    ExecBuilder::new(re)
        .skip_backtrack()
        .skip_validate(true)
        .only_utf8(false)
        .build()
        .map(regex::bytes::Regex::from)
        .unwrap()
});

skip_test!(regex_all_opt, |re| {
    ExecBuilder::new(re)
        .skip_backtrack()
        .only_utf8(false)
        .build()
        .map(regex::bytes::Regex::from)
        .unwrap()
});

skip_test!(regex_dotstar_off, |re| {
    ExecBuilder::new(re)
        .skip_backtrack()
        .skip_dotstar_term_opt(false)
        .only_utf8(false)
        .build()
        .map(regex::bytes::Regex::from)
        .unwrap()
});

skip_test!(regex_estar_off, |re| {
    ExecBuilder::new(re)
        .skip_backtrack()
        .skip_estar_term_opt(false)
        .only_utf8(false)
        .build()
        .map(regex::bytes::Regex::from)
        .unwrap()
});

skip_test!(regex_skip_lit_off, |re| {
    ExecBuilder::new(re)
        .skip_backtrack()
        .skip_skip_lit_opt(false)
        .only_utf8(false)
        .build()
        .map(regex::bytes::Regex::from)
        .unwrap()
});

skip_test!(regex_dotstar_estar_off, |re| {
    ExecBuilder::new(re)
        .skip_backtrack()
        .skip_dotstar_term_opt(false)
        .skip_estar_term_opt(false)
        .only_utf8(false)
        .build()
        .map(regex::bytes::Regex::from)
        .unwrap()
});

skip_test!(regex_dotstar_skip_lit_off, |re| {
    ExecBuilder::new(re)
        .skip_backtrack()
        .skip_dotstar_term_opt(false)
        .skip_skip_lit_opt(false)
        .only_utf8(false)
        .build()
        .map(regex::bytes::Regex::from)
        .unwrap()
});

skip_test!(regex_estar_skip_lit_off, |re| {
    ExecBuilder::new(re)
        .skip_backtrack()
        .skip_estar_term_opt(false)
        .skip_skip_lit_opt(false)
        .only_utf8(false)
        .build()
        .map(regex::bytes::Regex::from)
        .unwrap()
});

skip_test!(regex_dotstar_estar_skip_lit_off, |re| {
    ExecBuilder::new(re)
        .skip_backtrack()
        .skip_dotstar_term_opt(false)
        .skip_estar_term_opt(false)
        .skip_skip_lit_opt(false)
        .only_utf8(false)
        .build()
        .map(regex::bytes::Regex::from)
        .unwrap()
});
