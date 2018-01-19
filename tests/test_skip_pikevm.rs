
extern crate regex;

macro_rules! regex_new {
    ($re:expr) => {{
        use regex::internal::ExecBuilder;
        ExecBuilder::new($re)
            .skip_pikevm()
            .only_utf8(false)
            .build()
            .map(regex::bytes::Regex::from)
    }}
}

macro_rules! regex {
    ($re:expr) => {
        regex_new!($re).unwrap()
    }
}

mod skip;
