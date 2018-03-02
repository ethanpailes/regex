
use regex::internal::ExecBuilder;
use regex::bytes::Regex;
use regex::Error;

pub fn regex(re: &'static str) -> Result<Regex, Error> {
    println!("re={}", re);
    ExecBuilder::new(re).only_utf8(false).skip().build().map(Regex::from)
}
