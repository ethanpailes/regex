extern crate regex;

mod re_vec;
mod util;

use re_vec::re_vec;

fn main() {
    let mut no_lines = 0;

    let mut ops = vec![];

    fn b2i(b: bool) -> usize { if b { 1 } else { 0 } }

    let rv = vec![util::regex(r"([0-9a-zA-Z]{1}[0-9a-zA-Z]{1}[:]{1}){5}[0-9a-zA-Z]{1}[0-9a-zA-Z]{1}")];

    // for re in re_vec().into_iter() {
    for re in rv {
        let re_opts = match re {
            Ok(r) => r.get_skip_opts_used().clone(),

            // don't even count this line
            Err(_) => continue,
        };

        no_lines += 1;
        ops.push((b2i(re_opts.dotstar_term), b2i(re_opts.estar_term), b2i(re_opts.skip_lit)));

    }

    let p = |x| ((x as f64) / (no_lines as f64)) * 100.0;

    let dotstar: usize = ops.iter().map(|&(d,_,_)| d).sum();
    let elit: usize = ops.iter().map(|&(_,e,_)| e).sum();
    let skip_lit: usize = ops.iter().map(|&(_,_,s)| s).sum();
    let scan: usize = ops.iter()
        .map(|&(d,e,_)| if d > 0 || e > 0 {1} else {0}).sum();
    let any: usize = ops.iter()
        .map(|&(d,e,s)| if d > 0 || e > 0 || s > 0 {1} else {0}).sum();

    println!("{} total regex checked", no_lines);
    println!("{} ({} %) dotstar opts", dotstar, p(dotstar));
    println!("{} ({} %) eterm opts", elit, p(elit));
    println!("{} ({} %) scan opts", scan, p(scan));
    println!("{} ({} %) skip_lit opts", skip_lit, p(skip_lit));
    println!("{} ({} %) any opts", any, p(any));
}
