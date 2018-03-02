extern crate regex;

use regex::bytes::SkipOptFlags;

mod re_vec;
mod util;

use re_vec::re_vec;

fn main() {
    println!("PING");
    let mut no_lines = 0;
    let mut dot_star = 0;
    let mut elit = 0;
    let mut skip_lit = 0;

    for re in re_vec().into_iter() {
        no_lines += 1;

        let re_opts = re.map(|r| r.get_skip_opts_used().clone())
            .unwrap_or(SkipOptFlags::all_false());

        if re_opts.dotstar_term {
            dot_star += 1;
        }
        if re_opts.estar_term {
            elit += 1;
        }
        if re_opts.skip_lit {
            skip_lit += 1;
        }

        println!(
            "{} dotstar opts, {} elit opts, and {} skip_lit opts for {} lines.",
                    dot_star, elit, skip_lit, no_lines);
    }
}
