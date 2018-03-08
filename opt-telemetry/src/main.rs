extern crate regex;

mod re_vec;
mod util;

use re_vec::re_vec;

fn main() {
    let mut no_lines = 0;
    let mut dotstar = 0;
    let mut elit = 0;
    let mut skip_lit = 0;

    for re in re_vec().into_iter() {

        let re_opts = match re {
            Ok(r) => r.get_skip_opts_used().clone(),

            // don't even count this line
            Err(_) => continue,
        };

        no_lines += 1;

        if re_opts.dotstar_term {
            dotstar += 1;
        }
        if re_opts.estar_term {
            elit += 1;
        }
        if re_opts.skip_lit {
            skip_lit += 1;
        }

    }

    let p = |x| ((x as f64) / (no_lines as f64)) * 100.0;

    println!("{} total regex checked", no_lines);
    println!("{} ({} %) dotstar opts", dotstar, p(dotstar));
    println!("{} ({} %) eterm opts", elit, p(elit));
    println!("{} ({} %) skip_lit opts", skip_lit, p(skip_lit));
}
