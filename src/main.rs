mod helpers;
mod optimized_problems;
mod problems;

use clap::{value_t, App, Arg};

fn main() {
    let matches = App::new("euler")
        .about("Solutions for Project Euler problems up to 100")
        .author("Emily A. Michael <emilyam@protonmail.com>")
        .arg(
            Arg::with_name("optimized")
                .short("o")
                .long("optimized")
                .help(
                    "Whether to use the optimized solution, if both an optimized and an \
                    unoptimized solution exist",
                )
                .takes_value(true)
                .possible_values(&["true", "false"])
                .default_value("true"),
        )
        .arg(Arg::with_name("problem").index(1).required(true))
        .get_matches();

    let problem = value_t!(matches.value_of("problem"), usize).unwrap_or_else(|e| e.exit());
    let optimized = value_t!(matches.value_of("optimized"), bool).unwrap_or_else(|e| e.exit());

    solve(problem, optimized);
}

fn solve(n: usize, optimized: bool) {
    use optimized_problems::*;
    use problems::*;
    use std::collections::HashMap;

    let problems: Vec<(usize, &dyn Fn() -> String)> = vec![
        (1, &p1),
        (2, &p2),
        (3, &p3),
        (4, &p4),
        (5, &p5),
        (6, &p6),
        (7, &p7),
        (8, &p8),
        (9, &p9),
        (10, &p10),
        (11, &p11),
        (12, &p12),
        (13, &p13),
        (14, &p14),
        (15, &p15),
        (16, &p16),
        (17, &p17),
    ];
    let problems: HashMap<usize, &dyn Fn() -> String> = problems.iter().cloned().collect();

    let optimized_problems: Vec<(usize, &dyn Fn() -> String)> = vec![(10, &o10), (12, &o12)];
    let optimized_problems: HashMap<usize, &dyn Fn() -> String> =
        optimized_problems.iter().cloned().collect();

    if optimized && optimized_problems.contains_key(&n) {
        println!("{}", (*(optimized_problems.get(&n).unwrap())()).to_string());
    } else if problems.contains_key(&n) {
        println!("{}", (*(problems.get(&n).unwrap())()).to_string());
    } else {
        println!("No such solution.");
    }
}
