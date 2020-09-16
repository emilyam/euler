mod helpers;
mod first_score;
mod second_score;
mod prime_table;

use clap::{value_t, App, Arg};

fn main() {
    let matches = App::new("euler")
        .about("Solutions for Project Euler problems up to 100")
        .author("Emily A. Michael <emilyam@protonmail.com>")
        .arg(Arg::with_name("problem").index(1).required(true))
        .get_matches();

    let problem = value_t!(matches.value_of("problem"), usize).unwrap_or_else(|e| e.exit());

    solve(problem);
}

fn solve(n: usize) {
    use first_score::*;
    use second_score::*;
    use std::collections::HashMap;

    let problems: Vec<(usize, &dyn Fn() -> String)> = vec![
        (1, &p1),   (2, &p2),   (3, &p3),   (4, &p4),   (5, &p5),
        (6, &p6),   (7, &p7),   (8, &p8),   (9, &p9),   (10, &p10),
        (11, &p11), (12, &p12), (13, &p13), (14, &p14), (15, &p15),
        (16, &p16), (17, &p17), (18, &p18), (19, &p19), (20, &p20),
        (21, &p21), (22, &p22), (23, &p23), (24, &p24), (25, &p25),
    ];
    let problems: HashMap<usize, &dyn Fn() -> String> = problems.iter().cloned().collect();

    if problems.contains_key(&n) {
        println!("{}", (*(problems.get(&n).unwrap())()).to_string());
    } else {
        println!("No such solution.");
    }
}
