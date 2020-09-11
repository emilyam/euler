mod helpers;
mod problems;

fn main() {
    let mut a = std::env::args();
    let a1 = a.next();
    let a2 = a.next();

    if let Some(cmd) = a1 {
        match a2 {
            Some(n) => {
                solve(n.parse::<usize>().unwrap());
            }
            None => {
                println!("Provide a problem number as so: \"{} n\"", cmd);
            }
        }
    }
}

fn solve(n: usize) {
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
    ];
    let problems: HashMap<usize, &dyn Fn() -> String> = problems.iter().cloned().collect();
    if problems.contains_key(&n) {
        println!("{}", (*(problems.get(&n).unwrap())()).to_string());
    } else {
        println!("No such solution.");
    }
}
