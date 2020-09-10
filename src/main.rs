fn main() {
    let mut a = std::env::args();
    let a1 = a.next();
    let a2 = a.next();

    if let Some(cmd) = a1 {
        match a2 {
            Some(n) => {
                solve(n.parse::<u32>().unwrap());
            }
            None => { println!("Provide a problem number as so: \"{} n\"", cmd); }
        }
    }
}

fn solve(n: u32) {
    match n {
        0 => { println!("Project Euler is not zero-indexed.") }
        _ => { println!("Problem {} has not yet been solved.", n); }
    }
}
