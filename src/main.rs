mod helpers;
mod problems;

fn main() {
    let mut a = std::env::args();
    let a1 = a.next();
    let a2 = a.next();

    if let Some(cmd) = a1 {
        match a2 {
            Some(n) => {
                solve(n.parse::<u32>().unwrap());
            }
            None => {
                println!("Provide a problem number as so: \"{} n\"", cmd);
            }
        }
    }
}

fn solve(n: u32) {
    println!(
        "{}",
        match n {
            1 => {
                problems::p1()
            }
            2 => {
                problems::p2()
            }
            3 => {
                problems::p3()
            }
            4 => {
                problems::p4()
            }
            5 => {
                problems::p5()
            }
            6 => {
                problems::p6()
            }
            7 => {
                problems::p7()
            }
            _ => {
                0
            }
        }
    )
}
