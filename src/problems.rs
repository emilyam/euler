/// Find the sum of all the multiples of 3 or 5 below 1000.
pub fn p1() -> i32 {
    let mut sum = 0;
    for i in 1..1000 {
        if (i % 3 == 0) || (i % 5 == 0) {
            sum += i;
        }
    }
    sum
}
