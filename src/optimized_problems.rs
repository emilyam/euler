use crate::helpers::*;

/// Find the sum of all the primes below two million.
pub fn o10() -> String {
    let oddprimes = odd_primes_under(2_000_000);

    // Sum all primes under LIMIT
    let sum = 2 + oddprimes
        .iter()
        .enumerate()
        .filter(|(_, &is_prime)| is_prime)
        .map(|(n, _)| 2 * n + 1)
        .sum::<usize>();
    sum.to_string()
}

/// What is the value of the first triangle number to have over five hundred divisors?
pub fn o12() -> String {
    let mut n = 1;
    let tri = |n| n * (n + 1) / 2;
    let mut divisors = 1;
    let mut div_n;
    let mut div_n_next = 1;
    while divisors <= 500 {
        n += 1;
        div_n = div_n_next;
        div_n_next = if n % 2 == 0 {
            count_divisors(n + 1)
        } else {
            count_divisors((n + 1) / 2)
        };
        divisors = div_n * div_n_next;
    }
    tri(n).to_string()
}
