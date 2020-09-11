/// Find the sum of all the primes below two million.
pub fn o10() -> String {
    const LIMIT: usize = 2_000_000;
    const SQRT_LIMIT: usize = 1414;

    // Table for sieve of Eratosthenes, where oddprimes[i] = is_prime(2i+1)
    // true means prime, false means composite
    let mut oddprimes = [true; LIMIT / 2];
    oddprimes[0] = false; // 1 is not a prime

    // To compute odd primes under LIMIT, consider all odds in [2,SQRT_LIMIT]
    for n in 1..(SQRT_LIMIT / 2) {
        if !oddprimes[n] {
            continue;
        }

        // Flag all odd multiples of odd primes as composite
        let mut x = 3 * n + 1;
        while x < LIMIT / 2 {
            oddprimes[x] = false;
            x += 2 * n + 1;
        }
    }

    // Sum all primes under LIMIT
    let sum = 2 + oddprimes
        .iter()
        .enumerate()
        .filter(|(_, &is_prime)| is_prime)
        .map(|(n, _)| 2 * n + 1)
        .sum::<usize>();
    sum.to_string()
}
