use integer_sqrt::IntegerSquareRoot;

/// Determines if n is a palindrome in decimal representation.
pub fn is_palindrome(n: i64) -> bool {
    let s = n.to_string().chars().collect::<Vec<char>>();
    for i in 0..(s.len() / 2) {
        if s[i] != s[s.len() - 1 - i] {
            return false;
        }
    }
    true
}

/// Counts the number of divisors of n.
pub fn count_divisors(n: usize) -> u32 {
    if n <= 2 { return n as u32; }

    let primes = primes_under(n / 2 + 1);
    let mut divisor_count = 1;

    // Find number of times each prime divides n
    let mut curr = n;
    let mut idx = 0;
    let len = primes.len();
    while curr > 1 && idx < len {
        // Determine how many times p divides n
        let p = primes[idx];
        let mut times_divides = 0;
        while curr % p == 0 {
            curr /= p;
            times_divides += 1;
        }
        // no. divisors is the product of 1 + how many times each p divides n
        divisor_count *= 1 + times_divides;

        idx += 1;
    }
    // Special case: we never test that n divides n,
    // so if n is prime, we fail to count it.
    // This check accounts for this case
    if divisor_count < 2 { 2 } else { divisor_count }
}

/// Returns a list of primes below limit via the sieve of eratosthenes.
pub fn primes_under(limit: usize) -> Vec<usize> {
    if limit < 2 { return vec![]; }
    if limit == 2 { return vec![2]; }

    let mut oddprimes = vec![true; limit / 2];
    oddprimes[0] = false; // 1 is not a prime

    // To compute odd primes under limit, consider all odds in [2,√(limit)]
    for n in 1..((limit.integer_sqrt_checked().unwrap() + 1) / 2) {
        if !oddprimes[n] {
            continue;
        }

        // Flag all odd multiples of odd primes as composite
        let mut x = 3 * n + 1;
        while x < limit / 2 {
            oddprimes[x] = false;
            x += 2 * n + 1;
        }
    }

    // Convert odd prime indices to actual numbers
    let mut primes: Vec<usize> = oddprimes
        .iter()
        .enumerate()
        .filter_map(|(n, &is_prime)| {
            if is_prime { Some(2 * n + 1) } else { None }
        })
        .collect();
    primes.insert(0, 2);
    primes
}

/// Constructs a table of aliquot sums of all numbers less than limit.
pub fn aliquot_sums_under(limit: usize) -> Vec<usize> {
    let mut aliquot_sum = vec![1; limit];
    aliquot_sum[0] = 0;
    aliquot_sum[1] = 0;

    for n in 2..(limit / 2) {
        let mut x = 2 * n;
        while x < limit {
            aliquot_sum[x] += n;
            x += n;
        }
    }

    aliquot_sum
}

#[cfg(test)]
mod tests {
    use crate::helpers::*;

    #[test]
    fn test_is_palindrome() {
        let yes = [1, 101, 24342, 8008];
        let no = [10, 200, 321, 3233, 8080];

        for n in yes.iter() {
            assert!(is_palindrome(*n));
        }
        for n in no.iter() {
            assert!(!is_palindrome(*n));
        }
    }

    #[test]
    fn test_count_divisors() {
        assert_eq!(count_divisors(1), 1);
        assert_eq!(count_divisors(28), 6);
        assert_eq!(count_divisors(0xACAB), 2);
        assert_eq!(count_divisors(69_420), 48);
        assert_eq!(count_divisors(123456789), 12);
    }

    #[test]
    fn test_primes_under() {
        let mut primes = primes_under(30);

        assert_eq!(primes.pop(), Some(29));
        assert_eq!(primes.pop(), Some(23));
        assert_eq!(primes.pop(), Some(19));
        assert_eq!(primes.pop(), Some(17));
        assert_eq!(primes.pop(), Some(13));
        assert_eq!(primes.pop(), Some(11));
        assert_eq!(primes.pop(), Some(7));
        assert_eq!(primes.pop(), Some(5));
        assert_eq!(primes.pop(), Some(3));
        assert_eq!(primes.pop(), Some(2));
        assert_eq!(primes.pop(), None);

        primes = primes_under(10_000_000);
        assert_eq!(primes.len(), 664_579);
    }

    #[test]
    fn test_aliquot_sums_under() {
        let table = aliquot_sums_under(16);
        assert_eq!(table[0], 0);
        assert_eq!(table[1], 0);
        assert_eq!(table[2], 1);
        assert_eq!(table[3], 1);
        assert_eq!(table[4], 3);
        assert_eq!(table[5], 1);
        assert_eq!(table[6], 6);
        assert_eq!(table[7], 1);
        assert_eq!(table[8], 7);
        assert_eq!(table[9], 4);
        assert_eq!(table[10], 8);
        assert_eq!(table[11], 1);
        assert_eq!(table[12], 16);
        assert_eq!(table[13], 1);
        assert_eq!(table[14], 10);
        assert_eq!(table[15], 9);
        assert_eq!(table.len(), 16);
    }
}
