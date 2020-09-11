use integer_sqrt::IntegerSquareRoot;

/// Determines if n is a palindrome in decimal representation
pub fn is_palindrome(n: i64) -> bool {
    let s = n.to_string().chars().collect::<Vec<char>>();
    for i in 0..(s.len() / 2) {
        if s[i] != s[s.len() - 1 - i] {
            return false;
        }
    }
    true
}

/// Counts the number of natural divisors of n
pub fn count_divisors(n: u64) -> u64 {
    if n <= 2 {
        return n;
    }
    let sqrt_n = n.integer_sqrt_checked().unwrap() as usize;
    let odd_primes = odd_primes_under(sqrt_n + 1);

    let mut n = n as usize;
    let mut prime_table_index = 1;

    // Where the prime factorization of n = (p1^a1)*(p2^a2)*...
    // prime_factors[pi-1] = ai
    // special case: prime_factors[0] = 1 iff n is prime
    let mut prime_factors = vec![0; sqrt_n];
    while n % 2 == 0 {
        n /= 2;
        prime_factors[1] += 1;
    }
    while n > 1 {
        // Find next odd prime
        while prime_table_index < sqrt_n / 2 && !odd_primes[prime_table_index] {
            prime_table_index += 1;
        }
        if prime_table_index < sqrt_n / 2 {
            // p is the next odd prime
            let p = 2 * prime_table_index + 1;
            // Test divisibility
            while n % p == 0 {
                n /= p;
                prime_factors[p - 1] += 1;
            }
            prime_table_index += 1;
        } else {
            // exhausted table; n must be prime
            n = 1;
            prime_factors[0] = 1;
        }
    }
    prime_factors.iter().map(|f| f + 1).product::<u64>()
}

/// Returns a table of odd primes below limit via the sieve of eratosthenes
/// where oddprimes[n] = is_prime(2n+1)
pub fn odd_primes_under(limit: usize) -> Vec<bool> {
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

    oddprimes
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
    fn test_odd_primes_under() {
        let oddprimes = odd_primes_under(30);

        assert_eq!(oddprimes.len(), 15);
        assert!(!oddprimes[0]); // 1
        assert!(oddprimes[1]); // 3
        assert!(oddprimes[2]); // 5
        assert!(oddprimes[3]); // 7
        assert!(!oddprimes[4]); // 9
        assert!(oddprimes[5]); // 11
        assert!(oddprimes[6]); // 13
        assert!(!oddprimes[7]); // 15
        assert!(oddprimes[8]); // 17
        assert!(oddprimes[9]); // 19
        assert!(!oddprimes[10]); // 21
        assert!(oddprimes[11]); // 23
        assert!(!oddprimes[12]); // 25
        assert!(!oddprimes[13]); // 27
        assert!(oddprimes[14]); // 29
    }
}
