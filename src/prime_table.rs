pub mod prime_table {
    use integer_sqrt::IntegerSquareRoot;

    pub struct FactorTable {
        pub factors: Vec<usize>,
        pub n: usize,
    }

    impl Clone for FactorTable {
        fn clone(&self) -> Self {
            FactorTable {
                factors: self.factors.clone(),
                n: self.n,
            }
        }
    }

    impl FactorTable {
        /// Counts the number of divisors of n.
        pub fn count_divisors(&self) -> usize {
            if self.n <= 2 {
                return self.n;
            }

            self.prime_powers()
                .iter()
                .fold(1, |acc, &(_p, a)| acc * (a + 1))
        }

        /// Finds the value of the Euler phi function for n
        pub fn euler_phi(&self) -> usize {
            if self.n < 2 { return self.n; }
            self.prime_powers()
                .iter()
                .fold(self.n, |acc, &(p, _a)| acc * (p - 1) / p)
        }

        /// Finds the exponents of each prime factor of n
        fn prime_powers(&self) -> Vec<(usize, usize)> {
            if self.factors.len() == 0 {
                return vec![];
            }

            let mut prime_factors = self.factors.clone();
            let mut prime_powers: Vec<(usize, usize)> = vec![];

            let mut last_f = 0;
            let mut count_f = 0;
            while let Some(f) = prime_factors.pop() {
                if f == last_f {
                    count_f = count_f + 1;
                } else {
                    if count_f > 0 {
                        prime_powers.push((last_f, count_f));
                    }
                    last_f = f;
                    count_f = 1;
                }
            }
            prime_powers.push((last_f, count_f));

            prime_powers
        }
    }

    pub struct PrimeTable {
        pub primes: Vec<usize>,
        pub limit: usize,
    }

    impl Clone for PrimeTable {
        fn clone(&self) -> Self {
            PrimeTable {
                primes: self.primes.clone(),
                limit: self.limit,
            }
        }
    }

    /// Generates a table of primes below limit via the sieve of eratosthenes.
    pub fn primes_under(limit: usize) -> PrimeTable {
        if limit < 2 {
            return PrimeTable {
                primes: vec![],
                limit: limit,
            };
        }
        if limit == 2 {
            return PrimeTable {
                primes: vec![2],
                limit: limit,
            };
        }

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
            .filter_map(
                |(n, &is_prime)| {
                    if is_prime {
                        Some(2 * n + 1)
                    } else {
                        None
                    }
                },
            )
            .collect();
        primes.insert(0, 2);

        PrimeTable {
            primes: primes,
            limit: limit,
        }
    }

    impl PrimeTable {
        /// Finds prime factors of n.
        pub fn get_prime_factors(&self, n: usize) -> FactorTable {
            if n < 2 {
                return FactorTable {
                    factors: vec![],
                    n: n,
                };
            }
            if n <= 3 {
                return FactorTable {
                    factors: vec![n],
                    n: n,
                };
            }

            let mut prime_factors = vec![];

            // Find each prime that divides n
            let mut curr = n;
            let mut idx = 0;
            let len = self.primes.len();
            while curr > 1 && idx < len {
                // Determine if p divides n
                let p = self.primes[idx];
                while curr % p == 0 {
                    curr /= p;
                    prime_factors.push(p);
                }
                idx += 1;
            }
            // Special case: if n is prime
            if curr > 1 {
                prime_factors.push(curr)
            }

            FactorTable {
                factors: prime_factors,
                n: n,
            }
        }
    }
}

#[cfg(test)]
mod prime_table_tests {
    use crate::prime_table::*;

    #[test]
    fn test_primes_under() {
        let primetable = prime_table::primes_under(30);
        let mut primes = primetable.primes.clone();

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

        let primetable = prime_table::primes_under(10_000_000);
        assert_eq!(primetable.primes.len(), 664_579);
    }

    #[test]
    fn test_prime_factors() {
        let primetable = prime_table::primes_under(100);
        let factor_table = primetable.get_prime_factors(28);
        assert_eq!(factor_table.n, 28);

        let mut factors = factor_table.factors.clone();

        assert_eq!(factors.pop(), Some(7));
        assert_eq!(factors.pop(), Some(2));
        assert_eq!(factors.pop(), Some(2));
        assert_eq!(factors.pop(), None);

        factors = primetable.get_prime_factors(0xACAB).factors.clone();
        assert_eq!(factors.pop(), Some(0xACAB));
        assert_eq!(factors.pop(), None);

        factors = primetable.get_prime_factors(69_420).factors.clone();
        assert_eq!(factors.pop(), Some(89));
        assert_eq!(factors.pop(), Some(13));
        assert_eq!(factors.pop(), Some(5));
        assert_eq!(factors.pop(), Some(3));
        assert_eq!(factors.pop(), Some(2));
        assert_eq!(factors.pop(), Some(2));
        assert_eq!(factors.pop(), None);
    }

    #[test]
    fn test_count_divisors() {
        let primetable = prime_table::primes_under(3804);

        assert_eq!(primetable.get_prime_factors(1).count_divisors(), 1);
        assert_eq!(primetable.get_prime_factors(28).count_divisors(), 6);
        assert_eq!(primetable.get_prime_factors(0xACAB).count_divisors(), 2);
        assert_eq!(primetable.get_prime_factors(69_420).count_divisors(), 48);
        assert_eq!(primetable.get_prime_factors(123_456_789).count_divisors(), 12);
    }

    #[test]
    fn test_euler_phi() {
        let primetable = prime_table::primes_under(3804);

        assert_eq!(primetable.get_prime_factors(1).euler_phi(), 1);
        assert_eq!(primetable.get_prime_factors(28).euler_phi(), 12);
        assert_eq!(primetable.get_prime_factors(0xACAB).euler_phi(), 0xACAA);
        assert_eq!(primetable.get_prime_factors(69_420).euler_phi(), 16_896);
        assert_eq!(primetable.get_prime_factors(123_456_789).euler_phi(), 82_260_072);
    }
}
