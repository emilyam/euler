use crate::helpers::*;
use crate::prime_table::*;
use num_bigint::ToBigUint;
use permutohedron::LexicalPermutation;

/// Evaluates the sum of all the amicable numbers under 10000.
pub fn p21() -> String {
    const LIMIT: usize = 10_000;
    // First, construct a table of the aliquot sum of all n < 10000
    let aliquot_sum = aliquot_sums_under(LIMIT);

    // Search aliquot_sum table for amicable numbers
    // This will miss any amicable numbers whose pair is greater than
    // LIMIT, but fortunately no such pairs exist.
    let amicable_sum = aliquot_sum
        .iter()
        .enumerate()
        .filter_map(|(n, &sum)| {
            if sum != n && sum < LIMIT && aliquot_sum[sum] == n {
                Some(sum)
            } else {
                None
            }
        })
        .sum::<usize>();
    amicable_sum.to_string()
}

/// Finds the total of the "name scores" in a file provided,
/// where the "name score" is the product of the (1-indexed) position
/// of the name in alphabetical order and the sum of the position
/// in the alphabet of each letter in the name.
pub fn p22() -> String {
    // Get list of names and sort
    let raw_file = String::from_utf8(include_bytes!("p022_names.txt").to_vec()).unwrap();
    let mut names: Vec<&str> = raw_file.split(',').collect();
    names.sort();

    // Calculate the scores for each name and sum them
    let mut sum: u32 = 0;
    for (index, &name) in names.iter().enumerate() {
        let bytes = name.as_bytes();
        let mut score = 0;
        for b in bytes {
            let base = 'A' as u8 - 1;
            if b > &base {
                score += b - &base;
            }
        }
        sum += score as u32 * (index as u32 + 1);
    }

    sum.to_string()
}

/// Finds the sum of every positive integer inexpressable as
/// the sum of two abundant numbers (all of which are less than 28124).
pub fn p23() -> String {
    const LIMIT: usize = 28124;
    let aliquot_sums = aliquot_sums_under(LIMIT);

    // Find all abundant numbers
    let abundant: Vec<usize> = aliquot_sums
        .iter()
        .enumerate()
        .filter_map(|(n, &s)| if s > n { Some(n) } else { None })
        .collect();

    // Build table of sums of any two abundant numbers under LIMIT
    let mut is_sum = [false; LIMIT];
    let num_abundant = abundant.len();
    for a in 0..num_abundant {
        for b in a..num_abundant {
            let sum = abundant[a] + abundant[b];
            if sum < LIMIT {
                is_sum[sum] = true;
            }
        }
    }

    // Sum all numbers inexpressable as the sum of any two abundant numbers
    is_sum
        .iter()
        .enumerate()
        .fold(0, |acc, (n, &is_sum)| if !is_sum { acc + n } else { acc })
        .to_string()
}

/// Finds the millionth lexicographic permutation of the digits [0,9].
pub fn p24() -> String {
    let mut digits = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    for _ in 1..1_000_000 {
        digits.next_permutation();
    }

    let mut s = String::new();
    for d in digits.iter() {
        s.push_str(&(d.to_string()));
    }
    s
}

/// Finds the (one-indexed) index of the first term of the Fibonacci sequence
/// to contain 1000 digits.
///
/// Since the nth Fibonnaci number can be approximated with F(n) = ⌊φ^n/sqrt(5)+1/2⌋,
/// we can calculate the smallest n such that:
/// F(n) ≥ 10^999
///    n ≥ logφ(√5) * (10^999 - 1/2))
///    n ≥ logφ(√5) + 999logφ(10)
/// Note that since log(10^999 - 1/2) is extremely close to log(10^999)
/// (the difference is smaller than floating point error),
/// we can safely ignore the 1/2 term.
pub fn p25() -> String {
    let sqrt5: f32 = 5.0_f32.sqrt();
    let phi: f32 = (1.0 + sqrt5) / 2.0;

    let n: f32 = (sqrt5.log(phi) + 999.0 * 10.0_f32.log(phi)).ceil();
    n.to_string()
}

/// Find the natural number d < 1000 such that the decimal representation of its reciprocal
/// contains a repetend with the longest cycle of any natural number under 1000.
///
/// Since the period of 1/k is strictly less than k, we can count from the top of the range
/// and stop once d is less than the largest period encountered.
///
/// see http://mathforum.org/library/drmath/view/67018.html
pub fn p26() -> String {
    let pt = prime_table::primes_under(500);
    let mut d = 0;
    let mut largest_period = 0;

    let big = |n: usize| { n.to_biguint().unwrap() };
    // Compute repetend period of 1/n
    let period = |n| {
        let ft = pt.get_prime_factors(n);
        let phi = ft.euler_phi();
        let phi_ft = pt.get_prime_factors(phi);
        let mut phi_prime_factors = phi_ft.factors;
        phi_prime_factors.dedup();
        let mut d = phi;

        for f in phi_prime_factors.iter() {
            while d % f == 0 && big(10).pow((d / f) as u32) % n == big(1)
            {
                d /= f;
            }
        }
        d
    };

    let mut curr = 999;
    while curr > largest_period {
        let p = period(curr);
        if p > largest_period {
            d = curr;
            largest_period = p;
        }
        curr -= 1;
    }
    d.to_string()
}

#[cfg(test)]
mod tests {
    use crate::second_score::*;

    #[test]
    fn verify_solutions() {
        assert_eq!("31626".to_string(), p21());
        assert_eq!("871198282".to_string(), p22());
        assert_eq!("4179871".to_string(), p23());
        assert_eq!("2783915460".to_string(), p24());
        assert_eq!("4782".to_string(), p25());
        assert_eq!("983".to_string(), p26());
    }
}
