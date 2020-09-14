use crate::helpers::*;
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
    for d in digits.iter() { s.push_str(&(d.to_string())); }
    s
}

/// Find the (one-indexed) index of the first term of the Fibonacci sequence
/// to contain 1000 digits.
///
/// Since F(n) ≈ φ^n/sqrt(5), we can calculate the smallest n such that:
/// n ≈ logφ(sqrt(5) * (10^999 - 1/2))
/// n ≈ logφ(sqrt(5)) + 999logφ(10)
pub fn p25() -> String {
    let sqrt5: f32 = 5.0_f32.sqrt();
    let phi: f32 = (1.0 + sqrt5) / 2.0;

    let n: f32 = (sqrt5.log(phi) + 999.0 * 10.0_f32.log(phi)).round();
    n.to_string()
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
    }
}
