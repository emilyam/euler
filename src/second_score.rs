/// Evaluates the sum of all the amicable numbers under 10000.
pub fn p21() -> String {
    const LIMIT: usize = 10_000;
    // First, construct a table of the aliquot sum of all n < 10000
    let mut aliquot_sum = [1; LIMIT + 1];
    aliquot_sum[0] = 0;
    aliquot_sum[1] = 0;

    for n in 2..(LIMIT / 2) {
        let mut x = 2 * n;
        while x < LIMIT {
            aliquot_sum[x] += n;
            x += n;
        }
    }
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

#[cfg(test)]
mod tests {
    use crate::second_score::*;

    #[test]
    fn verify_solutions() {
        assert_eq!("31626".to_string(), p21());
        assert_eq!("871198282".to_string(), p22());
    }
}
