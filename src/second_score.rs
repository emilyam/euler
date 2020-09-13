/// Evaluate the sum of all the amicable numbers under 10000.
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
