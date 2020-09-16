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
