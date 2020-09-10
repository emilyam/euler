pub fn is_palindrome(n: i64) -> bool {
    let s = n.to_string().chars().collect::<Vec<char>>();
    for i in 0..(s.len() / 2) {
        if s[i] != s[s.len() - 1 - i] {
            return false;
        }
    }
    true
}

pub fn count_divisors(n: u64) -> u64 {
    let mut divisors = 1;
    for d in 1..((n/2)+1){
        if n % d == 0 {
            divisors += 1;
        }
    }
    divisors
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
    }
}
