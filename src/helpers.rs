pub fn is_palindrome(n: i64) -> bool {
    let s = n.to_string().chars().collect::<Vec<char>>();
    for i in 0..(s.len() / 2) {
        if s[i] != s[s.len() - 1 - i] {
            return false;
        }
    }
    true
}

#[cfg(test)]
mod test {
    #[cfg(test)]
    fn test_is_palindrome() {
        let yes = [1, 101, 24342, 8008];
        let no = [10, 200, 321, 3233, 8080];

        for n in yes {
            assert!(is_palindrome(n));
        }
        for n in no {
            assert!(!is_palindrome(n));
        }
    }
}
