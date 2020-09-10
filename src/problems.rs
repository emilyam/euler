use super::helpers::*;

/// Find the sum of all the multiples of 3 or 5 below 1000.
pub fn p1() -> i64 {
    let mut sum: i64 = 0;
    for i in 1..1000 {
        if (i % 3 == 0) || (i % 5 == 0) {
            sum += i;
        }
    }
    sum
}

/// By considering the terms in the Fibonacci sequence whose values do not
/// exceed four million, find the sum of the even-valued terms.
pub fn p2() -> i64 {
    let mut sum: i64 = 0;
    let mut prev = 0;
    let mut curr = 1;
    while curr < 4_000_000 {
        if curr % 2 == 0 {
            sum += curr;
        }
        let next = prev + curr;
        prev = curr;
        curr = next;
    }
    sum
}

/// What is the largest prime factor of the number 600851475143 ?
pub fn p3() -> i64 {
    let target = 600851475143;
    let mut curr_val = target;
    let mut curr_prime = 1;
    let mut factors: Vec<i64> = Vec::new();
    while curr_val != 1 {
        // deliberately skipping all even numbers as the target is odd
        curr_prime += 2;
        while curr_val % curr_prime == 0 {
            curr_val /= curr_prime;
            factors.push(curr_prime);
        }
    }
    // Check answer
    curr_val = 1;
    for f in factors {
        curr_val *= f;
    }
    assert_eq!(curr_val, target);
    curr_prime
}

/// Find the largest palindrome made from the product of two 3-digit numbers.
pub fn p4() -> i64 {
    let mut largest_palindrome = 0;
    for x in 100..1000 {
        for y in x..1000 {
            if (x * y > largest_palindrome) && is_palindrome(x * y) {
                largest_palindrome = x * y;
            }
        }
    }
    largest_palindrome
}

/// What is the smallest positive number that is evenly divisible by all of the numbers from 1 to 20?
pub fn p5() -> i64 {
    let lcm = 9699690; //lcm of all primes below 20; answer must be a multiple
    let mut index = lcm;
    let mut evenly_divides = false;
    while !evenly_divides {
        index += lcm;
        evenly_divides = true;
        for n in 2..21 {
            if index % n != 0 {
                evenly_divides = false;
                break;
            }
        }
    }
    index
}

/// Find the difference between the sum of the squares of the first one hundred natural numbers and the square of the sum.
pub fn p6() -> i64 {
    let mut sum: i64 = 0;
    let mut sumsquares: i64 = 0;
    for n in 1..101 {
        sum += n;
        sumsquares += n * n;
    }
    let squaresum = sum * sum;
    squaresum - sumsquares
}

/// What is the 10 001st prime number?
pub fn p7() -> i64 {
    let mut primes = vec![2];
    let mut n = 1;
    while primes.len() != 10_001 {
        n += 2;
        if !primes.iter().any(|x| n % x == 0) {
            primes.push(n);
        }
    }
    n
}
