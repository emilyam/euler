use super::helpers::*;

/// Find the sum of all the multiples of 3 or 5 below 1000.
pub fn p1() -> String {
    let mut sum: i64 = 0;
    for i in 1..1000 {
        if (i % 3 == 0) || (i % 5 == 0) {
            sum += i;
        }
    }
    sum.to_string()
}

/// By considering the terms in the Fibonacci sequence whose values do not
/// exceed four million, find the sum of the even-valued terms.
pub fn p2() -> String {
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
    sum.to_string()
}

/// What is the largest prime factor of the number 600851475143 ?
pub fn p3() -> String {
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
    curr_prime.to_string()
}

/// Find the largest palindrome made from the product of two 3-digit numbers.
pub fn p4() -> String {
    let mut largest_palindrome = 0;
    for x in 100..1000 {
        for y in x..1000 {
            if (x * y > largest_palindrome) && is_palindrome(x * y) {
                largest_palindrome = x * y;
            }
        }
    }
    largest_palindrome.to_string()
}

/// What is the smallest positive number that is evenly divisible by all of
/// the numbers from 1 to 20?
pub fn p5() -> String {
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
    index.to_string()
}

/// Find the difference between the sum of the squares of the first one hundred
/// natural numbers and the square of the sum.
pub fn p6() -> String {
    let mut sum: i64 = 0;
    let mut sumsquares: i64 = 0;
    for n in 1..101 {
        sum += n;
        sumsquares += n * n;
    }
    let squaresum = sum * sum;
    (squaresum - sumsquares).to_string()
}

/// What is the 10 001st prime number?
pub fn p7() -> String {
    let mut primes = vec![2];
    let mut n = 1;
    while primes.len() != 10_001 {
        n += 2;
        if !primes.iter().any(|x| n % x == 0) {
            primes.push(n);
        }
    }
    n.to_string()
}

/// Find the thirteen adjacent digits in the 1000-digit number that have the
/// greatest product. What is the value of this product?
pub fn p8() -> String {
    let digits = "73167176531330624919225119674426574742355349194934\
                  96983520312774506326239578318016984801869478851843\
                  85861560789112949495459501737958331952853208805511\
                  12540698747158523863050715693290963295227443043557\
                  66896648950445244523161731856403098711121722383113\
                  62229893423380308135336276614282806444486645238749\
                  30358907296290491560440772390713810515859307960866\
                  70172427121883998797908792274921901699720888093776\
                  65727333001053367881220235421809751254540594752243\
                  52584907711670556013604839586446706324415722155397\
                  53697817977846174064955149290862569321978468622482\
                  83972241375657056057490261407972968652414535100474\
                  82166370484403199890008895243450658541227588666881\
                  16427171479924442928230863465674813919123162824586\
                  17866458359124566529476545682848912883142607690042\
                  24219022671055626321111109370544217506941658960408\
                  07198403850962455444362981230987879927244284909188\
                  84580156166097919133875499200524063689912560717606\
                  05886116467109405077541002256983155200055935729725\
                  71636269561882670428252483600823257530420752963450";
    let mut largest: u64 = 0;
    for i in 0..(1000 - 13) {
        let mut product = 1;
        for c in digits[i..i + 13].chars() {
            product *= c.to_digit(10).unwrap() as u64;
        }
        if product > largest {
            largest = product;
        }
    }
    largest.to_string()
}

/// There exists exactly one Pythagorean triplet for which a + b + c = 1000.
/// Find the product abc.
pub fn p9() -> String {
    for a in 1..333 {
        for b in (a + 1)..((1000 - a) / 2) {
            let c = 1000 - a - b;
            if (a * a + b * b) == (c * c) {
                return format!("{} * {} * {} = {}", a, b, c, a * b * c);
            }
        }
    }
    0.to_string()
}

/// Find the sum of all the primes below two million.
pub fn p10() -> String {
    let mut primes = vec![2];
    let mut n = 1;
    while n < 2_000_000 {
        n += 2;
        if !primes.iter().any(|x| n % x == 0) {
            primes.push(n);
        }
    }
    primes.iter().sum::<u64>().to_string()
}

/// What is the greatest product of four adjacent numbers in the same direction
/// (up, down, left, right, or diagonally) in the 20×20 grid?
pub fn p11() -> String {
    let grid = [
        [
             8,  2, 22, 97, 38, 15,  0, 40,  0, 75,  4,  5,  7, 78, 52, 12, 50, 77, 91,  8,
        ],
        [
            49, 49, 99, 40, 17, 81, 18, 57, 60, 87, 17, 40, 98, 43, 69, 48,  4, 56, 62,  0,
        ],
        [
            81, 49, 31, 73, 55, 79, 14, 29, 93, 71, 40, 67, 53, 88, 30,  3, 49, 13, 36, 65,
        ],
        [
            52, 70, 95, 23,  4, 60, 11, 42, 69, 24, 68, 56,  1, 32, 56, 71, 37,  2, 36, 91,
        ],
        [
            22, 31, 16, 71, 51, 67, 63, 89, 41, 92, 36, 54, 22, 40, 40, 28, 66, 33, 13, 80,
        ],
        [
            24, 47, 32, 60, 99,  3, 45,  2, 44, 75, 33, 53, 78, 36, 84, 20, 35, 17, 12, 50,
        ],
        [
            32, 98, 81, 28, 64, 23, 67, 10, 26, 38, 40, 67, 59, 54, 70, 66, 18, 38, 64, 70,
        ],
        [
            67, 26, 20, 68,  2, 62, 12, 20, 95, 63, 94, 39, 63,  8, 40, 91, 66, 49, 94, 21,
        ],
        [
            24, 55, 58,  5, 66, 73, 99, 26, 97, 17, 78, 78, 96, 83, 14, 88, 34, 89, 63, 72,
        ],
        [
            21, 36, 23,  9, 75,  0, 76, 44, 20, 45, 35, 14,  0, 61, 33, 97, 34, 31, 33, 95,
        ],
        [
            78, 17, 53, 28, 22, 75, 31, 67, 15, 94,  3, 80,  4, 62, 16, 14,  9, 53, 56, 92,
        ],
        [
            16, 39,  5, 42, 96, 35, 31, 47, 55, 58, 88, 24,  0, 17, 54, 24, 36, 29, 85, 57,
        ],
        [
            86, 56,  0, 48, 35, 71, 89,  7,  5, 44, 44, 37, 44, 60, 21, 58, 51, 54, 17, 58,
        ],
        [
            19, 80, 81, 68,  5, 94, 47, 69, 28, 73, 92, 13, 86, 52, 17, 77,  4, 89, 55, 40,
        ],
        [
             4, 52,  8, 83, 97, 35, 99, 16,  7, 97, 57, 32, 16, 26, 26, 79, 33, 27, 98, 66,
        ],
        [
            88, 36, 68, 87, 57, 62, 20, 72,  3, 46, 33, 67, 46, 55, 12, 32, 63, 93, 53, 69,
        ],
        [
             4, 42, 16, 73, 38, 25, 39, 11, 24, 94, 72, 18,  8, 46, 29, 32, 40, 62, 76, 36,
        ],
        [
            20, 69, 36, 41, 72, 30, 23, 88, 34, 62, 99, 69, 82, 67, 59, 85, 74,  4, 36, 16,
        ],
        [
            20, 73, 35, 29, 78, 31, 90,  1, 74, 31, 49, 71, 48, 86, 81, 16, 23, 57,  5, 54,
        ],
        [
             1, 70, 54, 71, 83, 51, 54, 69, 16, 92, 33, 48, 61, 43, 52,  1, 89, 19, 67, 48,
        ],
    ];
    let mut greatest = 0;
    for x in 0..17 {
        for y in 0..20 {
            // Horizontal lines
            let product = (0..4).map(|n| grid[x + n][y]).product::<u32>();
            if product > greatest {
                greatest = product;
            }
            // Vertical lines
            let product = (0..4).map(|n| grid[y][x + n]).product::<u32>();
            if product > greatest {
                greatest = product;
            }
        }
        for y in 0..17 {
            // NW-SE Diagonals
            let product = (0..4).map(|n| grid[x + n][y + n]).product::<u32>();
            if product > greatest {
                greatest = product;
            }
            // NE-SW Diagonals
            let product = (0..4).map(|n| grid[x + n][19 - y - n]).product::<u32>();
            if product > greatest {
                greatest = product;
            }
        }
    }
    greatest.to_string()
}

/// What is the value of the first triangle number to have over five hundred divisors?
pub fn p12() -> String {
    let mut n: u64 = 7;
    let mut tri: u64 = 28;
    while count_divisors(tri) <= (500 as u64) {
        n += 1;
        tri += n;
    }
    tri.to_string()
}
