use super::helpers::*;
use num_bigint::{BigUint, ToBigUint};
use std::cmp::max;

/// Finds the sum of all the multiples of 3 or 5 below 1000.
pub fn p1() -> String {
    let mut sum: u32 = 0;
    for i in 1..1000 {
        if (i % 3 == 0) || (i % 5 == 0) { sum += i; }
    }
    sum.to_string()
}

/// Finds the sum of the even-valued terms of the Fibonnaci sequence
/// whose values do not exceed four million.
pub fn p2() -> String {
    let mut sum: u32 = 0;
    let mut prev = 0;
    let mut curr = 1;
    while curr < 4_000_000 {
        if curr % 2 == 0 { sum += curr; }
        let next = prev + curr;
        prev = curr;
        curr = next;
    }
    sum.to_string()
}

/// Finds the largest prime factor of the number 600851475143.
pub fn p3() -> String {
    let target = 600851475143;
    let mut curr_val = target;
    let mut curr_prime = 1;
    let mut factors: Vec<u64> = Vec::new();
    while curr_val != 1 {
        // deliberately skipping all even numbers as the target is odd
        curr_prime += 2;
        while curr_val % curr_prime == 0 {
            curr_val /= curr_prime;
            factors.push(curr_prime);
        }
    }
    // Check answer
    curr_val = factors.iter().product::<u64>();
    assert_eq!(curr_val, target);
    curr_prime.to_string()
}

/// Finds the largest palindrome made from the product of two 3-digit numbers.
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

/// Finds the smallest positive number that is evenly divisible by all of
/// the numbers from 1 to 20?
pub fn p5() -> String {
    let lcm = 9699690; //lcm of all primes below 20; answer must be a multiple
    let mut candidate = lcm;
    let mut evenly_divides = false;
    // Loops through multiples of the lcm until finding the solution 
    while !evenly_divides {
        candidate += lcm;
        evenly_divides = true;
        // Check if each (non-trivial) number below 20 evenly divides it
        for n in 2..21 {
            if candidate % n != 0 {
                evenly_divides = false;
                break;
            }
        }
    }
    candidate.to_string()
}

/// Finds the difference between the sum of the squares of the first one hundred
/// natural numbers and the square of the sum.
pub fn p6() -> String {
    let mut sum: u32 = 0;
    let mut sumsquares: u32 = 0;
    for n in 1..101 {
        sum += n;
        sumsquares += n * n;
    }
    let squaresum = sum * sum;
    (squaresum - sumsquares).to_string()
}

/// Finds the 10,001st prime number.
pub fn p7() -> String {
    let mut primes = vec![2];
    let mut n = 1;
    // Use trial division to find primes up to the 10,001st
    while primes.len() != 10_001 {
        n += 2;
        if !primes.iter().any(|x| n % x == 0) {
            primes.push(n);
        }
    }
    n.to_string()
}

/// Finds the maximum value of the product of thirteen adjacent digits
/// in the given 1000-digit number.
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

/// Finds the product abc of the sole Pythagorean triplet for which a + b + c = 1000.
pub fn p9() -> String {
    for a in 1..333 {
        for b in (a + 1)..((1000 - a) / 2) {
            let c = 1000 - a - b;
            if (a * a + b * b) == (c * c) {
                return (a * b * c).to_string()
            }
        }
    }
    0.to_string()
}

/// Finds the sum of all the primes below two million.
pub fn p10() -> String {
    let primes = primes_under(2_000_000);

    // Sum all primes under LIMIT
    let sum = primes.iter().map(|&p| p as u64).sum::<u64>();
    sum.to_string()
}

/// Finds the greatest product of four adjacent numbers in the same direction
/// (up, down, left, right, or diagonally) in the 20×20 grid provided.
pub fn p11() -> String {
    let grid = [[ 8,  2, 22, 97, 38, 15,  0, 40,  0, 75,  4,  5,  7, 78, 52, 12, 50, 77, 91,  8],
                [49, 49, 99, 40, 17, 81, 18, 57, 60, 87, 17, 40, 98, 43, 69, 48,  4, 56, 62,  0],
                [81, 49, 31, 73, 55, 79, 14, 29, 93, 71, 40, 67, 53, 88, 30,  3, 49, 13, 36, 65],
                [52, 70, 95, 23,  4, 60, 11, 42, 69, 24, 68, 56,  1, 32, 56, 71, 37,  2, 36, 91],
                [22, 31, 16, 71, 51, 67, 63, 89, 41, 92, 36, 54, 22, 40, 40, 28, 66, 33, 13, 80],
                [24, 47, 32, 60, 99,  3, 45,  2, 44, 75, 33, 53, 78, 36, 84, 20, 35, 17, 12, 50],
                [32, 98, 81, 28, 64, 23, 67, 10, 26, 38, 40, 67, 59, 54, 70, 66, 18, 38, 64, 70],
                [67, 26, 20, 68,  2, 62, 12, 20, 95, 63, 94, 39, 63,  8, 40, 91, 66, 49, 94, 21],
                [24, 55, 58,  5, 66, 73, 99, 26, 97, 17, 78, 78, 96, 83, 14, 88, 34, 89, 63, 72],
                [21, 36, 23,  9, 75,  0, 76, 44, 20, 45, 35, 14,  0, 61, 33, 97, 34, 31, 33, 95],
                [78, 17, 53, 28, 22, 75, 31, 67, 15, 94,  3, 80,  4, 62, 16, 14,  9, 53, 56, 92],
                [16, 39,  5, 42, 96, 35, 31, 47, 55, 58, 88, 24,  0, 17, 54, 24, 36, 29, 85, 57],
                [86, 56,  0, 48, 35, 71, 89,  7,  5, 44, 44, 37, 44, 60, 21, 58, 51, 54, 17, 58],
                [19, 80, 81, 68,  5, 94, 47, 69, 28, 73, 92, 13, 86, 52, 17, 77,  4, 89, 55, 40],
                [ 4, 52,  8, 83, 97, 35, 99, 16,  7, 97, 57, 32, 16, 26, 26, 79, 33, 27, 98, 66],
                [88, 36, 68, 87, 57, 62, 20, 72,  3, 46, 33, 67, 46, 55, 12, 32, 63, 93, 53, 69],
                [ 4, 42, 16, 73, 38, 25, 39, 11, 24, 94, 72, 18,  8, 46, 29, 32, 40, 62, 76, 36],
                [20, 69, 36, 41, 72, 30, 23, 88, 34, 62, 99, 69, 82, 67, 59, 85, 74,  4, 36, 16],
                [20, 73, 35, 29, 78, 31, 90,  1, 74, 31, 49, 71, 48, 86, 81, 16, 23, 57,  5, 54],
                [ 1, 70, 54, 71, 83, 51, 54, 69, 16, 92, 33, 48, 61, 43, 52,  1, 89, 19, 67, 48]];
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

/// Finds the value of the first triangle number to have over five hundred divisors.
pub fn p12() -> String {
    let mut n = 1;
    let tri = |n| n * (n + 1) / 2;
    let mut divisors = 1;
    let mut div_n;
    let mut div_n_next = 1;
    while divisors <= 500 {
        n += 1;
        div_n = div_n_next;
        div_n_next = if n % 2 == 0 {
            count_divisors(n + 1)
        } else {
            count_divisors((n + 1) / 2)
        };
        divisors = div_n * div_n_next;
    }
    tri(n).to_string()
}

/// Finds the first ten digits of the sum of the 100 provided 50-digit numbers.
pub fn p13() -> String {
    let addends = [
        "37107287533902102798797998220837590246510135740250",
        "46376937677490009712648124896970078050417018260538",
        "74324986199524741059474233309513058123726617309629",
        "91942213363574161572522430563301811072406154908250",
        "23067588207539346171171980310421047513778063246676",
        "89261670696623633820136378418383684178734361726757",
        "28112879812849979408065481931592621691275889832738",
        "44274228917432520321923589422876796487670272189318",
        "47451445736001306439091167216856844588711603153276",
        "70386486105843025439939619828917593665686757934951",
        "62176457141856560629502157223196586755079324193331",
        "64906352462741904929101432445813822663347944758178",
        "92575867718337217661963751590579239728245598838407",
        "58203565325359399008402633568948830189458628227828",
        "80181199384826282014278194139940567587151170094390",
        "35398664372827112653829987240784473053190104293586",
        "86515506006295864861532075273371959191420517255829",
        "71693888707715466499115593487603532921714970056938",
        "54370070576826684624621495650076471787294438377604",
        "53282654108756828443191190634694037855217779295145",
        "36123272525000296071075082563815656710885258350721",
        "45876576172410976447339110607218265236877223636045",
        "17423706905851860660448207621209813287860733969412",
        "81142660418086830619328460811191061556940512689692",
        "51934325451728388641918047049293215058642563049483",
        "62467221648435076201727918039944693004732956340691",
        "15732444386908125794514089057706229429197107928209",
        "55037687525678773091862540744969844508330393682126",
        "18336384825330154686196124348767681297534375946515",
        "80386287592878490201521685554828717201219257766954",
        "78182833757993103614740356856449095527097864797581",
        "16726320100436897842553539920931837441497806860984",
        "48403098129077791799088218795327364475675590848030",
        "87086987551392711854517078544161852424320693150332",
        "59959406895756536782107074926966537676326235447210",
        "69793950679652694742597709739166693763042633987085",
        "41052684708299085211399427365734116182760315001271",
        "65378607361501080857009149939512557028198746004375",
        "35829035317434717326932123578154982629742552737307",
        "94953759765105305946966067683156574377167401875275",
        "88902802571733229619176668713819931811048770190271",
        "25267680276078003013678680992525463401061632866526",
        "36270218540497705585629946580636237993140746255962",
        "24074486908231174977792365466257246923322810917141",
        "91430288197103288597806669760892938638285025333403",
        "34413065578016127815921815005561868836468420090470",
        "23053081172816430487623791969842487255036638784583",
        "11487696932154902810424020138335124462181441773470",
        "63783299490636259666498587618221225225512486764533",
        "67720186971698544312419572409913959008952310058822",
        "95548255300263520781532296796249481641953868218774",
        "76085327132285723110424803456124867697064507995236",
        "37774242535411291684276865538926205024910326572967",
        "23701913275725675285653248258265463092207058596522",
        "29798860272258331913126375147341994889534765745501",
        "18495701454879288984856827726077713721403798879715",
        "38298203783031473527721580348144513491373226651381",
        "34829543829199918180278916522431027392251122869539",
        "40957953066405232632538044100059654939159879593635",
        "29746152185502371307642255121183693803580388584903",
        "41698116222072977186158236678424689157993532961922",
        "62467957194401269043877107275048102390895523597457",
        "23189706772547915061505504953922979530901129967519",
        "86188088225875314529584099251203829009407770775672",
        "11306739708304724483816533873502340845647058077308",
        "82959174767140363198008187129011875491310547126581",
        "97623331044818386269515456334926366572897563400500",
        "42846280183517070527831839425882145521227251250327",
        "55121603546981200581762165212827652751691296897789",
        "32238195734329339946437501907836945765883352399886",
        "75506164965184775180738168837861091527357929701337",
        "62177842752192623401942399639168044983993173312731",
        "32924185707147349566916674687634660915035914677504",
        "99518671430235219628894890102423325116913619626622",
        "73267460800591547471830798392868535206946944540724",
        "76841822524674417161514036427982273348055556214818",
        "97142617910342598647204516893989422179826088076852",
        "87783646182799346313767754307809363333018982642090",
        "10848802521674670883215120185883543223812876952786",
        "71329612474782464538636993009049310363619763878039",
        "62184073572399794223406235393808339651327408011116",
        "66627891981488087797941876876144230030984490851411",
        "60661826293682836764744779239180335110989069790714",
        "85786944089552990653640447425576083659976645795096",
        "66024396409905389607120198219976047599490197230297",
        "64913982680032973156037120041377903785566085089252",
        "16730939319872750275468906903707539413042652315011",
        "94809377245048795150954100921645863754710598436791",
        "78639167021187492431995700641917969777599028300699",
        "15368713711936614952811305876380278410754449733078",
        "40789923115535562561142322423255033685442488917353",
        "44889911501440648020369068063960672322193204149535",
        "41503128880339536053299340368006977710650566631954",
        "81234880673210146739058568557934581403627822703280",
        "82616570773948327592232845941706525094512325230608",
        "22918802058777319719839450180888072429661980811197",
        "77158542502016545090413245809786882778948721859617",
        "72107838435069186155435662884062257473692284509516",
        "20849603980134001723930671666823555245252804609722",
        "53503534226472524250874054075591789781264330331690",
    ];

    let mut sum: BigUint = 0.to_biguint().unwrap();
    for n in addends.iter() {
        sum += n.parse::<BigUint>().unwrap();
    }
    sum.to_string()[0..10].to_string()
}

/// Finds which starting number under one million produces the longest Collatz sequence.
pub fn p14() -> String {
    // Table of C(n), where C(n) is the length of
    // the Collatz sequence beginning at n
    let mut lengths = [0; 999_999];
    // (n, C(n)) for the largest C(n) so far encountered
    let mut longest = (1, 1);

    // Fill out table of C(n)
    lengths[0] = 1; // C(1) = 1
    for n in 500_000..1_000_000 {
        if lengths[n - 1] != 0 {
            continue;
        }
        let mut len = 1;
        let mut x = n;

        // Tracks all x encountered for which C(x) is unknown
        let mut lengths_to_add: Vec<(usize, usize)> = vec![];

        // Loop while C(x) is unknown
        while x >= 1_000_000 || lengths[x - 1] == 0 {
            // Find next number in sequence
            if x % 2 == 0 {
                x /= 2
            } else {
                x = 3 * x + 1
            }

            if x < 1_000_000 {
                if lengths[x - 1] != 0 {
                    // C(x) is known, calculate C(n) and stop
                    len += lengths[x - 1];
                    break;
                } else {
                    // C(x) unknown, calculate later based on C(n)
                    lengths_to_add.push((len, x));
                }
            }
            len += 1;
        }

        // For each x encountered where C(x) was unknown, record C(x)
        for (diff, x) in lengths_to_add.iter() {
            lengths[x - 1] = len - diff;
        }
        // Then record C(n)
        lengths[n - 1] = len;
        // Track C(n) if C(n) > C(m) for any m < n.
        // Note C(n) is guaranteed to be greater than C(x)
        // for any x that occurs in the Collatz sequence beginning with n
        // so we don't need to consider any x in lengths_to_add
        if len > longest.1 {
            longest = (n, len);
        }
    }
    longest.1.to_string()
}

/// Finds the number of unique routes through a 20×20 grid.
pub fn p15() -> String {
    // The solution can be easily calculated as
    // P(40,40)/(C(20,20)^2) = C(40,20)
    //                       = (∏(i=21->40)i)/20!

    let sequence_product = |start: u32, end: u32| -> BigUint {
        let mut f = 1.to_biguint().unwrap();
        for i in start..(end + 1) {
            f *= i.to_biguint().unwrap()
        }
        f
    };
    let factorial = |n| sequence_product(1, n);
    let num_routes = sequence_product(21, 40) / factorial(20);
    num_routes.to_string()
}

/// Finds the sum of the digits of the number 2^1000.
pub fn p16() -> String {
    let n = 2.to_biguint().unwrap().pow(1000);
    n.to_str_radix(10)
        .chars()
        .map(|c| c.to_digit(10).unwrap())
        .sum::<u32>()
        .to_string()
}

/// Determines how many letters would be used if all the numbers from 1 to 1000
/// inclusive were written out in words.
pub fn p17() -> String {
    let under_20_len = [0, 3, 3, 5, 4, 4, 3, 5, 5, 4, 3, 6, 6, 8, 8, 7, 7, 9, 8, 8];
    let tens_name_len = [6, 6, 5, 5, 5, 7, 6, 6]; // 20, 30, ... 90
    let hundred_len = 7; // "hundred"
    let and_len = 3; // "and"
    let one_thousand_len = 11; // "one thousand"

    // returns English name for number in range [1, 1000]
    let english = |n: usize| {
        if n < 1 || n > 1000 {
            None
        } else if n == 1000 {
            Some(one_thousand_len)
        } else {
            let mut sum;
            if n % 100 < 20 {
                sum = under_20_len[n % 100]
            } else {
                sum = under_20_len[n % 10] + tens_name_len[(n % 100) / 10 - 2];
            }
            if n >= 100 {
                sum += under_20_len[n / 100] + hundred_len;
                if n % 100 != 0 {
                    sum += and_len;
                }
            }
            Some(sum)
        }
    };

    (1..1001)
        .map(|n| english(n).unwrap())
        .sum::<u32>()
        .to_string()
}

/// Finds the maximum total from top to bottom of the given triangle.
pub fn p18() -> String {
    let mut values = [vec![75],
                      vec![95,64],
                      vec![17,47,82],
                      vec![18,35,87,10],
                      vec![20, 4,82,47,65],
                      vec![19, 1,23,75, 3,34],
                      vec![88, 2,77,73, 7,63,67],
                      vec![99,65, 4,28, 6,16,70,92],
                      vec![41,41,26,56,83,40,80,70,33],
                      vec![41,48,72,33,47,32,37,16,94,29],
                      vec![53,71,44,65,25,43,91,52,97,51,14],
                      vec![70,11,33,28,77,73,17,78,39,68,17,57],
                      vec![91,71,52,38,17,14,91,43,58,50,27,29,48],
                      vec![63,66, 4,68,89,53,67,30,73,16,69,87,40,31],
                      vec![ 4,62,98,27,23, 9,70,98,73,93,38,53,60, 4,23]];
    // Compute path maxima
    for n in 1..15 {
        let row = 14 - n;
        for col in 0..(row + 1) {
            values[row][col] += max(values[row + 1][col], values[row + 1][col + 1]);
        }
    }
    values[0][0].to_string()
}

/// Finds how many Sundays fell on the first of the month
/// during the twentieth century (1 Jan 1901 to 31 Dec 2000).
pub fn p19() -> String {
    // Number of months that start on Sunday, if Jan 1 is n,
    // where n is the day of the week such that 0 is Sunday
    let sunday_1sts = [2, 2, 2, 1, 3, 1, 1];
    let sunday_1sts_leap = [3, 2, 1, 2, 2, 1, 1];

    // Returns the day of the week of Jan 1 of the next year
    let next_jan_1 = |jan_1_day, leap_year| {
        if leap_year {
            (jan_1_day + 2) % 7
        } else {
            (jan_1_day + 1) % 7
        }
    };

    // Returns whether the year is a leap year
    // since we know every year divisible by four is a leap year
    // within the bounds [1901,2000], we can optimise from
    // y % 4 == 0 && (y % 100 != 0 || y % 400 == 0)
    let is_leap = |y| y % 4 == 0;

    // Set 1901 values
    let mut year = 1901;
    let mut weekday = next_jan_1(1, true);
    let mut sum = 0;
    while year <= 2000 {
        if is_leap(year) {
            sum += sunday_1sts_leap[weekday];
            weekday = next_jan_1(weekday, true);
        } else {
            sum += sunday_1sts[weekday];
            weekday = next_jan_1(weekday, false);
        }
        year += 1;
    }
    sum.to_string()
}

/// Finds the sum of the digits in the number 100!.
pub fn p20() -> String {
    let f100 = (1..101)
        .map(|n| n.to_biguint().unwrap())
        .fold(1.to_biguint().unwrap(), |acc, n| acc * n);
    let sum = f100
        .to_string()
        .chars()
        .map(|c| c.to_digit(10).unwrap())
        .sum::<u32>();
    sum.to_string()
}
