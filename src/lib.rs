use std::cmp::Ordering;
use std::collections::VecDeque;
use std::ops::{Add, Sub};

#[derive(Debug, Clone, Eq)]
pub struct StringNumber(String);

impl Default for StringNumber {
    fn default() -> Self {
        Self("0".to_string())
    }
}

impl From<f64> for StringNumber {
    fn from(n: f64) -> Self {
        Self(n.to_string())
    }
}

impl StringNumber {
    pub fn nan() -> Self {
        StringNumber::from(f64::NAN)
    }

    pub fn infinity() -> Self {
        StringNumber::from(f64::INFINITY)
    }

    pub fn neg_infinity() -> Self {
        StringNumber::from(f64::NEG_INFINITY)
    }

    pub fn negate(&self) -> Self {
        if self == &StringNumber::nan() {
            self.clone()
        } else if let Some(s) = self.0.strip_prefix('-') {
            Self(s.to_string())
        } else {
            Self('-'.to_string() + &self.0)
        }
    }

    fn is_zero(&self) -> bool {
        matches!(self.0.as_str(), "0" | "-0" | "0.0" | "-0.0")
    }
}

impl PartialEq for StringNumber {
    fn eq(&self, other: &Self) -> bool {
        if self.is_zero() && other.is_zero() {
            true
        } else {
            self.0 == other.0
        }
    }
}

impl Add for StringNumber {
    type Output = StringNumber;

    fn add(self, rhs: Self) -> Self::Output {
        let l = Number::new(&self.0);
        let r = Number::new(&rhs.0);

        match l {
            Number::Positive(l) => match r {
                Number::Positive(r) => l + r,
                Number::Negative(r) => l - r.positive(),
                Number::NaN => StringNumber::nan(),
            },
            Number::Negative(l) => match r {
                Number::Positive(r) => r - l.positive(),
                Number::Negative(r) => (l.positive() + r.positive()).negate(),
                Number::NaN => StringNumber::nan(),
            },
            Number::NaN => StringNumber::nan(),
        }
    }
}

impl PartialOrd for StringNumber {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if self.is_zero() && other.is_zero() {
            return Some(Ordering::Equal);
        }

        let lhs = Number::new(&self.0);
        let rhs = Number::new(&other.0);

        match lhs {
            Number::NaN => None,
            Number::Positive(l) => match rhs {
                Number::NaN => None,
                Number::Positive(r) => l.partial_cmp(&r),
                Number::Negative(_) => Some(Ordering::Greater),
            },
            Number::Negative(l) => match rhs {
                Number::NaN => None,
                Number::Positive(_) => Some(Ordering::Less),
                Number::Negative(r) => {
                    Some(match l.positive().partial_cmp(&r.positive()).unwrap() {
                        Ordering::Less => Ordering::Greater,
                        Ordering::Greater => Ordering::Less,
                        Ordering::Equal => Ordering::Equal,
                    })
                }
            },
        }
    }
}

#[derive(Debug)]
enum Number<'s> {
    Positive(PositiveNumber<'s>),
    Negative(NegativeNumber<'s>),
    NaN,
}

impl<'s> Number<'s> {
    fn new(s: &'s str) -> Self {
        if s == StringNumber::nan().0 {
            Number::NaN
        } else if s.starts_with('-') {
            Number::Negative(NegativeNumber::new(s))
        } else {
            Number::Positive(PositiveNumber::new(s))
        }
    }
}

#[derive(Debug, PartialEq)]
struct PositiveNumber<'s> {
    s: &'s str,
    // decimal_index >= 1
    decimal_index: usize,
}

impl<'s> PositiveNumber<'s> {
    fn new(s: &'s str) -> Self {
        debug_assert!(!s.starts_with('-'));
        let decimal_index = s.find('.').unwrap_or(s.len());
        debug_assert!(decimal_index >= 1);
        Self { s, decimal_index }
    }

    fn is_inf(&self) -> bool {
        self.s == f64::INFINITY.to_string()
    }

    fn left_most_index(&self) -> isize {
        self.decimal_index as isize - 1
    }

    fn right_most_index(&self) -> isize {
        ((self.s.len() - self.decimal_index).saturating_sub(1)) as isize * -1
    }

    /// greater >= smaller
    fn subtract_ordered(greater: Self, less: Self) -> StringNumber {
        debug_assert!(greater >= less);

        if greater.is_inf() {
            return if less.is_inf() {
                StringNumber::nan()
            } else {
                StringNumber::infinity()
            };
        } else if less.is_inf() {
            return StringNumber::neg_infinity();
        }

        let mut result_digits: VecDeque<u8> = VecDeque::new();

        let mut carry = 0_i8;

        for index in isize::min(greater.right_most_index(), less.right_most_index())
            ..=isize::max(greater.left_most_index(), less.left_most_index())
        {
            let lhs_digit = greater.get_digit(index) as i8;
            let rhs_digit = less.get_digit(index) as i8;

            let mut digit_difference = lhs_digit - carry - rhs_digit;
            if digit_difference < 0 {
                carry = 1;
                digit_difference += 10;
            } else {
                carry = 0;
            }
            result_digits.push_front(digit_difference as u8);
        }

        if result_digits.is_empty() {
            result_digits.push_front(0);
        }

        let mut bytes: Vec<u8> = result_digits.iter().copied().map(number_to_ascii).collect();
        let decimal_index = usize::max(greater.decimal_index, less.decimal_index);
        if decimal_index + 1 < greater.s.len() {
            bytes.insert(decimal_index, b'.');
        }
        if decimal_index == 0 {
            bytes.insert(0, b'0');
        }
        StringNumber(String::from_utf8(bytes).unwrap())
    }
}

impl Add for PositiveNumber<'_> {
    type Output = StringNumber;

    fn add(self, rhs: Self) -> StringNumber {
        if self.is_inf() || rhs.is_inf() {
            return StringNumber::infinity();
        }

        let mut result_digits: VecDeque<u8> = VecDeque::new();

        let mut carry = 0_u8;

        for index in isize::min(self.right_most_index(), rhs.right_most_index())
            ..=isize::max(self.left_most_index(), rhs.left_most_index())
        {
            let lhs_digit = self.get_digit(index);
            let rhs_digit = rhs.get_digit(index);

            let mut digit_sum = lhs_digit + rhs_digit + carry;
            if digit_sum >= 10 {
                carry = 1;
                digit_sum -= 10;
            } else {
                carry = 0;
            }
            result_digits.push_front(digit_sum);
        }

        if carry > 0 {
            result_digits.push_front(carry);
        }

        if result_digits.is_empty() {
            result_digits.push_front(0);
        }

        let mut bytes: Vec<u8> = result_digits.iter().copied().map(number_to_ascii).collect();
        let decimal_index = usize::max(self.decimal_index, rhs.decimal_index);
        if decimal_index + 1 < self.s.len() {
            bytes.insert(decimal_index, b'.');
        }
        if decimal_index == 0 {
            bytes.insert(0, b'0');
        }
        StringNumber(String::from_utf8(bytes).unwrap())
    }
}

impl Sub for PositiveNumber<'_> {
    type Output = StringNumber;

    fn sub(self, rhs: Self) -> Self::Output {
        if self > rhs {
            PositiveNumber::subtract_ordered(self, rhs)
        } else {
            PositiveNumber::subtract_ordered(rhs, self).negate()
        }
    }
}

impl PartialOrd for PositiveNumber<'_> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if self.is_inf() {
            return if other.is_inf() {
                Some(Ordering::Equal)
            } else {
                Some(Ordering::Greater)
            };
        } else if other.is_inf() {
            return Some(Ordering::Less);
        }

        match self.left_most_index().partial_cmp(&other.left_most_index()) {
            Some(Ordering::Less) => return Some(Ordering::Less),
            Some(Ordering::Greater) => return Some(Ordering::Greater),
            _ => {}
        }

        for index in (self.right_most_index()..=self.left_most_index()).rev() {
            let lhs_digit = self.get_digit(index);
            let rhs_digit = other.get_digit(index);

            match lhs_digit.cmp(&rhs_digit) {
                Ordering::Equal => {}
                ordering => {
                    return Some(ordering);
                }
            }
        }
        Some(Ordering::Equal)
    }
}

impl GetDigit for PositiveNumber<'_> {
    fn str(&self) -> &str {
        self.s
    }

    fn decimal_index(&self) -> usize {
        self.decimal_index
    }
}

#[derive(Debug)]
struct NegativeNumber<'s> {
    s: &'s str,
    // decimal_index >= 1
    decimal_index: usize,
}

impl<'s> NegativeNumber<'s> {
    fn new(s: &'s str) -> Self {
        let stripped = s.strip_prefix('-').unwrap();
        let decimal_index = stripped.find('.').unwrap_or(stripped.len());
        debug_assert!(decimal_index >= 1);
        Self {
            s: stripped,
            decimal_index,
        }
    }

    fn positive(&self) -> PositiveNumber {
        PositiveNumber {
            s: self.s,
            decimal_index: self.decimal_index,
        }
    }
}

impl GetDigit for NegativeNumber<'_> {
    fn str(&self) -> &str {
        self.s
    }

    fn decimal_index(&self) -> usize {
        self.decimal_index
    }
}

trait GetDigit {
    fn str(&self) -> &str;

    fn decimal_index(&self) -> usize;

    fn get_digit(&self, mut index: isize) -> u8 {
        if index < 0 {
            // Skip past decimal point
            index -= 1;
        }

        if let Some(byte_index) = (self.decimal_index() as isize).checked_sub(index + 1) {
            self.str()
                .as_bytes()
                .get(byte_index as usize)
                .map_or(0, |&b| match b {
                    b'-' => 0,
                    _ => ascii_to_number(b),
                })
        } else {
            0
        }
    }
}

fn ascii_to_number(b: u8) -> u8 {
    b - b'0'
}

fn number_to_ascii(n: u8) -> u8 {
    n + b'0'
}

#[cfg(test)]
mod tests {
    use super::*;
    use quickcheck::{Arbitrary, Gen};
    use quickcheck_macros::quickcheck;
    use rstest::rstest;

    #[rstest]
    #[case(0.0, 0, 0)]
    #[case(0.0, 1, 0)]
    #[case(1.0, 0, 1)]
    #[case(1.0, -1, 0)]
    #[case(12.3, -2, 0)]
    #[case(12.3, -1, 3)]
    #[case(12.3, 0, 2)]
    #[case(12.3, 1, 1)]
    #[case(12.3, 2, 0)]
    #[case(-1.0, 0, 1)]
    #[case(-1.0, 1, 0)]
    fn get_digit(#[case] number: f64, #[case] index: isize, #[case] expected: u8) {
        match Number::new(&StringNumber::from(number).0) {
            Number::Positive(n) => {
                assert_eq!(n.get_digit(index), expected)
            }
            Number::Negative(n) => {
                assert_eq!(n.get_digit(index), expected)
            }
            Number::NaN => unreachable!(),
        }
    }

    #[rstest]
    #[case(0.0, 0.0, 0.0)] // 1
    #[case(1.0, 0.0, 1.0)] // 2
    #[case(0.0, 1.0, 1.0)] // 3
    #[case(1.0, 2.0, 3.0)] // 4
    #[case(1.0, 10.0, 11.0)] // 5
    #[case(5.0, 5.0, 10.0)] // 6
    #[case(15.0, 5.0, 20.0)] // 7
    #[case(15.0, 16.0, 31.0)] // 8
    #[case(55.0, 65.0, 120.0)] // 9
    #[case(0.0, -0.0, 0.0)] // 10
    #[case(0.0, -1.0, -1.0)] // 11
    #[case(1.0, -1.0, 0.0)] // 12
    #[case(0.1, 0.2, 0.3)] // 13
    #[case(0.1, -0.2, -0.1)] // 14
    #[case(-0.1, 0.2, 0.1)] // 15
    #[case(0.1, 0.02, 0.12)] // 16
    #[case(0.09, 0.03, 0.12)] // 17
    #[case(0.9, 0.3, 1.2)] // 18
    #[case(f64::NAN, 0.0, f64::NAN)] // 19
    #[case(f64::INFINITY, 1.0, f64::INFINITY)] // 20
    #[case(f64::NEG_INFINITY, 1.0, f64::NEG_INFINITY)] // 21
    #[case(f64::NEG_INFINITY, f64::INFINITY, f64::NAN)] // 22
    #[case(f64::INFINITY, f64::NEG_INFINITY, f64::NAN)] // 23
    fn add(#[case] a: f64, #[case] b: f64, #[case] expected: f64) {
        assert_eq!(
            StringNumber::from(a) + StringNumber::from(b),
            StringNumber::from(expected)
        );
    }

    #[rstest]
    #[case(0.0, 0.0, Some(Ordering::Equal))] // 1
    #[case(0.0, -0.0, Some(Ordering::Equal))] // 2
    #[case(1.0, 0.0, Some(Ordering::Greater))] // 3
    #[case(0.0, 1.0, Some(Ordering::Less))] // 4
    #[case(0.0, -1.0, Some(Ordering::Greater))] // 5
    #[case(-1.0, 0.0, Some(Ordering::Less))] // 6
    #[case(-1.0, 1.0, Some(Ordering::Less))] // 7
    #[case(1.0, -1.0, Some(Ordering::Greater))] // 8
    #[case(120.0, 21.0, Some(Ordering::Greater))] // 9
    #[case(-120.0, -21.0, Some(Ordering::Less))] // 10
    #[case(0.1, 0.2, Some(Ordering::Less))] // 11
    #[case(0.2, 0.1, Some(Ordering::Greater))] // 12
    #[case(f64::NAN, f64::NAN, None)] // 13
    #[case(f64::INFINITY, 0.0, Some(Ordering::Greater))] // 14
    #[case(1000.0, f64::INFINITY, Some(Ordering::Less))] // 15
    #[case(f64::NEG_INFINITY, 0.0, Some(Ordering::Less))] // 16
    #[case(f64::NEG_INFINITY, f64::INFINITY, Some(Ordering::Less))] // 17
    fn partial_cmp(#[case] a: f64, #[case] b: f64, #[case] expected: Option<Ordering>) {
        assert_eq!(StringNumber::from(a).partial_cmp(&b.into()), expected);
    }

    #[quickcheck]
    fn partial_cmp_quickcheck(a: NoShrink<f64>, b: NoShrink<f64>) -> bool {
        let a = a.into_inner();
        let b = b.into_inner();
        StringNumber::from(a).partial_cmp(&b.into()) == a.partial_cmp(&b)
    }

    #[rstest]
    #[case(0.0, 0, 0)]
    #[case(1.0, 0, 0)]
    #[case(1.2, 0, -1)]
    #[case(12.34, 1, -2)]
    fn left_most_index_right_most_index(
        #[case] f: f64,
        #[case] expected_left_most_index: isize,
        #[case] expected_right_most_index: isize,
    ) {
        let s = f.to_string();
        let number = PositiveNumber::new(&s);
        assert_eq!(number.left_most_index(), expected_left_most_index);
        assert_eq!(number.right_most_index(), expected_right_most_index);
    }

    // https://github.com/BurntSushi/quickcheck/pull/293/files
    #[derive(Clone, Debug)]
    pub struct NoShrink<A: Arbitrary> {
        inner: A,
    }

    impl<A: Arbitrary> NoShrink<A> {
        /// Unwrap the inner value
        pub fn into_inner(self) -> A {
            self.inner
        }
    }

    impl<A: Arbitrary> Arbitrary for NoShrink<A> {
        fn arbitrary(gen: &mut Gen) -> Self {
            Self {
                inner: Arbitrary::arbitrary(gen),
            }
        }
    }

    impl<A: Arbitrary> AsRef<A> for NoShrink<A> {
        fn as_ref(&self) -> &A {
            &self.inner
        }
    }
}
