use bigdecimal::BigDecimal;
use std::borrow::Cow;
use std::cmp::Ordering;
use std::convert::TryInto;
use std::mem::take;
use std::ops::{Add, AddAssign, Div, Mul, MulAssign, Sub, SubAssign};

const INFINITY_STR: &str = "inf";
const NEG_INFINITY_STR: &str = "-inf";
const NAN_STR: &str = "NaN";
const DECIMAL: char = '.';
const ZERO: &str = "0.0";

#[derive(Debug, Clone, Eq)]
pub struct StringNumber(String);

impl Default for StringNumber {
    fn default() -> Self {
        Self(ZERO.to_string())
    }
}

impl From<f64> for StringNumber {
    fn from(n: f64) -> Self {
        let mut s = n.to_string();
        if !(s == INFINITY_STR || s == NEG_INFINITY_STR || s == NAN_STR || s.contains(DECIMAL)) {
            // Number string should end with ".0"
            s.push_str(".0");
        }
        Self(s)
    }
}

impl From<&BigDecimal> for StringNumber {
    fn from(bd: &BigDecimal) -> Self {
        let mut s = bd.to_string();
        StringNumber::fix_zeros(&mut s);
        Self(s)
    }
}

impl From<StringNumber> for f64 {
    /// Doesn't return correct NaN value
    fn from(s: StringNumber) -> Self {
        s.0.parse().unwrap()
    }
}

impl From<PositiveNumber<'_>> for StringNumber {
    fn from(p: PositiveNumber<'_>) -> Self {
        StringNumber(p.s.to_string())
    }
}

impl From<PositiveOrNaN<'_>> for StringNumber {
    fn from(positive_or_nan: PositiveOrNaN<'_>) -> Self {
        match positive_or_nan {
            PositiveOrNaN::Positive(p) => p.into(),
            PositiveOrNaN::NaN => StringNumber::nan(),
        }
    }
}

impl From<NegativeNumber<'_>> for StringNumber {
    fn from(p: NegativeNumber<'_>) -> Self {
        StringNumber("-".to_string() + &p.s)
    }
}

impl StringNumber {
    pub fn nan() -> Self {
        StringNumber(NAN_STR.to_string())
    }

    pub fn infinity() -> Self {
        StringNumber(INFINITY_STR.to_string())
    }

    pub fn neg_infinity() -> Self {
        StringNumber(NEG_INFINITY_STR.to_string())
    }

    pub fn is_nan(&self) -> bool {
        self.0 == NAN_STR
    }

    pub fn is_infinity(&self) -> bool {
        self.0 == INFINITY_STR
    }

    pub fn is_neg_infinity(&self) -> bool {
        self.0 == NEG_INFINITY_STR
    }

    fn is_zero(&self) -> bool {
        matches!(self.0.as_str(), ZERO | "-0.0")
    }

    fn fix_zeros(s: &mut String) {
        debug_assert_ne!(s, NAN_STR);
        debug_assert_ne!(s, INFINITY_STR);
        debug_assert_ne!(s, NEG_INFINITY_STR);
        if !s.contains('.') {
            s.push_str(".0");
        }

        if s.starts_with("-.") {
            s.insert(1, '0');
        } else if s.starts_with('.') {
            s.insert(0, '0');
        }

        while s.starts_with('0') && !s.starts_with("0.") {
            s.remove(0);
        }
        while s.starts_with("-0") && !s.starts_with("-0.") {
            s.remove(1);
        }
        while s.ends_with('0') && !s.ends_with(".0") {
            s.pop();
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
                Number::Positive(r) => Some(l.cmp(&r)),
                Number::Negative(_) => Some(Ordering::Greater),
            },
            Number::Negative(l) => match rhs {
                Number::NaN => None,
                Number::Positive(_) => Some(Ordering::Less),
                Number::Negative(r) => Some(match l.positive().cmp(&r.positive()) {
                    Ordering::Less => Ordering::Greater,
                    Ordering::Greater => Ordering::Less,
                    Ordering::Equal => Ordering::Equal,
                }),
            },
        }
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
            Number::NaN => StringNumber::nan(),
            Number::Positive(l) => match r {
                Number::NaN => StringNumber::nan(),
                Number::Positive(r) => (l + r).into(),
                Number::Negative(r) => (l - r.positive()),
            },
            Number::Negative(l) => match r {
                Number::NaN => StringNumber::nan(),
                Number::Positive(r) => (r - l.positive()),
                Number::Negative(r) => (l.positive() + r.positive()).negative().into(),
            },
        }
    }
}

impl AddAssign for StringNumber {
    fn add_assign(&mut self, rhs: Self) {
        *self = take(self) + rhs;
    }
}

impl Sub for StringNumber {
    type Output = StringNumber;

    fn sub(self, rhs: Self) -> Self::Output {
        let l = Number::new(&self.0);
        let r = Number::new(&rhs.0);

        match l {
            Number::NaN => StringNumber::nan(),
            Number::Positive(l) => match r {
                Number::NaN => StringNumber::nan(),
                Number::Positive(r) => (l - r),
                Number::Negative(r) => (l + r.positive()).into(),
            },
            Number::Negative(l) => match r {
                Number::NaN => StringNumber::nan(),
                Number::Positive(r) => (l.positive() + r).negative().into(),
                Number::Negative(r) => r.positive() - l.positive(),
            },
        }
    }
}

impl SubAssign for StringNumber {
    fn sub_assign(&mut self, rhs: Self) {
        *self = take(self) - rhs;
    }
}

impl Mul for StringNumber {
    type Output = StringNumber;

    fn mul(self, rhs: Self) -> Self::Output {
        let lhs = Number::new(&self.0);
        let rhs = Number::new(&rhs.0);

        match lhs {
            Number::NaN => StringNumber::nan(),
            Number::Positive(l) => match rhs {
                Number::NaN => StringNumber::nan(),
                Number::Positive(r) => (l * r).into(),
                Number::Negative(r) => (l * r.positive()).negative_if_positive(),
            },
            Number::Negative(l) => match rhs {
                Number::NaN => StringNumber::nan(),
                Number::Positive(r) => (l.positive() * r).negative_if_positive(),
                Number::Negative(r) => (l.positive() * r.positive()).into(),
            },
        }
    }
}

impl MulAssign for StringNumber {
    fn mul_assign(&mut self, rhs: Self) {
        *self = take(self) * rhs;
    }
}

impl Div for StringNumber {
    type Output = StringNumber;

    fn div(self, rhs: Self) -> Self::Output {
        let lhs = Number::new(&self.0);
        let rhs = Number::new(&rhs.0);

        match lhs {
            Number::NaN => StringNumber::nan(),
            Number::Positive(l) => match rhs {
                Number::NaN => StringNumber::nan(),
                Number::Positive(r) => (l / r).into(),
                Number::Negative(r) => (l / r.positive()).negative().into(),
            },
            Number::Negative(l) => match rhs {
                Number::NaN => StringNumber::nan(),
                Number::Positive(r) => (l.positive() / r).negative().into(),
                Number::Negative(r) => (l.positive() / r.positive()).into(),
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
        if s == NAN_STR {
            Number::NaN
        } else if s.starts_with('-') {
            Number::Negative(NegativeNumber::new(s))
        } else {
            Number::Positive(PositiveNumber::new(s))
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
struct PositiveNumber<'s> {
    s: Cow<'s, str>,
    // decimal_index >= 1
    decimal_index: usize,
}

impl<'s> PositiveNumber<'s> {
    fn new(s: &'s str) -> Self {
        Cow::from(s).into()
    }

    fn infinity() -> PositiveNumber<'s> {
        PositiveNumber::new(INFINITY_STR)
    }

    fn is_inf(&self) -> bool {
        self.s == INFINITY_STR
    }

    fn is_zero(&self) -> bool {
        self.s == ZERO
    }

    fn left_most_index(&self) -> isize {
        self.decimal_index as isize - 1
    }

    fn right_most_index(&self) -> isize {
        -(((self.s.len() - self.decimal_index).saturating_sub(1)) as isize)
    }

    fn negative(self) -> NegativeNumber<'s> {
        NegativeNumber {
            s: self.s,
            decimal_index: self.decimal_index,
        }
    }

    /// greater >= smaller
    fn subtract_ordered(greater: Self, less: Self) -> PositiveOrNaN<'s> {
        debug_assert!(greater >= less);

        if greater.is_inf() {
            return if less.is_inf() {
                PositiveOrNaN::NaN
            } else {
                PositiveNumber::infinity().into()
            };
        }

        let mut result_digits: Vec<u8> = Vec::new();

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
            result_digits.push(digit_difference as u8);
        }

        PositiveNumber::from(Cow::from(PositiveNumber::digits_to_string(
            result_digits,
            usize::max(greater.decimal_index, less.decimal_index),
        )))
        .into()
    }

    fn digits_to_string(mut digits: Vec<u8>, mut decimal_index: usize) -> String {
        if digits.is_empty() {
            digits.push(0);
        }

        let mut bytes: Vec<u8> = Vec::new();
        if decimal_index == 0 {
            // bytes starts with '.'
            bytes.push(b'0');
            decimal_index += 1;
        }
        bytes.extend(
            digits
                .iter()
                .rev()
                .copied()
                .map(PositiveNumber::number_to_ascii),
        );

        bytes.insert(decimal_index, b'.');
        // bytes ends with '.'
        if decimal_index == bytes.len() - 1 {
            bytes.push(b'0');
        }

        String::from_utf8(bytes).unwrap()
    }

    fn number_to_ascii(n: u8) -> u8 {
        n + b'0'
    }

    /// self must not be infinity. n <= 9.
    fn mul_by_single_digit(&self, n: u8) -> PositiveNumber<'s> {
        debug_assert!(!self.is_inf());
        debug_assert!(n <= 9);
        let mut result_digits: Vec<u8> = Vec::new();

        let mut carry = 0_u8;
        for index in self.right_most_index()..=self.left_most_index() {
            let mut digit = self.get_digit(index) * n + carry;
            carry = digit / 10;
            digit -= carry * 10;
            result_digits.push(digit);
        }

        let mut decimal_index = self.decimal_index;
        if carry > 0 {
            result_digits.push(carry);
            decimal_index += 1;
        }

        if result_digits.iter().all(|&n| n == 0) {
            PositiveNumber::default()
        } else {
            Cow::from(PositiveNumber::digits_to_string(
                result_digits,
                decimal_index,
            ))
            .into()
        }
    }

    fn mul_10_power(mut self, power: isize) -> PositiveNumber<'s> {
        let mut s = self.s.to_string();

        let decimal_index = s.find(DECIMAL).unwrap();
        s.remove(decimal_index);
        let mut new_decimal_index = decimal_index as isize + power;
        if new_decimal_index <= 0 {
            // terrible time complexity
            #[allow(clippy::mut_range_bound)]
            for _ in new_decimal_index..=0 {
                s.insert(0, '0');
                new_decimal_index += 1;
            }
        } else if new_decimal_index >= s.len() as isize {
            for _ in 0..=new_decimal_index {
                s.push('0');
            }
        }
        s.insert(new_decimal_index.try_into().unwrap(), DECIMAL);
        StringNumber::fix_zeros(&mut s);

        self = Cow::from(s).into();
        self
    }
}

impl Default for PositiveNumber<'_> {
    fn default() -> Self {
        Cow::from(ZERO).into()
    }
}

impl<'s> From<Cow<'s, str>> for PositiveNumber<'s> {
    fn from(s: Cow<'s, str>) -> Self {
        debug_assert!(s != NAN_STR);
        debug_assert!(!s.starts_with('-'));

        let decimal_index = if s == INFINITY_STR {
            0
        } else {
            s.find(DECIMAL).unwrap()
        };
        Self { s, decimal_index }
    }
}

#[cfg(test)]
impl From<f64> for PositiveNumber<'_> {
    fn from(f: f64) -> Self {
        Cow::from(StringNumber::from(f).0).into()
    }
}

impl<'s> Add for PositiveNumber<'s> {
    type Output = PositiveNumber<'s>;

    fn add(self, rhs: Self) -> PositiveNumber<'s> {
        if self.is_inf() || rhs.is_inf() {
            return PositiveNumber::infinity();
        }

        let mut result_digits: Vec<u8> = Vec::new();

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
            result_digits.push(digit_sum);
        }

        if carry > 0 {
            result_digits.push(carry);
        }

        Cow::from(PositiveNumber::digits_to_string(
            result_digits,
            usize::max(self.decimal_index, rhs.decimal_index) + carry as usize,
        ))
        .into()
    }
}

impl AddAssign for PositiveNumber<'_> {
    fn add_assign(&mut self, rhs: Self) {
        *self = take(self) + rhs;
    }
}

impl<'s> Sub for PositiveNumber<'s> {
    type Output = StringNumber;

    fn sub(self, rhs: Self) -> Self::Output {
        if self > rhs {
            PositiveNumber::subtract_ordered(self, rhs).into()
        } else {
            PositiveNumber::subtract_ordered(rhs, self).negative_if_positive()
        }
    }
}

impl PartialOrd for PositiveNumber<'_> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for PositiveNumber<'_> {
    fn cmp(&self, other: &Self) -> Ordering {
        if self.is_inf() {
            return if other.is_inf() {
                Ordering::Equal
            } else {
                Ordering::Greater
            };
        } else if other.is_inf() {
            return Ordering::Less;
        }

        match self.left_most_index().partial_cmp(&other.left_most_index()) {
            Some(Ordering::Less) => return Ordering::Less,
            Some(Ordering::Greater) => return Ordering::Greater,
            _ => {}
        }

        for index in (self.right_most_index()..=self.left_most_index()).rev() {
            let lhs_digit = self.get_digit(index);
            let rhs_digit = other.get_digit(index);

            match lhs_digit.cmp(&rhs_digit) {
                Ordering::Equal => {}
                ordering => {
                    return ordering;
                }
            }
        }
        Ordering::Equal
    }
}

impl GetDigit for PositiveNumber<'_> {
    fn str(&self) -> &str {
        &self.s
    }

    fn decimal_index(&self) -> usize {
        self.decimal_index
    }
}

impl<'s> Mul for PositiveNumber<'s> {
    type Output = PositiveOrNaN<'s>;

    fn mul(self, rhs: Self) -> Self::Output {
        if self.is_inf() {
            return if rhs.is_zero() {
                PositiveOrNaN::NaN
            } else {
                PositiveNumber::infinity().into()
            };
        } else if rhs.is_inf() {
            return if self.is_zero() {
                PositiveOrNaN::NaN
            } else {
                PositiveNumber::infinity().into()
            };
        }

        let mut result = PositiveNumber::default();
        for rhs_index in rhs.right_most_index()..=rhs.left_most_index() {
            result += self
                .mul_by_single_digit(rhs.get_digit(rhs_index))
                .mul_10_power(rhs_index);
        }

        if result.s.ends_with('0') && !result.s.ends_with(".0") {
            let mut s = result.s.to_string();
            s.pop();
            result.s = s.into();
        }
        result.into()
    }
}

impl<'s> Div for PositiveNumber<'s> {
    type Output = PositiveNumber<'s>;

    /// Adopted from https://github.com/phishman3579/java-algorithms-implementation
    fn div(self, rhs: Self) -> Self::Output {
        assert_ne!(rhs.s, ZERO);

        let mut abs_a: i64 = f64::from(StringNumber(self.s.to_string())) as i64;
        let abs_b: i64 = f64::from(StringNumber(rhs.s.to_string())) as i64;
        let mut temp_a = 0_i64;
        let mut temp_b = 0_i64;
        let mut counter = 0_i64;

        let mut result = 0_i64;
        while abs_a >= abs_b {
            temp_a = abs_a >> 1;
            temp_b = abs_b;
            counter = 1;
            while temp_a >= temp_b {
                temp_b <<= 1;
                counter <<= 1;
            }
            abs_a -= temp_b;
            result += counter;
        }

        Cow::from((result as f64).to_string()).into()
    }
}

#[derive(Debug)]
enum PositiveOrNaN<'s> {
    Positive(PositiveNumber<'s>),
    NaN,
}

impl PositiveOrNaN<'_> {
    fn negative_if_positive(self) -> StringNumber {
        match self {
            PositiveOrNaN::Positive(p) => p.negative().into(),
            PositiveOrNaN::NaN => StringNumber::nan(),
        }
    }
}

impl<'s> From<PositiveNumber<'s>> for PositiveOrNaN<'s> {
    fn from(p: PositiveNumber<'s>) -> Self {
        PositiveOrNaN::Positive(p)
    }
}

#[derive(Debug)]
struct NegativeNumber<'s> {
    s: Cow<'s, str>,
    // decimal_index >= 1
    decimal_index: usize,
}

impl<'s> NegativeNumber<'s> {
    fn new(s: &'s str) -> Self {
        debug_assert!(s != NAN_STR);

        let stripped = s.strip_prefix('-').unwrap();
        let decimal_index = if s == NEG_INFINITY_STR {
            0
        } else {
            stripped.find(DECIMAL).unwrap()
        };

        Self {
            s: stripped.into(),
            decimal_index,
        }
    }

    fn positive(self) -> PositiveNumber<'s> {
        PositiveNumber {
            s: self.s,
            decimal_index: self.decimal_index,
        }
    }
}

impl GetDigit for NegativeNumber<'_> {
    fn str(&self) -> &str {
        &self.s
    }

    fn decimal_index(&self) -> usize {
        self.decimal_index
    }
}

trait GetDigit {
    fn str(&self) -> &str;

    fn decimal_index(&self) -> usize;

    /// -1 = 1/10th digit
    /// 0 = 1s digit
    /// 1 = 10s digit
    fn get_digit(&self, mut index: isize) -> u8 {
        if index < 0 {
            // Skip past decimal point
            index -= 1;
        }

        // TODO is checked sub necessary?
        if let Some(byte_index) = (self.decimal_index() as isize).checked_sub(index + 1) {
            self.str()
                .as_bytes()
                .get(byte_index as usize)
                .map_or(0, |&b| match b {
                    b'-' => 0, // TODO probably not necessary
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

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::{BigInt, Sign};
    use quickcheck::{Arbitrary, Gen};
    use quickcheck_macros::quickcheck;
    use rstest::rstest;
    use std::ops::Deref;
    use std::panic::{catch_unwind, set_hook, take_hook, UnwindSafe};

    fn catch_unwind_silent<F: FnOnce() -> R + UnwindSafe, R>(f: F) -> std::thread::Result<R> {
        let prev_hook = take_hook();
        set_hook(Box::new(|_| {}));
        let result = catch_unwind(f);
        set_hook(prev_hook);
        result
    }

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
    #[case(0.0, 0.0, Some(Ordering::Equal))] // 1
    #[case(0.0, -0.0, Some(Ordering::Equal))] // 2
    #[case(1.0, 0.0, Some(Ordering::Greater))] // 3
    #[case(0.0, 1.0, Some(Ordering::Less))] // 4
    #[case(0.0, -1.0, Some(Ordering::Greater))] // 5
    #[case(-1.0, 0.0, Some(Ordering::Less))] // 6
    #[case(-1.0, 1.0, Some(Ordering::Less))] // 7
    #[case(1.0, -1.0, Some(Ordering::Greater))] // 8
    #[case(-1.0, -1.0, Some(Ordering::Equal))] // 9
    #[case(-1.0, -2.0, Some(Ordering::Greater))] // 10
    #[case(120.0, 21.0, Some(Ordering::Greater))] // 11
    #[case(-120.0, -21.0, Some(Ordering::Less))] // 12
    #[case(0.1, 0.2, Some(Ordering::Less))] // 13
    #[case(0.2, 0.1, Some(Ordering::Greater))] // 14
    #[case(f64::NAN, f64::NAN, None)] // 15
    #[case(f64::INFINITY, 0.0, Some(Ordering::Greater))] // 16
    #[case(1000.0, f64::INFINITY, Some(Ordering::Less))] // 17
    #[case(f64::NEG_INFINITY, 0.0, Some(Ordering::Less))] // 18
    #[case(f64::NEG_INFINITY, f64::INFINITY, Some(Ordering::Less))] // 19
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
    #[case(0.0, 1.2, 1.2)] // 24
    fn add(#[case] a: f64, #[case] b: f64, #[case] expected: f64) {
        assert_eq!(
            StringNumber::from(a) + StringNumber::from(b),
            StringNumber::from(expected)
        );
    }

    #[quickcheck]
    fn add_quickcheck(a: NoShrink<BigDecimal>, b: NoShrink<BigDecimal>) -> bool {
        let a = a.into_inner().into_inner();
        let b = b.into_inner().into_inner();
        StringNumber::from(&a) + StringNumber::from(&b) == StringNumber::from(&(a + b))
    }

    #[rstest]
    #[case(0.0, 0.0, 0.0)] // 1
    #[case(1.0, 0.0, 1.0)] // 2
    #[case(0.0, 1.0, -1.0)] // 3
    #[case(-1.0, 0.0, -1.0)] // 4
    #[case(0.0, -1.0, 1.0)] // 5
    #[case(1.0, 1.0, 0.0)] // 6
    #[case(1.0, -1.0, 2.0)] // 7
    #[case(-1.0, 1.0, -2.0)] // 8
    #[case(f64::NAN, 0.0, f64::NAN)] // 9
    #[case(f64::INFINITY, 1.0, f64::INFINITY)] // 10
    #[case(f64::NEG_INFINITY, 1.0, f64::NEG_INFINITY)] // 11
    #[case(f64::INFINITY, f64::INFINITY, f64::NAN)] // 12
    fn sub(#[case] a: f64, #[case] b: f64, #[case] expected: f64) {
        assert_eq!(
            StringNumber::from(a) - StringNumber::from(b),
            StringNumber::from(expected)
        );
    }

    #[quickcheck]
    fn sub_quickcheck(a: NoShrink<BigDecimal>, b: NoShrink<BigDecimal>) -> bool {
        let a = a.into_inner().into_inner();
        let b = b.into_inner().into_inner();
        StringNumber::from(&a) - StringNumber::from(&b) == StringNumber::from(&(a - b))
    }

    #[rstest]
    #[case(0.0, 0, -1)]
    #[case(1.0, 0, -1)]
    #[case(1.2, 0, -1)]
    #[case(12.34, 1, -2)]
    fn left_most_index_right_most_index(
        #[case] f: f64,
        #[case] expected_left_most_index: isize,
        #[case] expected_right_most_index: isize,
    ) {
        let number = PositiveNumber::from(f);
        assert_eq!(number.left_most_index(), expected_left_most_index);
        assert_eq!(number.right_most_index(), expected_right_most_index);
    }

    #[rstest]
    #[case(vec![], 0, "0.0")]
    #[case(vec![0], 0, "0.0")]
    #[case(vec![0], 1, "0.0")]
    #[case(vec![1, 0], 0, "0.01")]
    #[case(vec![1, 0], 1, "0.1")]
    #[case(vec![1, 0], 2, "01.0")]
    #[case(vec![0, 1], 0, "0.10")]
    #[case(vec![0, 1], 1, "1.0")]
    #[case(vec![0, 1], 2, "10.0")]
    fn digits_to_string(
        #[case] digits: Vec<u8>,
        #[case] decimal_index: usize,
        #[case] expected: &str,
    ) {
        assert_eq!(
            PositiveNumber::digits_to_string(digits, decimal_index),
            expected
        );
    }

    #[test]
    fn digits_to_string_panic() {
        assert!(catch_unwind_silent(|| PositiveNumber::digits_to_string(vec![], 2)).is_err());
    }

    #[rstest]
    #[case(0.0, 0, 0.0)] // 1
    #[case(1.0, 0, 1.0)] // 2
    #[case(0.0, 1, 0.0)] // 3
    #[case(1.0, 1, 10.0)] // 4
    #[case(1.0, -1, 0.1)] // 5
    #[case(0.1, 1, 1.0)] // 6
    #[case(0.1, -1, 0.01)] // 7
    #[case(10.2, 2, 1020.0)] // 8
    #[case(1.2, -1, 0.12)] // 9
    #[case(1.2, -2, 0.012)] // 10
    fn mul_10_power(#[case] number: f64, #[case] power: isize, #[case] expected: f64) {
        assert_eq!(
            PositiveNumber::from(number).mul_10_power(power),
            PositiveNumber::from(expected)
        );
    }

    #[rstest]
    #[case(0.0, 0, 0.0)]
    #[case(1.0, 0, 0.0)]
    #[case(0.0, 1, 0.0)]
    #[case(1.0, 1, 1.0)]
    #[case(2.0, 1, 2.0)]
    #[case(1.0, 2, 2.0)]
    #[case(1.2, 2, 2.4)]
    #[case(1.2, 2, 2.4)]
    #[case(12.34, 2, 24.68)]
    #[case(0.2, 8, 1.6)]
    #[case(12.34, 4, 49.36)]
    #[case(12.34, 9, 111.06)]
    #[case(12.34, 0, 0.0)]
    fn mul_by_single_digit(#[case] number: f64, #[case] n: u8, #[case] expected: f64) {
        assert_eq!(
            PositiveNumber::from(number).mul_by_single_digit(n),
            PositiveNumber::from(expected)
        );
    }

    #[rstest]
    #[case(0.0, 0.0, 0.0)] // 1
    #[case(0.0, 1.0, 0.0)] // 2
    #[case(1.0, 0.0, 0.0)] // 3
    #[case(1.0, 1.0, 1.0)] // 4
    #[case(12.0, 1.0, 12.0)] // 5
    #[case(1.0, 12.0, 12.0)] // 6
    #[case(12.0, 34.0, 408.0)] // 7
    #[case(7.9, 6.8, 53.72)] // 8
    #[case(1.0, -1.0, -1.0)] // 9
    #[case(-1.0, 1.0, -1.0)] // 10
    #[case(-1.0, -1.0, 1.0)] // 11
    #[case(f64::NAN, 0.0, f64::NAN)] // 12
    #[case(0.0, f64::NAN, f64::NAN)] // 13
    #[case(f64::INFINITY, 1.0, f64::INFINITY)] // 14
    #[case(1.0, f64::INFINITY, f64::INFINITY)] // 15
    #[case(f64::INFINITY, 0.0, f64::NAN)] // 16
    #[case(0.0, f64::INFINITY, f64::NAN)] // 17
    fn mul(#[case] a: f64, #[case] b: f64, #[case] expected: f64) {
        assert_eq!(
            StringNumber::from(a) * StringNumber::from(b),
            StringNumber::from(expected)
        )
    }

    #[quickcheck]
    fn mul_quickcheck(a: NoShrink<BigDecimal>, b: NoShrink<BigDecimal>) -> bool {
        let a = a.into_inner().into_inner();
        let b = b.into_inner().into_inner();
        StringNumber::from(&a) * StringNumber::from(&b) == StringNumber::from(&(a * b))
    }

    #[rstest]
    #[case("0", "0.0")]
    #[case("0.0", "0.0")]
    #[case("001.0", "1.0")]
    #[case("-001.0", "-1.0")]
    #[case("0.100", "0.1")]
    #[case(".1", "0.1")]
    #[case("-.1", "-0.1")]
    fn fix_zeros(#[case] s: &str, #[case] expected: &str) {
        let mut result = s.to_string();
        StringNumber::fix_zeros(&mut result);
        assert_eq!(result, expected);
    }

    #[rstest]
    #[case(0.0, 1.0, 0.0)] // 1
    #[case(1.0, 1.0, 1.0)] // 2
    #[case(2.0, 1.0, 2.0)] // 3
    #[case(3.0, 2.0, 1.0)] // 4
    #[case(2.0, 3.0, 0.0)] // 5
    fn div(#[case] a: f64, #[case] b: f64, #[case] expected: f64) {
        assert_eq!(
            StringNumber::from(a) / StringNumber::from(b),
            StringNumber::from(expected)
        )
    }

    #[test]
    fn div_by_zero() {
        assert!(catch_unwind_silent(|| StringNumber::from(0.0) / StringNumber::from(0.0)).is_err());
    }

    #[derive(Debug, Clone)]
    struct BigDecimal(bigdecimal::BigDecimal);

    impl BigDecimal {
        fn into_inner(self) -> bigdecimal::BigDecimal {
            self.0
        }
    }

    impl Arbitrary for BigDecimal {
        fn arbitrary(g: &mut Gen) -> Self {
            let sign = match u64::arbitrary(g) % 3 {
                0 => Sign::Minus,
                1 => Sign::NoSign,
                2 => Sign::Plus,
                _ => unreachable!(),
            };
            let mut digits: Vec<u32> = Vec::new();
            digits.resize_with(u8::arbitrary(g) as usize, || Arbitrary::arbitrary(g));
            Self(bigdecimal::BigDecimal::new(
                BigInt::new(sign, digits),
                u8::arbitrary(g) as i64,
            ))
        }
    }

    impl Deref for BigDecimal {
        type Target = bigdecimal::BigDecimal;

        fn deref(&self) -> &Self::Target {
            &self.0
        }
    }

    // https://github.com/BurntSushi/quickcheck/pull/293/files
    #[derive(Clone, Debug)]
    struct NoShrink<A: Arbitrary> {
        inner: A,
    }

    impl<A: Arbitrary> NoShrink<A> {
        fn into_inner(self) -> A {
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
