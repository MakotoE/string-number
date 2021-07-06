use std::cmp::Ordering;
use std::collections::VecDeque;
use std::ops::Add;

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct StringNumber(String);

impl StringNumber {
    pub fn get_positive(&self) -> Self {
        Self(self.0.strip_prefix('-').unwrap_or(&self.0).to_string())
    }

    /// self and rhs must be positive.
    fn add_positive_numbers(self, rhs: Self) -> StringNumber {
        let mut result_digits: VecDeque<u8> = VecDeque::new();
        let lhs_digits = Digits::new(&self);
        let rhs_digits = Digits::new(&rhs);

        debug_assert!(!lhs_digits.is_negative());
        debug_assert!(!rhs_digits.is_negative());

        let mut carry = 0_u8;

        let mut digit = 0_isize;
        loop {
            let lhs_digit = lhs_digits.get_digit(digit);
            let rhs_digit = rhs_digits.get_digit(digit);
            if lhs_digit == 0 && rhs_digit == 0 {
                break;
            }

            let mut digit_sum = lhs_digit + rhs_digit + carry;
            if digit_sum >= 10 {
                carry = 1;
                digit_sum -= 10;
            } else {
                carry = 0;
            }
            result_digits.push_front(digit_sum);
            digit += 1;
        }

        if carry > 0 {
            result_digits.push_front(carry);
        }

        if result_digits.is_empty() {
            result_digits.push_front(0);
        }

        let bytes: Vec<u8> = result_digits
            .iter()
            .copied()
            .map(Digits::number_to_ascii)
            .collect();
        StringNumber(String::from_utf8(bytes).unwrap())
    }

    /// self and rhs must be positive.
    fn subtract_positive_numbers(self, rhs: Self) -> StringNumber {
        todo!()
    }

    /// smaller > 0, greater >= smaller
    fn subtract_ordered(greater: Self, smaller: Self) -> Self {
        let mut result_digits: VecDeque<u8> = VecDeque::new();
        let lhs_digits = Digits::new(&greater);
        let rhs_digits = Digits::new(&smaller);

        debug_assert!(!lhs_digits.is_negative());
        debug_assert!(!rhs_digits.is_negative());

        let mut carry = 0_i8;

        let mut digit = 0_isize;
        loop {
            let lhs_digit = lhs_digits.get_digit(digit) as i8;
            let rhs_digit = rhs_digits.get_digit(digit) as i8;
            if lhs_digit == 0 && rhs_digit == 0 {
                break;
            }

            let mut digit_difference = lhs_digit - carry - rhs_digit;
            if digit_difference < 0 {
                carry = 1;
                digit_difference += 10;
            } else {
                carry = 0;
            }
            result_digits.push_front(digit_difference as u8);
            digit += 1;
        }

        if result_digits.is_empty() {
            result_digits.push_front(0);
        }

        let mut bytes: Vec<u8> = result_digits
            .iter()
            .copied()
            .map(Digits::number_to_ascii)
            .collect();

        StringNumber(String::from_utf8(bytes).unwrap())
    }
}

impl Add for StringNumber {
    type Output = StringNumber;

    fn add(self, rhs: Self) -> Self::Output {
        let lhs_negative = Digits::new(&self).is_negative();
        let rhs_negative = Digits::new(&rhs).is_negative();
        if lhs_negative && rhs_negative {
            self.get_positive().add_positive_numbers(rhs.get_positive())
        } else if lhs_negative && !rhs_negative {
            rhs.subtract_positive_numbers(self.get_positive())
        } else if !lhs_negative && rhs_negative {
            self.subtract_positive_numbers(rhs.get_positive())
        } else {
            self.add_positive_numbers(rhs)
        }
    }
}

impl PartialOrd for StringNumber {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if self == &0.0.into() && other == &(-0.0).into()
            || self == &(-0.0).into() && other == &0.0.into()
        {
            return Some(Ordering::Equal);
        }

        let mut lhs_digits = Digits::new(self);
        let mut rhs_digits = Digits::new(other);

        let lhs_positive = self.get_positive();
        let rhs_positive = other.get_positive();

        if lhs_digits.is_negative() {
            if !rhs_digits.is_negative() {
                return Some(Ordering::Less);
            }
        } else {
            if rhs_digits.is_negative() {
                return Some(Ordering::Greater);
            }
        }

        let flipped = lhs_digits.is_negative() && rhs_digits.is_negative();
        if flipped {
            lhs_digits = Digits::new(&lhs_positive);
            rhs_digits = Digits::new(&rhs_positive);
        };

        Some(match lhs_digits.compare_positive(&rhs_digits) {
            Ordering::Less if flipped => Ordering::Greater,
            Ordering::Greater if flipped => Ordering::Less,
            ordering => ordering,
        })
    }
}

impl From<f64> for StringNumber {
    fn from(n: f64) -> Self {
        Self(n.to_string())
    }
}

impl Default for StringNumber {
    fn default() -> Self {
        Self("0".to_string())
    }
}

struct Digits<'s> {
    s: &'s str,
    decimal_index: usize,
}

impl<'s> Digits<'s> {
    fn new(string_number: &'s StringNumber) -> Self {
        Self {
            s: &string_number.0,
            decimal_index: string_number.0.find('.').unwrap_or(string_number.0.len()),
        }
    }

    fn ascii_to_number(b: u8) -> u8 {
        b - b'0'
    }

    fn number_to_ascii(n: u8) -> u8 {
        n + b'0'
    }

    /// -1 = 1/10th digit
    /// 0 = 1s digit
    /// 1 = 10s digit
    fn get_digit(&self, mut index: isize) -> u8 {
        if index < 0 {
            // Skip past decimal point
            index -= 1;
        }

        if let Some(byte_index) = (self.decimal_index as isize).checked_sub(index + 1) {
            self.s
                .as_bytes()
                .get(byte_index as usize)
                .map_or(0, |&b| match b {
                    b'-' => 0,
                    _ => Digits::ascii_to_number(b),
                })
        } else {
            0
        }
    }

    fn is_negative(&self) -> bool {
        self.s.starts_with('-')
    }

    fn left_most_index(&self) -> isize {
        self.decimal_index as isize - 1
    }

    /// self and rhs must be positive
    fn compare_positive(&self, other: &Self) -> Ordering {
        debug_assert!(!self.is_negative());
        debug_assert!(!other.is_negative());

        let mut lhs_index = self.left_most_index();
        let mut rhs_index = other.left_most_index();

        loop {
            let lhs_digit = self.get_digit(lhs_index);
            let rhs_digit = other.get_digit(rhs_index);

            if lhs_digit == 0 && rhs_digit == 0 {
                return Ordering::Equal;
            }

            match lhs_digit.partial_cmp(&rhs_digit) {
                Some(ordering) => {
                    if matches!(ordering, Ordering::Less | Ordering::Greater) {
                        return ordering;
                    }
                }
                None => unreachable!(),
            }

            lhs_index -= 1;
            rhs_index -= 1;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
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
        assert_eq!(Digits::new(&number.into()).get_digit(index), expected);
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
                            // TODO negative and non-integer
    fn add(#[case] a: f64, #[case] b: f64, #[case] expected: f64) {
        assert_eq!(
            StringNumber::from(a) + StringNumber::from(b),
            StringNumber::from(expected)
        );
    }

    #[rstest]
    #[case(0.0, 0.0, Ordering::Equal)]
    #[case(0.0, -0.0, Ordering::Equal)]
    #[case(1.0, 0.0, Ordering::Greater)]
    #[case(0.0, 1.0, Ordering::Less)]
    #[case(0.0, -1.0, Ordering::Greater)]
    #[case(-1.0, 0.0, Ordering::Less)]
    #[case(-1.0, 1.0, Ordering::Less)]
    #[case(1.0, -1.0, Ordering::Greater)]
    fn partial_cmp(#[case] a: f64, #[case] b: f64, #[case] expected: Ordering) {
        assert_eq!(StringNumber::from(a).partial_cmp(&b.into()), Some(expected));
    }
}
