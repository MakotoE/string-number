use std::collections::VecDeque;
use std::ops::Add;

#[derive(Debug, Eq, PartialEq)]
pub struct StringNumber(String);

impl Add for StringNumber {
    type Output = StringNumber;

    fn add(self, rhs: Self) -> Self::Output {
        let mut result_digits: VecDeque<u8> = VecDeque::new();
        let lhs_digits = Digits::new(&self.0);
        let rhs_digits = Digits::new(&rhs.0);

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
    fn new(s: &'s str) -> Self {
        Self {
            s,
            decimal_index: s.len(),
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
    fn get_digit(&self, index: isize) -> u8 {
        if index > self.s.len() as isize - 1 {
            return 0;
        }

        self.s
            .as_bytes()
            .get(self.s.len() - index as usize - 1)
            .copied()
            .map_or(0, Digits::ascii_to_number)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rstest::rstest;

    #[rstest]
    #[case(0.0, 0.0, 0.0)]
    #[case(1.0, 0.0, 1.0)]
    #[case(0.0, 1.0, 1.0)]
    #[case(1.0, 2.0, 3.0)]
    #[case(1.0, 10.0, 11.0)]
    #[case(5.0, 5.0, 10.0)]
    #[case(15.0, 5.0, 20.0)]
    #[case(15.0, 16.0, 31.0)]
    #[case(55.0, 65.0, 120.0)]
    // #[case(0.0, -0.0, 0.0)]
    // TODO negative and non-integer
    fn add(#[case] a: f64, #[case] b: f64, #[case] expected: f64) {
        assert_eq!(
            StringNumber::from(a) + StringNumber::from(b),
            StringNumber::from(expected)
        );
    }
}
