use std::collections::VecDeque;
use std::iter::repeat;
use std::ops::Add;

#[derive(Debug, Eq, PartialEq)]
pub struct StringNumber(String);

impl StringNumber {
    fn byte_to_number(b: u8) -> u8 {
        b - b'0'
    }

    fn number_to_byte(n: u8) -> u8 {
        n + b'0'
    }
}

impl Add for StringNumber {
    type Output = StringNumber;

    fn add(self, rhs: Self) -> Self::Output {
        let mut result_digits: VecDeque<u8> = VecDeque::new();
        let length = usize::max(self.0.len(), rhs.0.len());
        let lhs_digits: Vec<u8> = self
            .0
            .bytes()
            .rev()
            .map(StringNumber::byte_to_number)
            .chain(repeat(0).take(length - self.0.len()))
            .collect();
        let rhs_digits: Vec<u8> = rhs
            .0
            .bytes()
            .rev()
            .map(StringNumber::byte_to_number)
            .chain(repeat(0).take(length - rhs.0.len()))
            .collect();

        let mut carry = 0_u8;

        for digit in 0..lhs_digits.len() {
            let mut digit_sum = lhs_digits[digit] + rhs_digits[digit] + carry;
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

        let bytes: Vec<u8> = result_digits
            .iter()
            .copied()
            .map(StringNumber::number_to_byte)
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
    // TODO negative and non-integer
    fn add(#[case] a: f64, #[case] b: f64, #[case] expected: f64) {
        assert_eq!(
            StringNumber::from(a) + StringNumber::from(b),
            StringNumber::from(expected)
        );
    }
}
