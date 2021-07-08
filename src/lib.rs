use bigdecimal::BigDecimal;
use std::cmp::Ordering;
use std::collections::VecDeque;
use std::ops::{Add, Sub};

const INFINITY_STR: &str = "inf";
const NEG_INFINITY_STR: &str = "-inf";
const NAN_STR: &str = "NaN";

#[derive(Debug, Clone, Eq)]
pub struct StringNumber(String);

impl Default for StringNumber {
    fn default() -> Self {
        Self("0".to_string())
    }
}

impl From<f64> for StringNumber {
    fn from(n: f64) -> Self {
        let mut s = n.to_string();
        if !(s == INFINITY_STR || s == NEG_INFINITY_STR || s == NAN_STR || s.contains('.')) {
            s.push_str(".0");
        }
        Self(s)
    }
}

impl From<&BigDecimal> for StringNumber {
    fn from(bd: &BigDecimal) -> Self {
        Self(bd.to_string())
    }
}

impl Into<f64> for StringNumber {
    /// Doesn't return correct NaN
    fn into(self) -> f64 {
        self.0.parse().unwrap()
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
        self.s == INFINITY_STR
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

        // TODO don't use VecDeque
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
        bytes.insert(decimal_index + carry as usize, b'.');
        if decimal_index == bytes.len() - 1 {
            bytes.push(b'0');
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
    use num_bigint::{BigInt, Sign};
    use quickcheck::{Arbitrary, Gen};
    use quickcheck_macros::quickcheck;
    use rstest::rstest;
    use std::ops::Deref;

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

    #[test]
    fn test() {
        let a = bigdecimal::BigDecimal::from(0);
        let b = "1947180860012190420183833017535085365939433575159925911934686960276858290031676725642722279903539131606215742246224577812268301524429403672714456723895964962401226312401217413182487193316670341163755465162711309692671900070047666158234634951417807817193243374009723500608181433495000786736395969438801016740621615516673100282035649644424470743656364511840609893073071848842450191575351647726951924463327827253483766473878851981003668203161068438017352637948163266532332165424678463157053775521135499419826216229658132920628012644079456770831265389535948499787081421355799230049532544187647983131681326942155172134180505210418599117869883766619094639371814043121643159261134309054646979083159707302350872603228384690009491999013934659019708667838376247826801243879032763097041285471562331314538827849312911721266893431787585882599298207877696551693506876486054319736136808445261429714960335413449113250338731768617699764067729329801333878566291022160184132897034371868563053951677519909352906128192787177927047181086026836073592273172542189786618856931742769609890600203536258172294458428398893832765694563598787400142973019177447627176136895566383581403881863192600554150674713670486115291369298422034604527905421586713470591542677033072778909897355167963053979330904342181848834028532518235849905323621771590593323107712472208220691659661617075746801775232357216380081026926955610679234022456441715144928273745160441280903587494209144521539075265822980854917563720925911428143397627970321737622630295957485836526248709709237889111527181108362199311798975376399688024660909873934161967118715629677336307614631051120181030340757182921798349300148530962078352548972195938061746998132888609654822588013899386669759385651055057589706107260857919337023252923622154405574965497367273161562318955376342698188407052541188782017005165869050441605603.55674106827689381544194825757738719691116602260913114070241088783703005394038230962519239410708880608577806768377701851540431733879671964065870074853874376589506226019174983950377650935586087573975529306172183888".parse().unwrap();
        let result = StringNumber::from(&a) + StringNumber::from(&b);
        let expected = StringNumber::from(&(a + b));
        assert_eq!(result, expected);
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
