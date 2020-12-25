//! A library for parsing expressions.

/// The result of a parsing function.
///
/// All parsing functions provided by this library return a
/// `ParseResult<Output>` where `Output` is the expected output type.
pub type ParseResult<'a, Output> = Result<(Output, &'a str), &'a str>;

/// An interface for parsers.
///
/// Currently only the `parse` function is required to be implemented. A blanket
/// implementation is also provided for all functions that take a `&str` input
/// and return a `ParseResult`.
pub trait Parser<'a> {
    /// Expected return type of the parser.
    type Output;

    /// Parses `s` and returns a `ParseResult`.
    ///
    /// A successful parse returns the `Ok` result with the remaining unmatched
    /// part of the string. An unsuccessful parse returns an `Err` with the
    /// unmatched string.
    fn parse(&self, s: &'a str) -> ParseResult<'a, Self::Output>;
}

/// An implementation of `Parser` for all functions that input a `&str` and return a `ParseResult`.
impl<'a, F, Output> Parser<'a> for F
where
    F: Fn(&'a str) -> ParseResult<Output>,
{
    type Output = Output;

    fn parse(&self, s: &'a str) -> ParseResult<'a, Self::Output> {
        self(s)
    }
}

/// A parser that takes another parser `p` and tries to match it successively at
/// least once. Returns a `Vec` of all matched values.
pub fn one_or_more<'a, P, Op>(p: P) -> impl Parser<'a, Output = Vec<Op>>
where
    P: Parser<'a, Output = Op>,
{
    move |mut s: &'a str| {
        let mut result: Vec<Op> = Vec::new();

        if let Ok((item, rem_str)) = p.parse(s) {
            result.push(item);
            s = rem_str;
        } else {
            return Err(s);
        }

        while let Ok((item, rem_str)) = p.parse(s) {
            result.push(item);
            s = rem_str;
        }
        Ok((result, s))
    }
}

/// A parser that takes another parser `p` and tries to match it successively
/// zero or more times. Returns a `Vec` of all matched values.
pub fn zero_or_more<'a, P, Op>(parser: P) -> impl Parser<'a, Output = Vec<Op>>
where
    P: Parser<'a, Output = Op>,
{
    move |mut s: &'a str| {
        let mut result: Vec<Op> = Vec::new();
        while let Ok((item, rem_str)) = parser.parse(s) {
            result.push(item);
            s = rem_str;
        }
        Ok((result, s))
    }
}

/// A parser that takes another parser `p` and modiefies its output using a
/// mapping function.
pub fn map<'a, P, Op, F, MOp>(parser: P, map_fn: F) -> impl Parser<'a, Output = MOp>
where
    P: Parser<'a, Output = Op>,
    F: Fn(Op) -> Option<MOp>,
{
    move |s: &'a str| {
        parser.parse(s).and_then(|(res, rem_str)| {
            map_fn(res).map_or(Err(rem_str), |mapped| Ok((mapped, rem_str)))
        })
    }
}

/// Combines two parsers and applies them successively. Returns a tuple of the outputs of the two parsers.
///
/// Returns an `Err` if either of the parsers fail.
pub fn combination<'a, P, Op, Q, Oq>(parser0: P, parser1: Q) -> impl Parser<'a, Output = (Op, Oq)>
where
    P: Parser<'a, Output = Op>,
    Q: Parser<'a, Output = Oq>,
{
    move |s: &'a str| {
        parser0.parse(s).and_then(|(res0, rem_str0)| {
            parser1
                .parse(rem_str0)
                .map(|(res1, rem_str1)| ((res0, res1), rem_str1))
        })
    }
}

/// Combines two parsers and returns the output of the first parser (the left
/// parser) only.
///
/// Both parsers must be successful for the combination to be successful, but
/// the second parser's output is ignored.
pub fn left<'a, P, Op, Q, Oq>(parser0: P, parser1: Q) -> impl Parser<'a, Output = Op>
where
    P: Parser<'a, Output = Op>,
    Q: Parser<'a, Output = Oq>,
{
    map(combination(parser0, parser1), |(res0, _)| Some(res0))
}

/// Combines two parsers and returns the output of the second parser (the right
/// parser) only.
///
/// Both parsers must be successful for the combination to be successful, but
/// the first parser's output is ignored.
pub fn right<'a, P, Op, Q, Oq>(parser0: P, parser1: Q) -> impl Parser<'a, Output = Oq>
where
    P: Parser<'a, Output = Op>,
    Q: Parser<'a, Output = Oq>,
{
    map(combination(parser0, parser1), |(_, res1)| Some(res1))
}

/// Applies two parsers to the input and returns the result of whichever parser
/// is successful.
///
/// Both parsers must have the same output type. `choose` is short circuiting,
/// so if the first parser is successful, the second one is never evaluated.
pub fn choose<'a, P, Q, Op>(parser0: P, parser1: Q) -> impl Parser<'a, Output = Op>
where
    P: Parser<'a, Output = Op>,
    Q: Parser<'a, Output = Op>,
{
    move |s: &'a str| parser0.parse(s).or_else(|_| parser1.parse(s))
}

/// Creates a parser that matches a single parser.
pub fn char_parse_builder<'a>(parse_char: char) -> impl Fn(&'a str) -> ParseResult<'a, char> {
    move |s: &'a str| {
        let mut chars = s.chars();
        match chars.next() {
            None => Err(s),
            Some(ch) => {
                if ch == parse_char {
                    Ok((ch, chars.as_str()))
                } else {
                    Err(s)
                }
            }
        }
    }
}

/// A parser that matches any decimal digit.
pub fn digit(s: &str) -> ParseResult<u32> {
    let mut chars = s.chars();
    match chars.next() {
        None => Err(s),
        Some(ch) => match ch.to_digit(10) {
            None => Err(s),
            Some(n) => Ok((n, chars.as_str())),
        },
    }
}

fn whole_num(s: &str) -> ParseResult<u32> {
    fn combine_digits(dits: Vec<u32>) -> Option<u32> {
        if dits.len() > 1 && dits[0] == 0 {
            return None;
        }
        Some(dits.iter().fold(0, |acc, x| acc * 10 + *x))
    }
    map(one_or_more(digit), combine_digits).parse(s)
}

fn negative_sign(s: &str) -> ParseResult<()> {
    let mut chars = s.chars();
    if let Some(ch) = chars.next() {
        if ch == '-' {
            Ok(((), chars.as_str()))
        } else {
            Err(s)
        }
    } else {
        Err(s)
    }
}

fn int(s: &str) -> ParseResult<i32> {
    fn negate(n: u32) -> Option<i32> {
        Some(-(n as i32))
    }

    if let Ok((_, rem_str)) = negative_sign(s) {
        map(whole_num, negate).parse(rem_str)
    } else {
        whole_num
            .parse(s)
            .map(|(res, rem_str)| (res as i32, rem_str))
    }
}

/// Matches zero or more space (`U+0200`) characters.
pub fn spaces(s: &str) -> ParseResult<()> {
    zero_or_more(char_parse_builder(' '))
        .parse(s)
        .map(|(_, rem_str)| ((), rem_str))
}

/// Wraps another parser in `spaces` parsers so that spaces on both sides of the
/// token are ignored.
pub fn whitespace_wrap<'a, P, Op>(parser: P) -> impl Parser<'a, Output = Op>
where
    P: Parser<'a, Output = Op>,
{
    right(spaces, left(parser, spaces))
}

/// A parser that matches an integer.
pub fn integer(s: &str) -> ParseResult<i32> {
    whitespace_wrap(int).parse(s)
}

/// A parser that matches a whole number (zero or a natural number).
pub fn whole_number(s: &str) -> ParseResult<u32> {
    whitespace_wrap(whole_num).parse(s)
}

#[cfg(test)]
mod tests {
    use crate::*;

    #[test]
    fn characters_match() {
        let open_bracket = char_parse_builder('(');
        assert_eq!(Ok(('(', "")), open_bracket.parse("("));
        assert_eq!(Ok(('(', " a")), open_bracket.parse("( a"));
        assert_eq!(Err(" ("), open_bracket.parse(" ("));
    }

    #[test]
    fn multi_parser_works() {
        let digits = one_or_more(digit);
        assert_eq!(Ok((vec![1u32, 2], "")), digits.parse("12"));
        assert_eq!(Ok((vec![1u32, 2], " a")), digits.parse("12 a"));
        assert_eq!(Err("a"), digits.parse("a"));
    }

    #[test]
    fn digit_matching_works() {
        assert_eq!(Ok((1, "")), digit.parse("1"));
        assert_eq!(Ok((1, " a")), digit.parse("1 a"));
        assert_eq!(Err("a"), digit.parse("a"));
    }

    #[test]
    fn can_parse_whole_num() {
        assert_eq!(Ok((0, "")), whole_num.parse("0"));
        assert_eq!(Ok((20, "")), whole_num.parse("20"));
        assert_eq!(Ok((12, " a")), whole_num.parse("12 a"));
        assert_eq!(Err("a"), whole_num.parse("a"));
        assert_eq!(Err("-0"), whole_num.parse("-0"));
        assert_eq!(Err(""), whole_num.parse("020"));
    }

    #[test]
    fn sign_parsing_works() {
        assert_eq!(Ok(((), "")), negative_sign.parse("-"));
        assert_eq!(Ok(((), " a")), negative_sign.parse("- a"));
        assert_eq!(Err("a"), negative_sign.parse("a"));
    }

    #[test]
    fn int_parsing_works() {
        assert_eq!(Ok((0, "")), int.parse("0"));
        assert_eq!(Ok((0, "")), int.parse("-0"));
        assert_eq!(Ok((10, "")), int.parse("10"));
        assert_eq!(Ok((-10, "")), int.parse("-10"));
        assert_eq!(Ok((-10, " a")), int.parse("-10 a"));
        assert_eq!(Err("a"), int.parse("a"));
        assert_eq!(Err(""), int.parse("020"));
        assert_eq!(Err(""), int.parse("-020"));
    }

    #[test]
    fn whitespace_detection() {
        assert_eq!(Ok(((), "")), spaces.parse(" "));
        assert_eq!(Ok(((), "")), spaces.parse("  "));
        assert_eq!(Ok(((), "")), spaces.parse(""));
        assert_eq!(Ok(((), "a")), spaces.parse("a"));
        assert_eq!(Ok(((), "a")), spaces.parse(" a"));
    }

    #[test]
    fn whitespace_wrap_works() {
        assert_eq!(Ok((11, "")), integer.parse("11"));
        assert_eq!(Ok((11, "")), integer.parse(" 11"));
        assert_eq!(Ok((11, "")), integer.parse("11 "));
        assert_eq!(Ok((11, "")), integer.parse(" 11 "));
        assert_eq!(Ok((11, "a")), integer.parse("11  a"));
    }

    #[test]
    fn choice_can_be_made() {
        assert_eq!(
            Ok(('a', "")),
            choose(char_parse_builder('b'), char_parse_builder('a')).parse("a")
        );
        assert_eq!(
            Ok(('a', "")),
            choose(char_parse_builder('a'), char_parse_builder('b')).parse("a")
        );
    }
}
