# Nom Recipes

These are short recipes for accomplishing common tasks with nom.

- [Whitespace](#whitespace)
  - [Wrapper combinators that eat whitespace before and after a parser](#wrapper-combinators-that-eat-whitespace-before-and-after-a-parser)
- [Comments](#comments)
  - [`// C++/EOL-style comments`](#-ceol-style-comments)
  - [`/* C-style comments */`](#-c-style-comments-)
- [Identifiers](#identifiers)
  - [`Rust-Style Identifiers`](#rust-style-identifiers)
- [Literal Values](#literal-values)
  - [Escaped Strings](#escaped-strings)
  - [Integers](#integers)
    - [Hexadecimal](#hexadecimal)
    - [Octal](#octal)
    - [Binary](#binary)
    - [Decimal](#decimal)
  - [Floating Point Numbers](#floating-point-numbers)

## Whitespace

### Wrapper combinators that eat whitespace before and after a parser

```rust
/// A combinator that takes a parser `inner` and produces a parser that also consumes both leading and
/// trailing whitespace, returning the output of `inner`.
fn ws<'a, F: 'a, O, E: ParseError<&'a str>>(inner: F) -> impl FnMut(&'a str) -> IResult<&'a str, O, E>
  where
  F: Fn(&'a str) -> IResult<&'a str, O, E>,
{
  delimited(
    multispace0,
    inner,
    multispace0
  )
}
```

To eat only trailing whitespace, replace `delimited(...)` with `terminated(&inner, multispace0)`.
Likewise, the eat only leading whitespace, replace `delimited(...)` with `preceded(multispace0, &inner)`. You can use your own parser instead of `multispace0` if you want to skip a different set
of lexemes.

## Comments

### `// C++/EOL-style comments`

This version uses `%` to start a comment, does not consume the newline character, and returns an
output of `()`.

```rust
pub fn peol_comment<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, (), E>
{
  value(
    (), // Output is thrown away.
    pair(char('%'), is_not("\n\r"))
  )(i)
}
```

### `/* C-style comments */`

Inline comments surrounded with sentinel tags `(*` and `*)`. This version returns an output of `()`
and does not handle nested comments.

```rust
pub fn pinline_comment<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, (), E> {
  value(
    (), // Output is thrown away.
    tuple((
      tag("(*"),
      take_until("*)"),
      tag("*)")
    ))
  )(i)
}
```

## Identifiers

### `Rust-Style Identifiers`

Parsing identifiers that may start with a letter (or underscore) and may contain underscores,
letters and numbers may be parsed like this:

```rust
pub fn identifier(input: &str) -> IResult<&str, &str> {
  preceded(
    peek(alt((alpha1, tag("_")))),
    take_while1(|ch| is_alphanumeric(ch as u8) || ch == '_'),
  )(input)
}
```

The first `preceded` combinator will allow us to ignore the `peek` and only take
the output from `take_while`. The `peek` basically just runs the parser within
but does not consume the input. Within that, we check if the next character is a
letter (any case) or an underscore as you can't start an identifier with a
number. After that, we consume the rest of the identifier within the
`take_while` as long as the character is a letter, number, or underscore. This
way, it will either assert that the identifier is valid, or return an error. You
would mostly use this combinator with two parsers surrounding it such as in the
case of a basic variable initialization parser like in the following example:

```rust
pub fn function(input: &str) -> IResult<&str, &str> {
  delimited(pair(tag("let"), multispace1), identifier, char(';'))
}
// PASS let foo;
// PASS let _asdf234;
// FAIL let 34asdf;
// FAIL let a\nb; (newlines)
```

## Literal Values

### Escaped Strings

This is [one of the examples](https://github.com/Geal/nom/blob/master/examples/string.rs) in the
examples directory.

### Integers

The following recipes all return string slices rather than integer values. How to obtain an
integer value instead is demonstrated for hexadecimal integers. The others are similar.

The parsers allow the grouping character `_`, which allows one to group the digits by byte, for
example: `0xA4_3F_11_28`. If you prefer to exclude the `_` character, the lambda to convert from a
string slice to an integer value is slightly simpler. You can also strip the `_` from the string
slice that is returned, which is demonstrated in the second hexdecimal number parser.

If you wish to limit the number of digits in a valid integer literal, replace `many1` with
`many_m_n` in the recipes.

#### Hexadecimal

The parser outputs the string slice of the digits without the leading `0x`/`0X`.

```rust
fn hexadecimal(input: &str) -> IResult<&str, &str> { // <'a, E: ParseError<&'a str>>
  preceded(
    alt((tag("0x"), tag("0X"))),
    recognize(
      many1(
        terminated(one_of("0123456789abcdefABCDEF"), many0(char('_')))
      )
    )
  )(input)
}
```

If you want it to return the integer value instead, use map:

```rust
fn hexadecimal_value(input: &str) -> IResult<&str, i64> {
  map_res(
    preceded(
      alt((tag("0x"), tag("0X"))),
      recognize(
        many1(
          terminated(one_of("0123456789abcdefABCDEF"), many0(char('_')))
        )
      )
    ),
    |out: &str| i64::from_str_radix(&str::replace(&out, "_", ""), 16)
  )(input)
}
```

#### Octal

```rust
fn octal(input: &str) -> IResult<&str, &str> {
  preceded(
    alt((tag("0o"), tag("0O"))),
    recognize(
      many1(
        terminated(one_of("01234567"), many0(char('_')))
      )
    )
  )(input)
}
```

#### Binary

```rust
fn binary(input: &str) -> IResult<&str, &str> {
  preceded(
    alt((tag("0b"), tag("0B"))),
    recognize(
      many1(
        terminated(one_of("01"), many0(char('_')))
      )
    )
  )(input)
}
```

#### Decimal

```rust
fn decimal(input: &str) -> IResult<&str, &str> {
  recognize(
    many1(
      terminated(one_of("0123456789"), many0(char('_')))
    )
  )(input)
}
```

### Floating Point Numbers

The following is adapted from [the Python parser by Valentin Lorentz (ProgVal)](https://github.com/ProgVal/rust-python-parser/blob/master/src/numbers.rs).

```rust
fn float(input: &str) -> IResult<&str, &str> {
  alt((
    // Case one: .42
    recognize(
      tuple((
        char('.'),
        decimal,
        opt(tuple((
          one_of("eE"),
          opt(one_of("+-")),
          decimal
        )))
      ))
    )
    , // Case two: 42e42 and 42.42e42
    recognize(
      tuple((
        decimal,
        opt(preceded(
          char('.'),
          decimal,
        )),
        one_of("eE"),
        opt(one_of("+-")),
        decimal
      ))
    )
    , // Case three: 42. and 42.42
    recognize(
      tuple((
        decimal,
        char('.'),
        opt(decimal)
      ))
    )
  ))(input)
}
```

# implementing FromStr

The [FromStr trait](https://doc.rust-lang.org/std/str/trait.FromStr.html) provides
a common interface to parse from a string.

```rust
use nom::{
  IResult, Finish, error::Error,
  bytes::complete::{tag, take_while},
};
use std::str::FromStr;

// will recognize the name in "Hello, name!"
fn parse_name(input: &str) -> IResult<&str, &str> {
  let (i, _) = tag("Hello, ")(input)?;
  let (i, name) = take_while(|c:char| c.is_alphabetic())(i)?;
  let (i, _) = tag("!")(i)?;

  Ok((i, name))
}

// with FromStr, the result cannot be a reference to the input, it must be owned
#[derive(Debug)]
pub struct Name(pub String);

impl FromStr for Name {
  // the error must be owned as well
  type Err = Error<String>;

  fn from_str(s: &str) -> Result<Self, Self::Err> {
      match parse_name(s).finish() {
          Ok((_remaining, name)) => Ok(Name(name.to_string())),
          Err(Error { input, code }) => Err(Error {
              input: input.to_string(),
              code,
          })
      }
  }
}

fn main() {
  // parsed: Ok(Name("nom"))
  println!("parsed: {:?}", "Hello, nom!".parse::<Name>());

  // parsed: Err(Error { input: "123!", code: Tag })
  println!("parsed: {:?}", "Hello, 123!".parse::<Name>());
}
```
