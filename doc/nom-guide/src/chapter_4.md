# Chapter 4: Parsers With Custom Return Types 

So far, we have seen mostly functions that take an `&str`, and return a
`IResult<&str, &str>`. Splitting strings into smaller strings is certainly useful,
but it's not the only thing Nom is capable of!

A useful operation when parsing is to convert between types; for example
parsing from `&str` to another primitive, like `bool`.

All we need to do for our parser to return a different type is to change
the second type parameter of `IResult` to the desired return type.
For example, to return a bool, return a `IResult<&str, bool>`.

Recall that the first type parameter of the `IResult` is the input
type, so even if you're returning something different, if your input
is a `&str`, the first type argument of `IResult` should be also.

Until you have read the chapter on Errors, we strongly suggest avoiding
the use of parsers built into Rust (like `str.parse`); as they require
special handling to work well with Nom.

That said, one Nom-native way of doing a type conversion is to use the
[`value`](https://docs.rs/nom/latest/nom/combinator/fn.value.html) combinator
to convert from a successful parse to a particular value.

The following code converts from a string containing `"true"` or `"false"`,
to the corresponding `bool`.

```rust
# extern crate nom;
# use std::error::Error;
use nom::IResult;
use nom::bytes::complete::tag;
use nom::combinator::value;
use nom::branch::alt;

fn parse_bool(input: &str) -> IResult<&str, bool> {
    // either, parse `"true"` -> `true`; `"false"` -> `false`, or error.
    alt((
      value(true, tag("true")),
      value(false, tag("false")),
    ))(input)
}

fn main() -> Result<(), Box<dyn Error>> {
    // Parses the `"true"` out.
    let (remaining, parsed) = parse_bool("true|false")?;
    assert_eq!(parsed, true);
    assert_eq!(remaining, "|false");
   
    // If we forget about the "|", we get an error.
    let parsing_error = parse_bool(remaining);
    assert!(parsing_error.is_err());
    
    // Skipping the first byte gives us `false`!
    let (remaining, parsed) = parse_bool(&remaining[1..])?;
    assert_eq!(parsed, false);
    assert_eq!(remaining, "");
    
    

#   Ok(())
}
```

## Nom's in-built parser functions

Nom has a wide array of parsers built in. Here is a list of
[parsers which recognize specific characters](https://docs.rs/nom/latest/nom/character/complete/index.html).

Some of them we have seen before in Chapter 2, but now we also can try out the parsers that return different
types, like `i32`. An example of this parser is shown in the next section.

## Building a More Complex Example

A more complex example of parsing custom types might be parsing a 2D coordinate.

Let us try to figure out how to design this.

 - We know that we want to take a string, like `"(3, -2)"`, and convert into
   a `Coordinate` struct.
 - We can split this into three parts:
 
```ignore
(vvvvvvvvvvvvv) # The outer brackets.
  vvvv , vvvv   # The comma, separating values.
    3     -2    # The actual integers.
```

 - So, we will need three parsers, to deal with this:
   1. A parser for integers, which  will deal with the raw numbers.
   2. A parser for comma seperated pair, which will split it up into integers.
   3. A parser for the outer brackets.
   
 - We can see below how we achieve this:

```rust
# extern crate nom;
# use std::error::Error;
use nom::IResult;
use nom::bytes::complete::tag;
use nom::sequence::{separated_pair, delimited};

// This is the type we will parse into.
#[derive(Debug,PartialEq)]
pub struct Coordinate {
  pub x:   i32,
  pub y:   i32,
}

// 1. Nom has an in-built i32 parser.
use nom::character::complete::i32;

// 2. Use the `separated_pair` parser to combine two parsers (in this case,
//    both `i32`), ignoring something in-between.
fn parse_integer_pair(input: &str) -> IResult<&str, (i32, i32)> {
    separated_pair(
        i32,
        tag(", "),
        i32
    )(input)
}

// 3. Use the `delimited` parser to apply a parser, ignoring the results
//    of two surrounding parsers.
fn parse_coordinate(input: &str) -> IResult<&str, Coordinate> {
    let (remaining, (x, y)) = delimited(
        tag("("),
        parse_integer_pair,
        tag(")")
    )(input)?;
    
    // Note: we could construct this by implementing `From` on `Coordinate`,
    // We don't, just so it's obvious what's happening.
    Ok((remaining, Coordinate {x, y}))
    
}

fn main() -> Result<(), Box<dyn Error>> {
    let (_, parsed) = parse_coordinate("(3, 5)")?;
    assert_eq!(parsed, Coordinate {x: 3, y: 5});
   
    let (_, parsed) = parse_coordinate("(2, -4)")?;
    assert_eq!(parsed, Coordinate {x: 2, y: -4});
    
    let parsing_error = parse_coordinate("(3,)");
    assert!(parsing_error.is_err());
    
    let parsing_error = parse_coordinate("(,3)");
    assert!(parsing_error.is_err());
    
    let parsing_error = parse_coordinate("Ferris");
    assert!(parsing_error.is_err());
    

#   Ok(())
}
```

As an exercise, you might want to explore how to make this parser deal gracefully with 
whitespace in the input. 
