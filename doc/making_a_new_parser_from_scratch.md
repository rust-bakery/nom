# Making a new parser from scratch

Writing a parser is a very fun, interactive process, but sometimes a daunting
task. How do you test it? How to see ambiguities in specifications?

nom is designed to abstract data manipulation (counting array offsets,
converting to structures, etc) while providing a safe, composable API. It also
takes care of making the code easy to test and read, but it can be confusing at
first, if you are not familiar with parser combinators, or if you are not used
to Rust generic functions.

This document is here to help you in getting started with nom. You can also find
[nom recipes for common short parsing tasks here](nom_recipes.md). If you need
more specific help, please ping `geal` on IRC (libera, geeknode,
oftc), go to `#nom-parsers` on Libera IRC, or on the
[Gitter chat room](https://gitter.im/Geal/nom).

# First step: the initial research

A big part of the initial work lies in accumulating enough documentation and
samples to understand the format. The specification is useful, but specifications
represent an "official" point of view, that may not be the real world usage. Any
blog post or open source code is useful, because it shows how people understand
the format, and how they work around each other's bugs (if you think a
specification ensures every implementation is consistent with the others, think again).

You should get a lot of samples (file or network traces) to test your code. The
easy way is to use a small number of samples coming from the same source and
develop everything around them, to realize later that they share a very specific
bug.

# Code organization

While it is tempting to insert the parsing code right inside the rest of the
logic, it usually results in  unmaintainable code, and makes testing challenging.
Parser combinators, the parsing technique used in nom, assemble a lot of small
functions to make powerful parsers. This means that those functions only depend
on their input, not on an external state. This makes it easy to parse the input
partially, and to test those functions independently.

Usually, you can separate the parsing functions in their own module, so you
could have a `src/lib.rs` file containing this:

```rust
pub mod parser;
```

And the `src/parser.rs` file:

```rust
use nom::IResult;
use nom::number::complete::be_u16;
use nom::bytes::complete::take;

pub fn length_value(input: &[u8]) -> IResult<&[u8],&[u8]> {
    let (input, length) = be_u16(input)?;
    take(length)(input)
}
```

# Writing a first parser

Let's parse a simple expression like `(12345)`. nom parsers are functions that
use the `nom::IResult` type everywhere. As an example, a parser taking a byte
slice `&[u8]` and returning a 32 bits unsigned integer `u32` would have this
signature: `fn parse_u32(input: &[u8]) -> IResult<&[u8], u32>`.

The `IResult` type depends on the input and output types, and an optional custom
error type. This enum can either be `Ok((i,o))` containing the remaining input
and the output value, or, on the `Err` side, an error or an indication that more
data is needed.

```rust
pub type IResult<I, O, E=(I,ErrorKind)> = Result<(I, O), Err<E>>;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Needed {
  Unknown,
  Size(u32)
}

#[derive(Debug, Clone, PartialEq)]
pub enum Err<E> {
  Incomplete(Needed),
  Error(E),
  Failure(E),
}
```

nom uses this type everywhere. Every combination of parsers will pattern match
on this to know if it must return a value, an error, consume more data, etc.
But this is done behind the scenes most of the time.

Parsers are usually built from the bottom up, by first writing parsers for the
smallest elements, then assembling them in more complex parsers by using
combinators.

As an example, here is how we could build a (non spec compliant) HTTP request
line parser:

```rust
// first implement the basic parsers
let method = take_while1(is_alpha);
let space = take_while1(|c| c == ' ');
let url = take_while1(|c| c!= ' ');
let is_version = |c| c >= b'0' && c <= b'9' || c == b'.';
let http = tag("HTTP/");
let version = take_while1(is_version);
let line_ending = tag("\r\n");

// combine http and version to extract the version string
// preceded will return the result of the second parser
// if both succeed
let http_version = preceded(http, version);

// combine all previous parsers in one function
fn request_line(i: &[u8]) -> IResult<&[u8], Request> {

  // tuple takes as argument a tuple of parsers and will return
  // a tuple of their results
  let (input, (method, _, url, _, version, _)) =
    tuple((method, space, url, space, http_version, line_ending))(i)?;

  Ok((input, Request { method, url, version }))
}
```

Since it is easy to combine small parsers, I encourage you to write small
functions corresponding to specific parts of the format, test them
independently, then combine them in more general parsers.

# Finding the right combinator

nom has a lot of different combinators, depending on the use case. They are all
described in the [reference](https://docs.rs/nom).

[Basic functions](https://docs.rs/nom/#functions) are available. They deal mostly
in recognizing character types, like `alphanumeric` or `digit`. They also parse
big endian and little endian integers and floats of multiple sizes.

Most of the functions are there to combine parsers, and they are generic over
the input type.

# Testing the parsers

Once you have a parser function, a good trick is to test it on a lot of the
samples you gathered, and integrate this to your unit tests. To that end, put
all of the test files in a folder like `assets` and refer to test files like
this:

```rust
#[test]
fn header_test() {
  let data = include_bytes!("../assets/axolotl-piano.gif");
  println!("bytes:\n{}", &data[0..100].to_hex(8));
  let res = header(data);
  // ...
```

The `include_bytes!` macro (provided by Rust's standard library) will integrate
the file as a byte slice in your code. You can then just refer to the part of
the input the parser has to handle via its offset. Here, we take the first 100
bytes of a GIF file to parse its header
(complete code [here](https://github.com/Geal/gif.rs/blob/master/src/parser.rs#L305-L309)).

If your parser handles textual data, you can just use a lot of strings directly
in the test, like this:

```rust
#[test]
fn factor_test() {
  assert_eq!(factor("3"),       Ok(("", 3)));
  assert_eq!(factor(" 12"),     Ok(("", 12)));
  assert_eq!(factor("537  "),   Ok(("", 537)));
  assert_eq!(factor("  24   "), Ok(("", 24)));
}
```

The more samples and test cases you get, the more you can experiment with your
parser design.

# Debugging the parsers

There are a few tools you can use to debug how code is generated.

## dbg_dmp

This function wraps a parser that accepts a `&[u8]` as input and
prints its hexdump if the child parser encountered an error:

```rust
use nom::{IResult, error::dbg_dmp, bytes::complete::tag};

fn f(i: &[u8]) -> IResult<&[u8], &[u8]> {
  dbg_dmp(tag("abcd"), "tag")(i)
}

  let a = &b"efghijkl"[..];

// Will print the following message:
// Error(Position(0, [101, 102, 103, 104, 105, 106, 107, 108])) at l.5 by ' tag ! ( "abcd" ) '
// 00000000        65 66 67 68 69 6a 6b 6c         efghijkl
f(a);
```

