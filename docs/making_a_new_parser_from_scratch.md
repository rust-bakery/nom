Writing a parser is a very fun, interactive process, but sometimes a daunting task. How do you test it? How to  see ambiguities in specifications?

nom is designed to abstract data manipulation (counting array offsets, converting to structures, etc) while providing a safe, composable API. It also takes care of making the code easy to test and read, but it can be confusing at first, if you are not familiar with parser combinators, or if you are not used to Rust macros.

This document is here to help you in getting started with nom. If you need more specific help, please ping `geal` on IRC (mozilla, freenode, geeknode, oftc), go to `#nom` on Mozilla IRC, or on the [Gitter chat room](https://gitter.im/Geal/nom).

# First step: the initial research

A big part of the initial work lies in accumulating enough documentation and samples to understand the format. The specification is useful, but specifications represent an "official" point of view, that may not be the real world usage. Any blog post or open source code is useful, because it shows how people understand the format, and how they work around each other's bugs (if you think a specification ensures every implementation is consistent with the others, think again).

You should get a lot of samples (file or network traces) to test your code. The easy way is to use a small number of samples coming from the same source and develop everything around them, to realize later that they share a very specific bug.

# Code organization

While it is tempting to insert the parsing code right inside the rest of the logic, it usually results in  unmaintainable code, and makes testing challenging. Parser combinators, the parsing technique used in nom, assemble a lot of small functions to make powerful parsers. This means that those functions only depend on their input, not on an external state. This makes it easy to parse the input partially, and to test those functions independently.

Usually, you can separate the parsing functions in their own module, so you could have a `src/lib.rs`file containing this:

```rust
#[macro_use]
extern crate nom;

pub mode parser;
```

And use the methods and structure from `parser` there. The `src/parser.rs` would then import nom functions and structures if needed:

```rust
use nom::{be_u16, be_u32};
```

# Writing a first parser

Let's parse a simple expression like `(12345)`. nom parsers are functions that use the `nom::IResult` type everywhere. As an example, a parser taking a byte slice `&[u8]` and returning a 32 bits unsigned integer `u32` would have this signature: `fn parse_u32(input: &[u8]) -> IResult<&[u8], u32>`.

The `IResult` type depends on the input and output types, and an optional custom error type. This enum can either contain `Done(i,o)` containing the remaining input and the output value, an error, or an indication that more data is needed.

```rust
#[derive(Debug,PartialEq,Eq,Clone)]
pub enum IResult<I,O,E=u32> {
  Done(I,O),
  Error(Err<I,E>),
  Incomplete(Needed)
}
```

nom uses this type everywhere. Every combination of parsers will pattern match on this to know if it must return a value, an error, consume more data, etc. But this is done behind the scenes most of the time.

nom provides a macro for function definition, called `named!`:

```rust
named!(my_function( &[u8] ) -> &[u8], tag!("abcd"));

named!(my_function<&[u8], &[u8]>, tag!("abcd"));

named!(my_function, tag!("abcd"));
```

But you could as easily define the function yourself like this:

```rust
fn my_function(input: &[u8]) -> IResult<&[u8], &[u8]> {
  tag!(input, "abcd")
}
```

Note that we pass the input to the first parser in the manual definition, while we do not when we use `named!`. This is a macro trick specific to nom: every parser takes the input as first parameter, and the macros take care of giving the remaining input to the next parser. As an example, take a simple parser like the following one, which recognizes the word "hello" then takes the next 5 bytes:

```rust
named!(prefixed, preceded!(tag!("hello"), take!(5)));
```

Once the macros have expanded, this would correspond to:

```rust
fn prefixed(i: &[u8]) -> ::nom::IResult<&[u8], &[u8]> {
    {
        match {
                  #[inline(always)]
                  fn as_bytes<T: ::nom::AsBytes>(b: &T) -> &[u8] {
                      b.as_bytes()
                  }
                  let expected = "hello";
                  let bytes = as_bytes(&expected);
                  {
                      let res: ::nom::IResult<&[u8], &[u8]> =
                          if bytes.len() > i.len() {
                              ::nom::IResult::Incomplete(::nom::Needed::Size(bytes.len()))
                          } else if &i[0..bytes.len()] == bytes {
                              ::nom::IResult::Done(&i[bytes.len()..],
                                                   &i[0..bytes.len()])
                          } else {
                              ::nom::IResult::Error(::nom::Err::Position(::nom::ErrorKind::Tag,
                                                                         i))
                          };
                      res
                  }
              } {
            ::nom::IResult::Error(a) => ::nom::IResult::Error(a),
            ::nom::IResult::Incomplete(i) => ::nom::IResult::Incomplete(i),
            ::nom::IResult::Done(i1, _) => {
                match {
                          let cnt = 5 as usize;
                          let res: ::nom::IResult<&[u8], &[u8]> =
                              if i1.len() < cnt {
                                  ::nom::IResult::Incomplete(::nom::Needed::Size(cnt))
                              } else {
                                  ::nom::IResult::Done(&i1[cnt..],
                                                       &i1[0..cnt])
                              };
                          res
                      } {
                    ::nom::IResult::Error(a) => ::nom::IResult::Error(a),
                    ::nom::IResult::Incomplete(i) =>
                    ::nom::IResult::Incomplete(i),
                    ::nom::IResult::Done(i2, o2) => {
                        ::nom::IResult::Done(i2, o2)
                    }
                }
            }
        }
    }
}
```

While this may look like a lot of code, the compiler and the CPU will happily optimize everything, do not worry. You can see that the function matches on the result of the first parser, stops there if it returned an error or incomplete, and if it returned a value, takes the remaining input `i1`, applies the second parser on it, then matches on the result (and returns the value `o2` and the remaining input `i2`).

A lot of complex patterns are implemented that way: generic macros combining other macros or functions. This will handle partial consumption and passing data slices for you.

Since it is easy to combine small parsers, I encourage you to write small functions corresponding to specific parts of the format, test them independently, then combine them in more general parsers.

# Finding the right combinator

nom has a lot of different combinators, depending on the use case. They are all described in the [reference](http://rust.unhandledexpression.com/nom/).

[Basic functions](http://rust.unhandledexpression.com/nom/#functions) are available. They deal mostly in recognizing character types, like `alphanumeric` or `digit`. They also parse big endian and little endian integers and floats of multiple sizes.

Most of the macros are there to combine parsers, and they do not depend on the input type. this is the case for all of those defined in [src/macros.rs](https://github.com/Geal/nom/blob/master/src/macros.rs). The reference indicates a [possible type signature](http://rust.unhandledexpression.com/nom/#macros) for what the macros expect and return. In case of doubt, the documentation often indicates a [code example](http://rust.unhandledexpression.com/nom/macro.many0!.html) after the macro definition.

## Type specific combinators

Byte slice related macros can be found in [src/bytes.rs](https://github.com/Geal/nom/blob/master/src/bytes.rs). This file contains the following combinators: `tag!`, `is_not!`, `is_a!`, `escaped!`, `escaped_transform!`, `take_while!`, `take_while1!`, `take_till!`, `take!`, `take_str!`, `take_until_and_consume!`, `take_until_either!`, `take_until_either_and_consume`.

Bit stream related macros are in [src/bits.rs](https://github.com/Geal/nom/blob/master/src/bits.rs).

Character related macros are in [src/character.rs](https://github.com/Geal/nom/blob/master/src/character.rs).

Regular expression related macros are in [src/regexp.rs](https://github.com/Geal/nom/blob/master/src/regexp.rs).

# Testing the parsers

Once you have a parser function, a good trick is to test it on a lot of the samples you gathered, and integrate this to your unit tests. To that end, put all of the test files in a folder like `assets` and refer to test files like this:

```rust
  #[test]
  fn header_test() {
    let data = include_bytes!("../assets/axolotl-piano.gif");
    println!("bytes:\n{}", &data[0..100].to_hex(8));
    let res = header(data);
```

The `include_bytes!` macro (provided by Rust's standard library) will integrate the file as a byte slice in your code. You can then just refer to the part of the input the parser has to handle via its offset. Here, we take the first 100 bytes of a GIF file to parse its header (complete code [here](https://github.com/Geal/gif.rs/blob/master/src/parser.rs#L305-L309)).

If your parser handles textual data, you can just use a lot of strings directly in the test, like this:

```rust
#[test]
fn factor_test() {
  assert_eq!(factor(&b"3"[..]),       IResult::Done(&b""[..], 3));
  assert_eq!(factor(&b" 12"[..]),     IResult::Done(&b""[..], 12));
  assert_eq!(factor(&b"537  "[..]),   IResult::Done(&b""[..], 537));
  assert_eq!(factor(&b"  24   "[..]), IResult::Done(&b""[..], 24));
}
```

The more samples and test cases you get, the more you can experiment with your parser design.

# Debugging the parsers

While Rust macros are really useful to get a simpler syntax, they can sometimes give cryptic errors. As an example, `named!(manytag, many0!(take!(5)));` would result in the following error:

```
<nom macros>:6:38: 6:41 error: mismatched types:
 expected `&[u8]`,
    found `collections::vec::Vec<&[u8]>`
(expected &-ptr,
    found struct `collections::vec::Vec`) [E0308]
<nom macros>:6 } $ crate:: IResult:: Done ( input , res ) } ) ; ( $ i : expr , $ f : expr )
                                                    ^~~
<nom macros>:20:1: 20:34 note: in this expansion of many0! (defined in <nom macros>)
tests/arithmetic.rs:13:1: 13:35 note: in this expansion of named! (defined in <nom macros>)
<nom macros>:6:38: 6:41 help: run `rustc --explain E0308` to see a detailed explanation
error: aborting due to previous error
```

This particular one is caused by `named!` generating a function returning a `IResult< &[u8], &[u8] >`, while `many0!(take!(5))` returns a `IResult< &[u8], Vec<&[u8]> >`.

There are a few tools you can use to debug how code is generated.

## trace_macros

The `trace_macros` feature show how macros are applied. To use it, add `#![feature(trace_macros)]` at the top of your file (you need Rust nightly for this), then apply it like this:

```rust
trace_macros!(true);
named!(manytag, many0!(take!(5)));
trace_macros!(false);
```

It will result in the following output during compilation:

```
named! { manytag , many0 ! ( take ! ( 5 ) ) }
many0! { i , take ! ( 5 ) }
take! { input , 5 }
```

## Pretty printing

rustc can show how code is expanded with the option `--pretty=expanded`. If you want to use it with cargo, use the following command line: `cargo rustc <cargo options> -- -Z unstable-options --pretty=expanded`

It will print the `manytag` function like this:

```rust
fn manytag(i: &[u8]) -> ::nom::IResult<&[u8], &[u8]> {
    {
        let mut res = Vec::new();
        let mut input = i;
        while let ::nom::IResult::Done(i, o) =
                  {
                      let cnt = 5 as usize;
                      let res: ::nom::IResult<&[u8], &[u8]> =
                          if input.len() < cnt {
                              ::nom::IResult::Incomplete(::nom::Needed::Size(cnt))
                          } else {
                              ::nom::IResult::Done(&input[cnt..],
                                                   &input[0..cnt])
                          };
                      res
                  } {
            if i.len() == input.len() { break ; }
            res.push(o);
            input = i;
        }
        ::nom::IResult::Done(input, res)
    }
}
```
