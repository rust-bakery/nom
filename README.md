# nom, eating data byte by byte

[![Join the chat at https://gitter.im/Geal/nom](https://badges.gitter.im/Join%20Chat.svg)](https://gitter.im/Geal/nom?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge&utm_content=badge)
[![Build Status](https://travis-ci.org/Geal/nom.svg?branch=master)](https://travis-ci.org/Geal/nom)
[![Coverage Status](https://coveralls.io/repos/Geal/nom/badge.svg?branch=master)](https://coveralls.io/r/Geal/nom?branch=master)

nom is a parser combinators library written in Rust. Its goal is to provide tools to build safe parsers without compromising the speed or memory consumption. To that end, it uses extensively Rust's *strong typing*, *zero copy* parsing, *push streaming*, *pull streaming*, and provides macros and traits to abstract most of the error prone plumbing.

This work is currently experimental, the API and syntax may still change a lot, but it can already be used to parse relatively complex formats like [MP4](tests/mp4.rs).


## Features

Here are the current and planned features, with their status:
- [x] **byte-oriented**: the basic type is `&[u8]` and parsers will work as much as possible on byte array slices (but are not limited to them)
- [x] **bit-oriented**: nom can address a byte slice as a bit stream
- [x] **zero-copy**:
  - [x] **in the parsers**: a parsing chain will almost always return a slice of its input data
  - [x] **in the producers and consumers**: some copying still happens
- [x] **streaming**:
  - [x] **push**: a data producer can continuously feed consumers and parsers, as long as there is data available
  - [x] **pull**: a consumer will handle the produced data and drive seeking in the producer
- [x] **macro based syntax**: easier parser building through macro usage
- [x] **state machine handling**: consumers provide a basic way of managing state machines
- [x] **descriptive errors**: the parsers can aggregate a list of error codes with pointers to the incriminated input slice. Those error lists can be pattern matched to provide useful messages.
- [x] **custom error types**: you can provide a specific type to improve errors returned by parsers
- [x] **safe parsing**: nom leverages Rust's safe memory handling and powerful types, and parsers are routinely fuzzed and tested with real wolrd data. So far, the only flaws found by fuzzing were in code written outside of nom
- [x] **speed**: benchmarks have shown that nom parsers often outperform many parser combinators library like Parsec and attoparsec, some regular expression engines and even handwritten C parsers

Reference documentation is available [here](http://rust.unhandledexpression.com/nom/).

Some benchmarks are available on [Github](https://github.com/Geal/nom_benchmarks).

## Installation

nom is available on [crates.io](https://crates.io/crates/nom) and can be included in your Cargo enabled project like this:

```toml
[dependencies]
nom = "~0.5.0"
```

Then include it in your code like this:

```rust
#[macro_use]
extern crate nom;
```

There are a few compilation features:

* `core`: enables `no_std` builds
* `regexp`: enables regular expression parsers with the `regex` crate
* `regexp_macros`: enables regular expression parsers with the `regex` and `regex_macros` crates. Regular expressions can be defined at compile time, but it requires a nightly version of rustc

You can activate those features like this:

```toml
[dependencies.nom]
version = "~0.5.0"
features = [regexp]
```

## Usage

### Parser combinators

Parser combinators are an approach to parsers that is very different from software like lex and yacc. Instead of writing the grammar in a separate file and generating the corresponding code, you use very small functions with very specific purpose, like "take 5 bytes", or "recognize the word 'HTTP'", and assemble then in meaningful patterns like "recognize 'HTTP', then a space, then a version".
The resulting code is small, and looks like the grammar you would have written with other parser approaches.

This has a few advantages:

- the parsers are small and easy to write
- the parsers components are easy to reuse (if they're general enough, please add them to nom!)
- the parsers components are easy to test separately (unit tests and property-based tests)
- the parser combination code looks close to the grammar you would have written
- you can build partial parsers, specific to the data you need at the moment, and ignore the rest

Here is an example of one such parser, to recognize text between parenthesis:

```rust
named!(parens, delimited!(char!('('), none_of!(")"), char!(')'));
```

It defines a function named `parens`, which will recognize a sequence of the caracter '(', the longest byte array not containing ')', then the character ')', and will return the byte array in the middle.

Here is another parser, written without using nom's macros this time:

```rust
fn take4(i:&[u8]) -> IResult<&[u8], &[u8]>{
  if i.len() < 4 {
    IResult::Incomplete(Needed::Size(4))
  } else {
    IResult::Done(&i[4..],&i[0..4])
  }
}
```

This function takes a byte array as input, and tries to consume 4 bytes. With macros, you would write it like this:

```rust
named!(take4, take!(4));
```


A parser in nom is a function which, for an input type I, an output type O, and an optional error type E, will have the following signature:

```rust
fn parser(input: I) -> IResult<I, O, E>;
```

Or like this, if you don't want to specify a custom error type (it will be u32 by default):
```rust
fn parser(input: I) -> IResult<I, O>;
```

`IResult` is an enumeration that can represent:

- a correct result `Done(I,O)` with the first element being the rest of the input (not parsed yet), and the second being the output value
- an error `Error(Err)` with `Err` an enum that can represent an error with, optionally, position information and a chain of accumulated errors
- an `Incomplete(Needed)` indicating that more input is necessary. `Needed` can indicate how much data is needed

````rust
pub enum IResult<I,O,E=u32> {
  Done(I,O),
  Error(Err<I,E>),
  Incomplete(Needed)
}

pub enum Err<P,E=u32>{
  /// an error code
  Code(ErrorKind<E>),
  /// an error code, and the next error in the parsing chain
  Node(ErrorKind<E>, Box<Err<P,E>>),
  /// an error code and the related input position
  Position(ErrorKind<E>, P),
  /// an error code, the related input position, and the next error in the parsing chain
  NodePosition(ErrorKind<E>, P, Box<Err<P,E>>)
}

pub enum Needed {
  /// needs more data, but we do not know how much
  Unknown,
  /// contains the required data size
  Size(usize)
}
```

There is already a large list of basic parsers available, like:

- **length_value**: a byte indicating the size of the following buffer
- **not_line_ending**: returning as much data as possible until a line ending (\r or \n) is found
- **line_ending**: matches a line ending
- **alpha**: will return the longest alphabetical array from the beginning of the input
- **digit**: will return the longest numerical array from the beginning of the input
- **alphanumeric**: will return the longest alphanumeric array from the beginning of the input
- **space**: will return the longest array containing only spaces
- **multispace**: will return the longest array containing space, \r or \n
- **be_u8**, **be_u16**, **be_u32**, **be_u64** to parse big endian unsigned integers of multiple sizes
- **be_i8**, **be_i16**, **be_i32**, **be_i64** to parse big endian signed integers of multiple sizes
- **be_f32**, **be_f64** to parse big endian floating point numbers
- **eof**: a parser that is successful only if the input is over. In any other case, it returns an error.

Please refer to the documentation for an exhaustive list of parsers.

#### Making new parsers with macros

Macros are the main way to make new parsers by combining other ones. Those macros accept other macros or function names as arguments. You then need to make a function out of that combinator with **named!**, or a closure with **closure!**. Here is how you would do, with the **tag!** and **take!** combinators:

```rust
named!(abcd_parser, tag!("abcd")); // will consume bytes if the input begins with "abcd"


named!(take_10, take!(10));                // will consume 10 bytes of input
```

The **named!** macro can take three different syntaxes:

```rust
named!(my_function( &[u8] ) -> &[u8], tag!("abcd"));

named!(my_function<&[u8], &[u8]>, tag!("abcd"));

named!(my_function, tag!("abcd")); // when you know the parser takes &[u8] as input, and returns &[u8] as output
```

**IMPORTANT NOTE**: Rust's macros can be very sensitive to the syntax, so you may encounter an error compiling parsers like this one:

```rust
named!(my_function<&[u8], Vec<&[u8]>>, many0!(tag!("abcd")));
```

You will get the following error: "error: expected an item keyword". This happens because `>>` is seen as an operator, so the macro parser does not recognize what we want. There is a way to avoid it, by inserting a space:

```rust
named!(my_function<&[u8], Vec<&[u8]> >, many0!(tag!("abcd")));
```

This will compile correctly. I am very sorry for this inconvenience.

#### Common combinators

Here are the basic macros available:

- **tag!**: will match the byte array provided as argument
- **is_not!**: will match the longest array not containing any of the bytes of the array provided to the macro
- **is_a!**: will match the longest array containing only bytes of the array provided to the macro
- **take_while!**: will walk the whole array and apply the closure to each suffix until the function fails
- **take!**: will take as many bytes as the number provided
- **take_until!**: will take as many bytes as possible until it encounters the provided byte array, and will leave it in the remaining input
- **take_until_and_consume!**: will take as many bytes as possible until it encounters the provided byte array, and will skip it
- **take_until_either_and_consume!**: will take as many bytes as possible until it encounters one of the bytes of the provided array, and will skip it
- **take_until_either!**: will take as many bytes as possible until it encounters one of the bytes of the provided array, and will leave it in the remaining input
- **map!**: applies a function to the output of a `IResult` and puts the result in the output of a `IResult` with the same remaining input
- **flat_map!**: applies a parser to the ouput of a `IResult` and returns a new `IResult` with the same remaining input.
- **map_opt!**: applies a function returning an Option to the output of `IResult`, returns `Done(input, o)` if the result is `Some(o)`, or `Error(0)`
- **map_res!**: applies a function returning a Result to the output of `IResult`, returns `Done(input, o)` if the result is `Ok(o)`, or `Error(0)`

Please refer to the documentation for an exhaustive list of combinators.

#### Combining parsers

There are more high level patterns, like the **alt!** combinator, which provides a choice between multiple parsers. If one branch fails, it tries the next, and returns the result of the first parser that succeeds:

```rust
named!(alt_tags, alt!(tag!("abcd") | tag!("efgh")));

assert_eq!(alt_tags(b"abcdxxx"), Done(b"xxx", b"abcd"));
assert_eq!(alt_tags(b"efghxxx"), Done(b"xxx", b"efgh"));
assert_eq!(alt_tags(b"ijklxxx"), Error(1));
```

The pipe `|` character is used as separator.

The **opt!** combinator makes a parser optional. If the child parser returns an error, **opt!** will succeed and return None:

```rust
named!( abcd_opt, opt!( tag!("abcd") ) );

assert_eq!(abcd_opt(b"abcdxxx"), Done(b"xxx", Some(b"abcd")));
assert_eq!(abcd_opt(b"efghxxx"), Done(b"efghxxx", None));
```

**many0!** applies a parser 0 or more times, and returns a vector of the aggregated results:

```rust
named!(multi, many0!( tag!( "abcd" ) ) );
let a = b"abcdef";
let b = b"abcdabcdef";
let c = b"azerty";
assert_eq!(multi(a), Done(b"ef", vec![b"abcd"]));
assert_eq!(multi(b), Done(b"ef", vec![b"abcd", b"abcd"]));
assert_eq!(multi(c), Done(b"azerty", Vec::new()));
```

Here are some basic combining macros available:

- **opt!**: will make the parser optional (if it returns the O type, the new parser returns Option<O>)
- **many0!**: will apply the parser 0 or more times (if it returns the O type, the new parser returns Vec<O>)
- **many1!**: will appy the parser 1 or more times

Please refer to the documentation for an exhaustive list of combinators.

There are more complex (and more useful) parsers like the chain, which is used to parse a whole buffer, gather data along the way, then assemble everything in a final closure, if none of the subparsers failed or returned an `Incomplete`:

````rust
struct A {
  a: u8,
  b: u8
}

fn ret_int1(i:&[u8]) -> IResult<&[u8], u8> { Done(i,1) }
fn ret_int2(i:&[u8]) -> IResult<&[u8], u8> { Done(i,2) }

named!(f<&[u8],A>,
  chain!(    // the parser takes a byte array as input, and returns an A struct
    tag!("abcd")  ~      // begins with "abcd"
    tag!("abcd")? ~      // the question mark indicates an optional parser
    aa: ret_int1  ~      // the return value of ret_int1, if it does not fail, will be stored in aa
    tag!("efgh")  ~
    bb: ret_int2  ~
    tag!("efgh")  ,      // end the chain with a comma

    ||{A{a: aa, b: bb}} // the final closure will be able to use the variable defined previously
  )
);

let r = f(b"abcdabcdefghefghX");
assert_eq!(r, Done(b"X", A{a: 1, b: 2}));

let r2 = f(b"abcdefghefghX");
assert_eq!(r2, Done(b"X", A{a: 1, b: 2}));
```

The tilde `~` is used as separator between every parser in the sequence, the comma `,` indicates the parser chain ended, and the last closure can see the variables storing the result of parsers.

More examples of chain usage can be found in the [INI file parser example](tests/ini.rs).

### TODO: example for new producers and consumers
