# nom, eating data byte by byte

nom is a parser combinators library written in Rust. Its goal is to provide tools to build safe parsers without compromising the speed or memory consumption. To that end, it uses extensively Rust's *strong typing*, *zero copy* parsing, *push streaming*, *pull streaming*, and provides macros and traits to abstract most of the error prone plumbing.

This work is currently experimental, the API and syntax may still change a lot, but it can already be used to parse relatively complex formats like [MP4](tests/mp4.rs).

[![Build Status](https://travis-ci.org/Geal/nom.svg?branch=master)](https://travis-ci.org/Geal/nom)

## Features

Here are the current and planned features, with their actual status:
- [x] **zero copy**:
  - [x] **in the parsers**: a parsing chain will always return a reference to its input data
  - [x] **in the producers and consumers**: some copying still happens
- [x] **streaming**:
  - [x] **push**: a parser can be directly fed a producer's output and called every time there is data available
  - [x] **pull**: a consumer will take a parser and a producer, and handle all the data gathering and, if available, seeking the streaming
- [x] **macro based syntax**: easier parser building through macro usage
- [ ] **safe parsing**: while I have some confidence in Rust's abilities, this will be put to the test via extensive fuzzing and disassembling
- [ ] **descriptive errors**: currently, errors are just integers, but they should express what went wrong

Reference documentation is available [here](http://rust.unhandledexpression.com/nom/).

## Installation

nom is available on [crates.io](https://crates.io/crates/nom) and can be included in your Cargo enabled project like this:

```toml
[dependencies]
nom = "~0.1.0"
```

Then include it in your code like this:

```rust
#[macro_use]
extern crate nom;
```

While it is not mandatory to use the macros, they make it a lot easier to build parsers with nom.

## Usage

### Parser combinators

nom uses parser combinators to build and reuse parsers. To work with parser combinators, instead of writing the whole grammar from scratch and generating a parser, or writing the complete state machine by hand, you write small, reusable functions, that you will combine to make more interesting parsers.

Here is an example of one such parser:

```rust
fn take4(i:&[u8]) -> IResult<&[u8], &[u8]>{
  if i.len() < 4 {
    IResult::Incomplete(4)
  } else {
    IResult::Done(&i[4..],&i[0..4])
  }
}
```

This function takes a byte array as input, and tries to consume 4 bytes.

A parser combinator in Rust is basically a function which, for an input type I and an output type O, will have the following signature:

```rust
fn parser(input: I) -> IResult<I, O>;
```

IResult is an enumeration that can represent:

- a correct result `Done(I,O)` with the first element being the rest of the input (not parsed yet), and the second being the output value
- an error `Error(Err)` with Err being an integer
- an `Incomplete(u32)` indicating that more input is necessary (for now the value is ignored, but it should indicate how much is needed)

````rust
pub enum IResult<I,O> {
  Done(I,O),
  Error(Err),
  Incomplete(u32)
}
```

There is already a large list of parsers available, like:

- **be_u8**, **be_u16**, **be_u32**, **be_u64** to parse big endian unsigned integers of multiple sizes
- **length_value**: a byte indicating the size of the following buffer
- **alphanumeric**: will return the longest alphanumeric array possible from the beginning of the input

#### Making new parsers with macros

Some macros make it easier to create new parsers. Here are a few of them:

```rust
tag!(abcd_parser  "abcd".as_bytes()); // will consume bytes if the input begins with "abcd"

take!(take_10     10);                // will consume 10 bytes of input
```

#### Combining parsers

Here again, we use macros to combine parsers easily in useful patterns:

```rust
tag!(abcd_p "abcd".as_bytes());
tag!(efgh_p "efgh".as_bytes());

alt!(alt_tags<&[u8],&[u8]>, abcd_p, efgh_p); // the types indicates the input and output types, that must match for all alternatives

assert_eq!(alt_tags("abcdxxx".as_bytes()), Done("xxx".as_bytes(), "abcd".as_bytes()));
assert_eq!(alt_tags("efghxxx".as_bytes()), Done("xxx".as_bytes(), "efgh".as_bytes()));
assert_eq!(alt_tags("ijklxxx".as_bytes()), Error(1));

opt!(abcd_opt<&[u8], &[u8]>  abcd_p);       // make the abcd_p parser optional
assert_eq!(alt_tags("abcdxxx".as_bytes()), Done("xxx".as_bytes(), Some("abcd".as_bytes())));
assert_eq!(alt_tags("efghxxx".as_bytes()), Done("efghxxx".as_bytes(), None));

many0(multi<&[u8], &[u8]> abcd_p);         // the abcd_p parser can happen 0 or more times
let a = "abcdef".as_bytes();
let b = "abcdabcdef".as_bytes();
let c = "azerty".as_bytes();
assert_eq!(multi(a), Done("ef".as_bytes(), vec!["abcd".as_bytes()]));
assert_eq!(multi(b), Done("ef".as_bytes(), vec!["abcd".as_bytes(), "abcd".as_bytes()]));
assert_eq!(multi(c), Done("azerty".as_bytes(), Vec::new()));
```

There are more complex (and more useful) parsers like the chain, which is used to parse a whole buffer, gather data along the way, then assemble everything in a final closure:

````rust
struct A {
  a: u8,
  b: u8
}

tag!(abcd_p "abcd".as_bytes());
tag!(efgh_p "efgh".as_bytes());

fn ret_int1(i:&[u8]) -> IResult<&[u8], u8> { Done(i,1) };
fn ret_int2(i:&[u8]) -> IResult<&[u8], u8> { Done(i,2) };

chain!(f<&[u8],A>,          // the parser takes a byte array as input, and returns an A struct
  abcd_p       ~            // begins with "abcd"
  abcd_p?      ~            // the question mark indicates an optional parser
  aa: ret_int1 ~            // the return value of ret_int1, if it does not fail, will be stored in aa
  efgh_p       ~
  bb: ret_int2 ~
  efgh_p       ,            // end the chain with a comma

  ||{A{a: aa, b: bb}}       // the final closure will be able to use the variable defined previously
);

let r = f("abcdabcdefghefghX".as_bytes());
assert_eq!(r, Done("X".as_bytes(), A{a: 1, b: 2}));

let r2 = f("abcdefghefghX".as_bytes());
assert_eq!(r2, Done("X".as_bytes(), A{a: 1, b: 2}));
```

More examples of chain usage can be found in the [INI file parser example](tests/ini.rs).

### producers

Todo

### consumers

Todo
