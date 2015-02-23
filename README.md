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
- [x]: **macro based syntax**: easier parser building through macro usage
- [ ] **safe parsing**: while I have some confidence in Rust's abilities, this will be put to the test by extensive fuzzing
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


