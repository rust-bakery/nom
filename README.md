# nom, eating data byte by byte

[![Join the chat at https://gitter.im/Geal/nom](https://badges.gitter.im/Join%20Chat.svg)](https://gitter.im/Geal/nom?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge&utm_content=badge)
[![Build Status](https://travis-ci.org/Geal/nom.svg?branch=master)](https://travis-ci.org/Geal/nom)
[![Coverage Status](https://coveralls.io/repos/Geal/nom/badge.svg?branch=master)](https://coveralls.io/r/Geal/nom?branch=master)

nom is a parser combinators library written in Rust. Its goal is to provide tools to build safe parsers without compromising the speed or memory consumption. To that end, it uses extensively Rust's *strong typing*, *zero copy* parsing, *push streaming*, *pull streaming*, and provides macros and traits to abstract most of the error prone plumbing.

This work is currently experimental, the API and syntax may still change a lot, but it can already be used to parse relatively complex formats like [MP4](tests/mp4.rs).


## Features

Here are the current and planned features, with their status:
- [x] **byte oriented**: the basic type is `&[u8]` and parsers will work as much as possible on byte array slices (but are not limited to them)
- [x] **bit oriented**: nom can address a byte slice as a bit stream
- [x] **zero copy**:
  - [x] **in the parsers**: a parsing chain will almost always return a slice of its input data
  - [x] **in the producers and consumers**: some copying still happens
- [x] **streaming**:
  - [x] **push**: a parser can be directly fed a producer's output and called every time there is data available
  - [x] **pull**: a consumer will take a parser and a producer, and handle all the data gathering and, if available, seeking the streaming
- [x] **macro based syntax**: easier parser building through macro usage
- [x] **state machine handling**: consumers provide a basic way of managing state machines
- [x] **descriptive errors**: the parsers can aggregate a list of error codes with pointers to the incriminated input slice. Those error lists can be pattern matched to provide useful messages
- [ ] **safe parsing**: while I have some confidence in Rust's abilities, this will be put to the test via extensive fuzzing and disassembling

Reference documentation is available [here](http://rust.unhandledexpression.com/nom/).

Some benchmarks are available on [Github](https://github.com/Geal/nom_benchmarks).

## Installation

nom is available on [crates.io](https://crates.io/crates/nom) and can be included in your Cargo enabled project like this:

```toml
[dependencies]
nom = "~0.4.0"
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

## Usage

### Parser combinators

nom uses parser combinators to build and reuse parsers. To work with parser combinators, instead of writing the whole grammar from scratch and generating a parser, or writing the complete state machine by hand, you write small, reusable functions, that you will combine to make more interesting parsers.

This has a few advantages:

- the parsers are small and easy to write
- the parsers are easy to reuse (if they're general enough, please add them to nom!)
- the parsers are easy to test (unit tests and property-based tests)
- the parser combination code looks close to the grammar you would have written
- you can build partial parsers, specific to the data you need at the moment, and ignore the rest

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

`IResult` is an enumeration that can represent:

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

Here are the basic macros available:

- **tag!**: will match the byte array provided as argument
- **is_not!**: will match the longest array not containing any of the bytes of the array provided to the macro
- **is_a!**: will match the longest array containing only bytes of the array provided to the macro
- **filter!**: will walk the whole array and apply the closure to each suffix until the function fails
- **take!**: will take as many bytes as the number provided
- **take_until!**: will take as many bytes as possible until it encounters the provided byte array, and will leave it in the remaining input
- **take_until_and_consume!**: will take as many bytes as possible until it encounters the provided byte array, and will skip it
- **take_until_either_and_consume!**: will take as many bytes as possible until it encounters one of the bytes of the provided array, and will skip it
- **take_until_either!**: will take as many bytes as possible until it encounters one of the bytes of the provided array, and will leave it in the remaining input

#### Combining parsers

- **map!**: applies a function to the output of a `IResult` and puts the result in the output of a `IResult` with the same remaining input
- **flat_map!**: applies a parser to the ouput of a `IResult` and returns a new `IResult` with the same remaining input.
- **map_opt!**: applies a function returning an Option to the output of `IResult`, returns `Done(input, o)` if the result is `Some(o)`, or `Error(0)`
- **map_res!**: applies a function returning a Result to the output of `IResult`, returns `Done(input, o)` if the result is `Ok(o)`, or `Error(0)`

#### Combining parsers with macros

Here again, we use macros to combine parsers easily in useful patterns:

```rust
named!(alt_tags, alt!(tag!("abcd") | tag!("efgh")));

assert_eq!(alt_tags(b"abcdxxx"), Done(b"xxx", b"abcd"));
assert_eq!(alt_tags(b"efghxxx"), Done(b"xxx", b"efgh"));
assert_eq!(alt_tags(b"ijklxxx"), Error(1));

// make the abcd_p parser optional
named!( abcd_opt, opt!( tag!("abcd") ) );

assert_eq!(abcd_opt(b"abcdxxx"), Done(b"xxx", Some(b"abcd")));
assert_eq!(abcd_opt(b"efghxxx"), Done(b"efghxxx", None));

// the abcd_p parser can happen 0 or more times
named!(multi, many0!( tag!( "abcd" ) ) );
let a = b"abcdef";
let b = b"abcdabcdef";
let c = b"azerty";
assert_eq!(multi(a), Done(b"ef", vec![b"abcd"]));
assert_eq!(multi(b), Done(b"ef", vec![b"abcd", b"abcd"]));
assert_eq!(multi(c), Done(b"azerty", Vec::new()));
```

Here are the basic combining macros available:

- **opt!**: will make the parser optional (if it returns the O type, the new parser returns Option<O>)
- **many0!**: will apply the parser 0 or more times (if it returns the O type, the new parser returns Vec<O>)
- **many1!**: will appy the parser 1 or more times


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

More examples of chain usage can be found in the [INI file parser example](tests/ini.rs).

### Producers

While parser combinators alone are useful, you often need to handle the plumbing to feed them with data from a file, a network connection or a memory buffer. In nom, you can use producers to abstract those data accesses. A `Producer` has to implement the following trait:

````rust
use std::io::SeekFrom;
pub enum ProducerState<O> {
  Data(O),
  Eof(O),
  Continue,
  ProducerError(Err),
}

pub trait Producer {
  fn produce(&mut self)                   -> ProducerState<&[u8]>;
  fn seek(&mut self,   position:SeekFrom) -> Option<u64>;
}
```

nom currently provides `FileProducer` and `MemProducer`. The network one and the channel one will soon be implemented. To use them, see the following code:

```rust
use nom::{FileProducer, MemProducer};

FileProducer::new("my_file.txt", 20).map(|mut producer: FileProducer| {
      p.produce();
     //etc
});

let mut p = MemProducer::new(b"abcdefgh", 4);
```

The second argument for both of them is the chunk size for the produce function (which will not return the whole data at once).

The `pusher!` macro is provided to wrap an existing parser, and make it into a function that will handle a producer's chunk as soon as they are available.

```rust
let mut producer = MemProducer::new(b"abcdefgh", 8);

fn print_parser<'a>(data: &'a [u8]) -> IResult<&'a [u8],()> {
  println!("{:?}", data);
  Done(data, ())
}

pusher!(push, print_parser);
push(&mut producer);
```

Note that the code generated by `pusher!` has a very limited support for parsers returning `Incomplete` (it will concatenate multiple outputs of `produce()` and that is all), and does not handle seeking. It is more adapted to push-based streaming, where the data is given as soon as possible by the producer, with little or no support for seeking.

If you need your parser to be smarter with the way it navigates the data, please see the next section, about consumers.

### Consumers

The `Consumer` is used to wrap data gathering from a producer, manage seeking, and hold the parser state while it feeds on data (om nom nom nom). It has to implement the following trait:

```rust
pub enum ConsumerState {
  Await(
    usize,    // consumed
    usize     // needed buffer size
  ),
  Seek(
    usize,    // consumed
    SeekFrom, // new position
    usize     // needed buffer size
  ),
  Incomplete,
  ConsumerDone,
  ConsumerError(Err)
}

pub trait Consumer {
  fn consume(&mut self, input: &[u8]) -> ConsumerState;  // implement it
  fn end(&mut self);                                     // implement it
  fn failed(&mut self, error_code: u32);                 // implement it

  fn run(&mut self, producer: &mut Producer);            // already provided
}
```

In the consumer you implement, you will apply parsers on the input of the `consume` method, and depending on the parser's output, update your internal state and return a new `ConsumerState`:
- **Await(consumed, needed)** indicates how much data was parsed, and how much you need next
- **Seek(consumed, position, needed)** indicates where to seek in the stream, if applicable. For SeekFrom::Current, the current position is the end of the input of `consume`
- **Incomplete** indicates there is not enough input
- **ConsumerDone** indicates the parser is done, no more data should be fed. The `end()` method will be called
- **ConsumerError(error)** indicates there has been an error. The parser will stop

To use your `Consumer`, you need to pass a `Producer` instance to the `run()` method, and it will automatically handle buffering and seeking according to what the `consume()` method returns. Examples:

- if it got 100 bytes from the producer and `consume()` returned `Await(20, 50)`, it will directly give data from the internal buffer.
- if it got 100 bytes from the producer and `consume()` returned `Await(50, 80)`, it will keep the remaining 50 bytes of the input, and call the producer multiple times until it gets 30 bytes or more of data

All of the plumbing is handled for you!

Let's build `Consumer` parsing the `om(nom)*kthxbye` language. It will have an internal state indicating if it is parsing the beginning of the stream, the middle, or the suffix. It could be done easily in one entire parser, but that example is interesting enough to demonstrate consumers, and the consumer lets us handle data by chunks instead of parsing the whole byte array.

```rust
#[macro_use]
extern crate nom;

use nom::{Consumer,ConsumerState,MemProducer,IResult};
use nom::IResult::*;

#[derive(PartialEq,Eq,Debug)]
enum State {
  Beginning,
  Middle,
  End,
  Done
}

struct TestConsumer {
  state:   State,
  counter: usize
}
```

Then, we define the parsers that we will use at every state of our consumer. Note that we do not make one big parser at once. We just build some small, reusable, testable components.

```rust
named!( om_parser,             tag!( "om" ) );
named!( nomnom_parser, many1!( tag!( "nom" ) ) );
named!( end_parser,            tag!( "kthxbye")  );
```


```rust
impl Consumer for TestConsumer {
  fn consume(&mut self, input: &[u8]) -> ConsumerState {
    match self.state {
      State::Beginning => {
        match om_parser(input) {
          Error(a)      => ConsumerState::ConsumerError(a),
          Incomplete(_) => ConsumerState::Await(0, 2),
          Done(_,_)     => {
            // "om" was recognized, get to the next state
            self.state = State::Middle;
            ConsumerState::Await(2, 3)
          }
        }
      },
      State::Middle    => {
        match nomnom_parser(input) {
          Error(a)         => {
            // the "nom" parser failed, let's get to the next state
            self.state = State::End;
            ConsumerState::Await(0, 7)
          },
          Incomplete(_)    => ConsumerState::Await(0, 3),
          Done(i,noms_vec) => {
            // we got a few noms, let's count them and continue
            self.counter = self.counter + noms_vec.len();
            ConsumerState::Await(input.len() - i.len(), 3)
          }
        }
      },
      State::End       => {
        match end_parser(input) {
          Error(a)      => ConsumerState::ConsumerError(a),
          Incomplete(_) => ConsumerState::Await(0, 7),
          Done(_,_)     => {
            // we recognized the suffix, everything was parsed correctly
            self.state = State::Done;
            ConsumerState::ConsumerDone
          }
        }
      },
      State::Done      => {
        // this should not be called
        ConsumerState::ConsumerError(42)
      }
    }
  }

  fn failed(&mut self, error_code: u32) {
    println!("failed with error code {}", error_code);
  }

  fn end(&mut self) {
    println!("we counted {} noms", self.counter);
  }
}

fn main() {
  let mut p = MemProducer::new(b"omnomnomnomkthxbye", 4);
  let mut c = TestConsumer{state: State::Beginning, counter: 0};
  c.run(&mut p);

  assert_eq!(c.counter, 3);
  assert_eq!(c.state, State::Done);
}
```

You can find the code of that consumer in the [tests directory](tests/omnom.rs) with a few unit tests.
