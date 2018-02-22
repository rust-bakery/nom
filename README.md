# nom, eating data byte by byte

[![LICENSE](https://img.shields.io/badge/license-MIT-blue.svg)](LICENSE)
[![Join the chat at https://gitter.im/Geal/nom](https://badges.gitter.im/Join%20Chat.svg)](https://gitter.im/Geal/nom?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge&utm_content=badge)
[![Build Status](https://travis-ci.org/Geal/nom.svg?branch=master)](https://travis-ci.org/Geal/nom)
[![Coverage Status](https://coveralls.io/repos/Geal/nom/badge.svg?branch=master)](https://coveralls.io/r/Geal/nom?branch=master)
[![Crates.io Version](https://img.shields.io/crates/v/nom.svg)](https://crates.io/crates/nom)

nom is a parser combinators library written in Rust. Its goal is to provide tools to build safe parsers without compromising the speed or memory consumption. To that end, it uses extensively Rust's *strong typing* and *memory safety* to produce fast and correct parsers, and provides macros and traits to abstract most of the error prone plumbing.

## Example

[Hexadecimal color](https://developer.mozilla.org/en-US/docs/Web/CSS/color) parser:

```rust
#[macro_use]
extern crate nom;

#[derive(Debug,PartialEq)]
pub struct Color {
  pub red:   u8,
  pub green: u8,
  pub blue:  u8,
}

fn from_hex(input: &str) -> Result<u8, std::num::ParseIntError> {
  u8::from_str_radix(input, 16)
}

fn is_hex_digit(c: char) -> bool {
  let c = c as u8;
  (c >= 0x30 && c <= 0x39) || (c >= 0x41 && c <= 0x46) || (c >= 0x61 && c <= 0x66)
}

named!(hex_primary<&str, u8>,
  map_res!(take_while_m_n!(2, 2, is_hex_digit), from_hex)
);

named!(hex_color<&str, Color>,
  do_parse!(
           tag!("#")   >>
    red:   hex_primary >>
    green: hex_primary >>
    blue:  hex_primary >>
    (Color { red, green, blue })
  )
);

#[test]
fn parse_color() {
  assert_eq!(hex_color("#2F14DF"), Ok(("", Color {
    red: 47,
    green: 20,
    blue: 223,
  })));
}
```

## Documentation

- [Reference documentation](https://docs.rs/nom).
- [Various design documents and tutorials](https://github.com/Geal/nom/tree/master/doc).

If you need any help developing your parsers, please ping `geal` on IRC (mozilla, freenode, geeknode, oftc), go to `#nom` on Mozilla IRC, or on the [Gitter chat room](https://gitter.im/Geal/nom).

## Why use nom

If you want to write:

### binary format parsers

nom was designed to properly parse binary formats from the beginning. Compared
to the usual handwritten C parsers, nom parsers are just as fast, free from
buffer overflow vulnerabilities, and handle common patterns for you:

- [TLV](https://en.wikipedia.org/wiki/Type-length-value)
- bit level parsing
- hexadecimal viewer in the debugging macros for easy data analysis
- streaming parsers for network formats and huge files

Example projects:

- [FLV parser](https://github.com/rust-av/flavors)
- [Matroska parser](https://github.com/rust-av/matroska)
- [tar parser](https://github.com/Keruspe/tar-parser.rs)

### Text format parsers

While nom was made for binary format at first, but it soon grew to work just as
well with text formats. From line based formats like CSV, to more complex, nested
formats such as JSON, nom can manage it, and provides you with useful tools:

- fast case insensitive comparison
- recognizers for escaped strings
- regular expressions can be embedded in nom parsers to represent complex character patterns succintly
- special care has been given to managing non ASCII characters properly

Example projects:

- [HTTP proxy](https://github.com/sozu-proxy/sozu/blob/master/lib/src/parser/http11.rs)
- [TOML parser](https://github.com/joelself/tomllib)

### Programming language parsers

While programming language parsers are usually written manually for more
flexibility and performance, nom can be (and has been successfully) used
as a prototyping parser for a language.

nom will get you started quickly with powerful custom error types, that you
can leverage with [nom_locate](https://github.com/fflorent/nom_locate) to
pinpoint the exact line and column of the error. No need for separate
tokenizing, lexing and parsing phases: nom can automatically handle whitespace
parsing, and construct an AST in place.

Example projects:

- [PHP VM](https://github.com/tagua-vm/parser)
- [Rust parser](https://github.com/dtolnay/syn)
- eve language prototype

### Streaming formats

While a lot of formats (and the code handling them) assume that they can fit
the complete data in memory, there are formats for which we only get a part
of the data at once, like network formats, or huge files.
nom has been designed for a correct behaviour with partial data: if there is
not enough data to decide, nom will tell you it needs more instead of silently
returning a wrong result. Whether your data comes entirely or in chunks, the
result should be the same.

It allows you to build powerful, deterministic state machines for your protocols.

Example projects:

- [HTTP proxy](https://github.com/sozu-proxy/sozu/blob/master/lib/src/parser/http11.rs)
- [using nom with generators](https://github.com/geal/generator_nom)

## Technical features

nom parsers are for:
- [x] **byte-oriented**: the basic type is `&[u8]` and parsers will work as much as possible on byte array slices (but are not limited to them)
- [x] **bit-oriented**: nom can address a byte slice as a bit stream
- [x] **string-oriented**: the same kind of combinators can apply on UTF-8 strings as well
- [x] **zero-copy**: if a parser returns a subset of its input data, it will return a slice of that input, without copying
- [x] **streaming**: nom can work on partial data and detect when it needs more data to produce a correct result
- [x] **macro based syntax**: easier parser building through macro usage
- [x] **descriptive errors**: the parsers can aggregate a list of error codes with pointers to the incriminated input slice. Those error lists can be pattern matched to provide useful messages.
- [x] **custom error types**: you can provide a specific type to improve errors returned by parsers
- [x] **safe parsing**: nom leverages Rust's safe memory handling and powerful types, and parsers are routinely fuzzed and tested with real world data. So far, the only flaws found by fuzzing were in code written outside of nom
- [x] **speed**: benchmarks have shown that nom parsers often outperform many parser combinators library like Parsec and attoparsec, some regular expression engines and even handwritten C parsers

Some benchmarks are available on [Github](https://github.com/Geal/nom_benchmarks).

## Installation

nom is available on [crates.io](https://crates.io/crates/nom) and can be included in your Cargo enabled project like this:

```toml
[dependencies]
nom = "^3.2"
```

Then include it in your code like this:

```rust
#[macro_use]
extern crate nom;
```

**NOTE: if you have existing code using nom below the 4.0 version, please take a look
at the [upgrade documentation](https://github.com/Geal/nom/blob/master/doc/upgrading_to_nom_4.md)
to handle the breaking changes.**

There are a few compilation features:

* `std`: (activated by default) if disabled, nom can work in `no_std` builds
* `nightly`: enables helpful error messages if you use a nightly compiler
* `regexp`: enables regular expression parsers with the `regex` crate
* `regexp_macros`: enables regular expression parsers with the `regex` and `regex_macros` crates. Regular expressions can be defined at compile time, but it requires a nightly version of rustc
* `verbose-errors`: accumulate error codes and input positions as you backtrack through the parser tree. This gives you precise information about which part of the parser was affected by which part of the input

You can activate those features like this:

```toml
[dependencies.nom]
version = "^3.2"
features = ["regexp"]
```

## Usage

### Parser combinators

Parser combinators are an approach to parsers that is very different from software like [lex](https://en.wikipedia.org/wiki/Lex_(software)) and [yacc](https://en.wikipedia.org/wiki/Yacc). Instead of writing the grammar in a separate file and generating the corresponding code, you use very small functions with very specific purpose, like "take 5 bytes", or "recognize the word 'HTTP'", and assemble then in meaningful patterns like "recognize 'HTTP', then a space, then a version".
The resulting code is small, and looks like the grammar you would have written with other parser approaches.

This has a few advantages:

- the parsers are small and easy to write
- the parsers components are easy to reuse (if they're general enough, please add them to nom!)
- the parsers components are easy to test separately (unit tests and property-based tests)
- the parser combination code looks close to the grammar you would have written
- you can build partial parsers, specific to the data you need at the moment, and ignore the rest

Here is an example of one such parser, to recognize text between parentheses:

```rust
#[macro_use]
extern crate nom;

named!(parens, delimited!(char!('('), is_not!(")"), char!(')')));
```

It defines a function named `parens`, which will recognize a sequence of the character `(`, the longest byte array not containing `)`, then the character `)`, and will return the byte array in the middle.

Here is another parser, written without using nom's macros this time:

```rust
#[macro_use]
extern crate nom;

use nom::{IResult,Err,Needed};

fn take4(i:&[u8]) -> IResult<&[u8], &[u8]>{
  if i.len() < 4 {
    Err(Err::Incomplete(Needed::Size(4)))
  } else {
    Ok((&i[4..],&i[0..4]))
  }
}
```

This function takes a byte array as input, and tries to consume 4 bytes. With macros, you would write it like this:

```rust
#[macro_use]
extern crate nom;

named!(take4, take!(4));
```


A parser in nom is a function which, for an input type `I`, an output type `O` and an optional error type `E`, will have the following signature:

```rust
fn parser(input: I) -> IResult<I, O, E>;
```

Or like this, if you don't want to specify a custom error type (it will be `u32` by default):

```rust
fn parser(input: I) -> IResult<I, O>;
```

`IResult` is an alias for the `Result` type:

```rust
use nom::{Needed, Context};

type IResult<I, O, E = u32> = Result<(I, O), Err<I, E>>;

enum Err<I, E = u32> {
  Incomplete(Needed),
  Error(Context<I, E>),
  Failure(Context<I, E>),
}
```

It can have the following values:

- a correct result `Ok((I,O))` with the first element being the remaining of the input (not parsed yet), and the second the output value;
- an error `Err(Err::Error(c))` with `c` an enum that contians an error code with its position in the input, and optionally a chain of accumulated errors;
- an error `Err(Err::Incomplete(Needed))` indicating that more input is necessary. `Needed` can indicate how much data is needed
- an error `Err(Err::Failure(c))`. It works like the `Error` case, except it indicates an unrecoverable error: we cannot backtrack and test another parser

There is already a large list of basic parsers available, like:

- **`length_value`**: a byte indicating the size of the following buffer
- **`not_line_ending`**: returning as much data as possible until a line ending (\r or \n) is found
- **`line_ending`**: matches a line ending
- **`alpha`**: will return the longest alphabetical array from the beginning of the input
- **`digit`**: will return the longest numerical array from the beginning of the input
- **`alphanumeric`**: will return the longest alphanumeric array from the beginning of the input
- **`space`**: will return the longest array containing only spaces
- **`multispace`**: will return the longest array containing space, \r or \n
- **`be_u8`**, **`be_u16`**, **`be_u32`**, **`be_u64`** to parse big endian unsigned integers of multiple sizes
- **`be_i8`**, **`be_i16`**, **`be_i32`**, **`be_i64`** to parse big endian signed integers of multiple sizes
- **`be_f32`**, **`be_f64`** to parse big endian floating point numbers
- **`eof`**: a parser that is successful only if the input is over. In any other case, it returns an error.

Please refer to the [documentation][doc] for an exhaustive list of parsers.

#### Making new parsers with macros

Macros are the main way to make new parsers by combining other ones. Those macros accept other macros or function names as arguments. You then need to make a function out of that combinator with **`named!`**, or a closure with **`closure!`**. Here is how you would do, with the **`tag!`** and **`take!`** combinators:

```rust
named!(abcd_parser, tag!("abcd")); // will consume bytes if the input begins with "abcd"


named!(take_10, take!(10));        // will consume and return 10 bytes of input
```

The **`named!`** macro can take three different syntaxes:

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

- **`tag!`**: will match the byte array provided as argument
- **`is_not!`**: will match the longest array not containing any of the bytes of the array provided to the macro
- **`is_a!`**: will match the longest array containing only bytes of the array provided to the macro
- **`take_while!`**: will walk the whole array and apply the closure to each suffix until the function fails
- **`take!`**: will take as many bytes as the number provided
- **`take_until!`**: will take as many bytes as possible until it encounters the provided byte array, and will leave it in the remaining input
- **`take_until_and_consume!`**: will take as many bytes as possible until it encounters the provided byte array, and will skip it
- **`take_until_either_and_consume!`**: will take as many bytes as possible until it encounters one of the bytes of the provided array, and will skip it
- **`take_until_either!`**: will take as many bytes as possible until it encounters one of the bytes of the provided array, and will leave it in the remaining input
- **`map!`**: applies a function to the output of a `IResult` and puts the result in the output of a `IResult` with the same remaining input
- **`flat_map!`**: applies a parser to the output of a `IResult` and returns a new `IResult` with the same remaining input.
- **`map_opt!`**: applies a function returning an Option to the output of `IResult`, returns `Done(input, o)` if the result is `Some(o)`, or `Error(0)`
- **`map_res!`**: applies a function returning a Result to the output of `IResult`, returns `Done(input, o)` if the result is `Ok(o)`, or `Error(0)`

Please refer to the [documentation][doc] for an exhaustive list of combinators.

#### Combining parsers

There are more high level patterns, like the **`alt!`** combinator, which provides a choice between multiple parsers. If one branch fails, it tries the next, and returns the result of the first parser that succeeds:

```rust
named!(alt_tags, alt!(tag!("abcd") | tag!("efgh")));

assert_eq!(alt_tags(b"abcdxxx"), Done(&b"xxx"[..], &b"abcd"[..]));
assert_eq!(alt_tags(b"efghxxx"), Done(&b"xxx"[..], &b"efgh"[..]));
assert_eq!(alt_tags(b"ijklxxx"), Error(Position(Alt, &b"ijklxxx"[..])));
```

The pipe `|` character is used as separator.

The **`opt!`** combinator makes a parser optional. If the child parser returns an error, **`opt!`** will succeed and return None:

```rust
named!( abcd_opt< &[u8], Option<&[u8]> >, opt!( tag!("abcd") ) );

assert_eq!(abcd_opt(b"abcdxxx"), Done(&b"xxx"[..], Some(&b"abcd"[..])));
assert_eq!(abcd_opt(b"efghxxx"), Done(&b"efghxxx"[..], None));
```

**`many0!`** applies a parser 0 or more times, and returns a vector of the aggregated results:

```rust
use std::str;
named!(multi< Vec<&str> >, many0!( map_res!(tag!( "abcd" ), str::from_utf8) ) );
let a = b"abcdef";
let b = b"abcdabcdef";
let c = b"azerty";
assert_eq!(multi(a), Done(&b"ef"[..],     vec!["abcd"]));
assert_eq!(multi(b), Done(&b"ef"[..],     vec!["abcd", "abcd"]));
assert_eq!(multi(c), Done(&b"azerty"[..], Vec::new()));
```

Here are some basic combining macros available:

- **`opt!`**: will make the parser optional (if it returns the `O` type, the new parser returns `Option<O>`)
- **`many0!`**: will apply the parser 0 or more times (if it returns the `O` type, the new parser returns `Vec<O>`)
- **`many1!`**: will apply the parser 1 or more times

Please refer to the [documentation][doc] for an exhaustive list of combinators.

There are more complex (and more useful) parsers like `do_parse!` and `tuple!`, which are used to apply a series of parsers then assemble their results.

Example with `tuple!`:

```rust
named!(tpl<&[u8], (u16, &[u8], &[u8]) >,
  tuple!(
    be_u16 ,
    take!(3),
    tag!("fg")
  )
);

assert_eq!(
  tpl(&b"abcdefgh"[..]),
  Done(
    &b"h"[..],
    (0x6162u16, &b"cde"[..], &b"fg"[..])
  )
);
assert_eq!(tpl(&b"abcde"[..]), Incomplete(Needed::Size(7)));
let input = &b"abcdejk"[..];
assert_eq!(tpl(input), Error(Position(ErrorKind::Tag, &input[5..])));
```

Example with `do_parse!`:

```rust
#[derive(Debug, PartialEq)]
struct A {
  a: u8,
  b: u8
}

fn ret_int1(i:&[u8]) -> IResult<&[u8], u8> { Done(i,1) }
fn ret_int2(i:&[u8]) -> IResult<&[u8], u8> { Done(i,2) }

named!(f<&[u8],A>,
  do_parse!(    // the parser takes a byte array as input, and returns an A struct
    tag!("abcd")       >>      // begins with "abcd"
    opt!(tag!("abcd")) >>      // this is an optional parser
    aa: ret_int1       >>      // the return value of ret_int1, if it does not fail, will be stored in aa
    tag!("efgh")       >>
    bb: ret_int2       >>
    tag!("efgh")       >>

    (A{a: aa, b: bb})          // the final tuple will be able to use the variable defined previously
  )
);

let r = f(b"abcdabcdefghefghX");
assert_eq!(r, Done(&b"X"[..], A{a: 1, b: 2}));

let r2 = f(b"abcdefghefghX");
assert_eq!(r2, Done(&b"X"[..], A{a: 1, b: 2}));
```

The double right arrow `>>` is used as separator between every parser in the sequence, and the last closure can see the variables storing the result of parsers. Unless the specified return type is already a tuple, the final line should be that type wrapped in a tuple.

More examples of [`do_parse!`](http://rust.unhandledexpression.com/nom/macro.do_parse.html) and [`tuple!`](http://rust.unhandledexpression.com/nom/macro.tuple.html) usage can be found in the [INI file parser example](tests/ini.rs).

# Parsers written with nom

Here is a list of known projects using nom:

- Text file formats:
  * [Ceph Crush](https://github.com/cholcombe973/crushtool)
  * [XFS Runtime Stats](https://github.com/ChrisMacNaughton/xfs-rs)
  * [CSV](https://github.com/GuillaumeGomez/csv-parser)
  * [FASTQ](https://github.com/elij/fastq.rs)
  * [INI](https://github.com/Geal/nom/blob/master/tests/ini.rs)
  * [ISO 8601 dates](https://github.com/badboy/iso8601)
  * [libconfig-like configuration file format](https://github.com/filipegoncalves/rust-config)
  * [Web archive](https://github.com/sbeckeriv/warc_nom_parser)
- Programming languages:
  * [GLSL](https://github.com/phaazon/glsl)
  * [Lua](https://github.com/doomrobo/nom-lua53)
  * [SQL](https://github.com/ms705/nom-sql)
- Interface definition formats:
  * [Thrift](https://github.com/thehydroimpulse/thrust)
- Audio, video and image formats:
  * [GIF](https://github.com/Geal/gif.rs)
  * [MagicaVoxel .vox](https://github.com/davidedmonds/dot_vox)
  * [midi](https://github.com/derekdreery/nom-midi-rs)
- Document formats:
  * [TAR](https://github.com/Keruspe/tar-parser.rs)
  * [GZ](https://github.com/nharward/nom-gzip)
- Database formats:
  * [Redis database files](https://github.com/badboy/rdb-rs)
- Network protocol formats:
  * [Bencode](https://github.com/jbaum98/bencode.rs)
  * [IMAP](https://github.com/djc/imap-proto)
  * [IRC](https://github.com/Detegr/RBot-parser)
  * [Pcap-NG](https://github.com/richo/pcapng-rs)
  * [NTP](https://github.com/rusticata/ntp-parser)
  * [SNMP](https://github.com/rusticata/snmp-parser)
  * [DER](https://github.com/rusticata/der-parser)
  * [TLS](https://github.com/rusticata/tls-parser)
  * [IPFIX / Netflow v10](https://github.com/dominotree/rs-ipfix)
- Language specifications:
  * [BNF](https://github.com/snewt/bnf)
- [using nom as lexer and parser](https://github.com/Rydgel/monkey-rust)

Want to create a new parser using `nom`? A list of not yet implemented formats is available [here](https://github.com/Geal/nom/issues/14).

Want to add your parser here? Create a pull request for it!
