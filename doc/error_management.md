# Error management

nom's errors are designed with multiple needs in mind:
- indicate which parser failed and where in the input data
- accumulate more context as the error goes up the parser chain
- have a very low overhead, as errors are often discarded by the calling parser (examples: `many0`, `alt`)
- can be modified according to the user's needs, because some languages need a lot more information

To match these requirements, nom parsers have to return the following result
type:

```rust
pub type IResult<I, O, E=nom::error::Error<I>> = Result<(I, O), nom::Err<E>>;

pub enum Err<E> {
    Incomplete(Needed),
    Error(E),
    Failure(E),
}
```

The result is either an `Ok((I, O))` containing the remaining input and the
parsed value, or an `Err(nom::Err<E>)` with `E` the error type.
`nom::Err<E>` is an enum because combinators can have different behaviours
depending on the value. The `Err<E>` enum expresses 3 conditions for a parser error:
- `Incomplete` indicates that a parser did not have enough data to decide. This can be returned by parsers found in `streaming` submodules to indicate that we should buffer more data from a file or socket. Parsers in the `complete` submodules assume that they have the entire input data, so if it was not sufficient, they will instead return a `Err::Error`. When a parser returns `Incomplete`, we should accumulate more data in the buffer (example: reading from a socket) and call the parser again
- `Error` is a normal parser error. If a child parser of the `alt` combinator returns `Error`, it will try another child parser
- `Failure` is an error from which we cannot recover: The `alt` combinator will not try other branches if a child parser returns `Failure`. If we know we were in the right branch (example: we found a correct prefix character but input after that was wrong), we can transform a `Err::Error` into a `Err::Failure` with the `cut()` combinator

If we are running a parser and know it will not return `Err::Incomplete`, we can
directly extract the error type from `Err::Error` or `Err::Failure` with the
`finish()` method:

```rust
let parser_result: IResult<I, O, E> = parser(input);
let result: Result<(I, O), E> = parser_result.finish();
```

If we used a borrowed type as input, like `&[u8]` or `&str`, we might want to
convert it to an owned type to transmit it somewhere, with the `to_owned()`
method:

```rust
let result: Result<(&[u8], Value), Err<Vec<u8>>> =
  parser(data).map_err(|e: E<&[u8]>| -> e.to_owned());
```

nom provides a powerful error system that can adapt to your needs: you can
get reduced error information if you want to improve performance, or you can
get a precise trace of parser application, with fine grained position information.

This is done through the third type parameter of `IResult`, nom's parser result
type:

```rust
pub type IResult<I, O, E=nom::error::Error<I>> = Result<(I, O), Err<E>>;

pub enum Err<E> {
    Incomplete(Needed),
    Error(E),
    Failure(E),
}
```

This error type is completely generic in nom's combinators, so you can choose
exactly which error type you want to use when you define your parsers, or
directly at the call site.
See [the JSON parser](https://github.com/Geal/nom/blob/5405e1173f1052f7e006dcb0b9cfda2b06557b65/examples/json.rs#L209-L286)
for an example of choosing different error types at the call site.

## Common error types

### the default error type: nom::error::Error

```rust
#[derive(Debug, PartialEq)]
pub struct Error<I> {
  /// position of the error in the input data
  pub input: I,
  /// nom error code
  pub code: ErrorKind,
}
```

This structure contains a `nom::error::ErrorKind` indicating which kind of
parser encountered an error (example: `ErrorKind::Tag` for the `tag()`
combinator), and the input position of the error.

This error type is fast and has very low overhead, so it is suitable for
parsers that are called repeatedly, like in network protocols.
It is very limited though, it will not tell you about the chain of
parser calls, so it is not enough to write user friendly errors.

Example error returned in a JSON-like parser (from `examples/json.rs`):

```rust
let data = "  { \"a\"\t: 42,
\"b\": [ \"x\", \"y\", 12 ] ,
\"c\": { 1\"hello\" : \"world\"
}
} ";

// will print:
// Err(
//   Failure(
//       Error {
//           input: "1\"hello\" : \"world\"\n  }\n  } ",
//           code: Char,
//       },
//   ),
// )
println!(
  "{:#?}\n",
  json::<Error<&str>>(data)
);
```

### getting more information: nom::error::VerboseError

The  `VerboseError<I>` type accumulates more information about the chain of
parsers that encountered an error:

```rust
#[derive(Clone, Debug, PartialEq)]
pub struct VerboseError<I> {
  /// List of errors accumulated by `VerboseError`, containing the affected
  /// part of input data, and some context
  pub errors: crate::lib::std::vec::Vec<(I, VerboseErrorKind)>,
}

#[derive(Clone, Debug, PartialEq)]
/// Error context for `VerboseError`
pub enum VerboseErrorKind {
  /// Static string added by the `context` function
  Context(&'static str),
  /// Indicates which character was expected by the `char` function
  Char(char),
  /// Error kind given by various nom parsers
  Nom(ErrorKind),
}
```

It contains the input position and error code for each of those parsers.
It does not accumulate errors from the different branches of `alt`, it will
only contain errors from the last branch it tried.

It can be used along with the `nom::error::context` combinator to inform about
the parser chain:

```rust
context(
  "string",
  preceded(char('\"'), cut(terminated(parse_str, char('\"')))),
)(i)
```

It is not very usable if printed directly:

```rust
// parsed verbose: Err(
//   Failure(
//       VerboseError {
//           errors: [
//               (
//                   "1\"hello\" : \"world\"\n  }\n  } ",
//                   Char(
//                       '}',
//                   ),
//               ),
//               (
//                   "{ 1\"hello\" : \"world\"\n  }\n  } ",
//                   Context(
//                       "map",
//                   ),
//               ),
//               (
//                   "{ \"a\"\t: 42,\n  \"b\": [ \"x\", \"y\", 12 ] ,\n  \"c\": { 1\"hello\" : \"world\"\n  }\n  } ",
//                   Context(
//                       "map",
//                   ),
//               ),
//           ],
//       },
//   ),
// )
println!("parsed verbose: {:#?}", json::<VerboseError<&str>>(data));
```

But by looking at the original input and the chain of errors, we can build
a more user friendly error message. The `nom::error::convert_error` function
can build such a message.

```rust
let e = json::<VerboseError<&str>>(data).finish().err().unwrap();
// here we use the `convert_error` function, to transform a `VerboseError<&str>`
// into a printable trace.
//
// This will print:
// verbose errors - `json::<VerboseError<&str>>(data)`:
// 0: at line 2:
//   "c": { 1"hello" : "world"
//          ^
// expected '}', found 1
//
// 1: at line 2, in map:
//   "c": { 1"hello" : "world"
//        ^
//
// 2: at line 0, in map:
//   { "a" : 42,
//   ^
println!(
  "verbose errors - `json::<VerboseError<&str>>(data)`:\n{}",
  convert_error(data, e)
);
```

Note that `VerboseError` and `convert_error` are meant as a starting point for
language errors, but that they cannot cover all use cases. So a custom
`convert_error` function should probably be written.

### Improving usability: nom_locate and nom-supreme

These crates were developed to improve the user experience when writing nom
parsers.

#### nom_locate

[nom_locate](https://docs.rs/nom_locate/) wraps the input data in a `Span`
type that can be understood by nom parsers. That type provides location
information, like line and column.

#### nom-supreme

[nom-supreme](https://docs.rs/nom-supreme/) provides the `ErrorTree<I>` error
type, that provides the same chain of parser errors as `VerboseError`, but also
accumulates errors from the various branches tried by `alt`.

With this error type, you can explore everything that has been tried by the
parser.

## The `ParseError` trait

If those error types are not enough, we can define our own, by implementing
the `ParseError<I>` trait. All nom combinators are generic over that trait
for their errors, so we only need to define it in the parser result type,
and it will be used everywhere.

```rust
pub trait ParseError<I>: Sized {
    /// Creates an error from the input position and an [ErrorKind]
    fn from_error_kind(input: I, kind: ErrorKind) -> Self;

    /// Combines an existing error with a new one created from the input
    /// position and an [ErrorKind]. This is useful when backtracking
    /// through a parse tree, accumulating error context on the way
    fn append(input: I, kind: ErrorKind, other: Self) -> Self;

    /// Creates an error from an input position and an expected character
    fn from_char(input: I, _: char) -> Self {
        Self::from_error_kind(input, ErrorKind::Char)
    }

    /// Combines two existing errors. This function is used to compare errors
    /// generated in various branches of `alt`
    fn or(self, other: Self) -> Self {
        other
    }
}
```

Any error type has to implement that trait, that requires ways to build an
error:
- `from_error_kind`: From the input position and the `ErrorKind` enum that indicates in which parser we got an error
- `append`: Allows the creation of a chain of errors as we backtrack through the parser tree (various combinators will add more context)
- `from_char`: Creates an error that indicates which character we were expecting
- `or`: In combinators like `alt`, allows choosing between errors from various branches (or accumulating them)

We can also implement the `ContextError` trait to support the `context()`
combinator used by `VerboseError<I>`:

```rust
pub trait ContextError<I>: Sized {
    fn add_context(_input: I, _ctx: &'static str, other: Self) -> Self {
        other
    }
}
```

And there is also the `FromExternalError<I, E>` used by `map_res` to wrap
errors returned by other functions:

```rust
pub trait FromExternalError<I, ExternalError> {
  fn from_external_error(input: I, kind: ErrorKind, e: ExternalError) -> Self;
}
```

### Example usage

Let's define a debugging error type, that will print something every time an
error is generated. This will give us a good insight into what the parser tried.
Since errors can be combined with each other, we want it to keep some info on
the error that was just returned. We'll just store that in a string:

```rust
struct DebugError {
    message: String,
}
```

Now let's implement `ParseError` and `ContextError` on it:

```rust
impl ParseError<&str> for DebugError {
    // on one line, we show the error code and the input that caused it
    fn from_error_kind(input: &str, kind: ErrorKind) -> Self {
        let message = format!("{:?}:\t{:?}\n", kind, input);
        println!("{}", message);
        DebugError { message }
    }

    // if combining multiple errors, we show them one after the other
    fn append(input: &str, kind: ErrorKind, other: Self) -> Self {
        let message = format!("{}{:?}:\t{:?}\n", other.message, kind, input);
        println!("{}", message);
        DebugError { message }
    }

    fn from_char(input: &str, c: char) -> Self {
        let message = format!("'{}':\t{:?}\n", c, input);
        println!("{}", message);
        DebugError { message }
    }

    fn or(self, other: Self) -> Self {
        let message = format!("{}\tOR\n{}\n", self.message, other.message);
        println!("{}", message);
        DebugError { message }
    }
}

impl ContextError<&str> for DebugError {
    fn add_context(input: &str, ctx: &'static str, other: Self) -> Self {
        let message = format!("{}\"{}\":\t{:?}\n", other.message, ctx, input);
        println!("{}", message);
        DebugError { message }
    }
}
```

So when calling our JSON parser with this error type, we will get a trace
of all the times a parser stoppped and backtracked:

```rust
println!("debug: {:#?}", root::<DebugError>(data));
```

```
AlphaNumeric:   "\"\t: 42,\n  \"b\": [ \"x\", \"y\", 12 ] ,\n  \"c\": { 1\"hello\" : \"world\"\n  }\n  } "

'{':    "42,\n  \"b\": [ \"x\", \"y\", 12 ] ,\n  \"c\": { 1\"hello\" : \"world\"\n  }\n  } "

'{':    "42,\n  \"b\": [ \"x\", \"y\", 12 ] ,\n  \"c\": { 1\"hello\" : \"world\"\n  }\n  } "
"map":  "42,\n  \"b\": [ \"x\", \"y\", 12 ] ,\n  \"c\": { 1\"hello\" : \"world\"\n  }\n  } "

[..]

AlphaNumeric:   "\": { 1\"hello\" : \"world\"\n  }\n  } "

'"':    "1\"hello\" : \"world\"\n  }\n  } "

'"':    "1\"hello\" : \"world\"\n  }\n  } "
"string":       "1\"hello\" : \"world\"\n  }\n  } "

'}':    "1\"hello\" : \"world\"\n  }\n  } "

'}':    "1\"hello\" : \"world\"\n  }\n  } "
"map":  "{ 1\"hello\" : \"world\"\n  }\n  } "

'}':    "1\"hello\" : \"world\"\n  }\n  } "
"map":  "{ 1\"hello\" : \"world\"\n  }\n  } "
"map":  "{ \"a\"\t: 42,\n  \"b\": [ \"x\", \"y\", 12 ] ,\n  \"c\": { 1\"hello\" : \"world\"\n  }\n  } "

debug: Err(
    Failure(
        DebugError {
            message: "'}':\t\"1\\\"hello\\\" : \\\"world\\\"\\n  }\\n  } \"\n\"map\":\t\"{ 1\\\"hello\\\" : \\\"world
\\"\\n  }\\n  } \"\n\"map\":\t\"{ \\\"a\\\"\\t: 42,\\n  \\\"b\\\": [ \\\"x\\\", \\\"y\\\", 12 ] ,\\n  \\\"c\\\": { 1\
\"hello\\\" : \\\"world\\\"\\n  }\\n  } \"\n",
        },
    ),
)
```

Here we can see that when parsing `{ 1\"hello\" : \"world\"\n  }\n  }`, after
getting past the initial `{`, we tried:
- parsing a `"` because we're expecting a key name, and that parser was part of the
"string" parser
- parsing a `}` because the map might be empty. When this fails, we backtrack,
through 2 recursive map parsers:

```
'}':    "1\"hello\" : \"world\"\n  }\n  } "
"map":  "{ 1\"hello\" : \"world\"\n  }\n  } "
"map":  "{ \"a\"\t: 42,\n  \"b\": [ \"x\", \"y\", 12 ] ,\n  \"c\": { 1\"hello\" : \"world\"\n  }\n  } "
```

## Debugging parsers

While you are writing your parsers, you will sometimes need to follow
which part of the parser sees which part of the input.

To that end, nom provides the `dbg_dmp` function that will observe
a parser's input and output, and print a hexdump of the input if there was an
error. Here is what it could return:

```rust
fn f(i: &[u8]) -> IResult<&[u8], &[u8]> {
    dbg_dmp(tag("abcd"), "tag")(i)
}

let a = &b"efghijkl"[..];

// Will print the following message:
// tag: Error(Error(Error { input: [101, 102, 103, 104, 105, 106, 107, 108], code: Tag })) at:
// 00000000        65 66 67 68 69 6a 6b 6c         efghijkl
f(a);
```

You can go further with the [nom-trace crate](https://github.com/rust-bakery/nom-trace)
