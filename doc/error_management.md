# Error management

nom provides a powerful error system that can adapt to your needs: you can
get reduced error information if you want to improve performance, or you can
get a precise trace of parser application, with fine grained position information.

This is done through the third type parameter of `IResult`, nom's parser result
type:

```rust
pub type IResult<I, O, E=(I, ErrorKind)> = Result<(I, O), Err<E>>;

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

The `Err<E>` enum expresses 3 conditions for a parser error:
- `Incomplete` indicates that a parser did not have enough data to decide. This can be returned by parsers found in `streaming` submodules to indicate that we should buffer more data from a file or socket. Parsers in the `complete` submodules assume that they have the entire input data, so if it was not sufficient, they will instead return a `Err::Error`
- `Error` is a normal parser error. If a child parser of the `alt` combinator returns `Error`, it will try another child parser
- `Failure` is an error from which we cannot recover: The `alt` combinator will not try other branches if a child parser returns `Failure`

## The `ParseError` trait

To allow configurable error types, nom uses the `ParseError` trait in all
combinators, defined as follows:

```rust
pub trait ParseError<I>: Sized {
    fn from_error_kind(input: I, kind: ErrorKind) -> Self;

    fn append(input: I, kind: ErrorKind, other: Self) -> Self;

    fn from_char(input: I, _: char) -> Self {
        Self::from_error_kind(input, ErrorKind::Char)
    }

    fn or(self, other: Self) -> Self {
        other
    }

    fn add_context(_input: I, _ctx: &'static str, other: Self) -> Self {
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
- `add_context`: Works like `append` but uses a static string instead of an `ErrorKind`. Usable with the `nom::error`::context` function

This trait is currently implemented for 3 types:
- `()`: If you want to ignore errors completely
- `(I, ErrorKind)`: The default error type
- `nom::error::VerboseError`: This type accumulates a chain of errors and leverages `from_char` and `add_context`

The `VerboseError` type is especially useful if you need precise position information,
and you want to have a user friendly way of displaying the error.
By calling the `nom::error::convert_error` function with the original input data
(in `&str`) and the error, you can get a trace like this:

```
verbose errors - `root::<VerboseError>(data)`:
0: at line 2:
  "c": { 1"hello" : "world"
         ^
expected '}', found 1

1: at line 2, in map:
  "c": { 1"hello" : "world"
       ^

2: at line 0, in map:
  { "a" : 42,
  ^
```

See [examples/custom_error.rs](https://github.com/Geal/nom/blob/master/examples/custom_error.rs)
for an example of implementing your custom errors.

## Debugging parsers

While you are writing your parsers, you will sometimes need to follow
which part of the parser sees which part of the input.

To that end, nom provides the `dbg_dmp` function and macro, that will observe
a parser's input and output, and print a hexdump of the input if there was an
error. Here is what it could return:

```rust
fn f(i: &[u8]) -> IResult<&[u8], &[u8]> {
    dbg_dmp(tag("abcd"), "tag")(i)
}

let a = &b"efghijkl"[..];

// Will print the following message:
// Error(Position(0, [101, 102, 103, 104, 105, 106, 107, 108])) at l.5 by ' tag ! ( "abcd" ) '
// 00000000        65 66 67 68 69 6a 6b 6c         efghijkl
f(a);
```

You can go further with the [nom-trace crate](https://github.com/rust-bakery/nom-trace):

```rust
#[macro_use] extern crate nom;
#[macro_use] extern crate nom_trace;

//adds a thread local storage object to store the trace
declare_trace!();

pub fn main() {
    named!(parser<&str, Vec<&str>>,
        //wrap a parser with tr!() to add a trace point
        tr!(preceded!(
        tr!(tag!("data: ")),
        tr!(delimited!(
            tag!("("),
            separated_list!(
            tr!(tag!(",")),
            tr!(nom::digit)
            ),
            tr!(tag!(")"))
        ))
        ))
    );

    println!("parsed: {:?}", parser("data: (1,2,3)"));

    // prints the last parser trace
    print_trace!();

    // the list of trace events can be cleared
    reset_trace!();
}
```

This will display:

```
parsed: Ok(("", ["1", "2", "3"]))
preceded        "data: (1,2,3)"

        tag     "data: (1,2,3)"

        -> Ok("data: ")
        delimited       "(1,2,3)"

                digit   "1,2,3)"

                -> Ok("1")
                tag     ",2,3)"

                -> Ok(",")
                digit   "2,3)"

                -> Ok("2")
                tag     ",3)"

                -> Ok(",")
                digit   "3)"

                -> Ok("3")
                tag     ")"

                -> Error(Code(")", Tag))
                tag     ")"

                -> Ok(")")
        -> Ok(["1", "2", "3"])
-> Ok(["1", "2", "3"])
```
