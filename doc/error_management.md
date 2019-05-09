# Error management

Parser combinators are useful tools to build parsers, but they are notoriously
bad at error reporting. This happens because a tree of parser acts as a single
parser, and the only error you get will come from the root parser.

This is especially annoying while developing, since you cannot know which parsers
failed, and why.

Nom provides a few tools to help you in reporting errors and debugging parsers.

## Debugging macros

There are two macros that you can use to check what is happening while you write your parsers: `dbg!` and `dbg_dmp!`.

They take a parser or combinator as input and, if it returns an `Error` or `Incomplete`, will print the result and the parser passed as argument. It will return the result unmodified, so it can be added and removed from your parser without any impact.

```rust
#[macro_use] extern crate nom;

fn main() {
  named!(f, dbg!( tag!( "abcd" ) ) );

  let a = &b"efgh"[..];
  f(a);
}
```

Result:

```rust
Error(Err::Error((0, [101, 102, 103, 104]))) at l.5 by " tag ! ( "abcd" ) "
```

The result sent by `dbg_dmp!` is slightly different:

```rust
#[macro_use] extern crate nom;

fn main() {
  named!(f, dbg_dmp!( tag!( "abcd" ) ) );

  let a = &b"efghijkl"[..];
  f(a);
}
```

It will print, along with the result and the parser, a hexdump of the input buffer passed to the parser.

```
Error(Err::Error((0, [101, 102, 103, 104, 105, 106, 107, 108]))) at l.5 by " tag ! ( "abcd" ) "
00000000        65 66 67 68 69 6a 6b 6c         efghijkl
```

## Error reporting

As a reminder, here are the basic types of nom:

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

The 3 variants of `Err` mean the following:
- `Incomplete`: there's not enough data to decide, add more data (from the file or socket) and try again
- `Error`: a parser encountered an error, but we can backtrack and try other branches
- `Failure`: a parser encountered an error for which we should not backtrack. Typically, we are in the correct parser branch (a correct prefix was seen, etc) so there's no need to try other ones

You can decide which error type to use at function definition. The `named!`
macro will generate parsers with the default error type `(Input, ErrorKind)`,
that associates an error code with the position that triggered it.
There's also the `VerboseError` type, that accumulates errors and positions
as it backtracks through the parse tree.


### Adding an error

Sometimes, you want to provide an error code at a specific point in the parser
tree. The `context` function can be used for this:

```rust
fn string_parser(i: &str) -> IResult<&str, &str, VerboseError<&str>> {
  let (i, _) = char('\"')(i)?;

  context("string", terminated(parse_str, char('\"')))(i)
}

assert_eq!(string_parser("\"abc;"), Err(Err::Error(VerboseError { errors: vec![
  ("\"abc;", VerboseErrorKind::Context("string")),
  (";", VerboseErrorKind::Char('\"'))
])));
```

This function allows use to add user friendly information to an error trace.

## Error pattern matching

Once you get a chain of errors with easily identifying codes, you probably want
to match on these to provide useful error messages.

