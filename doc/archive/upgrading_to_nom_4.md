# Upgrading to nom 4.0

The nom 4.0 is a nearly complete rewrite of nom's internal structures, along with a cleanup of a lot of parser and combinators whose semantics were unclear. Upgrading from previous nom versions can require a lot of changes, especially if you have a lot of unit tests. But most of those changes are pretty straightforward.

## Changes in internal structures

Previous versions of nom all generated parsers with the following signature:

```rust
fn parser(input: I) -> IResult<I,O> { ... }
```

With the following definition for `IResult`:

```rust
pub enum IResult<I,O,E=u32> {
  /// remaining input, result value
  Done(I,O),
  /// indicates the parser encountered an error. E is a custom error type you can redefine
  Error(Err<E>),
  /// Incomplete contains a Needed, an enum that can represent a known quantity of input data, or unknown
  Incomplete(Needed)
}

pub enum Needed {
  /// needs more data, but we do not know how much
  Unknown,
  /// contains the required total data size
  Size(usize)
}

// if the "verbose-errors" feature is not active
pub type Err<E=u32> = ErrorKind<E>;

// if the "verbose-errors" feature is active
pub enum Err<P,E=u32>{
  /// An error code, represented by an ErrorKind, which can contain a custom error code represented by E
  Code(ErrorKind<E>),
  /// An error code, and the next error
  Node(ErrorKind<E>, Vec<Err<P,E>>),
  /// An error code, and the input position
  Position(ErrorKind<E>, P),
  /// An error code, the input position and the next error
  NodePosition(ErrorKind<E>, P, Vec<Err<P,E>>)
}
```

The new design uses the `Result` type from the standard library:

```rust
pub type IResult<I, O, E = u32> = Result<(I, O), Err<I, E>>;

pub enum Err<I, E = u32> {
  /// There was not enough data
  Incomplete(Needed),
  /// The parser had an error (recoverable)
  Error(Context<I, E>),
  /// The parser had an unrecoverable error
  Failure(Context<I, E>),
}

pub enum Needed {
  /// needs more data, but we do not know how much
  Unknown,
  /// contains the required additional data size
  Size(usize)
}

// if the "verbose-errors" feature is inactive
pub enum Context<I, E = u32> {
  Code(I, ErrorKind<E>),
}

// if the "verbose-errors" feature is active
pub enum Context<I, E = u32> {
  Code(I, ErrorKind<E>),
  List(Vec<(I, ErrorKind<E>)>),
}
```

With this new design, the `Incomplete` case is now part of the error case, and we get a `Failure`
case representing an unrecoverable error (combinators like `alt!` will not try another branch).
The verbose error management is now a truly additive feature above the simple one (it adds a
case to the `Context` enum).

Error management types also get smaller and more efficient. We can now return
the related input as part of the error in all cases.

All of this will likely not affect your existing parsers, but require changes to the surrounding
code that manipulates parser results.

## Faster parsers, new memory layout but with lower footprint

These changes keep the same memory footprint in simple errors mode, and reduce it in verbose errors:

| size of `IResult<&[u8], &[u8]>` | simple errors | verbose errors |
|---|---|---|
| nom 3 | 40 bytes | 64 bytes |
| nom 4 | 40 bytes | 48 bytes |

In addition, [parsers are faster in nom 4 than in nom 3](https://github.com/Geal/nom/issues/356#issuecomment-333816834). This change is justified.

## Replacing parser result matchers

Whenever you use pattern matching on the result of a parser, or compare it to another parser
result (like in a unit test), you will have to perform the following changes:

For the correct result case:

```rust
IResult::Done(i, o)

// becomes

Ok((i, o))
```

For the error case (note that argument position for `error_position` and other sibling macros was changed
for the sake of consistency with the rest of the code):

```rust
IResult::Error(error_position!(ErrorKind::OneOf, input)),

// becomes

Err(Err::Error(error_position!(input, ErrorKind::OneOf)))
```

```rust
IResult::Incomplete(Needed::Size(1))

// becomes

Err(Err::Incomplete(Needed::Size(1)))
```

For pattern matching, you now need to handle the `Failure` case as well, which works like the error
case:

```rust
match result {
  Ok((remaining, value)) => { ... },
  Err(Err::Incomplete(needed)) => { ... },
  Err(Err::Error(e)) | Err(Err::Failure(e)) => { ... }
}
```

## Errors on `Incomplete` data size calculation

In previous versions, `Needed::Size(sz)` indicated the total needed data size (counting the actual input).
Now it only returns the additional data needed, so the values will have changed.

## New trait for input types

nom allows other input types than `&[u8]` and `&str`, as long as they implement a set of traits
that are used everywhere in nom. This version introduces the `AtEof` trait:

```rust
pub trait AtEof {
  fn at_eof(&self) -> bool;
}
```

This trait allows the input value to indicate whether there can be more input coming later (buffering
data from a file, or waiting for network data).

## Dealing with `Incomplete` usage

nom's parsers are designed to work around streaming issues: if there is not enough data to decide, a
parser will return `Incomplete` instead of returning a partial value that might be false.

As an example, if you want to parse alphabetic characters then digits, when you get the whole input
`abc123;`, the parser will return `abc` for alphabetic characters, and `123` for the digits, and `;`
as remaining input.

But if you get that input in chunks, like `ab` then `c123;`, the alphabetic characters parser will
return `Incomplete`, because it does not know if there will be more matching characters afterwards.
If it returned `ab` directly, the digit parser would fail on the rest of the input, even though the
input had the valid format.

For some users, though, the input will never be partial (everything could be loaded in memory at once),
and the solution in nom 3 and before was to wrap parts of the parsers with the `complete!()` combinator
that transforms `Incomplete` in `Error`.

nom 4 is much stricter about the behaviour with partial data, but provides better tools to deal with it.
Thanks to the new `AtEof` trait for input types, nom now provides the `CompleteByteSlice(&[u8])` and
`CompleteStr(&str)` input types, for which the `at_eof()` method always returns true.
With these types, no need to put a `complete!()` combinator everywhere, you can just apply those types
like this:

```rust
named!(parser<&str,ReturnType>, ... );

// becomes

named!(parser<CompleteStr,ReturnType>, ... );
```

```rust
named!(parser<&str,&str>, ... );

// becomes

named!(parser<CompleteStr,CompleteStr>, ... );
```

```rust
named!(parser, ... );

// becomes

named!(parser<CompleteByteSlice,CompleteByteSlice>, ... );
```

And as an example, for a unit test:

```rust
assert_eq!(parser("abcd123"), Ok(("123", "abcd"));

// becomes

assert_eq!(parser(CompleteStr("abcd123")), Ok((CompleteStr("123"), CompleteStr("abcd")));
```

These types allow you to correctly handle cases like text formats for which there might be a last
empty line or not, as seen in [one of the examples](https://github.com/Geal/nom/blob/87d837006467aebcdb0c37621da874a56c8562b5/tests/multiline.rs).

If those types feel a bit long to write everywhere in the parsers, it's possible
to alias them like this:

```rust
use nom::types::CompleteByteSlice as Input;
```

## Custom error types

Custom error types caused a lot of type inference issues in previous nom versions. Now error types
are automatically converted as needed. If you want to set up a custom error type, you now need to
implement `std::convert::From<u32>` for this type.

## Producers and consumers

Producers and consumers were removed in nom 4. That feature was too hard to integrate in code that
deals with IO.

