# Upgrading to nom 5.0

## Changes in error types

**If you have a lot of unit tests, this is probably the biggest issue you'll encounter**

Error management has been rewritten to avoid two issues present in previous
versions:
- The error type was causing type inference issues in macros
- The `verbose-errors` was changing the API (adding a variant in an enum) and
reducing the parsing speed. Since compilation features are additive, if a
dependency used nom with `verbose-errors`, it would be activated for all dependencies

The new error management simplifies the internal type, removing the `Context`
type and the error conversions that needed to happen everywhere.

Here's how the types change. Before:

```rust
type IResult<I, O, E = u32> = Result<(I, O), Err<I, E>>;

pub enum Err<I, E = u32> {
    Incomplete(Needed),
    Error(Context<I, E>),
    Failure(Context<I, E>),
}

pub enum Context<I, E = u32> {
    Code(I, ErrorKind<E>),
    // this variant only present if `verbose-errors` is active
    List(Vec<(I, ErrorKind<E>)>),
}
```

In nom 5:

```rust
type IResult<I, O, E = (I, ErrorKind)> = Result<(I, O), Err<E>>;

pub enum Err<E> {
    Incomplete(Needed),
    Error(E),
    Failure(E),
}
```

Now the error type is completely generic, so you can choose exactly
what you need, from erasing errors entirely, to reproducing the
`verbose-errors` feature with the [`VerboseError` type](https://docs.rs/nom/latest/nom/error/struct.VerboseError.html).
The [`ErrorKind` enum](https://docs.rs/nom/latest/nom/error/enum.ErrorKind.html)
is not generic now: It does not need to hold a custom error type.

Any error type has to implement the [`ParseError` trait](https://docs.rs/nom/latest/nom/error/trait.ParseError.html)
that specifies methods to build an error from a position in input data,
and an `ErrorKind`, or another error, etc.

Since the error types change, this will probably generate errors
in your unit tests.

Usually, changing a `Err(Err::Error(Context::Code(input, error)))` to
`Err(Err::Error((input, error)))` is enough (if you use the default
error type `(Input, ErrorKind)`.

## Removal of `CompleteStr` and `CompleteByteSlice`

Those types were introduced in nom 4 as alternative input types, to
solve issues with streaming parsers.

A core feature of nom is its support for streaming parsers: When you are
handling network packets or large files, you might not have all of the data.
As an example, if you use a parser recognizing numbers and you pass as input
"123", the parser will return `Err(Err::Incomplete(_))` because it cannot decide
if it has the whole input or not. The complete data could be "123;" or "12345".

There are various issues with this approach, though. A lot of formats, especially
text formats, are not meant to be very large, and in all cases the data will be
entirely loaded in memory, so handling the streaming case gets annoying.
And for some binary formats, there will often be some TLV (tag/length/value)
elements for which we already know the complete size of the value.

nom can work on various input types, as long as they implement a common set of
traits, so nom 4 had the `CompleteByteSlice` and `CompleteStr` types as alternatives
of `&[u8]` and `&str`, that changed the behaviour of parsers to assume that the
input data is complete. Unfortunately, those types were hard to handle, since
we would often need to convert them back and forth with their inner types,
and they would appear everywhere in parser signatures. Also, they were unexpectedly
slow, even though they were just wrapper types.

In nom 5, those types were removed, and instead we have *streaming* and *complete*
versions of various function combinators. You can find them in the corresponding
submodules of the `bytes`, `character`, and `number` modules. Since macros cannot
be isolated in modules (they are all at the top level once exported), all macros
have been rewritten to use the *streaming* version.

Upgrading from nom 4 means removing the `CompleteStr` and `CompleteByteSlice` types
if you were using them, and checking which parsers suddenly return `Incomplete` on
valid inputs. It indicates that you will need to replace some macros combinators
with the *complete* function version.

## From macros to functions

nom has used macros as its core tool for a long time, since they were a powerful
tool to generate parsers. The code created was simple, approximately the same way
it could be written manually, and it was easy for the compiler to optimize it.

Unfortunately, macros were sometimes hard to manipulate, since nom was relying
on a few lesser known tricks to build its DSL, and macros parsing errors were
often too cryptic to understand.

nom 5 introduces a new technique to write combinators. Instead of using macros
that can take other macros as argument and call them by rewriting their argument
list, we have functions that take other functions as arguments, and return
functions.

This technique has a lot of advantages over macros:
- No type inference issues, you can explicitly describe the error type in
function definitions
- Nicer compilation errors: rustc can show you exactly what is missing when calling
a combinator, if you need to import new traits, etc.
- Those functions are actually faster than nom 4's macros when built with link time
optimization
- Small gain in compilation speed (since code can be reused instead of regenerated
everywhere)
- The macros are still there, but were rewritten to use the functions instead, so
they gain the performance benefit immediately

In practice, nom parsers will have the following signature:
`Input -> IResult<Input, Output, Error>`

A function combinator will then have this signature:
`<args> -> impl Fn(Input) -> IResult<Input, Output, Error>`

Here is an example with a simplified `take` combinator:

```rust
pub fn take(count: usize) -> impl Fn(&[u8]) -> IResult<&[u8], &[u8]>
where
{
  move |i: &[u8]| {
    if i.len() < count {
      Err(Err::Error((i, ErrorKind::Eof))
    } else {
      Ok(i.split_at(count))
    }
  }
}
```

`take` generates a closure and returns it. We can use it directly like this:
`take(5)(input)`.

(this version of `take` is simplified because it actually uses generic input
and error types and various traits over these types)

More complex combinators like `pair` (returns a tuple of the result of 2 parsers)
will be able to combine parsers to make more advanced ones:

```rust
pub fn pair<I, O1, O2, E, F, G>(first: F, second: G) -> impl Fn(I) -> IResult<I, (O1, O2), E>
where
  F: Fn(I) -> IResult<I, O1, E>,
  G: Fn(I) -> IResult<I, O2, E>,
{
  move |input: I| {
    let (input, o1) = first(input)?;
    second(input).map(|(i, o2)| (i, (o1, o2)))
  }
}
```

This combinator is generic over its parser arguments and can assemble them in
the closure that it returns.

You can then use it that way:

```rust
fn parser(i: &str) -> IResult<&str, (&str, &str)> {
  pair(alpha0, digit0)(i)
}

// will return `Ok((";", ("abc", "123")))`
parser("abc123;");
```
