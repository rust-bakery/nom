# Upgrading to nom 1.0

The 1.0 release of nom is one of the biggest since the beginning of the project. Its goal was to rework some core parts to be more flexible, and clean code that was awkward or unclear. This resulted in breaking changes, that I hope will not happen again in the future (but hey, we are Rust developers, breaking changes are FUN for us!).

Here are a few tips to update your code to run with nom 1.0:

# Error typing

`nom::Err` now depends on two generic types, the position `P` and the error type `E`:

```rust
pub enum Err<P,E=u32>{
  Code(ErrorKind<E>),
  Node(ErrorKind<E>, Box<Err<P,E>>),
  Position(ErrorKind<E>, P),
  NodePosition(ErrorKind<E>, P, Box<Err<P,E>>)
}
```

The default error type is `u32` to keep some compatibility with older code. To update your code, the first step is to **replace all usages of `nom::ErrorCode` by `nom::ErrorKind`**. `ErrorKind` is now an enum that contains the same instances as the previous `ErrorCode`, with an additional generic parameter:

```rust
pub enum ErrorKind<E=u32> {
  Custom(E),
  Tag,
  MapRes,
  MapOpt,
  Alt,
  [...]
}
```

`ErrorKind::Custom` is where you will store your custom error type. Note that default nom parsers like `alphabetic` use `u32` as custom type, so you may need to translate the error types coming from those parsers like this:

```rust
fix_error!(CustomErrorType, alphabetic)
```

Since the error type is now an enum instead of a `u32`, you can now **replace any `ErrorCode::Tag as u32` by `ErrorKind::Tag`**.

# Lifetime elision

The error type is now completely generic over the input type, so the lifetime that appeared in `IResult` is not necessary anymore. It changes function declarations like this:

```rust
fn parse_status<'a>(i: &'a [u8]) -> IResult<'a, &'a [u8], Status>

// To this:
fn parse_status(i: &[u8]) -> IResult<&[u8], Status>
```

# Producers and consumers

The old implementation was not flexible, and a bit slow (because of allocations). The new implementation can be driven more precisely outside of the consumer, step by step if needed, can return a result, has custom error types, and can combine consumers. You can see [an example in the repository](https://github.com/Geal/nom/blob/1.0/tests/omnom.rs#).

# Changes around `Incomplete`

* `chain!` will now count how much data has been consumed before a child parser returns `Incomplete`, and return an `Incomplete` with the added data size
* an optional parser (in `opt!` or `chain!`) will return `Incomplete` if the child parser returned `Incomplete`, instead of stopping there. This is the correct behaviour, because the result will be the same if the data comes in chunks or complete from the start
* `alt!` will now return `Incomplete` if one of its alternatives returns `Incomplete` instead of skipping to the next branch

In the cases where you know that the data you get is complete, you can wrap a parser with `complete!`. This combinator will transform `Incomplete` in an `Error`.

# Other changes

`filter!` has been renamed to `take_while!`

