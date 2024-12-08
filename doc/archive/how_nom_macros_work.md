# How nom macros work

**NOTE: macros were removed in nom 7. You should now use the function based combinators**

nom uses Rust macros heavily to provide a nice syntax and generate parsing code.
This has multiple advantages:

* It gives the appearance of combining functions without the runtime cost of closures
* It helps Rust's code inference and borrow checking (less lifetime issues than iterator based solutions)
* The generated code is very linear, just a large chain of pattern matching

As a prerequisite, if you need more information on macros, please refer to
[the little book of Rust macros](https://danielkeep.github.io/tlborm/book/README.html)
and the [Macromancy talk](https://www.youtube.com/watch?v=8rodUyaGkQo)

# Defining a new macro

Let's take the `opt!` macro as example: `opt!` returns `IResult<I,Option<O>>`,
producing a `Some(o)` if the child parser succeeded, and None otherwise. Here
is how you could use it:

```rust
named!(opt_tag<Option<&[u8]>>, opt!(digit));
```

And here is how it is defined:

```rust
#[macro_export]
macro_rules! opt(
  ($i:expr, $submac:ident!( $($args:tt)* )) => ({
    match $submac!($i, $($args)*) {
      Ok((i,o))          => Ok((i, Some(o))),
      Err(Err::Error(_)) => Ok(($i, None)),
      Err(e)             => Err(e),
    }
  });
  ($i:expr, $f:expr) => (
    opt!($i, call!($f));
  );
);
```

To define a Rust macro, you indicate the name of the macro, then each pattern it
is meant to apply to:

```rust
macro_rules! my_macro (
  (<pattern1>) => ( <generated code for pattern1> );
  (<pattern2>) => ( <generated code for pattern2> );
);
```

## Passing input

The first thing you can see in `opt!` is that the pattern have an additional
parameter that you do not use:

```rust
($i:expr, $f:expr)
```

While you call:

```rust
opt!(digit)
```

This is the first trick of nom macros: the first parameter, usually `$i` or `$input`,
is the input data, passed by the parent parser. The expression using `named!` will
translate like this:

```rust
named!(opt_tag<Option<&[u8]>>, opt!(digit));
```

to

```rust
fn opt_tag(input:&[u8]) -> IResult<&[u8], Option<&[u8]>> {
  opt!(input, digit)
}
```

This is how combinators hide all the plumbing: they receive the input automatically
from the parent parser, may use that input, and pass the remaining input to the child
parser.

When you have multiple submacros, such as this example, the input is always passed
to the first, top level combinator:

```rust
macro_rules! multispaced (
    ($i:expr, $submac:ident!( $($args:tt)* )) => (
        delimited!($i, opt!(multispace), $submac!($($args)*), opt!(multispace));
    );
    ($i:expr, $f:expr) => (
        multispaced!($i, call!($f));
    );
);
```

Here, `delimited!` will apply `opt!(multispace)` on the input, and if successful,
will apply `$submac!($($args)*)` on the remaining input, and if successful, store
the output and apply `opt!(multispace)` on the remaining input.

## Applying on macros or functions

The second trick you can see is the two patterns:

```rust
#[macro_export]
macro_rules! opt(
  ($i:expr, $submac:ident!( $($args:tt)* )) => (
    [...]
  );
  ($i:expr, $f:expr) => (
    opt!($i, call!($f));
  );
);
```

The first pattern is used to receive a macro as child parser, like this:

```rust
opt!(tag!("abcd"))
```

The second pattern can receive a function, and transforms it in a macro, then calls
itself again. This is done to avoid repeating code. Applying `opt!` with `digit`
as argument would be transformed from this:

```rust
opt!(digit)
```

transformed with the second pattern:

```rust
opt!(call!(digit))
```

The `call!` macro transforms `call!(input, f)` into `f(input)`. If you need to pass
more parameters to the function, you can Use `call!(input, f, arg, arg2)` to get
`f(input, arg, arg2)`.

## Using the macro's parameters

The macro argument is decomposed into `$submac:ident!`, the macro's name and a bang,
and `( $($args:tt)* )`, the tokens contained between the parenthesis of the macro call.

```rust
($i:expr, $submac:ident!( $($args:tt)* )) => ({
    match $submac!($i, $($args)*) {
      Ok((i,o))          => Ok((i, Some(o))),
      Err(Err::Error(_)) => Ok(($i, None)),
      Err(e)             => Err(e),
    }
  });
```

The macro is called with the input we got, as first argument, then we pattern
match on the result. Every combinator or parser must return a `IResult`, which
is a `Result<(I, O), nom::Err<I, E>>`, so you know which patterns you need to
verify. If you need to call two parsers in a sequence, use the first parameter
of `Ok((i,o))`: It is the input remaining after the first parser was applied.

As an example, see how the `preceded!` macro works:

```rust
($i:expr, $submac:ident!( $($args:tt)* ), $submac2:ident!( $($args2:tt)* )) => (
    {
      match $submac!($i, $($args)*) {
        Err(e) => Err(e),
        Ok((i1, _)) => {
          $submac2!(i1, $($args2)*)
        },
      }
    }
  );
```

It applies the first parser, and if it succeeds, discards its result, and applies
the remaining input `i1` to the second parser.
