# Chapter 1: The Nom Way

First of all, we need to understand the way that nom thinks about parsing.
As discussed in the introduction, nom lets us build simple parsers, and
then combine them (using "combinators").

Let's discuss what a "parser" actually does. A parser takes an input and returns
a result, where:
 - `Ok` indicates the parser successfully found what it was looking for; or
 - `Err` indicates the parser could not find what it was looking for.
 
Parsers do more than just return a binary "success"/"failure" code. If
the parser was successful, then it will return a tuple. The first field of the
tuple will contain everything the parser did not process. The second will contain
everything the parser processed. The idea is that a parser can happily parse the first
*part* of an input, without being able to parse the whole thing.

If the parser failed, then there are multiple errors that could be returned.
For simplicity, however, in the next chapters we will leave these unexplored.

```text
                                   ┌─► Ok(
                                   │      what the parser didn't touch,
                                   │      what matched the regex
                                   │   )
             ┌─────────┐           │
 my input───►│my parser├──►either──┤
             └─────────┘           └─► Err(...)
```


To represent this model of the world, nom uses the `IResult<I, O>` type.
The `Ok` variant has a tuple of `(remaining_input: I, output: O)`;
whereas the `Err` variant stores an error.

You can import that from:

```rust
# extern crate nom;
use nom::IResult;
```

You'll note that `I` and `O` are parameterized -- while most of the examples in this book
will be with `&str` (i.e. parsing a string); they do not have to be strings; nor do they
have to be the same type (consider the simple example where `I = &str`, and `O = u64` -- this
parses a string into an unsigned integer.)

Let's write our first parser!
The simplest parser we can write is one which successfully does nothing.

This parser should take in an `&str`:

 - Since it is supposed to succeed, we know it will return the Ok Variant.
 - Since it does nothing to our input, the remaining input is the same as the input.
 - Since it doesn't parse anything, it also should just return an empty string.


```rust
# extern crate nom;
# use nom::IResult;
# use std::error::Error;

pub fn do_nothing_parser(input: &str) -> IResult<&str, &str> {
    Ok((input, ""))
}

fn main() -> Result<(), Box<dyn Error>> {
    let (remaining_input, output) = do_nothing_parser("my_input")?;
    assert_eq!(remaining_input, "my_input");
    assert_eq!(output, "");
#   Ok(())
}
```

It's that easy!
