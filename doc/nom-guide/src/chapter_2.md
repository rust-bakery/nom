# Chapter 2: Tags and Character Classes

The simplest _useful_ parser you can write is one which
has no special characters, it just matches a string.

In `nom`, we call a simple collection of bytes a tag. Because
these are so common, there already exists a function called `tag()`.
This function returns a parser for a given string.

 **Warning**: `nom` has multiple different definitions of `tag`, make sure you use this one for the
 moment!

```rust,ignore
# extern crate nom;
pub use nom::bytes::complete::tag;
```

For example, code to parse the string `"abc"` could be represented as `tag("abc")`.

If you have not programmed in a language where functions are values, the type signature of them
tag function might be a surprise:

```rust,ignore
pub fn tag<T, Input, Error: ParseError<Input>>(
    tag: T
) -> impl Fn(Input) -> IResult<Input, Input, Error> where
    Input: InputTake + Compare<T>,
    T: InputLength + Clone, 
```

Or, for the case where `Input` and `T` are both `&str`, and simplifying slightly:

```rust,ignore
fn tag(tag: &str) -> (impl Fn(&str) -> IResult<&str, Error>)
```

In other words, this function `tag` *returns a function*. The function it returns is a
parser, taking a `&str` and returning an `IResult`. Functions creating parsers and 
returning them is a common pattern in Nom, so it is useful to call out.

Below, we have implemented a function that uses `tag`.

```rust
# extern crate nom;
# pub use nom::bytes::complete::tag;
# pub use nom::IResult;
# use std::error::Error;

fn parse_input(input: &str) -> IResult<&str, &str> {
    //  note that this is really creating a function, the parser for abc
    //  vvvvv 
    //         which is then called here, returning an IResult<&str, &str>
    //         vvvvv
    tag("abc")(input)
}

fn main() -> Result<(), Box<dyn Error>> {
    let (leftover_input, output) = parse_input("abcWorld")?;
    assert_eq!(leftover_input, "World");
    assert_eq!(output, "abc");

    assert!(parse_input("defWorld").is_err());
#   Ok(())
}
```

If you'd like to, you can also check tags without case-sensitivity
with the [`tag_no_case`](https://docs.rs/nom/latest/nom/bytes/complete/fn.tag_no_case.html) function.

## Character Classes

Tags are incredibly useful, but they are also incredibly restrictive.
The other end of Nom's functionality is pre-written parsers that allow us to accept any of a group of characters,
rather than just accepting characters in a defined sequence.

Here is a selection of them:

- [`alpha0`](https://docs.rs/nom/latest/nom/character/complete/fn.alpha0.html): Recognizes zero or more lowercase and uppercase alphabetic characters: `/[a-zA-Z]/`. [`alpha1`](https://docs.rs/nom/latest/nom/character/complete/fn.alpha1.html) does the same but returns at least one character
- [`alphanumeric0`](https://docs.rs/nom/latest/nom/character/complete/fn.alphanumeric0.html): Recognizes zero or more numerical and alphabetic characters: `/[0-9a-zA-Z]/`. [`alphanumeric1`](https://docs.rs/nom/latest/nom/character/complete/fn.alphanumeric1.html) does the same but returns at least one character
- [`digit0`](https://docs.rs/nom/latest/nom/character/complete/fn.digit0.html): Recognizes zero or more numerical characters: `/[0-9]/`. [`digit1`](https://docs.rs/nom/latest/nom/character/complete/fn.digit1.html) does the same but returns at least one character
- [`multispace0`](https://docs.rs/nom/latest/nom/character/complete/fn.multispace0.html): Recognizes zero or more spaces, tabs, carriage returns and line feeds. [`multispace1`](https://docs.rs/nom/latest/nom/character/complete/fn.multispace1.html) does the same but returns at least one character
- [`space0`](https://docs.rs/nom/latest/nom/character/complete/fn.space0.html): Recognizes zero or more spaces and tabs. [`space1`](https://docs.rs/nom/latest/nom/character/complete/fn.space1.html) does the same but returns at least one character
- [`line_ending`](https://docs.rs/nom/latest/nom/character/complete/fn.line_ending.html): Recognizes an end of line (both `\n` and `\r\n`)
- [`newline`](https://docs.rs/nom/latest/nom/character/complete/fn.newline.html): Matches a newline character `\n`
- [`tab`](https://docs.rs/nom/latest/nom/character/complete/fn.tab.html): Matches a tab character `\t`


We can use these in
```rust
# extern crate nom;
# pub use nom::IResult;
# use std::error::Error;
pub use nom::character::complete::alpha0;
fn parser(input: &str) -> IResult<&str, &str> {
    alpha0(input)
}

fn main() -> Result<(), Box<dyn Error>> {
    let (remaining, letters) = parser("abc123")?;
    assert_eq!(remaining, "123");
    assert_eq!(letters, "abc");
    
#   Ok(())
}
```

One important note is that, due to the type signature of these functions,
it is generally best to use them within a function that returns an `IResult`.

If you don't, some of the information around the type of the `tag` function must be
manually specified, which can lead to verbose code or confusing errors.
