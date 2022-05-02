# Chapter 2: Tags and Character Classes

The simplest _useful_ regex you can write is one which
has no special characters, it just matches a string.

Imagine, for example, the regex `/abc/`. It simply matches when the string
`"abc"` occurs.

In `nom`, we call a simple collection of bytes a tag. Because
these are so common, there already exists a function called `tag()`.
This function returns a parser for a given string.

<div class="example-wrap" style="display:inline-block"><pre class="compile_fail" style="white-space:normal;font:inherit;">
 **Warning**: `nom` has multiple different definitions of `tag`, make sure you use this one for the
 moment!
</pre></div>

```rust
# extern crate nom;
pub use nom::bytes::complete::tag;
```

For example, the regex `/abc/` (really, the regex `/^abc/`)
could be represented as `tag("abc")`.

Note, that the function `tag` will return
another function, namely, a parser for the tag you requested.

Below, we see a function using this:

```rust
# extern crate nom;
# pub use nom::bytes::complete::tag;
# pub use nom::IResult;

fn parse_input(input: &str) -> IResult<&str, &str> {
    //  note that this is really creating a function, the parser for abc
    //  vvvvv 
    //         which is then called here, returning an IResult<&str, &str>
    //         vvvvv
    tag("abc")(input)
}

    let ok_input = "abcWorld";

    match parse_input(ok_input) {
        Ok((leftover_input, output)) => {
            assert_eq!(leftover_input, "World");
            assert_eq!(output, "abc");
        },
        Err(_) => unreachable!()
    }

    let err_input = "defWorld";
    match parse_input(err_input) {
        Ok((leftover_input, output)) => unreachable!(),
        Err(_) => assert!(true),
    }
```

If you'd like to, you can also check case insensitive `/tag/i`
with the `tag_case_insensitive`.

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
pub use nom::character::complete::alpha0;
fn parser(input: &str) -> IResult<&str, &str> {
    alpha0(input)
}

    let ok_input = "abc123";
    match parser(ok_input) {
        Ok((remaining, letters)) => {
            assert_eq!(remaining, "123");
            assert_eq!(letters, "abc");
        },
        Err(_) => unreachable!()
    }

```

One important note is that, due to the type signature of these functions,
it is generally best to use them within a function that returns an `IResult`.

*TODO* : Better explaination of why.
