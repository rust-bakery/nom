# Chapter 5: Repeating with Predicates

Just as, when programming, the humble while loop unlocks many useful
features; in Nom, repeating a parser multiple times can be incredibly useful

There are, however, two ways of including repeating functionality into Nom --
parsers which are governed by a predicate; and combinators which repeat
a parser.

## Parsers which use a predicate

A `predicate` is a function which returns a boolean value (i.e. given some input,
it returns `true` or `false`). These are incredibly common when parsing -- for instance,
a predicate `is_vowel` might decide whether a character is an english vowel (a, e, i, o or u).

These can be used to make parsers that Nom hasn't built in. For instance, the below
parser will take as many vowels as possible.

There are a few different categories of predicate parsers that are worth mentioning:

 - For bytes, there are three different categories of parser: `take_till`, `take_until`, and `take_while`.
 `take_till` will continue consuming input until its input meets the predicate.
 `take_while` will continue consuming input until its input *does not* meet the predicate.
 `take_until` looks a lot like a predicate parser, but simply consumes until the first
  occurence of the pattern of bytes.
 - Some parsers have a "twin" with a `1` at the end of their name -- for example, `take_while`
 has `take_while1`. The difference between them is that `take_while` could return an empty
 slice if the first byte does not satisfy a predicate. `take_while1` returns an error if
 the predicate is not met.
 - As a special case, `take_while_m_n` is like `take_while`, but guarantees that it will consume
 at least `m` bytes, and no more than `n` bytes.
 

```rust
# extern crate nom;
# use std::error::Error;
use nom::IResult;
use nom::bytes::complete::{tag, take_until, take_while};
use nom::character::{is_space};
use nom::sequence::{terminated};

fn parse_sentence(input: &str) -> IResult<&str, &str> {
    terminated(take_until("."), take_while(|c| c == '.' || c == ' '))(input)
}

fn main() -> Result<(), Box<dyn Error>> {
    let (remaining, parsed) = parse_sentence("I am Tom. I write Rust.")?;
    assert_eq!(parsed, "I am Tom");
    assert_eq!(remaining, "I write Rust.");
   
    let parsing_error = parse_sentence("Not a sentence (no period at the end)");
    assert!(parsing_error.is_err());
    

#   Ok(())
}
```
 For detailed examples, see their documentation, shown below:

| combinator | usage | input | output | comment |
|---|---|---|---|---|
 | [take_while](https://docs.rs/nom/latest/nom/bytes/complete/fn.take_while.html) | `take_while(is_alphabetic)` |  `"abc123"` | `Ok(("123", "abc"))` |Returns the longest list of bytes for which the provided function returns true. `take_while1` does the same, but must return at least one character. `take_while_m_n` does the same, but must return between `m` and `n` characters.|
| [take_till](https://docs.rs/nom/latest/nom/bytes/complete/fn.take_till.html) | `take_till(is_alphabetic)` |  `"123abc"` | `Ok(("abc", "123"))` |Returns the longest list of bytes or characters until the provided function returns true. `take_till1` does the same, but must return at least one character. This is the reverse behaviour from `take_while`: `take_till(f)` is equivalent to `take_while(\|c\| !f(c))`|
| [take_until](https://docs.rs/nom/latest/nom/bytes/complete/fn.take_until.html) | `take_until("world")` |  `"Hello world"` | `Ok(("world", "Hello "))` |Returns the longest list of bytes or characters until the provided tag is found. `take_until1` does the same, but must return at least one character|
