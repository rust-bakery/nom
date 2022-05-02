# Chapter 1: The Nom Way

First of all, we need to understand the way that regexes and nom think about
parsing.

A regex, in a sense, controls its whole input. Given a single input,
it decides that either some text **did** match the regex, or it **didn't**.

```text
             ┌────────┐           ┌─► Some text that matched the regex
 my input───►│my regex├──►either──┤
             └────────┘           └─► None
```

As we mentioned above, Nom parsers are designed to be combined.
This makes the assumption that a regex controls its entire input
more difficult to maintain. So, there are three important changes
required to our mental model of a regex.

1. Rather than just returning the text that matched
   the regex, Nom tells you *both* what it parsed, and what is left
   to parse.

2. Additionally, to help with combining parsers, Nom also gives you
   error information about your parser. We'll talk about this more later,
   for now let's assume it's "basically" the same as the `None` we have above.

   Points 1 and 2 are illustrated in the diagram below:

```text
                                   ┌─► Ok(
                                   │      text that the parser didn't touch,
                                   │      text that matched the regex
                                   │   )
             ┌─────────┐           │
 my input───►│my parser├──►either──┤
             └─────────┘           └─► Err(...)
```

3. Lastly, Nom parsers are normally anchored to the beginning of their input.
   In other words, if you converted a Nom parser to regex, it would generally
   begin with `/^/`. This is sensible, because it means that nom parsers must
   (conceptually) be sequential -- your parser isn't going to jump
   ahead and start parsing the middle of the line.


To represent this model of the world, nom uses the `IResult<(I, O)>` type.
The `Ok` variant has a tuple of `(remaining_input: I, output: O)`;
The `Err` variant stores an error. You can import that from:

```rust
# extern crate nom;
use nom::IResult;
```

The simplest parser we can write is one which successfully does nothing.
In other words, the regex `/^/`.

This parser should take in an `&str`.
    - Since it is supposed to succeed, we know it will return the Ok Variant.
    - Since it does nothing to our input, the remaining input is the same as the input.
    - Since it doesn't do anything, it also should just return the unit type.


In other words, this code should be equivalent to the regex `/^/`.

```rust
# extern crate nom;
# use nom::IResult;

pub fn do_nothing_parser(input: &str) -> IResult<&str, ()> {
    Ok((input, ()))
}

match do_nothing_parser("my_input") {
    Ok((remaining_input, output)) => {
        assert_eq!(remaining_input, "my_input");
        assert_eq!(output, ());
    },
    Err(_) => unreachable!()
}
```
