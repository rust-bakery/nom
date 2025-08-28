# Chapter 6: Repeating Parsers

A single parser which repeats a predicate is useful, but more useful still is a combinator that
repeats a parser. Nom has multiple combinators which operate on this principle; the most obvious of
which is `many0`, which applies a parser as many times as possible; and returns a vector of
the results of those parses. Here is an example:

```rust
# extern crate nom;
# use std::error::Error;
use nom::IResult;
use nom::multi::many0;
use nom::bytes::complete::tag;

fn parser(s: &str) -> IResult<&str, Vec<&str>> {
  many0(tag("abc"))(s)
}

fn main() {
    assert_eq!(parser("abcabc"), Ok(("", vec!["abc", "abc"])));
    assert_eq!(parser("abc123"), Ok(("123", vec!["abc"])));
    assert_eq!(parser("123123"), Ok(("123123", vec![])));
    assert_eq!(parser(""), Ok(("", vec![])));
}
```

There are many different parsers to choose from:

| combinator | usage | input | output | comment |
|---|---|---|---|---|
| [count](https://docs.rs/nom/latest/nom/multi/fn.count.html) | `count(take(2), 3)` | `"abcdefgh"` | `Ok(("gh", vec!["ab", "cd", "ef"]))` |Applies the child parser a specified number of times|
| [many0](https://docs.rs/nom/latest/nom/multi/fn.many0.html) | `many0(tag("ab"))` |  `"abababc"` | `Ok(("c", vec!["ab", "ab", "ab"]))` |Applies the parser 0 or more times and returns the list of results in a Vec. `many1` does the same operation but must return at least one element|
| [many_m_n](https://docs.rs/nom/latest/nom/multi/fn.many_m_n.html) | `many_m_n(1, 3, tag("ab"))` | `"ababc"` | `Ok(("c", vec!["ab", "ab"]))` |Applies the parser between m and n times (n included) and returns the list of results in a Vec|
| [many_till](https://docs.rs/nom/latest/nom/multi/fn.many_till.html) | `many_till(tag( "ab" ), tag( "ef" ))` | `"ababefg"` | `Ok(("g", (vec!["ab", "ab"], "ef")))` |Applies the first parser until the second applies. Returns a tuple containing the list of results from the first in a Vec and the result of the second|
| [separated_list0](https://docs.rs/nom/latest/nom/multi/fn.separated_list0.html) | `separated_list0(tag(","), tag("ab"))` | `"ab,ab,ab."` | `Ok((".", vec!["ab", "ab", "ab"]))` |`separated_list1` works like `separated_list0` but must returns at least one element|
| [fold_many0](https://docs.rs/nom/latest/nom/multi/fn.fold_many0.html) | `fold_many0(be_u8, \|\| 0, \|acc, item\| acc + item)` | `[1, 2, 3]` | `Ok(([], 6))` |Applies the parser 0 or more times and folds the list of return values. The `fold_many1` version must apply the child parser at least one time|
| [fold_many_m_n](https://docs.rs/nom/latest/nom/multi/fn.fold_many_m_n.html) | `fold_many_m_n(1, 2, be_u8, \|\| 0, \|acc, item\| acc + item)` | `[1, 2, 3]` | `Ok(([3], 3))` |Applies the parser between m and n times (n included) and folds the list of return value|
| [length_count](https://docs.rs/nom/latest/nom/multi/fn.length_count.html) | `length_count(number, tag("ab"))` | `"2ababab"` | `Ok(("ab", vec!["ab", "ab"]))` |Gets a number from the first parser, then applies the second parser that many times|

