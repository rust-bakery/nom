# Custom input types

While historically, nom has worked mainly on `&[u8]` and `&str`, it can actually
use any type as input, as long as they follow a specific set of traits.
Those traits were developed first to abstract away the differences between
`&[u8]` and `&str`, but were then employed for more interesting types,
like [nom_locate](https://github.com/fflorent/nom_locate), a wrapper type
that can carry line and column information, or to parse
[a list of tokens](https://github.com/Rydgel/monkey-rust/blob/master/lib/parser/mod.rs).

## Implementing a custom type

Let's assume we have an input type we'll call `MyInput`. The goal is to define
nom parsers with this signature: `MyInput -> IResult<MyInput, Output>`.
To employ it in a `named!` parser, you can write it like this:

```rust
named!(parser<MyInput, Output>, tag!("test"));
```

Here are the traits we have to implement:


| trait | usage |
|---|---|
| [AsBytes](https://docs.rs/nom/latest/nom/trait.AsBytes.html) | casts the input type to a byte slice |
| [AsChar](https://docs.rs/nom/latest/nom/trait.AsChar.html) | transforms common types to a char for basic token parsing |
| [Compare](https://docs.rs/nom/latest/nom/trait.Compare.html) | character comparison operations |
| [ExtendInto](https://docs.rs/nom/latest/nom/trait.ExtendInto.html) |abstracts something which can extend an Extend |
| [FindSubstring](https://docs.rs/nom/latest/nom/trait.FindSubstring.html) | look for a substring in self |
| [FindToken](https://docs.rs/nom/latest/nom/trait.FindToken.html) |look for self in the given input stream |
| [InputIter](https://docs.rs/nom/latest/nom/trait.InputIter.html) | common iteration operations on the input type |
| [InputLength](https://docs.rs/nom/latest/nom/trait.InputLength.html) | calculate the input length |
| [InputTake](https://docs.rs/nom/latest/nom/trait.InputTake.html) | slicing operations |
| [InputTakeAtPosition](https://docs.rs/nom/latest/nom/trait.InputTakeAtPosition.html) | look for a specific token and split at its position |
| [Offset](https://docs.rs/nom/latest/nom/trait.Offset.html) | calculate the offset between slices |
| [ParseTo](https://docs.rs/nom/latest/nom/trait.ParseTo.html) | used to integrate `&str`'s parse() method |
| [Slice](https://docs.rs/nom/latest/nom/trait.Slice.html) | slicing operations using ranges |
