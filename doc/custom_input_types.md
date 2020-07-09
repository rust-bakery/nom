# Custom input types

While historically, nom has worked mainly on `&[u8]` and `&str`, it can actually
use any type as input, as long as they follow a specific set of traits.
Those traits were developed first to abstract away the differences between
`&[u8]` and `&str`, but were then employed for more interesting types,
like [nom_locate](https://github.com/fflorent/nom_locate), a wrapper type
that can carry line and column information, or to parse
[a list of tokens](https://github.com/Rydgel/monkey-rust/blob/master/lib/parser/mod.rs).

## Implementing a custom type

Let's assume we have an input type we'll call `MyInput`. `MyInput` is a sequence of `MyItem` type.
The goal is to define nom parsers with this signature: `MyInput -> IResult<MyInput, Output>`.

```rust
fn parser(i: MyInput) -> IResult<MyInput, Output> {
    tag("test")(i)
}
```

Here are the traits we have to implement for `MyInput`:

| trait | usage |
|---|---|
| [AsBytes](https://docs.rs/nom/latest/nom/trait.AsBytes.html) |Casts the input type to a byte slice|
| [Compare](https://docs.rs/nom/latest/nom/trait.Compare.html) |Character comparison operations|
| [ExtendInto](https://docs.rs/nom/latest/nom/trait.ExtendInto.html) |Abstracts something which can extend an `Extend`|
| [FindSubstring](https://docs.rs/nom/latest/nom/trait.FindSubstring.html) |Look for a substring in self|
| [FindToken](https://docs.rs/nom/latest/nom/trait.FindToken.html) |Look for self in the given input stream|
| [InputIter](https://docs.rs/nom/latest/nom/trait.InputIter.html) |Common iteration operations on the input type|
| [InputLength](https://docs.rs/nom/latest/nom/trait.InputLength.html) |Calculate the input length|
| [InputTake](https://docs.rs/nom/latest/nom/trait.InputTake.html) |Slicing operations|
| [InputTakeAtPosition](https://docs.rs/nom/latest/nom/trait.InputTakeAtPosition.html) |Look for a specific token and split at its position|
| [Offset](https://docs.rs/nom/latest/nom/trait.Offset.html) |Calculate the offset between slices|
| [ParseTo](https://docs.rs/nom/latest/nom/trait.ParseTo.html) |Used to integrate `&str`'s `parse()` method|
| [Slice](https://docs.rs/nom/latest/nom/trait.Slice.html) |Slicing operations using ranges|

Here are the traits we have to implement for `MyItem`:

| trait | usage |
|---|---|
| [AsChar](https://docs.rs/nom/latest/nom/trait.AsChar.html) |Transforms common types to a char for basic token parsing|
