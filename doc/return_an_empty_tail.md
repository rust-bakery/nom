A lot of nom parser use a trait call [`Offset`](https://docs.rs/nom/7.0.0/nom/trait.Offset.html), it has specific requirement such as:

* The origin of `Self` must be the same, bad example:
  ```rust
  use nom::Offset;

  fn main() {
    let input = &[];
    println!("{}", input.offset(&[])); // unspecified behavior
  }
  ```
  In Rust, nothing guarantie that two `&[]` is the same array so you can't do that. The correct code should be `input.offset(input)`.

* The second parameter must be "same or after" `self`, bad example:
  ```rust
  use nom::Offset;

  fn main() {
    let input = &[0, 1, 2, 3];
    let bad_origin = &input[2..];
    println!("{}", bad_origin.offset(input)); // will overflow usize::MAX - 1 on this case
  }
  ```

This mean when you made a parser you **SHOULD** return a tail related to your input even if you want to return an empty tail for example:

```rust
use nom::{Offset, IResult};

fn consume_all(input: &[u8]) -> IResult<&[u8], ()> {
  Ok((&input[input.len()..], ())) // This return an empty slice but related to input
}

fn main() {
  let input = &[0, 1, 2, 3];
  let (tail, _) = consume_all(input).unwrap();
  assert_eq!(input.offset(tail), 4); // expected behavior
}
```

This will prevent [Issues#1424](https://github.com/Geal/nom/issues/1424)