% FAQ

### The compiler indicates `error: expected an item keyword` then points to the function's return type in `named!`:

```ignore
error: expected an item keyword
named!(multi<Vec<&str>>, many0!( map_res!(tag!( "abcd" ), str::from_utf8) ) );
             ^~~
```

This happens because the macro processor mistakes `>>` for an operator. It will work correctly by adding a space, like this: `named!(multi< Vec<&str> >, ...`

### nom 1.0 does not compile on Rust older than 1.4

Typically, the error would look like this:

```ignore
src/stream.rs:74:44: 74:64 error: the parameter type `E` may not live long enough [E0309]
src/stream.rs:74     if let &ConsumerState::Done(_,ref o) = self.apply(consumer) {
                                                            ^~~~~~~~~~~~~~~~~~~~
note: in expansion of if let expansion
src/stream.rs:74:5: 78:6 note: expansion site
src/stream.rs:74:44: 74:64 help: run `rustc --explain E0309` to see a detailed explanation
src/stream.rs:74:44: 74:64 help: consider adding an explicit lifetime bound `E: 'b`...
src/stream.rs:74:44: 74:64 note: ...so that the reference type `&stream::ConsumerState<O, E, M>` does not outlive the data it points at
src/stream.rs:74     if let &ConsumerState::Done(_,ref o) = self.apply(consumer) {
                                                            ^~~~~~~~~~~~~~~~~~~~
note: in expansion of if let expansion
src/stream.rs:74:5: 78:6 note: expansion site
src/stream.rs:74:44: 74:64 error: the parameter type `M` may not live long enough [E0309]
src/stream.rs:74     if let &ConsumerState::Done(_,ref o) = self.apply(consumer) {
                                                            ^~~~~~~~~~~~~~~~~~~~
note: in expansion of if let expansion
src/stream.rs:74:5: 78:6 note: expansion site
src/stream.rs:74:44: 74:64 help: run `rustc --explain E0309` to see a detailed explanation
src/stream.rs:74:44: 74:64 help: consider adding an explicit lifetime bound `M: 'b`...
src/stream.rs:74:44: 74:64 note: ...so that the reference type `&stream::ConsumerState<O, E, M>` does not outlive the data it points at
src/stream.rs:74     if let &ConsumerState::Done(_,ref o) = self.apply(consumer) {
                                                            ^~~~~~~~~~~~~~~~~~~~
note: in expansion of if let expansion
src/stream.rs:74:5: 78:6 note: expansion site
error: aborting due to 2 previous errors

Could not compile `nom`.
```

This is caused by some lifetime issues that may be fixed in a future version of nom. In the meantime, you can add `default-features=false` to nom's declaration in `Cargo.toml` to deactivate this part of the code:

```toml
[dependencies.nom]
version = "~1.0.0"
default-features = false
```
