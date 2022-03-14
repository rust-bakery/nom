# FAQ

### Using nightly to get better error messages

**warning**: this only applies to nom 3. nom 4 uses the
[compile_error](https://doc.rust-lang.org/std/macro.compile_error.html) macro
available since Rust 1.20

If you got the following error when compiling your nom parser:

```
error[E0425]: cannot find value `INVALID_NOM_SYNTAX_PLEASE_SEE_FAQ` in this scope
   --> src/lib.rs:111:7
    |
111 |         INVALID_NOM_SYNTAX_PLEASE_SEE_FAQ //https://github.com/Geal/nom/blob/main/doc/archive/FAQ.md#using-nightly-to-get-better-error-messages
    |         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ not found in this scope
```

It means that you are using Rust stable, and that one of your nom parsers has an invalid syntax.
If you can switch to a nightly Rust compiler (as an example, with `rustup default nightly`),
and if you activate the `nightly` feature on your nom dependency like this:

```toml
[dependencies.nom]
version = "^3"
features = ["nightly"]
```

You can get more helpful error messages, such as this one:

```
$ cargo test --features nightly
   Compiling compiler_error v0.1.1
   Compiling nom v3.0.0 (file:///Users/geal/dev/rust/projects/nom)
error: "do_parse is missing the return value. A do_parse call must end
      with a return value between parenthesis, as follows:

      do_parse!(
        a: tag!(\"abcd\") >>
        b: tag!(\"efgh\") >>

        ( Value { a: a, b: b } )
    "
   --> src/sequence.rs:368:5
    |
368 | /     compiler_error!("do_parse is missing the return value. A do_parse call must end
369 | |       with a return value between parenthesis, as follows:
370 | |
371 | |       do_parse!(
...   |
375 | |         ( Value { a: a, b: b } )
376 | |     ");
    | |______^
...
851 | /         named!(no_compiler,
852 | |                 do_parse!(
853 | |                         length: be_u8         >>
854 | |                         bytes:  take!(length)
855 | |                 )
856 | |         );
    | |___- in this macro invocation

error: aborting due to previous error(s)

error: Could not compile `nom`.
```

If the error message is not helpful, please reach out on the [Gitter chat](https://gitter.im/Geal/nom?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge&utm_content=badge) or the IRC channel (#nom on freenode), and show
your code and the error message you got.

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

### The compiler indicates `error: expected an item keyword` then points to the function's return type in `named!`:

```ignore
error: expected an item keyword
named!(multi<Vec<&str>>, many0!( map_res!(tag!( "abcd" ), str::from_utf8) ) );
             ^~~
```

This happens because the macro processor mistakes `>>` for an operator. It will work correctly by adding a space, like this: `named!(multi< Vec<&str> >, ...`
