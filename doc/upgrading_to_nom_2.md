% Upgrading to nom 2.0

The 2.0 release of nom adds a lot of new features, but it was also time for a big cleanup of badly named functions and macros, awkwardly written features and redundant functionality. So this release has some breaking changes, but most of them are harmless.

# Simple VS verbose errors

```ignore
error: no associated item named `Code` found for type `nom::ErrorKind<_>` in the current scope
   --> src/metadata/parser.rs:309:31
    |
309 |     _       => IResult::Error(Err::Code(
    |                               ^^^^^^^^^

error: no associated item named `Code` found for type `nom::ErrorKind<_>` in the current scope
   --> src/metadata/parser.rs:388:41
    |
388 |     let result_invalid = IResult::Error(Err::Code(nom::ErrorKind::Custom(
    |                                         ^^^^^^^^^

error: no associated item named `Position` found for type `nom::ErrorKind<_>` in the current scope
  --> src/utility/macros.rs:16:41
   |
16 |             $crate::nom::IResult::Error($crate::nom::Err::Position(
   |                                         ^^^^^^^^^^^^^^^^^^^^^^^^^^
   |
  ::: src/metadata/parser.rs
   |
178|     bytes: skip_bytes!(14, 2) ~
   |                      - in this macro invocation

error: no associated item named `Position` found for type `nom::ErrorKind<_>` in the current scope
   --> src/utility/macros.rs:16:41
    |
16  |             $crate::nom::IResult::Error($crate::nom::Err::Position(
    |                                         ^^^^^^^^^^^^^^^^^^^^^^^^^^
    |
   ::: src/metadata/parser.rs
    |
201 |     skip_bytes!(3),
    |               - in this macro invocation
```

```diff
-nom             = "^1.0.0"
nom             = { version = "^2.0.0", features = ["verbose-errors"] }
```

If you only use `Err::Code`, you could switch to the simple errors, since it replaces the `Err` enum with `ErrorKind`.

# the eof function was removed

```ìgnore
error[E0432]: unresolved import `nom::eof`
 --> src/parser.rs:1:20
  |
1 | use nom::{IResult, eof, line_ending, not_line_ending, space};
  |                    ^^^ no `eof` in `nom`. Did you mean to use `eol`?
```

The `eof` function was replaced by the `eof!` macro to make it easier to adapt to new input types.

# parsers returning `Incomplete` instead of an error on empty input

`alpha`, `digit`, `alphanumeric`, `hex_digit`, `oct_digit`, `space`, `multispace`, `sized_buffer` will now return `Incomplete` if they get an empty input. If you get the following error message, you can wrap those calls with `complete!`, a combinator that transforms `Incomplete` to `Error`.

```
---- rules::literals::tests::case_invalid_hexadecimal_no_number stdout ----
        thread 'rules::literals::tests::case_invalid_hexadecimal_no_number' panicked at 'assertion failed: `(left == right)` (left: `Incomplete(Unknown)`, right: `Error(Position(HexDigit, []))`)', source/rules/literals.rs:726
```

# `take_till!` iterates on bytes or chars, not on references to them

```ignore
error[E0308]: mismatched types
  --> src/linux/parser.rs:32:1
   |
32 | named!(parse_c_string, take_till!(is_nul_byte));
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ expected &u8, found u8
   |
   = note: expected type `&u8`
   = note:    found type `u8`
   = note: this error originates in a macro outside of the current crate
```

fix with:

```diff
-fn is_nul_byte(c: &u8) -> bool {
-    *c == 0x0
+fn is_nul_byte(c: u8) -> bool {
+    c == 0x0
```

# length_value, length_bytes refactoring

The "length-value" pattern usually indicates that we get a length from the input, then take a slice of that size from the input, and convert that to a value of the type we need. The `length_value!` macro was using the length parameter to apply the value parser a specific number of times.

- the `length_value!` macro was replaced by `length_count!`
- the new `length_value!` macros takes a slice of the size obtained by the first child parser, then applies the second child parser on this slice. If the second parser returns incomplete, the parser fails
- `length_data!` gets a length from its child parser, then returns a subslice of that length

```ignore
error[E0308]: mismatched types
   --> src/tls.rs:378:37
    |
378 |                         cert_types: cert_types,
    |                                     ^^^^^^^^^^ expected struct `std::vec::Vec`, found u8
    |
    = note: expected type `std::vec::Vec<u8>`
    = note:    found type `u8`
```

```diff
 fn parse_tls_handshake_msg_certificaterequest( i:&[u8] ) -> IResult<&[u8], TlsMessageHandshake> {
     chain!(i,
-        cert_types: length_value!(be_u8,be_u8) ~
+        cert_types: length_count!(be_u8,be_u8) ~
         sig_hash_algs_len: be_u16 ~
```

# error! does not exist anymore

it has been replaced with return_error

```
error: macro undefined: 'error!'
   --> src/parser.rs:205:10
    |
205 |     error!(Custom(ParseError::InvalidData),
    |          ^
```

```diff
 named!(repeat<&str, u8, ParseError>,
-       error!(Custom(ParseError::RepeatNotNumeric), fix!(
+       return_error!(Custom(ParseError::RepeatNotNumeric), fix!(
        map_res!(flat_map!(take_s!(1), digit), FromStr::from_str))));
```

# the `offset()` method was moved to the `Offset` trait

There is now an implementation of `Offset` for `&str`. The `HexDisplay` trait is now reserved for `&[u8]`.

# `AsChar::is_0_to_9` is now `AsChar::is_dec_digit`

# the number parsing macros with configurable endianness now take an enum as argument instead of a boolean

Using a boolean was confusing, there is now the `nom::Endianness` enum:

```diff
-    named!(be_tst32<u32>, u32!(true));
-    named!(le_tst32<u32>, u32!(false));
+    named!(be_tst32<u32>, u32!(Endianness::Big));
+    named!(le_tst32<u32>, u32!(Endianness::Little));
```

# end of line parsing

There were different, incompatible ways to parse line endings. Now, the `eol`, `line_ending` and `not_line_ending` all have the same behaviour. First, test for '\n', then if it is not the right character, test for "\r\n". This fixes the length issues.
