Hello, and thank you for submitting an issue to nom!


First, please note that, for family reasons, I have limited time to work on
nom, so following the advice here will make sure I will quickly understand
your problem and answer as soon as possible.
Second, if I don't get to work on your issue quickly, that does not mean I
don't consider it important or useful. Major version releases happen once
a year, and a lot of fixes are done for the occasion, once I have had time
to think of the right solution. So I will get back to you :)

## Prerequisites

Here are a few things you should provide to help me understand the issue:

- Rust version : `rustc -V`
- nom version :
- nom compilation features used:

## Test case

Please provide a short, complete (with crate import, etc) test case for
the issue, showing clearly the expected and obtained results.

Example test case:

```
#[macro_use]
extern crate nom;

named!(multi<&[u8], Vec<&[u8]> >, many1!( tag!( "abcd" ) ) );

let a = b"abcdabcd";

fn main() {
  let res = vec![&b"abcd"[..], &b"abcd"[..]];
  assert_eq!(multi(&a[..]),Ok((&b""[..], res))); // returns Err::Incomplete(Unknown))
}
```

