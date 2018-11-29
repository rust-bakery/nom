% Error management

# Error management

Parser combinators are useful tools to build parsers, but they are notoriously bad at error reporting. This happens because a tree of parser acts as a single parser, and the only error you get will come from the root parser.

This is especially annoying while developing, since you cannot know which parser failed, and why.

Nom provides a few tools to help you in reporting errors and debugging parsers.

## Debugging macros

There are two macros that you can use to check what is happening while you write your parsers: `dbg!` and `dbg_dmp!`.

They take a parser or combinator as input and, if it returns an `Error` or `Incomplete`, will print the result and the parser passed as argument. It will return the result unmodified, so it can be added and removed from your parser without any impact.

```rust
#[macro_use] extern crate nom;

fn main() {
  named!(f, dbg!( tag!( "abcd" ) ) );

  let a = &b"efgh"[..];
  f(a);
}
```

Result:

```ignore
Error(Position(0, [101, 102, 103, 104])) at l.5 by " tag ! ( "abcd" ) "
```

The result sent by `dbg_dmp!` is slightly different:

```rust
#[macro_use] extern crate nom;

fn main() {
  named!(f, dbg_dmp!( tag!( "abcd" ) ) );

  let a = &b"efghijkl"[..];
  f(a);
}
```

It will print, along with the result and the parser, a hexdump of the input buffer passed to the parser.

```ignore
Error(Position(0, [101, 102, 103, 104, 105, 106, 107, 108])) at l.5 by " tag ! ( "abcd" ) "
00000000        65 66 67 68 69 6a 6b 6c         efghijkl
```

## Error reporting

As a reminder, here are the basic types of nom:

```ignore
pub type IResult<I, O, E = u32> = Result<(I, O), Err<I, E>>;
#[derive(Debug,PartialEq,Eq,CLone,Copy)]
pub enum Needed {
  Unknown,
  Size(u32)
}

#[derive(Debug, Clone, PartialEq)]
pub enum Err<I, E = u32> {
  Incomplete(Needed),
  Error(Context<I, E>),
  Failure(Context<I, E>),
}

#[derive(Debug,PartialEq,Eq,Clone)]
pub enum Err<P,E=u32>{
  Code(ErrorKind<E>),
  Node(ErrorKind<E>, Box<Err<P,E>>),
  Position(ErrorKind<E>, P),
  NodePosition(ErrorKind<E>, P, Box<Err<P,E>>)
}

#[derive(Debug,PartialEq,Eq)]
pub enum IResult<I,O,E=u32> {
  Done(I,O),
  Error(Err<I,E>),
  Incomplete(Needed)
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Context<I, E = u32> {
  Code(I, ErrorKind<E>),
  /// only available if the compilation feature `verbose-errors` is active
  List(Vec<(I, ErrorKind<E>)>),
}
```

An error in nom can be either:
- an `ErrorKind<E>` error code
- an `ErrorKind<E>` error code and a pointer to the next error
- an `ErrorKind<E>` error code and an input slice
- an `ErrorKind<E>` error code, an input slice and a pointer to the next error

`E` is the custom error type you can provide. Otherwise, it is an `u32` by default.
If you need more information on the errors, or want to act on them in the calling code you can use the `return_error!` combinator. It takes an `ErrorKind<E>` error code and a parser as argument. If the child parser returns an error, it will wrap it in another error (a `NodePosition`) with its own error code, and return it directly.

### Adding an error

Sometimes, you want to provide an error code at a specific point in the parser tree. The `add_return_error!` macro can be used for this:

```ignore
# #[macro_use] extern crate nom;
# use nom::ErrorKind;
# use nom::Err::*;
# use nom::IResult::Error;
named!(err_test,
  preceded!(tag!("efgh"), add_return_error!(ErrorKind::Custom(42),
      do_parse!(
             tag!("ijkl")                                     >>
        res: add_return_error!(ErrorKind::Custom(128), tag!("mnop")) >>
        (res)
      )
    )
));

# fn main() {
let a = &b"efghblah"[..];
let blah = &b"blah"[..];

let res_a = err_test(a);
assert_eq!(res_a, Error(NodePosition(ErrorKind::Custom(42), blah, Box::new(Position(ErrorKind::Tag, blah)))));
# }
```

If the child parser returns an error, `add_return_error!` will add its own at the head of the error chain.

### Early returns

This macro does an **early return**: it will not pass the error to the parent parser like other combinators, but will directly do a `return`, thus exiting the function. It works a bit like the "cut" operator in Prolog, in that there is no backtracking.

If another `return_error!` call is present in the parent parsing chain, it will intercept the previously returned error, and wrap it with its own error code.

Here is how it works in practice:

```ignore
# #[macro_use] extern crate nom;
# use nom::ErrorKind;
# use nom::IResult::Error;
# use nom::Err::*;
named!(err_test, alt!(
  tag!("abcd") |
  preceded!(
    tag!("efgh"),
    return_error!(
      ErrorKind::Custom(42),
      do_parse!(
             tag!("ijkl")              >>
        res: return_error!(ErrorKind::Custom(128), tag!("mnop")) >>
        (res)
      )
    )
  )
));

# fn main() {
let a = &b"efghblah"[..];
let b = &b"efghijklblah"[..];


let blah = &b"blah"[..];

let res_a = err_test(a);
let res_b = err_test(b);

assert_eq!(res_a, Error(NodePosition(ErrorKind::Custom(42), blah, Box::new(Position(ErrorKind::Custom(0), blah)))));
assert_eq!(res_b, Error(
  NodePosition(ErrorKind::Custom(42), &b"ijklblah"[..],
    Box::new(NodePosition(ErrorKind::Custom(128), blah,
      Box::new(Position(ErrorKind::Custom(0), blah))
    ))
  )
));
# }
```

With this mechanism, you get a chain of error codes and the corresponding positions in the input slice. If the `return_error!`calls are strategically placed, they can give a lot of information about what happened during parsing.

## Error pattern matching

Once you get a chain of errors with easily identifying codes, you probably want to match on these to provide useful error messages. This is the intended use of nom's error types.

### Simple matching

The `error_to_list` function can gather all of the error codes in a vector. This vector is essentially a signature of the parsing path and will let you distinguish between the different parsing errors.

```ignore
# #[macro_use] extern crate nom;
use nom::{Err,ErrorKind,error_to_list};

fn error_to_string<P>(e: &Err<P>) -> &'static str {
  let v:Vec<ErrorKind> = error_to_list(e);
  if &v[..] == [ErrorKind::Custom(42),ErrorKind::Tag] {
    "missing `ijkl` tag"
  } else if &v[..] == [ErrorKind::Custom(42), ErrorKind::Custom(128), ErrorKind::Tag] {
    "missing `mnop` tag after `ijkl`"
  } else {
    "unrecognized error"
  }
}

# fn main() {}
```

### With slice patterns

If you can use the *slice patterns* feature, you can easily match on errors this way:

```ignore
#![feature(slice_patterns)]
# #[macro_use] extern crate nom;
use nom::{Err,ErrorKind,error_to_list};

fn error_to_string<P>(e: &Err<P>) -> &'static str {
  let v:Vec<ErrorKind> = error_to_list(e);
  match &v[..] {
    [ErrorKind::Custom(42),ErrorKind::Tag]       => "missing `ijkl` tag",
    [ErrorKind::Custom(42), ErrorKind::Custom(128), ErrorKind::Tag] => "missing `mnop` tag after `ijkl`",
    _            => "unrecognized error"
  }
}
# fn main() {}
```

### With box patterns

If you can use box patterns, you can match directly on the error instead of filtering with `error_to_list`.

```ignore
#![feature(box_patterns)]
# #[macro_use] extern crate nom;
# use nom::{add_error_pattern, error_to_list};
# use nom::Err::*;
# use nom::ErrorKind;

use std::str;
fn error_to_string<P>(e:Err<P>) -> String
  match e {
    NodePosition(ErrorKind::Custom(42), i1, box Position(ErrorKind::Tag, i2)) => {
      format!("missing `ijkl` tag, found '{}' instead", str::from_utf8(i2).unwrap())
    },
     NodePosition(ErrorKind::Custom(42), i1, box NodePosition(ErrorKind::Custom(128), i2,  box Position(ErrorKind::Tag, i3))) => {
      format!("missing `mnop` tag after `ijkl`, found '{}' instead", str::from_utf8(i3).unwrap())
    },
    _ => "unrecognized error".to_string()
  }
}
```

### Merr pattern matching

This error reporting approach comes from the [Merr](https://github.com/pippijn/merr) library in Ocaml. Its basic idea is that if you match directly on the error codes to generate error messages, you will have to constantly update the matching code when you modify the grammar. So, instead of matching on static code lists (like the solutions above), you generate those lists from known wrong inputs, and associate them with the corresponding messages.

To do this in nom, you use the `add_error_pattern` function:

```ignore
fn add_error_pattern<'a,I,O>(h: &mut HashMap<Vec<ErrorKind>, &'a str>, res: IResult<I,O>, message: &'a str) -> bool
```

It takes as argument a mutable hashmap that will contain the correspondance between error code lists and error messages, an error, and an error message.

To use it, you fill up the hashmap, before parsing, with know bad inputs (if you work with binary data, the `include_bytes!` macro might help you there). Then you can just get the error by passing the result of `error_to_list!` as key of the hashmap. 

```ignore
# #[macro_use] extern crate nom;
use nom::{add_error_pattern, error_to_list};
use nom::IResult;

# fn main() {
let mut err_map = collections::HashMap::new();
add_error_pattern(
  &mut err_map,
  err_test(&b"efghpouet"[..]),
  "missing `ijkl` tag"
);

add_error_pattern(
  &mut err_map,
  err_test(&b"efghijklpouet"[..]),
  "missing `mnop` tag after `ijkl`"
);

if let IResult::Error(e) = err_test(&b"efghblah"[..]) {
  assert_eq!(err_map.get(&error_to_list(e)), Some(&"missing `ijkl` tag"));
};

if let IResult::Error(e) = err_test(&b"efghijklblah"[..]) {
  assert_eq!(err_map.get(&error_to_list(e)), Some(&"missing `mnop` tag after `ijkl`"));
};
# }
```

## Colored hexdump

To help in format discovery, visual tools can sometimes help. The error chain system gives a correspondence between codes and positions in the input, so displaying what input has been handled by which parser is possible.

Let's take a parser with a few more `return_error!` calls:

```ignore
# #[macro_use] extern crate nom;
named!(err_test, alt!(
  tag!("abcd") |
  return_error!(ErrorKind::Custom(12),
    preceded!(tag!("efgh"), return_error!(ErrorKind::Custom(42),
        do_parse!(
               tag!("ijk")                      >>
          res: return_error!(ErrorKind::Custom(128), tag!("mnop")) >>
          (res)
        )
      )
    )
  )
));
# fn main() {}
```

We can then define the function `display_error` as follows:

```ignore
use nom::util::{generate_colors,prepare_errors,print_codes,print_offsets};

pub fn display_error<I,O>(input: &[u8], res: IResult<I,O>) {
  let mut h: HashMap<u32, &str> = HashMap::new();
  h.insert(12,  "preceded");
  h.insert(42,  "chain");
  h.insert(128, "tag mnop");
  h.insert(0,   "tag");

  if let Some(v) = prepare_errors(input, res) {
    let colors = generate_colors(&v);
    println!("parsers: {}", print_codes(colors, h));
    println!("{}",   print_offsets(input, 0, &v));
  }
}
```

We give names for the error codes, then make a map between error codes and ANSI colors. The `nom::util::print_codes` shows this map  inline.

The `nom::util::print_offsets` will print the input data in hexadecimal format, with colors applying to different parts of the input.

As an example, for this call:

```ignore
  let input = &b"efghijklblahblah"[..];

  display_error(input, err_test(input));
```

We get the following output:
![colored hexdump](http://dev.unhandledexpression.com/slides/langsec-2015/img/colortest.png)
