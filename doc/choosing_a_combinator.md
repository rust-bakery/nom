# List of parsers and combinators

## Basic elements
Those are used to recognize the lowest level elements of your grammar, like, "here is a dot", or "here is an big endian integer".

| usage | input | output | comment |
|--|--|--|--|
| `char!('a')` |  `"abc"` | `Ok(("bc", 'a'))`| matches one character (works with non ASCII chars too) | 
| ` is_a!("ab")` |  `"ababc"` | `Ok(("c", "abab"))`|matches a sequence of any of the characters passed as arguments. `is_a_s` is an alias for `is_a`|
| `is_not!("cd")` |  `"ababc"` | `Ok(("c", "abab"))`|matches a sequence of none of the characters passed as arguments|
| `one_of!("abc")` |  ``"abc"`` | `Ok(("bc", 'a'))`|matches one of the provided characters (works with non ASCII characters too)|

