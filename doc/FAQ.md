# FAQ

### The compiler indicates `error: expected an item keyword` then points to the function's return type in `named!`:

```ignore
error: expected an item keyword
named!(multi<Vec<&str>>, many0!( map_res!(tag!( "abcd" ), str::from_utf8) ) );
             ^~~
```

This happens because the macro processor mistakes `>>` for an operator. It will work correctly by adding a space, like this: `named!(multi< Vec<&str> >, ...`
