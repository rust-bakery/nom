# nom++, [nom](https://github.com/Geal/nom) for methods


**nom** is a parser combinators library written in Rust. Its goal is to provide tools to build safe parsers without compromising the speed or memory consumption. To that end, it uses extensively Rust's *strong typing*, *zero copy* parsing, *push streaming*, *pull streaming*, and provides macros and traits to abstract most of the error prone plumbing.

**nom++** is an extension of **nom** that allows you to create parsing [methods](http://stackoverflow.com/questions/155609/difference-between-a-method-and-a-function). The goal is for method-making macros have parity with the function-making macros that are already in **nom**. 

## Features

Here are the current and planned features, with their status:
- [x] Make method creating and using macros
- [ ] Add variations on parser combinators in macros.rs that will wrap methods just like they wrap functions right now
- [ ] Write tests for all of the new ways you can create and call methods and functions (partially done)

## How to use it

First read up on how to use [**nom**](https://github.com/Geal/nom) because the basics are the same. The differences come in creating methods and then calling methods (although phase 2 will eliminate the extra step in calling methods).

In **nom** you used `named!` to create a parser function:
```rust
named!(<&str, &str>, take4, take!(4));
```
In **nom++** you use `method!`, and supply it with the type of `self` and the `self` struct (a macro can't declare the `self` struct on it's own due to macro hygiene):
```rust
impl<'a> SomeStruct<'a> {
  //      --self's type---                        -self-
  method!(<SomeStruct<'a>, &str, &str>, take4, mut self, take_s!(4));
}
```
You can make `self` immutable if you like:
```rust
  method!(<SomeStruct<'a>, &str, &str>, take4, self, take!(4));
```

Now you can call that method from another method by specifying `call_m!(self.method)` like this:
```rust
impl<'a> SomeStruct<'a> {
  method!(<SomeStruct<'a>, &str, &str>, take4, self, take_s!(4));
  //                                                            -struct.method-
  method!(<&SomeStruct<'a>, &str, &str>, call_take4, self, call_m!(self.take4));
}
```
And that's all there is to it. In phase two I will eliminate the need to wrap `self.method` in a `call_m!` macro:
```rust
  method!(<&SomeStruct<'a>, &str, &str>, call_take4, self, self.take4);
```
so that it's just like how you currently call a function in **nom** parser combinators.

## LOL why would I even need this?

Story time! I was writing a [TOML](https://github.com/toml-lang/toml) parser and needed to store keys and values that were parsed and keep a line count to report where non-failure errors occurred. My options were:

1. Parse the file generating an AST, then post-process the AST noting errors and inserting key/value pairs in a hash table
2. Insert key/value pairs and keep track of line count in global variables
3. Turn my parser functions into methods of a struct and access member variables to insert key/value pairs and keep a line count.

The whole point of **nom**`, besides ease of use, is that it's dang fast. Putting in a post-processing step would be wasteful when what I wanted to do could easily be done on-the-fly. So option 1 was out. Global variables would allow me store my extra information on-the-fly, but, while global variables aren't always bad, I feel they should be avoided whenever possible. So option 2 was also out. Option three avoids globals and does it's work on-the-fly and so was the best option. The only problem was that **nom** didn't support creating parsing methods. So I made them myself.

The anwser then is: you'll want to use parsing structs and methods whenever your parsing requires accessing variables other than the input or your generated output.

It remains to be seen whether [Geal](https://github.com/Geal/) will want to merge this into **nom**. If he doesn't want to add it, I'll just keep this as a fork of **nom** or as a separate crate that builds on top of **nom**.

## How does it work?

I tried many different ways of implementing method calls. It seemed like an easy task, just add `self` to the function signature and call `self.method` instead calling `function`. It turns out to be very tricky due to the lifetime of `self`, its borrows, and the return values of the methods. Simply moving `self` into a called method makes `self` inaccessable for the rest of the method, so macros like `chain` wouldn't be able to call more than one method or modify `self` in it's post processing step:
```rust
chain!(
  stuff: self.do_stuff,
  ||{self.my_stuff = stuff} // Error, use of moved value, self was moved into the do_stuff method.
);
chain!(
  self.do_stuff ~
  self.do_more  , // Error, use of moved value, self was moved into the do_stuff method.
  ||{}
);
```
Borrowing is problematic because of the lifetimes imposed by Rust. In certain situations, usually involving methods that call more than one method and store the return values of the methods, a borrow needs to last the entire function so (pseudo-code of an expanded `chain!` macro):
```rust
  impl<'a> Parser<'a> {
  fn call_two(self: &'a mut Parser<'a>, i: &'a str) -> IResult<&'a str &'a str> {
  ...
    let (stuff, input) = match self.do_stuff(i) {
  ...
    };
    let (more, input) = match self.do_more(input) { // Error, self was borrowed at self.do stuff
    // and the lifetime 'a says that the borrow lasts the entire function, even if the call to
    // do_stuff is in a separate scope
  ...
    };
  )
}
```
Taking the lifetime `'a` off of `self` results in the compiler not being able to resolve conflicting lifetimes.

I tried using `RefCells` with some success, in some situations they worked where simple borrowing didn't but there were plenty of situations where this happened:
```rust
  let self_cell = RefCell::new(self);
  let (stuff, input) = self.borrow_mut().do_stuff(i); // Error, borrow doen't live long enough,
  // it needs to last the entire function, but only lasts until the call to do_stuff..
```
Storing the result of `borrow_mut()` and calling more than one method on it results in a "`self` cannot be mutably borrowed twice" error.

I even tried storing the `RefCell` of `self` in `self` to extend its lifetime, but you have to use a wrapper to do that (otherwise you get a recursive struct error), but unwrapping it to get at the `RefCell` results again in a reference that doesn't live long enough.

So regular borrows last too long to use multiple times. `RefCell` borrows don't last long enough in a lot of cases. After looking at the Rust book chapter on ownership multiple times I decided to try a technique they basically said was really ugly and you should use borrowing instead. This technique is moving a value into a method then returning the value back to the callee.
```rust
fn move_and_return(v: Vec<i32>) -> Vec<i32> {
    // do stuff with v

    // hand back ownership
    v
}
```
The Rust book says:
> This would get very tedious...The return type, return line, and calling the function gets way more complicated.

> Luckily, Rust offers a feature, borrowing, which helps us solve this problem.

Unfortunately for my situation borrowing doesn't solve the problem. So I decided to try, what I'm going to call, "move and return". A `method!` invocation creates a function signature like this:
```rust
fn do_stuff(mut self: Parser<'a>, i: &'a str) -> (Parser<'a>, nom::IResult<&'a str, &'a str>)
```
We now take ownership of `self`, but we return it in a tuple with the `IResult`.

The `call_m` macro makes it work transparently with current parser combinators by restoring ownership of `self` and then returning only the `IResult` that all parser combinators are expecting:
```rust
{
  let (tmp, res) = self.do_more(i); // get self and the IResult back from the called method
  self = tmp; // restore ownership of self
  res // return only the IResult
}
```
In the future, I would like to eliminate the explicit invocation of `call_m` and have parser combinators detect a method call and automatically wrap it in a `call_m` invocation just as it does with function calls and the `call` macro invocation.
