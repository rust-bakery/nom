# The Nominomicon

Welcome to Nominomicon; a guide to using the Nom parser for great good.
This guide will give you an introduction to the theory and practice of 
using Nom.

This guide assumes only that you are:
 - Wanting to learn Nom,
 - Already familiar with Rust.

Nom is a parser-combinator library. In other words, it gives you tools to define:
 - "parsers" (a function that takes an input, and gives back an output), and
 - "combinators" (functions that take parsers, and _combine_ them together!).

By combining parsers with combinators, you can build complex parsers up from
simpler ones. These complex parsers are enough to understand HTML, mkv or Python!

Before we set off, it's important to list some caveats:
 - This guide is for Nom7. Nom has undergone significant changes, so if
   you are searching for documentation or StackOverflow answers, you may
   find older documentation. Some common indicators that it is an old version are:
    - Documentation older than 21st August, 2021
    - Use of the `named!` macro
    - Use of `CompleteStr` or `CompleteByteArray`.
 - Nom can parse (almost) anything; but this guide will focus almost entirely on parsing
   complete `&str` into things.
