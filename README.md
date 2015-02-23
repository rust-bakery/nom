# nom, eating data byte by byte

nom is a parser combinators library written in Rust. Its goal is to provide tools to build safe parsers without compromising the speed or memory consumption. To that end, it uses extensively Rust's *strong typing*, *zero copy* parsing, *push streaming*, *pull streaming*, and provides macros and traits to abstract most of the error prone plumbing.

This work is currently experimental, the API and syntax may still change a lot, but it can already be used to parse relatively complex formats like [MP4](tests/mp4.rs).

[![Build Status](https://travis-ci.org/Geal/nom.svg?branch=master)](https://travis-ci.org/Geal/nom)

## Features

Here are the current and planned features, with their actual status:
- [ ] *safe parsing*: while I have some confidence in Rust's abilities, this will be put to the test by extensive fuzzing
- [x] *zero copy*:
  - [x] _in the parsers_: a parsing chain will always return a reference to its input data
  - [x] _in the producers and consumers_: some copying still happens
- [x] *streaming*:
  - [x] _push_: a parser can be directly fed a producer's output and called every time there is data available
  - [x] _pull_: a consumer will take a parser and a producer, and handle all the data gathering and, if available, seeking the streaming

Some documentation is available [here](http://rust.unhandledexpression.com/nom/).
