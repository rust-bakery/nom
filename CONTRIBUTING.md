# Contributing to nom

Thanks a lot for contributing to this project!

The following is a set of guidelines for contributing to [nom][1].

**Since the project is young**: consider those best practices prone to change. Please suggest improvements!

[1]: https://github.com/geal/nom

## Basics

### License

The project uses the [MIT][l1] license. By contributing to this project you agree to license
your changes under this license.

[l1]: https://opensource.org/licenses/MIT


## What to do

### Issues

There is plenty of [features missing][i1] and possibly bugs might be already there. Feel free to add new [issues][i2]
and to wrangle over those already [open][i3] and help fixing them.

[i1]: https://github.com/geal/nom/issues?q=is%3Aopen+is%3Aissue+label%3Aenhancement
[i2]: https://github.com/geal/nom/issues
[i3]: https://github.com/geal/nom/issues?q=is%3Aopen+is%3Aissue

### Code

Implementing new codecs, container formats or protocols is always welcome!

### Tests

It is strongly suggested to provide test along changes so the coverage stays around the **85%**, helping to
get to full coverage is pretty welcome.

### Benchmark

Help in making sure the code does not have performance regression, by improving the benchmark suite or just by
running it weekly, is welcome as well.


## Style

### Issue style

Try to write at least 3 short paragraphs describing what were you trying to achieve, what is not working and
the step by step actions that lead to the unwanted outcome.

If possible provide:

- a code snippet or a link to a [gist][is1] showcasing the problem, if is a library usage issue.
- a backtrace, if it is a crash.
- a sample file, if it is a decoding or encoding issue.

[is1]: https://gist.github.com

### Coding style

The normal rust coding style is suggested as enforced by [rustfmt][cs1] is suggested.
Readable code is the first step on having good and safe libraries.

[cs1]: https://github.com/rust-lang-nursery/rustfmt

