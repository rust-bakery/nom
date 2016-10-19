#[macro_use]
extern crate nom;
extern crate unicode_categories;
#[macro_use]
extern crate slog;
extern crate slog_term;

use nom::{self, IResult, ErrorKind, digit, AsBytes, Compare, Slice, Offset,
InputLength, IterIndices, Needed};
use std::iter::{Iterator};
use unicode_categories::UnicodeCategories;
use slog::Logger;
use std::ops::{Range, RangeFrom, RangeTo, RangeFull};

//trace_macros!(true);


macro_rules! test_one {
    (Done, $log:ident, $r:ident, ($rem:pat, $out:pat)) => {
        match $r {
            IResult::Done($rem, $out) => info!($log, "ok"),
            IResult::Done(rem, out) => /*error!($log,
                "out" => out,
                "rem" => rem;
                "different output"),*/ (),
            IResult::Error(e) => error!($log, "error: {:?}", e),
            IResult::Incomplete(e) => error!($log, "incomplete: {:?}", e),
        }
    };
    
    (Error, $log:ident, $r:ident, ) => {
        match $r {
            IResult::Done(rem, out) => error!($log,
                "out" => out,
                "rem" => rem;
                "did not fail"
            ),
            IResult::Error(e) => info!($log, "ok"),
            IResult::Incomplete(e) => error!($log, "incomplete: {:?}", e),
        }
    }
}
macro_rules! test_many {
    ( $(
        $parser:ident ($case:expr $(, $arg:expr)* ) => $d:tt $( ( $e:pat, $f:pat ) )* ;
        )* ) => {
        use slog_term::streamer;
        use slog::DrainExt;
        let log = streamer().build().fuse();
        
        $(
            /*let root = Logger::root(log, o!(
                "parser" => stringify!($parser),
                "case" => stringify!($case $(,$arg)*)));
            */
            let root = log.clone();
            let b = wrap($case.into(), root);
            let r = $parser(b $(,$arg)*);
            test_one!($d, root, r, $( ($e, $f) )* );
        )*
    }
}

//type Data<'a> = &'a str;
type Data<'a> = Baguette<'a>;

#[macro_export]
macro_rules! named (
  ($name:ident, $submac:ident!( $($args:tt)* )) => (
    fn $name<'a>( i: Data<'a> ) -> nom::IResult<Data<'a>, Data<'a>, u32> {
      $submac!(i, $($args)*)
    }
  );
  ($name:ident<$o:ty>, $submac:ident!( $($args:tt)* )) => (
    fn $name<'a>( i: Data<'a> ) -> nom::IResult<Data<'a>, $o, u32> {
      $submac!(i, $($args)*)
    }
  );
);

named!(space, recognize!(many1!(alt!(tag!(" ") | tag!("\t")))));
#[test]
fn test_space() {
    test_many!(
        space("  x") => Done("x", "  ");
        space(" \t \nx") => Done("\nx", " \t ");
        space("\nx") => Error;
        space("x") => Error;
    );
}

named!(newline, tag!("\n"));

named!(endline <()>, map!(tuple!(space, newline), |_| {()}));
#[test]
fn test_endline() {
    test_many!(
        endline("  \n") => Done("", ());
        endline("\t\n") => Done("", ());
        endline("\n") => Done("", ());
    );
}
named!(empty_lines <usize>,
    map!(many1!(endline), |v: Vec<()>| { v.len() } )
);

named!(indent_any,
    alt_complete!(
        tag!("    ")
      | tag!("\t")
    )
);

#[derive(Debug, PartialEq)]
pub enum Var<'a> {
    Name(&'a str),
    Number(usize)
}
named!(var <Var>,
    alt!(
        map!(letter_sequence, |s: Data<'a>| { Var::Name(s.into()) }) |
        map_opt!(digit, |s: Data| { s.parse::<usize>().ok().map(Var::Number) })
    )
);


#[derive(Debug, PartialEq)]
pub enum Item<'a> {
    Word(&'a str),
    Reference(&'a str),
    Symbol(&'a str),
    Punctuation(&'a str),
    Placeholder(Var<'a>)
}

fn letter_sequence(input: Data) -> IResult<Data, Data> {
    //use unicode_segmentation::UnicodeSegmentation;
    //let gi = UnicodeSegmentation::grapheme_indices(input, true);
    let mut codepoints = input.iter_elements();
    let cp = match codepoints.next() {
        Some(cp) => cp,
        None => return IResult::Error(error_position!(ErrorKind::Alpha, input))
    };
    if cp.is_letter() == false {
        return IResult::Error(error_position!(ErrorKind::Alpha, input));
    }
    loop {
        let remaining = codepoints.as_str();
        match codepoints.next() {
            Some(cp) => {
                if cp.is_letter() {
                    continue;
                } else {
                    let p = input.input_len() - remaining.input_len();
                    return IResult::Done(input.slice(p..), input.slice(..p));
                }
            }
            None => break
        }
    }
    
    IResult::Done(input.slice(input.input_len() ..), input)
}
#[test]
fn test_letter_sequence() {
    test_many!(
        letter_sequence("hello") => Done("", "hello");
        letter_sequence("h") => Done("", "h");
        letter_sequence("hello world") => Done(" world", "hello");
        letter_sequence("hello\nworld") => Done("\nworld", "hello");
        letter_sequence("") => Error;
    );
}

fn string_esc<'a>(input: Data<'a>) -> IResult<Data<'a>, String> {
    map!(input, many1!(
        complete!(alt!(
            map!(take_until_either!("\\\""), { |d: Data<'a>| d.into() })
          | map!(tag!(r"\\"),     { |_| "\\" })
          | map!(tag!(r"\t"),     { |_| "\t" })
          | map!(tag!(r"\n"),     { |_| "\n" })
          | map!(tag!(r"\ "),     { |_| " "  })
          | map!(tag!(r##"\""##), { |_| "\"" })
        ))),
        |v: Vec<&str>| v.concat()
    )
}

named!(string <String>,
    alt!(
        complete!(delimited!(tag!("\""), string_esc, tag!("\"")))
      | map!(take_until_either!("\" \t\n"), |s: Data| s.into())
    )
);
#[test]
fn test_string() {
    test_many!(
        string("hallo ") => Done(" ", String::from("hallo"));
        string("hallo welt") => Done(" welt", String::from("hallo"));
        string(r"hallo\ welt") => Done(r" welt", String::from(r"hallo\"));
        string(r##""hallo welt""##) => Done("", String::from("hallo welt"));
        string(r##""hallo\ welt" .."##) => Done(" ..", String::from(r"hallo welt"));
        string(r##""hallo\nwelt""##) => Done("", String::from("hallo\nwelt"));
    );
}

fn test_chars<'a, F: Fn(char) -> bool>(input: Data<'a>, test: F) -> IResult<Data<'a>, Data<'a>>
{
    let mut codepoints = input.iter_elements();
    let cp = match codepoints.next() {
        Some(cp) => cp,
        None => return IResult::Error(error_position!(ErrorKind::Alpha, input))
    };
    if test(cp) == false {
        return IResult::Error(error_position!(ErrorKind::Alpha, input));
    }
    
    loop {
        let p = input.input_len() - codepoints.as_str().len();
        match codepoints.next() {
            Some(cp) => {
                if test(cp) {
                    continue;
                } else {
                    return IResult::Done(input.slice(p..), input.slice(..p));
                }
            }
            None => break
        }
    }
    
    IResult::Done(input.slice(input.input_len() ..), input)
}

fn item<'a>(input: Data<'a>) -> IResult<Data<'a>, Item<'a>> {
    alt!(input,
        map!(preceded!(tag!("."), letter_sequence),
            |s: Data<'a>| { Item::Reference(s.into()) }
        )
      | map!(preceded!(tag!("$"), var),
            |v| { Item::Placeholder(v) }
        )
      | map!(letter_sequence,
            |s: Data<'a>| { Item::Word(s.into()) }
        )
      | map!(apply!(test_chars, |c: char| c.is_symbol() ),
            |s: Data<'a>| { Item::Symbol(s.into()) }
        )
      | map!(apply!(test_chars, |c: char| c.is_punctuation() ),
            |s: Data<'a>| { Item::Punctuation(s.into()) }
        )
    )
}
#[test]
fn test_item() {
    test_many!(
        item(".foo\n") => Done("\n", Item::Reference("foo"));
        item(".foo baz") => Done(" baz", Item::Reference("foo"));
        item(".baä\n") => Done("\n", Item::Reference("baä"));
        item("foo baz") => Done(" baz", Item::Word("foo"));
        item("$body\n") => Done("\n", Item::Placeholder(Var::Name("body")));
        item("$3\n") => Done("\n", Item::Placeholder(Var::Number(3)));
    );
}

fn leaf_indent(input: Data, expected_indent: usize) -> IResult<Data, Data> {
    recognize!(input,
        complete!(preceded!(
            endline,
            count!(indent_any, expected_indent)
        ))
    )
}
fn leaf_seperator(input: Data, expected_indent: usize) -> IResult<Data, Data> {
    alt_complete!(input,
        apply!(leaf_indent, expected_indent) |
        space
    )
}
fn leaf<'a>(input: Data<'a>, expected_indent: usize) -> IResult<Data<'a>, Vec<Item<'a>>> {
    delimited!(input,
        complete!(count!(indent_any, expected_indent)),
        separated_nonempty_list!(
            apply!(leaf_seperator, expected_indent),
            item
        ),
        endline
    )
}
#[test]
fn test_leaf() {
    test_many!(
        leaf("x\n\ne", 0) => Done("\ne", vec![Item::Word("x")]);
        leaf("x \n", 0) => Done("", vec![Item::Word("x")]);
        leaf("x $y\n", 0) => Done("", vec![
            Item::Word("x"),
            Item::Placeholder(Var::Name("y"))
        ]);
        leaf("x \ny\n", 0) => Done("", vec![Item::Word("x"), Item::Word("y")]);
        leaf("Hello world\nThis is the End .\n") => Done("", vec![
            Item::Word("Hello"),
            Item::Word("world"),
            Item::Word("This"),
            Item::Word("is"),
            Item::Word("the"),
            Item::Word("End"),
            Item::Punctuation(".")
        ]);
        leaf("        foo\n        bar \n", 2) => Done("", vec![
            Item::Word("foo"),
            Item::Word("bar")
        ]);
    );
}

fn list_item(input: Data, expected_indent: usize) -> IResult<Data, Vec<Item>> {
    preceded!(input,
        complete!(tuple!(
            count!(indent_any, expected_indent),
            tag!("  - ")
        )),
        separated_nonempty_list!(
            alt_complete!(
                dbg!(space) |
                dbg!(apply!(leaf_indent, expected_indent + 1))
            ),
            dbg!(item)
        )
    )
}
#[test]
fn test_list_item() {
    test_many!(
        list_item("  - hello world", 0) => Done("", vec![
            Item::Word("hello"),
            Item::Word("world")
        ]);
        list_item("      - hello", 1) => Done("", vec![Item::Word("hello")]);
        list_item("  - hello\n    world\n", 0) => Done("\n", vec![
            Item::Word("hello"),
            Item::Word("world")
        ]);
    );
}

#[derive(Debug, PartialEq)]
pub struct Parameter<'a> {
    pub name: &'a str,
    pub args: Vec<Item<'a>>,
    pub value: BlockBody<'a>
}

#[derive(Debug, PartialEq)]
pub struct Command<'a> {
    pub name: &'a str,
    pub args: Vec<String>
}

#[derive(Debug, PartialEq)]
pub struct Block<'a> {
    pub name:       &'a str,
    pub argument:   Vec<Item<'a>>,
    pub body:       BlockBody<'a>
}

#[derive(Debug, PartialEq)]
pub struct BlockBody<'a> {
    pub commands:   Vec<Command<'a>>,
    pub parameters: Vec<Parameter<'a>>,
    pub childs:     Vec<Body<'a>>
}

#[derive(Debug, PartialEq)]
pub enum Body<'a> {
    Leaf(Vec<Item<'a>>),
    List(Vec<Vec<Item<'a>>>),
    Block(Block<'a>),
    Placeholder(Var<'a>)
}

fn block_leaf(input: Data, indent_level: usize) -> IResult<Data, Body> {
    map!(input,
        apply!(leaf, indent_level),
        |items| { Body::Leaf(items) }
    )
}

fn block_list(input: Data, indent_level: usize) -> IResult<Data, Body> {
    //println!("list_item at level {}", indent_level + 1);
    map!(input,
        complete!(many1!(
            apply!(list_item, indent_level)
        )),
        |l| Body::List(l)
    )
}
fn block_block(input: Data, indent_level: usize) -> IResult<Data, Body> {
    map!(input,
        complete!(apply!(block, indent_level)),
        |b| Body::Block(b)
    )
}
fn block_placeholder(input: Data, indent_level: usize) -> IResult<Data, Body> {
    do_parse!(input,
            complete!(count!(indent_any, indent_level))
    >>      tag!("$")
    >> var: var
    >>      endline
    >>     (Body::Placeholder(var))
    )
}
#[test]
fn test_block_placeholder() {
    test_many!(
        block_placeholder("    $foo\n", 1) =>
            Done("", Body::Placeholder(Var::Name("foo")));
    );
}

pub fn block_body(input: Data, indent_level: usize) -> IResult<Data, BlockBody> {
    do_parse!(input,
          commands: many0!(apply!(command, indent_level))
    >>  parameters: many0!(apply!(pattern, indent_level))
    >>      childs: many0!(terminated!(
                        alt_apply!(indent_level,
                            block_leaf | block_list | block_block | block_placeholder
                        ),
                        opt!(empty_lines)
                    ))
    >>             (BlockBody {
                        commands:   commands,
                        parameters: parameters,
                        childs:     childs,
                    })
    )
}
pub fn command(input: Data, indent_level: usize) -> IResult<Data, Command> {
    do_parse!(input,
                complete!(count!(indent_any, indent_level))
    >>          tag!("!")
    >>    name: letter_sequence
    >>          space
    >>    args: separated_list!(space, string)
    >>          endline
    >>          opt!(empty_lines)
    >>         (Command { name: name.into(), args: args })
    )
}
pub fn pattern(input: Data, indent_level: usize) -> IResult<Data, Parameter> {
    do_parse!(input,
              complete!(count!(indent_any, indent_level))
    >>        tag!("/")
    >>  name: letter_sequence
    >>        space
    >>  args: separated_list!(space, item)
    >>        endline
    >> value: apply!(block_body, indent_level + 1)
    >>       (Parameter { name: name.into(), args: args, value: value })
    )
}

#[test]
fn test_pattern_1() {
    test_many!(
        pattern("/foo x\n", 0) => Done("", Parameter {
            name:   "foo",
            args:   vec![Item::Word("x")],
            value:  BlockBody {
                commands:   vec![],
                parameters: vec![],
                childs:     vec![],
            }
        });
    );
}
#[test]
fn test_pattern_2() {
    test_many!(
        pattern("/foo x\n    bar\n", 0) => Done("", Parameter {
            name:   "foo",
            args:   vec![Item::Word("x")],
            value:  BlockBody {
                commands:   vec![],
                parameters: vec![],
                childs:     vec![
                    Body::Leaf(vec![
                        Item::Word("bar")
                    ])
                ]
            }
        });
    );
}
#[test]
fn test_pattern_3() {
    test_many!(
        pattern("/foo x\n    bar $baz\n", 0) => Done("", Parameter {
            name:   "foo",
            args:   vec![Item::Word("x")],
            value:  BlockBody {
                commands:   vec![],
                parameters: vec![],
                childs:     vec![
                    Body::Leaf(vec![
                        Item::Word("bar"),
                        Item::Placeholder(Var::Name("baz"))
                    ])
                ]
            }
        });
    );
}

pub fn block(input: Data, indent_level: usize) -> IResult<Data, Block> {
    //println!("block at level {}:", indent_level);
    do_parse!(input,
                complete!(count!(indent_any, indent_level))
    >>          complete!(tag!(":"))
    >>    name: letter_sequence
    >>          opt!(space)
    >>     arg: separated_list!(space, item)
    >>          endline
    >>          opt!(empty_lines)
    >>    body: apply!(block_body, indent_level + 1)
    >>         (Block {
                    name:       name.into(),
                    argument:   arg,
                    body:       body
                })
    )
}
#[test]
fn test_block_1() {
    test_many!(
        block(":foo\n    x\n", 0) => Done("", Block {
            name:       "foo",
            argument:   vec![],
            body: BlockBody {
                commands:   vec![],
                parameters: vec![],
                childs:     vec![
                    Body::Leaf(vec![
                        Item::Word("x"),
                    ])
                ]
            }
        });
    );
}
#[test]
fn test_block_2() {
    test_many!(
        block(":foo\n\n   x\n", 0) => Done("", Block {
            name:       "foo",
            argument:   vec![],
            body: BlockBody {
                commands:   vec![],
                parameters: vec![],
                childs:     vec![
                    Body::Leaf(vec![
                        Item::Word("x"),
                    ])
                ]
            }
        });
    );
}
#[test]
fn test_block_3() {
    test_many!(
        block(":foo\n    !x\n    x\n", 0) => Done("", Block {
            name:       "foo",
            argument:   vec![],
            body: BlockBody {
                commands: vec![
                    Command {
                        name:   "x",
                        args:   vec![]
                    }
                ],
                parameters: vec![],
                childs:     vec![
                    Body::Leaf(vec![
                        Item::Word("x"),
                    ])
                ]
            }
        });
    );
}

fn count_lines(data: &str, offset: usize) -> (usize, usize) {
    if let Some((n, last)) = data.lines().enumerate().last() {
        (n+1, last.len())
    } else {
        (0, offset)
    }
}

use std;
#[derive(Clone)]
pub struct Baguette<'a> {
    // full input data
    data:           &'a str,
    
    // current slice
    slice:          &'a str,
    
    line:           usize,
    line_offset:    usize,
    
    logger:         Logger
}
impl<'a> Baguette<'a> {
    fn parse<F>(&self) -> Result<F, F::Err> where F: std::str::FromStr {
        self.slice.parse()
    }
}
impl<'a> Into<&'a str> for Baguette<'a> {
    fn into(self) -> &'a str {
        self.slice
    }
}
impl<'a> Into<String> for Baguette<'a> {
    fn into(self) -> String {
        self.slice.to_owned()
    }
}
impl<'a> std::fmt::Debug for Baguette<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        self.slice.fmt(f)
    }
}   

impl<'a> AsBytes for Baguette<'a> {
    fn as_bytes(&self) -> &[u8] {
        self.data.as_bytes()
    }
}
impl<'a, 'b> Compare<&'b str> for Baguette<'a> {
    fn compare(&self, o: &'b str) -> nom::CompareResult {
        self.slice.compare(o)
    }
    
    fn compare_no_case(&self, o: &'b str) -> nom::CompareResult {
        use nom::Compare;
        self.slice.compare_no_case(o)
    }
}
impl<'a> Slice<Range<usize>> for Baguette<'a> {
    fn slice(&self, r: Range<usize>) -> Baguette<'a> {
        let (lines, offset) = count_lines(&self.slice[.. r.start], self.line_offset);
        Baguette {
            data:           self.data,
            slice:          self.slice.slice(r),
            line:           self.line + lines,
            line_offset:    offset,
            logger:         self.logger.clone()
        }
    }
}
impl<'a> Slice<RangeFrom<usize>> for Baguette<'a> {
    fn slice(&self, r: RangeFrom<usize>) -> Baguette<'a> {
        let (lines, offset) = count_lines(&self.data[.. r.start], self.line_offset);
        Baguette {
            data:           self.data,
            slice:          self.slice.slice(r),
            line:           self.line + lines,
            line_offset:    offset,
            logger:         self.logger.clone()
        }
    }
}
impl<'a> Slice<RangeTo<usize>> for Baguette<'a> {
    fn slice(&self, r: RangeTo<usize>) -> Baguette<'a> {
        Baguette {
            data:           self.data,
            slice:          self.slice.slice(r),
            line:           self.line,
            line_offset:    self.line_offset,
            logger:         self.logger.clone()
        }
    }
}
impl<'a> Slice<RangeFull> for Baguette<'a> {
    fn slice(&self, r: RangeFull) -> Baguette<'a> {
        Baguette {
            data:           self.data,
            slice:          self.slice,
            line:           self.line,
            line_offset:    self.line_offset,
            logger:         self.logger.clone()
        }
    }
}
impl<'a> Offset for Baguette<'a> {
    fn offset(&self, second: &Baguette) -> usize {
        second.slice.as_ptr() as usize - self.slice.as_ptr() as usize
    }
}
impl<'a> InputLength for Baguette<'a> {
    fn input_len(&self) -> usize {
        self.slice.len()
    }
}
impl<'a> IterIndices for Baguette<'a> {
    type Item     = char;
    type RawItem  = char;
    type Iter     = std::str::CharIndices<'a>;
    type IterElem = std::str::Chars<'a>;
    #[inline]
    fn iter_indices(&self) -> std::str::CharIndices<'a> {
        self.slice.char_indices()
    }
    #[inline]
    fn iter_elements(&self) -> std::str::Chars<'a> {
      self.slice.chars()
    }
    fn position<P>(&self, predicate: P) -> Option<usize> where P: Fn(Self::RawItem) -> bool {
      for (o,c) in self.slice.char_indices() {
        if predicate(c) {
          return Some(o)
        }
      }
      None
    }
    #[inline]
    fn index(&self, count: usize) -> Option<usize> {
      let mut cnt    = 0;
      for (index, _) in self.slice.char_indices() {
        if cnt == count {
          return Some(index)
        }
        cnt += 1;
      }
      None
    }
}
pub fn wrap(data: &str, logger: Logger) -> Baguette {
    Baguette {
        data:           data,
        slice:          data,
        line:           0,
        line_offset:    0,
        logger:         logger
    }
}

trace_macros!(false);
