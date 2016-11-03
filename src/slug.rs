use traits::*;
use ::{Offset, AsBytes};
use std::ops::{Range, RangeFrom, RangeTo, RangeFull};


#[macro_export]
macro_rules! dbg (
  ($i: expr, $submac:ident!( $($args:tt)* )) => (
    {
      let input = $i;
      let l = line!();
      input.show();
      println!("{} @ {}", stringify!($submac($($args)*)), l);
      match $submac!(input.clone(), $($args)*) {
        $crate::IResult::Error(a) => {
          println!("=> Error({:?})", a);
          $crate::IResult::Error(a)
        },
        $crate::IResult::Incomplete(a) => {
          println!("=> Incomplete({:?})", a);
          $crate::IResult::Incomplete(a)
        },
        $crate::IResult::Done(i, o) => {
          println!("=> Done({:?})", o);
          $crate::IResult::Done(i, o)
        }
      }
    }
  );

  ($i:expr, $f:ident) => (
      dbg!($i, call!($f));
  );
);

#[macro_export]
macro_rules! slug {
    (__internal Done, $log:ident, $r:ident, ($rem:expr, $out:expr)) => {
        {
        match $r {
            $crate::IResult::Done(rem, out) => {
                if rem.compare($rem) != $crate::CompareResult::Ok {
                    let expected: &str = $rem.into();
                    let found: &str = rem.into();
                    println!("expected {:?}, found {:?}", expected, found);
                    panic!();
                }
                if !out.eq(&$out) {
                    println!("different output: {:?} != {:?}", out, $out);
                    panic!();
                }
                println!("ok");
            },
            $crate::IResult::Error(e) => {
                println!("error: {:?}", e);
                panic!();
            },
            $crate::IResult::Incomplete(e) => {
                println!("incomplete: {:?}", e);
                panic!();
            }
        }

        }
    };
    
    (__internal Error, $log:ident, $r:ident, ) => {
        match $r {
            $crate::IResult::Done(_, _) => {
                println!("did not fail");
                panic!();
            },
            $crate::IResult::Error(_) => println!("ok"),
            $crate::IResult::Incomplete(e) => {
                println!("incomplete: {:?}", e);
                panic!();
            }
        }
    };
    
    ( $(
        $parser:ident ($case:expr $(, $arg:expr)* ) => $d:tt $( ( $e:expr, $f:expr ) )* ;
        )* ) => {
        $(
            println!("{}({:?})", stringify!($parser), stringify!($case $(,$arg)*));
            
            let b = $crate::slug::wrap($case.into());
            let r = $parser(b.clone() $(,$arg)*);
            slug!(__internal $d, b, r, $( ($e, $f) )* );
        )*
    }
}

use std;
#[derive(Clone)]
pub struct Slug<'a> {
    // full input data
    data:           &'a str,
    
    // current slice
    slice:          &'a str,
    
    line:           usize
}
impl<'a> Slug<'a> {
    pub fn parse<F>(&self) -> Result<F, F::Err> where F: std::str::FromStr {
        self.slice.parse()
    }
    pub fn show(&self) {
        use std::iter::{repeat};
        
        // offset of slice into data
        let offset = self.slice.as_ptr() as usize - self.data.as_ptr() as usize;
        let line_start = self.data[.. offset]
            .rfind('\n')
            .map(|p| p+1)
            .unwrap_or_else(|| 0);
        let (line, endl) = match self.data[offset ..].find('\n') {
            Some(end) => (&self.data[line_start .. end+offset], '\u{21B5}'),
            None => (&self.data[line_start ..], '\u{2016}')
        };
        let cursor = self.data[line_start .. offset].chars().count();
        let marker: String = repeat(" ").take(cursor).collect();
        println!("line {}\n{}{}\n{}^ position", self.line, line, endl, marker);
    }
    
}
impl<'a> PartialEq for Slug<'a> {
    #[inline(always)]
    fn eq(&self, other: &Slug<'a>) -> bool {
        self.slice.eq(other.slice)
    }
}
impl<'a> PartialEq<str> for Slug<'a> {
    #[inline(always)]
    fn eq(&self, other: &str) -> bool {
        self.slice.eq(other)
    }
}
impl<'a, 'b> PartialEq<&'b str> for Slug<'a> {
    #[inline(always)]
    fn eq(&self, other: &&'b str) -> bool {
        self.slice.eq(*other)
    }
}
impl<'a> Into<&'a str> for Slug<'a> {
    #[inline(always)]
    fn into(self) -> &'a str {
        self.slice
    }
}
impl<'a> Into<String> for Slug<'a> {
    fn into(self) -> String {
        self.slice.to_owned()
    }
}
impl<'a> std::fmt::Debug for Slug<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        self.slice.fmt(f)
    }
}   

impl<'a> AsBytes for Slug<'a> {
    #[inline(always)]
    fn as_bytes(&self) -> &[u8] {
        self.data.as_bytes()
    }
}
impl<'a, 'b> Compare<&'b str> for Slug<'a> {
    #[inline(always)]
    fn compare(&self, o: &'b str) -> CompareResult {
        self.slice.compare(o)
    }
    
    #[inline(always)]
    fn compare_no_case(&self, o: &'b str) -> CompareResult {
        self.slice.compare_no_case(o)
    }
}
impl<'a> Slice<Range<usize>> for Slug<'a> {
    #[inline(always)]
    fn slice(&self, r: Range<usize>) -> Slug<'a> {
        let lines = self.slice[.. r.start].chars().filter(|&c| c == '\n').count();
        Slug {
            data:           self.data,
            slice:          self.slice.slice(r),
            line:           self.line + lines
        }
    }
}
impl<'a> Slice<RangeFrom<usize>> for Slug<'a> {
    #[inline(always)]
    fn slice(&self, r: RangeFrom<usize>) -> Slug<'a> {
        let lines = self.slice[.. r.start].chars().filter(|&c| c == '\n').count();
        Slug {
            data:           self.data,
            slice:          self.slice.slice(r),
            line:           self.line + lines
        }
    }
}
impl<'a> Slice<RangeTo<usize>> for Slug<'a> {
    #[inline(always)]
    fn slice(&self, r: RangeTo<usize>) -> Slug<'a> {
        Slug {
            data:           self.data,
            slice:          self.slice.slice(r),
            line:           self.line
        }
    }
}
impl<'a> Slice<RangeFull> for Slug<'a> {
    #[inline(always)]
    fn slice(&self, r: RangeFull) -> Slug<'a> {
        Slug {
            data:           self.data,
            slice:          self.slice,
            line:           self.line
        }
    }
}
impl<'a> Offset for Slug<'a> {
    #[inline(always)]
    fn offset(&self, second: &Slug) -> usize {
        let start = self.slice.as_ptr() as usize;
        let end = second.slice.as_ptr() as usize;
        
        assert!(end >= start, "negative offset");
        end - start
    }
}
impl<'a> InputLength for Slug<'a> {
    #[inline(always)]
    fn input_len(&self) -> usize {
        self.slice.len()
    }
}
impl<'a> IterIndices for Slug<'a> {
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

pub fn wrap(data: &str) -> Slug {
    Slug {
        data:           data,
        slice:          data,
        line:           1
    }
}
