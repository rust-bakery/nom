#[doc(hidden)]
#[macro_export]
macro_rules! named_table_intern {
    (match $c:expr; $($p:pat => $e:expr,)*) => (
        match $c {
            $($p => $e, )*
        }
    );
    (enum $name:ident, m=$meta:meta; $($i:ident,)*) => (
        #[$meta]
        enum $name {
            $($i,)*
        }
    );
    (enum $name:ident; $($i:ident,)*) => (
        enum $name {
            $($i,)*
        }
    );
}
/// Generates a table from the specified map.
///
/// It also defines an enum with the name given by enum=name .
///
/// ```
/// # #[macro_use] extern crate nom;
/// use nom::{IResult, IterIndices, Slice};
/// # fn main() {
/// named_table!(c0_table, enum=C0, meta=derive(PartialEq, Debug);
///     0x1D => GroupSeparator,
///     0x1E => RecordSeparator,
///     0x1F => UnitSeparator,
/// );
/// # }
/// ```
///
/// The generated macro `c0_table` can then either be used to:
///
/// #### match one input value:
/// If and only if the table does not match all input values,
/// an additional fallback has to be specified.
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::{IResult, IterIndices, Slice};
/// # fn main() {
/// # named_table!(c0_table, enum=C0, meta=derive(PartialEq, Debug);
/// #     0x1D => GroupSeparator,
/// #     0x1E => RecordSeparator,
/// #     0x1F => UnitSeparator,
/// # );
/// let byte: u8 = 0x1D;
///
/// // this does not work:
/// // let symbol = c0_table!(match byte);
/// let symbol = c0_table!(match byte, _ => panic!());
/// assert_eq!(symbol, C0::GroupSeparator);
/// # }
/// ```
///
/// ### match a symbol and get the corresponding input value:
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::{IResult, IterIndices, Slice};
/// # fn main() {
/// # named_table!(c0_table, enum=C0, meta=derive(PartialEq, Debug);
/// #     0x1D => GroupSeparator,
/// #     0x1E => RecordSeparator,
/// #     0x1F => UnitSeparator,
/// # );
/// let symbol: C0 = C0::UnitSeparator;
/// let byte = c0_table!(rev symbol);
/// assert_eq!(byte, 0x1F);
/// # }
/// ```
///
/// ### work as a tag and match the specifed values:
///
/// ```
/// # #[macro_use] extern crate nom;
/// # use nom::{IResult, IterIndices, Slice};
/// # fn main() {
/// # named_table!(c0_table, enum=C0, meta=derive(PartialEq, Debug);
/// #     0x1D => GroupSeparator,
/// #     0x1E => RecordSeparator,
/// #     0x1F => UnitSeparator,
/// # );
/// let input: &[u8] = b"\x1dbar" as &[u8];
/// let result: IResult<&[u8], C0> = c0_table!(parse input);
/// assert_eq!(result, IResult::Done(b"bar" as &[u8], C0::GroupSeparator));
/// # }
/// ```
#[macro_export]
macro_rules! named_table {
    ($t:ident, enum = $n:ident, meta = $m:meta; $($a:expr => $b:ident,)*) => {
        named_table_intern!(enum $n, m=$m; $($b,)*);
        macro_rules! $t {
            (match $e:expr) => (
                named_table_intern!(match $e; $($a => $n::$b,)*);
            );
            (match $e:expr, _ => $d:expr) => (
                named_table_intern!(match $e; $($a => $n::$b,)* _ => {$d},);
            );
            (rev $e:expr) => (
                named_table_intern!(match $e; $($n::$b => $a,)*);
            );
            (parse $i:expr) => (
                match $i.iter_elements().next() {
                    None =>
                        $crate::IResult::Incomplete($crate::Needed::Size(1)),
                    Some(&c) =>
                        named_table_intern!(match c;
                            $($a => $crate::IResult::Done($i.slice(1 ..), $n::$b),)*
                            _ => $crate::IResult::Error(
                                error_code!($crate::ErrorKind::TableParser)
                            ),
                        )
                }
            );
            (parse $i:expr; x $op:tt $x:expr) => (
                match $i.iter_elements().next() {
                    None =>
                        $crate::IResult::Incomplete($crate::Needed::Size(1)),
                    Some(&c) =>
                        named_table_intern!(match c $op $x;
                            $($a => $crate::IResult::Done($i.slice(1 ..), $n::$b),)*
                            _ => $crate::IResult::Error(
                                error_code!($crate::ErrorKind::TableParser)
                            ),
                        )
                }
            );
        }
    }
}

#[test]
fn test_table(){
    use super::{IResult, IterIndices, Slice};

    named_table!(c0_table, enum=C0, meta=derive(PartialEq, Debug);
        0x1D => GroupSeparator,
        0x1E => RecordSeparator,
        0x1F => UnitSeparator,
    );

    named_table!(c1_table, enum=C1, meta=derive(PartialEq, Debug);
        0x97 => EndProtectedArea,
        0x80 => PaddingCharacter,
        0x85 => NextLine,
    );

    fn test_c1(b: u8) -> C1 {
        c1_table!(match b, _ => panic!())
    }
    fn test_c1_rev(c: C1) -> u8 {
        c1_table!(rev c)
    }
    fn test_c0_parse(buf: &[u8]) -> IResult<&[u8], C0> {
        c0_table!(parse buf)
    }
    fn test_c1_parse_40(buf: &[u8]) -> IResult<&[u8], C1> {
        c1_table!(parse buf; x + 0x40)
    }

    assert_eq!(C1::EndProtectedArea, test_c1(0x97));
    assert_eq!(test_c1_rev(C1::EndProtectedArea), 0x97);
    
    assert_eq!(test_c0_parse(&b"\x1dfoo"[..]), IResult::Done(&b"foo"[..], C0::GroupSeparator));
    
    assert_eq!(test_c1_parse_40(&b"\x57foo"[..]), IResult::Done(&b"foo"[..], C1::EndProtectedArea));
}
