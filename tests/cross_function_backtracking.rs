/// this file tests a different backtracking behaviour. With the current
/// `error!` macro, an early return is done in the current function, but
/// backtracking continues normally outside of that function.
///
/// The solution here wraps `IResult` in a `Result`: a `Ok` indicates usual
/// backtracking, `Err` indicates that we must "cut".

#[macro_use]
extern crate nom;

macro_rules! n (
    ($name:ident( $i:ty ) -> $o:ty, $submac:ident!( $($args:tt)* )) => (
        fn $name( i: $i ) -> std::result::Result<nom::IResult<$i,$o,u32>, nom::Err<$i, u32>> {
            std::result::Result::Ok($submac!(i, $($args)*))
        }
    );
    ($name:ident<$i:ty,$o:ty,$e:ty>, $submac:ident!( $($args:tt)* )) => (
        fn $name( i: $i ) -> std::result::Result<nom::IResult<$i, $o, $e>, nom::Err<$i, $e>> {
            std::result::Result::Ok($submac!(i, $($args)*))
        }
    );
    ($name:ident<$i:ty,$o:ty>, $submac:ident!( $($args:tt)* )) => (
        fn $name( i: $i ) -> std::result::Result<nom::IResult<$i, $o, u32>, nom::Err<$i, u32>> {
            std::result::Result::Ok($submac!(i, $($args)*))
        }
    );
    ($name:ident<$o:ty>, $submac:ident!( $($args:tt)* )) => (
        fn $name<'a>( i: &'a[u8] ) -> std::result::Result<nom::IResult<&'a [u8], $o, u32>, nom::Err<&'a [u8], u32>> {
            std::result::Result::Ok($submac!(i, $($args)*))
        }
    );
    ($name:ident, $submac:ident!( $($args:tt)* )) => (
        fn $name( i: &[u8] ) -> std::result::Result<nom::IResult<&[u8], &[u8], u32>, nom::Err<&[u8], u32>> {
            std::result::Result::Ok($submac!(i, $($args)*))
        }
    );
    (pub $name:ident( $i:ty ) -> $o:ty, $submac:ident!( $($args:tt)* )) => (
        pub fn $name( i: $i ) -> std::result::Result<nom::IResult<$i,$o, u32>, nom::Err<$i, u32>> {
            std::result::Result::Ok($submac!(i, $($args)*))
        }
    );
    (pub $name:ident<$i:ty,$o:ty,$e:ty>, $submac:ident!( $($args:tt)* )) => (
        pub fn $name( i: $i ) -> std::result::Result<nom::IResult<$i, $o, $e>, nom::Err<$i, $e>> {
            std::result::Result::Ok($submac!(i, $($args)*))
        }
    );
    (pub $name:ident<$i:ty,$o:ty>, $submac:ident!( $($args:tt)* )) => (
        pub fn $name( i: $i ) -> std::result::Result<nom::IResult<$i, $o, u32>, nom::Err<$i, u32>> {
            std::result::Result::Ok($submac!(i, $($args)*))
        }
    );
    (pub $name:ident<$o:ty>, $submac:ident!( $($args:tt)* )) => (
        pub fn $name( i: &[u8] ) -> std::result::Result<nom::IResult<&[u8], $o, u32>, nom::Err<&[u8], u32>> {
            std::result::Result::Ok($submac!(i, $($args)*))
        }
    );
    (pub $name:ident, $submac:ident!( $($args:tt)* )) => (
        pub fn $name<'a>( i: &'a [u8] ) -> std::result::Result<nom::IResult<&[u8], &[u8], u32>, nom::Err<&[u8], u32>> {
            std::result::Result::Ok($submac!(i, $($args)*))
        }
    );
);

macro_rules! cut (
  ($i:expr, $code:expr, $submac:ident!( $($args:tt)* )) => (
    {
      let cl = || {
        Ok($submac!($i, $($args)*))
      };

      match cl() {
        std::result::Result::Ok(nom::IResult::Incomplete(x)) => nom::IResult::Incomplete(x),
        std::result::Result::Ok(nom::IResult::Done(i, o))    => nom::IResult::Done(i, o),
        std::result::Result::Ok(nom::IResult::Error(e)) | std::result::Result::Err(e)  => {
          return std::result::Result::Err(nom::Err::NodePosition($code, $i, Box::new(e)))
        }
      }
    }
  );
  ($i:expr, $code:expr, $f:expr) => (
    cut!($i, $code, call!($f));
  );
);

macro_rules! c (
  ($i:expr, $f:expr) => (
    {
      match $f($i) {
        std::result::Result::Ok(nom::IResult::Incomplete(x)) => nom::IResult::Incomplete(x),
        std::result::Result::Ok(nom::IResult::Done(i, o))    => nom::IResult::Done(i, o),
        std::result::Result::Ok(nom::IResult::Error(e))      => nom::IResult::Error(e),
        std::result::Result::Err(e)     => {
          return std::result::Result::Err(e)
        }
      }
    }
  );
);

n!(pub foo< bool >,
    chain!(
        tag!("a") ~
        cut!(nom::ErrorKind::Custom(42),dbg_dmp!(tag!("b"))) ,
        || { true }
    )
);

n!(pub foos< Vec<bool> >,
    delimited!(
        tag!("("),
        many0!(c!(foo)),
        tag!(")")
    )
);

#[test]
fn test_ok() {
    let r = foos(b"(abab)");
    println!("result: {:?}", r);
    match r {
        Ok(nom::IResult::Done(_,result)) => assert_eq!(result,vec![true,true]),
        res => panic!("Oops {:?}.",res)
    }
}

#[test]
fn test_err() {
    let input = b"(ac)";
    let r = foos(&input[..]);
    println!("result: {:?}", r);
    match r {
        //Ok(nom::IResult::Error(nom::Err::Position(kind,_))) => assert_eq!(kind,nom::ErrorKind::Custom(42)),
        Err(nom::Err::NodePosition(kind, position, _)) => {
          assert_eq!(kind, nom::ErrorKind::Custom(42));
          assert_eq!(position, &input[2..]);
        }
        res => panic!("Oops, {:?}",res)
    }
}

