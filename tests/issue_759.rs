#[macro_use]
extern crate nom;

use std::str;

fn atom_specials(c: u8) -> bool {
    c == b'q'
}

named!(
    capability<&str>,
    do_parse!(tag_s!(" ") >> _atom: map_res!(take_till1!(atom_specials), str::from_utf8) >> ("a"))
);

#[test]
fn issue_759() {
    assert_eq!(capability(b" abcqd"), Ok((&b"qd"[..], "a")));
}
