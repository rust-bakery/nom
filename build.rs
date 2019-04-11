extern crate version_check;

fn main() {
  match version_check::is_min_version("1.28.0") {
    Some((true, _actual_version)) => {
      println!("cargo:rustc-cfg=stable_i128");
    }
    Some(_) => (),
    None => {
      eprintln!("couldn't query version info from rustc");
    }
  }
}
