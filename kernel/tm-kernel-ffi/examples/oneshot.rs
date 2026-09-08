//! Read one request from stdin, print the kernel's response.  Used to
//! reproduce boundary behaviour by hand.
use std::io::Read;
fn main() {
    let mut s = String::new();
    std::io::stdin().read_to_string(&mut s).unwrap();
    println!("{}", tm_kernel_ffi::call(s.trim()).unwrap());
}
