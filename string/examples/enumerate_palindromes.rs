use iolib::{putitln, scan};
use string::Palindrome;

fn main() {
    scan!(s: String);

    let pal = Palindrome::new(&s);
    putitln!(pal.enumerate_length(), sep = ' ');
}
