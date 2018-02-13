#![allow(dead_code)]
#![deny(non_upper_case_globals)]

static foo: isize = 1;
static mut bar: isize = 1;

fn main() {
    const b: usize = 1;
}

trait Foo {
    const camelCase: usize;
}

impl Foo for i32 {
    const camelCase: usize = 2;
}
