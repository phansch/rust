use std::ffi::CString;

mod foo {
    fn bar() {}
}

fn main() {
    let _ = Cstring::new("hello").unwrap();
    //~^ ERROR failed to resolve: use of undeclared type or module `Cstring`

    let _ = CStRiNg::new("hello").unwrap();
    //~^ ERROR failed to resolve: use of undeclared type or module `CStRiNg`

    let _ = cStrIng::new("hello").unwrap();
    //~^ ERROR failed to resolve: use of undeclared type or module `cStrIng`

    let _ = foO::bar();
    //~^ ERROR failed to resolve: use of undeclared type or module `foO`
}
