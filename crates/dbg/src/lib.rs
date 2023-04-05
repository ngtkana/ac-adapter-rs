//! Provides a macro [lg]

#[macro_export]
macro_rules! lg {
    (@contents $head:expr $(,)?) => {
        match $head {
            head => {
                eprintln!(" {} = {:?}", stringify!($head), &head);
            }
        }
    };
    (@contents $head:expr $(,$tail:expr)+ $(,)?) => {
        match $head {
            head => {
                eprint!(" {} = {:?},", stringify!($head), &head);
            }
        }
        $crate::lg!(@contents $($tail),*);
    };
    ($($expr:expr),* $(,)?) => {
        eprint!("[{}:{}]", file!(), line!());
        $crate::lg!(@contents $($expr),*)
    };
}
