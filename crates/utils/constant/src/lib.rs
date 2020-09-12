#[macro_export]
macro_rules! define_constant {
    (type $wrapper_type:ident: $value_type:ty = $value:expr;) => {
        #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
        struct $wrapper_type {}

        impl constant::Constant for $wrapper_type {
            type Output = $value_type;
            const VALUE: Self::Output = $value;
        }
    };
}

pub trait Constant: Copy {
    type Output: Copy;
    const VALUE: Self::Output;
}
