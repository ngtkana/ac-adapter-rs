#[macro_export]
macro_rules! define_constant {
    ($(#[$attr:meta])? $vis:vis type $wrapper_type:ident: $value_type:ty = $value:expr;) => {
        $(#[$attr])?
        #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
        $vis struct $wrapper_type {}

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
