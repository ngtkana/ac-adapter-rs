/// `change_min` and `change_max`
pub trait ChangeMinMax: PartialOrd + Sized {
    fn change_min(&mut self, rhs: Self) {
        if *self > rhs {
            *self = rhs
        }
    }

    fn change_max(&mut self, rhs: Self) {
        if *self < rhs {
            *self = rhs
        }
    }
}

impl<T: PartialOrd + Sized> ChangeMinMax for T {}
