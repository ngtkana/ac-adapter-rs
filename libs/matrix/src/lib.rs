use std::ops::Mul;

pub trait Scalar {
    const CONST_0: Self;
    const CONST_1: Self;

    fn fma_assign(a: &mut Self, b: &Self, c: &Self);
}

#[derive(Clone)]
pub struct Matrix<T> {
    pub items: Vec<T>,
    pub width: usize,
}

impl<T> Matrix<T> {
    pub fn height(&self) -> usize {
        self.items.len() / self.width
    }
}

impl<T: Scalar> Matrix<T> {
    pub fn zeros(height: usize, width: usize) -> Self {
        Self {
            items: (0..height * width).map(|_| T::CONST_0).collect::<Vec<_>>(),
            width,
        }
    }

    pub fn identity(size: usize) -> Self {
        let mut result = Self::zeros(size, size);
        for i in 0..size {
            result[(i, i)] = T::CONST_1;
        }
        result
    }

    pub fn pow(self, exp: u64) -> Self {
        let mut result = Self::identity(self.width);
        result.mul_pow_assign(self, exp);
        result
    }

    pub fn mul_pow_assign(&mut self, mut other: Self, mut exp: u64) {
        if exp == 0 {
            return;
        }
        while exp != 1 {
            if exp & 1 == 1 {
                *self = &*self * &other;
            }
            other = &other * &other;
            exp >>= 1;
        }
        *self = &*self * &other;
    }

    pub fn companion<I>(bottom: I) -> Self
    where
        I: IntoIterator<Item = T>,
        I::IntoIter: ExactSizeIterator,
    {
        let mut iter = bottom.into_iter();
        let size = iter.len();
        assert!(size > 0);
        let mut result = Self::zeros(size, size);
        for i in 1..size {
            result[(i, i - 1)] = T::CONST_1;
        }
        for i in 0..size {
            result[(i, size - 1)] = iter.next().unwrap();
        }
        assert!(iter.next().is_none());
        result
    }
}

impl<T> std::ops::Index<usize> for Matrix<T> {
    type Output = [T];

    fn index(&self, i: usize) -> &Self::Output {
        &self.items[i * self.width..(i + 1) * self.width]
    }
}

impl<T> std::ops::IndexMut<usize> for Matrix<T> {
    fn index_mut(&mut self, i: usize) -> &mut Self::Output {
        &mut self.items[i * self.width..(i + 1) * self.width]
    }
}

impl<T> std::ops::Index<(usize, usize)> for Matrix<T> {
    type Output = T;

    fn index(&self, (i, j): (usize, usize)) -> &Self::Output {
        &self.items[i * self.width + j]
    }
}

impl<T> std::ops::IndexMut<(usize, usize)> for Matrix<T> {
    fn index_mut(&mut self, (i, j): (usize, usize)) -> &mut Self::Output {
        &mut self.items[i * self.width + j]
    }
}

impl<'a, T: Scalar> Mul<&'a Matrix<T>> for &'a Matrix<T> {
    type Output = Matrix<T>;

    fn mul(self, rhs: &'a Matrix<T>) -> Self::Output {
        assert_eq!(self.width * rhs.width, rhs.items.len());
        let mut result = Matrix::zeros(self.height(), rhs.width);
        for i in 0..self.height() {
            for j in 0..self.width {
                for k in 0..rhs.width {
                    T::fma_assign(&mut result[(i, k)], &self[(i, j)], &rhs[(j, k)]);
                }
            }
        }
        result
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[derive(Clone, Debug)]
    struct Int(i32);
    impl Scalar for Int {
        const CONST_0: Self = Self(0);
        const CONST_1: Self = Self(1);

        fn fma_assign(a: &mut Self, b: &Self, c: &Self) {
            a.0 += b.0 * c.0;
        }
    }
    impl PartialEq<i32> for Int {
        fn eq(&self, other: &i32) -> bool {
            self.0 == *other
        }
    }
    impl Int {
        fn vec<I>(iter: I) -> Vec<Self>
        where
            I: IntoIterator<Item = i32>,
        {
            iter.into_iter().map(Self).collect()
        }
    }

    #[test]
    fn test_matrix_mul_typed_int() {
        let a = Matrix {
            items: Int::vec([1, 2, 3, 4]),
            width: 2,
        };
        let b = Matrix {
            items: Int::vec([5, 6, 7, 8]),
            width: 2,
        };
        let c = &a * &b;
        assert_eq!(c.items, [19, 22, 43, 50]);
        assert_eq!(c.width, 2);
    }

    #[test]
    fn test_matrix_pow_typed_int() {
        let a = Matrix {
            items: Int::vec([1, 2, 3, 4]),
            width: 2,
        };

        let b = a.clone().pow(0);
        assert_eq!(b.items, [1, 0, 0, 1]);
        assert_eq!(b.width, 2);

        let b = a.clone().pow(1);
        assert_eq!(b.items, [1, 2, 3, 4]);
        assert_eq!(b.width, 2);

        let b = a.clone().pow(2);
        assert_eq!(b.items, [7, 10, 15, 22]);
        assert_eq!(b.width, 2);

        let b = a.clone().pow(3);
        assert_eq!(b.items, [37, 54, 81, 118]);
        assert_eq!(b.width, 2);
    }
}
