use std::fmt::{self, Debug, Formatter};

/// A foldable queue data structure by SWAG algorithm.
///
/// You can use [`push`](SwagQueue::push), [`pop`](SwagQueue::pop), and [`fold`](SwagQueue::fold) operation on a sequence.
///
#[derive(Clone, PartialEq)]
pub struct SwagQueue<T, Op, Identity> {
    back: Vec<T>,
    front: Vec<T>,
    fold: T,
    op: Op,
    identity: Identity,
}
impl<T, Op, Identity> Debug for SwagQueue<T, Op, Identity>
where
    T: Debug,
{
    fn fmt(&self, w: &mut Formatter) -> fmt::Result {
        let Self {
            back, front, fold, ..
        } = self;
        w.debug_struct("SwagQueue")
            .field("back", back)
            .field("front", front)
            .field("fold", fold)
            .finish()
    }
}
impl<T, Op, Identity> SwagQueue<T, Op, Identity>
where
    T: Clone + Debug,
    Op: Fn(T, T) -> T,
    Identity: Fn() -> T,
{
    /// Makes a new empty `SwagQueue`
    ///
    /// Does not allocate anything on its own.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swag::SwagQueue;
    ///
    /// let mut queue = SwagQueue::new(std::ops::Add::add, || 0);
    ///
    /// queue.push(10);
    /// queue.push(20);
    /// assert_eq!(queue.fold(), 30);
    /// ```
    pub fn new(op: Op, identity: Identity) -> Self {
        Self {
            back: Vec::new(),
            front: Vec::new(),
            fold: identity(),
            op,
            identity,
        }
    }

    /// Appends an element to the back of a collection.
    ///
    /// # Examples
    ///
    /// ```
    /// use swag::SwagQueue;
    ///
    /// let mut queue = SwagQueue::new(std::ops::Add::add, || 0);
    ///
    /// queue.push(10);
    /// queue.push(20);
    /// assert_eq!(queue.fold(), 30);
    /// ```
    pub fn push(&mut self, x: T) {
        let Self { fold, back, op, .. } = self;
        back.push(x.clone());
        *fold = op(fold.clone(), x);
    }

    /// Removes the front element from a swag, returning `Some(())` if it is nonempy while `None`,
    /// otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use swag::SwagQueue;
    ///
    /// let mut queue = SwagQueue::new(std::ops::Add::add, || 0);
    ///
    /// queue.push(10);
    /// queue.push(20);
    /// assert_eq!(queue.fold(), 30);
    /// queue.pop();
    /// assert_eq!(queue.fold(), 20);
    /// queue.push(30);
    /// assert_eq!(queue.fold(), 50);
    /// ```
    pub fn pop(&mut self) -> Option<()> {
        let Self {
            front,
            op,
            back,
            identity,
            fold,
            ..
        } = self;
        if front.is_empty() {
            while let Some(x) = back.pop() {
                let x = if let Some(y) = front.last() {
                    op(x, y.clone())
                } else {
                    x
                };
                front.push(x);
            }
            *fold = identity();
        }
        front.pop().map(|_| ())
    }

    /// Removes the front element from a swag, returning `Some(())` if it is nonempy while `None`,
    /// otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use swag::SwagQueue;
    ///
    /// let mut queue = SwagQueue::new(std::ops::Add::add, || 0);
    ///
    /// queue.push(10);
    /// queue.push(20);
    /// assert_eq!(queue.fold(), 30);
    /// queue.pop();
    /// assert_eq!(queue.fold(), 20);
    /// queue.push(30);
    /// assert_eq!(queue.fold(), 50);
    /// ```
    pub fn fold(&self) -> T {
        let Self {
            front, op, fold, ..
        } = self;
        front
            .last()
            .map_or_else(|| fold.clone(), |f| op(f.clone(), fold.clone()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::prelude::*;
    use std::collections::VecDeque;

    #[test]
    fn test_hand() {
        let mut test = Test::new(
            |s, t| s.chars().chain(t.chars()).collect::<String>(),
            String::new,
        );
        test.fold();
        test.push("a".to_owned());
        test.pop();
        test.push("a".to_owned());
        test.push("b".to_owned());
        test.push("c".to_owned());
        test.pop();
        test.push("d".to_owned());
        test.push("e".to_owned());
        test.push("f".to_owned());
        test.pop();
    }

    #[test]
    fn test_rand_strcat() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..5 {
            let mut test = Test::new(
                |s, t| s.chars().chain(t.chars()).collect::<String>(),
                String::new,
            );
            for _ in 0..100 {
                match rng.gen_range(0..3) {
                    0 => test.push(
                        (rand::distributions::Alphanumeric.sample(&mut rng) as char).to_string(),
                    ),
                    1 => test.pop(),
                    2 => test.fold(),
                    _ => unreachable!(),
                }
            }
        }
    }

    #[test]
    fn test_rand_add() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..5 {
            let mut test = Test::new(std::ops::Add::add, || 0);
            for _ in 0..10_000 {
                match rng.gen_range(0..3) {
                    0 => test.push(rng.gen_range(0..1000)),
                    1 => test.pop(),
                    2 => test.fold(),
                    _ => unreachable!(),
                }
            }
        }
    }

    struct Test<T, Op, Identity> {
        swag: SwagQueue<T, Op, Identity>,
        vec: VecDeque<T>,
    }
    impl<T, Op, Identity> Test<T, Op, Identity>
    where
        T: Clone + Debug + PartialEq,
        Op: Fn(T, T) -> T,
        Identity: Fn() -> T,
    {
        pub fn new(op: Op, identity: Identity) -> Self {
            Self {
                swag: SwagQueue::new(op, identity),
                vec: VecDeque::new(),
            }
        }

        pub fn push(&mut self, x: T) {
            println!("push {:?}, now = {:?}", &x, &self.swag);
            self.swag.push(x.clone());
            self.vec.push_back(x);
        }

        pub fn pop(&mut self) {
            println!("pop, now = {:?}", &self.swag);
            let result = self.swag.pop();
            let expected = self.vec.pop_front().map(|_| ());
            assert_eq!(result, expected);
        }

        pub fn fold(&self) {
            println!("fold, now = {:?}", &self.swag);
            let result = self.swag.fold();
            let expected = self
                .vec
                .iter()
                .cloned()
                .fold((self.swag.identity)(), |x, y| (self.swag.op)(x, y));
            assert_eq!(result, expected);
        }
    }
}
