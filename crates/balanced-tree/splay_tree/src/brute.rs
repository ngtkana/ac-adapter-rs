use {
    super::{LazyOps, SplayTree},
    itertools::Itertools,
    rand::{prelude::StdRng, Rng},
    std::{mem::swap, ops::Range},
};

#[derive(Clone, Debug, Default, Hash, PartialEq)]
pub struct Brute<O: LazyOps> {
    pub vec: Vec<O::Value>,
}
impl<O: LazyOps> Brute<O> {
    pub fn new() -> Self {
        Self { vec: Vec::new() }
    }
    pub fn len(&self) -> usize {
        self.vec.len()
    }
    pub fn get(&self, index: usize) -> Option<&O::Value> {
        let ans = self.vec.get(index);
        println!("get({}) = {:?}", index, ans);
        ans
    }
    pub fn fold(&self, range: Range<usize>) -> Option<O::Acc> {
        let Range { start, end } = range;
        let ans = self.vec[start..end]
            .iter()
            .map(O::proj)
            .fold1(|acc, x| O::op(&acc, &x));
        println!("fold({:?}) = {:?}", start..end, ans);
        ans
    }
    pub fn push_back(&mut self, value: O::Value) {
        self.vec.push(value.clone());
        println!("push_back({:?}); {:?}", &value, &self.vec);
    }
    pub fn push_front(&mut self, value: O::Value) {
        self.vec.insert(0, value.clone());
        println!("push_front({:?}); {:?}", &value, &self.vec);
    }
    pub fn insert(&mut self, i: usize, value: O::Value) {
        self.vec.insert(i, value.clone());
        println!("insert({}, {:?}); {:?}", i, &value, &self.vec);
    }
    pub fn pop_back(&mut self) -> Option<O::Value> {
        let ans = self.vec.pop();
        println!("pop_back() = {:?}; {:?}", &ans, &self.vec);
        ans
    }
    pub fn pop_front(&mut self) -> Option<O::Value> {
        let ans = if self.vec.is_empty() {
            None
        } else {
            Some(self.vec.remove(0))
        };
        println!("pop_front() = {:?}; {:?}", &ans, &self.vec);
        ans
    }
    pub fn delete(&mut self, i: usize) -> O::Value {
        let ans = self.vec.remove(i);
        println!("delete({}) = {:?}; {:?}", i, &ans, &self.vec);
        ans
    }
}

#[derive(Default)]
pub struct Spec {
    pub get: usize,
    pub fold: usize,
    pub push_back: usize,
    pub push_front: usize,
    pub insert: usize,
    pub pop_back: usize,
    pub pop_front: usize,
    pub delete: usize,
}

pub fn test_case<O: LazyOps, F>(rng: &mut StdRng, random_value: F, spec: &Spec)
where
    O::Value: PartialEq,
    O::Acc: PartialEq,
    F: Fn(&mut StdRng) -> O::Value,
{
    println!("New test case");
    let mut splay = SplayTree::<O>::new();
    let mut brute = Brute::<O>::new();
    let dice_max = spec.get
        + spec.fold
        + spec.push_back
        + spec.push_front
        + spec.insert
        + spec.pop_back
        + spec.pop_front;
    for _ in 0..200 {
        let mut dice = rng.gen_range(0..dice_max);

        // get
        if dice < spec.get {
            let i = rng.gen_range(0..=brute.len());
            let expected = brute.get(i);
            let result = splay.get(i);
            assert_eq!(result, expected);
            continue;
        }
        dice -= spec.get;

        // fold
        if dice < spec.fold {
            let mut l = rng.gen_range(0..=brute.len() + 1);
            let mut r = rng.gen_range(0..=brute.len());
            if l > r {
                swap(&mut l, &mut r);
                r -= 1;
            }
            let expected = brute.fold(l..r);
            let result = splay.fold(l..r);
            assert_eq!(expected, result);
            continue;
        }
        dice -= spec.fold;

        // push_back
        if dice < spec.push_back {
            let value = random_value(rng);
            brute.push_back(value.clone());
            splay.push_back(value.clone());
            continue;
        }
        dice -= spec.push_back;

        // push_front
        if dice < spec.push_front {
            let value = random_value(rng);
            brute.push_front(value.clone());
            splay.push_front(value.clone());
            continue;
        }
        dice -= spec.push_front;

        // insert
        if dice < spec.insert {
            let i = rng.gen_range(0..=brute.len());
            let value = random_value(rng);
            brute.insert(i, value.clone());
            splay.insert(i, value.clone());
            continue;
        }
        dice -= spec.insert;

        // pop_back
        if dice < spec.pop_back {
            let expected = brute.pop_back();
            let result = splay.pop_back();
            assert_eq!(expected, result);
            continue;
        }
        dice -= spec.pop_back;

        // pop_front
        if dice < spec.pop_front {
            let expected = brute.pop_front();
            let result = splay.pop_front();
            assert_eq!(expected, result);
            continue;
        }
        dice -= spec.pop_front;

        // delete
        if dice < spec.delete {
            let i = rng.gen_range(0..brute.len());
            if i < brute.len() {
                let expected = brute.delete(i);
                let result = splay.delete(i);
                assert_eq!(expected, result);
            }
            continue;
        }
        unreachable!();
    }
}
