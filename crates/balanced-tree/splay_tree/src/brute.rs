use std::iter::repeat_with;

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
        let ans = self.vec.len();
        ans
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
    pub fn act(&mut self, range: Range<usize>, lazy: O::Lazy) {
        let Range { start, end } = range;
        self.vec[start..end]
            .iter_mut()
            .for_each(|value| O::act_value(&lazy, value));
        println!("act({:?}, {:?}); {:?}", start..end, &lazy, &self.vec);
    }
}

#[derive(Default)]
pub struct Spec {
    pub len: usize,
    pub get: usize,
    pub fold: usize,
    pub push_back: usize,
    pub push_front: usize,
    pub insert: usize,
    pub pop_back: usize,
    pub pop_front: usize,
    pub delete: usize,
    pub act: usize,
}

pub fn test_case<O: LazyOps, F, G>(rng: &mut StdRng, random_value: F, random_lazy: G, spec: &Spec)
where
    O::Value: PartialEq,
    O::Acc: PartialEq,
    F: Fn(&mut StdRng) -> O::Value,
    G: Fn(&mut StdRng) -> O::Lazy,
{
    println!("New test case");
    let a = repeat_with(|| random_value(rng))
        .take(4)
        .collect::<Vec<_>>();
    let mut splay = a.iter().cloned().collect::<SplayTree<O>>();
    let mut brute = Brute::<O> { vec: a };
    let dice_max = spec.len
        + spec.get
        + spec.fold
        + spec.push_back
        + spec.push_front
        + spec.insert
        + spec.pop_back
        + spec.delete
        + spec.act;
    for _ in 0..200 {
        let mut dice = rng.gen_range(0..dice_max);

        // len
        if dice < spec.len {
            let expected = brute.len();
            let result = splay.len();
            assert_eq!(result, expected);
            continue;
        }
        dice -= spec.len;

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
            if brute.len() != 0 {
                let i = rng.gen_range(0..brute.len());
                let expected = brute.delete(i);
                let result = splay.delete(i);
                assert_eq!(expected, result);
            }
            continue;
        }
        dice -= spec.delete;

        // act
        if dice < spec.act {
            let mut l = rng.gen_range(0..=brute.len() + 1);
            let mut r = rng.gen_range(0..=brute.len());
            if l > r {
                swap(&mut l, &mut r);
                r -= 1;
            }
            let lazy = random_lazy(rng);
            brute.act(l..r, lazy.clone());
            splay.act(l..r, lazy.clone());
            continue;
        }
        unreachable!();
    }
}
