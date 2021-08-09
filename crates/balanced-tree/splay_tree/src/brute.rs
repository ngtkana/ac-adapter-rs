use {
    super::{LazyOps, SplayTree},
    itertools::Itertools,
    rand::{prelude::StdRng, Rng},
    std::collections::BTreeMap,
    std::{mem::swap, ops::Range},
};

#[derive(Clone, Debug, Default, Hash, PartialEq)]
pub struct Brute<O: LazyOps> {
    pub vec: Vec<O::Value>,
}
impl<O: LazyOps> Brute<O> {
    pub fn len(&self) -> usize {
        let ans = self.vec.len();
        ans
    }
    pub fn insert(&mut self, i: usize, value: O::Value) {
        self.vec.insert(i, value.clone());
        println!("insert({}, {:?}); {:?}", i, &value, &self.vec);
    }
    pub fn delete(&mut self, i: usize) -> O::Value {
        let ans = self.vec.remove(i);
        println!("delete({}) = {:?}; {:?}", i, &ans, &self.vec);
        ans
    }
    pub fn reverse(&mut self, range: Range<usize>) {
        let Range { start, end } = range;
        self.vec[start..end].reverse();
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
    pub fn act(&mut self, range: Range<usize>, lazy: O::Lazy) {
        let Range { start, end } = range;
        self.vec[start..end]
            .iter_mut()
            .for_each(|value| O::act_value(&lazy, value));
        println!("act({:?}, {:?}); {:?}", start..end, &lazy, &self.vec);
    }
}

pub struct Spec {
    map: BTreeMap<&'static str, usize>,
    sum: usize,
}
impl Spec {
    pub fn new() -> Self {
        Self {
            map: BTreeMap::new(),
            sum: 0,
        }
    }
    pub fn add(&mut self, name: &'static str, weight: usize) {
        *self.map.entry(name).or_insert(0) += weight;
        self.sum += weight;
    }
}

pub fn test_case<O: LazyOps, F, G>(rng: &mut StdRng, random_value: F, random_lazy: G, spec: &Spec)
where
    F: Fn(&mut StdRng) -> O::Value,
    G: Fn(&mut StdRng) -> O::Lazy,
    O::Value: PartialEq,
    O::Acc: PartialEq,
{
    Test {
        rng,
        random_value,
        random_lazy,
    }
    .run::<O>(spec)
}

struct Test<'a, F, G> {
    pub rng: &'a mut StdRng,
    pub random_value: F,
    pub random_lazy: G,
}
impl<F, G> Test<'_, F, G> {
    fn run<O: LazyOps>(&mut self, spec: &Spec)
    where
        F: Fn(&mut StdRng) -> O::Value,
        G: Fn(&mut StdRng) -> O::Lazy,
        O::Value: PartialEq,
        O::Acc: PartialEq,
    {
        println!("New test case");
        let a = Vec::new();
        let mut splay = a.iter().cloned().collect::<SplayTree<O>>();
        let mut brute = Brute::<O> { vec: a };
        for _ in 0..200 {
            let mut dice = self.rng.gen_range(0..spec.sum);
            'MAP: for (name, &weight) in &spec.map {
                if dice < weight {
                    self.query(name, &mut brute, &mut splay);
                    break 'MAP;
                }
                dice -= weight;
            }
        }
    }
    fn query<O: LazyOps>(
        &mut self,
        name: &'static str,
        brute: &mut Brute<O>,
        splay: &mut SplayTree<O>,
    ) where
        F: Fn(&mut StdRng) -> O::Value,
        G: Fn(&mut StdRng) -> O::Lazy,
        O::Value: PartialEq,
        O::Acc: PartialEq,
    {
        match name {
            "insert" => {
                let i = self.rng.gen_range(0..=brute.len());
                let value = (self.random_value)(self.rng);
                brute.insert(i, value.clone());
                splay.insert(i, value.clone());
            }
            "delete" => {
                if brute.len() != 0 {
                    let i = self.rng.gen_range(0..brute.len());
                    let expected = brute.delete(i);
                    let result = splay.delete(i);
                    assert_eq!(expected, result);
                }
            }
            "reverse" => {
                let mut l = self.rng.gen_range(0..=brute.len() + 1);
                let mut r = self.rng.gen_range(0..=brute.len());
                if l > r {
                    swap(&mut l, &mut r);
                    r -= 1;
                }
                brute.reverse(l..r);
                splay.reverse(l..r);
            }
            "act" => {
                let mut l = self.rng.gen_range(0..=brute.len() + 1);
                let mut r = self.rng.gen_range(0..=brute.len());
                if l > r {
                    swap(&mut l, &mut r);
                    r -= 1;
                }
                let lazy = (self.random_lazy)(self.rng);
                let expected = brute.act(l..r, lazy.clone());
                let result = splay.act(l..r, lazy);
                assert_eq!(expected, result);
            }
            "fold" => {
                let mut l = self.rng.gen_range(0..=brute.len() + 1);
                let mut r = self.rng.gen_range(0..=brute.len());
                if l > r {
                    swap(&mut l, &mut r);
                    r -= 1;
                }
                let expected = brute.fold(l..r);
                let result = splay.fold(l..r);
                assert_eq!(expected, result);
            }
            _ => unreachable!(),
        }
    }
}
