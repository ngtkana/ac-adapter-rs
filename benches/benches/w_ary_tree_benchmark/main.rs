use criterion::{black_box, criterion_group, criterion_main, Criterion};
use rand::SeedableRng;
use w_ary_tree::WAryTree;

// ベンチマーク前提条件:
// - constructor: 確率 1/2 のランダムビット列
// - predecessor_sparse: Fisher-Yates shuffleで確実に 1000 個配置
// - insert: 空の木から開始

const N: usize = 1 << 29; // 2^29 ≈ 500M elements
const Q: usize = 3_000_000; // 300万クエリ

#[derive(Clone)]
enum Query {
    Insert(usize),
    Predecessor(usize),
}

trait PredecessorSet {
    fn execute_predecessor(&mut self, queries: &[Query]);
    fn execute_insert(&mut self, queries: &[Query]);
}

impl PredecessorSet for WAryTree {
    fn execute_predecessor(&mut self, queries: &[Query]) {
        for query in queries {
            if let Query::Predecessor(x) = query {
                self.predecessor_including(*x);
            }
        }
    }

    fn execute_insert(&mut self, queries: &[Query]) {
        for query in queries {
            if let Query::Insert(x) = query {
                self.insert(*x);
            }
        }
    }
}

fn gen_bitstring(sparsity: f64) -> Vec<bool> {
    use rand::Rng;
    let mut rng = rand::rngs::StdRng::seed_from_u64(42);
    (0..N).map(|_| rng.gen_bool(sparsity)).collect()
}

/// Exact Count Sampling: 正確に count 個の異なる位置にビットを立てる
fn gen_bitstring_exact(n: usize, count: usize) -> Vec<bool> {
    use rand::seq::SliceRandom;
    let mut rng = rand::rngs::StdRng::seed_from_u64(42);
    let mut bits = vec![false; n];
    let mut indices: Vec<usize> = (0..n).collect();
    indices.shuffle(&mut rng);
    for i in 0..count.min(n) {
        bits[indices[i]] = true;
    }
    bits
}

fn gen_queries_predecessor(count: usize) -> Vec<Query> {
    use rand::Rng;
    let mut rng = rand::rngs::StdRng::seed_from_u64(42);
    (0..count)
        .map(|_| Query::Predecessor(rng.gen_range(0..N)))
        .collect()
}

fn gen_queries_insert(count: usize) -> Vec<Query> {
    use rand::Rng;
    let mut rng = rand::rngs::StdRng::seed_from_u64(42);
    (0..count)
        .map(|_| Query::Insert(rng.gen_range(0..N)))
        .collect()
}

fn benchmark_constructor(c: &mut Criterion) {
    let bits = gen_bitstring(0.5);
    c.bench_function("constructor", |b| {
        b.iter(|| {
            WAryTree::from_slice_of_bool(black_box(&bits))
        });
    });
}

fn benchmark_predecessor_sparse(c: &mut Criterion) {
    // 1000個をFisher-Yates shuffleで配置、構築は計測外
    let sparse_bits = gen_bitstring_exact(N, 1000);
    let queries = gen_queries_predecessor(Q);

    c.bench_function("predecessor_sparse", |b| {
        b.iter_batched(
            || WAryTree::from_slice_of_bool(&sparse_bits), // 計測外：構築
            |mut tree| {
                tree.execute_predecessor(black_box(&queries));
                black_box(tree)
            },
            criterion::BatchSize::SmallInput,
        );
    });
}

fn benchmark_insert(c: &mut Criterion) {
    let queries = gen_queries_insert(Q);

    c.bench_function("insert", |b| {
        b.iter_batched(
            || WAryTree::new(N), // 計測外：構築
            |mut tree| {
                tree.execute_insert(black_box(&queries));
                black_box(tree)
            },
            criterion::BatchSize::SmallInput,
        );
    });
}

criterion_group!(
    benches,
    benchmark_constructor,
    benchmark_predecessor_sparse,
    benchmark_insert
);
criterion_main!(benches);
