use criterion::{
    criterion_group, criterion_main, AxisScale, BatchSize, BenchmarkId, Criterion,
    PlotConfiguration,
};
use rand::random;
use rmq::{CompoundTable, FastMinimum, LeastCommonAncestor, Prec, SparseTable};
use segtree::{MinInfo, Segtree};

////////////////////////////////////////////////////////////////////////////////
// Generators //////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

struct Spec {
    len: usize,
    value_limit: usize,
}

fn generate_random_seq(spec: &Spec) -> Vec<usize> {
    std::iter::repeat_with(|| random::<usize>() % spec.value_limit)
        .take(spec.len)
        .collect()
}

fn with_generate_random_seq(spec: Spec) -> impl FnMut() -> Vec<usize> {
    move || generate_random_seq(&spec)
}

fn generate_random_tree_by_parent_table(len: usize) -> Vec<usize> {
    let mut p = vec![0; len];
    for i in 1..len {
        p[i] = random::<usize>() % i;
    }
    p
}

fn generate_random_tree_by_adjacent_list(len: usize) -> Vec<Vec<usize>> {
    let p = generate_random_tree_by_parent_table(len);
    let mut g = vec![vec![]; len];
    for (u, v) in p.iter().copied().enumerate() {
        if u != v {
            g[u].push(v);
            g[v].push(u);
        }
    }
    g
}

fn generate_random_pm1_seq(len: usize) -> Vec<usize> {
    std::iter::successors(Some(len), |x| {
        Some(match random::<usize>() % 2 {
            0 => x + 1,
            1 => x - 1,
            _ => panic!(),
        })
    })
    .take(len)
    .collect()
}

fn generate_random_range(len: usize) -> std::ops::Range<usize> {
    let mut l = random::<usize>() % len;
    let mut r = random::<usize>() % len;
    if l > r {
        std::mem::swap(&mut l, &mut r);
    }
    r += 1;
    l..r
}

////////////////////////////////////////////////////////////////////////////////
// Counterpart Algorithms //////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
#[allow(dead_code)]
struct DoublingLCA {
    table: Vec<Vec<usize>>,
}

impl DoublingLCA {
    fn build(p: &[usize]) -> Self {
        let n = p.len();
        let h = n.next_power_of_two().trailing_zeros() as usize + 1;
        let mut table = vec![vec![0; n]; h];
        table[0].copy_from_slice(p);
        for i in 0..h - 1 {
            let (left, right) = table.split_at_mut(i + 1);
            let crr = &left[i];
            let nxt = &mut right[0];
            for j in 0..n {
                nxt[j] = crr[crr[j]];
            }
        }
        Self { table }
    }
}

////////////////////////////////////////////////////////////////////////////////
// Benchmarking ////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
fn bench_constructions(c: &mut Criterion) {
    let mut group = c.benchmark_group("Constructions");
    group.plot_config(PlotConfiguration::default().summary_scale(AxisScale::Logarithmic));
    for len in [10usize, 100usize, 1000usize, 10000usize, 100000usize].iter() {
        group.bench_with_input(
            BenchmarkId::new(
                "Fast Minimum (\
                Cartesian tree + Euler tour + \
                Decomposition into blocks + Sparse table + All-pattern precalculation)\
                ",
                len,
            ),
            len,
            |b, &len| {
                b.iter_batched(
                    with_generate_random_seq(Spec {
                        len,
                        value_limit: len,
                    }),
                    |seq| FastMinimum::build(&seq),
                    BatchSize::SmallInput,
                )
            },
        );
        group.bench_with_input(BenchmarkId::new("Sparse table", len), len, |b, &len| {
            b.iter_batched(
                with_generate_random_seq(Spec {
                    len,
                    value_limit: len,
                }),
                |seq| SparseTable::from_vec(seq),
                BatchSize::SmallInput,
            )
        });
        group.bench_with_input(BenchmarkId::new("Segtree", len), len, |b, &len| {
            b.iter_batched(
                with_generate_random_seq(Spec {
                    len,
                    value_limit: len,
                }),
                |seq| Segtree::<MinInfo<_>>::from(seq),
                BatchSize::SmallInput,
            )
        });
        group.bench_with_input(
            BenchmarkId::new(
                "Fast LCA (Euler tour + Decomposition into blocks \
                Sparse table + All-pattern precalculation)",
                len,
            ),
            len,
            |b, &len| {
                b.iter_batched(
                    || generate_random_tree_by_adjacent_list(len),
                    |tree| LeastCommonAncestor::from_tree(0, tree.as_slice()),
                    BatchSize::SmallInput,
                )
            },
        );
        group.bench_with_input(BenchmarkId::new("Doubling", len), len, |b, &len| {
            b.iter_batched(
                || generate_random_tree_by_parent_table(len),
                |p| DoublingLCA::build(&p),
                BatchSize::SmallInput,
            )
        });
        group.bench_with_input(
            BenchmarkId::new(
                "Compound table (\
                    Decomposition into blocks + Sparse table + All-pattern calculation)",
                len,
            ),
            len,
            |b, &len| {
                b.iter_batched(
                    || generate_random_pm1_seq(len),
                    |seq| CompoundTable::from_vec(seq),
                    BatchSize::SmallInput,
                )
            },
        );
    }
    group.finish();
}

fn bench_queries(c: &mut Criterion) {
    let mut group = c.benchmark_group("Queries");
    group.plot_config(PlotConfiguration::default().summary_scale(AxisScale::Logarithmic));
    for len in [10usize, 100usize, 1000usize, 10000usize, 100000usize].iter() {
        group.bench_with_input(
            BenchmarkId::new(
                "Fast Minimum (\
                Cartesian tree + Euler tour + \
                Decomposition into blocks + Sparse table + All-pattern precalculation)\
                ",
                len,
            ),
            len,
            |b, &len| {
                b.iter_batched(
                    || {
                        (
                            FastMinimum::build(&generate_random_seq(&Spec {
                                len,
                                value_limit: len,
                            })),
                            generate_random_range(len),
                        )
                    },
                    |(first_minimum, range)| first_minimum.query(range),
                    BatchSize::SmallInput,
                )
            },
        );
        group.bench_with_input(BenchmarkId::new("Sparse table", len), len, |b, &len| {
            b.iter_batched(
                || {
                    (
                        SparseTable::from_vec(generate_random_seq(&Spec {
                            len,
                            value_limit: len,
                        })),
                        generate_random_range(len),
                    )
                },
                |(sparse_table, range)| sparse_table.query(range),
                BatchSize::SmallInput,
            )
        });
        group.bench_with_input(BenchmarkId::new("Segtree", len), len, |b, &len| {
            b.iter_batched(
                || {
                    (
                        Segtree::<MinInfo<_>>::from(generate_random_seq(&Spec {
                            len,
                            value_limit: len,
                        })),
                        generate_random_range(len),
                    )
                },
                |(segtree, range)| segtree.fold(range.start, range.end),
                BatchSize::SmallInput,
            )
        });
        group.bench_with_input(
            BenchmarkId::new(
                "Compound table (\
                    Decomposition into blocks + Sparse table + All-pattern calculation)",
                len,
            ),
            len,
            |b, &len| {
                b.iter_batched(
                    || {
                        (
                            CompoundTable::from_vec(generate_random_pm1_seq(len)),
                            generate_random_range(len),
                        )
                    },
                    |(compound_table, range)| compound_table.query(range),
                    BatchSize::SmallInput,
                )
            },
        );
    }
    group.finish();
}

fn bench_all_pattern_precalculation(c: &mut Criterion) {
    let mut group = c.benchmark_group("All-pattern precalculation");
    group.plot_config(PlotConfiguration::default().summary_scale(AxisScale::Logarithmic));
    for len in [1usize, 3usize, 6usize, 10usize].iter() {
        group.bench_with_input(
            BenchmarkId::new("All-pattern precalculation", len),
            len,
            |b, &len| b.iter(|| Prec::with_len(len)),
        );
    }
    group.finish();
}

criterion_group!(
    benches,
    bench_constructions,
    bench_queries,
    bench_all_pattern_precalculation
);
criterion_main!(benches);
