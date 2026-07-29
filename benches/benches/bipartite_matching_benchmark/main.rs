use bipartite_matching::bipartite_matching;
use criterion::black_box;
use criterion::criterion_group;
use criterion::criterion_main;
use criterion::Criterion;
use rand::seq::SliceRandom;
use rand::{rngs::StdRng, Rng, SeedableRng};

fn bipartite_matching_bench_1m(c: &mut Criterion) {
    c.bench_function("bipartite_matching_V1M_E1M", |b| {
        let mut rng = StdRng::seed_from_u64(42);

        // Bipartite graph: 500k left nodes, 500k right nodes (total n=1M)
        let n = 1_000_000;
        let left_count = 500_000;
        let edge_count = 1_000_000;

        // Mark which nodes are in the left partition
        let mut is_left = vec![false; n];
        is_left[..left_count].fill(true);
        is_left.shuffle(&mut rng);

        let mut g = vec![vec![]; n];
        let mut edges_added = 0;

        while edges_added < edge_count {
            let i = rng.gen_range(0..n);
            let j = rng.gen_range(0..n);

            // Ensure i is left, j is right, and edge doesn't already exist
            if (is_left[i] && !is_left[j]) && !g[i].contains(&j) {
                g[i].push(j);
                edges_added += 1;
            }
        }

        b.iter(|| bipartite_matching(black_box(&g)));
    });
}

criterion_group!(benches, bipartite_matching_bench_1m);
criterion_main!(benches);
