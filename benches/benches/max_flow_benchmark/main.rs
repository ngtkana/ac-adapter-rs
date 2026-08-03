use criterion::{black_box, criterion_group, criterion_main, Criterion};
use max_flow::MaxFlow;
use rand::{rngs::StdRng, Rng, SeedableRng};

/// ランダムグラフでのベンチマーク
/// 典型的なユースケースを想定
fn max_flow_random_graph(c: &mut Criterion) {
    c.bench_function("max_flow_random_n40000_m400000", |b| {
        // Setup: n=40000頂点、m=400000エッジのランダムグラフ（m/n=10でBFS回数が最大）
        let mut rng = StdRng::seed_from_u64(42);
        let n = 40_000;
        let m = 400_000;

        let mut edges = vec![];
        for _ in 0..m {
            let src = rng.gen_range(0..n);
            let tar = rng.gen_range(0..n);
            if src != tar {
                let cap = rng.gen_range(1..=100);
                edges.push((src, tar, cap));
            }
        }

        let source = 0;
        let sink = n - 1;

        b.iter(|| {
            let mut inst = MaxFlow::new();
            for &(src, tar, cap) in &edges {
                inst.add_edge(src, tar, cap);
            }
            black_box(inst.solve([source], [sink]))
        });
    });
}

/// MiSawaのキラーケースグラフでのベンチマーク
/// Dinicのcurrent_edge最適化が効かないと指数時間になる
/// https://gist.github.com/MiSawa/47b1d99c372daffb6891662db1a2b686 参考
fn max_flow_binary_tree_graph(c: &mut Criterion) {
    c.bench_function("max_flow_killer_case_depth200_layer200", |bencher| {
        // Setup: MiSawaのキラーケース構造
        // source(0) -> a(1), b_node(2) [容量1, 2]
        // b_node -> a [容量2]
        // a -> 各層layer_size頂点、depth層の中間層
        // 各層で各頂点から次層の全頂点へ容量3（layer_size^2本の辺/層）
        // 最終層 -> c -> sink [容量3]
        // current_edge最適化のバグがあるとO(layer_size^depth)時間になる
        let depth = 200;
        let layer_size = 200; // 各層の頂点数（2にするとバグのない実装では速すぎる）

        let source = 0;
        let a = 1;
        let b_node = 2;

        // 中間層の頂点数を計算
        // source, a, b_node + depth層×layer_size頂点/層 + c + sink
        let vertex_count = 3 + depth * layer_size + 2;
        let c_node = vertex_count - 2;
        let sink = vertex_count - 1;

        let mut edges = vec![];

        // source -> a, b_node
        edges.push((source, a, 1));
        edges.push((source, b_node, 2));

        // b_node -> a
        edges.push((b_node, a, 2));

        // a -> 第1層（layer_size頂点）
        let mut current_vertex = 3;
        let first_layer_start = current_vertex;
        for _ in 0..layer_size {
            edges.push((a, current_vertex, 3));
            current_vertex += 1;
        }

        // 各層間の接続（各層layer_size頂点、各頂点から次層の全頂点へ容量3）
        let mut layer_start = first_layer_start;
        for _ in 0..(depth - 1) {
            let next_layer_start = current_vertex;

            for i in 0..layer_size {
                let u = layer_start + i;
                // 各ノードから次層の全ノードへ容量3
                for j in 0..layer_size {
                    let v = next_layer_start + j;
                    edges.push((u, v, 3));
                }
            }

            layer_start = next_layer_start;
            current_vertex += layer_size;
        }

        // 最終層 -> c
        for i in 0..layer_size {
            let u = layer_start + i;
            edges.push((u, c_node, 3));
        }

        // c -> sink
        edges.push((c_node, sink, 3));

        bencher.iter(|| {
            let mut inst = MaxFlow::new();
            for &(src, tar, cap) in &edges {
                inst.add_edge(src, tar, cap);
            }
            black_box(inst.solve([source], [sink]))
        });
    });
}

criterion_group!(benches, max_flow_random_graph, max_flow_binary_tree_graph);
criterion_main!(benches);
