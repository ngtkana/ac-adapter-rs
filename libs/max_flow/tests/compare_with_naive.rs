use max_flow::MaxFlow;
use rand::{Rng, SeedableRng, rngs::StdRng};

/// 最大流の正当性を検証する
/// 1. フロー保存則：source流出 = sink流入 = 戻り値、その他は流入=流出
/// 2. 容量制約：各辺で flow ≤ cap
/// 3. 逆辺の整合性：(src,tar,cap,flow) と (tar,src,cap,cap-flow) がペア
/// 4. 最適性（最大流最小カット定理）：sourceから残余グラフで到達可能な集合Sがsinkを含まず、
///    カット容量 Σ{cap(u,v) : u∈S, v∉S} = フロー値
fn verify_max_flow(n: usize, sources: &[usize], sinks: &[usize], inst: &MaxFlow, flow_value: u64) {
    let edges = &inst.edges;

    let mut kind = vec![NodeKind::Internal; n];
    for &x in sources {
        kind[x] = NodeKind::Source;
    }
    for &x in sinks {
        kind[x] = NodeKind::Sink;
    }

    // 隣接リストを構築（検証用）
    let mut g = vec![vec![]; n];
    for (i, e) in edges.iter().enumerate() {
        g[e.src].push(i);
    }

    // 1. フロー保存則の検証
    // 注意：add_edgeは順辺（偶数インデックス）と逆辺（奇数インデックス）をペアで追加する
    // 順辺のflowのみを使用してフローバランスを計算
    let mut flow_balance = vec![0i128; n];
    for i in (0..edges.len()).step_by(2) {
        let e = &edges[i];
        if e.flow > 0 {
            flow_balance[e.src] -= e.flow as i128;
            flow_balance[e.tar] += e.flow as i128;
        }
    }

    // sourceの流出量総和
    let source_outflow: i128 = sources.iter().map(|&s| -flow_balance[s]).sum();
    assert_eq!(
        source_outflow, flow_value as i128,
        "source流出量総和が戻り値と一致しません: {source_outflow} != {flow_value}",
    );

    // sinkの流入量総和
    let sink_inflow: i128 = sinks.iter().map(|&t| flow_balance[t]).sum();
    assert_eq!(
        sink_inflow, flow_value as i128,
        "sink流入量総和が戻り値と一致しません: {sink_inflow} != {flow_value}",
    );

    // その他の頂点は流入=流出
    let source_set: std::collections::HashSet<_> = sources.iter().copied().collect();
    let sink_set: std::collections::HashSet<_> = sinks.iter().copied().collect();
    for v in 0..n {
        if !source_set.contains(&v) && !sink_set.contains(&v) {
            assert_eq!(
                flow_balance[v], 0,
                "頂点{}でフロー保存則が満たされていません: balance={}",
                v, flow_balance[v]
            );
        }
    }

    // 2. 容量制約の検証
    for (i, e) in edges.iter().enumerate() {
        assert!(
            e.flow <= e.cap,
            "辺{}で容量制約違反: flow={} > cap={}",
            i,
            e.flow,
            e.cap
        );
    }

    // 3. 逆辺の整合性検証
    for i in (0..edges.len()).step_by(2) {
        let e1 = &edges[i];
        let e2 = &edges[i + 1];
        assert_eq!(e1.src, e2.tar, "辺{i}と{}でsrc/tar不一致", i + 1);
        assert_eq!(e1.tar, e2.src, "辺{i}と{}でtar/src不一致", i + 1);
        assert_eq!(e1.cap, e2.cap, "辺{i}と{}で容量不一致", i + 1);
        assert_eq!(
            e1.flow + e2.flow,
            e1.cap,
            "辺{i}と{}でflow整合性違反: {}+{}!={}",
            i + 1,
            e1.flow,
            e2.flow,
            e1.cap
        );
    }

    // 4. 最適性検証（最大流最小カット定理）
    // sourceから残余グラフでDFS
    let mut reachable = vec![false; n];
    let mut stack = sources.to_vec();
    for &s in sources {
        reachable[s] = true;
    }

    while let Some(v) = stack.pop() {
        for &i in &g[v] {
            let e = &edges[i];
            if e.flow < e.cap && !reachable[e.tar] {
                reachable[e.tar] = true;
                stack.push(e.tar);
            }
        }
    }

    // sinkが到達不可能であることを確認
    for &t in sinks {
        assert!(
            !reachable[t],
            "sink{t}が残余グラフで到達可能です（増加パスが存在）",
        );
    }

    // カット容量を計算（順辺のみ）
    let mut cut_capacity = 0u64;
    for i in (0..edges.len()).step_by(2) {
        let e = &edges[i];
        if reachable[e.src] && !reachable[e.tar] {
            cut_capacity += e.cap;
        }
    }

    assert_eq!(
        cut_capacity, flow_value,
        "カット容量がフロー値と一致しません: {cut_capacity} != {flow_value}",
    );
}

#[test]
fn test_random() {
    let mut rng = StdRng::seed_from_u64(42);

    for _ in 0..200 {
        let n = rng.gen_range(2..=4);
        let m = rng.gen_range(1..=(n * (n - 1) / 2).max(1));

        let mut inst = MaxFlow::new();
        for _ in 0..m {
            let src = rng.gen_range(0..n);
            let tar = rng.gen_range(0..n);
            let cap = rng.gen_range(1..1_000);
            inst.add_edge(src, tar, cap);
        }

        let n_sources = rng.gen_range(1..=(n - 1).min(3));
        let n_sinks = rng.gen_range(1..=(n - n_sources).min(3));

        let mut sources = vec![];
        let mut sinks = vec![];
        for _ in 0..n_sources {
            loop {
                let x = rng.gen_range(0..n);
                if sources.contains(&x) || sinks.contains(&x) {
                    continue;
                }
                sources.push(x);
                break;
            }
        }
        for _ in 0..n_sinks {
            loop {
                let x = rng.gen_range(0..n);
                if sources.contains(&x) || sinks.contains(&x) {
                    continue;
                }
                sinks.push(x);
                break;
            }
        }

        let flow_value = inst.solve(sources.clone(), sinks.clone());

        // フロー条件と最適性を検証
        verify_max_flow(n, &sources, &sinks, &inst, flow_value);
        eprintln!();
    }
}

#[test]
fn test_case_1_linear_path() {
    let mut inst = MaxFlow::new();
    inst.add_edge(0, 1, 10);
    inst.add_edge(1, 2, 5);
    let flow = inst.solve([0], [2]);
    assert_eq!(flow, 5);
    verify_max_flow(3, &[0], &[2], &inst, flow);
}

#[test]
fn test_case_2_parallel_paths() {
    let mut inst = MaxFlow::new();
    inst.add_edge(0, 1, 10);
    inst.add_edge(0, 2, 10);
    inst.add_edge(1, 3, 10);
    inst.add_edge(2, 3, 10);
    let flow = inst.solve([0], [3]);
    assert_eq!(flow, 20);
    verify_max_flow(4, &[0], &[3], &inst, flow);
}

#[test]
fn test_case_3_bottleneck() {
    let mut inst = MaxFlow::new();
    inst.add_edge(0, 1, 100);
    inst.add_edge(1, 2, 10);
    inst.add_edge(2, 3, 100);
    let flow = inst.solve([0], [3]);
    assert_eq!(flow, 10);
    verify_max_flow(4, &[0], &[3], &inst, flow);
}

#[test]
fn test_case_4_multi_source() {
    let mut inst = MaxFlow::new();
    inst.add_edge(0, 2, 10);
    inst.add_edge(1, 2, 15);
    inst.add_edge(2, 3, 30);
    let flow = inst.solve([0, 1], [3]);

    // デバッグ出力
    if flow != 25 {
        eprintln!("Expected flow: 25, got: {flow}");
        eprintln!("Edges after solve:");
        for (i, e) in inst.edges.iter().enumerate() {
            eprintln!(
                "  [{}] {}→{}: cap={}, flow={}",
                i, e.src, e.tar, e.cap, e.flow
            );
        }
    }

    assert_eq!(flow, 25);
    verify_max_flow(4, &[0, 1], &[3], &inst, flow);
}

#[test]
fn test_case_5_multi_sink() {
    let mut inst = MaxFlow::new();
    inst.add_edge(0, 1, 10);
    inst.add_edge(0, 2, 15);
    inst.add_edge(1, 3, 20);
    inst.add_edge(2, 4, 20);
    let flow = inst.solve([0], [3, 4]);
    assert_eq!(flow, 25);
    verify_max_flow(5, &[0], &[3, 4], &inst, flow);
}

#[test]
fn test_case_6_doc_example() {
    let mut inst = MaxFlow::new();
    inst.add_edge(0, 1, 20);
    inst.add_edge(0, 2, 10);
    inst.add_edge(1, 2, 10);
    inst.add_edge(1, 3, 10);
    inst.add_edge(2, 3, 20);
    let flow = inst.solve([0], [3]);
    assert_eq!(flow, 30);
    verify_max_flow(4, &[0], &[3], &inst, flow);
}

#[test]
fn test_case_7_requires_multiple_primal_calls_per_bfs() {
    // 同じBFSフェーズで同じsourceから複数回primalを呼ぶ必要があるケース
    //
    //   s0 --10--> v1 --1--> v3 --10--> t
    //          ^         /
    //         1|        /1
    //          |       v
    //         v2 -----+
    //
    // 最初のprimal(s0)がs0→v1→v3→tで1を流す
    // するとv1→v3が飽和し、label[v3]=usize::MAXに設定される
    // しかしv2→v3経由でまだ1流せる
    // 同じBFSフェーズでもう一度primal(s0)を呼ばないと、
    // s0→v1→v2→v3→tが流せない

    let mut inst = MaxFlow::new();
    inst.add_edge(0, 1, 10); // s0 -> v1
    inst.add_edge(1, 3, 1); // v1 -> v3
    inst.add_edge(1, 2, 1); // v1 -> v2
    inst.add_edge(2, 3, 1); // v2 -> v3
    inst.add_edge(3, 4, 10); // v3 -> t
    let flow = inst.solve([0], [4]);

    // デバッグ出力
    if flow != 2 {
        eprintln!("Expected flow: 2, got: {flow}");
        eprintln!("Edges after solve:");
        for (i, e) in inst.edges.iter().enumerate() {
            if i % 2 == 0 {
                eprintln!("  {}→{}: cap={}, flow={}", e.src, e.tar, e.cap, e.flow);
            }
        }
    }

    assert_eq!(flow, 2);
    verify_max_flow(5, &[0], &[4], &inst, flow);
}

#[test]
fn test_case_8_directly_connect_between_source_and_sink() {
    let mut inst = MaxFlow::new();
    inst.add_edge(0, 1, 42);
    let flow = inst.solve([0], [1]);
    assert_eq!(flow, 42);
    verify_max_flow(2, &[0], &[1], &inst, flow);
}

#[derive(PartialEq, Debug, Clone, Copy)]
enum NodeKind {
    Source,
    Sink,
    Internal,
}
