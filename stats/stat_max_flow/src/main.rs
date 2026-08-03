use rand::{rngs::StdRng, Rng, SeedableRng};
use stat_max_flow::{MaxFlow, Recorder};
use std::fmt::Display;

const ITERATION: usize = 100;
const EPOCH_LEN: usize = 20;

fn main() {
    let n = 1000;
    let ratios = [1, 2, 5, 10, 20, 50, 100];

    for &ratio in &ratios {
        let m = n * ratio;
        run_experiment(n, m);
        println!();
    }
}

fn run_experiment(n: usize, m: usize) {
    let mut rng = StdRng::seed_from_u64(42);
    let mut bfs_count = vec![];
    let mut flow_value = vec![];
    let mut call_primal_count = vec![];
    let mut epochwise_call_primal_count = vec![vec![]; EPOCH_LEN];

    for _ in 0..ITERATION {
        let edges = gen_case(&mut rng, n, m);

        let mut inst = MaxFlow::new();
        for &(src, tar, cap) in &edges {
            inst.add_edge(src, tar, cap);
        }

        let mut recorder = Recorder::default();
        let flow = inst.solve([0], [n - 1], &mut recorder);

        bfs_count.push(recorder.bfs_count.len() as f64);
        flow_value.push(flow as f64);
        call_primal_count.push(recorder.call_primal_count.iter().sum::<usize>() as f64);
        for epoch in 0..EPOCH_LEN {
            epochwise_call_primal_count[epoch].push(
                recorder
                    .call_primal_count
                    .get(epoch)
                    .map_or(0., |&x| x as f64),
            );
        }
    }

    println!("Condition: N = {n}, M = {m}, M/N = {}", m / n);
    println!("BFS count: {}", Stats(&bfs_count));
    println!("Flow value: {}", Stats(&flow_value));
    println!("Call primal count (sum): {}", Stats(&call_primal_count));
    for epoch in 0..EPOCH_LEN {
        let stats = &epochwise_call_primal_count[epoch];
        if stats.iter().any(|&x| x > 0.0) {
            println!(
                "Call primal count (epoch {epoch}): {}",
                Stats(stats)
            );
        }
    }
}

struct Stats<'a>(&'a [f64]);
impl Display for Stats<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self(items) = self;
        write!(
            f,
            "[min, average, max] = [{}, {}, {}]",
            min(items),
            average(items),
            max(items)
        )
    }
}

fn average(items: &[f64]) -> f64 {
    items.iter().sum::<f64>() / items.len() as f64
}

fn min(items: &[f64]) -> f64 {
    items.iter().fold(f64::INFINITY, |x, y| x.min(*y))
}

fn max(items: &[f64]) -> f64 {
    items.iter().fold(f64::NEG_INFINITY, |x, y| x.max(*y))
}

fn gen_case(rng: &mut impl Rng, n: usize, m: usize) -> Vec<(usize, usize, u64)> {
    let mut edges = vec![];
    for _ in 0..m {
        let src = rng.gen_range(0..n);
        let tar = rng.gen_range(0..n);
        if src != tar {
            let cap = rng.gen_range(1..=100);
            edges.push((src, tar, cap));
        }
    }
    edges
}
