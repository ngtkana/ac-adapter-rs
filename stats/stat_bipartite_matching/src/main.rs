use rand::{Rng, SeedableRng, rngs::StdRng};
use stat_bipartite_matching::{Recorder, bipartite_matching};
use std::fmt::Display;

const ITERATION: usize = 100;
const EPOCH_LEN: usize = 20;

const N: usize = 100_000;
const M: usize = 300_000;

fn main() {
    let mut rng = StdRng::seed_from_u64(42);
    let mut epoch_count = vec![];
    let mut matching_count = vec![];
    let mut call_primal_count = vec![];
    let mut epochwise_call_primal_count = vec![vec![]; EPOCH_LEN];

    for _ in 0..ITERATION {
        let g = gen_case(&mut rng, N, M);

        let mut recorder = Recorder::default();
        let _h = bipartite_matching(&g, &mut recorder);

        epoch_count.push(recorder.aug_path_count.len() as f64);
        matching_count.push(recorder.aug_path_count.iter().sum::<usize>() as f64);
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

    println!("Condition: N = {N}, M = {M}");
    println!("Epoch count: {}", Stats(&epoch_count));
    println!("Matching count: {}", Stats(&matching_count));
    println!("Call primal count (sum): {}", Stats(&call_primal_count));
    for epoch in 0..EPOCH_LEN {
        println!(
            "Call primal count (epoch {epoch}): {}",
            Stats(&epochwise_call_primal_count[epoch])
        );
        println!();
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

fn gen_case(rng: &mut impl Rng, n: usize, m: usize) -> Vec<Vec<usize>> {
    let mut g = vec![vec![]; 2 * n];
    for _ in 0..m {
        let (i, j) = loop {
            let i = rng.gen_range(0..n);
            let j = rng.gen_range(n..2 * n);
            if g[i].contains(&j) {
                continue;
            }
            break (i, j);
        };
        g[i].push(j);
    }
    g
}
