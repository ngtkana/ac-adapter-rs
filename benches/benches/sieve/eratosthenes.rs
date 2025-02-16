pub fn build_sieve(len: usize) -> Vec<bool> {
    if len < 2 {
        return vec![false; len];
    }
    let mut sieve = vec![true; len];
    sieve[0] = false;
    sieve[1] = false;
    for p in (2..).take_while(|p| p * p < len) {
        if sieve[p] {
            for i in (p * p..len).step_by(p) {
                sieve[i] = false;
            }
        }
    }
    sieve
}
