pub fn build_sieve(len: usize) -> Vec<bool> {
    let mut sieve = vec![true; len];
    sieve[0] = false;
    sieve[1] = false;
    for p in (4..len).step_by(2) {
        sieve[p] = false;
    }
    for p in (9..len).step_by(3) {
        sieve[p] = false;
    }
    let mut p = 5;
    loop {
        {
            let mut i = p * p;
            loop {
                sieve[i] = false;
                i += 2 * p;
                if i >= len {
                    break;
                }
                sieve[i] = false;
                i += 4 * p;
                if i >= len {
                    break;
                }
            }
        }
        p += 2;
        if p * p >= len {
            break;
        }
        {
            let mut i = p * p;
            loop {
                sieve[i] = false;
                i += 4 * p;
                if i >= len {
                    break;
                }
                sieve[i] = false;
                i += 2 * p;
                if i >= len {
                    break;
                }
            }
        }
        p += 4;
        if p * p >= len {
            break;
        }
    }
    sieve
}
