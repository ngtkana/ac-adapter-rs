pub fn factorize(mut n: u64) -> Vec<(u64, u32)> {
    let mut vec = Vec::new();
    for p in 2.. {
        if n < p * p {
            break;
        }
        if n % p == 0 {
            let mut m = 0;
            while n % p == 0 {
                n /= p;
                m += 1;
            }
            vec.push((p, m));
        }
    }
    if n != 1 {
        vec.push((n, 1));
    }
    vec
}

#[cfg(test)]
mod tests {
    use super::factorize;

    #[test]
    fn test_factorize() {
        assert_eq!(factorize(1), vec![]);
        assert_eq!(factorize(2), vec![(2, 1)]);
        assert_eq!(factorize(3), vec![(3, 1)]);
        assert_eq!(factorize(4), vec![(2, 2)]);
        assert_eq!(factorize(5), vec![(5, 1)]);
        assert_eq!(factorize(6), vec![(2, 1), (3, 1)]);
    }
}
