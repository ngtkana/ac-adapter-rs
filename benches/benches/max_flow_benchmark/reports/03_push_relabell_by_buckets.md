# 03. Push-Relabel by Buckets

高さの管理をヒープではなく buckets で行うようにしてみた。

```
Benchmarking max_flow_random_n100000_m500000: Warming up for 3.0000 s
Warning: Unable to complete 100 samples in 5.0s. You may wish to increase target time to 14.3s, or reduce sample count to 30.
max_flow_random_n100000_m500000
                        time:   [147.54 ms 148.05 ms 148.59 ms]
                        change: [-8.0118% -7.2124% -6.4679%] (p = 0.00 < 0.05)
                        Performance has improved.
Found 1 outliers among 100 measurements (1.00%)
  1 (1.00%) high mild

max_flow_misawa         time:   [177.50 µs 177.91 µs 178.38 µs]
                        change: [+10.641% +11.195% +11.979%] (p = 0.00 < 0.05)
                        Performance has regressed.
Found 10 outliers among 100 measurements (10.00%)
  7 (7.00%) high mild
  3 (3.00%) high severe

Benchmarking max_flow_worst_gary_n3000: Warming up for 3.0000 s

Warning: Unable to complete 100 samples in 5.0s. You may wish to increase target time to 13.3s, or reduce sample count to 30.
max_flow_worst_gary_n3000
                        time:   [131.69 ms 131.92 ms 132.18 ms]
                        change: [+10.460% +10.880% +11.292%] (p = 0.00 < 0.05)
                        Performance has regressed.
```
