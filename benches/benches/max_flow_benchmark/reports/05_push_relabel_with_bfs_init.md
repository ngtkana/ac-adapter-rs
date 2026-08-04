# 05. Push-Relabel with BFS Init.

高さの初期化を次のように行います:

* source: $n$
* sink: $0$
* internal: $G_f$ における sink への距離

```
Benchmarking max_flow_random_n100000_m500000: Warming up for 3.0000 s
Warning: Unable to complete 100 samples in 5.0s. You may wish to increase target time to 14.8s, or reduce sample count to 30.
max_flow_random_n100000_m500000
                        time:   [152.36 ms 152.92 ms 153.52 ms]
                        change: [+169.33% +171.24% +173.02%] (p = 0.00 < 0.05)
                        Performance has regressed.
Found 2 outliers among 100 measurements (2.00%)
  2 (2.00%) high mild

max_flow_misawa         time:   [8.8099 µs 8.8233 µs 8.8371 µs]
                        change: [+1.5155% +2.2435% +2.9444%] (p = 0.00 < 0.05)
                        Performance has regressed.
Found 9 outliers among 100 measurements (9.00%)
  1 (1.00%) low mild
  5 (5.00%) high mild
  3 (3.00%) high severe

max_flow_worst_gary_n3000
                        time:   [256.64 µs 257.69 µs 258.85 µs]
                        change: [-0.5206% +0.2404% +1.0174%] (p = 0.54 > 0.05)
                        No change in performance detected.
Found 3 outliers among 100 measurements (3.00%)
  2 (2.00%) high mild
  1 (1.00%) high severe
```
