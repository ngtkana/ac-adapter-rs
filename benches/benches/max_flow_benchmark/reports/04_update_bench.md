# 04. Update bench

辺のランダム生成と `add_edge` の時間が含まれてしまっていたので、`b.iter_batched` を使って測定対象から排除

```
Benchmarking max_flow_random_n100000_m500000: Warming up for 3.0000 s
Warning: Unable to complete 100 samples in 5.0s. You may wish to increase target time to 5.3s, or reduce s
ample count to 90.
Benchmarking max_flow_random_n100000_m500000: Collecting 100 samples in estimated 5.3145 s (100 iterations
max_flow_random_n100000_m500000
                        time:   [35.015 ms 35.256 ms 35.505 ms]
                        change: [-22.281% -21.571% -20.849%] (p = 0.00 < 0.05)
                        Performance has improved.
Found 3 outliers among 100 measurements (3.00%)
  3 (3.00%) high mild

max_flow_misawa         time:   [61.950 µs 62.104 µs 62.288 µs]
                        change: [-0.3588% +0.0425% +0.4572%] (p = 0.83 > 0.05)
                        No change in performance detected.
Found 8 outliers among 100 measurements (8.00%)
  5 (5.00%) high mild
  3 (3.00%) high severe

Benchmarking max_flow_worst_gary_n3000: Warming up for 3.0000 s
Warning: Unable to complete 100 samples in 5.0s. You may wish to increase target time to 13.0s, or reduce 
sample count to 30.
max_flow_worst_gary_n3000
                        time:   [128.71 ms 129.26 ms 129.81 ms]
                        change: [-1.7158% -1.1180% -0.4863%] (p = 0.00 < 0.05)
                        Change within noise threshold.
```
