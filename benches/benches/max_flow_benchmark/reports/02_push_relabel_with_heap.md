# 02. Push-Relabel with heap

Highest hight 戦略の push-relabel
Excess 頂点を heap で管理

```
Benchmarking max_flow_random_n100000_m500000: Warming up for 3.0000 s
Warning: Unable to complete 100 samples in 5.0s. You may wish to increase target time to 15.5s, or reduce sample count to 30.
max_flow_random_n100000_m500000
                        time:   [158.43 ms 159.56 ms 160.82 ms]
                        change: [+0.0923% +0.8247% +1.6970%] (p = 0.05 < 0.05)
                        Change within noise threshold.
Found 9 outliers among 100 measurements (9.00%)
  4 (4.00%) high mild
  5 (5.00%) high severe

max_flow_misawa         time:   [160.31 µs 160.41 µs 160.52 µs]
                        change: [-0.9193% -0.6557% -0.3843%] (p = 0.00 < 0.05)
                        Change within noise threshold.
Found 6 outliers among 100 measurements (6.00%)
  2 (2.00%) high mild
  4 (4.00%) high severe

Benchmarking max_flow_worst_gary_n3000: Warming up for 3.0000 s
Warning: Unable to complete 100 samples in 5.0s. You may wish to increase target time to 11.8s, or reduce sample count to 40.
max_flow_worst_gary_n3000
                        time:   [118.60 ms 118.98 ms 119.37 ms]
                        change: [-1.8549% -1.4329% -0.9578%] (p = 0.00 < 0.05)
                        Change within noise threshold.
Found 1 outliers among 100 measurements (1.00%)
  1 (1.00%) high mild
```
