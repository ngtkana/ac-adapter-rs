# 02. Push-Relabel with heap

Highest hight 戦略の push-relabel
Excess 頂点を heap で管理

```
Benchmarking max_flow_random_n100000_m500000: Warming up for 3.0000 s
Warning: Unable to complete 100 samples in 5.0s. You may wish to increase target time to 14.7s, or reduce sample count to 30.
max_flow_random_n100000_m500000
                        time:   [148.14 ms 148.79 ms 149.43 ms]
                        change: [+10.859% +11.466% +12.123%] (p = 0.00 < 0.05)
                        Performance has regressed.

max_flow_misawa         time:   [132.10 µs 132.37 µs 132.67 µs]
                        change: [+1464.4% +1472.3% +1479.1%] (p = 0.00 < 0.05)
                        Performance has regressed.
Found 5 outliers among 100 measurements (5.00%)
  2 (2.00%) high mild
  3 (3.00%) high severe

Benchmarking max_flow_worst_gary_n3000: Warming up for 3.0000 s
Warning: Unable to complete 100 samples in 5.0s. You may wish to increase target time to 11.5s, or reduce sample count to 40.
max_flow_worst_gary_n3000
                        time:   [114.20 ms 114.52 ms 114.85 ms]
                        change: [+44333% +44655% +44955%] (p = 0.00 < 0.05)
                        Performance has regressed.
```
