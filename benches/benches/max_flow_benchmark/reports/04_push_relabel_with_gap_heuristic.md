# 04. Push-Relabel with Gap Heuristic

Gap heuristic を導入。そのために各 $h$ に対して高さ $h$ である中間ノードの個数を管理します。

```
Benchmarking max_flow_random_n100000_m500000: Warming up for 3.0000 s
Warning: Unable to complete 100 samples in 5.0s. You may wish to increase target time to 15.7s, or reduce sample count to 30.
max_flow_random_n100000_m500000
                        time:   [154.78 ms 156.07 ms 157.68 ms]
                        change: [+1.2197% +2.0981% +3.1435%] (p = 0.00 < 0.05)
                        Performance has regressed.
Found 2 outliers among 100 measurements (2.00%)
  1 (1.00%) high mild
  1 (1.00%) high severe

max_flow_misawa         time:   [8.6111 µs 8.6569 µs 8.7131 µs]
                        change: [-96.012% -95.986% -95.956%] (p = 0.00 < 0.05)
                        Performance has improved.
Found 13 outliers among 100 measurements (13.00%)
  6 (6.00%) high mild
  7 (7.00%) high severe

max_flow_worst_gary_n3000
                        time:   [254.57 µs 256.18 µs 257.92 µs]
                        change: [-99.844% -99.843% -99.842%] (p = 0.00 < 0.05)
                        Performance has improved.
Found 3 outliers among 100 measurements (3.00%)
  3 (3.00%) high mild
```
