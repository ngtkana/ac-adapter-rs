# 04. Push-Relabel with Gap Heuristic

Gap heuristic を導入。そのために各 $h$ に対して高さ $h$ である中間ノードの個数を管理します。

```
Benchmarking max_flow_random_n100000_m500000: Warming up for 3.0000 s
Warning: Unable to complete 100 samples in 5.0s. You may wish to increase target time to 15.4s, or reduce sample count to 30.
max_flow_random_n100000_m500000
                        time:   [152.36 ms 152.87 ms 153.41 ms]
                        change: [+2.7511% +3.2541% +3.7789%] (p = 0.00 < 0.05)
                        Performance has regressed.
Found 1 outliers among 100 measurements (1.00%)
  1 (1.00%) high mild

max_flow_misawa         time:   [214.62 µs 214.98 µs 215.36 µs]
                        change: [+19.625% +20.505% +21.270%] (p = 0.00 < 0.05)
                        Performance has regressed.
Found 8 outliers among 100 measurements (8.00%)
  1 (1.00%) low mild
  3 (3.00%) high mild
  4 (4.00%) high severe

Benchmarking max_flow_worst_gary_n3000: Warming up for 3.0000 s
Warning: Unable to complete 100 samples in 5.0s. You may wish to increase target time to 16.3s, or reduce sample count to 30.
max_flow_worst_gary_n3000
                        time:   [163.20 ms 163.56 ms 163.96 ms]
                        change: [+23.636% +23.987% +24.360%] (p = 0.00 < 0.05)
                        Performance has regressed.
Found 3 outliers among 100 measurements (3.00%)
  2 (2.00%) high mild
  1 (1.00%) high severe

```
