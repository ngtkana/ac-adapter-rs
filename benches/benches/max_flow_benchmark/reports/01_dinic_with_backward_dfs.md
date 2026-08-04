# 01. Dinic with backward DFS

次の参考文献の「注意 3」にある、DFS を逆からやるという改善

参考: https://topcoder-g-hatena-ne-jp.jag-icpc.org/Mi_Sawa/20140311/

```
Benchmarking max_flow_random_n100000_m500000: Warming up for 3.0000 s
Warning: Unable to complete 100 samples in 5.0s. You may wish to increase target time to 10.8s, or reduce sample count to 40.
max_flow_random_n100000_m500000
                        time:   [110.40 ms 111.08 ms 111.84 ms]
                        change: [-49.335% -48.712% -48.107%] (p = 0.00 < 0.05)
                        Performance has improved.
Found 7 outliers among 100 measurements (7.00%)
  6 (6.00%) high mild
  1 (1.00%) high severe

max_flow_misawa         time:   [7.2607 µs 7.2797 µs 7.2993 µs]
                        change: [-7.6107% -7.0815% -6.6276%] (p = 0.00 < 0.05)
                        Performance has improved.
Found 10 outliers among 100 measurements (10.00%)
  5 (5.00%) low mild
  4 (4.00%) high mild
  1 (1.00%) high severe

Benchmarking max_flow_worst_gary_n3000: Warming up for 3.0000 s
Warning: Unable to complete 100 samples in 5.0s. You may wish to increase target time to 14.6s, or reduce sample count to 30.
max_flow_worst_gary_n3000
                        time:   [146.89 ms 148.04 ms 149.24 ms]
                        change: [-39.449% -38.941% -38.361%] (p = 0.00 < 0.05)
                        Performance has improved.
```
