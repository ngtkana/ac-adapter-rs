# 03. Push-Relabel by BFS Init.

高さの初期化を次のように変更しました

* 旧: source 以外全て $0$
* 新: source 以外全て sink からの $G_f$ における距離

```
max_flow_random_n100000_m500000
                        time:   [47.169 ms 47.381 ms 47.603 ms]
                        change: [-68.353% -68.156% -67.964%] (p = 0.00 < 0.05)
                        Performance has improved.
Found 1 outliers among 100 measurements (1.00%)
  1 (1.00%) high mild

max_flow_misawa         time:   [71.037 µs 71.164 µs 71.307 µs]
                        change: [-46.301% -46.120% -45.950%] (p = 0.00 < 0.05)
                        Performance has improved.
Found 4 outliers among 100 measurements (4.00%)
  3 (3.00%) high mild
  1 (1.00%) high severe

Benchmarking max_flow_worst_gary_n3000: Warming up for 3.0000 s
Warning: Unable to complete 100 samples in 5.0s. You may wish to increase target time to 11.3s, or reduce sample count to 40.
max_flow_worst_gary_n3000
                        time:   [110.97 ms 111.36 ms 111.76 ms]
                        change: [-3.1915% -2.7612% -2.2775%] (p = 0.00 < 0.05)
                        Performance has improved.
```
