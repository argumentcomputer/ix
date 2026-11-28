# Checked reserve/reuse counter folding

One source function, two checked native lowerings, and identical C driver objects. The only loop rewrite removes four cancelling reservation/live counter changes (12 instructions per element). Every cell operation and cumulative reuse/payload counter update remains.

Each row contains 30 paired blocks across three sessions, using each variant's median of three native samples per block. Operation counts are common within each row and frozen before measurement. Samples accumulate at least 100 ms. The paired speedup is baseline time divided by folded time; values above one favor folding. The 95% intervals use 10,000 hierarchical paired bootstrap draws, resampling sessions and then blocks (seed 2671931027). All valid slow samples are retained and the timer control is not subtracted. This is a shared host with a pinned worker, uncontrolled SMT sibling and only three session clusters; it establishes no CI timing threshold.

## Entry plus handoff

Nanoseconds per operation; lifecycle includes fresh construction, reversal, digest and full reclamation.

| Length | Domain | Baseline ns | Folded ns | Paired speedup [95% interval] |
| ---: | --- | ---: | ---: | ---: |
| 0 | primary | 7.630000 | 7.400000 | 1.030000 [1.020000, 1.040000] |
| 1 | primary | 10.700000 | 9.840000 | 1.090000 [1.080000, 1.090000] |
| 2 | primary | 13.950000 | 12.380000 | 1.120000 [1.120000, 1.130000] |
| 4 | primary | 20.460000 | 17.450000 | 1.170000 [1.160000, 1.190000] |
| 8 | primary | 33.320000 | 27.610000 | 1.210000 [1.200000, 1.230000] |
| 16 | primary | 59.180000 | 48.380000 | 1.220000 [1.210000, 1.260000] |
| 32 | primary | 114.150000 | 90.060000 | 1.270000 [1.260000, 1.280000] |
| 48 | primary | 174.220000 | 131.200000 | 1.330000 [1.320000, 1.340000] |
| 63 | primary | 231.250000 | 170.510000 | 1.360000 [1.350000, 1.420000] |
| 64 | primary | 235.000000 | 172.130000 | 1.360000 [1.360000, 1.400000] |
| 1 | stress-2^63-1 | 10.680000 | 9.830000 | 1.090000 [1.080000, 1.090000] |
| 16 | stress-2^63-1 | 59.240000 | 48.450000 | 1.220000 [1.210000, 1.250000] |
| 64 | stress-2^63-1 | 234.740000 | 172.760000 | 1.360000 [1.360000, 1.360000] |
| 1 | stress-2^63 | 10.680000 | 9.830000 | 1.090000 [1.080000, 1.100000] |
| 16 | stress-2^63 | 59.300000 | 48.470000 | 1.220000 [1.220000, 1.240000] |
| 64 | stress-2^63 | 234.850000 | 172.550000 | 1.360000 [1.350000, 1.410000] |
| 1 | stress-2^64-1 | 10.680000 | 9.870000 | 1.090000 [1.080000, 1.090000] |
| 16 | stress-2^64-1 | 59.240000 | 48.330000 | 1.220000 [1.220000, 1.240000] |
| 64 | stress-2^64-1 | 235.220000 | 172.960000 | 1.360000 [1.350000, 1.370000] |

## Complete lifecycle

Nanoseconds per operation; lifecycle includes fresh construction, reversal, digest and full reclamation.

| Length | Domain | Baseline ns | Folded ns | Paired speedup [95% interval] |
| ---: | --- | ---: | ---: | ---: |
| 0 | primary | 20.870000 | 20.740000 | 1.010000 [1.000000, 1.020000] |
| 1 | primary | 24.460000 | 23.120000 | 1.050000 [1.040000, 1.070000] |
| 2 | primary | 28.980000 | 26.500000 | 1.090000 [1.080000, 1.100000] |
| 4 | primary | 38.120000 | 34.580000 | 1.100000 [1.090000, 1.110000] |
| 8 | primary | 56.340000 | 49.960000 | 1.130000 [1.120000, 1.140000] |
| 16 | primary | 99.840000 | 86.010000 | 1.170000 [1.150000, 1.170000] |
| 32 | primary | 208.270000 | 180.890000 | 1.150000 [1.140000, 1.180000] |
| 48 | primary | 311.860000 | 269.360000 | 1.170000 [1.150000, 1.190000] |
| 63 | primary | 418.450000 | 351.800000 | 1.200000 [1.190000, 1.220000] |
| 64 | primary | 417.000000 | 357.750000 | 1.180000 [1.170000, 1.190000] |
| 1 | stress-2^63-1 | 24.250000 | 23.060000 | 1.060000 [1.040000, 1.060000] |
| 16 | stress-2^63-1 | 99.700000 | 86.040000 | 1.160000 [1.150000, 1.170000] |
| 64 | stress-2^63-1 | 415.470000 | 358.440000 | 1.170000 [1.150000, 1.190000] |
| 1 | stress-2^63 | 24.060000 | 22.980000 | 1.050000 [1.030000, 1.060000] |
| 16 | stress-2^63 | 99.670000 | 86.340000 | 1.150000 [1.140000, 1.170000] |
| 64 | stress-2^63 | 415.400000 | 357.930000 | 1.180000 [1.150000, 1.190000] |
| 1 | stress-2^64-1 | 24.160000 | 22.920000 | 1.040000 [1.040000, 1.060000] |
| 16 | stress-2^64-1 | 99.620000 | 86.140000 | 1.150000 [1.130000, 1.170000] |
| 64 | stress-2^64-1 | 416.080000 | 355.280000 | 1.190000 [1.160000, 1.200000] |

## Code and checking work

The object text sizes below isolate the checked reversal and release functions. Generation and independent-gate CPU/wall/RSS records are diagnostic envelopes: generation includes pipeline construction and modeled fixture executions; each gate includes two fresh generations, decoding, corruption checks and a linked native harness. They are retained as complete costs, without attributing them to an isolated compiler or proof-checker phase.

| Variant | Reversal `.text` bytes | Release `.text` bytes | Producer wall s | Gate wall s |
| --- | ---: | ---: | ---: | ---: |
| baseline | 1036 | 231 | 13.580000 | 28.020000 |
| counter-fold | 952 | 231 | 10.660000 | 21.170000 |
