# Native reversal: shared-host reference run

This report covers one bounded reversal workload on one recorded x86-64 Linux host. It compares the checked Compilatrix object with consuming Lean and CakeML programs and the same arena C kernel compiled by CompCert, GCC, and Clang. The worker is pinned, but the host, SMT sibling, temperature, and turbo behavior are not controlled. These observations do not establish a dedicated regression baseline.

Every row has 30 paired blocks in three sessions, with the median of three samples per executable per block. Samples accumulate at least 100 ms of measured work. Counts are identical across implementations in each paired case. The raw timer and handoff control is retained without subtraction. All valid slow observations are included. Intervals use 10,000 hierarchical paired bootstrap replicates (seed 2671931027), resampling sessions then blocks. Only three session clusters are available, so interval precision and generalization remain limited. Full medians, quartiles, intervals, session medians, and paired ratios are in `summary.json`.

## Entry plus bounded handoff

Nanoseconds per operation, median across block medians. Lifecycle includes construction, reversal, order-sensitive consumption, and normal memory management.

| Length | Payload domain | Compilatrix | Lean | CakeML | CompCert | GCC | Clang |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 0 | six patterns, <2^30 | 7.710000 | 2.620000 | 4.170000 | 5.090000 | 4.660000 | 5.140000 |
| 1 | six patterns, <2^30 | 10.790000 | 3.090000 | 5.380000 | 6.220000 | 5.570000 | 6.450000 |
| 2 | six patterns, <2^30 | 14.100000 | 3.810000 | 6.460000 | 7.320000 | 6.480000 | 7.140000 |
| 4 | six patterns, <2^30 | 20.620000 | 5.170000 | 8.880000 | 9.660000 | 8.280000 | 8.530000 |
| 8 | six patterns, <2^30 | 33.590000 | 8.460000 | 13.630000 | 13.840000 | 11.950000 | 11.420000 |
| 16 | six patterns, <2^30 | 59.810000 | 30.480000 | 38.350000 | 22.400000 | 19.120000 | 16.900000 |
| 32 | six patterns, <2^30 | 115.020000 | 66.140000 | 84.650000 | 39.900000 | 35.040000 | 28.070000 |
| 48 | six patterns, <2^30 | 176.050000 | 73.880000 | 131.890000 | 57.450000 | 53.920000 | 39.300000 |
| 63 | six patterns, <2^30 | 233.740000 | 90.810000 | 189.540000 | 73.900000 | 71.760000 | 51.830000 |
| 64 | six patterns, <2^30 | 237.600000 | 92.230000 | 180.270000 | 74.940000 | 72.990000 | 50.630000 |
| 1 | 2^63-1 | 10.790000 | 3.080000 | 5.380000 | 6.210000 | 5.570000 | 6.450000 |
| 16 | 2^63-1 | 59.860000 | 30.920000 | 40.560000 | 22.360000 | 19.070000 | 16.880000 |
| 64 | 2^63-1 | 237.770000 | 91.580000 | 179.160000 | 75.060000 | 73.000000 | 50.690000 |
| 1 | 2^63 | 10.780000 | 3.060000 | 5.390000 | 6.220000 | 5.570000 | 6.450000 |
| 16 | 2^63 | 59.800000 | 33.770000 | 40.780000 | 22.380000 | 19.090000 | 16.880000 |
| 64 | 2^63 | 237.530000 | 95.420000 | 179.450000 | 74.790000 | 72.860000 | 50.640000 |
| 1 | 2^64-1 | 10.800000 | 3.060000 | 5.380000 | 6.210000 | 5.570000 | 6.450000 |
| 16 | 2^64-1 | 59.870000 | 33.760000 | 40.570000 | 22.360000 | 19.090000 | 16.890000 |
| 64 | 2^64-1 | 237.710000 | 94.920000 | 178.080000 | 74.930000 | 72.930000 | 50.700000 |

## Fresh allocation lifecycle

Nanoseconds per operation, median across block medians. Lifecycle includes construction, reversal, order-sensitive consumption, and normal memory management.

| Length | Payload domain | Compilatrix | Lean | CakeML | CompCert | GCC | Clang |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 0 | six patterns, <2^30 | 20.900000 | 7.160000 | 8.960000 | 18.250000 | 17.800000 | 18.060000 |
| 1 | six patterns, <2^30 | 24.340000 | 12.890000 | 53.730000 | 20.070000 | 18.730000 | 19.680000 |
| 2 | six patterns, <2^30 | 29.070000 | 18.470000 | 98.720000 | 22.050000 | 20.620000 | 21.140000 |
| 4 | six patterns, <2^30 | 38.480000 | 29.910000 | 187.440000 | 27.440000 | 26.290000 | 25.130000 |
| 8 | six patterns, <2^30 | 56.990000 | 55.470000 | 370.160000 | 40.070000 | 37.670000 | 38.650000 |
| 16 | six patterns, <2^30 | 100.820000 | 112.810000 | 726.690000 | 67.880000 | 63.390000 | 62.640000 |
| 32 | six patterns, <2^30 | 210.560000 | 227.310000 | 1442.290000 | 138.290000 | 126.140000 | 124.770000 |
| 48 | six patterns, <2^30 | 315.270000 | 339.240000 | 2159.640000 | 199.560000 | 189.260000 | 184.910000 |
| 63 | six patterns, <2^30 | 422.470000 | 445.840000 | 2841.280000 | 261.470000 | 249.990000 | 235.310000 |
| 64 | six patterns, <2^30 | 418.380000 | 455.160000 | 2879.840000 | 263.410000 | 252.280000 | 234.350000 |
| 1 | 2^63-1 | 24.070000 | 12.890000 | 54.400000 | 19.800000 | 18.530000 | 19.390000 |
| 16 | 2^63-1 | 100.540000 | 112.720000 | 735.040000 | 67.580000 | 63.360000 | 62.230000 |
| 64 | 2^63-1 | 418.580000 | 454.490000 | 2888.330000 | 263.420000 | 253.490000 | 238.670000 |
| 1 | 2^63 | 24.080000 | 56.520000 | 54.370000 | 19.820000 | 18.460000 | 19.400000 |
| 16 | 2^63 | 100.690000 | 820.780000 | 734.500000 | 67.510000 | 63.300000 | 62.430000 |
| 64 | 2^63 | 420.080000 | 3216.880000 | 2902.600000 | 263.570000 | 252.450000 | 237.990000 |
| 1 | 2^64-1 | 24.140000 | 56.660000 | 54.310000 | 19.790000 | 18.460000 | 19.400000 |
| 16 | 2^64-1 | 100.720000 | 825.520000 | 735.130000 | 67.480000 | 63.320000 | 62.490000 |
| 64 | 2^64-1 | 418.900000 | 3254.130000 | 2910.990000 | 263.470000 | 253.070000 | 233.950000 |

## Paired comparison at the current 64-element bound

Each cell is baseline time / Compilatrix time, followed by its 95% interval. Values above one favor Compilatrix. The JSON summary retains paired intervals for every other length as well.

| Profile | Domain | Lean | CakeML | CompCert | GCC | Clang |
| --- | --- | --- | --- | --- | --- | --- |
| entry+handoff | primary | 0.390000 [0.390000, 0.390000] | 0.760000 [0.740000, 0.780000] | 0.310000 [0.310000, 0.320000] | 0.310000 [0.310000, 0.310000] | 0.210000 [0.210000, 0.210000] |
| entry+handoff | stress-2^63-1 | 0.380000 [0.380000, 0.390000] | 0.750000 [0.740000, 0.760000] | 0.320000 [0.310000, 0.320000] | 0.310000 [0.300000, 0.310000] | 0.210000 [0.210000, 0.210000] |
| entry+handoff | stress-2^63 | 0.400000 [0.400000, 0.400000] | 0.750000 [0.740000, 0.770000] | 0.310000 [0.310000, 0.320000] | 0.310000 [0.310000, 0.310000] | 0.210000 [0.210000, 0.210000] |
| entry+handoff | stress-2^64-1 | 0.400000 [0.400000, 0.400000] | 0.750000 [0.740000, 0.760000] | 0.310000 [0.310000, 0.320000] | 0.310000 [0.310000, 0.310000] | 0.210000 [0.210000, 0.210000] |
| lifecycle | primary | 1.090000 [1.080000, 1.100000] | 6.870000 [6.800000, 6.930000] | 0.630000 [0.630000, 0.630000] | 0.600000 [0.600000, 0.610000] | 0.560000 [0.560000, 0.570000] |
| lifecycle | stress-2^63-1 | 1.080000 [1.080000, 1.090000] | 6.880000 [6.850000, 6.940000] | 0.630000 [0.630000, 0.630000] | 0.600000 [0.600000, 0.610000] | 0.570000 [0.560000, 0.570000] |
| lifecycle | stress-2^63 | 7.650000 [7.610000, 7.700000] | 6.910000 [6.840000, 6.960000] | 0.630000 [0.630000, 0.630000] | 0.600000 [0.600000, 0.610000] | 0.560000 [0.560000, 0.570000] |
| lifecycle | stress-2^64-1 | 7.750000 [7.690000, 7.800000] | 6.920000 [6.860000, 6.970000] | 0.630000 [0.630000, 0.630000] | 0.600000 [0.600000, 0.610000] | 0.560000 [0.560000, 0.570000] |

## Process memory and collection observations

RSS is read from `/proc/self/statm`; peak RSS is the maximum recorded `getrusage(RUSAGE_SELF)` high-water value. Ready-process RSS includes initialized runtimes and immutable scalar datasets, before list work. These process measurements include allocator/runtime reservation and differ from live application bytes.

| Implementation | Median ready RSS KiB | Minimum sample RSS KiB | Maximum sample RSS KiB | Maximum recorded peak KiB |
| --- | ---: | ---: | ---: | ---: |
| compilatrix | 2028.000000 | 2192 | 2464 | 11104 |
| lean | 7342.000000 | 7300 | 15720 | 15716 |
| cakeml | 2540.000000 | 68060 | 68108 | 67896 |
| compcert | 2024.000000 | 2188 | 2460 | 11100 |
| gcc | 2024.000000 | 2188 | 2460 | 11100 |
| clang | 2024.000000 | 2188 | 2460 | 11100 |

The separate CakeML lifecycle diagnostic observed 11258 natural collections across 20 samples. Maximum observed post-collection live data was 348952 bytes; the separately timed terminal collection took 74990 ns and retained 347640 bytes. These instrumented event counts include each sample envelope and are separate from primary timing. Hardware counters: unavailable; the diagnostic record gives the actual availability reason/event output.

## Native code and compiler work

The following object `.text` sizes come from retained `size -A` output. The CakeML object includes the ML driver and basis code; the Lean object includes its generated module entry, and the C/Compilatrix rows isolate the arena kernels. The complete sections, linked executable sizes, and dynamic dependencies are retained; these scopes are not interchangeable.

| Object | `.text` bytes |
| --- | ---: |
| compilatrix-main | 1036 |
| compilatrix-release | 231 |
| lean-kernel | 0 |
| cakeml-kernel | 106564 |
| compcert-kernel | 679 |
| gcc-kernel | 596 |
| clang-kernel | 776 |

Compiler rows are single observed process envelopes. They include process startup and the named producer/checker work; they are separate from seed installation, proof-library builds, and runtime comparisons. CPU time and peak compiler RSS are in the retained diagnostics.

| Operation | Elapsed ms | Peak RSS KiB |
| --- | ---: | ---: |
| compilatrix-produce | 13502.260000 | 83660 |
| compilatrix-independent-gate | 31847.570000 | 84696 |
| lean-generate-c | 284.920000 | 466108 |
| lean-kernel | 129.480000 | 71508 |
| cakeml-kernel | 1100.610000 | 740392 |
| kernel-compcert | 51.210000 | 20612 |
| kernel-gcc | 55.330000 | 36160 |
| kernel-clang | 82.740000 | 108284 |
| upstream-applyClosed-produce | 54.370000 | 53980 |
| upstream-applyClosed-check | 36.530000 | 49588 |
| upstream-letClosed-produce | 62.780000 | 56004 |
| upstream-letClosed-check | 42.420000 | 49760 |

## Unchanged upstream computations

These closed entries retain their native successor instructions and four direct calls. They take no runtime arguments. Their call timings are separate from the runtime-input reversal comparison.

| Entry | Result | Native text bytes | Object bytes | Median ns/call | 95% interval |
| --- | ---: | ---: | ---: | ---: | --- |
| applyClosed | 3 | 84 | 936 | 5.200000 | 5.200000–5.210000 |
| letClosed | 4 | 91 | 944 | 5.200000 | 5.200000–5.210000 |

The baseline source/physical heap is fully reclaimed in the checked artifacts. Native Nat values use one exact 64-bit word and allocate no heap. The call traces write 48 bytes below the caller return slot. These closed translation-validation and supplied-state execution certificates do not close N3's open-call, branch/join, or F1's general stack contracts.

Code sizes, compiler/checker resource envelopes, runtime dependencies, RSS observations, GC diagnostics, and complete inputs are retained with the build and raw run. Arena capacity is n+2 cells (80+32*(n+2) bytes); release clears cells before freeing the arena. Lean uniqueness diagnostics establish exclusive spines and cons reuse. CakeML uses a 64 MiB simple copying heap and an 8 MiB stack; separate diagnostics report actual collection cycles and terminal collection. Dropping roots is not immediate reclamation. Hardware counters are reported only when available.
