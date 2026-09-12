# Compiler scaling

114 workload/cache rows; 3 consecutive sessions × 3 shuffled blocks. Each stage sample is one invocation in a fresh, pinned worker process. Tables show medians; the JSON retains quartiles, minima, maxima, and every stage. These are descriptive observations on a shared host, with no performance threshold or confidence claim.

The source frontend includes address/usage checking, erasure, source certification, and IxIR₁ lowering. Separate coverage discovery/source certificate timings rerun that work. HPT certificate checking and snapshot ingestion also have separate replay timings. The primary-stage sum omits those repeated diagnostics and the preflight already included in the frontend; the process envelope includes all work and artifact IO. No timer or diagnostic cost is subtracted.

Memory is process RSS and raw reported VmHWM at stage boundaries, including earlier phases, retained artifacts, diagnostics and IO; GNU time records the final process peak. It is not an isolated allocation count or per-phase incremental peak. ELF-less rows retain their exact rejection or requested endpoint. Source proof terms are erased; source database counts/work charges, HPT candidate JSON bytes, and canonical HPT store bytes are reported separately.

## declarations

| Size | Result | Frontend ms | HPT ms | IxIR₂ ms | x86 encode/check ms | Process peak MiB | HPT store B | Snapshot B | ELF B |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | compiled | 0.140000 | 0.070000 | 0.070000 | 1.330000 | 74.920000 | 889 | 450 | 1240 |
| 2 | compiled | 0.190000 | 0.110000 | 0.100000 | 1.330000 | 74.940000 | 1331 | 584 | 1240 |
| 4 | compiled | 0.330000 | 0.250000 | 0.200000 | 1.350000 | 76.850000 | 2215 | 852 | 1240 |
| 8 | compiled | 0.730000 | 0.680000 | 0.550000 | 1.360000 | 77.040000 | 3983 | 1388 | 1240 |
| 16 | compiled | 2.170000 | 2.170000 | 1.740000 | 1.360000 | 77.090000 | 7519 | 2460 | 1240 |
| 32 | compiled | 7.230000 | 8.240000 | 6.400000 | 1.350000 | 77.030000 | 14591 | 4604 | 1240 |
| 64 | compiled | 26.560000 | 32.330000 | 24.750000 | 1.350000 | 76.730000 | 28736 | 8893 | 1240 |
| 128 | compiled | 101.650000 | 133.330000 | 96.210000 | 1.350000 | 78.830000 | 57024 | 17469 | 1240 |
| 256 | compiled | 398.240000 | 543.390000 | 384.130000 | 1.370000 | 80.800000 | 113600 | 34621 | 1240 |
| 352 | compiled | 753.180000 | 918.170000 | 728.500000 | 1.370000 | 83.000000 | 156032 | 47485 | 1240 |
| 353 | reject: source-preflight | — | — | — | — | 74.640000 | — | — | — |
| 512 | reject: source-preflight | — | — | — | — | 74.830000 | — | — | — |

## call-depth

| Size | Result | Frontend ms | HPT ms | IxIR₂ ms | x86 encode/check ms | Process peak MiB | HPT store B | Snapshot B | ELF B |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | compiled | 0.190000 | 0.050000 | 0.080000 | 2.370000 | 74.880000 | 652 | 743 | 1400 |
| 2 | compiled | 0.240000 | 0.070000 | 0.090000 | 3.020000 | 74.790000 | 889 | 823 | 1472 |
| 4 | compiled | 0.330000 | 0.120000 | 0.120000 | 4.780000 | 76.890000 | 1363 | 983 | 1608 |
| 8 | compiled | 0.590000 | 0.250000 | 0.180000 | 9.030000 | 76.730000 | 2311 | 1303 | 1888 |
| 16 | compiled | 1.270000 | 0.770000 | 0.350000 | 22.070000 | 76.750000 | 4207 | 1943 | 2440 |
| 32 | compiled | 3.540000 | 3.010000 | 0.900000 | 64.460000 | 76.760000 | 7999 | 3223 | 3544 |
| 33 | reject: native-select | 3.710000 | 3.200000 | 0.930000 | — | 76.910000 | 8236 | 3303 | — |
| 64 | reject: native-select | 12.140000 | 11.830000 | 2.980000 | — | 76.800000 | 15583 | 5783 | — |
| 128 | reject: native-select | 41.760000 | 47.450000 | 10.770000 | — | 78.910000 | 30752 | 10904 | — |
| 256 | reject: native-select | 164.990000 | 187.590000 | 41.750000 | — | 78.570000 | 61088 | 21144 | — |
| 318 | reject: native-select | 257.320000 | 269.150000 | 62.320000 | — | 78.950000 | 75782 | 26104 | — |
| 319 | reject: source-preflight | — | — | — | — | 74.530000 | — | — | — |
| 512 | reject: source-preflight | — | — | — | — | 76.890000 | — | — | — |

## branches

| Size | Result | Frontend ms | HPT ms | IxIR₂ ms | x86 encode/check ms | Process peak MiB | HPT store B | Snapshot B | ELF B |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | compiled | 0.200000 | 0.080000 | 0.110000 | 2.250000 | 75.030000 | 955 | 509 | 1376 |
| 2 | compiled | 0.280000 | 0.100000 | 0.180000 | 4.870000 | 74.800000 | 1192 | 628 | 1616 |
| 4 | compiled | 0.450000 | 0.150000 | 0.350000 | 13.040000 | 77.040000 | 1666 | 866 | 2088 |
| 8 | compiled | 0.900000 | 0.310000 | 0.870000 | 41.460000 | 76.940000 | 2614 | 1342 | 3048 |
| 16 | compiled | 2.320000 | 0.930000 | 2.750000 | 143.490000 | 76.900000 | 4510 | 2294 | 4960 |
| 31 | compiled | 6.380000 | 2.880000 | 9.000000 | 506.100000 | 76.430000 | 8065 | 4079 | 8544 |
| 32 | reject: native-select | 6.680000 | 3.090000 | 9.340000 | — | 76.900000 | 8302 | 4198 | — |
| 64 | reject: native-select | 23.840000 | 11.800000 | 37.480000 | — | 78.840000 | 15886 | 8006 | — |
| 128 | reject: native-select | 88.620000 | 46.830000 | 146.640000 | — | 77.960000 | 31055 | 15623 | — |
| 256 | reject: native-select | 346.700000 | 189.480000 | 578.420000 | — | 80.220000 | 61391 | 30855 | — |
| 453 | reject: native-select | 1077.120000 | 628.560000 | 1941.480000 | — | 84.930000 | 108080 | 54298 | — |
| 454 | reject: source-construction | — | — | — | — | 76.580000 | — | — | — |
| 512 | reject: source-construction | — | — | — | — | 76.700000 | — | — | — |

## allocations

| Size | Result | Frontend ms | HPT ms | IxIR₂ ms | x86 encode/check ms | Process peak MiB | HPT store B | Snapshot B | ELF B |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | compiled | 0.260000 | 0.080000 | 0.090000 | 31.740000 | 76.750000 | 961 | 820 | 2776 |
| 2 | compiled | 0.290000 | 0.110000 | 0.110000 | 38.450000 | 76.740000 | 961 | 893 | 2984 |
| 4 | compiled | 0.350000 | 0.140000 | 0.150000 | 54.100000 | 76.720000 | 961 | 1039 | 3392 |
| 8 | compiled | 0.460000 | 0.210000 | 0.250000 | 92.730000 | 76.990000 | 961 | 1331 | 4208 |
| 9 | reject: native-select | 0.500000 | 0.230000 | 0.290000 | — | 76.810000 | 961 | 1404 | — |
| 16 | reject: native-select | 0.700000 | 0.390000 | 0.610000 | — | 76.720000 | 961 | 1915 | — |
| 32 | reject: native-select | 1.120000 | 0.760000 | 1.830000 | — | 76.860000 | 961 | 3083 | — |
| 64 | reject: native-select | 2.070000 | 1.830000 | 6.800000 | — | 77.750000 | 961 | 5419 | — |
| 128 | reject: native-select | 4.090000 | 5.240000 | 24.870000 | — | 80.960000 | 961 | 10220 | — |

## candidates

| Size | Result | Frontend ms | HPT ms | IxIR₂ ms | x86 encode/check ms | Process peak MiB | HPT store B | Snapshot B | ELF B |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 511 | preflight-only | — | — | — | — | 76.650000 | — | — | — |
| 512 | preflight-only | — | — | — | — | 76.890000 | — | — | — |
| 513 | reject: source-preflight | — | — | — | — | 76.880000 | — | — | — |

## joins

| Size | Result | Frontend ms | HPT ms | IxIR₂ ms | x86 encode/check ms | Process peak MiB | HPT store B | Snapshot B | ELF B |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | compiled | — | — | — | 1.960000 | 74.670000 | — | 269 | 1344 |
| 2 | compiled | — | — | — | 6.640000 | 74.800000 | — | 315 | 1760 |
| 4 | compiled | — | — | — | 96.040000 | 76.800000 | — | 407 | 4272 |
| 6 | compiled | — | — | — | 1466.120000 | 76.540000 | — | 499 | 14304 |
| 8 | compiled | — | — | — | 23115.970000 | 78.490000 | — | 591 | 54432 |
| 9 | lowered | — | — | — | — | 77.030000 | — | 637 | — |
| 10 | reject: native-select | — | — | — | — | 76.790000 | — | 683 | — |
| 11 | reject: native-select | — | — | — | — | 76.800000 | — | 729 | — |
| 12 | reject: native-select | — | — | — | — | 76.790000 | — | 775 | — |
| 32 | reject: native-select | — | — | — | — | 76.700000 | — | 1695 | — |
| 43 | reject: native-select | — | — | — | — | 76.800000 | — | 2205 | — |

## Cache reuse

Cold/warm refer to absent/persisted HPT evidence, not the OS page cache. Warm processes decode the retained store and validate hits against the current addressed graph. Source certification runs again. The edit changes one leaf projection and readdresses dependent callers; its scalar result stays unchanged. Ratios are paired within each block; values above one favor the warm run.

| Cold row | Hits | Rebuilt | HPT cold/warm median | Primary stages cold/warm | Process cold/warm |
| --- | ---: | ---: | ---: | ---: | ---: |
| declarations-1-cold | 4 | 0 | 0.900000 | 1.010000 | 1.030000 |
| declarations-2-cold | 6 | 0 | 0.940000 | 0.990000 | 1.000000 |
| declarations-4-cold | 10 | 0 | 0.980000 | 1.010000 | 1.010000 |
| declarations-8-cold | 18 | 0 | 1.010000 | 1.020000 | 1.000000 |
| declarations-16-cold | 34 | 0 | 1.140000 | 1.040000 | 0.990000 |
| declarations-32-cold | 66 | 0 | 1.150000 | 1.050000 | 1.020000 |
| declarations-64-cold | 130 | 0 | 1.180000 | 1.060000 | 1.040000 |
| declarations-128-cold | 258 | 0 | 1.170000 | 1.050000 | 1.040000 |
| declarations-256-cold | 514 | 0 | 1.190000 | 1.070000 | 1.050000 |
| declarations-352-cold | 706 | 0 | 1.180000 | 1.050000 | 1.040000 |
| call-depth-1-cold | 3 | 0 | 0.860000 | 1.000000 | 0.990000 |
| call-depth-2-cold | 4 | 0 | 0.860000 | 0.990000 | 1.000000 |
| call-depth-4-cold | 6 | 0 | 0.970000 | 1.010000 | 1.020000 |
| call-depth-8-cold | 10 | 0 | 1.000000 | 1.000000 | 1.000000 |
| call-depth-16-cold | 18 | 0 | 1.070000 | 0.990000 | 1.000000 |
| call-depth-32-cold | 34 | 0 | 1.130000 | 1.010000 | 1.010000 |
| call-depth-33-cold | 35 | 0 | 1.140000 | 1.040000 | 1.030000 |
| call-depth-64-cold | 66 | 0 | 1.150000 | 1.070000 | 1.030000 |
| call-depth-128-cold | 130 | 0 | 1.160000 | 1.070000 | 1.030000 |
| call-depth-256-cold | 258 | 0 | 1.170000 | 1.070000 | 1.040000 |
| call-depth-318-cold | 320 | 0 | 1.180000 | 1.070000 | 1.040000 |
| branches-1-cold | 4 | 0 | 0.900000 | 0.990000 | 1.010000 |
| branches-2-cold | 5 | 0 | 0.930000 | 0.990000 | 0.990000 |
| branches-4-cold | 7 | 0 | 0.970000 | 1.000000 | 1.020000 |
| branches-8-cold | 11 | 0 | 1.010000 | 1.000000 | 0.990000 |
| branches-16-cold | 19 | 0 | 1.090000 | 1.000000 | 0.970000 |
| branches-31-cold | 34 | 0 | 1.130000 | 1.000000 | 1.000000 |
| branches-32-cold | 35 | 0 | 1.130000 | 1.000000 | 0.990000 |
| branches-64-cold | 67 | 0 | 1.160000 | 1.010000 | 1.000000 |
| branches-128-cold | 131 | 0 | 1.170000 | 1.030000 | 1.020000 |
| branches-256-cold | 259 | 0 | 1.170000 | 1.020000 | 1.010000 |
| branches-453-cold | 456 | 0 | 1.190000 | 1.030000 | 1.020000 |
| allocations-1-cold | 4 | 0 | 0.880000 | 1.000000 | 1.010000 |
| allocations-2-cold | 4 | 0 | 0.920000 | 1.000000 | 1.010000 |
| allocations-4-cold | 4 | 0 | 0.970000 | 0.990000 | 1.000000 |
| allocations-8-cold | 4 | 0 | 1.030000 | 0.990000 | 1.000000 |
| allocations-9-cold | 4 | 0 | 1.050000 | 1.010000 | 1.000000 |
| allocations-16-cold | 4 | 0 | 1.090000 | 0.990000 | 1.000000 |
| allocations-32-cold | 4 | 0 | 1.110000 | 1.010000 | 1.000000 |
| allocations-64-cold | 4 | 0 | 1.130000 | 1.030000 | 1.000000 |
| allocations-128-cold | 4 | 0 | 1.130000 | 1.030000 | 1.030000 |
| call-depth-1-edited-edit-cold | 2 | 1 | 0.860000 | 1.000000 | 1.030000 |
| call-depth-4-edited-edit-cold | 2 | 4 | 0.890000 | 0.990000 | 1.000000 |
| call-depth-16-edited-edit-cold | 2 | 16 | 0.960000 | 1.000000 | 0.990000 |
| call-depth-32-edited-edit-cold | 2 | 32 | 0.980000 | 0.990000 | 1.000000 |
| call-depth-128-edited-edit-cold | 2 | 128 | 1.000000 | 1.000000 | 1.000000 |
| call-depth-318-edited-edit-cold | 2 | 318 | 1.000000 | 1.000000 | 1.000000 |

## Rejections and experiment endpoints

- `declarations-353-cold` / `source-preflight`: Compilatrix.Pipeline.Error.resource   { metric := Compilatrix.Ixon.Work.Metric.certificateSourceNodeWork, actual := 135287305, limit := 134217728 }
- `declarations-512-cold` / `source-preflight`: Compilatrix.Pipeline.Error.resource   { metric := Compilatrix.Ixon.Work.Metric.certificateCandidates, actual := 514, limit := 512 }
- `call-depth-33-cold` / `native-select`: heap CFG call graph is recursive or exceeds 32 functions
- `call-depth-64-cold` / `native-select`: heap CFG call graph is recursive or exceeds 32 functions
- `call-depth-128-cold` / `native-select`: heap CFG call graph is recursive or exceeds 32 functions
- `call-depth-256-cold` / `native-select`: heap CFG call graph is recursive or exceeds 32 functions
- `call-depth-318-cold` / `native-select`: heap CFG call graph is recursive or exceeds 32 functions
- `call-depth-319-cold` / `source-preflight`: Compilatrix.Pipeline.Error.resource   { metric := Compilatrix.Ixon.Work.Metric.certificateSourceNodeWork, actual := 135413228, limit := 134217728 }
- `call-depth-512-cold` / `source-preflight`: Compilatrix.Pipeline.Error.resource   { metric := Compilatrix.Ixon.Work.Metric.certificateCandidates, actual := 516, limit := 512 }
- `branches-32-cold` / `native-select`: heap CFG call graph is recursive or exceeds 32 functions
- `branches-64-cold` / `native-select`: heap CFG call graph is recursive or exceeds 32 functions
- `branches-128-cold` / `native-select`: heap CFG call graph is recursive or exceeds 32 functions
- `branches-256-cold` / `native-select`: heap CFG call graph is recursive or exceeds 32 functions
- `branches-453-cold` / `native-select`: heap CFG call graph is recursive or exceeds 32 functions
- `branches-454-cold` / `source-construction`: synthetic source address rejected: Compilatrix.Ixon.Constant.AddressError.resource   { metric := Compilatrix.Ixon.Work.Metric.compressionInputUnits, actual := 4097, limit := 4096 }
- `branches-512-cold` / `source-construction`: synthetic source address rejected: Compilatrix.Ixon.Constant.AddressError.resource   { metric := Compilatrix.Ixon.Work.Metric.compressionInputUnits, actual := 4619, limit := 4096 }
- `allocations-9-cold` / `native-select`: heap CFG entry has no admitted scalar-argument interface
- `allocations-16-cold` / `native-select`: heap CFG entry has no admitted scalar-argument interface
- `allocations-32-cold` / `native-select`: heap CFG entry has no admitted scalar-argument interface
- `allocations-64-cold` / `native-select`: heap CFG entry has no admitted scalar-argument interface
- `allocations-128-cold` / `native-select`: heap CFG source function exceeds the block/instruction limits
- `candidates-513-cold` / `source-preflight`: Compilatrix.Pipeline.Error.resource   { metric := Compilatrix.Ixon.Work.Metric.certificateCandidates, actual := 513, limit := 512 }
- `joins-9-cold`: fixed experiment endpoint after native lowering; 3584 target blocks, 11786 instructions. No ELF timing or rejection is claimed.
- `joins-10-cold` / `native-select`: heap CFG entry has no admitted scalar-argument interface
- `joins-11-cold` / `native-select`: heap CFG entry has no admitted scalar-argument interface
- `joins-12-cold` / `native-select`: heap CFG entry has no admitted scalar-argument interface
- `joins-32-cold` / `native-select`: heap CFG entry has no admitted scalar-argument interface
- `joins-43-cold` / `native-select`: heap CFG source function exceeds the block/instruction limits
- `call-depth-128-edited-edit-cold` / `native-select`: heap CFG call graph is recursive or exceeds 32 functions
- `call-depth-318-edited-edit-cold` / `native-select`: heap CFG call graph is recursive or exceeds 32 functions

The Ixon branch family has no converging joins. The supplementary join family starts from a checked IxIR₂ snapshot and has no source/HPT measurements. Full object emission stops at eight joins; larger cases measure selection/lowering and preserve its rejection boundary. Candidate fixtures isolate preflight admission only and do not claim successful source certification at 512 candidates.

The allocation reference matrix stops at size 128. Larger setup probes are retained separately: size 256 required about 21 seconds to construct its canonical input; size 512 hit the 120-second process CPU guard during construction. That setup failure is not a compiler rejection or a reference timing sample.
