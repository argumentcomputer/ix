# K4/K5 benchmark report (process profile, unhardened)

Host: "Intel(R) Xeon(R) 6975P-C", worker CPU 2, load "1.03 1.75 2.34 1/932 52554".
Blocks per fixture: 5. Ratio = row / lean-clang (< 1 is faster than lean-clang); 95% paired percentile-bootstrap intervals.
Build command: `bench-k45 run --rungs K4 --cpu 2 --blocks 5 --gcc --closures /tmp/pr694-bench/k4-closures --rc off --bignat --opt --bignat-lib /tmp/pr694-bench/bignat-lib.json --region 4294967296 /tmp/pr694-bench/k4-bignat-opt`.
IxCC config: `{"bignat":true,"bignat_lib":"/tmp/pr694-bench/bignat-lib.json","bignat_lib_sha256":"7cba24f00900b9c060eaf6c4e08e6d2bc515319cb5c9d22684099f52f9a784fb","cc":"cc","closures":"/tmp/pr694-bench/k4-closures","embed_cert":false,"harness":true,"opt":true,"rc_mode":"off","region_bytes":4294967296,"stack_bytes":null}`.
Toolchains: `{"cc":"cc (Ubuntu 13.3.0-6ubuntu2~24.04.1) 13.3.0","clang":"Ubuntu clang version 18.1.3 (1ubuntu1)","clang++":"Ubuntu clang version 18.1.3 (1ubuntu1)","g++":"g++ (Ubuntu 13.3.0-6ubuntu2~24.04.1) 13.3.0","gcc":"gcc (Ubuntu 13.3.0-6ubuntu2~24.04.1) 13.3.0","ixcc":"../../.lake/build/bin/ixcc","ixcc_sha256":"bcf63d37739d222782a544990e4ec9721ac136ef77814f0a15adb376bb5c9d91","lean":"Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)","leanc":"clang version 22.1.4 (https://github.com/llvm/llvm-project 35990504507d79e0b9deb809c8ee5e1b34ceef20)","objdump":"GNU objdump (GNU Binutils for Ubuntu) 2.42","repository":"0c324194f9d4"}`.

| Fixture | Rung | Args | lean-clang ms | clang-O2 ms | clang-O3 ms | gcc-O2 ms | gcc-O3 ms | ixcc ms | clang-O2 / lean-clang | clang-O3 / lean-clang | gcc-O2 / lean-clang | gcc-O3 / lean-clang | ixcc / lean-clang |
| --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| blake3 | K4 | `4194304` | 58.67 | 10.81 | 11.24 | 12.78 | 12.30 | 1810.43 | 0.184 [0.177, 0.190] | 0.192 [0.182, 0.199] | 0.217 [0.213, 0.230] | 0.210 [0.202, 0.216] | 30.829 [30.551, 31.150] |
| array-qsort | K4 | `1000000` | 166.95 | 75.91 | 75.92 | 78.76 | 77.74 | 390.05 | 0.455 [0.454, 0.458] | 0.455 [0.453, 0.458] | 0.471 [0.469, 0.474] | 0.466 [0.464, 0.468] | 2.336 [2.322, 2.364] |

## Peak RSS (KiB)

| Fixture | Rung | lean-clang KiB | clang-O2 KiB | clang-O3 KiB | gcc-O2 KiB | gcc-O3 KiB | ixcc KiB |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| blake3 | K4 | 12936 | 5668 | 5668 | 5668 | 5668 | 2487328 |
| array-qsort | K4 | 17000 | 4640 | 4640 | 4640 | 4640 | 77824 |

## Geometric means by rung (ratio to lean-clang)

| Rung | Row | Geomean [95%] | Fixtures |
| --- | --- | ---: | ---: |
| K4 | clang-O2 | 0.290 [0.284, 0.295] | 2 |
| K4 | clang-O3 | 0.295 [0.288, 0.301] | 2 |
| K4 | gcc-O2 | 0.320 [0.317, 0.329] | 2 |
| K4 | gcc-O3 | 0.312 [0.307, 0.318] | 2 |
| K4 | ixcc | 8.487 [8.449, 8.536] | 2 |

## Measured executable artifacts

| Fixture | Row | Mode | .text B | File B | SHA-256 |
| --- | --- | --- | ---: | ---: | --- |
| blake3 | lean-clang | `lean-clang` | 2075553 | 4514680 | `cec7549e0be19a8e` |
| blake3 | clang-O2 | `clang-twin` | 2411 | 16528 | `14f8902a0188ac69` |
| blake3 | clang-O3 | `clang-twin` | 2597 | 16560 | `699b4e465e18fc31` |
| blake3 | gcc-O2 | `gcc-twin` | 2878 | 16480 | `841d88dd7b01a763` |
| blake3 | gcc-O3 | `gcc-twin` | 2874 | 16448 | `6c932c8e28c29578` |
| blake3 | ixcc | `object+harness(RESULT_BYTEARRAY_HEX)` | 137693 | 151768 | `380a5a670a73c461` |
| array-qsort | lean-clang | `lean-clang` | 2056033 | 4490864 | `6ee946982c09dd04` |
| array-qsort | clang-O2 | `clang-twin` | 1150 | 16296 | `d7a3769d36efe672` |
| array-qsort | clang-O3 | `clang-twin` | 1150 | 16296 | `d7a3769d36efe672` |
| array-qsort | gcc-O2 | `gcc-twin` | 892 | 16224 | `8ca363cd95fb37c6` |
| array-qsort | gcc-O3 | `gcc-twin` | 990 | 16224 | `d4dcd8b3ff9cb481` |
| array-qsort | ixcc | `standalone-exe` | 63395 | 65351 | `f3e5a1cf9dd75fb1` |
