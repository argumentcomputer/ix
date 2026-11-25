# K4/K5 benchmark report (process profile, unhardened)

Host: "Intel(R) Xeon(R) 6975P-C", worker CPU 2, load "2.46 1.99 1.01 1/938 26794".
Blocks per fixture: 10. Ratio = row / lean-clang (< 1 is faster than lean-clang); 95% paired percentile-bootstrap intervals.
Build command: `bench-k45 run --rungs K1 --cpu 2 --blocks 10 --closures ../../fixtures/ixon-v4/bench-k1 --rc off --opt /tmp/pr694-bench/k1-opt`.
IxCC config: `{"bignat":false,"bignat_lib":null,"bignat_lib_sha256":null,"cc":"cc","closures":"../../fixtures/ixon-v4/bench-k1","embed_cert":false,"harness":true,"opt":true,"rc_mode":"off","region_bytes":null,"stack_bytes":null}`.
Toolchains: `{"cc":"cc (Ubuntu 13.3.0-6ubuntu2~24.04.1) 13.3.0","clang":"Ubuntu clang version 18.1.3 (1ubuntu1)","clang++":"Ubuntu clang version 18.1.3 (1ubuntu1)","g++":"g++ (Ubuntu 13.3.0-6ubuntu2~24.04.1) 13.3.0","gcc":"gcc (Ubuntu 13.3.0-6ubuntu2~24.04.1) 13.3.0","ixcc":"../../.lake/build/bin/ixcc","ixcc_sha256":"bcf63d37739d222782a544990e4ec9721ac136ef77814f0a15adb376bb5c9d91","lean":"Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)","leanc":"clang version 22.1.4 (https://github.com/llvm/llvm-project 35990504507d79e0b9deb809c8ee5e1b34ceef20)","objdump":"GNU objdump (GNU Binutils for Ubuntu) 2.42","repository":"0c324194f9d4"}`.

| Fixture | Rung | Args | lean-clang ms | clang-O2 ms | clang-O3 ms | ixcc ms | clang-O2 / lean-clang | clang-O3 / lean-clang | ixcc / lean-clang |
| --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| fib | K1 | `40` | 522.75 | 209.21 | 209.11 | 398.97 | 0.400 [0.398, 0.401] | 0.400 [0.397, 0.401] | 0.763 [0.758, 0.764] |
| sum-loop | K1 | `100000000` | 155.51 | 2.11 | 2.05 | 55.07 | 0.014 [0.013, 0.014] | 0.013 [0.013, 0.014] | 0.354 [0.354, 0.355] |
| ackermann | K1 | `3 10` | 74.38 | 35.39 | 35.32 | 69.51 | 0.476 [0.473, 0.476] | 0.475 [0.472, 0.478] | 0.935 [0.927, 0.940] |
| tak | K1 | `24 24 16 8` | 9.04 | 5.34 | 5.37 | 5.62 | 0.594 [0.581, 0.603] | 0.590 [0.583, 0.604] | 0.627 [0.596, 0.644] |
| gcd | K1 | `4660046610375530309 2880067194370816120` | 3.40 | 1.90 | 1.84 | 1.99 | 0.586 [0.537, 0.610] | 0.561 [0.530, 0.600] | 0.605 [0.571, 0.648] |
| collatz | K1 | `1000000` | 491.39 | 134.97 | 134.89 | 274.29 | 0.275 [0.274, 0.275] | 0.274 [0.274, 0.275] | 0.558 [0.558, 0.559] |
| prime-count | K1 | `2000000` | 530.09 | 286.54 | 286.71 | 290.50 | 0.541 [0.540, 0.541] | 0.541 [0.540, 0.541] | 0.548 [0.548, 0.548] |
| even-odd | K1 | `200000` | 5.26 | 1.94 | 1.89 | 2.07 | 0.373 [0.355, 0.409] | 0.359 [0.350, 0.375] | 0.404 [0.366, 0.414] |
| sfib | K1 | `100000000` | 201.25 | 24.15 | 45.75 | 60.79 | 0.120 [0.119, 0.121] | 0.227 [0.227, 0.228] | 0.302 [0.302, 0.302] |

## Peak RSS (KiB)

| Fixture | Rung | lean-clang KiB | clang-O2 KiB | clang-O3 KiB | ixcc KiB |
| --- | --- | ---: | ---: | ---: | ---: |
| fib | K1 | 8780 | 1584 | 1584 | 1584 |
| sum-loop | K1 | 8808 | 1584 | 1584 | 1584 |
| ackermann | K1 | 8726 | 1584 | 1584 | 1584 |
| tak | K1 | 8842 | 1584 | 1584 | 1584 |
| gcd | K1 | 8776 | 1584 | 1584 | 1584 |
| collatz | K1 | 8738 | 1584 | 1584 | 1584 |
| prime-count | K1 | 8758 | 1584 | 1584 | 1584 |
| even-odd | K1 | 14946 | 1584 | 1584 | 1584 |
| sfib | K1 | 8740 | 1584 | 1584 | 1584 |

## Geometric means by rung (ratio to lean-clang)

| Rung | Row | Geomean [95%] | Fixtures |
| --- | --- | ---: | ---: |
| K1 | clang-O2 | 0.263 [0.259, 0.266] | 9 |
| K1 | clang-O3 | 0.278 [0.276, 0.282] | 9 |
| K1 | ixcc | 0.535 [0.526, 0.540] | 9 |

## Measured executable artifacts

| Fixture | Row | Mode | .text B | File B | SHA-256 |
| --- | --- | --- | ---: | ---: | --- |
| fib | lean-clang | `lean-clang` | 2047585 | 4479952 | `b7165c8931f7a89e` |
| fib | clang-O2 | `clang-twin` | 391 | 16184 | `b86fff3c830da6cf` |
| fib | clang-O3 | `clang-twin` | 391 | 16184 | `f4e2f9931ef4d688` |
| fib | ixcc | `standalone-exe` | 1165 | 3122 | `62255efcbe5238a8` |
| sum-loop | lean-clang | `lean-clang` | 2047649 | 4480224 | `7c3410307f4284fd` |
| sum-loop | clang-O2 | `clang-twin` | 359 | 16160 | `32d47f800b4256c4` |
| sum-loop | clang-O3 | `clang-twin` | 361 | 16160 | `2ea41f887914511d` |
| sum-loop | ixcc | `standalone-exe` | 1078 | 3026 | `60b64ec61705c635` |
| ackermann | lean-clang | `lean-clang` | 2048417 | 4480904 | `062911343fc66b89` |
| ackermann | clang-O2 | `clang-twin` | 423 | 16192 | `1e3a1e333de05161` |
| ackermann | clang-O3 | `clang-twin` | 423 | 16192 | `1e3a1e333de05161` |
| ackermann | ixcc | `standalone-exe` | 1154 | 3106 | `8ffc6f872c812aea` |
| tak | lean-clang | `lean-clang` | 2050529 | 4483000 | `8a7d104621028966` |
| tak | clang-O2 | `clang-twin` | 603 | 16184 | `4c86427dbf1111c2` |
| tak | clang-O3 | `clang-twin` | 603 | 16184 | `4c86427dbf1111c2` |
| tak | ixcc | `standalone-exe` | 1312 | 3266 | `fee8351a2f164010` |
| gcd | lean-clang | `lean-clang` | 2048033 | 4480440 | `24a8512bb8c929bb` |
| gcd | clang-O2 | `clang-twin` | 402 | 16152 | `7b82da4528dc3a8f` |
| gcd | clang-O3 | `clang-twin` | 410 | 16152 | `74c1878f3fc12cb5` |
| gcd | ixcc | `standalone-exe` | 1122 | 3074 | `9d83b6f676b87025` |
| collatz | lean-clang | `lean-clang` | 2048673 | 4481344 | `7e8dd31266197747` |
| collatz | clang-O2 | `clang-twin` | 424 | 16160 | `98a722de78a97a9a` |
| collatz | clang-O3 | `clang-twin` | 426 | 16160 | `0eff8df6c183ca02` |
| collatz | ixcc | `standalone-exe` | 1283 | 3234 | `241b1fcdfe688069` |
| prime-count | lean-clang | `lean-clang` | 2048865 | 4481744 | `14cdb529fa10c5cd` |
| prime-count | clang-O2 | `clang-twin` | 487 | 16160 | `e6aeeabeda701420` |
| prime-count | clang-O3 | `clang-twin` | 486 | 16160 | `f43255b92777404d` |
| prime-count | ixcc | `standalone-exe` | 1409 | 3362 | `cd66aeb16b6df7b1` |
| even-odd | lean-clang | `lean-clang` | 2047457 | 4479944 | `3b8a623c203581a2` |
| even-odd | clang-O2 | `clang-twin` | 365 | 16224 | `e05f8c02d6fe981b` |
| even-odd | clang-O3 | `clang-twin` | 365 | 16224 | `f321906d30a9deae` |
| even-odd | ixcc | `standalone-exe` | 1131 | 3090 | `21598dfaf30c33d8` |
| sfib | lean-clang | `lean-clang` | 2047585 | 4479960 | `d7ce50162441bdfe` |
| sfib | clang-O2 | `clang-twin` | 538 | 16160 | `1230abbb31e0d97a` |
| sfib | clang-O3 | `clang-twin` | 588 | 16160 | `ce194c019e55e4fd` |
| sfib | ixcc | `standalone-exe` | 1119 | 3074 | `726e5df2b8f7f948` |
