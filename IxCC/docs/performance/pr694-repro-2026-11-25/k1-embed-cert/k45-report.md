# K4/K5 benchmark report (process profile, unhardened)

Host: "Intel(R) Xeon(R) 6975P-C", worker CPU 2, load "1.51 1.80 1.01 1/934 29583".
Blocks per fixture: 10. Ratio = row / lean-clang (< 1 is faster than lean-clang); 95% paired percentile-bootstrap intervals.
Build command: `bench-k45 run --rungs K1 --cpu 2 --blocks 10 --closures ../../fixtures/ixon-v4/bench-k1 --rc off --embed-cert /tmp/pr694-bench/k1-embed-cert`.
IxCC config: `{"bignat":false,"bignat_lib":null,"bignat_lib_sha256":null,"cc":"cc","closures":"../../fixtures/ixon-v4/bench-k1","embed_cert":true,"harness":true,"opt":false,"rc_mode":"off","region_bytes":null,"stack_bytes":null}`.
Toolchains: `{"cc":"cc (Ubuntu 13.3.0-6ubuntu2~24.04.1) 13.3.0","clang":"Ubuntu clang version 18.1.3 (1ubuntu1)","clang++":"Ubuntu clang version 18.1.3 (1ubuntu1)","g++":"g++ (Ubuntu 13.3.0-6ubuntu2~24.04.1) 13.3.0","gcc":"gcc (Ubuntu 13.3.0-6ubuntu2~24.04.1) 13.3.0","ixcc":"../../.lake/build/bin/ixcc","ixcc_sha256":"bcf63d37739d222782a544990e4ec9721ac136ef77814f0a15adb376bb5c9d91","lean":"Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)","leanc":"clang version 22.1.4 (https://github.com/llvm/llvm-project 35990504507d79e0b9deb809c8ee5e1b34ceef20)","objdump":"GNU objdump (GNU Binutils for Ubuntu) 2.42","repository":"0c324194f9d4"}`.

| Fixture | Rung | Args | lean-clang ms | clang-O2 ms | clang-O3 ms | ixcc ms | clang-O2 / lean-clang | clang-O3 / lean-clang | ixcc / lean-clang |
| --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| fib | K1 | `40` | 522.81 | 209.25 | 209.30 | 399.03 | 0.400 [0.398, 0.401] | 0.400 [0.399, 0.401] | 0.763 [0.759, 0.764] |
| sum-loop | K1 | `100000000` | 155.49 | 2.11 | 2.10 | 55.20 | 0.014 [0.013, 0.015] | 0.014 [0.012, 0.015] | 0.355 [0.354, 0.356] |
| ackermann | K1 | `3 10` | 74.44 | 35.39 | 35.44 | 69.83 | 0.475 [0.474, 0.477] | 0.476 [0.475, 0.478] | 0.937 [0.923, 0.944] |
| tak | K1 | `24 24 16 8` | 9.04 | 5.43 | 5.54 | 5.69 | 0.596 [0.582, 0.610] | 0.613 [0.599, 0.627] | 0.625 [0.597, 0.647] |
| gcd | K1 | `4660046610375530309 2880067194370816120` | 3.23 | 1.93 | 1.88 | 1.96 | 0.596 [0.542, 0.617] | 0.586 [0.541, 0.622] | 0.606 [0.577, 0.715] |
| collatz | K1 | `1000000` | 491.28 | 134.92 | 134.97 | 239.81 | 0.275 [0.274, 0.275] | 0.275 [0.274, 0.275] | 0.488 [0.488, 0.489] |
| prime-count | K1 | `2000000` | 530.15 | 286.73 | 286.69 | 289.78 | 0.541 [0.541, 0.541] | 0.541 [0.540, 0.541] | 0.547 [0.546, 0.547] |
| even-odd | K1 | `200000` | 5.17 | 1.96 | 1.94 | 2.09 | 0.379 [0.359, 0.410] | 0.377 [0.366, 0.408] | 0.399 [0.374, 0.435] |
| sfib | K1 | `100000000` | 201.31 | 24.20 | 45.81 | 71.69 | 0.120 [0.120, 0.121] | 0.228 [0.227, 0.228] | 0.356 [0.355, 0.357] |

## Peak RSS (KiB)

| Fixture | Rung | lean-clang KiB | clang-O2 KiB | clang-O3 KiB | ixcc KiB |
| --- | --- | ---: | ---: | ---: | ---: |
| fib | K1 | 8776 | 1584 | 1584 | 1584 |
| sum-loop | K1 | 8824 | 1584 | 1584 | 1584 |
| ackermann | K1 | 8740 | 1584 | 1584 | 1584 |
| tak | K1 | 8764 | 1584 | 1584 | 1584 |
| gcd | K1 | 8778 | 1584 | 1584 | 1584 |
| collatz | K1 | 8718 | 1584 | 1584 | 1584 |
| prime-count | K1 | 8816 | 1584 | 1584 | 1584 |
| even-odd | K1 | 14858 | 1584 | 1584 | 1584 |
| sfib | K1 | 8748 | 1584 | 1584 | 1584 |

## Geometric means by rung (ratio to lean-clang)

| Rung | Row | Geomean [95%] | Fixtures |
| --- | --- | ---: | ---: |
| K1 | clang-O2 | 0.264 [0.261, 0.268] | 9 |
| K1 | clang-O3 | 0.283 [0.279, 0.289] | 9 |
| K1 | ixcc | 0.536 [0.530, 0.546] | 9 |

## Measured executable artifacts

| Fixture | Row | Mode | .text B | File B | SHA-256 |
| --- | --- | --- | ---: | ---: | --- |
| fib | lean-clang | `lean-clang` | 2047585 | 4479952 | `b7165c8931f7a89e` |
| fib | clang-O2 | `clang-twin` | 391 | 16184 | `b86fff3c830da6cf` |
| fib | clang-O3 | `clang-twin` | 391 | 16184 | `f4e2f9931ef4d688` |
| fib | ixcc | `standalone-exe` | 1165 | 82832 | `fb25038683bad782` |
| sum-loop | lean-clang | `lean-clang` | 2047649 | 4480224 | `7c3410307f4284fd` |
| sum-loop | clang-O2 | `clang-twin` | 359 | 16160 | `32d47f800b4256c4` |
| sum-loop | clang-O3 | `clang-twin` | 361 | 16160 | `2ea41f887914511d` |
| sum-loop | ixcc | `standalone-exe` | 1078 | 2639392 | `0298ac243c2fcab7` |
| ackermann | lean-clang | `lean-clang` | 2048417 | 4480904 | `062911343fc66b89` |
| ackermann | clang-O2 | `clang-twin` | 423 | 16192 | `1e3a1e333de05161` |
| ackermann | clang-O3 | `clang-twin` | 423 | 16192 | `1e3a1e333de05161` |
| ackermann | ixcc | `standalone-exe` | 1154 | 2590960 | `c7eefd1270847ee9` |
| tak | lean-clang | `lean-clang` | 2050529 | 4483000 | `8a7d104621028966` |
| tak | clang-O2 | `clang-twin` | 603 | 16184 | `4c86427dbf1111c2` |
| tak | clang-O3 | `clang-twin` | 603 | 16184 | `4c86427dbf1111c2` |
| tak | ixcc | `standalone-exe` | 1312 | 148344 | `5d95eb0fd3485a57` |
| gcd | lean-clang | `lean-clang` | 2048033 | 4480440 | `24a8512bb8c929bb` |
| gcd | clang-O2 | `clang-twin` | 402 | 16152 | `7b82da4528dc3a8f` |
| gcd | clang-O3 | `clang-twin` | 410 | 16152 | `74c1878f3fc12cb5` |
| gcd | ixcc | `standalone-exe` | 1132 | 248240 | `efb80f442a798883` |
| collatz | lean-clang | `lean-clang` | 2048673 | 4481344 | `7e8dd31266197747` |
| collatz | clang-O2 | `clang-twin` | 424 | 16160 | `98a722de78a97a9a` |
| collatz | clang-O3 | `clang-twin` | 426 | 16160 | `0eff8df6c183ca02` |
| collatz | ixcc | `standalone-exe` | 1289 | 2652048 | `1184a64de7af9936` |
| prime-count | lean-clang | `lean-clang` | 2048865 | 4481744 | `14cdb529fa10c5cd` |
| prime-count | clang-O2 | `clang-twin` | 487 | 16160 | `e6aeeabeda701420` |
| prime-count | clang-O3 | `clang-twin` | 486 | 16160 | `f43255b92777404d` |
| prime-count | ixcc | `standalone-exe` | 1414 | 2653352 | `b9e383a8f0d10ab2` |
| even-odd | lean-clang | `lean-clang` | 2047457 | 4479944 | `3b8a623c203581a2` |
| even-odd | clang-O2 | `clang-twin` | 365 | 16224 | `e05f8c02d6fe981b` |
| even-odd | clang-O3 | `clang-twin` | 365 | 16224 | `f321906d30a9deae` |
| even-odd | ixcc | `standalone-exe` | 1131 | 98296 | `b0ab7deb468b3c7f` |
| sfib | lean-clang | `lean-clang` | 2047585 | 4479960 | `d7ce50162441bdfe` |
| sfib | clang-O2 | `clang-twin` | 538 | 16160 | `1230abbb31e0d97a` |
| sfib | clang-O3 | `clang-twin` | 588 | 16160 | `ce194c019e55e4fd` |
| sfib | ixcc | `standalone-exe` | 1142 | 139488 | `234d713119219b27` |
