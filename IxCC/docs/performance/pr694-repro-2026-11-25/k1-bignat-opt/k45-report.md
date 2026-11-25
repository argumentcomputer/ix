# K4/K5 benchmark report (process profile, unhardened)

Host: "Intel(R) Xeon(R) 6975P-C", worker CPU 2, load "1.37 2.88 2.81 1/932 50033".
Blocks per fixture: 10. Ratio = row / lean-clang (< 1 is faster than lean-clang); 95% paired percentile-bootstrap intervals.
Build command: `bench-k45 run --rungs K1 --cpu 2 --blocks 10 --closures ../../fixtures/ixon-v4/bench-k1 --rc off --bignat --opt --bignat-lib /tmp/pr694-bench/bignat-lib.json /tmp/pr694-bench/k1-bignat-opt`.
IxCC config: `{"bignat":true,"bignat_lib":"/tmp/pr694-bench/bignat-lib.json","bignat_lib_sha256":"7cba24f00900b9c060eaf6c4e08e6d2bc515319cb5c9d22684099f52f9a784fb","cc":"cc","closures":"../../fixtures/ixon-v4/bench-k1","embed_cert":false,"harness":true,"opt":true,"rc_mode":"off","region_bytes":null,"stack_bytes":null}`.
Toolchains: `{"cc":"cc (Ubuntu 13.3.0-6ubuntu2~24.04.1) 13.3.0","clang":"Ubuntu clang version 18.1.3 (1ubuntu1)","clang++":"Ubuntu clang version 18.1.3 (1ubuntu1)","g++":"g++ (Ubuntu 13.3.0-6ubuntu2~24.04.1) 13.3.0","gcc":"gcc (Ubuntu 13.3.0-6ubuntu2~24.04.1) 13.3.0","ixcc":"../../.lake/build/bin/ixcc","ixcc_sha256":"bcf63d37739d222782a544990e4ec9721ac136ef77814f0a15adb376bb5c9d91","lean":"Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)","leanc":"clang version 22.1.4 (https://github.com/llvm/llvm-project 35990504507d79e0b9deb809c8ee5e1b34ceef20)","objdump":"GNU objdump (GNU Binutils for Ubuntu) 2.42","repository":"0c324194f9d4"}`.

| Fixture | Rung | Args | lean-clang ms | clang-O2 ms | clang-O3 ms | ixcc ms | clang-O2 / lean-clang | clang-O3 / lean-clang | ixcc / lean-clang |
| --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| fib | K1 | `40` | 524.31 | 209.10 | 209.30 | 710.88 | 0.399 [0.397, 0.401] | 0.399 [0.396, 0.400] | 1.355 [1.345, 1.359] |
| sum-loop | K1 | `100000000` | 155.42 | 2.13 | 2.11 | 99.79 | 0.014 [0.013, 0.015] | 0.014 [0.013, 0.015] | 0.642 [0.640, 0.645] |
| ackermann | K1 | `3 10` | 74.53 | 35.45 | 35.48 | 87.56 | 0.475 [0.475, 0.477] | 0.476 [0.475, 0.477] | 1.173 [1.158, 1.188] |
| tak | K1 | `24 24 16 8` | 9.08 | 5.29 | 5.36 | 7.86 | 0.590 [0.581, 0.594] | 0.590 [0.579, 0.601] | 0.864 [0.834, 0.895] |
| gcd | K1 | `4660046610375530309 2880067194370816120` | 3.24 | 1.90 | 1.89 | 1.96 | 0.580 [0.558, 0.614] | 0.581 [0.552, 0.653] | 0.615 [0.577, 0.657] |
| collatz | K1 | `1000000` | 491.43 | 134.89 | 135.02 | 945.53 | 0.274 [0.274, 0.275] | 0.275 [0.274, 0.275] | 1.924 [1.923, 1.925] |
| prime-count | K1 | `2000000` | 530.40 | 286.69 | 286.93 | 489.86 | 0.540 [0.540, 0.540] | 0.541 [0.540, 0.541] | 0.924 [0.923, 0.925] |
| even-odd | K1 | `200000` | 5.30 | 2.10 | 2.00 | 2.11 | 0.401 [0.376, 0.411] | 0.373 [0.359, 0.401] | 0.390 [0.379, 0.444] |
| sfib | K1 | `100000000` | 202.11 | 24.33 | 45.75 | 247.21 | 0.120 [0.120, 0.121] | 0.227 [0.224, 0.228] | 1.221 [1.215, 1.231] |

## Peak RSS (KiB)

| Fixture | Rung | lean-clang KiB | clang-O2 KiB | clang-O3 KiB | ixcc KiB |
| --- | --- | ---: | ---: | ---: | ---: |
| fib | K1 | 8820 | 1584 | 1584 | 1584 |
| sum-loop | K1 | 8800 | 1584 | 1584 | 1584 |
| ackermann | K1 | 8818 | 1584 | 1584 | 1584 |
| tak | K1 | 8798 | 1584 | 1584 | 1584 |
| gcd | K1 | 8778 | 1584 | 1584 | 1584 |
| collatz | K1 | 8724 | 1584 | 1584 | 1584 |
| prime-count | K1 | 8806 | 1584 | 1584 | 1584 |
| even-odd | K1 | 14964 | 1584 | 1584 | 1584 |
| sfib | K1 | 8764 | 1584 | 1584 | 1584 |

## Geometric means by rung (ratio to lean-clang)

| Rung | Row | Geomean [95%] | Fixtures |
| --- | --- | ---: | ---: |
| K1 | clang-O2 | 0.265 [0.262, 0.268] | 9 |
| K1 | clang-O3 | 0.281 [0.278, 0.288] | 9 |
| K1 | ixcc | 0.917 [0.910, 0.932] | 9 |

## Measured executable artifacts

| Fixture | Row | Mode | .text B | File B | SHA-256 |
| --- | --- | --- | ---: | ---: | --- |
| fib | lean-clang | `lean-clang` | 2047585 | 4479952 | `b7165c8931f7a89e` |
| fib | clang-O2 | `clang-twin` | 391 | 16184 | `b86fff3c830da6cf` |
| fib | clang-O3 | `clang-twin` | 391 | 16184 | `f4e2f9931ef4d688` |
| fib | ixcc | `standalone-exe` | 7577 | 9538 | `d1e4281273904d98` |
| sum-loop | lean-clang | `lean-clang` | 2047649 | 4480224 | `7c3410307f4284fd` |
| sum-loop | clang-O2 | `clang-twin` | 359 | 16160 | `32d47f800b4256c4` |
| sum-loop | clang-O3 | `clang-twin` | 361 | 16160 | `2ea41f887914511d` |
| sum-loop | ixcc | `standalone-exe` | 7121 | 9074 | `23e449f7044a69a9` |
| ackermann | lean-clang | `lean-clang` | 2048417 | 4480904 | `062911343fc66b89` |
| ackermann | clang-O2 | `clang-twin` | 423 | 16192 | `1e3a1e333de05161` |
| ackermann | clang-O3 | `clang-twin` | 423 | 16192 | `1e3a1e333de05161` |
| ackermann | ixcc | `standalone-exe` | 7592 | 9538 | `e903bb7b13718d93` |
| tak | lean-clang | `lean-clang` | 2050529 | 4483000 | `8a7d104621028966` |
| tak | clang-O2 | `clang-twin` | 603 | 16184 | `4c86427dbf1111c2` |
| tak | clang-O3 | `clang-twin` | 603 | 16184 | `4c86427dbf1111c2` |
| tak | ixcc | `standalone-exe` | 8902 | 10850 | `a9e654b7b6be4cc0` |
| gcd | lean-clang | `lean-clang` | 2048033 | 4480440 | `24a8512bb8c929bb` |
| gcd | clang-O2 | `clang-twin` | 402 | 16152 | `7b82da4528dc3a8f` |
| gcd | clang-O3 | `clang-twin` | 410 | 16152 | `74c1878f3fc12cb5` |
| gcd | ixcc | `standalone-exe` | 24946 | 26898 | `ae9c809562f11d35` |
| collatz | lean-clang | `lean-clang` | 2048673 | 4481344 | `7e8dd31266197747` |
| collatz | clang-O2 | `clang-twin` | 424 | 16160 | `98a722de78a97a9a` |
| collatz | clang-O3 | `clang-twin` | 426 | 16160 | `0eff8df6c183ca02` |
| collatz | ixcc | `standalone-exe` | 52886 | 54834 | `c54d7ebf6b007ffd` |
| prime-count | lean-clang | `lean-clang` | 2048865 | 4481744 | `14cdb529fa10c5cd` |
| prime-count | clang-O2 | `clang-twin` | 487 | 16160 | `e6aeeabeda701420` |
| prime-count | clang-O3 | `clang-twin` | 486 | 16160 | `f43255b92777404d` |
| prime-count | ixcc | `standalone-exe` | 39092 | 41042 | `e5325109837cc186` |
| even-odd | lean-clang | `lean-clang` | 2047457 | 4479944 | `3b8a623c203581a2` |
| even-odd | clang-O2 | `clang-twin` | 365 | 16224 | `e05f8c02d6fe981b` |
| even-odd | clang-O3 | `clang-twin` | 365 | 16224 | `f321906d30a9deae` |
| even-odd | ixcc | `standalone-exe` | 4061 | 6018 | `565ec522441df7e5` |
| sfib | lean-clang | `lean-clang` | 2047585 | 4479960 | `d7ce50162441bdfe` |
| sfib | clang-O2 | `clang-twin` | 538 | 16160 | `1230abbb31e0d97a` |
| sfib | clang-O3 | `clang-twin` | 588 | 16160 | `ce194c019e55e4fd` |
| sfib | ixcc | `standalone-exe` | 16454 | 18402 | `d74f8fe33df61708` |
