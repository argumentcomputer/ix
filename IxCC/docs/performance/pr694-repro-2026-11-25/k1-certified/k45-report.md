# K4/K5 benchmark report (process profile, unhardened)

Host: "Intel(R) Xeon(R) 6975P-C", worker CPU 2, load "1.82 1.92 0.89 1/938 23362".
Blocks per fixture: 10. Ratio = row / lean-clang (< 1 is faster than lean-clang); 95% paired percentile-bootstrap intervals.
Build command: `bench-k45 run --rungs K1 --cpu 2 --blocks 10 --gcc --closures ../../fixtures/ixon-v4/bench-k1 --rc off /tmp/pr694-bench/k1-certified`.
IxCC config: `{"bignat":false,"bignat_lib":null,"bignat_lib_sha256":null,"cc":"cc","closures":"../../fixtures/ixon-v4/bench-k1","embed_cert":false,"harness":true,"opt":false,"rc_mode":"off","region_bytes":null,"stack_bytes":null}`.
Toolchains: `{"cc":"cc (Ubuntu 13.3.0-6ubuntu2~24.04.1) 13.3.0","clang":"Ubuntu clang version 18.1.3 (1ubuntu1)","clang++":"Ubuntu clang version 18.1.3 (1ubuntu1)","g++":"g++ (Ubuntu 13.3.0-6ubuntu2~24.04.1) 13.3.0","gcc":"gcc (Ubuntu 13.3.0-6ubuntu2~24.04.1) 13.3.0","ixcc":"../../.lake/build/bin/ixcc","ixcc_sha256":"bcf63d37739d222782a544990e4ec9721ac136ef77814f0a15adb376bb5c9d91","lean":"Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)","leanc":"clang version 22.1.4 (https://github.com/llvm/llvm-project 35990504507d79e0b9deb809c8ee5e1b34ceef20)","objdump":"GNU objdump (GNU Binutils for Ubuntu) 2.42","repository":"0c324194f9d4"}`.

| Fixture | Rung | Args | lean-clang ms | clang-O2 ms | clang-O3 ms | gcc-O2 ms | gcc-O3 ms | ixcc ms | clang-O2 / lean-clang | clang-O3 / lean-clang | gcc-O2 / lean-clang | gcc-O3 / lean-clang | ixcc / lean-clang |
| --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| fib | K1 | `40` | 524.24 | 209.26 | 209.37 | 105.13 | 105.06 | 399.07 | 0.399 [0.395, 0.400] | 0.399 [0.395, 0.401] | 0.201 [0.199, 0.201] | 0.201 [0.198, 0.201] | 0.761 [0.753, 0.764] |
| sum-loop | K1 | `100000000` | 155.44 | 2.04 | 2.17 | 28.28 | 28.25 | 55.05 | 0.013 [0.013, 0.014] | 0.014 [0.014, 0.014] | 0.182 [0.181, 0.183] | 0.182 [0.181, 0.182] | 0.354 [0.353, 0.356] |
| ackermann | K1 | `3 10` | 74.37 | 35.36 | 35.36 | 16.06 | 16.22 | 69.21 | 0.477 [0.473, 0.479] | 0.476 [0.475, 0.477] | 0.216 [0.212, 0.219] | 0.218 [0.215, 0.219] | 0.930 [0.920, 0.943] |
| tak | K1 | `24 24 16 8` | 8.95 | 5.36 | 5.24 | 4.75 | 3.99 | 5.58 | 0.597 [0.581, 0.618] | 0.593 [0.581, 0.600] | 0.529 [0.504, 0.548] | 0.442 [0.433, 0.472] | 0.617 [0.604, 0.639] |
| gcd | K1 | `4660046610375530309 2880067194370816120` | 3.33 | 1.80 | 1.94 | 1.85 | 1.84 | 2.03 | 0.553 [0.498, 0.603] | 0.578 [0.546, 0.635] | 0.560 [0.519, 0.610] | 0.571 [0.538, 0.602] | 0.607 [0.577, 0.661] |
| collatz | K1 | `1000000` | 492.51 | 135.39 | 134.89 | 186.57 | 186.49 | 239.91 | 0.275 [0.274, 0.276] | 0.274 [0.273, 0.274] | 0.379 [0.378, 0.379] | 0.379 [0.378, 0.379] | 0.487 [0.486, 0.488] |
| prime-count | K1 | `2000000` | 530.28 | 286.70 | 286.68 | 468.67 | 468.75 | 289.61 | 0.541 [0.540, 0.541] | 0.541 [0.540, 0.541] | 0.884 [0.884, 0.884] | 0.884 [0.884, 0.884] | 0.546 [0.546, 0.547] |
| even-odd | K1 | `200000` | 5.27 | 2.01 | 1.95 | 2.08 | 1.93 | 2.01 | 0.361 [0.353, 0.402] | 0.365 [0.360, 0.382] | 0.379 [0.353, 0.412] | 0.368 [0.332, 0.391] | 0.378 [0.365, 0.402] |
| sfib | K1 | `100000000` | 201.08 | 24.25 | 45.66 | 28.40 | 28.38 | 71.65 | 0.121 [0.120, 0.121] | 0.227 [0.226, 0.228] | 0.141 [0.141, 0.142] | 0.141 [0.141, 0.143] | 0.356 [0.355, 0.357] |

## Peak RSS (KiB)

| Fixture | Rung | lean-clang KiB | clang-O2 KiB | clang-O3 KiB | gcc-O2 KiB | gcc-O3 KiB | ixcc KiB |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| fib | K1 | 8784 | 1584 | 1584 | 1584 | 1584 | 1584 |
| sum-loop | K1 | 8798 | 1584 | 1584 | 1584 | 1584 | 1584 |
| ackermann | K1 | 8882 | 1584 | 1584 | 1584 | 1584 | 1584 |
| tak | K1 | 8752 | 1584 | 1584 | 1584 | 1584 | 1584 |
| gcd | K1 | 8726 | 1584 | 1584 | 1584 | 1584 | 1584 |
| collatz | K1 | 8724 | 1584 | 1584 | 1584 | 1584 | 1584 |
| prime-count | K1 | 8776 | 1584 | 1584 | 1584 | 1584 | 1584 |
| even-odd | K1 | 14978 | 1584 | 1584 | 1584 | 1584 | 1584 |
| sfib | K1 | 8762 | 1584 | 1584 | 1584 | 1584 | 1584 |

## Geometric means by rung (ratio to lean-clang)

| Rung | Row | Geomean [95%] | Fixtures |
| --- | --- | ---: | ---: |
| K1 | clang-O2 | 0.259 [0.256, 0.264] | 9 |
| K1 | clang-O3 | 0.282 [0.279, 0.285] | 9 |
| K1 | gcc-O2 | 0.326 [0.322, 0.332] | 9 |
| K1 | gcc-O3 | 0.320 [0.315, 0.323] | 9 |
| K1 | ixcc | 0.531 [0.527, 0.538] | 9 |

## Measured executable artifacts

| Fixture | Row | Mode | .text B | File B | SHA-256 |
| --- | --- | --- | ---: | ---: | --- |
| fib | lean-clang | `lean-clang` | 2047585 | 4479952 | `b7165c8931f7a89e` |
| fib | clang-O2 | `clang-twin` | 391 | 16184 | `b86fff3c830da6cf` |
| fib | clang-O3 | `clang-twin` | 391 | 16184 | `f4e2f9931ef4d688` |
| fib | gcc-O2 | `gcc-twin` | 1143 | 16128 | `1b9f344c7b02a926` |
| fib | gcc-O3 | `gcc-twin` | 1143 | 16128 | `1b9f344c7b02a926` |
| fib | ixcc | `standalone-exe` | 1165 | 3122 | `62255efcbe5238a8` |
| sum-loop | lean-clang | `lean-clang` | 2047649 | 4480224 | `7c3410307f4284fd` |
| sum-loop | clang-O2 | `clang-twin` | 359 | 16160 | `32d47f800b4256c4` |
| sum-loop | clang-O3 | `clang-twin` | 361 | 16160 | `2ea41f887914511d` |
| sum-loop | gcc-O2 | `gcc-twin` | 377 | 16104 | `f438ef3d76bed3e6` |
| sum-loop | gcc-O3 | `gcc-twin` | 377 | 16104 | `f438ef3d76bed3e6` |
| sum-loop | ixcc | `standalone-exe` | 1078 | 3026 | `60b64ec61705c635` |
| ackermann | lean-clang | `lean-clang` | 2048417 | 4480904 | `062911343fc66b89` |
| ackermann | clang-O2 | `clang-twin` | 423 | 16192 | `1e3a1e333de05161` |
| ackermann | clang-O3 | `clang-twin` | 423 | 16192 | `1e3a1e333de05161` |
| ackermann | gcc-O2 | `gcc-twin` | 773 | 16128 | `043e4b6fee6d0cc1` |
| ackermann | gcc-O3 | `gcc-twin` | 773 | 16128 | `043e4b6fee6d0cc1` |
| ackermann | ixcc | `standalone-exe` | 1154 | 3106 | `8ffc6f872c812aea` |
| tak | lean-clang | `lean-clang` | 2050529 | 4483000 | `8a7d104621028966` |
| tak | clang-O2 | `clang-twin` | 603 | 16184 | `4c86427dbf1111c2` |
| tak | clang-O3 | `clang-twin` | 603 | 16184 | `4c86427dbf1111c2` |
| tak | gcc-O2 | `gcc-twin` | 597 | 16176 | `b38e5b1c8bbfbaf4` |
| tak | gcc-O3 | `gcc-twin` | 4310 | 20272 | `7a38ba36601d02da` |
| tak | ixcc | `standalone-exe` | 1312 | 3266 | `fee8351a2f164010` |
| gcd | lean-clang | `lean-clang` | 2048033 | 4480440 | `24a8512bb8c929bb` |
| gcd | clang-O2 | `clang-twin` | 402 | 16152 | `7b82da4528dc3a8f` |
| gcd | clang-O3 | `clang-twin` | 410 | 16152 | `74c1878f3fc12cb5` |
| gcd | gcc-O2 | `gcc-twin` | 393 | 16096 | `6026be4e3ee4c95e` |
| gcd | gcc-O3 | `gcc-twin` | 393 | 16096 | `6026be4e3ee4c95e` |
| gcd | ixcc | `standalone-exe` | 1132 | 3090 | `556d3407e4fc1e12` |
| collatz | lean-clang | `lean-clang` | 2048673 | 4481344 | `7e8dd31266197747` |
| collatz | clang-O2 | `clang-twin` | 424 | 16160 | `98a722de78a97a9a` |
| collatz | clang-O3 | `clang-twin` | 426 | 16160 | `0eff8df6c183ca02` |
| collatz | gcc-O2 | `gcc-twin` | 409 | 16104 | `b688d5de1a83d210` |
| collatz | gcc-O3 | `gcc-twin` | 409 | 16104 | `8ebd74e2fb64ab4f` |
| collatz | ixcc | `standalone-exe` | 1289 | 3250 | `e3ca79b17187f07a` |
| prime-count | lean-clang | `lean-clang` | 2048865 | 4481744 | `14cdb529fa10c5cd` |
| prime-count | clang-O2 | `clang-twin` | 487 | 16160 | `e6aeeabeda701420` |
| prime-count | clang-O3 | `clang-twin` | 486 | 16160 | `f43255b92777404d` |
| prime-count | gcc-O2 | `gcc-twin` | 441 | 16104 | `1508bef68dcf0f45` |
| prime-count | gcc-O3 | `gcc-twin` | 441 | 16104 | `1508bef68dcf0f45` |
| prime-count | ixcc | `standalone-exe` | 1414 | 3362 | `43e8126be300a920` |
| even-odd | lean-clang | `lean-clang` | 2047457 | 4479944 | `3b8a623c203581a2` |
| even-odd | clang-O2 | `clang-twin` | 365 | 16224 | `e05f8c02d6fe981b` |
| even-odd | clang-O3 | `clang-twin` | 365 | 16224 | `f321906d30a9deae` |
| even-odd | gcc-O2 | `gcc-twin` | 406 | 16168 | `0342497ae2bb5774` |
| even-odd | gcc-O3 | `gcc-twin` | 406 | 16168 | `0342497ae2bb5774` |
| even-odd | ixcc | `standalone-exe` | 1131 | 3090 | `21598dfaf30c33d8` |
| sfib | lean-clang | `lean-clang` | 2047585 | 4479960 | `d7ce50162441bdfe` |
| sfib | clang-O2 | `clang-twin` | 538 | 16160 | `1230abbb31e0d97a` |
| sfib | clang-O3 | `clang-twin` | 588 | 16160 | `ce194c019e55e4fd` |
| sfib | gcc-O2 | `gcc-twin` | 377 | 16096 | `8205f305082f3877` |
| sfib | gcc-O3 | `gcc-twin` | 377 | 16096 | `8205f305082f3877` |
| sfib | ixcc | `standalone-exe` | 1142 | 3090 | `26dad1223c24c355` |
