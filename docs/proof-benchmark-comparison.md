# Init proof benchmark comparison

Measured on October 16–17, 2026, using 48 logical CPUs of an Intel Xeon
Platinum 8559C, 499 GiB of host RAM, local NVMe storage, and one NVIDIA RTX
PRO 6000 Blackwell Server GPU for GPU runs.

Proving timings assume reusable preprocessing and proving keys are already
available. One-time key preparation is shown separately. Full prover processes
still load and authenticate those artifacts; core proving starts after the
circuit and keys are loaded. Times are rounded to the nearest second and
written as minutes and seconds.

Proof size uses the largest available proof encoding: the ix envelope for
KZG and the Solidity payload for PLONK. Transaction calldata includes
additional arguments and is accounted for in the gas measurements.

The GPU KZG pipeline starts with the saved Init FRI proof and produces the
final recursive KZG proof. It uses authenticated Filecoin parameters for
BLS12-381 and Ignition parameters for BN254. Initial aggregation and FRI
compression are outside these timings.

| GPU KZG measurement     |       BLS12-381 |           BN254 |
| ----------------------- | --------------: | --------------: |
| First KZG stage         |           2m27s |           2m16s |
| Recursive KZG stage     |           1m32s |           0m45s |
| **Total proving time**  |       **3m59s** |        **3m0s** |
| Peak host RAM           |      175.79 GiB |      175.29 GiB |
| Sampled peak GPU memory |       64.70 GiB |       57.27 GiB |
| **Proof size**          | **2,189 bytes** | **1,917 bytes** |

Total proving time is the sum of the two worker processes. BN254's complete
driver, including orchestration overhead, took 3m1s. Both stages reuse fixed
preprocessing and start fresh worker processes; OS page-cache state is
uncontrolled. These are one run per curve; both proofs passed independent
CPU verification. BN254 took approximately **25% less proving time**.

The PLONK wrapper runs after KZG compression. Its timings are additional to
the KZG pipeline above.

| PLONK measurement        |   BLS12-381 CPU |     BN254 CPU |     BN254 GPU |
| ------------------------ | --------------: | ------------: | ------------: |
| Constraints              |      21,184,618 |    14,689,440 |    14,689,440 |
| Domain                   |             2²⁵ |           2²⁴ |           2²⁴ |
| One-time key preparation |          20m17s |         5m58s |         5m57s |
| **Core proving time**    |        **2m7s** |     **0m54s** |     **0m11s** |
| **Full prover process**  |       **4m54s** |     **1m14s** |     **0m32s** |
| Peak host RAM            |       53.63 GiB |     25.19 GiB |     20.64 GiB |
| Sampled peak GPU memory  |               — |             — |     19.26 GiB |
| **Proof size**           | **1,184 bytes** | **864 bytes** | **864 bytes** |

The matched BN254 core timings are medians of three runs with the same loaded
circuit, keys and witness. GPU acceleration gives a **4.75× speedup** over
CPU. BLS core proving and each complete process timing come from
one run. Full process time includes startup, artifact authentication/loading,
witness assembly, proving, verification and output.

Key preparation covers SRS import, Lagrange conversion and generation of the
circuit's proving and verifying keys. Parameter downloads and circuit
compilation are excluded. This work is reusable across proofs and is not
included in either proving-time row. CPU and GPU use the same Lagrange basis
and keys. The current cache binds artifacts to a helper executable, so the
GPU helper required a separate preparation run despite that equivalence.

**TODO:** Allow validated Lagrange-basis reuse across compatible CPU/GPU
helper builds without requiring the same executable hash. Preserve SRS and
domain binding, content hashes, format compatibility and basis validation;
keep circuit and proving-key compatibility checks separate.

GPU process time and host RAM come from a separate production CLI run, using
the same circuit and byte-identical proving and verifying keys as the CPU
baseline. Its proof passed independent CPU verification, including rejection
of an altered claim and proof. Key preparation is excluded. GPU device
memory uses the earlier repeated benchmark; polling in the standalone run
missed the short peak. Its native allocation pool recorded an 18.59 GiB
reservation peak, excluding driver overhead. Device samples may miss peaks.

Verification costs use **1.1718 gwei**, the arithmetic mean of Etherscan's
daily averages for **September 15–October 14, 2026**, the latest 30 days
available through [YCharts](https://ycharts.com/indicators/ethereum_average_gas_price)
when this comparison was prepared. The USD conversion uses
**$2,439.96 per ETH**, the [October 16 price](https://ycharts.com/indicators/ethereum_price).
That is approximately **$2.859 per million gas**.

| Proof                              | Verification transaction gas | Estimated cost |
| ---------------------------------- | ---------------------------: | -------------: |
| BLS12-381 KZG, Keccak v5 reference |                  **825,229** |      **$2.36** |
| BLS12-381 CPU PLONK                |                  **404,637** |      **$1.16** |
| BN254 CPU PLONK                    |                  **320,103** |      **$0.92** |
| BN254 GPU PLONK                    |                  **320,091** |      **$0.92** |

These are complete verification transactions, including calldata and the
PLONK claim-digest adapter, but excluding contract deployment. Measurements
use local Anvil with Osaka execution rules and solc 0.8.37, optimizer 200,
via-IR and Prague bytecode. The 12-gas difference between BN254 CPU and GPU
proofs comes from calldata bytes; the verifier execution costs are identical.

The KZG row verifies the aggregate BLS12-381 Keccak v5 proof. The PLONK rows
verify wrappers around the current BLAKE3 KZG proofs; the KZG reference uses
a different transcript.

The dollar estimate is `transaction gas × average gwei × 10⁻⁹ × ETH/USD`.
It uses the historical gas average rather than a live gas quote.

The [recorded results](benchmarks/init-proof-comparison-2026-10-17.json)
preserve exact timings, memory measurements, proof and artifact identities,
verification results, daily gas-price inputs and source-report hashes.
Implementation context is in the [PLONK status record](bls-plonk-wrapper-status.md)
and [KZG compression README](../crates/proof-compression/README.md).
