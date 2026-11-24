# Compressed Nat.add_comm root, release 0.5

`nat-add-comm.ixon-proof` is a recursive KZG proof of `Nat.add_comm` + the
default 108-role table's aggregate root under the bundled 0.5 verifying keys
(Protocol `v6`, 128-bit `Fp^3` FRI, unified `root-layout.ixl` covering `Nat`,
`Init+Std`, and full `Mathlib` 4.34.1).
`lake test -- compression-cli` checks that `ix verify` accepts it, and that it
refuses the same proof under another claim. Replace it whenever the release
changes (see "Deriving the verifying keys" in `crates/proof-compression/README.md`).

## Artifact identity

- Format: serialized `Ixon.Proof`, a `CheckEnv` claim with an `IXBN` recursive
  KZG packet
- Ixon content address (BLAKE3):
  `8b71d46ecceae7c06aa888fd6b8850fa70d28add7fa1ad3083187c093b99a672`
- SHA-256: `d3706dba36d199ce8aca66111726774cc090559e547b203857b28a3a3475d520`
- Size: 2,020 bytes
- Claim digest (BLAKE3 of the claim):
  `c9f440791f4be07cca16a1afe221ce2138a9cc508c8bf74c28f47cf6f567ddf0`
- Role table: `c60dd3126e86fe6d5221f514a229569a30d1c1075f88f3b23243df82da8194b7`
  (the default role table, validated in the proof)
- Root layout: `verifying-keys/0.5/root-layout.ixl` (95 bytes, BLAKE3
  `035f3b31e438becfe9294b792e7b0cb9aef8a10d073216731ac171c10cdd5748`,
  `--headroom 1` union over `Nat.add_comm`, `Init+Std`, and full `Mathlib` 4.34.1)
- Recursive verifying key: `verifying-keys/0.5/recursive-vk.bin`, BLAKE3
  `adb2415c05975b848ad38f123a5e49d718ad6a63a094d2e852634da9923e1aa5`
  (ID `07b533959666cf26b9ed44baeda8a2c26bc839591b329c2ccc3d2f8622976914`),
  under the released Aztec Ignition setup

## Inputs and producer

- Environment: `Nat.add_comm` together with the 108 default-table roles
  (`IxC/Kernel/Key.lean`), compiled into `nat-default-roles.ixe`
- Aggregate root: `c825ae9a2dacdea5928696b6ee4638d3acfd64f7540aca2322f84b394b7ab3ff`
  (`ix verify --aggregate` PASS with zero `--allow-*` flags)
- Backends: Protocol `v6` (`Fp^3`, `Parameters::DEFAULT`: `lb=2, q=128, qpow=20`),
  formal IxVM artifact `e9021411…` and formal aggregation key BLAKE3
  `d3813ae554af0aa6a24c5c72c796e17403756aa1f9cabbb08519ed4d767c9f13`
  (artifact `96aefd74…`)
- Host: NVIDIA RTX PRO 6000 Blackwell (96 GiB VRAM, `sm_120`, CUDA 13.5),
  32 vCPU, 249 GiB RAM:
  - GPU Normalize (`--headroom 1`): 9.36 s wall (3.2 s GPU prove)
  - Stage-0 FRI (`SpillableTwoAdicFriPcs`, NVMe spill): 62.6 GiB peak RSS
  - GPU Recursive KZG (stage-1 + stage-2, warm fixed preprocessing cache):
    3m07.54s wall, 129.6 GiB peak RSS

The same run also proved the root in PLONK under the bundled Ignition PLONK key
(`verifying-keys/0.5/plonk-verifying-key.bin`, SHA-256 `ae9638f0…`, 15,652,020
constraints, 11.46 s GPU prove, 1.51 ms verify, 292,245 EVM gas; exported to
`contracts/plonk/testdata/nat-add-comm.json` and `contracts/plonk/src/PlonkVerifier.sol`,
`forge test` 14/14 PASS) and derived the Release 0.5 development Groth16 key
(`verifying-keys/0.5/groth16-development-verifying-key.bin`, SHA-256 `3e6bb1ff…`,
4,568,533 constraints). Both `Init+Std` (99,462 constants) and full `Mathlib`
4.34.1 (684,691 constants) compress and verify under these exact Release 0.5
keys (287,909 EVM gas for PLONK; 1.325 s ICICLE CUDA prove / 1.14 ms verify for
Groth16).
