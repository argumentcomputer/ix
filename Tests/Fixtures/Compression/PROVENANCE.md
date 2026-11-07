# Compressed Nat.add_comm root, release 0.2

`nat-add-comm.ixon-proof` is a recursive KZG proof of `Nat.add_comm`'s
aggregate root under the bundled 0.2 verifying keys.
`lake test -- compression-cli` checks that `ix verify` accepts it, and that it
refuses the same proof under another claim. Replace it whenever the release
changes (see "Deriving the verifying keys" in `crates/proof-compression/README.md`).

## Artifact identity

- Format: serialized `Ixon.Proof`, a `CheckEnv` claim with an `IXBN` recursive
  KZG packet
- Ixon content address (BLAKE3):
  `90f78383ab0f9ca6f4433be7d1c05967e5647246acfb8fb36d752252d98b5556`
- SHA-256: `dd376795d54588123908c5a159944a80ed592cf738ca52d72b7d2caf3c3b4be7`
- Size: 2,020 bytes
- Claim digest (BLAKE3 of the claim):
  `ae8be56a6d0e097ed904405abbe29ad0f30640937d80037f9537a9b40f8d1e95`
- Recursive verifying key: `verifying-keys/0.2/recursive-vk.bin`, BLAKE3
  `81ca053b35d43bf4d17447e8c21749ad74d24573abc367da5682b4bb6506c7fd`, under
  the released Aztec Ignition setup

## Inputs and producer

- Environment: `Nat.add_comm`'s closure (213 constants), compiled from a file
  holding only `theorem ixReleaseLayout : True := trivial` with
  `ix compile --consts Nat.add_comm`; `nat.ixe`, SHA-256
  `e1174122fd9af5fa6897c285013358f01a32e492b4d8cbde3ff372f38fbd5c3f`
- One shard (`ix shard --shards 1`), aggregated by `ix prove --aggregate`:
  the wrapped-leaf root
  `3f414752488f33e1bccf545cf6b6f7e08a124adf6c1d091fb08f6dcb0b88c9cf`
  (file SHA-256
  `c8428753d5bf7c86398d7a0703d97f92f89e0f315d05c8854bc3ea113cf6de24`), one of
  the four roots the 0.2 layout was derived from
- Backends: the formal IxVM key (BLAKE3 `4c4b908c…`) and aggregation key
  (BLAKE3 `d286b37b…`) at the restored STARK parameters
- Command: `ix compress ROOT --out DIR`, with the Ignition SRS under
  `IX_PARAMS_DIR` and the fixed preprocessing `release_keys` published
- Host: 64-core box, 495 GB of RAM, CPU only; 2,326 s wall time and 389 GB
  peak RSS (box job `params-b2-4`)

The same run also proved the root in PLONK, under the bundled PLONK key
(`contracts/plonk/testdata/nat-add-comm.json`), and in Groth16 under the
bundled development key; `ix verify` accepted both.
