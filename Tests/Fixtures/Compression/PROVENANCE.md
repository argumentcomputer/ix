# Compressed Nat.add_comm root, release 0.4

`nat-add-comm.ixon-proof` is a recursive KZG proof of `Nat.add_comm` + the
default 108-role table's aggregate root under the bundled 0.4 verifying keys.
`lake test -- compression-cli` checks that `ix verify` accepts it, and that it
refuses the same proof under another claim. Replace it whenever the release
changes (see "Deriving the verifying keys" in `crates/proof-compression/README.md`).

## Artifact identity

- Format: serialized `Ixon.Proof`, a `CheckEnv` claim with an `IXBN` recursive
  KZG packet (version 7)
- Ixon content address (BLAKE3):
  `837cc8252dda72e915a8f84a8aa237b3e33df71798b048cdcd735c581d4c80d5`
- SHA-256: `4c27be51f45a39e82b04a65593713499539736d0b96816c7258022deae594a3e`
- Size: 2,020 bytes
- Claim digest (BLAKE3 of the claim):
  `e970dd8b218a90109911fa4a26de673ab4f2b7f5783f6d289a74f31e0ff6bba1`
- Subject canonical tree root:
  `1b6c3292e63d2efcd4fb985a51d8ea0e55f72d112ecfddc6adbecc76041ff0be`
- Role table: `c60dd3126e86fe6d5221f514a229569a30d1c1075f88f3b23243df82da8194b7`
  (the default role table, validated in the proof)
- Recursive verifying key: `verifying-keys/0.4/recursive-vk.bin`, BLAKE3
  `c57f3938d3dd0f5b1b0f343d74594cb01fec4dd3adc32d17006b7a16be591988`
  (ID `01a27eaaf9cc588848739503c9e5f94780558a408789107767b27474881faa2a`),
  under the released Aztec Ignition setup

## Inputs and producer

- Environment: `Nat.add_comm` together with the 108 default-table roles
  (`IxC/Kernel/Key.lean`), compiled into `nat-default-roles.ixe` (5,736
  constants, 5,682 claimable; SHA-256
  `7fd50b5fcca77df339ce2a9ba0d317cdad22cc7e45775c05d987cc9386eae50c`)
- 16 shards (`nat-default-16.ixes`), aggregated by
  `ix prove --aggregate --binding-proof b2793a59…`: root
  `b6d78dc9c804a05a4ce820c5ed3752e2fa29afc85abed2ecd716684f4358a3d2`
  (file SHA-256
  `4913f255e534c1a729e1b5885397785fb45a3cece00bb1073b121316c9761d72`)
- Backends: the formal IxVM key (BLAKE3 `d9ff752f…`, artifact `b377e6f9…`) and
  aggregation key (BLAKE3 `81e744bb…`, artifact `23dbe6ac…`, 45 circuits) at
  `Parameters::DEFAULT`
- Command: `ix compress ROOT --out DIR`, with the Ignition SRS under
  `IX_KZG_SRS` and the fixed preprocessing `release_keys` published
- Host: 64-thread Xeon 6975P-C box, 495 GiB RAM, CPU only:
  - In-RAM default on ≥256 GiB host: 1,754 s total wall time (FRI 163 s, first
    KZG 818 s / 516 s prove, final KZG 611 s / 364 s prove) and 182.9 GB peak
    RSS (down from 1,903 s and 389 GB in release 0.3)
  - Bounded-RAM disk-spill mode (`IX_KZG_DISK_SPILL=1`, default on <256 GiB
    CPU hosts): FRI peaks at 50.8 GB RSS (−87.0% vs 389 GB)

The same run also proved the root in PLONK under the bundled Ignition PLONK key
(`verifying-keys/0.4/plonk-verifying-key.bin`, SHA-256 `032ff41e…`, 11,932,057
constraints, 45.0 s prove, 2.1 ms verify; exported to
`contracts/plonk/testdata/nat-add-comm.json` and `contracts/plonk/src/PlonkVerifier.sol`)
and in Groth16 (3,476,708 constraints, 2.16 s prove, 1.4 ms verify) under a
development setup; `ix verify` accepted all three.
