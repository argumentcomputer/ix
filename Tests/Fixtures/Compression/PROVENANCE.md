# Compressed Nat.add_comm root, release 0.6

`nat-add-comm.ixon-proof` is a recursive KZG proof of `Nat.add_comm` + the
default 108-role table's aggregate root under the bundled 0.6 verifying keys
(Protocol `v6`, 128-bit `Fp^3` FRI, key-bound KZG transcripts `vk_version = 8`,
hardened formal IxVM / MultiStark verifier / aggregation circuits).
`lake test -- compression-cli` checks that `ix verify` accepts it, and that it
refuses the same proof under another claim. Replace it whenever the release
changes (see "Deriving the verifying keys" in `crates/proof-compression/README.md`).

## Artifact identity

- Format: serialized `Ixon.Proof`, a `CheckEnv` claim with an `IXBN` recursive
  KZG packet (`vk_version = 8`, 1,909-byte packet)
- Ixon content address (BLAKE3):
  `f6e7fdb3e212cc36083e39243e7a7b9afd20421548e57e3fecd0150da219d6c1`
- SHA-256: `5ada96350c9f290eeda7269e05cd69fd88c85abd4eb2b59f45290de38861ec4a`
- Size: 2,020 bytes
- Claim digest (BLAKE3 of the claim):
  `7276777b46265570e99e572d223026bcab0647c82ed340b7790c6033433e7763`
- Environment canonical tree root:
  `0d55f4d5dafcccafde3f78636a68e1209f347d8782f00f3c72568af6ca7b54d1`
- Role table: `c60dd3126e86fe6d5221f514a229569a30d1c1075f88f3b23243df82da8194b7`
  (the default role table; not assumed by the root claim — validated lazily by
  the leaf proofs under it as far as each check uses the table, or discharged by
  a binding proof verified during aggregation)
- Root layout: `verifying-keys/0.6/root-layout.ixl` (96 bytes, BLAKE3
  `baf7e4f0f7dd873a0e72dd3cd600732e0ae68c4c28fa5e1bb6c7b7588ad7aca0`,
  `--headroom 1`)
- Recursive verifying key: `verifying-keys/0.6/recursive-vk.bin`, BLAKE3
  `3ba4f8a4a88d427c82c5146a3e712bf49f70434955e4b364627c3e12d475adcb`
  (ID `7182cd465935d85032f40e689915064a020f294e81ff9c243267a5d9719f28ef`),
  under the released Aztec Ignition setup

## Inputs and producer

- Environment: `Nat.add_comm` together with the 108 default-table roles
  (`IxCK/Kernel/Key.lean`), compiled into `nat-default-roles.ixe`
  (5,625 constants)
- Aggregate root:
  `936b7f95176dfee4d992bab9c1544b30a6e433125694370e34d1d9f349354819`
  (`ix verify --aggregate` PASS with zero `--allow-*` flags)
- Backends: Protocol `v6` (`Fp^3`, `Parameters::DEFAULT`: `lb=2, q=128, qpow=20`),
  formal IxVM artifact `5d099cad…` (key `49069013…`) and formal aggregation key
  BLAKE3 `e28ef326f80704567ddd29fd1367f21318335626c1b692b9588ee3ae7605175d`
  (artifact `7234e606…`)
- Host: CPU build (24 Rayon threads, 495 GiB RAM, warm fixed-preprocessing
  cache):
  - Normalize (`--headroom 1`): 41.7 s prove (1 trace shard, 2,097,152 rows)
  - Stage-0 FRI: 425.1 s prove+verify, 350.3 GiB peak RSS, 1,908,501-byte FRI
    proof
  - Stage-1 KZG (warm fixed cache): 1,294.8 s wall, 87.6 GiB peak RSS,
    27,333-byte proof (9.06 ms verify)
  - Stage-2 Recursive KZG (warm fixed cache): 473.9 s wall, 60.3 GiB peak RSS,
    1,909-byte packet (3.74 ms native verify)

Legacy final PLONK and Groth16 compression stages are retired in favor of the
pure-Rust `aiur_backend::plonk::native` and `aiur_backend::groth16` backends;
archived release 0.5 PLONK and development Groth16 verifying keys remain under
`verifying-keys/0.5/` for `#[cfg(test)]` verification coverage only.
