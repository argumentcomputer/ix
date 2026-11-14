# Compressed Nat.add_comm root, release 0.3

`nat-add-comm.ixon-proof` is a recursive KZG proof of `Nat.add_comm`'s
aggregate root under the bundled 0.3 verifying keys.
`lake test -- compression-cli` checks that `ix verify` accepts it, and that it
refuses the same proof under another claim. Replace it whenever the release
changes (see "Deriving the verifying keys" in `crates/proof-compression/README.md`).

## Artifact identity

- Format: serialized `Ixon.Proof`, a `CheckEnv` claim with an `IXBN` recursive
  KZG packet
- Ixon content address (BLAKE3):
  `69038aa7bfdb8ca7c0fe53d0d88fb95e8d9f9c9193dcf852739ab7c55b10b882`
- SHA-256: `a78df99ee0328aff20a61452db01fed12e1cf5d41af240b93b0345ec7d24ab2b`
- Size: 2,020 bytes
- Claim digest (BLAKE3 of the claim):
  `9871a66a0f7df6edd6a3a76f606de47892b7f25d750c19266255facfacdcb863`
- Recursive verifying key: `verifying-keys/0.3/recursive-vk.bin`, BLAKE3
  `25e785599ee246a08052bd15cae3ca8bef9501b181f886d8e8e7bf2d23e90fbe`, under
  the released Aztec Ignition setup

## Inputs and producer

- Environment: `Nat.add_comm`'s closure (213 constants), compiled from a file
  holding only `theorem ixReleaseLayout : True := trivial` with
  `ix compile --consts Nat.add_comm`; `nat.ixe`, SHA-256
  `ebf96b76a8a2eff752d75e67e1bc682e3ee569451580b786eb8b9b1859c1fbd9`
- One shard (`ix shard --shards 1`), aggregated by `ix prove --aggregate`:
  the wrapped-leaf root
  `0fb6ff2496f18d386365eefea17d6a7ac5c9f3904b2aa37c4e38ffefa7019e20`
  (file SHA-256
  `8dd3ef5452e1c1ad70d09873f68b53b8260080ba41b78ef9ac6e2f552a3e34c9`), one of
  the four roots the 0.3 layout was derived from
- Backends: the formal IxVM key (BLAKE3 `4312e28b…`) and aggregation key
  (BLAKE3 `f6d00e04…`) at the restored STARK parameters
- Command: `ix compress ROOT --out DIR`, with the Ignition SRS under
  `IX_PARAMS_DIR` and the fixed preprocessing `release_keys` published
- Host: 64-core box, 495 GB of RAM, CPU only; 1,903 s wall time and 389 GB
  peak RSS (box job `params-03-6`)

The same run also proved the root in PLONK, under the bundled PLONK key
(`contracts/plonk/testdata/nat-add-comm.json`), and in Groth16 under the
bundled development key; `ix verify` accepted both.
