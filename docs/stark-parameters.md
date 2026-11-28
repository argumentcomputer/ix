# STARK Parameters, Protocol `v6`, and Concrete Endpoint Security

Every production Aiur proof (IxVM claims, the recursive verifier, aggregation,
and the Endpoint 1 STARK shrinker) is a Protocol `v6` `multi-stark` proof over
Goldilocks ($\mathbb{F}_p$, $p = 2^{64} - 2^{32} + 1$) with challenges in its
cubic extension $\mathbb{F}_{p^3} = \mathbb{F}_p[X]/(X^3 - X - 1)$,
domain-separated BLAKE3 `derive_key` Merkle commitments and Fiat–Shamir
transcripts, and `FriBatching::Tensor` FRI.

This document specifies:

1. Production Protocol `v6` and `v6-zk` parameters, wire format invariants, and
   the enforced 128-bit security floor.
2. FRI soundness estimation with `lake exe fri-security`.
3. A concrete security-bit calculation and comparison table across all three
   Ix proof endpoints (**Endpoint 1: Native STARK `v6`/`v6-zk`**,
   **Endpoint 2: BLS12-381 Filecoin $2^{27}$ / EIP-2537**, and
   **Endpoint 3: Pre-Pectra BN254 Aztec Ignition**, the current default), clearly separating
   Lean-4 kernel-certified properties from cryptanalytic literature estimates.
4. How to update parameters safely.

---

## Protocol `v6` Parameters and Wire Invariants

### Production Defaults

| Parameter | Production `v6` Value | Scope |
| --- | --- | --- |
| Base field | Goldilocks $\mathbb{F}_p$, $p = 2^{64} - 2^{32} + 1$ (2-adicity $32$) | fixed |
| Extension field | $\mathbb{F}_{p^3} = \mathbb{F}_p[X]/(X^3 - X - 1)$, $p^3 > 2^{191}$ ($\approx 192.00$ bits) | fixed (`extension_degree = 3`) |
| Protocol version | `6` (`v6` transparent; `v6-zk` hiding PCS) | fixed (`protocol_version = 6`) |
| FRI batching | `FriBatching::Tensor` (multilinear tensor batching) | fixed (`fri_batching = 1`) |
| `log_blowup` | `2` (rate $\rho = 1/4$, blowup factor $4$) | varies (`1..=4`) |
| `num_queries` | `128` | varies (per-`log_blowup` floor) |
| `query_proof_of_work_bits` | `20` | varies (`0..=32`) |
| `commit_proof_of_work_bits` | `0` | varies (`0..=32`) |
| `max_log_arity` | `1` (binary FRI folding) | fixed by adapter & recursive verifier |
| `log_final_poly_len` | `0` (constant final polynomial) | fixed |
| `cap_height` | `0` (strictly singleton Merkle roots) | fixed |

The canonical Rust source is `aiur::trace::stark::Parameters::DEFAULT`
(`crates/aiur/src/trace/stark.rs`), shared by `ixvm-proof`, `stark-verifier`,
`ix-prover`, `stark-shrinker`, and the compression pipeline. Lean mirrors it in
`Ix/Aiur/Parameters.lean` (`Aiur.defaultCommitmentParameters`,
`Aiur.defaultFriParameters`, and the `v6` floor constants), and the Rust test
`lean_mirror_matches` enforces exact parity between the two files.

At `Parameters::DEFAULT` (`log_blowup = 2, num_queries = 128, commit_pow = 0, query_pow = 20`),
the FRI **query term** is as follows. This is one term of the soundness error, not
a soundness level (a level is the weakest term; with the shipped 32-byte digest the
hash term alone is about 128 bits), and these are estimates: no machine-checked
theorem covers the tensor-batched `v6` verifier (see
[what is Lean-certified](#lean-4-kernel-certified-properties-vs-cryptanalytic-literature-estimates)).

- **142.24 bits** finite-$m$ ($m = 16$) Johnson list-decoding query term
  (conservative integer lower bound `142_240` millibits,
  exact $-\!128 \log_2((33/32)\cdot 2^{-1}) + 20 = 142.32$ bits; the margin above 128
  bits is in this term only),
- **106.78 bits** provable unique-decoding (UD) query soundness (integer floor `106_784` millibits;
  exact $106.79$ bits),
- **276 bits** ethSTARK conjectured query soundness ($2 \cdot 128 + 20$).

### Protocol `v6` Cryptographic & Structural Binding

1. **Cubic extension field ($\mathbb{F}_{p^3}$):** Legacy `v5` used the quadratic
   extension $\mathbb{F}_{p^2}$ ($p^2 < 2^{128}$), where DEEP, ALI, LogUp, and
   Johnson batching lost $\log_2(\text{instance size})$ from 128 bits and capped
   recursive proofs around 80–92 bits regardless of query count. Upgrading to
   $\mathbb{F}_{p^3} = \mathbb{F}_p[X]/(X^3 - X - 1)$ raises field entropy to
   $p^3 > 2^{191}$ ($\approx 192$ bits), giving $> 63$ bits of algebraic
   headroom for traces up to $2^{28}$ rows. Irreducibility of $X^3 - X - 1$ over
   $\mathbb{F}_p$ is kernel-certified in Lean
   (`Ix.Cert.Compression.StarkShrinkerZk.Fp3Model.cubicTrinomial_no_root`,
   `CertiFri.P3`).
2. **`FriBatching::Tensor`:** Protocol `v6` mandates multilinear tensor FRI
   batching (`fri_batching = 1`). Legacy power/Horner batching (`0`) is rejected
   fail-closed by `stark_key::from_bytes`, `multi-stark`, and the Lean formal
   profiles.
3. **BLAKE3 `derive_key` domain separation:** Every hash role uses BLAKE3's
   native keyed derivation mode (`DERIVE_KEY_MATERIAL = 64`) with pairwise
   distinct precomputed 8-word context keys:
   - `v6` transparent domains: `multi-stark/v6/merkle/leaf`,
     `multi-stark/v6/merkle/compress`, `multi-stark/v6/transcript/single`,
     `multi-stark/v6/transcript/batch`, `multi-stark/v6/vk`.
   - `v6-zk` hiding domains: `multi-stark/v6-zk/merkle/leaf`,
     `multi-stark/v6-zk/merkle/compress`, `multi-stark/v6-zk/transcript/single`,
     `multi-stark/v6-zk/transcript/batch`, `multi-stark/v6-zk/vk`, plus
     `multi-stark/v6-zk/preprocessed-salt` for deterministic preprocessed leaf
     salting.
   - All 11 domains (including retired unkeyed `plain` / `v5`) are proved
     pairwise distinct in Lean (`CertiFri.P3.Blake3Domain.mode_injective`,
     `v6Zk_keyWords_ne_nonZk`, `Ix.Cert.Compression.StarkShrinker.Blake3Domain.*`).
4. **`vk_digest` and key header binding:** The dense `stark-key` v6 wire format
   (`crates/stark-key/src/lib.rs`) writes `protocol_version = 6`,
   `extension_degree = 3`, `fri_batching = 1`, the 32-byte `vk_digest`
   (`BLAKE3 derive_key("multi-stark/v6/vk")` over all compiled circuits), and
   all seven commitment/FRI parameters into the header. Decoding recomputes
   `vk_digest` and rejects mismatches fail-closed. `multi-stark` seeds the
   Fiat–Shamir transcript with the protocol tag, parameters, and `vk_digest`, so
   a proof produced under any other parameters or circuits fails verification.
   The aggregation program pins the IxVM and aggregation key digests, binding
   every recursive step.
5. **Exact `MerkleCap` root counts:** Production keys fix `cap_height = 0`
   (singleton Merkle roots). Both `multi-stark` and every formal Aiur in-circuit
   verifier (`Mmcs::mmcs_verify_multi`, `ProofDeserialize::read_merkle_cap_at`,
   `SystemDeserialize::read_opt_commit`, `StarkVerifier::{cap_onto, snoc_cap, header_onto}`,
   `Aggregation::aggr_read_header`) enforce strictly singleton (`len == 1`)
   `MerkleCap` payloads on preprocessed, stage-1, stage-2, quotient, FRI
   commit-phase, and shard-header commitments, rejecting extra roots or
   out-of-range cap indices fail-closed. Test-only `from_bytes_below_floor` with
   `cap_height > 0` validates exact LDE cap length
   `1 << cap_height.min(max_prep_log + log_blowup)`.
6. **`v6-zk` hiding PCS (Endpoint 1b, `--stark-128-zk`):** Adds 16-byte
   (`128`-bit) per-leaf BLAKE3-CTR salting (`ZK_LEAF_SALT_BYTES = 16`, binding
   both `(row, salt)`), $2\times$ interleaved odd-coset witness blinding
   $T(X) = T_0(X) + (X^N - 1)\,b(X)$ preserving evaluations on $H_N$,
   half-stride telescoping blinded quotient slicing, mandatory base-field
   randomizer width $W_R \ge 4$ (ensuring the 4-element tensor basis
   $\{1, r_0, r_1, r_0 r_1\}$ spans $\mathbb{F}_{p^3}$ over $\mathbb{F}_p$ with
   failure probability $\le 2/p^2 < 2^{-126}$, whereas $W_R = 3$ fails with
   probability $\ge 1/p > 2^{-64}$), blinded interior LogUp accumulators, trace
   height $N \ge \operatorname{next\_pow2}(2Q + 2D)$ with
   $\log_2 N + 1 + \text{log\_blowup} \le 32$, quotient degree check
   `zkQuotientDegree d ≤ 2^log_blowup`, and a standalone 1-circuit layout that
   avoids cleartext `MEMSEG` count leakage
   (`Ix/Cert/Compression/StarkShrinkerZk.lean`).

---

## Enforced Security Floor

`stark_key::security::check` (`crates/stark-key/src/security.rs`) and its Lean
mirror `Aiur.meetsSecurityFloor` (`Ix/Aiur/Parameters.lean`) enforce a
**query-phase heuristic floor** at a finite-$m$ ($m = 16$) literature radius.
These boolean checks do **not** bound commit-phase, batching, DEEP, LogUp, or
hash terms, do not depend on instance size, and do **not** imply the hypotheses
of any Lean soundness theorem (for example, the floor admits `q ≥ 101 / 66 / 53`
at `lb = 2 / 3 / 4` and `qpow ∈ 0..=32`, whereas CertiFRI's unconditional
Johnson theorems require `q ≥ 128` or `118 / 78 / 58`, exact `qpow = 20`, and
the `hclaims` size bound below). They reject any key or backend that fails
**any** of the following simultaneous conditions:

- **Fixed structural parameters:** `cap_height == 0`, `log_final_poly_len == 0`,
  `max_log_arity == 1`, `log_blowup ∈ 1..=4`, `num_queries ≥ 1`.
- **Proof-of-work ceiling:** `commit_proof_of_work_bits ≤ 32` and
  `query_proof_of_work_bits ≤ 32` (grinding cannot substitute for queries).
- **Per-`log_blowup` minimum query floor:**
  `log_blowup = 1 → 211`, `2 → 101`, `3 → 66`, `4 → 53` queries.
- **Conjectured query floor:**
  `log_blowup · num_queries + query_pow ≥ 220` bits.
- **Provable unique-decoding (UD) query floor:**
  `ud_millibits_per_query(log_blowup) · num_queries + 1000 · query_pow ≥ 80,000`
  millibits (`80.000` bits), where `ud_millibits_per_query` is a conservative
  integer lower bound on $-1000 \log_2((1 + 2^{-\text{log\_blowup}})/2)$:
  `415 / 678 / 830 / 912` mbit/q for `log_blowup = 1 / 2 / 3 / 4`. This blocks
  deceptive high-blowup / low-query configurations such as `(4, 55, 0, 0)`
  (220 conjectured bits, but only 50.2 UD bits).
- **Finite-$m$ ($m = 16$) Johnson list-decoding query floor:**
  `(500 · log_blowup - 45) · num_queries + 1000 · query_pow ≥ 128,000`
  millibits (`128.000` bits), accounting for the finite-$m$ proximity slack
  $1000 \log_2(1 + 1/(2m)) = 1000 \log_2(33/32) \approx 44.39 \le 45$ mbit/q
  (`455 / 955 / 1455 / 1955` mbit/q for `log_blowup = 1 / 2 / 3 / 4`). This
  rejects the retired `v5` default `(2, 100, 0, 20)` (115.5 Johnson bits).

Strict 128-bit query-phase validators (`stark_key::security::{check_128_ud, check_128_johnson}`
and `Aiur.meetsSecurityFloor128{Ud,Johnson}`) additionally check
`extension_degree ≥ 3` and `protocol_version ≥ 6`; `check_128_ud` raises the
UD query floor to `128.000` bits with per-`log_blowup` query floors `232 / 142 / 116 / 106`
(e.g., `(2, 160, 0, 20)` achieves `128.480` UD bits). In production only `check`
runs; `check_128_ud` and `check_128_johnson` run in tests only, and neither is a
hypothesis of any soundness theorem.

Building any production backend (`Backend::new`, `for_batch`,
`for_batch_verification`, `for_batch_on_device`) and decoding any production key
(`stark_key::from_bytes`, `aiur::trace::stark::VerifyingKey::from_bytes`) runs
this check unconditionally. Test-only helpers `from_bytes_below_floor` and
`Backend::for_batch_below_floor` are `#[doc(hidden)]` and must never decode or
build keys trusted by a verifier.

---

## Computing FRI Soundness with `fri-security`

`lake exe fri-security` (`Scripts/FriSecurity.lean`, `Ix/Aiur/FriSecurity.lean`)
computes every soundness term of a FRI-based STARK instance across five models:

1. **`CertiFRI proven UD`:** Matches the exact Lean-verified theorems in
   `CertiFRI` for binary-folding `Fri.verify` (Horner) and `Fri.verifyTensor`
   (tensor-batched `v6`, `CertiFriProofs.Exec.SoundnessTensorSponge`), using
   quadratic Berlekamp–Welch batching/commit, `DecodeMarginOff`
   $2\delta + \rho + 1/|D_{\min}| \le 1$, off-domain DEEP
   $2|D| + \max(\text{degreeTerm}, (q+1)k)$, and LogUp `(W + 2) · L / |K|`.
2. **`unique decoding`:** Ideal linear unique-decoding bound (`p3-security`).
3. **`Johnson, BCHKS25`** and **`Johnson, DKT26`:** Proven list-decoding bounds
   over $\mathbb{F}_{p^3}$ (including $-\log_2(\text{list size})$ on ALI, DEEP,
   and LogUp).
4. **`conjectured (2025/2010)`:** ethSTARK / proximity-gap conjecture.

Usage:

```sh
target/release/stark-verifier statistics key.bin proof.bin > stats.json
lake exe fri-security stats.json
lake exe fri-security stats.json --table \
  --parameters 2,128,0,20 --parameters 2,160,0,20 \
  --parameters 3,78,0,20  --parameters 4,66,0,20
# CI-style gate: shipped 32B BLAKE3 is hash-limited at 127.71 bits (`3N^2/(2*2^256)`),
# so require >= 127 bits for 32B digests or >= 128 bits with `--digest-bytes 64`
lake exe fri-security stats.json --regime johnson --require-min-bits 127
lake exe fri-security stats.json --digest-bytes 64 --regime johnson --require-min-bits 128
# Evaluate the 64-byte (512-bit) RFC 7693 BLAKE2b-512 formal PQ profile directly
lake exe fri-security stats.json --extension-degree 3 --digest-bytes 64 --table \
  --parameters 2,128,0,20 --parameters 2,160,0,20 \
  --parameters 3,78,0,20  --parameters 4,66,0,20
```

It also accepts `fri_sizing --statistics outer-vk.bin` and `--instance
LOG_TRACE,COLUMNS,CONSTRAINTS,MAX_DEGREE,LOOKUP_ROWS,LOOKUP_WIDTH`.

### Representative Protocol `v6` ($\mathbb{F}_{p^3}$) Soundness (`fri-security`)

Evaluated on a large recursive-verifier-scale instance ($2^{22}$ rows, 1,800
batched columns, 3,500 constraints, max degree 5, 367M lookup rows, lookup width
24) with `extension_degree = 3` ($\mathbb{F}_{p^3}$, ~192-bit field):

| Profile `(lb, q, cpow, qpow)` | Conjectured query | `CertiFRI` proven UD | Johnson (BCHKS25 / DKT26) — 32B BLAKE3-256 (classical) | Johnson (BCHKS25 / DKT26) — 64B BLAKE2b-512 (classical; digest not shipped) | Conjectured (64B BLAKE2b-512) | Floor status |
| --- | ---: | ---: | --- | --- | --- | --- |
| `(2, 100, 0, 20)` *(retired `v5`)* | 220 | 87.81 (query) | 119.46 / 119.76 (query) | 119.46 / 119.76 (query) | 158.85 (lookup) | **Rejected** (`115.5b` $m\!=\!16$ Johnson $< 128$) |
| **`(2, 128, 0, 20)` *(v6 default)*** | 276 | 106.79 (query) | **127.71 / 127.71** (collision) | **138.02 (query) / 141.91 (batching)** | 158.85 (lookup) | **Admitted** (`142.24b` $m\!=\!16$ Johnson) |
| `(2, 160, 0, 20)` *(strict UD-128)* | 340 | **128.49 (query)** *(127.71 @ 32B)* | **127.71 / 127.71** (collision) | **144.42 (query) / 147.26 (batching)** | 158.85 (lookup) | **Admitted** (`128.48b` UD, `172.80b` Johnson) |
| `(3, 78, 0, 20)` *(v1 shrinker default)* | 254 | 84.75 (query) | **127.71 / 127.71** (collision) | **132.98 (batching) / 135.64 (query)** | 158.85 (lookup) | **Admitted** (`133.49b` $m\!=\!16$ Johnson) |
| `(4, 66, 0, 20)` *(v1 shrinker compact)* | 284 | 80.23 (query) | **127.71 / 127.71** (collision) | **138.92 / 142.39 (batching)** | 158.85 (lookup) | **Admitted** (`149.03b` $m\!=\!16$ Johnson) |

Every algebraic term (ALI, DEEP, LogUp, batching, commit) now clears 132–158+
bits even on $2^{22}$-row / 367M-lookup recursive proofs, eliminating the
legacy $\mathbb{F}_{p^2}$ ~80-bit ceiling.

The two shrinker rows are the v1 (`.ixa`) shrinker's profiles. Endpoint 1 v2
(`IXSTARK6` Plonkish, `ix compress --stark-128[-zk]`) is verified only under
its two shipped outer profiles, `(4, 58, 0, 28)` (default) and `(4, 55, 0, 30)`
(`--compact`), each with `cap_height = 0`, 8-ary folding (`max_log_arity = 3`)
and a $2^8$-coefficient final polynomial (`ENDPOINT1_PROFILES`); its floor
(141.390b / 137.525b Johnson, 80.896b / 80.160b UD) counts the FRI query phase
only, and no `CertiFRI` theorem covers folding by more than two.

---

## Concrete Security Analysis Across All Three Endpoints

Ix is migrating default proof compression to the **Lean-compiled Aiur
compression stages** (`ix compress run-stages`, `crates/proof-compression/src/aiur_backend/`:
`CompressWrap → CompressGL → CompressNarrowFixed → CompressFinalNarrow → native Rust PLONK`,
exported via `stark-export export-trace --compress-wrap` / `--compress-gl`,
`wide_export`, `tiling_export2`, `plonk_export`), retiring the legacy
hand-written `pipeline::compress` Rust circuits (see
[compression stage boundaries](compression-stage-collapse.md) and
[Aiur compression architecture](aiur-compression-architecture.md)). That
migration is not done: at this revision `ix compress` defaults to BN254
(Endpoint 3) through the hand-written pipeline, whose BN254 keys are the only
bundled release keys; the output of the Aiur stages (`ix compress
--aiur-stages`) has no bundled release L3 verifying key yet (verification uses an
independently pinned `ix verify --l3-verifier <bundle> --l3-verifier-blake3 <pin>`
or `IxL3PlonkVerifier.sol`); and Endpoint 2 (BLS12-381) has no release key, so
no shipped command verifies it under a bundled production key.

Regardless of whether the inner stages are compiled from Aiur or wrapped by the
STARK shrinker, every Ix proof terminates at one of **three cryptographic
endpoints** with distinct classical security, post-quantum security, trust setup,
and on-chain verification properties:

| Security Dimension | Endpoint 1: Native STARK (`v6` / `v6-zk`, `--stark-128` / `--stark-128-zk`) | Endpoint 2: BLS12-381 KZG / EIP-2537 PLONK (`--bls12-381`; no release key yet) | Endpoint 3: BN254 KZG / Pre-Pectra PLONK & Groth16 (`--bn254`, current default) |
| --- | --- | --- | --- |
| **Headline Classical Security** | **~128 bits estimated** in the Johnson and conjectured regimes, hash-limited by the 32-byte digest (`127.71b` classical BCS; about 81 bits if only unique-decoding bounds are used for the default `(4, 58, 0, 28)` shape). `CertiFRI` now proves unconditional binary-folding random-oracle soundness for executable tensor-batched `Fri.verifyTensor` in both UD and Johnson regimes over 32B BLAKE3 and 64B BLAKE2b-512 (under `htensor` size bounds); no theorem covers the Rust `multi-stark` implementation directly or the v2 shrinker's 8-ary folding | **~126–128 bits** *(curve exTNFS / Pollard-$\rho$; see Cheon $q$-SDH note below)* | **~100 bits** *(BN254 exTNFS bottleneck — rejected by 128-bit profile)* |
| **Headline Post-Quantum Security** | **Not established.** The shipped 32B `BLAKE3-256` digests give **~85.3b** BHT quantum collision resistance, and no theorem considers a quantum adversary (all are classical random-oracle statements). *(A 64B RFC 7693 `BLAKE2b-512` profile — 170.7b BHT / 204.8b CNS / 256b Grover — is a Lean specification and parameter study; no prover or verifier uses it.)* | **0 bits** *(Shor breaks ECDLP / pairings in poly-time)* | **0 bits** *(Shor breaks ECDLP / pairings in poly-time)* |
| **Algebraic / Field Modulus** | Goldilocks $\mathbb{F}_{p^3}$, $p^3 > 2^{191}$ ($\log_2 p^3 = 192.00$b) | $q$: 381b ($\log_2 q = 380.70$, $q^{12} \approx 2^{4568.4}$); $r$: 255b ($\log_2 r = 254.86$) | $q$: 254b ($\log_2 q = 253.60$, $q^{12} \approx 2^{3043.2}$); $r$: 254b ($\log_2 r = 253.60$) |
| **Curve DLP (Pollard-$\rho$ in $G_1$)** | N/A (no elliptic curve) | **~127.25 bits** ($\frac{1}{2}\log_2(\pi r / 4)$) | **~126.62 bits** ($\frac{1}{2}\log_2(\pi r / 4)$) |
| **Pairing Target DLP (exTNFS in $\mathbb{F}_{q^{12}}^*$)** | N/A (no pairing) | **~126–128 bits** *(Barbulescu–Duquesne 2019 / Guillevic 2020)* | **~100 bits** *(Kim–Barbulescu 2016 / Guillevic 2020)* |
| **SRS $q$-SDH (Cheon's attack)** | N/A (transparent, zero SRS) | **~113.6–113.9 bits** for public $d = 2^{28}-2$ ($D = 2^{27}$ or $3\cdot 2^{26} \mid r-1$) | **~112.8 bits** for public $d = 2^{28}$ ($2^{28} \mid r-1$; dominated by ~100b exTNFS) |
| **Schwartz–Zippel / Polynomial IOP Loss** | ALI/DEEP/LogUp over $\mathbb{F}_{p^3}$: $\ge 157\text{–}176$b; FRI query: $133.5\text{–}172.8$b Johnson | Over $\mathbb{F}_r$: $\ge 227.9$b at $N=2^{27}$, $\ge 229.9$b at $2^{25}$; folded pairing $254.86$b | Over $\mathbb{F}_r$: $\ge 225.6$b at $N=2^{28}$, $\ge 228.6$b at $2^{25}$; folded pairing $253.60$b |
| **Fiat–Shamir / Merkle Hash Collision** | **Classical prod (`BLAKE3-256`, 32B):** `127.7b` classical BCS / `85.3b` BHT PQ; **64B profile, not shipped (RFC 7693 `BLAKE2b-512`, 512b state):** `255.7b` classical BCS / `170.7b` BHT / `204.8b` CNS / `256b` Grover | Recursive KZG: BLAKE3 (**128b** classical); final PLONK: SHA-256 (**128b** classical) | Recursive KZG: BLAKE3 (**128b** classical); final PLONK: SHA-256 (**128b** classical); Groth16: non-interactive (AGM/KEA) |
| **Subgroup Check Requirement** | N/A | **Mandatory `G1` prime-order check** ($h_1 \approx 2^{125.84} > 1$, $3 \mid h_1$; $\psi(P) = [-u^2]P$) | $h_1 = 1$ in $G_1$ (curve check suffices); $G_2$ has $h_2 = 2q - r$ (checked on SRS import/verify) |
| **Trusted Setup / SRS** | **None (transparent)** | **Filecoin Phase 1 `challenge_19`** ($2^{27}$ trace / $2^{28}-2$ public degree, universal 1-of-$N$, no Phase 2) | **PLONK/KZG:** Aztec Ignition ($2^{28}$, universal 1-of-$N$, 176 participants). **Groth16:** circuit-specific Phase 2 (bundled key is dev-only!) |
| **Zero-Knowledge Posture** | `v6`: transparent non-ZK; `v6-zk`: hiding PCS by design (16B salt, $2\times$ odd-coset, $W_R \ge 4$, 1-circuit); no hiding property is formally stated | Final PLONK: ZK; bare recursive KZG: succinct non-ZK | Final PLONK / Groth16: ZK; bare recursive KZG: succinct non-ZK |
| **Target Environment** | Off-chain / transparent verification | **Ethereum Pectra+ (EIP-2537)** & 128-bit-class pairing verification | **Pre-Pectra EVM (EIP-196/197)**; current `ix compress` default and the only endpoint with bundled release keys |

### Component-by-Component Security Derivation

#### 1. Endpoint 1 — Native `Fp^3` STARK (`v6` and `v6-zk`)

- **Algebraic IOP errors over $\mathbb{F}_{p^3}$ ($p = 2^{64} - 2^{32} + 1$, $p^3 > 2^{191}$):**
  - Constraint batching (ALI): $\varepsilon_{\text{ALI}} \le C / p^3$ ($\ge 176$b for $C \le 2^{16}$).
  - Out-of-domain evaluation (DEEP): $\varepsilon_{\text{DEEP}} \le (2|D| + \max(d_{\max} N, (q+1)N)) / p^3$ ($\ge 163$b for $N = 2^{24}, \text{lb} = 2$).
  - LogUp lookup argument (`fractionLE_logup_pair_or_zero_denom`): $\varepsilon_{\text{LogUp}} \le (W + 2) L / p^3$ ($\ge 157$b for $L = 2^{29}, W = 64$).
  - FRI batching & commit phase: Lean proves `CertiFri.P3.Exec.curveListCA_fp3` over $\mathbb{F}_{p^3}$, `goldilocksExt3_tensor2DMCA_ud_128` / `goldilocksExt3_zk_tensor2DMCA_ud_128`, and connects them directly to the executable binary-folding tensor-batched verifier `Fri.verifyTensor` in `CertiFriProofs.Exec.SoundnessTensorSponge` (`goldilocksExt3_soundnessTensor_sponge_{uniqueDecoding,johnson}_128_blake3` and `…blake2b512…`), achieving $\le \frac{3}{4} N / 2^{128} + \frac{3}{2} N^2 / 2^{256}$ (32B BLAKE3) and literal $\le N / 2^{128}$ (64B BLAKE2b-512, $N \le 2^{128}$) under the explicit width/opening size bounds (`W, M \le 2^{16}` for UD; `htensor` for Johnson). No machine-checked theorem bridges the Lean `Fri.verifyTensor` model to the Rust `multi-stark` binary or covers the v2 shrinker's 8-ary folding.
- **FRI query-phase soundness (classical; quantum not established):**
  - For rate $\rho = 2^{-\text{lb}}$ and finite-$m$ ($m = 16$) Johnson agreement factor $\theta_J = (1 + \frac{1}{32})\sqrt{\rho} = \frac{33}{32} 2^{-\text{lb}/2}$, each query rejects a far codeword with failure $\le \theta_J$. With $q$ queries and $w$ query PoW bits:
    - Classical query soundness: $q \cdot (-\log_2 \theta_J) + w$.
    - Quantum: no theorem considers a quantum adversary. In the non-interactive protocol the query positions are a hash of the transcript, so a quantum prover can run Grover over its whole search, which halves the whole exponent: $(q \cdot (-\log_2 \theta_J) + w) / 2$.
  - Concrete Endpoint 1 query budgets:
    - Default `v6` `(lb=2, q=128, qpow=20)`: **142.32b** classical (`142.24b` integer floor) / **71.16b** with the exponent halved (quantum) Johnson; **106.79b** UD.
    - Strict UD-128 `(lb=2, q=160, qpow=20)`: **128.49b** classical (`128.48b` integer floor) / **64.25b** halved UD; **172.90b** classical / **86.45b** halved Johnson.
    - Shrinker v1 default `(lb=3, q=78, qpow=20)`: **133.54b** classical (`133.49b` integer floor) / **66.77b** halved Johnson; **84.75b** UD.
    - Shrinker v1 compact `(lb=4, q=66, qpow=20)`: **149.07b** classical (`149.03b` integer floor) / **74.54b** halved Johnson; **80.23b** UD.
    - Shrinker v2 default `(lb=4, q=58, qpow=28)` / `--compact` `(lb=4, q=55, qpow=30)` (`IXSTARK6` Plonkish, `max_log_arity=3`, `log_final_poly_len=8`): **141.39b** / **137.53b** classical Johnson query-phase floor (**70.70b** / **68.76b** halved); **80.90b** / **80.16b** UD. *(None of these profiles reaches 128 bits against a quantum prover under this rule.)*
- **Hash collision & multi-node aggregation ROM bound:**
  - Under straight-line extraction from a single shared random-oracle log (`Ix.Cert.Aggr.MonolithicRom.monolithic_aggrTree_rom_sound`), an adversary making $Q$ oracle queries against an aggregation tree with $M_{\text{verif}}$ verifier queries has forgery probability
    $$\Pr[\text{forge}] \le (Q + M_{\text{verif}})\,\varepsilon_{\max} + \frac{c\,(Q + M_{\text{verif}})^2}{2^{8d}}$$
    with incremental-sponge constant $c = 3/2$ and digest width $d \in \{32, 64\}$ bytes. The theorem takes round-by-round soundness (`MultiRbrSound`) with error $\varepsilon_{\max}$ and the extraction step as hypotheses over abstract types; no theorem discharges them for the shipped verifier, so this is a schema, not a bound on `v6` proofs. Under it the naive $-\log_2 M$ union-bound penalty across $M$-node aggregation trees disappears. (The naive union-bound figure, $+14.24$b covering $M \le 2^{14} = 16{,}384$ nodes at `(2, 128, 0, 20)`, `aggr_johnson_128_union_headroom`, is arithmetic on the query term alone, not a forgery bound: a per-node forgery probability against a $Q$-query adversary is at least $Q$ times that term, plus the other terms.)
  - **Production (`BLAKE3-256`, 32B) vs. the 64-byte profile (`BLAKE2b-512`, not shipped):**
    - **Production 128-bit classical (`DIGEST_BYTES_BLAKE3_256 = 32`):** Live `multi-stark` v6 wire proofs use 32-byte (256-bit) BLAKE3 `derive_key` digests (**127.71b** classical BCS collision resistance, where $3(2^{128})^2 / (2\cdot 2^{256}) = 3/2 > 1$ at the exact $Q = 2^{128}$ boundary, and **85.3b** BHT quantum collision resistance since $(2^{86})^3 / 2^{256} = 4 > 1$).
    - **64-byte profile (`DIGEST_BYTES_BLAKE2B512 = 64`; no prover or verifier uses this digest):** The bounds below are inequalities about the number $2^{512}$; the soundness theorems that use `Digest64` are classical random-oracle statements, so none of this is a post-quantum soundness theorem. The formal 64-byte profile uses **RFC 7693 `BLAKE2b-512`** (`CertiFri.P3.Digest64`, 64 bytes = `8 × UInt64`, true **512-bit internal state**, 128-byte block so 2-to-1 Merkle node compression `left64 || right64` fits in **one single compression block**, with RFC 7693 `personal` domain separation). It achieves **255.71b** classical BCS collision resistance ($\frac{3}{2} N^2 / 2^{512} \le N / (4\cdot 2^{128})$ for all $N \le 2^{128}$), **170.7b** BHT/Zhandry QROM collision resistance ($Q^3 / 2^{512} \le 1 / 2^{128}$ for $Q \le 2^{128}$, $+42.7$b headroom; $Q^3 / 2^{512} \le 1/4$ for $Q \le 2^{170}$), **204.8b** CNS (non-qRAM) collision resistance ($Q^5 / 2^{1024} \le 1/16$ for $Q \le 2^{204}$), and **256b** Grover preimage resistance ($Q^2 / 2^{512} = (Q/2^{256})^2$).
    - **Why `BLAKE3-XOF48` / `BLAKE3-XOF64` are excluded from concrete 128-bit PQ:** Although widening BLAKE3's XOF output to 48 or 64 bytes enlarges the ROM output codomain to $2^{384}$ or $2^{512}$, BLAKE3's internal chaining value (`cv`) is fixed at **256 bits** (`8 × u32`). On every $> 64$-byte input (including every 2-to-1 Merkle node and every multi-block leaf row), an adversary can find internal `cv` collisions in $2^{128}$ classical or $2^{85.3}$ BHT quantum queries, capping concrete collision resistance at `85.3b` PQ regardless of XOF output length. Legacy `DIGEST_BYTES_XOF48 = 48` is constructively rejected by all 128-bit PQ Lean profiles (`negControl_digest48_xof_rejected_128`, `negControl_aggr128_rejects_48b_xof`).

#### 2. Endpoint 2 — BLS12-381 (Filecoin `challenge_19` $2^{27}$ / EIP-2537)

- **Curve parameters:** Barreto–Lynn–Scott family with $k = 12$, seed $u = -\texttt{0xd201000000010000}$:
  - $r = u^4 - u^2 + 1$ (255-bit prime, $\log_2 r \approx 254.86$, 2-adicity $32$),
  - $q = (u - 1)^2 r / 3 + u$ (381-bit prime, $\log_2 q \approx 380.70$, $\log_2 q^{12} \approx 4568.41$),
  - `G1` cofactor $h_1 = (u - 1)^2 / 3 \approx 2^{125.84}$ ($3 \mid h_1$).
- **Discrete logarithm & exTNFS:**
  - Generic Pollard-$\rho$ in $G_1$ / $G_2$: $\frac{1}{2}\log_2(\pi r / 4) \approx \mathbf{127.25}$ bits ($\sqrt{r} \approx 2^{127.43}$).
  - Extended Tower Number Field Sieve (exTNFS) in $\mathbb{F}_{q^{12}}^*$: cryptanalytic literature consensus (Barbulescu–Duquesne 2019, Guillevic 2020, IETF CFRG / Zcash) places BLS12-381 at **~126–128 bits** classical depending on gate/memory cost model.
  - **Cheon's strong-DLP / $q$-SDH caveat:** Because $r - 1$ has smooth divisors up to the Filecoin `challenge_19` public maximum degree $d = 2^{28} - 2$ (specifically $2^{27} \mid r - 1$ and $3 \cdot 2^{26} \mid r - 1$), Cheon's algorithm recovers the trapdoor $\tau$ from $[1]_1, [\tau]_1, \dots, [\tau^d]_1$ in $O(\sqrt{r / D} + \sqrt{D})$ group operations: $\frac{1}{2}(\log_2 r - 27) \approx \mathbf{113.93}$ bits (or $\mathbf{113.64}$ bits using $D = 3 \cdot 2^{26}$), at substantial memory/group-operation cost. This is a standard property of all $2^{27}$–$2^{28}$ powers-of-tau ceremonies over 255-bit prime-order subgroups.
  - **Post-quantum:** **0 bits** (Shor's algorithm solves ECDLP and extracts $\tau$ in polynomial time).
- **Mandatory `G1` prime-order subgroup check:** Because $h_1 > 1$, an unvalidated point $P \in E(\mathbb{F}_q)$ can carry non-trivial torsion ($[r]P \neq \mathcal{O}$), breaking KZG binding and deferred pairing accumulation. Ix enforces the fast endomorphism check $\psi(P) = [-u^2]P$ (proved correct for the Lean model by `Ix.Cert.Compression.Bls12381.CurveMsm.bls12381_endoSubgroupCheck_sound`) in the hand-written recursive KZG circuit (`recursive/native_curve.rs`), in-circuit in the Aiur compression backend (`aiur_backend/g1.rs`, though no BLS12-381 Aiur program ships yet), and on EIP-2537 / Rust deserialization. The negative control `negControl_bls12381_missing_subgroup_check_rejected` refutes a Lean profile predicate, not a shipped circuit.
- **KZG / PLONK Schwartz–Zippel & Fiat–Shamir:** Over $\mathbb{F}_r$ ($\log_2 r \approx 254.86$), polynomial identity checks at degree $2^{27}$ (KZG trace cap) and $2^{25}$ (final PLONK) lose at most 27 and 25 bits respectively ($\ge 227.86$b and $\ge 229.86$b); deferred pairing folding loses $\le 1/r$ ($254.86$b); batched Horner openings over $m$ polynomials lose $\le (m - 1)/r$. Fiat–Shamir uses BLAKE3 (recursive KZG) and SHA-256 (final PLONK / `Bls12381PlonkVerifier.sol`), each providing **128 bits** classical collision resistance.
- **SRS provenance:** Filecoin Phase 1 `challenge_19` (`FILECOIN_CHALLENGE_19_BLAKE2B` BLAKE2b-512 pin, verified `FILECOIN_TAU_G1` / `FILECOIN_TAU_G2` anchors, `crates/proof-compression/src/kzg/srs/filecoin.rs`). Universal setup (1-of-$N$ honest participant); no circuit-specific Phase 2 setup.

#### 3. Endpoint 3 — BN254 (Aztec Ignition, Pre-Pectra EVM; current default)

- **Curve parameters:** Barreto–Naehrig curve (`alt_bn128`, EIP-196/EIP-197), $k = 12$, seed $u = 4965661367192848881$:
  - $q \approx 2^{253.60}$ ($\log_2 q = 253.60$, $\log_2 q^{12} = 3043.16$),
  - $r \approx 2^{253.60}$ ($\log_2 r = 253.60$, 2-adicity $28$),
  - `G1` cofactor $h_1 = 1$ (prime order; `G2` has cofactor $h_2 = 2q - r$).
- **Discrete logarithm & exTNFS:**
  - Pollard-$\rho$ in $G_1$: $\approx \mathbf{126.62}$ bits.
  - Cheon $q$-SDH with $2^{28}$ Ignition powers ($2^{28} \mid r - 1$): $\frac{1}{2}(253.60 - 28) \approx \mathbf{112.80}$ bits.
  - **exTNFS in $\mathbb{F}_{q^{12}}^*$ (bottleneck):** Kim–Barbulescu (2016), Menezes–Sarkar–Singh (2016), Barbulescu–Duquesne (2019), and Guillevic (2020) reduce BN254 target-field DLP to **~100 bits** classical. Consequently, Endpoint 3 fails Ix's Lean 128-bit compression profile (`negControl_bn254_fq_below_380`, `negControl_bn254_rejected_128`; a Lean predicate that no executable consults), yet it is the current `ix compress` default and the only endpoint with bundled release keys.
  - **Post-quantum:** **0 bits** (Shor's algorithm).
- **Schwartz–Zippel, Fiat–Shamir, and SRS:** Over $\mathbb{F}_r$ ($\log_2 r = 253.60$), polynomial checks at $2^{28}$ / $2^{25}$ retain $\ge 225.60$b / $\ge 228.60$b; folded pairing retains $253.60$b. Recursive KZG uses BLAKE3 (128b classical) and final PLONK (`PlonkVerifier.sol`) uses SHA-256 (128b classical); Groth16 is non-interactive (AGM / Knowledge-of-Exponent). KZG and PLONK use Aztec MAIN IGNITION (positions 196–197, 176 participants, universal 1-of-$N$). Groth16 requires a circuit-specific Phase 2 setup; the bundled Groth16 key is **development-only** (known trapdoor) and is rejected unless `--dev-srs` / `--dev-final-srs` is passed explicitly.

---

### Lean-4 Kernel-Certified Properties vs. Cryptanalytic Literature Estimates

All Lean-certified theorems below are checked by Lean's kernel when their
modules build, and `#guard_module_axioms` holds them to strictly standard Lean
axioms `[propext, Classical.choice, Quot.sound]` (zero `sorry`, zero custom
`axiom`, zero `native_decide`/`bv_decide`). CI independently replays every
project module in the full transitive import closure of the kernel, refinement,
and Aiur audit roots with Lean's kernel via `Scripts/KernelReplay.lean` (in
`certified-kernel`, `ixvm-refinement`, and `formal-unit-tests`), in addition to
`leanchecker` on the named audit modules. Definitional closures are SHA-256
pinned in `Ix/Cert/Security128ClosureManifest.lean`
(`Tests/Fixtures/security-128-closure-manifest.txt`),
`Ix/Cert/StatementClosureManifest.lean`
(`Tests/Fixtures/statement-closure-manifest.txt`), and
`Ix/Cert/AiurCompressionClosureManifest.lean`
(`Tests/Fixtures/aiur-compression-closure-manifest.txt`).

"Lean-Certified" below means that a statement is proved, not that it is about
the compiled binaries that ship. **No machine-checked theorem is about the Rust
or Solidity verifier binaries** (`multi-stark`, `stark-shrinker`,
`ix-proof-compression`, or Solidity): the FRI, STARK, and HVZK theorems are about
`CertiFRI`'s executable Lean verifiers `Fri.verify` (Horner batching),
`Fri.verifyTensor` (binary tensor batching), multi-arity (`2^a` / 8-ary)
tensor-batched FRI (`Fri.verifyTensorMulti`), unpruned & pruned-MMCS
`GoldilocksExt3` STARKs, and the `v6-zk` ROM HVZK model (over both 32-byte
`Digest` and 64-byte `Digest64`), the `IxCCAiur` compression proofs cover the
certified Lean-compiled AIR/LogUp circuit pipeline (`Aiur.MultiStarkBridge` →
`CompressionIntrinsicsProof` → `CompressWrapSpec`/`KzgPairingSpec` →
`EndToEndChain`), and the rest are inequalities between numbers or lemmas about
Lean models.

| Category | What Is Established | Authority / Location |
| --- | --- | --- |
| **Lean-Certified** | Goldilocks $\mathbb{F}_{p^3}$ cardinality $p^3 \ge 2^{191}$, irreducibility of $X^3 - X - 1$, exact UD `(5/8)^160 / 2^20 ≤ (3/4)/2^128` & Johnson `(33/64)^q / 2^20 ≤ (3/4)/2^128` ($q \ge 118$), 64B RFC 7693 `BLAKE2b-512` classical BCS (`255.7b`), BHT (`170.7b`), CNS (`204.8b`), & Grover (`256b`) bounds, LogUp `(W+2)L/|K|`, concrete `DynamicRom` instantiations for binary & multi-arity `Fp^3` tensor-STARKs (`soundness_dynamic_rom_starkTensor_fp3_ud`, `soundness_dynamic_rom_starkTensorMulti_fp3_ud`), negative controls rejecting $\mathbb{F}_{p^2}$, `(2,100,0,20)`, `(4,55,0,0)`, 32B digests at $N=2^{128}$ / $Q=2^{86}$, and retired 48B `BLAKE3-XOF48` for concrete 128-bit PQ (BHT/CNS/Grover lines are arithmetic inequalities and consider no quantum adversary) | `Ix/Cert/MultiStark/Audit.lean`, `Ix/Cert/MultiStark/DynamicRom.lean`, `Ix/Cert/MultiStark/Security128Audit.lean` |
| **Lean-Certified** | Pure-Lean RFC 7693 `BLAKE2b-512` spec + 6 kernel-checked KATs, 122 keyed & `derive_key` BLAKE3 KATs, `Blake2b512Domain` `personal` & `Blake3Domain` `derive_key` mode injectivity, `card_digest64 = 2^512`, unconditional `CurveListCA` (`curveListCA_fp3`) over $\mathbb{F}_{p^3}$, unconditional `Tensor2DMCA` (`goldilocksExt3_tensor2DMCA_ud_128`, `goldilocksExt3_zk_tensor2DMCA_ud_128`), unconditional Johnson/UD random-oracle soundness of `CertiFRI`'s executable Horner (`Fri.verify`), binary tensor (`Fri.verifyTensor`), and multi-arity (`2^a`, `logArity ∈ {1,2,3}`, fold factors `2, 4, 8`) tensor FRI verifiers including concrete Endpoint 1 profiles `FriParams.compact400KBBalanced` (`lb=4, q=58, pow=28`) and `FriParams.ultraCompact400KBZk` (`lb=4, q=55, pow=30`) over both 32B `BLAKE3` and 64B `BLAKE2b-512` under incremental-sponge BCS $c = 3/2$; cubic-extension `GoldilocksExt3.starkModel` + unpruned & pruned-MMCS (`prunedMmcs`) binary and multi-arity tensor STARK + LogUp soundness; and formal Protocol `v6-zk` HVZK (`v6Zk_alg_perfect_hvzk`, `v6Zk_hvzk`, `goldilocksExt3_v6Zk_hvzk`, `goldilocksExt3_ultraCompact400KBZk_hvzk` for both 16B `Salt16` / $2^{128}$ and 32B `Salt32` / $2^{256}$ salts, covering polynomial blinding, telescoping quotient slicing, masked-LogUp boundary hiding, multi-arity FRI randomizer uniformity, and salted-Merkle leaf hiding) | Upstream `CertiFRI` (`CertiFriProofs.Audit128`, `GoldilocksExt3Soundness`, `GoldilocksExt3MultiAritySoundness`, `Exec.Zk.V6ZkHvzk` at pinned `9ae20f3` on `formal/t53-v6-zk-hvzk`) |
| **Lean-Certified** | Monolithic single-oracle straight-line ROM extraction across $M$-node aggregation trees (eliminating $-\log_2 M$ union-bound loss) as a schema that assumes round-by-round soundness (`MultiRbrSound`), $\varepsilon_{\max}$ and extraction, which no theorem provides for the shipped verifier; Shape 17 security envelope equivalence; and the $M \le 16{,}384$ naive union-bound "headroom" at `(2, 128, 0, 20)`, which is arithmetic on the query term alone | `Ix/Cert/Aggr/MonolithicRom.lean`, `Ix/Cert/Aggr/Security128Audit.lean` |
| **Lean-Certified** | Endpoint 1a (`v6`) & Endpoint 1b (`v6-zk`) shrinker soundness schemas (`starkShrinker_v6_sound_128`, `starkShrinker_v6zk_sound_128`: they assume `MultiRbrSound`, $\varepsilon_{\max} \le (1/2)/2^{128}$ and extraction over abstract types, and their profile requires a 64-byte digest and has no folding-arity, cap or final-length fields, so they cannot be instantiated at the shipped shrinker), 11-domain BLAKE3 injectivity, 16B salted Merkle binding (no hiding or zero-knowledge property is defined or proved), $2\times$ odd-coset witness blinding, half-stride quotient telescoping, $W_R \ge 4$ span failure $< 2^{-126}$ (and $W_R = 3 > 2^{-64}$ negative control), all 4 `v6-zk` guardrails | `Ix/Cert/Compression/StarkShrinker.lean`, `StarkShrinkerZk.lean`, `StarkShrinkerAudit.lean` |
| **Lean-Certified** | BLS12-381 primality of $q, r$, BLS seed identities, $q \ge 2^{380}$, $r \ge 2^{254}$, $h_1 > 1$, 5×80-bit non-native $\mathbb{F}_q$ no-overflow & canonicality, 64-round Straus MSM, mandatory endomorphism `G1` subgroup check (`bls12381_endoSubgroupCheck_sound`) + torsion rejection, KZG batched Horner & folded pairing Schwartz–Zippel bounds (`≤ (m-1)/r`, `≤ 1/r`), `"ix/outer-ir/v1"` encoding injectivity, and constructive rejection of BN254 ($q < 2^{255} < 2^{380}$) & unchecked BLS12-381 cofactor. These are lemmas about Lean models: the `Ix/Cert/Compression` stage theorems quantify over arbitrary circuits and do not mention the shipped Rust circuits or keys | `Ix/Cert/Compression/Security128Audit.lean`, `Ix/Cert/Compression/Bls12381/{Field,CurveMsm,RecursiveKzg,OuterRelation,EndToEnd,Audit}.lean` |
| **Cryptanalytic Literature Estimate (Not Lean-Certified)** | Concrete exTNFS complexity in $\mathbb{F}_{q^{12}}^*$ (BLS12-381 ~126–128b, BN254 ~100b), Pollard-$\rho$ & Cheon $q$-SDH concrete work estimates, and 0b post-quantum security (Shor) for pairing curves | Kim–Barbulescu 2016, Menezes–Sarkar–Singh 2016, Barbulescu–Duquesne 2019, Guillevic 2020, Cheon 2006 |
| **External Cryptographic Assumption (Not Lean-Certified)** | Random Oracle / collision-resistance idealization of concrete BLAKE3 and SHA-256; AGM / $q$-SDH / Knowledge-of-Exponent knowledge soundness of KZG, PLONK, and Groth16; 1-of-$N$ honest participant assumption for Filecoin `challenge_19` and Aztec Ignition ceremonies | Standard cryptographic assumptions |
| **Implementation Surface (Differential / CI Tested; no machine-checked theorem)** | Rust provers/verifiers (`multi-stark`, `ix-proof-compression` KZG/PLONK/Groth16, `stark-shrinker`), and Solidity verifiers (`contracts/plonk`, `contracts/groth16`): the code that decides acceptance | Mirror tests (`lean_mirror_matches`), Foundry EVM suites, CPU↔GPU parity tests |

#### Size Hypotheses (`hclaims` / `htensor`) of CertiFRI's Packaged Unconditional Johnson Theorems

Each packaged unconditional Johnson theorem in `CertiFriProofs.Exec.SoundnessSponge`
(Horner batching) carries an explicit opened-values $\times$ LDE-size hypothesis
`hclaims : (Fri.claimRefs params.logBlowup shape).length * 2 ^ Fri.logMaxHeight params.logBlowup shape ≤ 2 ^ ClaimExp`,
and each packaged tensor-batching theorem in `CertiFriProofs.Exec.SoundnessTensorSponge`
carries the analogous padded tensor-dimension hypothesis
`htensor : 2 ^ (kCol + kOpen) * 2 ^ Fri.logMaxHeight params.logBlowup shape ≤ 2 ^ ClaimExp`
(while the unique-decoding tensor theorems only require `maxWidth ≤ 2^16`, `maxOpeningsPerHeight ≤ 2^16`, and `logMaxHeight ≤ 32`).
Neither the Lean nor the Rust verifiers enforce these `ClaimExp` products, and
full IxVM (~22,908 opened values) or recursive-verifier (~9,222 opened values)
widths at $2^{22}$–$2^{23}$ rows exceed these packaged Johnson constants
(at $2^{25}$ LDE size, $22{,}908 \cdot 2^{25} \approx 2^{39.5} > 2^{36}$):

| Packaged Johnson Theorem | `ClaimExp` | Max opened values at LDE $2^{24}$ / $2^{25}$ / $2^{28}$ |
| --- | ---: | ---: |
| `lb = 2, q ≥ 128` (`qpow = 20`) | 36 | 4,096 / 2,048 / 256 |
| `lb = 2, q ≥ 118` (`qpow = 20`) | 31 | 128 / 64 / 8 |
| `lb = 3, q ≥ 78` (`qpow = 20`) | 32 | 256 / 128 / 16 |
| `lb = 4, q ≥ 58` (`qpow = 20`) | 33 | 512 / 256 / 32 |

---

## Changing the Parameters

1. Update `Parameters::DEFAULT` (`crates/aiur/src/trace/stark.rs`) and its Lean
   mirror (`Ix/Aiur/Parameters.lean`) together. If any floor constant changes,
   update `crates/stark-key/src/security.rs` and `Ix/Aiur/Parameters.lean`
   together; `lean_mirror_matches` checks parity.
2. Run `lake exe fri-security` on representative proofs under the new parameters
   with `--regime johnson --require-min-bits 127` (for shipped 32-byte BLAKE3,
   hash-limited at 127.71b) or `--digest-bytes 64 --regime johnson --require-min-bits 128`
   (for the 64-byte profile), and verify UD $\ge 80$b, to confirm every regime
   remains above the security floor.
3. Every verifying key changes: the IxVM key, the recursion and aggregation keys
   (`tools/formal-aiur.keys`, updated via `lake env lean --run Scripts/CheckFormalKeys.lean --update`),
   and any compression release keys / stage manifests derived for the root key
   ([Deriving the verifying keys](../crates/proof-compression/README.md#deriving-the-verifying-keys)).
4. Run `lake env lean --run Scripts/CheckFormal.lean` to prove and verify IxVM,
   recursion, and aggregation under the new parameters.

For measurements, `compare` (`crates/stark-verifier/examples/compare.rs`) takes
`--parameters LOG_BLOWUP,QUERIES,COMMIT_POW,QUERY_POW`, and `--below-floor` for
research-only weaker settings.

---

## Historical Reference: Legacy `v5` ($\mathbb{F}_{p^2}$) Parameter Tradeoff Study

For provenance, the table below records the original legacy `v5`
($\mathbb{F}_{p^2}$, 100 queries, 220 conjectured bits) parameter sweep measured
on 2026-11-07 at `b919c570` on a 64-core Xeon 6975P-C (`compare --parameters`,
`Nat.add_comm` IxVM + recursive verifier). Protocol `v6` retired these
$\mathbb{F}_{p^2}$ / 100-query settings because the quadratic extension field
capped Johnson security near ~80 bits and conjectured security at 92.2 bits;
the relative blowup vs. query cost tradeoffs (higher `log_blowup` shrinks proofs
at the expense of LDE memory and prover time, while higher query PoW adds ~6 s
at 28 bits) remain informative when tuning Protocol `v6` profiles such as
`(2, 128, 0, 20)` vs. shrinker `(3, 78, 0, 20)` and `(4, 66, 0, 20)`.

| Legacy `v5` `(lb, q, cpow, qpow)` | Conjectured query | IxVM prove (s) | IxVM proof (MB) | Recursion cells (M) | Recursion FFT cost (G) | Recursion prove (s) | Recursion peak RSS (GB) | Recursion proof (MB) | `v5` $\mathbb{F}_{p^2}$ UD | `v5` $\mathbb{F}_{p^2}$ Johnson (BCHKS25 / DKT26) | `v5` $\mathbb{F}_{p^2}$ Conjectured |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 1, 64, 0, 0 *(#678)* | 64 | 0.49 | 6.00 | 930 | 142 | 20.7 | 45.8 | 3.17 | 26.6 | 31.9 / 31.9 | 62.3 |
| 2, 100, 0, 20 *(retired `v5`)* | 220 | 0.69 | 9.20 | 1,037 | 160 | 29.4 | 71.1 | 4.88 | 87.8 | 80.3 / 82.9 | 92.2 |
| 1, 200, 0, 20 | 220 | 0.56 | 17.90 | 1,839 | 292 | 39.9 | 82.9 | 9.36 | 92.2 | 81.0 / 83.8 | 92.2 |
| 3, 67, 0, 20 | 221 | 0.92 | 6.32 | 944 | 144 | 40.1 | 111.7 | 3.39 | 75.6 | 77.8 / 80.9 | 92.2 |
| 4, 50, 0, 20 | 220 | 1.36 | 4.84 | 929 | 141 | | | | 65.6 | 75.3 / 78.9 | 92.2 |
| 2, 96, 0, 28 | 220 | 6.59 | 8.85 | 1,032 | 159 | | | | 91.8 | 80.3 / 82.9 | 92.2 |
| 2, 100, 16, 20 | 220 | 0.75 | 9.20 | 1,037 | 160 | | | | 87.8 | 80.3 / 82.9 | 92.2 |
