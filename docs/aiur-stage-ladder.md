# Aiur compression stage ladder: minimal total work

> **Historical (2026-11-15).** This document is the ladder study. L3 was chosen; §4 records its implementation and measurements. BN1, BN2, `chain_v1` and the packed-chain terminal were removed afterwards. The current pipeline is described in [aiur-compression-architecture.md](aiur-compression-architecture.md).

Status: design study, 2026-11-15. Counts come from executions plus the
narrow template backend. Times are measured, except where a row says
"est.". There is one new GPU proof. Data:
`target/ladder-study/summary.json`. Tools:

- `narrow_count.rs`: `aiur_template_v2_init` plus `--stage/--key/--src`;
- `fixedkey_count.rs`: template counts, and with `--prove` a proof, of any
  fixed-key Aiur entry;
- `pkload/`: PLONK key-load timing.

Baseline: `target/e2e-narrow/run-lean`, Init, warm, **298.8 s**.

| Stage | Time | RSS |
|---|---:|---:|
| wrap | 10.7 s | 11.7 GB |
| packed CompressGL | 83.1 s | 85 GB |
| BN1 | 14.9 s | 37 GB |
| BN2 | 14.6 s | 37 GB |
| chain overhead | 6.7 s | |
| narrow BN3, 2 shards, 110 evaluations | 98.9 s, of which 27 s is fixed build, commit and SRS | 113 GB |
| terminal + PLONK `2^25` | 70.0 s, of which 47 s is load | 45 GB |

## 1. Findings

**BN2 does nothing.** BN1 turns the 219 KB GL proof into 122.5 KB. BN2 turns
122.5 KB into 122.6 KB. BN2 exists because the self-recursive `chain_v1`
originally needed its shapes to settle (§6.5a), and the narrow stage was
configured against stage-3 executions. A narrow stage at stage 2 (verifying
BN1) needs 61.84M rows at h0 and 66.80M at +8%: 2 shards, the same as today's
stage 3 (62.0M and 66.88M).

**Generic narrow directly on GL.** This is `chain_v1` stage 1, which reads the
GL key as data:

| Headroom | Rows | Shards |
|---|---:|---:|
| h0 | 69.25M | 3 |
| +8% | 74.79M | 3 |

That is only 12% more rows than on a BN proof, but it crosses the 2-shard
boundary at `2^25` (67.1M rows). The extra is 1,859 more BLAKE3 compressions
for the larger proof.

**Most of the generic stage is key hashing and parsing.**

- In the generic stage, `Blake3::compress` runs 9,314 times; about 6.8K of
  those hash the 415 KB predecessor key. `KzgDeserialize::node*` adds 8.6M
  rows, and `realign` adds 7.4M.
- The fixed-key verifier (`KzgPackedTerminal`, key tables fixed at export)
  avoids all of this:

| Fixed-key template counts (W=8) | h0 | +8% | +25% |
|---|---:|---:|---:|
| `CompressFinalPacked` complete relation, 121 KB BN proof | 19.65M rows, 1 shard | | 24.57M, 1 shard |
| `KzgPackedTerminal::verify`, GL proof (219 KB, GL key fixed) | 28.25M, 1 shard | **30.52M, 1 shard** | 35.32M, 2 shards |

On the GL proof, one shard holds up to +18.7% headroom. The generic 2-shard
stage holds only +8.2%.

**GPU validation: fixed-key narrow stage on the GL proof**, +8%, Ignition,
packed SHPLONK:

- **Phases:** execution 1.7 s, witness 6.2 s, fixed build 10.6 s, fixed commit
  14.3 s, SRS load 4.1 s, **prove 39.5 s**.
- **Total:** 77.5 s wall, peak RSS 105 GB.
- **Checks:** the proof verifies natively and a changed output is rejected.
- **Proof size:** the proof has 607 evaluations and is 22.9 KB, because the
  current Rust backend emits each map and ROM as its own circuit (32 table
  circuits). This is the same table-encoding problem the Lean stacked layout
  has today (561 evaluations, terminal 42.7M).
- **Expected with stacked tables:** the narrow stage scales at about 22
  evaluations per shard (2 shards: 110, 3 shards: 132), so a 1-shard proof
  should have about 88 evaluations, and the terminal should be about 20.6M.
  The terminal costs about 2.7M per shard (23.37M at 2 shards, 26.08M at 3),
  extrapolated, not compiled.
- **Sensitivity:** the table/ROM encoding is the largest risk to the terminal
  figure. Per-table circuits roughly double it.

**CompressGL narrow or fixed-key** (`target/root-width/model.py` components):

- **Fully narrow CompressGL (rejected).** It executes 2.63B instructions.
  `chain_v1` gives about 0.22 template rows per instruction, so a narrow
  CompressGL would be about 580M rows: about 18 shards, roughly 350 s.
- **Fixed wrap key in CompressGL.** The GL model attributes about 11–15% of
  CompressGL's cells to hashing the wrap key as data (`keyc`). This needs
  Aiur source only (est. −8 to −12 s).

**A narrow wrap on Goldilocks** (the hand-written FRI stage's role):

- CompressGL's leaf and row-opening terms scale with the wrap's opened
  elements per query. The two measured points are 5,598 elements → 126.7 s
  and 3,262 → 83.7 s, which fit about 18 ms per element plus about 24 s.
- At about 150 elements, CompressGL would be about 30 s, but the wrap would
  cost about 3–5× its 1.65B committed cells (est. 25–45 s).
- Net est. −10 to −30 s, unmeasured. It needs the template backend on
  Goldilocks.

**PLONK load (47 s; `pkload.txt`, `pkload-unbuf.txt`).**

- **Unbuffered reads.** `readVerified` feeds gnark an unbuffered
  `TeeReader(LimitReader(*os.File))`. Decoding the proving key takes 45.0 s
  this way and 22.3 s with `bufio`. A circuit decode takes 1.1 s, and SHA-256
  over 2.15 GB takes 1.7 s.
- **Point decompression.** The remaining 20–22 s is decompressing 2^26
  compressed G1 points. A raw re-encoding (`WriteRawTo`, 4.3 GB) loads in
  4.6 s with `UnsafeReadFrom` and 4.8 s with `ReadFrom`. SHA-256 over the raw
  file takes 3.0 s.
- **Result.** Load drops from 47 s to about 8 s; a resident prover makes it 0.
  These are prover-side changes; the key stays bound by the manifest digest.

## 2. Candidate ladders (Init, warm)

| | Ladder | Narrow stage | Terminal | Total |
|---|---|---|---|---:|
| B0 | wrap → GL → BN1 → BN2 → narrow | 2 shards, 98.9 s | 23.4M | **298.8** (measured) |
| L1 | wrap → GL → BN1 → narrow (stage 2) | 2 shards, about 99 s | 23.4M | about 283 |
| L2 | wrap → GL → generic narrow (stage 1) | 3 shards, about 118 s | 26.1M | about 285 |
| **L3** | wrap → GL → **fixed-key narrow** → terminal | 1 shard, 77.5 s (measured) | about 20.6M (`2^25`) | **about 242** |
| L3+ | L3 with the PLONK load fix, a cached fixed commitment and the fixed build overlapped with witness generation | about 53 s | same | **about 180** |
| L4 | L3+ with a fixed wrap key in CompressGL | | | about 170 |
| L5 | L4 with a narrow Goldilocks wrap | | | 150–190 (unmeasured) |

The L3 total is wrap 10.7 + GL 83.1 + narrow 77.5 + PLONK 70.0 s, plus about
1 s for the stage's claim and fold. L3+ is 242 s, less 39 s of load, less
14 s of commit, less about 9 s of overlapped build.

Memory: the peak stays CompressGL at 85 GB and the narrow stage at 105 GB.
The 1-shard stage uses 8 GB less than the 2-shard one.

**Trusted, unverified surface.** Every ladder keeps three items, so they are
not scored per ladder:

- packed SHPLONK in the crypto layer;
- the Go Aiur→PLONK translator;
- the Rust v2 lowering. The Lean tiling export replaces it as the
  production layout source.

| | New crypto-layer surface | Non-Lean, soundness-relevant | Prover-only (no soundness impact) |
|---|---|---|---|
| B0, L1, L2 | **Shared fixed slots** (`System::new_shared`, tag-2 key, owner openings) | Chain policy (`IXAUKG01`), stage-interval configuration | wrap admission, stage configurations |
| L3 / L3+ | **None.** One shard owns its fixed matrix (tag 1), so no shared slot. | No self-recursive chain policy: three fixed keys. The verifier plan comes from Lean `compilePackage` (§5a option 1). | PLONK raw key and `bufio`; fixed-commit cache keyed by layout digest |
| L4 | None | same as L3 | same |
| L5 | Narrow layout over Goldilocks FRI, crypto unchanged | Tiling theorem instantiated over Goldilocks | |

## 3. Recommendation: L3, then L3+, then L4

L3 is about −57 s (−19%) as a first step and about −120 s (−40%) with L3+.
It removes BN1, BN2, the self-recursive chain and shared fixed slots, and
gives a smaller terminal.

It requires:

1. **A fixed-key narrow stage program in Lean.**
   - `KzgPackedTerminal::verify` on the pinned GL key, plus `CompressBNPacked`'s
     transcript fold and claim output: a `CompressFinalPacked`-like entry
     without `PairingCheck`.
   - GL's proof shape must be fixed. The normalized wrap fixes its input, so
     the GL capacities only need to be pinned.
2. **The Lean tiling export of that artifact,** with stacked map/ROM tables.
   Without them the terminal is not at `2^25` (evaluations 607 instead of
   about 88).
3. **`CompressFinalNarrow` reconfigured** for the new narrow key and stage 2.
4. **Prover-side changes:**
   - a 4 MiB `bufio` in `readVerified`;
   - raw proving-key encoding read with `UnsafeReadFrom` under the manifest
     SHA-256;
   - optionally a resident PLONK prover;
   - caching the fixed-slot commitment by layout digest. Storing the fixed
     matrix is not viable: 1.41B cells is about 45 GB, so rebuild it, which
     takes 8–11 s and can overlap with execution.

**Narrow-stage levers, measured:**

| Lever | Effect |
|---|---|
| Shards | prove 39.5 / 56.0 / 75.0 s at 1 / 2 / 3 shards; about 2.7M terminal constraints and 22 evaluations per shard |
| `W` | the planner's optimum is `W` = 6–8, and 12–16 only add evaluations |
| Headroom | free up to the shard boundary |
| Fixed preprocessing | 22–25 s per run, nearly all avoidable |

**`2^24` (16.78M) is not established.** The 1-shard terminal is about
20.6M: G1 about 8M, BLAKE3 about 5M, the contract 1.8M. Closing the 3.9M gap
needs a census of the 1-shard terminal. Candidates within the rules: fixed-base
tables for the key's constant commitments and anchors, shared doublings
across the fold MSM, and fewer transcript compressions.

Not done: a proof with stacked tables, and the terminal compile on a 1-shard
proof.

## 4. L3 implemented (2026-11-15)

Run: `target/e2e-l3/run.sh` (warm), `target/e2e-l3/setup.sh` (cold). Data:
`target/e2e-l3/run/{table.txt,summary.json}`, census in
`target/e2e-l3/census/`.

**Stages.**

- **Narrow stage:** `CompressNarrowFixed::step_v1`
  (`MultiStark/MultiStark/CompressNarrowFixed.lean`, exe
  `compress_narrow_fixed_export GL_KEY OUT`).
  - Public call and semantics: `chain_v1` at stage one. The policy digest is
    checked, the policy's GL key digest must equal the digest of the embedded
    key (fixed at export, as in `CompressFinalPacked`), and the policy's
    anchors must equal the key's.
  - It checks the CompressGL claim (entry, reserved words, statement), runs
    `KzgPackedTerminal::verify_key` on the tabled key, and folds with
    `CompressBNPacked::fold` from infinity.
  - The stage is asserted to be 1. The terminal runs at stage 2
    (`Configuration::narrow` now accepts stage 2).
  - Policy (`aiur_packed_final_config --fixed-key-policy`): `IXAUKG01` with
    the GL key at stage one and the narrow key in the later slot. A bootstrap
    policy with a zero slot produces the narrow key first. That key depends
    only on the layout.
- **Tests** (`tests/aiur_narrow_fixed.rs`, ignored, on the Init GL proof).
  - The honest proof is accepted and passes the pairing check.
  - Each of these is refused by its own Aiur assertion: a changed
    statement, stage 2, flipped policy bytes, a re-digested policy naming
    another GL key digest, and another GL entry.
  - A forged `w2` executes but fails the pairing check.
- **Layout:** compact tables of `narrow_heap_sound_compact` (§5g), consumed
  from the exporter. The proof has 3 circuits (shard `2^25`, map and ROM
  tables `2^19`), 96 evaluations, 33 packs and 3,853 bytes.
- **Terminal:** 30,198,869 constraints (`2^25`). Power-of-two capacities,
  every map receiver kept, current Go gate lowering. With the per-node Go
  path (HEAD `aiur_plonk.go`, compile only) it is 34,687,714 (`2^26`, no SRS).
  Gas 285,614 (forge, memory args), the same as B0.

**Warm Init, end to end: 209.7 s** (B0 298.8 s, −89.1 s; hand-written 403 s):

| Stage | Total | Notes | Hand-written |
|---|---:|---|---:|
| wrap | 10.7 s | | 25 s |
| CompressGL (`--gl-only`) | 88.0 s | | FRI 94 s |
| fixed-key narrow | 75.9 s | witness 8.8 s, prove 36.7 s, SRS 4.1 s, cached commitment 4.8 s (was 14.3 s), waiting for the Lean layout 19.7 s | first + recursive KZG 98 s |
| terminal + PLONK | 35.2 s | load 11.0 s (was 47 s): raw key 8.9 s including the canonical re-encoding check; prove 22.6 s | 36 s |

**PLONK load.** `readVerified` reads through a 4 MiB `bufio`.
`proving-key.raw` is written on the first load. It is read with gnark's
checked `ReadFrom` and re-encoded compressed, and the re-encoding must match
the manifest's `proving-key.bin` length and SHA-256. Otherwise the
compressed key is used. The verifying key and the manifest are unchanged.

**Cold costs** (one-time):

| Step | Time |
|---|---:|
| narrow program export (Lean) | 197 s |
| terminal export (Lean) | 168 s |
| bootstrap narrow proof, which fixes the key | 86 s |
| PLONK compile | 45 s |
| PLONK SRS export | 19 s |
| PLONK setup, with the `2^25` Lagrange basis reused | 92 s |
| first key load, which writes the raw key | 59 s |
| first commitment, which fills the cache | +9.5 s |

**Terminal census** (Go census on per-chip compiles, 28.1M of 30.2M; the
rest is the global LogUp and commitment overhead):

| Part | Lowered | Per-node |
|---|---:|---:|
| G1, Fq and MSM | 13.18M | 16.12M |
| `Blake3::compress` | 6.82M | 7.55M |
| BLAKE3 glue and transcript | 1.63M | 1.88M |
| fixed tables (`UInt8::pair_inputs` 4.34M) | 4.36M | 4.36M |
| other | 2.12M | 2.68M |

`2^24` (16.78M) needs about −13.4M. For comparison, B0's terminal was
23.3M, at exact capacities with unused maps removed, on a 110-evaluation
proof. The L3 terminal was not compiled with those settings, because the
audit rules them out. Reaching `2^24` would need the padding back (exact
rows, argued only in a comment) plus G1 and BLAKE3 reductions; it is not
established.

**Remaining overhead.** The narrow stage waits 19.7 s for `tiling_export2`,
which is bounded by `Sharded.check` and `checkTables`; caching the export by
input digest would remove most of this wait. The 4.8 s commitment time with
a cache hit is interpolation. CompressGL is 88 s.

**Prover-side scheduling (2026-11-15).** Benchmark:
`target/e2e-l3/bench.sh`, record in
`docs/measurements/aiur-compression-l3.json`. Warm Init end to end is
167.9 s, median of 3 runs [156.8–187.8]; the spread comes from other
sessions' load. The changes are all prover-side, and the proofs are
unchanged.

- The `tiling_export2` output is replayed from a cache keyed by the exporter
  binary and its input (`tiling-export-cached.sh`).
- Each stage process starts early and waits for its predecessor
  (`--wait-for`). During CompressGL's single-threaded execution, the narrow
  stage builds its circuits and the fixed-slot setup, and the PLONK key
  loads.
- CompressGL witness generation fills and shards traces in parallel (trace
  22.4 s → 8.8 s).
- The SHPLONK opening divides packs that share a width and point set once
  (CompressGL open 10.2 s → 8.9 s).

**PLONK prover profile** (`target/e2e-l3/prof/*.pprof`, Go CPU profile via
`IX_PLONK_CPU_PROFILE`): `Prove` is 22.4 s wall but 103 s CPU, an average
of 4.6 cores. The CUDA callbacks (MSM, quotient numerator, canonical
transform) cover about 6 s.

| CPU phase | Wall time |
|---|---:|
| `NewTrace` (selectors and permutation), serial, before solving | 5.6 s |
| permutation ratio `Z` | 3.6 s |
| linearized polynomial | 2.2 s |
| KZG batch opening, two segments | 4.3 s |
| solver | 1.9 s |

`NewTrace` depends only on the circuit. A gnark that precomputes it while
the prover waits for its witness takes the prove from 22.5 s to 16.9 s;
measured once, and the proof verifies against the same verifying key.
- The patch is `target/e2e-l3/0001-plonk-bn254-let-a-proving-key-carry-a-precomputed-tr.patch`
  (fork `~/repos/forks/gnark-trace-cache`).
- `tools/gnark` already calls it through an optional interface, so with the
  pinned gnark it is a no-op.
- The trace holds about 16 GB while it waits.
- **Pending decision (the user's):** moving the gnark pin to a revision with
  this hook. `go.mod` and every pin are unchanged until then.
- The remaining CPU phases, the permutation ratio `Z` (3.6 s) and the KZG
  batch-opening folds (4.3 s), are not behind gnark's `Accelerator`
  interface, which offloads only MSMs, the quotient numerator and the large
  inverse FFT. Moving them to the GPU needs the same kind of gnark or
  gnark-crypto change.

## 5. L4: the wrapper key fixed in CompressGL (2026-11-16)

L4 is L3 with CompressGL compiled for the one wrapper key that the
normalized wrap layout pins (`m16384w64-v3.layout.json`, `key_blake3`
`1bc0cd05…`). Setup: `L3_DIR=target/e2e-l4 GL_FIXED=1 GL_ROM_SRC=
LEAN=target/e2e-l4/lean-bin target/e2e-l3/setup.sh`. Warm run:
`L3_DIR=target/e2e-l4 target/e2e-l3/run.sh`. Benchmark:
`L3_DIR=target/e2e-l4 target/e2e-l3/bench.sh 3
docs/measurements/aiur-compression-l4.json`. L3's products in
`target/e2e-l3` are unchanged, and the scripts default to them.

**Program.** `MultiStark/MultiStark/CompressGLFixed.lean` (exe
`compress_gl_fixed_export WRAP_KEY OUT`) uses the same mechanism as
`CompressNarrowFixed` and `KzgPackedTerminal::withKey`:

- The template module `CompressGL` declares the key word table
  (`key_inputs`/`key_values`, `map key_word`), the constants `KEY_WORDS` and
  `KEY_OFFSET`, and a one-row digest table (`key_digest_bytes`).
- `source key` fills these at export from the key bytes. The digest table
  holds `BLAKE3(key)`, computed from the same bytes.
- `CompressGL::verify_root` keeps the public call and the statement of
  `CompressWrap::verify_root`: `reserved = 0`, and
  `statement_digest = BLAKE3("ix/compress-wrap/v1" ‖ key digest ‖ claims digest)`.
  The key digest is the tabled one. The claims stay data on channel 2 and
  are hashed in circuit.
- The key is parsed in circuit by `SystemDeserialize::read_system`, from a
  byte stream rebuilt from the tabled words. Each byte is range-checked by
  `UInt8::from_fields`. The proof is verified by
  `StarkVerifier::verify_batch_at`, as in
  `MultiStark::verify_multi_stark_proof`.
- Removed from the circuit: reading the key from channel 1 twice and hashing
  it twice, once for the statement and once in
  `verify_multi_stark_proof`.

Nothing else changes. The Rust entry, the wrapper admission (`WrapPolicy`)
and the narrow and terminal programs are the same; only their inputs are
regenerated.

**How the wrapper key stays bound.**

1. The key bytes are fixed columns of CompressGL's map table, so CompressGL's
   key (`gl-key.bin`, fixed commitments) commits to them. A proof under that
   key verifies a STARK against exactly those bytes.
2. The narrow stage embeds the CompressGL key in its tables. Its policy
   (`IXAUKG01`) names that key's digest, the terminal embeds the narrow key,
   and the PLONK verifying key fixes the terminal. So the PLONK verifying
   key determines the wrapper key, through the same chain that already bound
   the CompressGL key in L3.
3. The statement is unchanged and still contains the key digest. The narrow
   stage checks the CompressGL claim against the original statement
   (`CompressBN::previous`). The tabled digest is `BLAKE3` of the tabled
   bytes, computed at export as in `CompressNarrowFixed`, so a GL proof
   can only satisfy a statement that names this key.
4. Prover-side admission is unchanged. `WrapPolicy` pins the wrapper
   artifact, key and layout, and `run.sh` checks
   `wrap_key_is_layout_key`.

A different wrapper key would need a new export and new keys downstream,
in the same way that a new GL key needs a new narrow program in L3.

**Counts** (CompressGL on the Init wrap proof, L3 → L4):

| | L3 | L4 |
|---|---:|---:|
| instructions | 2,665,679,264 | 2,550,652,484 (−4.3%) |
| main cells, unpadded | 665,440,666 | 640,301,317 (−3.8%) |
| main cells, padded, sharded | 703,868,438 | 675,768,284 (−4.0%) |
| circuits (system / active / fixed) | 94 / 83 / 15 | 96 / 86 / 17 |
| fixed rows | 2,066,050 | 2,131,428 (a key table of 2^16 rows) |
| ROM heights (`gl-rom.json`) | | width 8: 256 → 128, width 11: 32 → 1 |
| key / proof bytes | 406,989 / 212,701 | 403,748 / 219,469 |
| narrow rows (one `2^25` shard) | 30,036,791 | 31,117,651 |
| terminal constraints (`2^25`) | 27,611,602 | 27,611,609 |
| gas (memory-argument call) | 285,614 | 285,614 |

The saving is about a third of the model's `keyc` estimate (11–15% of
cells). That estimate attributed key reading, hashing and parsing together,
on a raw root key. The in-circuit parse remains: about 244K
`SystemDeserialize::read_vk_u8` rows and the node and lookup lists, plus one
read of the key from the table. The extra circuits (key table, `key_stream`)
make the GL proof 3% larger, so the narrow stage verifies about 1.1M more
rows, still within its single shard. The next lever is the same move as
`KzgPackedTerminal::parseKey`: parse the `Sys` structure at export into
structured tables, so that the verifier reads nodes and lookups from tables
instead of parsing bytes. That requires a tabled variant of the
`StarkVerifier` graph evaluation and was not done.

**Warm Init, end to end: 163.1 s**, median of 3 [162.5–165.8], against
L3's 167.2 s [167.2–167.2]: −4.1 s (−2.5%). Same machine conditions as L3
(bench.sh: idle, `heavy.lock`, `ixbench.slice`), stage binaries identical to
L3's, and all 8 checks passed in every run.

| Stage (median) | L3 exposed | L4 exposed | L3 process | L4 process | L4 witness / prove |
|---|---:|---:|---:|---:|---:|
| wrap | 11.6 s | 11.7 s | 11.5 s | 11.7 s | 6.9 / 3.5 s |
| CompressGL | 77.2 s | 72.8 s | 82.5 s | 77.5 s | 39.3 / 32.6 s (L3 42.1 / 34.1) |
| fixed-key narrow | 54.7 s | 54.5 s | 75.3 s | 73.9 s | 7.6 / 46.3 s |
| terminal + PLONK | 23.8 s | 24.1 s | 45.5 s | 36.8 s | 0.5 / 23.1 s |
| **end to end** | **167.2 s** | **163.1 s** | | | |

CompressGL peak RSS drops from 85.1 GB to 82.1 GB. The PLONK process time
differs only because of how long the process waits before its predecessor
finishes; its exposed time and prove time are unchanged.

**Cold setup.** One new step, `export_gl`: 162 s and 0.9 GB RSS when
measured alone (the generic `compress_gl_export` takes 101 s). The other
steps are L3's. Their recorded times in `target/e2e-l4/artifacts/setup-times.txt`
include waiting for another session's runs on `heavy.lock`, so they are not
comparable with L3's 1,405 s. The new wide export of CompressGL was a cache
miss (49 s) in the setup's GL step.

**Identities** (BLAKE3 unless marked; L3 → L4):

| Item | L3 | L4 |
|---|---|---|
| CompressGL artifact | `a05f4ee78f024e8a…` (re-exported bit-identically today) | `aa97f5d2642d7bc1…` |
| CompressGL key | `0b71c06784c5c76a…` | `26c98f70981b8a5a…` |
| `gl-rom.json` (SHA-256) | `ddfb51049e55398b…` | `3c33a3b25459df9b…` |
| `narrow-fixed.ixa` | `efaf4ede3b3890d2…` | `2fd371ee2aacb819…` |
| narrow key | `a955432ea0d2fb62…` | `eeb778cf4469db74…` |
| policy (`l3-policy.bin`) | `9b95e86b3f8e2512…` | `6034486774bd9396…` |
| terminal artifact | `bd9a0daca36a421c…` | `75818669b070e4e4…` |
| terminal SCS (SHA-256) | `54a12ad1ea0b6015…` | `bbdeab0303bde52f…` |
| PLONK verifying key (SHA-256) | `30dd3ee852f4fb3b…` | `1eba23135718e487…` |
| `PlonkVerifier.sol` (SHA-256) | `e8f62c3bc4c5c9e2…` | `0ac2a51766e67703…` |

These are pin candidates only; no pin was edited. Record:
`docs/measurements/aiur-compression-l4.json`.
