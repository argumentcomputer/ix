# Aiur compression: architecture (L3)

Status: current, 2026-11-16 (all-Lean circuits, §3). This is the entry point for the Aiur
compression pipeline. It describes the one supported ladder (L3), what each
stage verifies, where the verified relation is defined, what is still
trusted, and where each soundness argument is written down. Design studies
and logs that led here are listed in §6 and are historical.

## 1. The ladder

```
IxVM root (Goldilocks/BLAKE3 STARK)
  -> CompressWrap        normalized wrap of the root (Goldilocks FRI)
  -> CompressGL          FRI verifier over BN254, packed-SHPLONK KZG proof
  -> CompressNarrowFixed fixed-key narrow stage, stage 1, packed-SHPLONK proof
  -> CompressFinalNarrow terminal Aiur relation, stage 2
  -> gnark PLONK         2^25 Ignition circuit, Solidity verifier
```

| Stage | Lean source | Entry | Prover (Rust) |
|---|---|---|---|
| wrap | Goldilocks wrap program (`target/wrap-normalized/policies/m16384w64.ixa`) | CompressWrap | `stark-verifier wrap-prove` (`crates/stark-verifier/src/compress_wrap*.rs`) |
| GL | `MultiStark/MultiStark/CompressGL*.lean` | `CompressGL::verify_root` | `compress_gl_packed_chain --gl-only` (`PackedGlProver`, `aiur_backend/compress_gl.rs`) |
| narrow | `MultiStark/MultiStark/CompressNarrowFixed.lean` (exe `compress_narrow_fixed_export GL_KEY OUT`) | `CompressNarrowFixed::step_v1` | `aiur_template_v2_init --fixed-key --config ... --prove --packed --save` (`aiur_backend/template/v2*.rs`) |
| terminal | `MultiStark/MultiStark/CompressFinalNarrow.lean` (exe `compress_final_narrow_export`) | `CompressFinalNarrow::verify_accumulator_v1` | `aiur_narrow_terminal_prove --cuda` (`aiur_backend/plonk.rs`, `tools/gnark`) |

Driver scripts: `target/e2e-l3/setup.sh` (cold: Lean exports, stage
configuration, bootstrap and L3 policies, the narrow key, PLONK setup) and
`target/e2e-l3/run.sh` (warm: every stage proves and verifies). Measurements:
`docs/aiur-stage-ladder.md` §4 (warm Init 209.7 s when first measured, 143.5 s with the single-process driver, §8.11; narrow proof 3,853 bytes,
96 evaluations; terminal 30,198,869 constraints at `2^25`; gas 285,614).

**Narrow stage.** The CompressGL key is embedded in the program's fixed
tables (`KzgPackedTerminal`), and its BLAKE3 digest is fixed at export. The
entry asserts stage 1, authenticates the chain policy, requires the policy's
GL key digest to be the embedded key's and its anchors to be the key's,
checks the CompressGL claim, verifies the packed proof
(`KzgPackedTerminal::verify_key`) and folds the deferred pairing with the
transcript-derived weight (`CompressBNPacked::fold`) from infinity. The
program is laid out by the verified Lean tiling pass (`tiling_export2`, one
`2^25` shard, compact map and ROM tables, `narrow_heap_sound_compact`), so
its proof has three circuits and each owns its fixed matrix.

**Terminal.** It embeds the narrow key, authenticates the policy against the
configured digest, checks the narrow claim's chunk headers, verifies the
narrow proof, folds, and returns the folded pair as eighteen affine words.
The PLONK backend binds those words to gnark's constrained `PairingCheck`
with the Ignition anchors.

## 2. Formats

One format per role. Everything else was removed (§5).

| Role | Format | Writer | In-circuit parser |
|---|---|---|---|
| Packed key | `IXAUSK02` (fixed section tag 0: no fixed, tag 1: per-circuit commitment; tag 2: shared slots, not used by L3) | `kzg_packed_advice::key_bytes` | `KzgPackedDeserialize::key` / `KzgPackedTerminal` tables |
| Packed proof | `IXAUSP01` | `kzg_packed_advice::proof_bytes` | `KzgPackedDeserialize::proof` |
| Claims | `IXAUCL01` | `kzg_advice::claims_bytes` | `KzgDeserialize::claims` |
| Chain policy | `IXAUKG01`: anchors, GL key digest and entry, narrow key digest and entry | `PackedPolicy::chain` | `KzgPackedDeserialize::chain_policy` |
| Fold rule | transcript-derived weight, `acc = cur + w·prev` | `compress_bn::fold_packed` (native reference) | `CompressBNPacked::fold` |
| Terminal schema | `ix-aiur-plonk-terminal-v1`, power-of-two capacities, every map receiver kept | `plonk::Exporter::terminal_entry` | `tools/gnark` |

The per-column formats (`IXAUKY01`, `IXAUPF01`, `IXAUKL01`, `CompressBN`,
`CompressFinal`) remain only for the documented fixtures checked by
`tools/check-aiur-compression-fixtures.sh` and their tests; L3 does not use
them.

## 3. Verification surface

Policy: only the cryptography layer (multi-stark STARK, FRI, LogUp, PCS) and
the final endpoint (gnark PLONK, the Solidity verifier, the Ignition SRS) may
stay outside Lean. Soundness-relevant logic belongs in Lean/Aiur, and no new
unverified functionality is added. Witness generation, GPU kernels and
scheduling are prover-only: a wrong witness only fails verification.

**In Lean, proved.** The Aiur compiler (`Aiur/Aiur/Audit.lean`); the narrow
tiling pass and its composition with the compiler theorem
(`Aiur/Aiur/Tiling/*`, `Periodic.narrow_heap_sound_compact`, the `enables`
certificate `Bridge.checkEnables`).

**In Lean, not yet proved.** The verifier programs themselves
(`MultiStark/MultiStark/BN/*`, `CompressGL*`, `CompressNarrowFixed`,
`CompressFinalNarrow`): no theorem yet says they implement the verifiers.

**Outside Lean, soundness-relevant** (each a migration item of
`docs/aiur-verification-surface.md` §3):

1. Rust lowering of chips to multi-stark circuits (`trace/stark.rs`,
   `aiur_backend/kzg.rs`, `kzg/circuits.rs`) and the artifact decoder. Since
   2026-11-16 (02:47 UTC) no L3 stage proves a Rust-lowered circuit: the
   wrapper (layout v3, `lowering: "lean-wide-v1"`) and CompressGL (grouped
   export) prove `wide_export`'s circuits, the terminal's map tables are the
   shared tables of `plonk_export`. The Rust lowering still runs to generate
   witnesses and to supply shapes and counts that are checked against the
   export, and as the cross-check (`--rust-cross-check`,
   `IX_WRAP_RUST_CROSS_CHECK=1`) or old-key path (`--rust-circuits`, layouts
   without `lowering`).
2. The narrow stage takes every circuit from `tiling_export2` (input format
   2, `aiur-template-lean-plan.md` §8): Rust lowers the exported
   `Bridge.lower` graphs to templates and proves the exported shard and
   compact table circuits read literally; the template lowering itself
   (`template/v2.rs`: `lower`) is still Rust, checked template by template
   against the export. Rust's `compile_graph` lowering, `narrow_circuit` and
   `compact_circuit` remain only as a cross-check (`--rust-cross-check`).
3. Key writers (`kzg_packed_advice::key_bytes`): the key bytes are the
   verified relation.
4. Statements and policies (`compress_wrap.rs` statement, `WrapPolicy`,
   `PackedPolicy`, `pairing/final_program.rs` configuration).
5. The terminal circuit: the Lean-checked constraint system
   (`plonk_export`, `ix-aiur-scs-v1`) and its Go loader
   (`tools/gnark/aiur_plonk_scs.go`: the reader and `Define`, which makes one
   gnark constraint per file gate), gnark's `PairingCheck` on the outputs
   (`aiur_plonk_pairing.go`) and the BSB22 commitment. The Go translator
   (schema circuit, gate lowering, LogUp and BLAKE3 in Go) was deleted on
   2026-11-16 (`aiur-plonk-lean-backend.md`, Round 6c). Prover-only:
   the witness of the input wires (`plonk/scs.rs`) and the hints of the
   other wires (`aiur_plonk_scs_wires.go`).

**Crypto layer additions (B, FV TODOs).** Packed SHPLONK, the transcript
fold weight, deferred-pairing accumulation, circuit copies, and the
shared fixed slots of the multi-stark fork (`System::new_shared`; L3 does not
share a slot, multi-shard narrow stages do).

**L3 keys after the Lean-circuit switch (2026-11-15, 21:46).** The narrow
stage now proves the `tiling_export2` format-2 circuits and the terminal's
function and ROM circuits are the `wide_export` tables, so the keys after
CompressGL changed (`target/e2e-l3/artifacts`, `plonk-prepared`; the old
ones are kept in `target/e2e-l3-lean/old`). Unchanged: CompressGL key
(`gl-key.bin`, BLAKE3 `faa3101f…`), `narrow-fixed.ixa` (BLAKE3 `fb48452d…`),
bootstrap policy. Old → new:

| Item | Old | New |
|---|---|---|
| narrow key (BLAKE3) | `6885ff89914a3155…` | `dd3dab1bf7792295…` |
| L3 policy (BLAKE3) | `e9a259a00b8a276a…` | `a0a3c5bd6dd9c5e7…` |
| `compress-final-narrow-l3.ixa` (BLAKE3) | `0b62c5ce8cf7edb4…` | `5cee447778a7be60…` |
| PLONK schema (SHA-256) | `852dc4030d1b8883…` | `17303b9eef91ce0a…` |
| PLONK verifying key (SHA-256) | `64060d3d3f4245d1…` | `ed36739b0878cee0…` |
| `PlonkVerifier.sol` (SHA-256) | `32806f3360bfc667…` | `9c150ce75fbee196…` |
| terminal constraints at `2^25` | 30,198,869 | 30,109,043 |

Gas of the Solidity verifier is unchanged (285,614). These are pin
candidates; no pin was edited.

**L3 terminal keys after the Lean SCS switch (2026-11-16, 00:27 UTC).** The
terminal PLONK circuit is now the Lean-checked constraint system
(`plonk_export`, `ix-aiur-scs-v1`) loaded by `tools/gnark/aiur_plonk_scs.go`;
the Go translator is retired. `target/e2e-l3/plonk-prepared` holds the new
keys (the translator's are kept in
`target/e2e-l3-lean/old-translator-plonk-prepared`); `run.sh` passes
`--scs $A/terminal.ixscs` (setup.sh step 6 writes it). Everything before the
terminal is unchanged. Old → new:

| Item | Old (translator) | New (Lean SCS) |
|---|---|---|
| terminal circuit | schema `17303b9eef91ce0a…` | SCS `4d8b599fe5d8bf16…2a6aa` + pairing `eec66e8aa0bc78e8…3b86` |
| PLONK verifying key (SHA-256) | `ed36739b0878cee0…7e06` | `e1be9b01483fdf9f…3ed5d` |
| `PlonkVerifier.sol` (SHA-256) | `9c150ce75fbee196…` | `a33226a6560ffb7c…7c71` |
| terminal constraints at `2^25` | 30,109,043 | 28,000,870 |
| gas (memory-argument call) | 285,614 | 285,614 |

The manifest (`ix-aiur-scs-artifacts-v1`) pins `ScsSHA256` and
`PairingSHA256`. Pin candidates only; no pin was edited.

**L3 keys after the all-Lean switch (2026-11-16, 02:47 UTC; current).**
Every circuit of every L3 stage now comes from a Lean exporter:
- the wrapper proves `wide_export`'s circuits at layout
  `m16384w64-v3.layout.json`, which has `lowering: "lean-wide-v1"`;
- CompressGL proves `wide_export`'s grouped export, with its 12 ROM heights
  pinned by `artifacts/gl-rom.json` (`--gl-rom`), so its key has 15 fixed
  circuits;
- the narrow stage proves `tiling_export2`'s circuits, as before;
- the terminal is `plonk_export`'s constraint system with shared map tables
  (`plonk_shared_heap_sound`).

Because the GL key changed, everything that embeds it was regenerated.
`target/e2e-l3/setup.sh` now runs the whole cold setup (wrap → GL → narrow
→ terminal → PLONK, 1,405 s in total). It snapshots the stage binaries in
`target/e2e-l3/stage-bin`, which `run.sh` and `bench.sh` run. `run.sh`
writes `checks.json`, which records each stage's native verification and its
rejection of a changed output. `gas.sh RUN_DIR` runs the forge
memory-argument test. The previous setup is kept in
`target/e2e-l3-lean/old-pre-allLean`.

The narrow stage still fits one `2^25` shard, using 30,036,791 of
33,554,432 rows (previously 30.58M).

Old → new (BLAKE3 unless marked):

| Item | Old | New |
|---|---|---|
| wrap layout config | `m16384w64-v2` | `m16384w64-v3` (`lean-wide-v1`) |
| wrapper artifact | `9db8e6585bfc730b…` | unchanged |
| wrapper key | `1d30e08a87a42d1b…` | `1bc0cd05e3d1ad8d…` |
| wrap layout | `e97e6b3658ee5adc…` | `81b62471a48b5ec8…` |
| `WrapPolicy` digest (`claim_prefix [1,0]` unchanged) | `9d8fc61dea103514…` | `f366829dcfe9bf71…` |
| CompressGL artifact | `a05f4ee78f024e8a…` | unchanged |
| CompressGL key (`gl-key.bin`) | `faa3101f1a5956cb…` | `0b71c06784c5c76a…` |
| `gl-rom.json` (SHA-256) | (none) | `ddfb51049e55398b…` |
| `narrow-fixed.ixa` | `fb48452d2e088634…` | `efaf4ede3b3890d2…` |
| bootstrap policy (SHA-256) | `69fcbfd4cdc5836e…` | `31d04e96de28a063…` |
| narrow key | `dd3dab1bf7792295…` | `a955432ea0d2fb62…` |
| L3 policy | `a0a3c5bd6dd9c5e7…` | `9b95e86b3f8e2512…` |
| `compress-final-narrow-l3.ixa` | `5cee447778a7be60…` | `bd9a0daca36a421c…` |
| terminal SCS (SHA-256) | `4d8b599fe5d8bf16…` | `54a12ad1ea0b6015…` |
| pairing configuration (SHA-256) | `eec66e8aa0bc78e8…` | unchanged |
| PLONK verifying key (SHA-256) | `e1be9b01483fdf9f…` | `30dd3ee852f4fb3b…` |
| `PlonkVerifier.sol` (SHA-256) | `a33226a6560ffb7c…` | `e8f62c3bc4c5c9e2…` |
| terminal constraints at `2^25` | 28,000,870 | 27,611,602 |
| gas (memory-argument call) | 285,614 | 285,614 |

These are pin candidates only; no pin was edited.

## 4. Soundness notes index

| Topic | Where |
|---|---|
| Packed SHPLONK construction, transcript order, soundness sketch | `aiur-packed-kzg-soundness.md` §1–§3 |
| Recursion, circuit copies, transcript-derived fold weight | `aiur-packed-kzg-soundness.md` §4, §4a |
| Deferred-pairing accumulation and the terminal pairing | `aiur-compression.md` §3.2, §3.3, §27 |
| Narrow template obligations (copy wiring, messages, keyed chunks) | `aiur-template-backend.md` "Soundness argument" |
| Shared fixed slots in multi-stark | `aiur-template-backend.md` "Soundness of sharing" |
| Verified tiling theorems and their hypotheses | `aiur-template-lean-plan.md` §3–§4, §5f (coverage), §5g (compact tables), §8 (trust gaps) |
| Inventory of the non-Lean surface and the migration plan | `aiur-verification-surface.md` §2–§3 |
| Trust after the change (original statement) | `aiur-compression.md` §5 |

## 5. Removed in the consolidation (2026-11-15)

- Non-power-of-two PLONK capacities (`plonk.rs`, Go `validate`): capacities
  are powers of two again and the row cycle is the STARK's.
- Unused-map receiver removal (`plonk/unused_maps.rs` and its Go test).
- The combined-coefficient KZG overlay (`KzgPcsCombined.lean`,
  `kzg_combined_export`, its test).
- The Rust template prototypes: the v1 layout (`template.rs` v1 backend,
  `template/lower.rs`, `template/lean.rs`) with its tests, and the v2
  Rust-only layout path (proving from a Rust-derived fixed matrix, the
  `--lean-reference` cross-check, stacked tables in the driver).
- Stage entries outside L3: `CompressBNPacked::{first_v1, compress_v1,
  chain_v1}` with their step functions, the three-key packed policy
  `IXAUKP01`, the packed-chain terminal `CompressFinalPacked` and its test.
  The Rust `PackedProver` for `chain_v1` artifacts remains only because
  `compress_gl_packed_chain` still links it.
- Diagnostic examples (`aiur_column_verifier_cost`, `aiur_packed_*_cost`,
  `aiur_packed_verifier_comparison`, `aiur_packed_straightline_dump`,
  `aiur_template_{count,lean_chain,v2_fixture}`, `compress_bn_packed*`,
  `packed_shplonk_comparison`). Their recorded results stay in
  `docs/measurements/`.

## 6. Historical documents

These record the designs and measurements that led to L3. They are kept for
their arguments and data, not as descriptions of the current code:
`aiur-compression.md` (original proposal and checkpoint log),
`aiur-narrow-recursion.md`, `aiur-structural-gap.md`,
`aiur-template-backend.md` (prototype; its soundness sections are current),
`aiur-template-lean-plan.md` (plan and proof status), `aiur-stage-ladder.md`
(ladder study; §4 is the L3 measurement), `aiur-verification-surface.md`
(audit before the consolidation).

## 7. Environment: keeping the Lean toolchain alive (proposal)

Lake's link trace does not include the dynamic loader, so an executable
linked by a Nix `lean`/`leanc` records `/nix/store/...-glibc-*/lib/ld-linux-x86-64.so.2`
as its interpreter and stays "up to date" after that store path is
garbage-collected; it then fails with "No such file or directory". The same
applies to env scripts that hard-code store paths (such as
`/tmp/aiur-stage-lean-env.sh`). Every remedy below is optional; pick one.

**A. Official release toolchain (works today, nothing in the store).** The
official `lean-4.34.1-linux` release has the same githash as the pinned
`lean-toolchain` (`5045d0056413...`), bundles its own clang/sysroot, and links
against the system loader `/lib64/ld-linux-x86-64.so.2`:

```bash
export PATH=$PWD/target/terminal-complete/toolchain/lean-4.34.1-linux/bin:$PATH
export LIBCLANG_PATH=/usr/lib/llvm-21/lib   # bindgen, system LLVM
unset LEAN_PATH LEAN_SYSROOT
bash tools/check-aiur-compression-fixtures.sh
```

Executables already linked against a collected loader must be relinked:
move the binary out of `*/.lake/build/bin/` (keep `.hash`/`.trace`) and
`lake build` relinks only that step. To find them:

```bash
for f in Aiur/.lake/build/bin/* MultiStark/.lake/build/bin/* .lake/build/bin/*; do
  i=$(readelf -l "$f" 2>/dev/null | sed -n 's/.*interpreter: \(.*\)]/\1/p')
  [[ -n $i && ! -e $i ]] && echo "$f -> $i"
done
```

Cargo build scripts have the same problem: a `build-script-build` linked in
a Nix shell is never re-linked by cargo, and fails with "could not execute
process ... (never executed) / No such file or directory". Check
`target/release/build/*/build-script-build` and
`.lake/packages/Blake3/rust/target` with the same loop and move the dead
`build/<crate>-<hash>` directories (or the whole Blake3 `target/`) aside;
cargo rebuilds them.

**B. GC roots for the flake's dev shell.** Root the whole dev-shell closure
(Lean, clang, glibc, libclang) inside the worktree, so it survives
`nix-collect-garbage` until the link is deleted:

```bash
mkdir -p target/nix-gcroots
nix develop --profile target/nix-gcroots/dev .#default -c true
nix develop target/nix-gcroots/dev       # later: enter without re-evaluating
```

or root individual outputs:

```bash
nix build .#devShells.x86_64-linux.default --out-link target/nix-gcroots/devshell
nix-store --add-root target/nix-gcroots/glibc --realise \
  "$(nix eval --raw nixpkgs#glibc.outPath)"
```

`--add-root`/`--out-link` create indirect roots under
`/nix/var/nix/gcroots/auto`; they only protect against a GC that reads this
machine's `gcroots`. If the store is collected from elsewhere (a host
sharing its store with a VM), the roots must be created on that host, and
option A is the durable choice.

**C. Resolve store paths on every use instead of hard-coding them.** An env
script that asks Nix each time rebuilds or re-substitutes collected paths
instead of pointing at dead ones:

```bash
eval "$(nix print-dev-env .#default)"     # PATH, LIBCLANG_PATH, CC from the dev shell
```

`nix print-dev-env` is the least fragile form of C; combine it with B's
`--profile` to also keep the closure rooted.

**Memory caps for builds and tests.** A shared agent session on this machine
was OOM-killed (2026-11-15 05:31) by uncapped concurrent jobs. Run every
build or test inside a memory-capped systemd user scope, so an overrun kills
only that job:

```bash
target/light.sh [-m 40G] <cmd...>    # Lean/cargo builds, tests, fixture gate; no lock
target/heavy.sh [-m 160G] <cmd...>   # anything > 20 GB: serialised on target/heavy.lock
```

Both are `systemd-run --user --scope -p MemoryMax=<N> -p MemorySwapMax=0`;
`heavy.sh` wraps that in `flock target/heavy.lock`. They need the user
systemd bus, which a bubblewrap command sandbox blocks ("Failed to connect
to user scope bus"), so run them outside the sandbox. The fixture gate with
option A's environment:

```bash
target/light.sh -m 40G bash -c '. <env with option A exports> && bash tools/check-aiur-compression-fixtures.sh'
```

## 8. Single-process driver

Goal: `ix` runs the whole ladder in one process. Lean builds the circuits in
process and hands them to Rust over FFI. Rust proves each stage, and gnark is
linked in through the existing cgo archive (`ix_rs_net`, feature `plonk`).
The process-level pipelining of `run.sh` is replaced by threads.
Intermediate products go to disk only for the export cache, the setup
products, `--out` and resumption. The driver only orchestrates: every
circuit still comes from a Lean exporter, every key and digest is checked
exactly as `setup.sh`/`run.sh` check it, and no relation, parameter or
format changes. `target/e2e-l3/*.sh` stay until the driver reaches parity
(§8.8).

### 8.1 Ladder description (data, not code)

The stage list and the setup products are a JSON manifest,
`ix-aiur-ladder-v1`, so L4 and L5 are new manifests and not new code. The
CLI takes the manifest together with an independent BLAKE3 pin of its bytes
(the same pattern as `--aiur-chain`/`--aiur-chain-blake3`). Each stage has a
`kind`, one of four prover kinds that already exist, and the files that kind
reads, each with a digest:

| Stage kind | Products in the manifest (digest) | Checks at run time (from `run.sh`/the stage binary) |
|---|---|---|
| root | root key pin (`ROOT_PIN`, BLAKE3) | `compress_wrap::Input::from_bytes` against the pin |
| `wrap` | package `m16384w64.ixa`, layout `m16384w64-v3.layout.json` (BLAKE3 each) | wrapper key BLAKE3 = layout `key_blake3`; native verify |
| `compress-gl` | `compress-gl.ixa` (`a05f4ee7…`), `chain-fold.ixa`, `gl-rom.json` (SHA-256 `ddfb5104…`), parameters (`26 0`, lookup budget 4, quotient degree 4, 2 shards, streaming), pinned key file `gl-key.bin` (BLAKE3 `0b71c067…`) | wrap admission rejects a changed claim and layout; native verify; changed output rejected; key bytes equal the pinned file (`cmp`) |
| `narrow-fixed` | `narrow-fixed.ixa` (`efaf4ede…`), stage config, policy `l3-policy.bin` (`9b95e86b…`), pinned `narrow-key.bin` (`a955432e…`) | native verify, changed output rejected; key bytes equal the pinned file |
| `terminal-plonk` | `compress-final-narrow-l3.ixa` (`bd9a0dac…`), `terminal.ixscs` (SHA-256 `54a12ad1…`), prepared directory and its `manifest.json` (SHA-256 of every file) | prover refuses a changed statement; verifier rejects it; verifying key SHA-256 = the manifest's `verifying-key.bin` |

Environment-level inputs (`IX_KZG_SRS`, `IX_PARAMS_DIR`, CUDA SRS cache)
become manifest fields with the digests the stage code already checks. The
digest of each setup product is checked when the manifest is opened, before
any proving starts. A stage whose own code checks a digest again keeps that
check. L4 adds or changes stage entries in its own manifest (for example
`target/e2e-l4/ladder.json`). The driver never needs to know which ladder it
runs.

### 8.2 Code layout

- **Rust library.** New module `ix_proof_compression::aiur_backend::ladder`:
  - `manifest` (parse, pin and check);
  - one file per stage kind (`wrap`, `gl`, `narrow`, `terminal`);
  - `exports` (the export broker, §8.3);
  - `memory` (the budget, §8.5);
  - `report` (`summary.json`, `checks.json`).

  The stage logic that now lives in the bodies of
  `examples/{compress_gl_packed_chain,aiur_template_v2_init,aiur_narrow_terminal_prove}.rs`
  and `stark-verifier wrap-prove` moves into library functions with an
  explicit split: `prepare` (input-independent work: artifact, SRS, circuits,
  fixed-slot setup, keys) and `prove(prepared, input)`. The examples become
  thin wrappers over those functions, so their command lines and outputs
  stay the same. The scripts keep running the snapshots in `stage-bin`, so a
  rebuild changes nothing they measure.
- **FFI.** New file `crates/ffi/src/aiur_ladder.rs` with the `rs_ladder_*`
  externs.
- **Lean.**
  - `Ix/Cli/AiurLadder.lean`: the FFI declarations, the export runner and
    the cache.
  - `ix compress` gains `--aiur-ladder FILE --aiur-ladder-blake3 PIN`. A
    subcommand `ix compress aiur-ladder-run --root-dir DIR --out DIR` proves
    a raw root from files, the way `run.sh` does, which is what the parity
    bench compares.
- **Lean exporters.**
  - The bodies of `MultiStark/Examples/{WideExport,TilingExport2,PlonkExport}.lean`
    (and later `CompressNarrowFixed`, `CompressFinalNarrow` for setup) move
    into importable library modules (`MultiStark/MultiStark/Export/*.lean`,
    part of the `MultiStark` lean_lib).
  - Each module gets a function `exportTo (input : Json) (base : FilePath) (out : Paths) : IO Report`.
  - The `lean_exe` roots shrink to `def main := ….main`, so the same
    executables still exist and the scripts' snapshots are unaffected.
  - The move is needed because each `Examples/*.lean` defines a top-level
    `main`, so they cannot be imported together.
  - The exporter logic itself is unchanged.

### 8.3 FFI surface and ownership

Rust never calls into Lean. Lean pushes the exports to Rust, and Rust only
waits on them, so no Lean closure crosses threads.

```lean
opaque LadderPointed : NonemptyType            -- external object: Arc<rust LadderState>
structure ExportRequest where                  -- Rust → Lean
  id : UInt32; exporter : UInt8                -- 0 wide_export, 1 tiling_export2, 2 plonk_export
  input : ByteArray                            -- the exporter's input JSON, as Rust builds it today
  tables : Bool                                -- tiling_export2 with compact tables
structure ExportResult where                   -- Lean → Rust
  id : UInt32; layout : ByteArray              -- layout JSON (small)
  fixed : String; tables : Option String       -- paths of the cache entry's matrices (GBs; Rust mmaps)
  key : String; cached : Bool; seconds : Float
structure RootInput where vk claims proof : ByteArray
@[extern "rs_ladder_open"]     opaque Ladder.open (manifest : @& ByteArray) (pin : @& String) : IO Ladder
@[extern "rs_ladder_requests"] opaque Ladder.requests (l : @& Ladder) : IO (Array ExportRequest)
@[extern "rs_ladder_provide"]  opaque Ladder.provide (l : @& Ladder) (r : @& ExportResult) : IO Unit
@[extern "rs_ladder_fail"]     opaque Ladder.fail (l : @& Ladder) (id : UInt32) (err : @& String) : IO Unit
@[extern "rs_ladder_run"]      opaque Ladder.run (l : @& Ladder) (root : @& RootInput) (out : @& String)
                                 (opts : @& RunOptions) : IO RunReport   -- final proof, Solidity proof, summary/checks JSON
```

**Call sequence.**

1. `open` checks the manifest pin and every product digest. It builds the
   exporter inputs, which depend only on artifacts, configuration and
   pinned ROM heights. That is already true today: the GL export runs
   before the wrap proof is awaited, and the narrow export runs beside
   execution.
2. `requests` returns those inputs.
3. Lean starts one dedicated `IO.asTask` per request. Each task looks up
   the cache (§8.6), runs the exporter in process on a miss, and then calls
   `provide` (or `fail`).
4. Meanwhile the main Lean thread calls `run`, which blocks in Rust until
   the ladder ends. A stage that needs export `id` waits on a
   condition-variable slot. A `fail` there, or a missing result, aborts the
   run with the exporter's error.

**Ownership rules.**

- Every Lean argument is borrowed (`@&`) and copied or mmapped into
  Rust-owned data before the extern returns. No Rust thread holds a Lean
  object.
- The multi-GB fixed matrices never pass through the Lean heap. The
  exporter writes them into the cache entry, and Rust maps the files.
- `Ladder` is a Lean external object. Its finalizer drops the resident Rust
  state.
- Panics are caught at the boundary (`catch_unwind`) and become `IO.userError`.

**Resident in `LadderState`.** For the lifetime of the handle it holds the
manifest, artifacts, pinned keys and policies (all small), and one shared
host KZG SRS (with the CUDA SRS cache when enabled). Today GL and narrow
each load the SRS, 3.5 s and 4.1 s. Large prepared state (the narrow
fixed-slot system and the PLONK proving key) is resident only from its
`prepare` until its stage ends (§8.5). `--keep-prepared` keeps it across
runs of a long-lived process when the budget allows.

### 8.4 Threads and overlap

The schedule reproduces `PIPELINE=1` with threads. The edges are the same
`done` edges `run.sh` enforces:

```
t0  wrap.prove ─────────────┐                      (main lane)
t0  gl.prepare ─────────────┤ (artifact, wrapper package, wide export, SRS)
wrap done ──► gl.prove: execution (1 thread, ~33 s) → trace (85 GB) → PCS
              narrow.prepare (export replay, circuits, fixed-slot setup ≤104 GB → ~60 GB resident)
              plonk.prepare  (prepared SCS check, raw proving key load)
gl done + key == pin ──► narrow.prove ──► key == pin ──► terminal + PLONK.prove
```

- **Two rayon pools.** Today two processes run at once, each with its own
  full-width rayon pool. Here the prove lane and the prepare lane each get a
  full-width `rayon::ThreadPool`, and each stage runs in its pool's
  `install`. Parallelism is not capped. A `prepare` that overlaps a
  single-threaded phase gets the whole machine, as it does now.
- **Gates replace the `done` files.**
  - `gl.prove` waits for the wrap output (passed in memory).
  - `narrow.prove` waits for the GL proof, its key check and the end of
    `narrow.prepare`.
  - `terminal.prove` waits for the narrow proof and its key check.
- **Shared state.** The root is decoded once. The wrapper is built once:
  today both the wrap stage and the GL stage build it for the layout. The
  SRS is loaded once.
- **GPU.**
  - All lanes share one CUDA context.
  - Phase 2 audits `libmulti_stark_cuda`, `ix_bn254_cuda` and the gnark CUDA
    backend for process-global state: the device SRS cache, pools, static
    streams.
  - Until the audit clears them, GPU sections take a process-wide GPU mutex.
    Today the processes overlapped mostly CPU work against GPU work, so the
    mutex is expected to cost little. Phase 3 measures it.
  - Every stage ends with `Compression.releaseGpuMemory`'s Rust counterpart.

### 8.5 Memory budget

Measured peaks (bench, median RSS):

| Stage | Peak RSS | Peak GPU |
|---|---:|---:|
| wrap | 11.5 GB | 55.7 GB |
| CompressGL (trace phase) | 85 GB | 39 GB |
| narrow, prepare (fixed-slot interpolation, transient) | about 104 GB | |
| narrow, prepared and resident | about 60 GB | |
| narrow, prove (`run.sh` comments put it at up to about 105 GB) | 94 GB | 42.6 GB |
| terminal + PLONK | 43.5 GB | 38.9 GB |
| PLONK key while it waits | 8 GB | |

The whole pipelined run peaked at about 155 GB (`BENCH_MEM=180G`), and the
total GPU peak was 55.7 GB of 96 GB.

`memory::Budget` is a counting semaphore over a configured total, by
default `--memory` or else the cgroup's `memory.max` minus 10%. Each phase
reserves its manifest-declared estimate before it allocates and releases it
when its state drops. The estimates are data in the stage entry, measured
per ladder.

| Window | Live | Sum |
|---|---|---:|
| wrap | wrap 12 + gl.prepare | < 25 GB |
| GL execution | GL exec + narrow.prepare ≤104 (falls to 60) + PLONK key 8 | ≤ about 125 GB |
| GL trace/PCS | GL 85 + narrow prepared 60 + PLONK key 8 | about 153 GB |
| narrow prove | narrow ≤105 + PLONK key 8 | ≤ about 113 GB |
| terminal | PLONK 43.5 | about 44 GB |

**Invariants.**

1. **The GL and narrow prove peaks never coexist.** `gl.prove` consumes its
   prepared state by value. The driver drops the GL traces, system and
   prover state, keeping only the proof (213 KB) and key bytes, before
   `narrow.prove` reserves its peak.
2. **The narrow setup's transient is gated.** The GL trace phase reserves
   85 GB, and it cannot be granted while `narrow.prepare` holds its
   104 GB transient. Within budget it finishes inside GL's 33 s
   single-threaded execution, as today. If it does not, GL's trace phase
   waits instead of the process being OOM-killed. `run.sh` only guarded
   this with `need_gb 170` at the start.
3. **Freed memory goes back to the OS.** After each stage drop the driver
   calls `mi_collect(true)` (`ix-ffi` uses mimalloc) and records RSS in
   the summary. The multi-GB buffers are mmapped anyway, so they return to
   the OS on free. Phase 3 checks that RSS between stages matches this
   table.
4. **The cap covers the whole process.** The bench runs `ix` under
   `heavy.sh -m 180G` exactly as it runs `run.sh` now, and that cap now
   covers Lean, Rust and Go together.

### 8.6 Disk: export cache, setup products, outputs

Layout (root: manifest `cache` field, default `$L3_ARTIFACTS/ladder-cache`;
it is separate from `export-cache`/`wide-cache`, because
`tiling-export-cached.sh` keeps only its newest entry and would evict the
driver's):

```
ladder-cache/
  exports/{wide,tiling2,plonk-scs}/<key>/  input.json layout.json fixed.bin [tables.bin|terminal.ixscs(.sha256)] export.log complete
  commit/                                  fixed-commitment cache (today's --fixed-commit-cache format)
  plonk/<vk-sha256>/proving-key.raw        written on first load (today's raw-key rule)
```

**Cache keys.** The keys have the same components the wrappers use now:
the exporter's identity, the digest of the exact input bytes, and the mode
(`tables=1`). The encoding is one domain-separated form for all three
caches, in place of today's three ad hoc ones:
`BLAKE3("ix/aiur-ladder-export/v1\0" ‖ kind ‖ exporter_id ‖ BLAKE3(input) ‖ mode)`.

**`exporter_id`.** In process there is no exporter binary to hash.
`exporter_id` is the Lake trace hash of the exporter's library module,
which covers its whole source closure and the toolchain. The `ix` build
writes it next to the executable. If that file is missing, the SHA-256 of
`/proc/self/exe` is used, with a warning.

**Why a stale entry is harmless.** A replayed export is validated exactly
like a fresh one. A wrong export changes a key, and the key pins
(wrapper key, `gl-key.bin`, `narrow-key.bin`, SCS SHA-256) reject it. So the
cache affects time only, never what is accepted.

**First run.** The first driver run misses once (the existing caches
belong to other exporter binaries) and fills the cache. Warm runs then
replay.

**Writes.** Entries are written to `.tmp-<pid>-<nanos>` and renamed into
place, with `complete` written last. Stale `.tmp-*` directories of dead
PIDs are swept on open.

**Run outputs** (`--out DIR`):
- `proof.bin` and `proof.solidity.bin`;
- `summary.json`, with the same fields `summarize.py` reads, so
  `bench_summarize.py` works unchanged, plus RSS between stages;
- `checks.json`, with the same eight keys and the same meaning as
  `run.sh`'s;
- `stages/<i>-<kind>/{proof,claims,key}.bin`, the stage outputs. They are
  small: wrap 3.4 MB, GL 213 KB, narrow 3.9 KB. Each directory has a `done`
  record that holds the manifest pin, the stage index and the BLAKE3 of the
  stage input.

The outputs are passed to the next stage in memory. They are written to
disk only for resumption and inspection, off the critical path, by a writer
thread.

### 8.7 Errors and resumption

**First error wins.** The first error sets a cancellation flag.
- Prepare lanes check it between phases.
- Lean export tasks are left to finish or are abandoned. Their staging
  directories are never published.
- `run` joins every Rust thread, writes `summary.json` with
  `status: "failed"`, the stage, the phase and the message, and returns
  `IO.userError`.

A failed key comparison or check is an error of its stage. Exactly as in
`run.sh`, nothing after it runs.

**`--resume`** skips stage `i` only when all of these hold:
- `stages/i/done` names the same manifest pin and input digest;
- its proof verifies natively again against the pinned key;
- the changed-output rejection check passes again. These checks take
  milliseconds.

Otherwise the stage and everything after it rerun. Resumption never skips
a check, only proving.

`--fresh` deletes `stages/`.

### 8.8 Parity, bench and retirement

**Determinism.**
- The wrap, GL and narrow proofs are Fiat–Shamir transcripts without
  blinding. The three bench runs produced the same GL proof BLAKE3
  (`799c026c…`).
- gnark's PLONK prover blinds with fresh randomness
  (`backend/plonk/bn254/prove.go`, `initBlindingPolynomials`), so even two
  `run.sh` runs produce different final proof bytes.

**Parity criterion**, on the same root (`init-raw-root`):
1. byte-identical wrap, GL and narrow proofs and keys. Phase 3 first checks
   that `run.sh` itself reproduces them across two runs;
2. the same terminal statement (the eighteen output words) and the same
   PLONK verifying key SHA-256 (`30dd3ee8…`);
3. the final proof verifies natively and in the Solidity verifier, with gas
   285,614 (`gas.sh`);
4. every `checks.json` entry is true.

**Bench.** The bench has the same discipline as `bench.sh`: an idle
machine, `heavy.sh` per run, N = 3, and medians against the 167.2 s
baseline (wrap 11.6, GL 77.2, narrow 54.7, PLONK 23.8 exposed). It runs
through `bench.sh`'s `RUN=` hook with a two-line `run-ladder.sh` that
calls `ix compress aiur-ladder-run`.

**Retirement.** At parity, Phase 3 proposes, and does not execute,
removing:
- `run.sh`, `bench.sh`'s binary snapshots, `stage-bin` and
  `{tiling,plonk}-export-cached.sh`;
- the examples' `--wait-for` modes.

`setup.sh` is retired later, once the in-process setup (`aiur-ladder-setup`:
the narrow and terminal exports, policies, the PLONK preparation) exists.

### 8.9 Risks that Phase 2 must settle

- **One build replaces three.** `stage-bin` holds three different
  `libmulti_stark_cuda.so` builds (wrap/GL from build `becb7b95…`, narrow
  from `95f50b80…`), and one process loads only one. The key pins detect any
  behavioural difference. Phase 2 builds the stage examples and `ix` from
  one tree and compares all keys before benchmarking.
- **mimalloc versus the system allocator.** `ix-ffi` sets mimalloc as the
  global allocator, and the stage examples use the system allocator.
  Timings may move either way.
- **CUDA thread safety** (§8.4). The GPU mutex is the fallback.
- **Go runtime in process.** gnark's heap (about 40 GB) and
  `GOMAXPROCS`/GC share the process with Rust. The PLONK stage runs last,
  so only the 8 GB key overlaps other stages.
- **Ownership of the moved exporter bodies.** `CompressNarrowFixed.lean`
  and `CompressGL.lean` belong to the L4 work and are not touched. Only the
  exporter wrappers in `MultiStark/Examples` move.

### 8.10 Implementation (2026-11-16)

What exists, and where it departs from the design above:

- **Rust.** `ix_proof_compression::aiur_backend::ladder`:
  - `ladder.rs`: manifest, products, budget, GPU lock, stage threads,
    `checks.json` and `ladder.json`;
  - `ladder/exports.rs`: export cache, binary runner and request broker;
  - `ladder/{wrap,gl,narrow,terminal}.rs`: the four stage kinds, which follow
    the L3 paths of `stark-verifier wrap-prove`, `compress_gl_packed_chain
    --gl-only`, `aiur_template_v2_init --fixed-key ... --save` and
    `aiur_narrow_terminal_prove --reuse --scs`.

  `stark_verifier::compress_wrap::WideExporter` lets the wrapper take its
  `wide_export` circuits from the ladder's cache (`Wrapper::for_layout_with`).
  `template::v2::lean::Layout::load_export` reads a stored `tiling_export2`
  export.

  The examples still hold their own copies of the stage logic and were not
  turned into wrappers. The scripts run setup.sh's snapshot binaries, so this
  changes nothing they run. Folding the examples onto the library is
  follow-up work.
- **FFI.** `crates/ffi/src/aiur_ladder.rs` provides `rs_ladder_open`,
  `rs_ladder_next_export`, `rs_ladder_complete_export` and `rs_ladder_run`.
  Options, requests and the summary cross the boundary as JSON strings and
  tab-separated strings, not structures.
- **Lean.**
  - `Ix/Cli/AiurLadder.lean` adds `ix compress aiur-ladder-run --ladder
    FILE --ladder-blake3 PIN --root-dir DIR --out DIR [--memory-gb N]
    [--cache DIR] [--no-gpu-lock]`.
  - The exporter bodies moved to `MultiStark/MultiStark/Export/{WideExport,TilingExport2}.lean`.
    The `lean_exe`s are now one-line wrappers.
  - The file is not a `module`, because the exporters are not, so `Main`
    adds the subcommand to `compress`.
- **Rust example.** `examples/aiur_ladder.rs` runs the same ladder with the
  exporters as executables. `aiur_ladder digest FILE...` prints the digests
  a manifest pins.
- **Exporter identity.** In `ix` each exporter's identity is the Lake trace
  hash (`depHash`) of its module (`MultiStark.Export.WideExport`,
  `MultiStark.Export.TilingExport2`). `Ix/Cli/AiurLadder.lean` reads it from
  the module's `.trace` file when it is compiled (`lake_dep_hash%`); the
  hash covers the module's source, its transitive imports and the
  toolchain, and the file is recompiled whenever it changes. The cache key
  uses `BLAKE3("ix/aiur-ladder-exporter/lake-trace/v1\0" ‖ kind ‖ 0 ‖ depHash)`
  per kind, so an `ix` rebuild that leaves an exporter unchanged keeps its
  cached exports (before, every rebuild re-exported, about 45 s). A build
  without Lake traces falls back to the BLAKE3 of the `ix` executable and
  says so on stderr. As before, a stale entry costs time only: a wrong
  export changes a pinned key.
- **Rayon.** Each stage runs in its own rayon pool, as wide as the global
  pool (`RAYON_NUM_THREADS` or every logical CPU), whose threads are named
  `ladder-<stage>-<i>`. In one shared pool a thread blocked in `join` steals
  other stages' tasks; separate pools leave core sharing to the kernel, as
  the separate processes of `run.sh` did. In the warm runs of §8.11 no
  other stage computed during CompressGL's parallel phases, so this changed
  no time there; it makes the per-stage CPU profile readable by thread name.
- **Not implemented.**
  - `--resume`, and stage outputs as resumable checkpoints. The outputs are
    written in `run.sh`'s layout, but nothing reads them back.
  - In-process setup (`setup.sh` steps).
  - Storing the result in the `ix` store, which `ix compress ADDR` does.
  - A shared SRS between GL and narrow. Each still loads its own, as the
    separate processes did.
- **Runs.** `target/ladder/run-ladder.sh RUN_DIR` makes one run (`DRIVER=ix`
  by default, `DRIVER=example` for the example). It writes `run.sh`'s run
  directory, so `summarize.py`, `gas.sh` and `bench.sh` (with `RUN=`) work
  unchanged. `target/ladder/l3.json` is the L3 manifest (pin
  `51f544c0…ee7f`), and `target/ladder/make-manifest.py` writes one for any
  e2e setup directory.

**Parity (L3, root `init-raw-root`).** Two `run.sh` runs (`target/ladder/repro-{1,2}`)
reproduce byte for byte:
- the wrap key and proof (SHA-256 `77df6b9f…`, `c5c74268…`);
- the GL key and proof (`337dee38…`, `f352609b…`);
- the narrow key and proof (`e1cfb51a…`, `05a17fdf…`).

The final PLONK proof differs from run to run (gnark blinds).

The driver in `ix` produced exactly those bytes in three runs
(`target/ladder/ix-{1,2,3}`). It also produced:
- the same narrow claims and `narrow.json`;
- the same PLONK public inputs and witness;
- verifying key `30dd3ee8…`;
- all eight `checks.json` entries true;
- gas 285,614 (`gas.sh target/ladder/ix-1`).

**GPU lock.** In those runs no stage ever waited for the lock: the GPU
sections did not overlap. Its cost is the overlap it forbids, and that
overlap did not occur in these runs.


**L4 through the same driver.** `make-manifest.py L4 target/e2e-l4` wrote
`target/ladder/l4.json` (pin `777f37a9…bd7e`) from the L4 setup products.
`ix compress aiur-ladder-run` ran it with no code change
(`target/ladder/l4-1`):
- every check passed;
- the GL and narrow keys equal the L4 pins;
- the GL and narrow proofs are byte-identical to L4's `run.sh` run
  (`target/e2e-l4/run`: `65f7af82…`, `644e89cf…`);
- the PLONK public inputs and verifying key (`1eba2313…`) are the same.

**Bench (L3).** The bench used the discipline of `bench.sh`: an idle
machine, `heavy.sh` per run, the `ixbench.slice` CPU weight and N = 3, run
through `RUN=target/ladder/run-ladder.sh`. The record is now
`before.earlier_record` in `docs/measurements/aiur-compression-l3-ladder.json`
(§8.11). Warm runs, one `ix`
process each, the GPU lock enabled:

| Stage (exposed) | `run.sh` (2026-11-16) | driver |
|---|---:|---:|
| wrap | 11.6 s | 10.2 s [10.0–11.0] |
| CompressGL | 77.2 s | 79.5 s [78.4–83.5] |
| narrow | 54.7 s | 54.8 s [54.5–55.2] |
| terminal + PLONK | 23.8 s | 23.8 s [23.7–24.0] |
| **end to end** | **167.2 s** [167.2–167.2] | **167.6 s** [167.1–173.7] |

In all three runs the wrap, GL and narrow keys and proofs were the pinned
bytes, and every check passed. Peak RSS of the whole process was 146 GB.
No stage ever waited for the GPU lock or for the memory budget.

Inside CompressGL, execution is faster (30.4 s against 32.6 s) and trace
generation slower (13.0 s against 9.5 s). Generating the trace while the
narrow stage prepares in the same process is the likely cause of the
slowdown. The median is 0.4 s above `run.sh`'s, which is inside the spread
of these runs, but it does not meet "≤ 167.2 s" strictly.

**Retirement (proposal, not done).** The driver now gives the same proofs
and keys and checks the same things, and its time is within the noise of
`run.sh`'s. That makes these candidates for removal:
- `target/e2e-l3/run.sh`, and in `bench.sh` the defaults that copy and run
  the stage snapshots;
- `tiling-export-cached.sh`, which the ladder cache replaces;
- `stage-bin`;
- the `--wait-for` modes of the four stage examples.

`setup.sh` and `plonk-export-cached.sh` stay until setup runs in process.
One prerequisite comes first: fold the examples onto the
library. (The other, keying the exporter identity by the Lake trace hash so
that an `ix` rebuild does not re-export, is done; §8.10.)

### 8.11 Mathlib, and the warm Init profile (2026-11-17)

**Mathlib through L3.** The Mathlib aggregate root
`e9ade9ab…ea42` (IxVM artifact `5111b234…`, aggregation artifact
`7d687ca0…`, 63 shards, 684,697 constants) was exported raw as Init's was:
`export_root expected target/mathlib-root/mathlib.ixe
target/mathlib-root/mathlib-final.ixes` (Ix claim `741234e5…`), then
`export_root extract` of the stored proof, which checks the claim and
verifies the proof (one trace shard). `export_root` was built from the
sources of the tree that proved the root, since its final partition carries
the measured-records section this tree's `ixon` does not parse. Its root key
is `55f0b8b0…8e86`, the key the L3 manifest pins, so the ladder ran
unchanged (`target/mathlib-compress/raw-root`, runs in
`target/mathlib-compress/`). Every check passed; the wrap, GL and narrow
keys are the pinned ones and their proofs repeat byte for byte across two
runs; the PLONK proof verifies natively and in the Solidity verifier (gas
285,614), under verifying key `30dd3ee8…`. The record is
`docs/measurements/aiur-compression-mathlib-l3-ladder.json`.

| Stage (exposed) | Init (§8.10 bench) | Mathlib, warm |
|---|---:|---:|
| wrap | 10.2 s | 10.2 s |
| CompressGL | 79.5 s | 79.2 s |
| narrow | 54.8 s | 54.9 s |
| terminal + PLONK | 23.8 s | 23.8 s |
| **end to end** | **167.6 s** | **168.1 s** |

Peak RSS was 146 GB for both. The wrap normalizes every root to the same
geometry, so only the wrap's witness depends on the root, and the times
match. A first Mathlib run took 195.4 s: the PLONK proving key was not in
the page cache (other jobs had evicted it), its 37 s load held the GPU lock,
the narrow stage's fixed commitment waited for the lock and kept its
preparation memory, and CompressGL's trace phase waited 27.7 s for the
memory budget.

**Profile.** `target/ladder/prof/sample.py` samples the `ix` process's
threads every 0.5 s (`SAMPLE=1` with `prof/run-ladder.sampled.sh`), and
`prof/windows.py` sums CPU per phase. Two single-threaded stretches stood
out on the critical path:

- the narrow stage's SHPLONK opening spent 25.7 s on one core combining
  the packs of each column (`scatter_group_quotient`): its groups have few,
  2^25-row columns, and the combination ran on one thread per column;
- CompressGL's trace phase ended with 4 s on one core: sharding shrank the
  first piece of each multi-copy trace in place (`shrink_to_fit`), which
  mimalloc, `ix`'s allocator, does by copying on one thread; the
  stand-alone examples use glibc, which remaps (9.5 s against 13.0 s in
  §8.10).

**Changes.** None changes a proof, key or check: the wrap, GL and narrow
keys and proofs are the pinned bytes in every run below, and the PLONK
public inputs and verifying key are unchanged.

1. `kzg::shplonk::scatter_group_quotient` combines a column's packs in row
   blocks of 2^14 in parallel. Narrow proving: 48.6 s → 25.9 s (SHPLONK
   quotients 25.7 s → 3.8 s); the GL opening's quotients stay at 4.0 s.
2. `compress_bn::packed::shard` copies the first piece out in parallel
   instead of shrinking it in place, and the wide stage's map-column
   projection (`wide::Stage::traces`) runs row-parallel. CompressGL trace:
   13.0 s → 10.1 s.
3. The terminal reads the files gnark's open loads (`circuit.bin`,
   `verifying-key.bin`, `proving-key.raw`, 5.3 GB) before it takes the GPU
   lock. Warm this costs nothing measurable. With those files evicted from
   the page cache (`prof/evict.py`, `prof/series-cold.sh`): the old binary
   took 189.5 s (narrow waited 31.7 s for the lock, CompressGL 20.3 s for
   memory), the new one 148.5 s (its terminal waits for the lock instead,
   off the critical path, and the narrow stage 4.6 s).
4. Per-stage rayon pools and the Lake-trace exporter identity (§8.10).

**Bench (Init, L3, warm).** Same discipline as §8.10 (idle machine,
`heavy.sh`, `ixbench.slice`), `RUN=target/ladder/prof/run-ladder.sampled.sh`.
Before: the previous `ix` in the same session, two runs; after: three runs
(`docs/measurements/aiur-compression-l3-ladder.json`).

| Stage (exposed, mean) | before | after |
|---|---:|---:|
| wrap | 10.0 s | 10.0 s |
| CompressGL | 79.8 s | 77.1 s |
| narrow | 55.8 s | 33.2 s |
| terminal + PLONK | 24.7 s | 23.2 s |
| **end to end** | **170.4 s** [168.3–172.5] | **143.5 s** [143.0–143.9] |

Peak RSS stays 146 GB. What remains on the critical path is mostly
CompressGL's single-threaded execution (30 s), CompressGL's GPU-bound
commitments and openings (35 s), the narrow stage's GPU work and its
mostly single-threaded witness (4.8 s), and gnark (23 s).
