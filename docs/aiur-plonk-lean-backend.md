# Verified Aiur → gnark PLONK backend in Lean

Status: design, sizing and first implementation round, 2026-11-15. This is
migration step 1 of `aiur-verification-surface.md` §3. It removes
`tools/gnark/aiur_plonk{,_lower,_lookup,_blake3,_counts}.go` and
`crates/proof-compression/src/aiur_backend/plonk.rs` from the trust base.
gnark (PLONK prover, verifier and Solidity verifier) stays the endpoint.
Lean builds the constraint system, and Go only loads it.

Gate counts in §6 come from a constraint-count model of the Go backend. The
model reproduces the Go census exactly: 181 of 181 chips, 28,107,619 in total.

## 1. Where trust begins: gnark's sparse R1CS

gnark compiles a PLONK circuit to a `constraint.SparseR1CS` (from
`gnark@v0.16.5-0.20261015185324-262cf453c107`, `constraint/r1cs_sparse.go`,
`frontend/cs/scs`, `backend/plonk/bn254/setup.go`). Its parts:

- **Wires.** Wires `0 .. P−1` are public, followed by the secret wires and then
  the internal wires. The verifier sees only the public values.
- **Gates.** Each constraint is one `SparseR1C`:
  `qL·w[a] + qR·w[b] + qO·w[c] + qM·w[a]·w[b] + qC = 0`, with arbitrary
  coefficients in Fr. Width is 3. There are no custom gates. The selector
  polynomials are `ql, qr, qm, qo, qk, qcp`: `qk` carries the public inputs
  and `qcp` carries the BSB22 commitment.
- **Copy constraints.** These are the permutation argument: every occurrence
  of a wire id in some gate's `a`, `b` or `c` slot carries the same value.
  Copies cost nothing beyond the gate slots that hold them.
- **One BSB22 commitment.** `Commit(v…)` adds one row `−v + Pi = 0` for each
  distinct committed wire. It also adds one output row, whose wire holds
  `γ = H(commit(Pi))`, computed by the prover and recomputed by the verifier.
  Committing costs one constraint per distinct committed wire.

The Lean model (`Aiur/Aiur/Plonk/Scs.lean`):

```lean
structure Gate (F) where a b c : Nat; qL qR qO qM qC : F
def Gate.Holds (w : Nat → F) (g : Gate F) : Prop :=
  g.qL * w g.a + g.qR * w g.b + g.qO * w g.c + g.qM * (w g.a * w g.b) + g.qC = 0
structure Scs (F) where
  wires publics : Nat; committed : List Nat; gamma : Nat; gates : List (Gate F)
def Scs.Satisfied (S) (w) (pub : List F) (H : List F → F) : Prop :=
  (∀ i (h : i < pub.length), i < S.publics → w i = pub[i]) ∧
  w S.gamma = H (S.committed.map w) ∧ ∀ g ∈ S.gates, g.Holds w
```

The crypto layer owns two things: that a valid gnark proof implies
`Scs.Satisfied` for some `w`, and that `H` behaves as a random oracle on a
binding commitment (Fiat–Shamir). Everything above that layer is Lean.

**What Go can express.** The frontend's `AddPlonkConstraint(a, b, o, sL,
sR, sO, sM, qC)` takes integer selectors. Coefficients ride on the operand
terms (`Mul(x, α)` is free). The exported gate is therefore
`sL·α·a + sR·β·b + sO·ω·c + sM·α·β·a·b + qC` with `sX ∈ {0,1}` and `qC` a
small integer (`Scs.GGate`, whose `toGate` is its meaning). Every gate whose
`qM·qC = qL·qR` whenever all four are nonzero can be scaled into this form.
Lean does the scaling, so the loader does no arithmetic. Products
`(αx+k)(βy+l)` always qualify. A gate that does not qualify is split by the
lowering, and the checker rejects any gate that is not in `GGate` form.

## 2. The backend pass

```text
Aiur circuits (Bridge.lower chips, tableCircuit, ROM; capacities)
  ──Plonk.lower (untrusted)──▶  certificate: per-circuit gate templates + global pool
  ──Plonk.check (trusted, decidable)──▶  emit ──▶ Scs (+ GGate export, wire map)
```

This has the Tiling shape: an untrusted lowering, a small decidable
checker, and a generated constraint system.

**Source.** `Plonk.Table` is a `Tiling.Circuit` with a capacity `rows` and
a fixed matrix. Its variables are main (current), main (next), fixed and the
selectors `first/last/transition`. A `Bridge.lower` chip is the special case
with no next, fixed or selector reads. Fixed tables (`tableCircuit`) read fixed
columns. ROM circuits read the next row. In the Stacked form of
`PeriodicStacked` the ROM has fixed addresses instead, so its counter row and
its next-row reads go away. Capacities are powers of two
(`aiur-verification-surface.md` §4.1), and every map receiver is kept.

**Slots, copy wiring, lanes.** A *uniform* circuit is one with no fixed or
selector reads, which covers every chip of the terminal. It is lowered once,
to a template: slots (`column c`, `column W+c` for the next row, and `sum`
slots) and gate rows. Each gate row is a single lane of `Tiling.Shape`,
`qm·x0·x1 + q0·x0 + q1·x1 + q2·x2 + qc`, with `c3 = none`. That lane is
exactly a gnark gate.

`emit` instantiates the template for every row `r < rows`:

- column slots go to the cell wires `(t, r, c)` and `(t, (r+1) % rows, c)`;
- sum slots go to fresh internal wires.

The Tiling copy bus is not needed here: a wire id that appears in several
gates *is* the copy class, and gnark's permutation enforces it. The labels and
multiplicities of `Copy.lean` and the `copy_class` lemma have no
counterpart, because the permutation argument is crypto-layer trust.

Fixed tables and ROM rows depend on the row, so their templates are per row.
They have no constraints, or a few (ROM: 5), so per-row checking is cheap.

**Global pool.** The challenge wires are a small global template over the
pseudo-columns `γ` and `β`:

- the powers `P_e = γ^e`, a chain of `max length` gates;
- `β = B(γ)`, the in-circuit expansion;
- shared fingerprint bases `β + n·P_n + Σ k_e·P_e`.

Row templates refer to pool slots as columns.

**Lookups, as today.** The encoding stays that of `aiur_plonk_lookup.go`, so
counts and gas are comparable:

- `fp(t) = β + n·γ^n + Σ t_i·γ^{e(i)}`, with `e` the rotation that gives
  index 2 exponent 0;
- `γ` is the BSB22 output, and `β` is `γ` expanded by BLAKE3 (64 bytes reduced
  in Fr, domain `ix/aiur-plonk/logup/v1`);
- signed multiplicities.

The changes, all inside the lowering:

1. **q-form.** Per message, one gate `q·d − m = 0` and one running-sum
   gate. This replaces `inverse·d = 1` plus the grouped partial sum, the
   count product and the add. When `d = 0` (probability at most `N/|F|`
   given binding) `q` is free, so the bad event moves into the
   challenge-soundness bound (§3).
2. **Commit only message cells.** Commit only the cells that some lookup
   argument or multiplicity depends on, together with the public and output
   wires. The challenge must bind the message multiset only. Cells outside
   every message cannot change the LogUp sum after the challenge, and the
   constraints are checked for the final witness.
3. **Fixed rows in one gate.** A fixed-table message is
   `d = U + k_x·P_x + k_0`, where `U` is the shared pool slot of the
   remaining constants and `k_0` (exponent 0) rides on `qC`.

**Statement binding.** Public wires 0 and 1 are the two statement limbs. The
root message `[1, callable, public…, outputs…]` enters the LogUp sum with
multiplicity +1, as in `Define`. The 18 private output wires are handed to
gnark's `PairingCheck` (D-trusted std gadget), exactly as
`aiur_plonk_pairing.go` does today. The Lean SCS exports their wire ids, and
the loader binds them.

## 3. Theorems

Let `S = emit cert`, `ok : Plonk.check src cert = true`, and
`sat : S.Satisfied w pub H`. Let `main t r c := w (cell t r c)`. Write
`γ = w S.gamma` and `β = w S.beta`.

```lean
theorem Plonk.rows_hold (ok) (sat) :
    ∀ t ∈ src.tables, ∀ r < t.rows, t.Holds (main t) r
theorem Plonk.logup (ok) (sat) :
    (∀ j, q j * fp γ β (tuple j) = mult j) ∧ Σ j, q j = 0 ∧ β = B γ
```

`rows_hold` is `Template.Checked.constraints_hold`. It runs the same
descending (definitions) and ascending (meaning) inductions over slots, for a
template whose gate rows are one-lane rows. `meaning_val` and
`subst_meaning` carry over unchanged. The message half replaces
`checkMessage`: the `d` slot's meaning, with pool slots substituted, is the
`Poly` of `fp` over the arguments' meanings. That is decided by `Poly.norm`.

**Lookup balance.** `logup` is deterministic. Turning it into
`ledger = 0` splits in two:

- **Lean, proved:** `fingerprint_injective`. The length-tagged power
  encoding is injective on tuples as polynomials in `γ`, the same pattern as
  `trimZeros_inj_of_length` in `Trim.lean`. Also proved in Lean: if the
  ledger is nonzero, then `R(β, γ) = Σ m_t/(β+fp_γ(t))` is a nonzero rational
  function with numerator degree below `N·L`. So the challenge pairs where it
  vanishes, or where some `fp = 0`, number at most `N·(L+1)·|F|` (Schwartz–Zippel).
- **Crypto layer:** `(γ, β)` is uniform and independent of the committed
  values, for a binding BSB22 commitment and `H` and `B` modelled as random
  oracles. Message values are committed cells (§2 item 2), and `β = B γ` is
  forced by gates proved functional. Hence `Pr[logup ∧ ledger ≠ 0] ≤
  N(L+1)/|F| + ε_FS`.

`B` must be a function of `γ`, which the Lean check of the expansion gates
establishes. That `B` is BLAKE3 is a separate lemma, testable now and
provable later against the pure-Lean `Blake3` package. It is not needed for
soundness beyond the random-oracle model.

**Composition.** With the ledger balanced and every row holding, the
terminal's chips satisfy exactly the hypotheses of `Bridge.Wide.checkMemo`
(rows of `Bridge.lower` chips whose ledger balances against the root plus
fixed tables and ROM). `Wide.checkMemo`, `Grouping.Plan.checkMemo` and
`Optimized/EndToEnd` then give the terminal's `EvalFn` statement, as in
`narrow_heap_sound`. The terminal program's own correctness (step 5) and
the narrow stage (`Periodic.narrow_heap_sound_stacked`) sit beside it. The
remaining hypotheses are `characteristic`, `SmallCast` and the size bounds,
which are decidable once `bound` is fixed.

## 4. Exporter and loader

The exporter (Lean exe `plonk_export`) writes `ix-aiur-scs-v1`, a
little-endian binary file:

- header: publics, outputs[18], wires, gates, commit count, γ wire;
- coefficient table (canonical 32-byte Fr);
- gates: `a b c : u32`, `sel : u8`, `α β ω : u32` (coefficient ids),
  `qC : i8`;
- the commit wire list;
- the pre-commitment and post-commitment gate split;
- for each internal wire, its defining gate.

The file's SHA-256 is pinned in the manifest beside the schema hash.

The Go loader (≈200 lines) has these duties:

- **Read.** Read and hash-check the file.
- **Wires.** Allocate the publics, secrets (cells) and outputs. Create
  internal wires as hints (`solveGate`, prover-only).
- **Gates.** For each gate, call `AddPlonkConstraint(Mul(a,α), Mul(b,β),
  Mul(c,ω), sL, sR, sO, sM, qC)`.
- **Commitment.** Call `multicommit.WithCommitment(committed…)`, and add the
  post-commitment gates in the callback.
- **Pairing.** Call `PairingCheck` on the output wires.
- **Round trip.** Iterate the compiled `SparseR1C`s and compare them with the
  file, modulo the commit rows and the pairing gadget.

The loader must not create, merge, scale, skip or reorder constraints, and it
must not choose coefficients or wire roles. Its only non-mechanical parts are
gnark std's commitment and pairing gadgets.

## 5. Effort and risks

| Piece | Lean lines | Weeks |
|---|---:|---:|
| `Scs`, `Source`, `GGate` model and semantics | 300 | 0.5 |
| untrusted lowering (forms, fusion, pool, q-form) | 900 | 1.5 |
| checker and `rows_hold`, adapted from `Tiling/Sound` | 700 | 1.5 |
| lookup check, `logup`, `fingerprint_injective`, Schwartz–Zippel bound | 900 | 2 |
| emit, wire map, `β` expansion gates and their functionality lemma | 600 | 1 |
| composition with `Wide.checkMemo` and EndToEnd | 400 | 1 |
| exporter, Go loader, round-trip test, e2e | 300 + Go | 1 |
| **total** | **≈4,100** | **7–9** |

Risks:

- **Checker time.** Templates are checked once per chip, and fixed and ROM
  rows once per row (≈660k messages, linear). This is far below
  `tiling_export2`.
- **Loader trust.** This is the round trip of §4. gnark's `multicommit` and
  the emulated range-check commitments share the single BSB22 commitment.
  That is fine for binding, but it must stay a single commitment.
- **Wire count.** About 30M wires and hints; gnark's solver handles this.
- **Input agreement.** The first version reads `schema.json`, which is the
  current Rust export, so agreement is trusted, as for `tiling_export2`. The
  fix is to read the `.ixa` and apply `Bridge.lower` (step 2).
- **`B` uniqueness.** `ToBinary(γ, 256)` must be canonical. gnark's `ToBase`
  includes a modulus check. The Lean gates must constrain it explicitly.

## 6. Counts on the L3 terminal

Input: `target/e2e-l3/plonk-prepared/prepared/schema.json`, with power-of-two
capacities and every map receiver kept. Counts are per-chip compiles, the
same method as `target/e2e-l3/census/lowered.txt`. The global part (pairing
gadget, BLAKE3 β, root message and output commits) is 2,091,250 in both
cases.

**Go lowering, decomposed (model = census):**

| Part | commit | constraints | count bool | fingerprint + arg wires | inverse + sums | total |
|---|---:|---:|---:|---:|---:|---:|
| G1, Fq, MSM | 2.204 | 2.607 | 0.100 | 5.382 | 2.887 | 13.180 |
| `Blake3::compress` | 1.028 | 1.333 | 0.004 | 3.522 | 0.932 | 6.820 |
| BLAKE3 glue | 0.259 | 0.199 | 0.016 | 0.992 | 0.161 | 1.627 |
| fixed tables | 0.593 | — | — | 1.988 | 1.778 | 4.359 |
| other | 0.421 | 0.520 | 0.023 | 0.936 | 0.221 | 2.121 |
| **all (M)** | 4.504 | 4.660 | 0.144 | 12.820 | 5.980 | **28.108** |

**Lean design (q-form, message-cell commit, fixed rows in one gate):**

| Part | commit | constraints | count | fingerprint | q + sum | total | Δ |
|---|---:|---:|---:|---:|---:|---:|---:|
| G1, Fq, MSM | 2.096 | 2.607 | 0.100 | 5.472 | 2.731 | 13.006 | −0.17 |
| `Blake3::compress` | 0.995 | 1.333 | 0.004 | 3.523 | 0.926 | 6.781 | −0.04 |
| BLAKE3 glue | 0.255 | 0.199 | 0.016 | 0.991 | 0.136 | 1.598 | −0.03 |
| fixed tables | 0.593 | — | — | 0.672 | 1.185 | 2.450 | −1.91 |
| other | 0.384 | 0.521 | 0.023 | 0.938 | 0.169 | 2.035 | −0.09 |
| **all (M)** | 4.323 | 4.661 | 0.144 | 11.595 | 5.147 | **25.870** | −2.24 |

**Terminal total: 27.96M**, against Go's 30.20M and the per-node path's 34.69M.
That is still `2^25`.

The model's dynamic fingerprints are 0.09M worse than gnark's
prefix-sharing memo. Canonical chain order (by wire) closes that gap, and the
Lean lowering does this.

**Which techniques matter.** These are measured on this terminal.

- **Per-node vs Go lowering (−4.49M).** Affine forms, with fixed columns
  and selectors folded into coefficients, product-atom fusion and memoised
  linear wires. The verified version keeps all of these, because they live in
  the untrusted lowering.
- **Fixed rows in one gate (−1.32M).** Together with q-form on the tables
  (−0.59M) this nearly halves the fixed tables: 4.36M → 2.45M.
- **q-form (−0.83M overall).**
- **Message-cell commit (−0.18M).** Only 4.0% of cells appear in no message.
  A determinacy certificate (commit only cells not functionally fixed by a
  linear constraint) adds just −0.05M.
- **Arbitrary-coefficient gates.** Lean scales gates into `GGate` form, so
  gnark's integer-selector API costs nothing. The Go `aiurGateScale` split
  case (`L, R, C ≠ 0`, `MC ≠ LR`) becomes 2 gates, as today.
- **Multi-term fusion.** In a width-3 gate a product can fuse only at a
  chain end. Counting slots, `n` linear terms plus `p` fused products need
  `n + 2p − 2` gates, the same as unfused. No further gain.
- **Custom gates.** gnark PLONK has none.

**Floor.** In width-3 SCS with wire challenges, each message costs at least:

- 2 gates for `q` and the sum;
- 2 gates per variable argument (`v·γ^e`, then the add);
- 1 gate for the exponent-0 argument.

That is 2.57M messages and 5.44M variable arguments: about 15.5M of the
25.9M. Reaching `2^24` therefore needs fewer or narrower messages, a
program-level change (for example `Blake3::compress`'s 226 byte lookups per
row), not a better backend.

## 7. Implementation status and next steps

**Round 1 (2026-11-15).** New files only, all building, no `sorry`:

| File | Status |
|---|---|
| `Aiur/Aiur/Plonk/Scs.lean` | trusted model: `Gate`, `Scs`, `Scs.Satisfied`, `GGate`, `GGate.ofCoeffs` |
| `Aiur/Aiur/Plonk/ScsLemmas.lean` | `GGate.ofCoeffs_holds`, proved: the exported frontend form holds iff the intended gate does |
| `Aiur/Aiur/Plonk/Source.lean` | trusted spec: `Table`, `Table.value`/`Holds`/`rowLedger`, `Source.ledger`, `expOf`, `fp` |
| `Aiur/Aiur/Plonk/Lower.lean` | untrusted lowering (§2): forms, product fusion, memoised linear wires, pool, q-form, fixed-row split, census |
| `Aiur/Aiur/Plonk/Schema.lean` | reader for `ix-aiur-plonk-terminal-v1` JSON |
| `Aiur/Examples/PlonkCensus.lean` | per-table and per-group census |

Run (repo root, about 47 s, interpreted):

```text
PATH=$PWD/target/terminal-complete/toolchain/lean-4.34.1-linux/bin:$PATH \
  lake build Aiur.Plonk.Schema && \
  lake env lean --run Aiur/Examples/PlonkCensus.lean target/e2e-l3/plonk-prepared/prepared/schema.json
```

**Lean lowering on L3: 25,845,015 table gates + 58,988 pool gates =
25,904,003.** By group, G1/Fq/MSM 13.06M, `Blake3::compress` 6.78M,
BLAKE3 glue 1.60M, fixed 2.37M, other 2.04M. That is the §6 projection to
within 0.03M. With the global 2.09M, the terminal is ≈28.0M against Go's
30.20M.

The Python model used for §6 and for checking the Go census is not in the
tree (scratchpad). The Lean census supersedes it.


**Round 2 (2026-11-15), building, no `sorry`:**

- **`Plonk/Template.lean`.**
  - `Table.wideCircuit` (constraints over cell atoms `2c+next`).
  - `Lower.toTemplate`: a row's constraint gates as a `Tiling.Template`
    with width 4 and one lane (`c3 = none`) per row. Each gate either
    defines a `sum` slot or is `root j`; `LGate.root` now records `j`.
  - `Lower.cone` and `Lower.checkUniform`: each constraint is checked by
    the *existing* `Tiling.Template.check` on the template of its own gate
    cone. One template per row is O(n³) in `Template.check`
    (`T.relations` is rebuilt per slot, and lists are indexed linearly), so
    cones keep each check small.
- **`Plonk/Link.lean`.** `Lane.poly_denote_gate` and `Lane.toGate_holds_iff`:
  a one-lane row's relation holds under `w ∘ wire` iff its gnark `Gate` does.
- **`Plonk/Expr.lean`.** `Table.expr_denote` and `Table.holds_of_wide`: for a
  table with no fixed or selector reads, `wideCircuit.Holds (cellView …)`
  gives `Table.Holds`.
- **Accepted so far** (interpreted, `target/plonk-lean/check_main.lean`):
  - `BN254G1::add`, `BN254Fq::canonical_high`, all KzgBlake3 tables, and
    `UInt64::is_zero`;
  - `Blake3::compress` constraints 0–37.
- **Blocker found: constraint 38 of `Blake3::compress`.** `Template.check`
  calls `Poly.ofExpr` on the *tree* unfolding of the hash-consed node DAG
  (`Table.expr`, like `Tiling.Graph.expr`), which is exponential when the
  DAG shares subterms. The cone itself is small (18 gates, 35 slots, 273
  terms after normalisation).
  - Fix (next): pass `Template.check` a circuit whose constraints are
    already normal forms. Build `polys : Array (Poly Fr)` bottom-up over
    the DAG, normalising at each node. Prove
    `(polys[i]).denote a = (t.expr i).denote a` (array-fold invariant, from
    `Poly.denote_norm` and `denote_mul`) and `Poly.toExpr_denote`, so that
    `Holds` transfers.
  - Do not unfold DAGs anywhere else on the checker path either.
- **Memory.** Run every interpreted check through `target/light.sh -m 8G`
  (outside the sandbox). The unbounded constraint-38 check contributed to the
  05:31 OOM.


**Round 3 (2026-11-15): normal forms. All 157 uniform tables accepted.**

- **`Plonk/Norm.lean`.**
  - `Table.polys` normalises node by node over the shared graph.
  - `Table.polysUpTo_spec` and `Table.polys_denote` (proved): each entry
    denotes `Table.expr`.
  - `Poly.toExpr_denote` (proved).
  - `Table.normCircuit_holds_iff` (proved): the normal-form circuit has the
    same `Holds` as `wideCircuit`.
  - `Lower.checkUniformNorm` runs the existing `Tiling.Template.check` per
    constraint cone against `normCircuit`.
- **A second blow-up, in the template itself.** `toTemplate` emitted the
  zero-coefficient `linear`/`product` terms of each defining gate. Since
  `Template.meaning` is not memoised, each linear-chain slot then expanded its
  predecessor twice. Only nonzero terms are emitted now.
- **Result.** `target/plonk-lean/check_main.lean` (interpreted, under
  `target/light.sh -m 40G`, `timeout`) accepts **157 of 157 uniform
  tables, 0 rejected**. `Blake3::compress` takes 42 s;
  `UInt64::wrapping_succ` 2 s; the rest are under 1 s each. Log:
  `target/plonk-lean/check.log`.
- **Not yet checked:** the 24 non-uniform tables (11 fixed tables, 13 ROMs).
  These go to the `Air` path (per-row fixed values; `romAirs` have no
  next-row reads). Messages, pool, q and sum gates are not checked yet either.

**Source of the circuits (replaces the schema.json assumption).** The
composition target is `Tiling.WideStage.wide_heap_sound`. Its `holds` and
`balanced` hypotheses are about `Air`s:

- `unitAirs idOf units`;
- `mapAirs (mapClaims.map (encode idOf)) mapCap`;
- `romAirs roms`, with the ROM as witness at fixed addresses, so it has no
  next-row or selector reads.

`Ixa.lean` (`decodePackage`, `IChip.lower`, `IChip.lower_ofChip`) produces
them from the `.ixa`. The PLONK backend should therefore take `List (Air Fr)`
from that path instead of the Rust `schema.json`:

- `Air.assign` reads the main columns, then the fixed columns at
  `width + k`;
- uniform `Air`s (no fixed columns) are checked once per template;
- the fixed-table `Air`s are checked per row, as now;
- `Plonk.Table` and `Schema.lean` stay only as the Rust cross-check.

Required from the tiling side, coordinated through
`aiur-template-lean-plan.md` §8: an exporter entry that yields the terminal's
`units`, `mapCap` and `roms` at the PLONK capacities. Then the PLONK theorem's
conclusion is `StageHolds airs main ∧ logup`, and Schwartz–Zippel plus the
crypto layer turn `logup` into `balanced`.

**Round 4 (2026-11-15): the stage's `Air`s as input; messages, `q`, sums
and pool checked. 179 of 179 tables accepted.**

The trusted input is now the table list of `WideStage.wide_heap_sound`
(`units ++ maps ++ roms`, built from the `.ixa` by the definitions
`WideIxa.stageOf` uses). `Plonk.Table` is only the lowering's working form;
`Source.lean`'s `Table` semantics, `Schema.lean`, `Expr.lean` and
`normCircuit` serve only the Rust cross-check (`check_main.lean`).

- **`Plonk/Air.lean`.** `AirIn.fixRow` (fixed columns of a row as
  constants), `rowConstraint a r j` (normalised constraint `j` of row `r`),
  `holds_of_rowConstraints`, `rowConstraint_uniform` (no fixed reads: every
  row is row 0). `AirIn.table` hash-conses the circuit bottom-up (Tiling's
  `Graph.ofCircuit` compares trees against a list and was quadratic). Map
  and ROM tables have no constraints, so per-row constraint checking is
  vacuous on this stage; the per-row path exists for Airs that have both.
  `coneTemplate`/`coneOk`/`rowOk` with `rowOk_spec`; the check now also
  requires `coversVars` (every variable of the normalised constraint is a
  slotted main column).
- **`Plonk/Msg.lean`.** `fpExpr` with `fpExpr_denote` (= `Source.fp`).
  `msgCircuit a r k` over main columns plus pseudo-columns `γ, β, q, s, s'`:
  `q·fp(γ,β,args) − m`, `s + q − s'`, and `m² − m` when a booleanity gate
  exists. `toTemplateG`/`coneOf`: cones through row-local and pool gates,
  pool wires as sum slots, so `P_e = γ^e` and the shared bases are checked in
  every cone that reaches them. `msgOk` with `msgOk_spec`. `LGate.msg` tags
  the gates of lookup `k`.
- **`Plonk/Sound.lean`** (proved). `holds_of_cover`; `constraint_of_cone`:
  a checked, covering cone whose column slots carry row `r` gives constraint
  `j` of the Air at `a.assign main r`; `message_of_cone`: gives
  `q · fp γ β tuple = multiplicity ∧ s' = s + q` for lookup `k`.
- **`Plonk/Realise.lean`** (proved). `Realised T wire gates` (each template
  row is an emitted gnark gate through `wire`) and
  `relationsHold_of_realised`: a satisfying wire assignment gives
  `T.RelationsHold (w ∘ wire)`, the hypothesis of the two lemmas above.
- **`Plonk/Emit.lean`** (proved). `LGate.inst wireOf` (a lowered gate as a
  gnark gate), `realisedB T sr gs` (every template row is a gate of `gs` with
  slot `s` read as reference `sr s`, same coefficients; independent of the
  wire map) and `realised_of_realisedB`: then `T` is `Realised` by
  `gs.map (LGate.inst wireOf)` for every `wireOf`.
- **`Plonk/RowSound.lean`** (proved). `rowOkR` adds `realisedB` (against
  the row's constraint gates, with the slot → reference map `slotRefs`, which
  is untrusted and verified by the check) and `colsB` (each `.column c` slot
  reads cell reference `8c`) to every cone.
  `constraints_of_gates`: suppose `w` satisfies the row's constraint gates
  instantiated through some `wireOf` with `wireOf x = cellWire (x / 8)` on
  cell references. Then `a.circuit.Holds (a.assign main r)` for every
  `main` with `main r v = w (cellWire v)`. This is the constraint half of
  `StageHolds` for one row, with no assumption on the lowering.
  `check_stage` uses `checkConstraintsR`. With it, all 157 units are
  accepted again (`check_stage_r.log`, 307 s, map and ROM rows sampled to
  1; those tables have no constraints, and their messages were checked in
  full by the run above).
- **`Plonk/MsgSound.lean`** (proved). Message cones name their gates by
  index into the row's gates followed by the pool gates (`rowPoolGates`), so
  realisation costs one lookup per template row (`realisedIdx`,
  `realised_of_realisedIdx`). `msgCertOk` adds `realisedIdx` and
  `msgColsB` (each column slot reads its cell, `γ`, `β`, `q`, `s`, `s'` or
  the `sumIn` reference). `message_of_gates`: if `w` satisfies the named
  gates (instantiated through `wireOf`, cells to `cellWire`), then either
  the multiplicity is 0, or `w(q)·fp(w(γ), w(β), tuple) = multiplicity` and
  `w(s') = w(s) + w(q)` at the certificate's references. `Realised` now
  takes a gate predicate instead of a list.
- **Compiled checker.** `MultiStark/Examples/PlonkCheckStage.lean`,
  `lean_exe plonk_check_stage` (`MultiStark/lakefile.lean`). It runs
  `checkConstraintsR` and `checkMessagesR` over every row of all 179 tables:
  **179 of 179 accepted in 185 s** (`target/plonk-lean/check_stage_compiled.log`). The census is the same apart from the pool, which has 58,986 gates instead
  of 58,988. The Tiling edits did not cause this; the inputs changed:
  - `compress-final-narrow-l3.ixa` was regenerated at 21:30:33, going from
    3,651,865 to 3,651,844 bytes, and `schema.json` at 21:46:01. Both were
    rewritten by another process. The first compiled run (58,988) had read
    the old artifact. The `Plonk.Lower` sources and every Tiling olean the
    checker imports predate that run.
  - On the current inputs the count is deterministic: three runs give
    58,986, including a rebuild with the earlier message-check driver.
  - The stage keeps its shape: the same tables, rows, lookups and arities,
    and the same count in every non-pool gate class. Pool size is the only
    count that depends on constant values (shared prefixes of the
    fingerprint bases), so the artifact's constants changed. The BN254
    library sources (`Fq.lean`, `FqRelation.lean`) are being edited
    concurrently.
  - The old artifact was overwritten and no copy exists, so the changed
    constants cannot be named.
  - The current inputs agree with each other: per unit table, the pool
    growth on the schema side equals the `.ixa` side (1,021 in total). The
    map callable ids are identical (160–184). The new schema's ROM tables
    are now the Lean witness-address ROMs, with no counter constraints
    (`compare2.log`).
  - To make the next such change attributable, `plonk_check_stage` now
    prints a claims digest and a pool-gate digest.
  - Current inputs: `.ixa` SHA-256 `6c33cd0ac3c400eb…`, `schema.json`
    `17303b9eef91ce0a…`; claims digest 12532005143065522469, pool digest
    7812023920678697977 (179 of 179 accepted, 207 s). The same checks interpreted took 35 min.
- **Padding in the current Rust/Go terminal (soundness question).** The
  padding rows of the compiler's fixed map tables (`crates/aiur/src/trace/
  stark/tables.rs`, `fixed_tables`) are filled with a copy of row 0 in every
  column ("Duplicating a valid row preserves table membership"). `plonk.rs`
  passes that authenticated matrix through unchanged as the schema's
  `fixed`, and the Go lowering folds those values in as constants
  (`aiur_plonk_lower.go`, `case "fixed"`). So a padding row's message
  receives the genuine claim of row 0, and its free multiplicity only adds
  to that claim's count. That is sound, as if row 0 had a larger
  multiplicity. Checked on the deployed L3 schema: in all 7 padded tables
  every padding row equals row 0 (`add_sub_carry_inputs` hosts two maps;
  its padding row copies both). Empty maps get the constraint
  `multiplicity = 0`. No live issue was found.
- **`Plonk/Stage.lean`.** `mapFixedArr_eq`, `mapAirsArr_eq`: array-backed
  map matrices equal `mapAirs` (`mapFixed` is quadratic row by row).
- **Result** (`target/plonk-lean/check_stage.lean`, interpreted, log
  `check_stage.log`): **179 of 179 tables
  accepted, 0 rejected**: 157 units (constraints once per template), 9 map
  tables (984,329 rows) and 13 ROM tables, checked row by row. Every lookup's
  message is checked. The pool is threaded through all tables. Run time is
  2,092 s interpreted under `target/light.sh -m 40G`, peak about 3 GB. Map
  rows run at about 2 ms each and account for 27 min of that. `Blake3::compress`
  takes 22 s. The artifact is decoded with `Ixa.decodeChecked modulus
  ZMod.val` (byte round trip). The driver builds the tables with
  `unitAirI`/`mapAirsArr`/`romAirs`. It does not call `stageOf` itself,
  because `stageOf_spec` is still requested in §8 of the template plan.
  Census on the `.ixa` tables (no commit rows): constraint 6.70M,
  count 0.14M, fingerprint 9.42M, logup 5.15M, pool 58,988, **total 21.47M**.
  The Round 1 census on the Rust schema's tables was 25.90M. The two counts measure different things; nothing is dropped (next item).
- **Gap analysis** (`target/plonk-lean/compare.lean`, log `compare.log`).
  The Round 1 25.90M includes 4.32M BSB22 commit rows (`Census.commit`).
  `check_stage`'s census leaves them at 0. Without commit rows, the current
  lowering gives 21,579,991 on the schema and 21,471,299 on the `.ixa`
  stage. The difference of 108,692 decomposes exactly:
  - **Units:** all 157 are identical, gate class by gate class: same
    capacities, constraints, lookups, arities and gates per row (19,361,208
    both).
  - **Constraint gates, −89,734:** the Rust ROM tables carry a counter column
    with next-row constraints. `romAirs` holds the address as a fixed column
    and has no constraints.
  - **Fingerprint gates, −18,549:** ROM addresses are fixed constants folded
    into coefficients instead of witness arguments (17,952 ROM rows). The
    schema's padding messages contribute the rest.
  - **Messages, −597 (1,194 q/sum gates):** the schema's per-map fixed tables
    are padded to powers of two, and each padding row keeps a message with a
    witness multiplicity. In `mapAirs` the padding rows have `sel = 0`, so the
    multiplicity normalises to 0 and the lowering drops them (checked:
    `msgOk`'s no-gate case). Per map, the claim counts equal the schema's
    receivers: 610,101 = 592,149 claims + 17,952 ROM rows on both sides,
    plus the 597 padding rows (sum 256, key_word 203, key_node 126, key_id 6,
    constant_weight 3, key_circuit 2, key_lookup 1).
  - **Pool, +785.**

  So the `.ixa` stage keeps every receiver, message and constraint the
  schema has, except the ROM counter constraints, which are absent by design
  in the witness-address ROM. The §6 projection plus commit rows still
  applies: about 21.47M + 4.32M + 2.09M global.
- Axioms of all new theorems: `propext`, `Classical.choice`, `Quot.sound`.

**Next, in order:**
1. Done (Round 3); 1b done (Round 4).
2. Done (Round 4): messages, `q`, sums and pool, per cone.
3. Composition, remaining pieces:
   - done: `constraints_of_gates`, `message_of_gates`;
   - a sum-chain check: lookup `k`'s `s` reference is lookup `k−1`'s `s'`,
     and the first is `sumIn`. Then the row's final sum is `sumIn + Σ q`;
   - a uniform-row lemma for messages (`table a r = table a 0` when no
     expression reads a fixed column), as `rowConstraint_uniform` for
     constraints;
   - `StageHolds airs main` with `main t r c := w (cell t r c)`, from
     `rowOk_spec`, `constraint_of_cone` and `relationsHold_of_realised`;
   - the per-row `q`/sum facts summed along the running-sum chain into
     `logup`, then `wide_heap_sound`'s `balanced` via item 5.
4. The emitter and wire map: cells `(t, r, c)`, publics and outputs, row
   locals by `(t, r)`, pool wires once, `sumIn` of row `r` = final sum of row
   `r − 1` (first `= 0` plus the root message), last sum `= 0`.
5. `fingerprint_injective` and Schwartz–Zippel.
6. The β gates.
7. The exporter.

Then specify the Go loader and its round-trip test against the exporter's
actual file layout.

**Round 5 (2026-11-15): sum chain, uniform rows, `stageOk`, the
end-to-end theorem, fingerprint injectivity and the challenge count.**

Inputs, snapshotted before the run: `target/plonk-lean/inputs/2599db25dc50af01/`
(`compress-final-narrow-l3.ixa` SHA-256 `6c33cd0ac3c400eb…`, `schema.json`
`17303b9eef91ce0a…`, the Round 4 inputs). Claims digest
12532005143065522469, pool digest 7812023920678697977, census unchanged.

- **`Plonk/MsgSound.lean`** split into `certNoneOk`/`certSomeOk`
  (`mult_zero_of_certNoneOk`, `message_of_certSomeOk`); `msgCertOk` and
  `message_of_gates` are unchanged in meaning.
- **`Plonk/Chain.lean`** (proved).
  - `chainOk`: every lookup's certificate holds, the first gated lookup's
    `s` is `sumIn`, each next one's `s` is the previous `s'`, and the last
    `s'` is the row's final sum. `chain_sound`: with every fingerprint
    nonzero, `w(final) − w(sumIn) = Σ_k m_k / fp_k`.
  - `logupEval γ β L = Σ_t L(t)/fp γ β t` (an `→+`).
    `logupEval_rowLedger`: the chain sum is `logupEval` of the row's ledger.
  - `rowCheck a r P poolIdx`: lower row `r` against pool `P`, check its
    constraints (`rowOkG`, `constraints_of_gatesG`: `constraints_of_gates`
    for any gate array) and its messages and chain (`msgChainOk`) against
    the row's gates followed by `P`'s. `rowCheck_sound` gives
    `a.circuit.Holds` and the row's LogUp equation.
  - Uniform rows: `uniformB` (no constraint, multiplicity or argument reads a
    fixed column); `table_uniform`, `msgCircuit_uniform`,
    `lowerRowState_uniform`, `rowCheck_uniform`.
- **`Plonk/StageSound.lean`** (proved).
  - `instances airs` (every `(t, r)`), `rowState`, `Wiring` (wire maps:
    cells to `cellWire`, pool references to `poolWire` in every row, and
    `Linked`, the running sum threaded through `instances` from `init` to
    `last`), `emitGates` (boundary gate `w(last) = 0`, pool gates, every
    row's gates), `poolClosed`, and `stageOk`.
  - `linkedB`/`linked_of_linkedB` decide `Linked` for a concrete wiring.
  - `stage_sound`: satisfying `emitGates` gives `StageHolds airs main`, and
    `logupEval γ β (stageLedger airs main) = −w(init)` when no message tuple
    has a zero fingerprint.
  - `ChallengeGood γ β T L`: no tuple of `T` has a zero fingerprint, and
    `logupEval γ β L = 0 → L = 0`. `stage_balanced`: with
    `w(init)·fp(root) = 1`, the ledger plus `single root 1` is 0.
  - Soundness needs no injectivity of the wire maps.
- **`Plonk/WideSound.lean`, `plonk_wide_heap_sound`** (proved). This is the
  end-to-end theorem. Hypotheses:
  - those of `Compiled.wide_heap_sound_compiled`, without `holds` and
    `balanced`;
  - `airs = unitAirs idOf units ++ mapAirs claims mapCap ++ romAirs roms`;
  - `stageOk airs P poolIdx = true`;
  - a `Wiring`;
  - `(emitScs …).Satisfied w pub H`;
  - `hroot`;
  - `ChallengeGood`.

  The conclusion is `wideRom` valid and `EvalFn ∧ Represents`. Lemmas:
  `stageLedger_append` and `stageHolds_append_left`.
  - Crypto layer: `ChallengeGood` and gnark's proof ⇒ `Satisfied`.
  - Emitter obligations: `hroot` and the `Wiring`.
- **`Plonk/Logup.lean`** (proved).
  - `fp_eq`: `fp γ β u = β + (fpPoly u).eval γ`.
  - `fpPoly_inj`: tuples with equal polynomials are equal, when the lengths
    are nonzero in `Fr`. Supporting lemmas: `expOf_inj`, `expOf_lt`.
  - `card_gamma_collide_le`: at most `|S|²ℓ` values of `γ` make two members
    of `S` collide.
  - `card_beta_bad_le`: for a non-colliding `γ` and `L ≠ 0`, fewer than
    `|supp L|` values of `β` give a vanishing LogUp sum.
  - `card_fp_zero_le`: at most `|T|` values of `β` give some tuple of `T` a
    zero fingerprint.
  - `card_not_good_le`: fewer than `|T| + |supp L|` values of `β` violate
    `ChallengeGood` for each non-colliding `γ`.
  - Hence `Pr[¬ChallengeGood] ≤ (|S|²ℓ + |T| + |S|)/|Fr|`. On L3
    (`|T| ≈ 2.6M`, `ℓ` the longest tuple, a few hundred at most) that is below `2^−190`, plus `ε_FS`.
- **Compiled checker** (`plonk_check_stage`) now decides `stageOk` itself, in
  two passes:
  1. lower every row (row 0 of uniform tables) to the final pool `P`;
  2. `poolClosed P`, then `rowCheck` on row 0 of each `uniformB` table and on
     every row of the others.

  All 157 units are `uniformB`, and no table's lowering grows `P`. Result:
  **`stageOk`: 179 tables accepted, 0 rejected, 213 s**
  (`target/plonk-lean/check_stage_ok.log`). `Blake3::compress` takes 2.5 s
  and `map/6` 105 s.
- Axioms (`target/plonk-lean/axioms3.lean`): `propext`, `Classical.choice`,
  `Quot.sound` (`linked_of_linkedB`: `propext`, `Quot.sound`). No `sorry`.

**Round 5b (2026-11-15): root table, concrete layout, `stageOf` driver.**

- **Root message as a table.** `rootAir n` (`WideSound.lean`) has one row,
  `n` main cells and the lookup `push(1, cells)`. `stageLedger_root`: its
  ledger is `single (cells of row 0) 1`. The tables are now
  `airs ++ [rootAir n]`, and `emitGates` adds the boundary gate
  `w(init) = 0` (`init_zero`).
  - `stage_balanced` (rewritten) concludes `StageHolds airs` and
    `stageLedger airs + single (root cells) 1 = 0`.
  - `plonk_wide_heap_sound` replaces `hroot` by
    `statement : (List.range n).map (W.main w airs.length 0) = encode idOf root`.
    The root cells are wires `0 … n−1` of the layout, i.e. the publics, so
    `Satisfied` with `pub` = the statement gives it.
  - The root message is lowered and checked like any other
    (`q·fp(root) = 1`), so no hand-written root gates remain.
- **`Plonk/Layout.lean`** (proved). `Layout` numbers the wires:
  - cell `(t, r, c)` ↦ `cellBase t + r·width t + c`;
  - pool `4k+2` ↦ `poolBase + k`;
  - local `4k+1` of row `i` ↦ `locBase i + k`;
  - `sumIn` of row `i` ↦ `sumIn i`;
  - anything else ↦ `spare`.

  `cell_eq` and `pool_eq` hold by construction. For the link, `finalOk`
  checks the final-sum references, once per uniform table (`finalOk_spec`,
  via `lowerRowState_uniform`). `Linked.congr_out` and `linkOkF` (`linkedB`)
  give `Layout.wiringF : Wiring`.
- **Driver.** It now calls `WideIxa.stageOf` (`allMaps`, `pow2`) and uses
  `st.units`/`st.roms`. Maps are `mapAirsArr st.claims (mapRows st.claims)`,
  equal to `st.maps` by `stageOf_spec` and `mapAirsArr_eq`. `stageOf` takes
  0.8 s compiled, and the claims digest is unchanged. The table-matching gap
  of Round 5 item 4 is closed, except the `.ixa` program-section trust gap.
  After `stageOk`, the driver builds the dense layout (root cells first, then
  cells, pool, locals, `init`, `spare`) and evaluates `finalOk` and
  `linkOkF`. Result (`target/plonk-lean/check_stage_layout.log`, same
snapshot `2599db25dc50af01`):
  - **`stageOk`: 180 of 180 tables accepted** (179 plus the root table, 22
    cells);
  - **`finalOk` and `linkOkF` true**;
  - 25,419,671 wires: cells 4.86M, pool 58,988 slots, locals 20.5M;
  - 192 s in total.

  The census grows by the root message (43 fingerprint, 2 logup gates) to
  21,471,342 gates without commit rows. The pool digest is unchanged.
- Axioms unchanged: `propext`, `Classical.choice`, `Quot.sound`. No `sorry`.

**Open after Round 5b** were the β gates, the commit list and the exporter
(then the Go loader). Round 6 does all three. Its loader specification
replaces the earlier sketch, which assumed an `AssertIsEqual` for `γ` and
had no real file to check against.

**Round 6 (2026-11-15): β gates, commit list, exporter, loader
specification.** Inputs are the snapshot `2599db25dc50af01` (claims digest
12532005143065522469, pool 58,986 gates, as in Round 5b).

- **`Plonk/Beta.lean`** (trusted, proved). The β gadget is a list of
  `Step`s:
  - `lin g` requires `qO ≠ 0` and `a`, `b` already determined; then `c` is
    determined.
  - `bits x bs accs canon` gives the bits of a determined wire `x`, most
    significant first. It emits one booleanity gate per bit and a Horner
    chain `acc' = 2·acc + b` that ends at `x`. With `canon = some ps` it also
    emits a comparison chain against the constant bits of `r − 1`:
    - where the constant bit is 1, the "prefix equal" flag becomes `p·b`;
    - where it is 0, the gate `p·b = 0` applies.

    `checkAll` decides the structural side conditions without reading values
    (determined wires, `qO ≠ 0`, `2^n ≤ r` or `canon` with `r ≤ 2^n`).
    `evalAll` computes the values.
  - **`bits_canonical`**: in a checked decomposition, the bit wires are
    `natBits n (w x).val`. This is the canonicity lemma. `canon_le` shows
    `Σ 2^i·bᵢ ≤ r − 1` over ℕ, so a prover cannot use the bits of `γ + r`
    even when that value is below `2^254`.
  - **`beta_functional`**: `betaOk steps γ β` and a satisfying `w` give
    `w β = betaFn steps γ β (w γ)`. `B := betaFn …` is a fixed computable
    function `Fr → Fr`.
- **`Plonk/BetaGadget.lean`** (untrusted). It emits the same function as
  `aiurLookupBeta`:
  - the domain `"ix/aiur-plonk/logup/v1\0"`, then 254 canonical bits of `γ`
    and two zero bits (gnark's `ToBinary(γ, 256)`);
  - block length 55 and flags `1|2|8`;
  - seven rounds;
  - 16 output words read as a little-endian integer and reduced in `Fr`.

  Bits are constants or wires, possibly negated, so constants fold. A
  `XOR` of two wires is `a + b − 2ab`. Each word sum is a linear chain plus a
  33- or 34-bit decomposition. The gadget has **37,119 gates** and 36,749
  wires.
- **Test** (`plonk_beta_test`, `MultiStark/Examples/PlonkBetaTest.lean`,
  log `target/plonk-lean/beta_test.log`):
  - `betaOk` is true;
  - on the 12 vectors of `TestAiurLookupBlake3` (`0`, `1`, `2^200`, `r − 1`,
    and `BLAKE3([i, 0xa5]) mod r`), `betaFn` equals the specification built
    from `Aiur/Aiur/Library/Blake3/Correctness.lean` (`round`, `schedules`,
    `initialWords`, `blockWords`);
  - the first 8 output words equal its `compress`, and their bytes equal
    `digest` of the same 55 bytes (the standard hash);
  - the prover assignment (`witnessAll`) satisfies every gate.

  Go is not installed on this machine, so the Go test (which checks the Go
  gadget against `zeebo/blake3` on the same vectors) was not run. Its
  reference formula `aiurNativeBeta` is the one the Lean specification
  implements: 64 XOF bytes, little-endian, mod `r`. For example,
  `β(0) = 5140142324035610167810379451217089588625449690236684332715132069877794677037`.
- **`Plonk/Commit.lean`** (proved).
  - `msgCols a`: the main columns that some lookup's multiplicity or
    argument reads.
  - `commitList airs cellWire`: those cells for every row, in `instances`
    order.
  - **`committed_binds`**: assignments that agree on the committed wires have
    the same `stageLedger` and the same `MsgTuple`. Hence `ledgerOf W c` and
    `tuplesOf W c` are functions of the committed values `c`
    (`ledgerOf_spec`).
  - The publics and outputs are root cells that the root message reads, so
    they are in the list. Pool, β and local wires are not committed; they
    are functions of `γ` and the cells.
  - The exporter also decides, table by table, that `msgCols` equals the
    lowering's `messageColumns` (true for all 180).
- **`Plonk/Terminal.lean`** (proved).
  - `emitScsFull` = `emitGates ++ Beta.gadgetGates steps`, committed
    `commitList`, `γ` at `poolWire gammaRef`.
  - `exportGate` = `GGate.ofCoeffs` then `GGate.nz` (unselected operand
    coefficients set to 1). This is needed because gnark's `Mul(x, 0)` is a
    constant, which would send `AddPlonkConstraint` down its `AssertIsEqual`
    path. `exportGate_holds` shows the exported gate holds iff the emitted
    one does.
  - `challenge_premise`: a satisfying `w` with `c = commitList.map w` has
    `w γ = H c`, `w β = B (H c)`, ledger `= ledgerOf W c` and tuples
    `= tuplesOf W c`.
  - **`plonk_terminal_sound`**: the conclusion of `plonk_wide_heap_sound`,
    with `betaOk` added. The challenge hypothesis is now
    `ChallengeGood (H c) (B (H c)) (tuplesOf W c) (ledgerOf W c)`.
  - Axioms (`target/plonk-lean/axioms4.log`): `propext`, `Classical.choice`,
    `Quot.sound`. No `sorry`.
- **The challenge premise, stated precisely.** Fix the public function
  `B = W.betaB steps` and the statement. For committed values `c`, let
  `E_c = {γ ∈ Fr | ¬ChallengeGood γ (B γ) (tuplesOf W c) (ledgerOf W c)}`.
  `E_c` depends on `c` and `γ` only; β is not a prover choice
  (`beta_functional`, `bits_canonical`).
  - The crypto layer assumes that for the `c` a prover commits to (BSB22
    binding, so `c` is fixed before `H c`), `γ = H c` is uniform (`H` a
    random oracle: Fiat–Shamir). The bound is
    `Pr[γ ∈ E_c] ≤ q·max_c |E_c|/|Fr| + ε_bind`.
  - To bound `|E_c|`, `B` is modelled as a random oracle independent of `H`.
    The 512-bit output reduced mod `r` is within `2^−258` of uniform. Then
    `card_gamma_collide_le` and `card_not_good_le` give
    `E_B |E_c| ≤ |S|²ℓ + |T| + |S|` (`T = tuplesOf c`, `S = supp ledgerOf c`).
  - Nothing about the β wire is assumed beyond this.
- **Exporter** (`plonk_export`, `MultiStark/Examples/PlonkExport.lean`, log
  `target/plonk-lean/export.log`, 201 s under `target/light.sh -m 40G`). Before
  writing anything it decides `stageOk` (180 tables), `finalOk`, `linkOkF`
  and `betaOk`, and checks that every gate has a `GGate` form with nonzero
  operand coefficients. It then writes
  `target/plonk-lean/export/terminal-2599db25dc50af01.ixscs`: 812,619,747
  bytes, SHA-256 `82138a5fe6c9196aef89f12395e69b8a7b1c9ee72bba20e2a34eeeedb88fefc8`.
  - The layout is in the module docstring: magic, ten `u64` counts, output
    wires, the coefficient table, 26-byte gates, the commit list, a 9-byte
    hint per wire, and the tables.
  - **Gates: 21,508,463.** That is 21,471,342 (Round 5b) + 2 boundary gates
    + 37,119 β gates. 6,842,002 are pre-commitment and 14,666,461
    post-commitment.
  - Other counts: 171,824 distinct coefficients, 4,696,365 committed cells,
    25,456,420 wires and 0 gates without `GGate` form.
  - Hints: 0 gates with two unsolved wires. 7,423 bit hints, 19,414,523
    solve hints, 1,174,996 unused wires (gaps in per-row local blocks, and
    `spare`).
  - An independent reader (scratchpad `inspect_scs.py`, log
    `target/plonk-lean/export_inspect.log`) confirms the sizes, no trailing
    bytes, all coefficients `< r` and nonzero, all ids in range, distinct
    commits, `γ` of kind 3 and every sampled solve hint inside its gate.
- **Counts against Go.**
  - The SCS rows that Lean determines are
    `gates + commits + 1 = 26,204,829`. This already includes the β gadget,
    the root message and the output commits.
  - Adding the pairing gadget, at most Go's global 2,091,250 (which also
    counts Go's β, root message and output commits), gives
    **≤ 28,296,079 against Go's 30,198,869**, at least 1.90M fewer. It stays
    `2^25`.
  - The commit is 4.70M message cells rather than all 4.86M cells. The
    Round 1 estimate of 4.32M was taken on the Rust schema's tables.

**Go loader specification** (against the real file above; no Go edited).
Name it `aiur_plonk_scs.go`. It replaces the Go lowering
(`aiur_plonk_lower.go`, `_lookup.go`, `_blake3.go`, `_counts.go`).

1. **Read.**
   - Check the SHA-256 against the manifest, the magic `ixscs001` and the
     exact total length (`88 + 4·outputs + 32·coeffs + 26·gates +
     4·commits + 9·wires` plus the tables section, nothing after it).
   - Require every coefficient `< r` and `≠ 0`; every `a, b, c, γ, β`,
     output, commit and hint wire `< wires`; coefficient ids `< coeffs`;
     `sel ≤ 15`; `pre ≤ gates`; the commits distinct.
   - Require `wires 0 … publics − 1` to be kind 0, `γ` to be kind 3 (and the
     only kind 3), and each kind-1 hint to name a gate containing its wire.
   - Reject anything else.
2. **Circuit.**
   - The fields are `Public [publics]` (`gnark:",public"`) and `Cells`, one
     secret per kind-0 wire `≥ publics`, in increasing wire order, filled
     from the trace through the tables section (`cellBase + r·width + c`).
   - The loader keeps `v[0 … wires)`.
   - A wire of kind 1, 2 or 4 gets `v` = `NewHint` (solve gate `x` for it;
     bit `y` of `v[x]`; zero) the first time a gate reads it. Hints are
     prover-only and carry no constraints.
3. **Gates.** For gate `i` in file order, make exactly one call:
   `AddPlonkConstraint(api.Mul(v[a], α), api.Mul(v[b], β), api.Mul(v[c], ω),
   sL, sR, sO, sM, int(qC))`, with `α, β, ω` the `big.Int`s from the table.
   This reproduces `GGate.toGate`: gnark sets `qL = sL·α`, `qM = sM·α·β`. The
   `v` are non-constant terms with coefficient 1, so gnark's
   constant-operand path is never taken.
4. **Order.**
   - Gates `0 … pre − 1` come first.
   - Then `PairingCheck` on `v[outputs]`, the D-trusted gadget. It registers
     its range-check commitment first.
   - Then `multicommit.WithCommitment(api, cb, v[commits]…)`. The callback
     sets `v[γ] := γvar`, with no `AssertIsEqual`, because the file's `γ`
     wire *is* the commitment output. It then adds gates `pre … gates − 1`.
5. **Refusals.** The loader must not:
   - create a constraint other than the step 3 calls (no
     `AssertIsEqual/IsBoolean/ToBinary`, no lookup);
   - merge, scale, skip or reorder gates;
   - compute or choose a coefficient, a selector or a wire role.

   Every non-file constraint comes from gnark's commitment and the pairing
   gadget.
6. **Round-trip test** (Go test on this file).
   - Compile with `scs.NewBuilder` and map each file wire to its VID by
     `api.Compiler().ToCanonicalVariable(v[i]).(constraint.Term).VID`.
   - Let `N = ccs.GetNbConstraints()` and `M = N − gates`. Require:
     - compiled constraints `[0, pre)` equal file gates `[0, pre)`;
     - the last `gates − pre` compiled constraints equal file gates
       `[pre, gates)`;
     - equality means VIDs through the map and coefficients
       `qL, qR, qO, qM, qC` as field elements (`ccs.Coefficients`).
   - The middle `M` constraints must match a reference circuit, compiled
     separately, with the same 18 output secrets, `PairingCheck`, and
     `WithCommitment` over the same committed wires with an empty callback:
     the same `M` and the same constraint sequence up to VID renaming.
   - The commitment's committed VIDs (`GetCommitments()[0]`) must be the
     file's commit wires plus only non-file (range-check) wires.
   - Require `nbPublic = 4` and `nbSecret = #kind-0 − 4`.
   - Solve the circuit on the L3 witness. Then prove and verify once.
   - Expected: `gates = 21,508,463`, `pre = 6,842,002`, and
     `N = 21,508,463 + M` with `M ≈ 4,696,366 + pairing`.

**Next.**

1. Write the Go loader and round-trip test above. Run them on this file
   (needs Go; the heavy prove step goes through `target/heavy.sh`).
2. Pin the file's SHA-256 in the manifest beside the schema hash.
3. Gas on L3 against 285,614. The verifier has 4 publics (`CALL`, the entry
   id and the 2 statement limbs) instead of 2.
4. A proof that the exporter's streamed gate list is a permutation of
   `emitScsFull`. At present this holds by construction: it mirrors
   `emitGates` and reuses row 0 for uniform tables by
   `lowerRowState_uniform`.
5. Read the `.ixa` program section instead of trusting it (the Round 5b
   gap).

**Round 6b (2026-11-15): Go loader, round trip and L3 end to end.**

- **Two public inputs: `CALL` and the entry id are circuit constants.** The
  deployed verifier interface (the 2 statement limbs) is kept.
  - `rootAir k n` (`WideSound.lean`) has `n` cells and the lookup
    `push(1, [CALL, k, cells…])`. The two constants are folded into the root
    fingerprint's pool base (the entry chip's receive already uses the same
    base, so the pool is still 58,986 gates).
  - `stageLedger_root` gives `single (CALL :: k :: cells) 1`.
    `plonk_wide_heap_sound` and `plonk_terminal_sound` take
    `entryId : idOf root.channel = k` and
    `statement : cells = (encode idOf root).drop 2`; together they rebuild
    `encode idOf root`. The cells are the 2 public limbs (wires 0, 1) followed
    by the 18 pairing outputs.
  - Exporter: `k = st.request[1]` (entry id 0 on L3), root cells
    `request.length − 2 = 20`, `publics = public_inputs = 2`. The
    `plonk_check_stage` driver is updated the same way.
  - The entry is the schema's `callable`, resolved by `Schema.entryOf`, not
    the first listed circuit: it must be a callable listed in the package's
    `entries` under that index, a listed circuit, and take `public_inputs`
    argument and `private_outputs` output words; both drivers pass it to
    `stageOf` and refuse the schema otherwise. The theorems need no change:
    `entryId` and `rooted` tie `k` to an entry `name ∈ entries`, and the
    drivers now establish that the `k` they build is such an id.
    `TestAiurScsEntryRoot` (`tools/gnark`, fixture from
    `plonk_entry_fixture`) checks a terminal whose non-entry helper accepts
    any statement.
  - Axioms (`target/plonk-lean/axioms5.log`): `propext`, `Classical.choice`,
    `Quot.sound` for `plonk_terminal_sound`, `plonk_wide_heap_sound`,
    `stage_balanced`, `stageLedger_root`, `challenge_premise` and
    `exportGate_holds`. No `sorry` under `Aiur/Aiur/Plonk`.
- **Re-export** (`target/plonk-lean/export_k.log`, same snapshot
  `2599db25dc50af01`, claims and pool digests unchanged; `stageOk`,
  `finalOk`, `linkOkF` and `betaOk` all true):
  `target/plonk-lean/export/terminal-2599db25dc50af01-k.ixscs`, 812,619,581
  bytes, SHA-256 `4d8b599fe5d8bf16b2519e525217db1699180bde0e1d902f16178f31cfe2a6aa`.
  It has 21,508,459 gates (6,842,002 pre), 4,696,363 commits, 25,456,414
  wires and 4,859,475 input wires. The two root cells that are gone remove
  4 fingerprint gates and 2 commits. The Round 6 file (4 publics) is
  superseded.
- **Loader** (`tools/gnark/aiur_plonk_scs.go`).
  - `readAiurScs` checks the pinned SHA-256 and decodes the file;
    `parseAiurScs` validates it completely (§7, item 1). The input wires
    must be a prefix, outputs and commits must be inputs, and there must be
    one γ.
  - `aiurScsCircuit` has `Public [2]` and `Cells`. `Define` issues one
    `AddPlonkConstraint(Mul(v[a],α), Mul(v[b],β), Mul(v[c],ω), sL, sR, sO, sM, qC)`
    per file gate, in file order: gates `0..pre)`, then `PairingCheck` on the
    outputs (`aiurPairing.constrain`, reused unchanged), then
    `multicommit.WithCommitment` over the commit list, whose callback binds
    `v[γ]` to the commitment and adds gates `pre..)`.
  - Non-input wires are created as hints on first read: solve gate, bit `y`
    of `x`, or zero. A solve hint must be created at its own gate, so all its
    inputs exist. For the common case where the unsolved wire's coefficient
    does not depend on the witness, the hint receives `1/A` as a constant.
    That keeps it at 0.3 µs and the solve at 3.9 s; inverting inside the hint
    took 2.9 µs and 13.6 s.
  - The pairing configuration is the terminal schema's `pairing` object,
    pinned by SHA-256 (`target/e2e-l3-scs/pairing.json`, `eec66e8a…`).
- **The commitment layout differs from the Round 6 sketch.** gnark's range
  checker builds its log-derivative argument in a second multicommit
  callback, which runs after the file's callback. The compiled system is
  therefore `[file 0..pre) [reference 0..P) [file pre..) [reference P..)`,
  where `P` ends at the reference's commitment row. The file callback is the
  first callback, so γ is the commitment output itself, not a power of it.
- **Round trip** (`TestAiurScsTerminal`, `aiur_plonk_scs_test.go`; unit
  tests `TestAiurScsParse`, `TestAiurScsSolveHint`). On L3 it passes:
  - 28,000,870 constraints = 21,508,459 file gates + 6,492,411 reference;
  - `P` = 5,346,289 (pairing gadget, range-check recomposition, 4,696,363 +
    383,674 commit rows and the commitment row), suffix 1,146,122;
  - every file block matches gate for gate (VIDs through the wire map, all
    five coefficients as field elements);
  - both reference blocks match a separately compiled reference
    (`aiurScsReference`: same inputs, `PairingCheck`, `WithCommitment` with an
    empty callback) up to a bijective renaming of internal VIDs, with input
    VIDs fixed;
  - the committed rows are the file's commit list in order, followed by
    383,674 wires that are not file wires;
  - 2 public and 4,859,473 secret inputs.
- **L3 end to end** (`target/e2e-l3-scs`, CUDA, current L3 chain inputs):
  - Witness: the deployed terminal prover (`aiur_narrow_terminal_prove
    --cuda --reuse` on `setup-narrow-l3`, the shared keys hard-linked) was
    run under gdb, and its binary witness was dumped at `ix_gnark_aiur_prove`
    (`capture.sh`).
  - `witness.py` rearranges that witness into the file's input wires. Unit
    and ROM matrices are copied as they are. Map tables take, by callable,
    each map's counts from its compiler map table column, with real rows only
    (padding rows repeat row 0 and carry count 0).
  - That run also re-measured the translator: 30,109,043 constraints, 22.9 s
    prove, and a changed statement refused and rejected.
  - Loader run (`run_test.sh`, `MODE=prove`, `target/heavy.sh -m 85G`, peak
    70 GB): compile 69 s, setup 27 s on the pinned SRS and Lagrange files,
    solve 3.9 s, **prove 25.1 s** (25.7 s on the second run), verify 1 ms.
  - A changed statement is rejected by the verifier and refused by the
    prover (the root message no longer balances). Artifacts and digests are
    in `out/` and `out/summary.json`.
- **Gas** (`target/e2e-l3-scs/evm`, the memory-argument test of
  `target/e2e-l3/evm`): **285,614**, the same as the translator. The verifier
  has the same 2 publics and one commitment. Runtime code is 7,533 bytes,
  calldata 1,060 bytes, and a changed statement is rejected.
- **Against the Go translator:**

  | | Go translator | Lean SCS + loader |
  |---|---:|---:|
  | constraints | 30,109,043 | 28,000,870 (−2.11M) |
  | domain | 2^25 | 2^25 |
  | solve | 1.8 s | 3.9 s |
  | prove (CUDA, incl. solve) | 22.9 s | 25.1 s |
  | gas | 285,614 | 285,614 |

  Both systems share the 2^25 domain, so the GPU part is the same (about
  21 s). The gap is the solver: 19.4M hint calls against gnark's native
  constraint solving. It closes if the Rust witness also supplies the row
  locals, or with a batched hint per row template.
- **Release pin candidates** (not edited):
  - SCS SHA-256 `4d8b599f…2a6aa`;
  - pairing configuration `eec66e8a…3b86`;
  - verifying key SHA-256 `e1be9b01483fdf9f9832e35c7bb4a46c329c95222e8cffe55b922382e843ed5d`;
  - `PlonkVerifier.sol` `a33226a6…7c71`.

  The current release key is the translator's `ed36739b…7e06`.

**Retiring the Go translator** (the plan; done in Round 6c below):

1. **Witness in the file's order.** The Rust terminal prover emits the input
   wires of the `.ixscs` directly: the 2 publics, the 18 outputs, then each
   Lean table's cells. With `--lean-maps`, `plonk::sources` already produces
   the Lean map tables (`Feed::Map`) and the Lean unit and ROM tables, so this
   is a permutation of today's `binary_witness` (outputs move up front).
   `witness.py` is the reference.
2. **Preparation and FFI.** Add `ix_gnark_aiur_scs_compile` / `_prepare`,
   which take the `.ixscs` and the pairing configuration with their digests
   instead of `schema.json`. The manifest (`artifacts.go`,
   `aiurManifest`) carries `ScsSHA256` and `PairingSHA256` beside
   `SchemaSHA256`, and later in its place. `openAiurProver` and `prove` are
   unchanged, because the circuit, the keys and the binary witness format
   are the same objects.
3. **Pipeline.** `run.sh` and `setup.sh` run `plonk_export` after
   `terminal_export` and point the terminal prover at the loader. This is
   checked by running the e2e on CUDA and comparing the verifying key with
   `e1be9b01…`.
4. **Then delete** `aiur_plonk_lower.go`, `aiur_plonk_lookup.go`,
   `aiur_plonk_blake3.go`, `aiur_plonk_counts.go` and their tests,
   `aiurCircuit` and the schema circuit types in `aiur_plonk.go`, and the
   schema circuit emission in `plonk.rs` (`circuit`, `lean_circuit`).
   - Kept: `aiurPairing` (`aiur_plonk_pairing.go`), the prover and manifest
     code, and the witness feeds.
   - The trusted Go surface is then the loader's reader and `Define`
     (about 330 of its 530 lines; the solve, bit and zero hints are
     prover-only and do no arithmetic on constraint coefficients) plus
     gnark's `PairingCheck` and BSB22 commitment.
5. **Still trusted after that:** the `.ixa` program section (Round 5b gap)
   and the exporter's streamed gate order (next-step 4).

**Round 6c (2026-11-16): the translator is retired.** The production L3
terminal proves the Lean SCS; the circuit is exactly the file's
(round trip, VK `e1be9b01…` unchanged).

- **Witness.** `plonk/scs.rs` (`Witness`) writes the file's input wires
  from the compiler traces, as `witness.py` did: unit tables from the function
  traces, `rom/N` from the ROM traces, `map/L` (maps with `in + out = L − 2`,
  by callable) from the compiler map columns, the root from the claim. It is
  byte-identical to `target/e2e-l3-scs/cells.bin` (SHA-256 `cc6526ee…`).
  The rest of plan step 1 is not possible as stated: 14.66M of the 19.41M
  solved wires come after the commitment and depend on γ (fingerprints,
  quotients, running sums, the β gadget), which exists only inside gnark's
  solve. Rust supplying the 4.76M pre-commitment wires would save about 0.2 s
  and add 150 MB of witness, so it is not done.
- **Hints instead** (`aiur_plonk_scs_wires.go`, prover-only, no constraint):
  coefficients folded into the hint inputs (sum and product hints), the
  2.57M quotients in batches of 1024 with one inversion, and add-one-term
  chains (the running sum, about one link per message, and fingerprint
  steps) as segmented chain hints, created lazily so hint instructions stay
  interleaved with the gates (gnark's `SparseR1CIterator` recurses per
  consecutive hint; an eager version overflowed its 1 GB stack in setup).
  Solver levels 2,573,499+ → 517, solve 4.2 s → 1.6 s (isolated).
- **Preparation.** `ix_gnark_aiur_scs_compile` / `_prepare` take the `.ixscs`
  and `pairing.json` with their SHA-256s; the manifest
  (`ix-aiur-scs-artifacts-v1`) records `ScsSHA256` and `PairingSHA256` and
  pins `inputs.json` (the input layout the witness reads). `setup.sh` step 6:
  `aiur_narrow_terminal_prove --stage-only` writes `stage.json` (names, rows,
  widths; `plonk_export` reads only these) and `pairing.json`, then
  `plonk-export-cached.sh` runs `$A/bin/plonk_export` keyed by the exporter,
  artifact and stage (this reproduced `4d8b599f…` byte for byte); step 7
  prepares with `--scs $A/terminal.ixscs`.
- **Switch** (`aiur-compression-architecture.md` §3 has old → new). Staged
  in `target/e2e-l3-scs/stage`: VK `e1be9b01…`, `PlonkVerifier.sol`
  `a33226a6…`, changed statement refused and rejected, forge memory-argument
  test 285,614 gas (`target/e2e-l3-scs/evm-stage`), `run.sh` end to end; then
  moved to `target/e2e-l3/plonk-prepared` (old keys:
  `target/e2e-l3-lean/old-translator-plonk-prepared`).
- **`bench.sh 3`** (`docs/measurements/aiur-compression-l3.json`): PLONK
  prove 22.2 / 23.1 / 23.1 s (median 23.1, exposed 24.2), end to end median
  166.7 s. One same-binary pair outside the bench: translator 24.9 s (solve
  1.6), Lean SCS 28.5 s (solve 2.3); its non-solve gap was in the CUDA
  backend's host copies (4.6 vs 2.4 s) and numerator callback (4.7 vs
  2.1 s), which did not recur in the bench.
- **Deleted.** Go: `aiur_plonk_{lower,lookup,blake3,counts,backend}.go`, the
  schema circuit in `aiur_plonk.go`, schema preparation and the v1 manifest
  in `aiur_plonk_prover.go`, `ix_gnark_aiur_compile/_prepare`,
  `validateOutputContract`, their tests and `testdata/aiur`. Rust: the schema
  emission and `Exporter` in `plonk.rs`, `gnark::compile/prepare`, the
  translator examples (`aiur_plonk_fixture`, `aiur_terminal_fixture`,
  `aiur_terminal_profile`, `plonk_cost`, the PLONK options of the two other
  profiles), `tests/aiur_plonk.rs`, and the old path of
  `aiur_narrow_terminal_prove` (which now requires `--scs`). New Go tests
  (`aiur_plonk_scs_wires_test.go`) cover every hint kind, the round trip on
  a synthetic file, pairing binding, manifests, strict witness decoding and
  a development proof. `tools/check-aiur-compression-fixtures.sh` did not
  reference the translator.
- **Release pin candidates** (not edited): SCS `4d8b599f…2a6aa`, pairing
  `eec66e8a…3b86`, VK `e1be9b01…3ed5d`, `PlonkVerifier.sol` `a33226a6…7c71`.

**Round-1 plan (kept for reference):**

1. **Templates as data.** `Lower` keeps the row templates, not only their
   counts (uniform tables: one per table; other tables: one per row,
   streamed). Add the slot table (`column`/`sum` meanings) the checker needs.
2. **`Plonk/Check.lean`.** Implement:
   - `checkSlot`/`checkRelation`/`checkConstraint` for one-lane gate rows,
     ported from `Tiling/Shape.lean`, reusing `Poly`;
   - the message check: `d` meaning = `fp`, with pool meanings over
     pseudo-columns `γ`, `β`;
   - the q and sum gates;
   - the pool check (`P_e = γ^e`, bases).
3. **`Plonk/Sound.lean`.** `meaning_val` and `constraints_hold`, by the
   proofs of `Tiling/Sound.lean` lines 204–350 adapted to `PlonkChecked`.
   Then `rows_hold` and `logup` (§3).
4. **`Plonk/Emit.lean`.** Implement:
   - the wire map (cells, then publics and outputs, then locals by
     `(table, row)`, then the pool);
   - `emit` and its theorem `Satisfied (emit) → ∀ t r, RelationsHold (val t r)`;
   - the commit list from `messageColumns`.
5. **`Plonk/Logup.lean`.** `fingerprint_injective`, and the Schwartz–Zippel
   bound on `Σ m/(β+fp)` for nonzero ledgers.
6. **The `β` expansion as Lean gates**, with a functionality lemma; BLAKE3
   equality as a test.
7. **Exporter `ix-aiur-scs-v1`, Go loader, round-trip test, e2e on L3**, with
   gas compared against 285,614. Heavy steps go through
   `flock target/heavy.lock`.
8. **Composition** with `Wide.checkMemo` and EndToEnd. Then replace the
   JSON input by `.ixa` + `Bridge.lower`.
