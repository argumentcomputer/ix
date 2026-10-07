# The Lean compiler as passes: design document (Phase A)

Status: **draft for the owner's signature (review R1)**. It was folded onto `564d03f0` (wave 2: the
A2 migration, Pass 3 behind its switch, the A7 driver checks, the perf ports) and revised 2026-10-03
with the owner's

decisions on the first draft's questions (§8). Written 2026-10-02/03
 on `jcb/ix-certified`
at `f829b760` (Lean 4.34.1). No compiler file changed between `e9cb732e` (where the planning reports
cite lines) and `f829b760`, so every `file:line` below is valid at both. Nothing was built or run to
write this document.

What the certification lane (`Ix/CompileCert/**`) establishes about the compiler's output, the
theorems W and S, their receipts and trust, and how to run the certifier `compile-certify`, is in
`docs/compiler-certification.md`.

Lean's elaborator is cited from a Lean **4.34.0** source tree (`src/lean/Lean/...`), the only one
readable when this was written; whether 4.34.1 changed any cited line is **[open]**.

**Status markers** (as in the old plan):
- **[measured]**: an experiment or census recorded it; the input file is cited.
- **[argued]**: a paper argument given here.
- **[open]**: not established.
- **[proved]**: machine-checked in Lean, with no `sorry` and only the standard axioms; the module is
  cited.

A fact about code carries a citation and no marker.

**Abbreviations.**
- *Old plan*: `plans/review/auxgen-certify/PLAN.md` (untracked). Its definition numbers (Def 1.x–4.x,
  O1–O17, M.1–M.6) are reused here.
- *Phase A*: `plans/PLAN-A-compiler-design.md` (untracked).
- *CEN*, *PRO*, *ORA*, *MUT*: the census, prototype, oracle and mutual-definition study under
  `plans/review/auxgen-certify/inputs/` (`exp-census-1.md`, `exp-prototype-1.md`, `exp-oracle-1.md`,
  `study-mutual-definitions-1.md`).
- *A1C*: `plans/wave1/a1c.md` (untracked): the Pass 1 port and census at `f829b760`, Lean 4.34.1,
  Ixon v4 (bookmark `jcb/ix-cc-a1c`).
- Wave-2 reports, all under `plans/wave1/` (untracked):

  | Tag | File | Subject |
  |---|---|---|
  | *A2O* | `a2o.md` | discovery order |
  | *A2P* | `a2p.md` | one constant per auxiliary |
  | *A2M* | `a2m.md` | the migration commit |
  | *A3W* | `a3w.md` | Pass 3 |
  | *A3M* | `a3m.md` | Pass 3 merged onto the migrated head |
  | *A7S* | `a7s.md` | driver claims and the A7 worklist |
  | *A1G2* | `a1g2.md` | twins and oracle reconciled with A0 |
  | *PERF* | `perf.md` | the perf ports |
  | *CI* | `ci.md` | `aux-cert --local`, phase timers |

  All of them ran under Lean 4.34.1 on the box. Their measurements were taken under load unless
  stated otherwise.

Every definition used here is restated, so this document does not depend on those files.

---

## 0. Findings in brief

1. **The comparator is a total preorder at every fixed context, on every input Lean can produce**
   [proved for the Lean compiler's comparison under its rules, given distinct member names and an
   address map that answers alike for `==` names: `compareFresh_total`,
   `Ix/CompileCert/Canon/Cache.lean`; §3.2]. The fixed point of the refinement does not depend on the
   seed order: neither the partition nor the order of the classes does [proved: `sortClasses_setEq`,
   `Ix/CompileCert/Canon/SeedFree.lean`; §3.3]. Only the order of members inside a class does (the
   same theorem), and that is metadata [argued]. The Rust port is not proved; its agreement with the
   Lean compiler is tested by byte identity (§4.8).
   - The Lean port has two latent defects that the Rust original does not have. **C1:** comparing
     members of different kinds always returns `lt`. **C2:** the comparison cache is not normalised
     for argument order.
   - Neither is reachable today [argued; measured by A1C §4: 0 reversed non-equal cache hits inside
     the sort on Init+Std, Mathlib and the fixtures]. Both are fixed in A2's migration commit, with
     no byte change.
   - Measured by A1C §1.3: 0 seed-sweep differences on 145 fixture components, 17 Mathlib components
     and 170 Mathlib cliques; 0 preorder violations on components of up to 40 members.

   - The order is *defined by the refinement procedure*. A declarative "fixed point of sorting" is not
     unique (§2.3, §3.4 C9).
2. **Addresses are compared at the first difference, and Phase A keeps that.** External references
   are compared by address wherever two members first differ, interleaved with the structural
   comparison. The owner decided to keep this comparator (2026-10-03): the canonical order may flip
   across Ixon format versions, which are breaking changes anyway. A two-key alternative was
   considered and rejected (§2.3).

3. **Discovery order** is a FIFO queue over the block's types, each constructor walked pre-order. It
   is not "depth first into new auxiliaries" as the old plan's Def 2.5 says. It is pinned in §2.5.
   - The definition is confirmed against `src/kernel/inductive.cpp:985-1180` at v4.34.1, and it
     matches Lean's `rec_N` on 98 of 98 nested blocks [measured, A1C §0.3, §1.3].
   - Both Ix ports deduplicate sibling occurrences of an external mutual inductive wrongly: 4
     auxiliaries where Lean has 2, and production `ix compile` rejects the block [measured, A1C
     item 7]. The fix is assigned to A0.

4. **Transport of clique proofs is not a pure renaming in any of the three encodings** (§5). They
   use up to four kinds of step:
   - (R) a renaming of the encoding's own constants;
   - (A) a re-association of the packing types, injections, case trees, tuples and projection paths;
   - (S) re-stated obligations wherever a statement mentions the packing (well-founded `proof_N`,
     `partial_fixpoint` monotonicity goals);
   - for `partial_fixpoint`, (G) regeneration of the projection-path monotonicity sub-proofs, whose
     shape depends on the path.

   Every transported term proves the canonical obligation [argued]. Where the conjugation does not
   apply, Lean's own term is a fallback proof:
   - by conversion, for the well-founded obligations;
   - by composition with the re-association isomorphism, for monotonicity;
   - unchanged, for theorem bodies, whose statements never mention the encoding.

   The constant is then recorded in the non-canonical set (§0.1, §7.2).

5. **Lean 4.34's well-founded definitions with a single `Nat` measure use `WellFounded.Nat.fix`.**
   That combinator reduces on closed arguments (`src/lean/Init/WF.lean:470-499`), so the old plan's
   "never meet by conversion, not even on closed arguments" holds only for the `WellFounded.fix`
   route (§5.2).

### 0.1 The governing principle (owner, 2026-10-03)

**Faithfulness comes first.** Canonicity is approximated as closely as the Lean-elaborated input
allows. Some of Lean's proof terms were built against the non-canonical presentation in ways that
cannot be re-created as the terms an Ix elaborator would have produced from the canonical input.
Where faithfulness demands it, a pass emits non-canonical or non-minimal Ixon, records the constant
with its cause in the **non-canonical set** (§7.2), and moves on.

This is a temporary expedient until elaboration is under Ix's control. The Ix elaborator will then
produce the canonical terms directly.

Every pass's "Side condition and fallback" section refers to this principle: **the fallback is always
the faithful form.**

Terminology: "non-canonical set" replaces the first draft's "residue", which collided with the old
plan's "residual image". "Image" keeps its meaning: the extra constants of Def 3.4–3.5.

---

### 0.2 Status at `564d03f0` (wave 2)

- **Pass 1 and the A2 migration.** Pass 1 is implemented as total pure functions
  (`Ix/Compile/Canon/**`). The compiler's comparator is Pass 1's `Rules.compiler := Rules.phaseA`:
  name-hash seed, least-name-hash representative, addresses at the first difference, `canonUniv`
  levels, discovery order, and the C1/C2 port fixes (`Ix/Compile/Canon/Order.lean:446-461`).
- **D2 and D6** (discovery order; one constant per auxiliary) landed in one migration, with every
  moved address accounted for (§2.8) [measured, A2M].
- **Pass 2** is today's generators with D6 packaging.
- **Pass 3 (images, the faithful rewrite)** is the default since the flip (M6, 2026-10-06; §4.8, §7.4);
  `IX_PASS3=off` selects the legacy call-site surgery, kept as the comparison mode against the Rust
  compiler's default until M6R slice 6. The Rust compiler implements Pass 3 under `IX_PASS3=images`
  (M6R slices 1–4), byte-identical to Lean's default on Init+Std and Mathlib; with `IX_PASS3` unset it
  still runs the surgery (§4.8, "Switch").
  With the switch off (`IX_PASS3=off`), no byte moves against the pre-Pass 3 compiler [measured, A3W/A3M].
- **Not yet wired into the compiler** at `564d03f0` (since wired, under Pass 3: the clique transport
  through `Ix/Compile/Pass/Cliques.lean`, §5.7, and the optimisation passes O1–O12, §1.5–§1.6):
  - the clique transport (`Ix/Compile/Clique/**`, §5.7–5.8);
  - the optimisation passes (A4).
- **The Lean drivers' claims are insert-once with Rust's error (§6).** The Lean environment writer
  and the area search were ported (§10).

## 1. The pipeline and the convention

### 1.1 The passes

Input: the prepared `List (Lean.Name × Lean.ConstantInfo)` (`Ix/CompileDriver.lean:1194-1226`), plus
read access to `Structural.eqnInfoExt`, `WF.eqnInfoExt` and the `partial_fixpoint` `EqnInfo`.

Output:
- the Ixon v4 environment `E`;
- the side-car: names, hints, metadata, `Named.original`, clique permutations, call-site records.

| # | Pass | Input | Output | Module (to be) |
|---|---|---|---|---|
| P1a | Components | prepared constants | the SCCs of the reference graph (§2.1) | `Ix/Compile/Canon/Graph.lean` |
| P1b | Classes and order | one SCC; the closure's addresses | ordered classes; representative per class (§2.2–2.3) | `Ix/Compile/Canon/{Classes,Order}.lean` |
| P1c | Nested auxiliaries | canonical inductive block | the expanded block in discovery order; evaporation set (§2.5–2.6) | `Ix/Compile/Canon/Nested.lean` |
| P1d | Cliques | `EqnInfo`, `_unsafe_rec`, `partial_fixpoint` data | cliques, specifications, classes, order, `σ` (§2.7) | `Ix/Compile/Canon/Clique.lean` |
| P1e | Name map | P1a–P1d | `N : Lean.Name → canonical position` | `Ix/Compile/Canon/NameMap.lean` |
| P2 | Ix auxiliaries | canonical blocks | `rec`, `rec_N`, `casesOn`, `recOn`, `below*`, `brecOn*` (`.go`, `.eq`, `_N`), `IndPredBelow`; one constant per auxiliary | `Ix/Compile/Pass/Aux.lean` over `Ix/AuxGen/*` |
| P3a | Images | Lean recursors of changed blocks; P1, P2 | `img(r)` (Def 3.3–3.4, §4) | `Ix/Compile/Pass/Image.lean` |
| P3b | Translation and baseline | every other constant | `tr_N`, Def 3.5 images, Def 3.6 baselines, inline call sites (§4.5) | `Ix/Compile/Pass/Translate.lean` |
| P3c | Canonical cliques | changed cliques | the repacked functional, transported proofs, members as projections (§5) | `Ix/Compile/Pass/Clique/{Structural,WF,PartialFixpoint,Transport}.lean` |
| P4+ | Optimisations | baselines | O1–O17, each a module with a side condition | `Ix/Compile/Pass/Opt/O*.lean` |
| P4e | Rewrite engine | P4+ modules | the fixed point (§1.4) | `Ix/Compile/Pass/Opt/Engine.lean` (A4: fused with P3b, §1.5) |
| P5 | Emission | compiled terms | sharing, serialisation, side-car | `Ix/Compile/Pass/Emit.lean` |
| — | Fold | all of the above | the sequential fold over blocks that defines `compile` (§6) | `Ix/Compile/Fold.lean` |

P1 is written as total pure functions over data types. They have no `partial`, and import nothing
from `Lean` beyond the data types (Phase A §3.1).

**As built at `564d03f0`.** The modules differ from the planned names above:

| Pass | Built as |
|---|---|
| P1 | `Ix/Compile/Canon/{Expr,Graph,Order,Classes,Nested,Block,Clique,NameMap}.lean` |
| image generator | `Ix/Compile/Image/{Expr,Spec,Develop,Build}.lean` |
| Pass 3 wiring | `Ix/Compile/Pass/{Names,Translate,ImageView,SideCar,Driver}.lean`, about 1,050 lines [A3W §1] |
| clique transport | `Ix/Compile/Clique/**`, including `Recover.lean` and `FixPerm.lean` |

P2 is today's `Ix/AuxGen/*` with D6 packaging.

### 1.2 The five-part docstring

Every `Ix/Compile/Pass/**` module opens with:

```
/-! # <Pass name>

## Contract
Input invariants, output invariants, stated with the definitions of §2 (components, classes,
canonical order, discovery order, name map N, images, baselines) and the kernel's declaration
language.

## Faithfulness
Definitional pass: the conversion steps (δ of which constants, β, ζ, η, ι, projection of a
constructor) that make each rewritten constant definitionally equal to its baseline.
Proof-justified pass: the equation, the statement Phase B formalises, and its proof sketch
(induction on what, which lemma).

## Canonicity
What the output depends on: canonical data only, or canonical data plus addresses (where), plus
the members of the non-canonical set. Why two presentations of one canonical block or clique give
equal bytes.

## Side condition and fallback
The decidable condition. What remains when it fails, and why that is faithful. Per §0.1 the fallback
is always the faithful form, usually the baseline. A constant the fallback leaves non-canonical is
recorded in the non-canonical set with its cause.

## Non-canonical set and evidence

Known non-canonical outputs with their cause code (§7.2). The fixtures, twins, value pins and
census counts that exercise the pass, with their status markers.
-/
```

### 1.3 Worked example: O1, permutation pass-through

```
/-! # O1: recursor of a permuted block

## Contract
Input: a baseline term containing an occurrence `img(T.rec).{u,us} a₁ … a_m` or
`img(T.recOn).{u,us} a₁ … a_m`, where T is a member of a Lean inductive block b whose
canonicalisation is a *pure permutation*:
  - one component;
  - every class a singleton;
  - only the member order and/or the discovery order of nested auxiliaries differ from Lean's.
Let ρ be the Ix recursor of T's class (the recursor block of canon(b), projection at T's canonical
motive index).
Let π be the bijection from Lean motive indices to Ix motive indices: members by the class map,
auxiliaries by the discovery-order map (§2.5).
Let π′ be the induced bijection on minors: Lean minor (i, k) ↦ Ix minor (π i, k), with
constructors by position.
Output: the occurrence is replaced by
    ρ.{u′, us′} ps (ms ∘ π⁻¹) (mins ∘ π′⁻¹) is x a_{n+1} … a_m
where
  - ps, ms, mins, is, x are the first n = np + nm + nmin + ni + 1 arguments in Lean's order;
  - u′, us′ are the canonical levels (`canonUniv`, positional renaming);
  - for `recOn` the Lean argument order (ps ms is x mins) is read accordingly.
The result contains no image reference at this position. The arguments are copied unchanged.

## Faithfulness (definitional)
By Def 3.4 with all classes singletons:
  - no slot is a tuple, so the level is u (step 2) and no slot is lifted (step 3);
  - every Lean induction hypothesis comes from a field that is recursive for ρ: the block is one
    component, so nothing is relocated (step 4.2);
  - so the Ix minor for constructor c of slot π i is `λ fs ihs. lean_minor_{i,k} fs ihs`, with the
    IHs in the same field order. Ix and Lean constructors have the same fields by position.
The development (§4.3) η-contracts it to `lean_minor_{i,k}`, so
    img(T.rec) ≡ λ ps ms mins is x. ρ ps (ms∘π⁻¹) (mins∘π′⁻¹) is x.
The rewrite is one δ-step (img), one β-step (n arguments) and η-steps on the minors. Each is a
conversion the kernel performs, so `Eq.refl : @Eq τ c base(c)` checks, where τ is the translated
Lean type of the rewritten constant c [argued].
For recOn: Def 3.5 makes img(T.recOn) Lean's value over img(T.rec), and the same steps apply.

## Canonicity
Let twin(c) be c's counterpart in the source where b is declared in canonical order. Then twin(c)
mentions T′.rec with its arguments already in canonical order, and its translation is
`ρ ps ms′ mins′ is x …` with ms′ = ms∘π⁻¹ term for term, because the user's motives and minors are
the same terms up to the renaming.
The output depends on: π (a function of the canonical order, §2.3, and of the discovery order,
§2.5); the canonical levels; the arguments.
It does not depend on Lean's member order beyond π.
So two presentations give equal bytes once their arguments are equal after translation [argued].
Addresses enter only through ρ's address, i.e. through the canonical block.

## Side condition and fallback
Decidable: m ≥ n (fully applied), and b is permutation-only (read from P1).
Otherwise the occurrence keeps its baseline reference to the image constant img(T.rec), which is
faithful by Def 3.6 and Prop 3.3. This is the faithful form of §0.1.

## Non-canonical set and evidence
Entries: none for full applications.
 Bare or partial occurrences stay faithful only (cause BARE,
§7.2).
Evidence:
  - [measured] ORA (exp-oracle-1.md, DQReord): 53/53 constants of a reordered fixture equal the
    twin's, including the structural functions and the theorem.
  - [measured] CEN (exp-census-1.md:20, Q3): in Mathlib's closure, 6 reordered blocks; 206 `rec`-plan
    call sites; 14 `Ring` definitions and 16 `_f`.
  - [measured] PRO (exp-prototype-1.md, C1): permutation images 2/2, rules 3/3, `rfl` bridges 4/4.
  - Twins gate: every permutation of every fixture block (§3.6).
-/
```

### 1.4 Pass order and the fixed point

**The engine.**
- Passes P1 → P2 → P3 run once per block or clique, in the fold order of §6.
- The optimisation passes run in the engine, separately on every compiled constant:
  - repeat: traverse the term bottom-up (arguments before the head, left to right);
  - at each image occurrence, apply the first pass in the fixed order whose pattern and side
    condition hold;
  - after each rewrite, develop the created redexes (§4.3);
  - stop when no pass applies.
- Whole-unit passes (cliques: O13–O17; helper families: O11a/b) run once per unit, after the
  occurrence passes have finished on the unit's constants.

**Termination** [argued]:
- the measure is the number of image-constant occurrences in the term;
- every occurrence pass removes one, the occurrence it rewrote;
- no pass introduces an image occurrence. The outputs are over Ix constants and the copied
  arguments; O2's relocated calls are Ix recursors, not images;
- the development (§4.3) contracts only redexes created at the rewrite site, so it is finite;
- unit passes run once.

**Confluence of the definitional passes** [argued]:
- O1–O4 and O11a have pairwise disjoint patterns, distinguished by the auxiliary kind and by the
  block's change kind.
- O5 is O1–O4 at universe 0, not a separate pattern. It is implemented as the level rule inside
  O1–O4.
- O6 overlaps O1, O3 and O4: every permuted-block image of theirs is "an Ix auxiliary applied to a
  permutation of its arguments". On the overlap, both rewrites produce the same term.
- Every rewrite is left-linear in its arguments and copies them unchanged, so rewrites at nested
  positions commute.
- One interaction needs the bottom-up order. The development can make a bare occurrence fully
  applied: `(λ g. g p q) (img a)` develops to `img a p q`. The engine re-scans after each
  development, so the result does not depend on which occurrence was examined first.
- So for the definitional passes, the order of the table below is immaterial.

**Order constraints for the other passes** [argued]:
1. Definitional passes first (O1–O6, O11a, O13a/b). They recover today's output on the library call
   sites, and the clique passes need them: a canonical clique is elaborated over the *Ix*
   auxiliaries of canonical blocks (M.6 counts a clique that ranges over a changed block as changed).
2. Clique passes (O14–O16) next. O9 (split, structural recursion with a cross field) is the target of
   O14 over a split block (old plan §3.6), so the two produce the same rewrite and do not conflict.
3. Collapse and split passes last (O7, O8, O10, O11b, O12, O17). Their side conditions compare the
   *compiled* forms of arguments ("arguments identical after compilation"), so every argument must
   already be in normal form. The bottom-up traversal guarantees that.
   - O7 is disjoint from O1 (collapsed versus permuted-only block).
   - O8 is disjoint from O3 (collapsed or lifted member versus permuted or split block).
4. **No demotion** (decision 5, D1, owner 2026-10-05, replacing the old plan's §3.5 requirement 2):
   a proof-justified rewrite (O7–O12) never changes the Lean name. The Lean name keeps its faithful,
   convertible form (the baseline), the rewrite goes into the canonical constant `c._ix`, and the
   Lean name is recorded non-canonical with the pass as its cause (§1.6). So no dependent can be
   broken by a pass, and no pass reads a dependent (§6.3): there is nothing to demote.

---

### 1.5 The definitional passes as implemented (A4)

Modules `Ix/Compile/Pass/Opt/{Core,O1,O2,O3,O4,O5,O6,O11a,Engine}.lean`, each with the five-part
docstring. One hook: `Ix.Compile.Pass.Translate.rw` asks the engine at every full application of
an image-kind head, after the arguments were rewritten and before the image is inlined; the
engine's `none` is the baseline. The driver builds the blocks' data once per block rewrite
(`Ix.Compile.Pass.optLookup`). With the switch off nothing runs.

- **The shape of an image.** Every pass reads the image of the related Lean recursor: `img(r) =
  λ ps ms mins is t. ρ.{ℓs} ps ms′ mins′ is t` with the parameters, indices and major as the
  image's variables, each Ix motive a motive variable, each Ix minor a minor variable or a term
  headed by one. The motive and minor correspondence is therefore the image generator's (§4.2
  step 1, by motive type), never recomputed; the Ix auxiliary of another kind is the display name
  next to `ρ` (D14); the universe arguments are `ℓs` at the occurrence's levels (O5's rule, which
  covers the Prop member that gained large elimination).
- **O1** `rec`/`recOn`, permutation-only block (Pass 1's change kind): `ρ` (or the Ix `recOn`)
  with motives and minors permuted. `recOn` goes to the Ix `recOn`, the twin's term.
- **O2** `rec`, split block: `ρ` with the component's motives, and each minor with a field into
  another component adapted: `λ fs ihsᶜ. mⱼ fs ih⃗`, domains from Lean's minor type, the relocated
  hypothesis the engine's rewrite of `r_T ps ms mins idx (f ys)`, `mⱼ` applied (β-redex left).
  This is the term the old surgery emitted; the image's developed form differs from it only by β.
  The minor's constructor, its type and its field and IH binders are read with the surgery's
  split-minor helpers (`Ix/CallSiteSurgery.lean`: `auxMotiveSigs`, `sourceCtorForMinor`,
  `sourceMinorType`, `peelBinders`, `findSourceRecTarget`; the Rust compiler's `surgery.rs`
  counterparts), which O11a uses too: deleting the surgery (M6R slice 6) must keep them.
- **O3** `casesOn`, no collapsed class (permuted or split): the Ix `casesOn`, same arguments.
- **O4** `below`/`brecOn`/`.go`/`.eq` when the recursor's image is a *selection* (every minor a
  bare variable): permuted blocks and the cross-field-free components of split blocks; motives and
  handlers selected and permuted. Declines for a component with a cross field (O9, A6) and for the
  `brecOn` family of a Prop block whose `below` is Lean's `IndPredBelow` inductive (the Ix `brecOn`
  is over a different inductive; measured on the twins' `Cliques.IP`).
- **O6** `rec`/`recOn` with a selection image, any change kind.
- **O11a** definitional (one `rfl` per `Linear.EqCnstr` member, accepted by the three kernels), run
  before O2 since A6f: its output references `T._sizeOf_inst`, which the input `_sizeOf_N` does not,
  so the edges `all₀._sizeOf_N → T._sizeOf_inst` (each cross target `T` of the recursor's
  component) and `→ SizeOf.sizeOf` are added to the condensation's block dependencies
  (`O11a.addSizeOfEdges`). Where (the drivers differ, harmlessly, since an edge only orders blocks):
  `compileEnvAux` (sequential, waves) and `compileEnvParallelAux` add them under Pass 3 only
  (`CompileDriver.prepareSizeOfScheduling`); `compileDecoratedConsts` (`compileLeanInput`,
  `ix compile-lean`) adds them in both modes after `CondenseM.run`, and again under Pass 3 through
  `compileEnvParallelAux` (`addSizeOfEdges` is idempotent); the Rust compiler under Pass 3 only. No
  cycle: an added path descends strictly through components of one split block; no component or
  representative moves (Tarjan is not re-run). A first, coarser edge set (every `_sizeOf_N` to every
  cross target) closed the cycle `T._sizeOf_k → T._sizeOf_inst → T._sizeOf_k` [measured]. With the
  switch on the library twins' seven `Linear` instances are twin-equal (`pass3`, twins unit)
  [measured, A6f]; those instances are Lean's (`Lean.Meta.Tactic.Grind.Arith.Linear`, in the
  toolchain's `Lean` package), so on the libraries O11a fires in Mathlib's environment, not on
  Init+Std (no changed inductive block). Where O11a's side condition fails on the recursion of
  Lean's `sizeOf` family, it declines to O2's form and records the cause
  (`O11a.declineCause?`, `CompileEnv.p3NonCanonical`): a parametric, indexed or
  universe-polymorphic cross target, a reflexive or indexed cross field, an instance or size
  function not of Lean's shape or not over the occurrence's telescope, a minor that is not a λ over
  its fields and IHs, an absent instance, and "the constructor and minor type of minor `j` cannot be
  read": the split-minor helpers O2 uses cannot place minor `j` (measured on split blocks with an
  evaporated nested auxiliary: EvapClosure, F2, C4 and their twins); the minor itself exists, the
  wording is the code's (the Rust compiler mirrors it).
- **O13a/b**: A5's slot after the occurrence passes.

**Measured (A4, Lean core part of the library, the `pass3` suite's surgery comparison).** Of the
58 Lean-core constants the switch-off output marks as surgered (`Linear`, `Cutsat`, LCNF `Alt`:
`_sizeOf_N` and `_sparseCasesOn`), 51 are byte-identical with the switch on; the other 7 (the
`Linear.EqCnstr._sizeOf_N`, split) have exactly the surgery's expressions and differ only in their
tables: the surgery compiled the dropped arguments of the other components into the reference and
sharing tables (leftover entries, or a different first-occurrence order), Pass 3 derives the tables
from the final term (§4.7 (e), now measured). The Mathlib measurement is in the A4 report.

### 1.6 The proof-justified passes as implemented (A6p, reworked to D1 in M1-b)

Modules `Ix/Compile/Pass/Opt/{Packed,O7,O8,O9,CollapseRec,O10,O12,O11b}.lean`, each with the
five-part docstring whose Faithfulness part is the lemma Phase B formalises. All run under
Pass 3 (the default; not under `IX_PASS3=off`); with the switch off nothing runs, and with it on they need a collapsed or split
block, so Init+Std is unchanged by them (§1.6.3).

**The rule (decision 5, D1, owner 2026-10-05).** Each of these passes produces a term that is
provably equal to the baseline but not convertible to it. So:

- the **Lean name keeps the faithful, convertible form**: the baseline, Lean's term over the images
  (Def 3.6; δβ-convertible to Lean's own term, Def 3.4–3.5), byte for byte what the image path
  gives without the passes;
- the **canonical form is stored under `c._ix`** (`Ix.Compile.Pass.ixFormName`): Lean's constant `c`
  renamed, with `c`'s type, whose value the passes rewrite in place;
- the Lean name is **recorded** in the switch-on non-canonical set with the cause `PJ-FORM-<pass>`
  (`Tests/Ix/Compile/NonCanonical.lean`, `nonCanonicalPasses`);
- **no pass reads a dependent**: the dependents rule of the A6p branch (`Opt/Packed.lean`
  `demotionIn`, `isCarriedDependent`, the `demotion` field of `OptEnv`, `pjAllowed`'s caller scan,
  O11b's `demoted` argument, the cause `DEMOTED`) is removed. A caller of the Lean name keeps working
  because the Lean name keeps its form; a caller that wants the canonical form refers to the `_ix`
  name (callers adapt, never the callee, §6.3). A matcher's equation-compiler companions (`f`,
  `q._f`, `q._sunfold`, the equation lemmas) are ordinary callers of a matcher whose form did not
  change.

**How it runs** (`Ix/Compile/Pass/{Translate,Driver}.lean`).

- The passes fire only in the value of a definition (`RwState.site`), never in a type, a theorem's
  proof or a shared expansion.
- A Lean constant is rewritten with `inPlace := false`: at an occurrence where a proof-justified
  pass applies, the rewrite keeps the baseline (the engine's answer without the site, i.e. the
  definitional passes only) and notes that a pass fired; the definition's canonical form `c._ix` is
  then returned with the block (`BlockRewrite.canon`).
- `Driver.compileCanon` rewrites each canonical constant **in place** (`inPlace := true`), adds the
  helpers its rewrite references (O9/O10: the re-typed handler `p._ix_retyped.s` for Lean's `p.s`; O12:
  `f._ix.fg`). **No reference is renamed**: a canonical constant refers to its dependencies by
  their Lean names, so it is well typed whatever forms they have. A first version redirected every
  reference `d` with a compiled `d._ix` to it; the certified checker rejected the resulting
  `noConfusionType._ix` of several corpus types (`application type mismatch`: a constant whose type
  mentions `ctorIdx` applied to a term built with `ctorIdx._ix`; a raw renaming is not
  conversion-preserving, R2 F7). A caller that wants a canonical form refers to it itself: O9's
  `c._ix` to its handler, O12's to `fg`, O11b's `noConfusion._ix` (typed over
  `noConfusionType._ix`, one decision). O10 and O12 compare handlers through their references'
  canonical forms (`OptEnv.canonAddrOf`, `Driver.ixFormOf`). A reserved name that is already bound must be bound to the
  same bytes (O12's `fg`, emitted by both functions' blocks); a different binding fails the compile.
- The clique hook's canonical constants (`Driver.cliqueRewrite`) are rewritten with
  `inPlace := false`, so no proof-justified pass fires inside a transported clique.

#### 1.6.1 The passes, their canonical forms and their proofs

Every pass below is **proof-justified**, not definitional: `c._ix = c` is a theorem, and the two
values are convertible only at closed constructor-headed arguments (both sides reduce by ι, which is
what the value pins check). The proof term in each case is the corollary of the pass's lemma: `funext`
over the binders above each rewritten occurrence, then `congrArg` with the lemma at the occurrence
(the occurrences are disjoint subterms and the arguments are copied).

| Pass | Lean name `c` keeps | `c._ix` | Lemma (the proof term's core) | Why not convertible |
|---|---|---|---|---|
| O7 `rec`/`recOn` over a collapsed, unsplit block, motives and minors agreeing per class (α-equal under the collapse renaming) | `unwrap_p (ρ.{max 1 u} ps M⃗ N⃗ is t)`, the packed image | `ρ.{u} ps P⃗ N⃗′ is t`, duplicates dropped | `unwrap_p (D t) = S t`: induction on `t` with `ρ` at the Prop motive `∀ p, unwrap_p (D t) = S t`; each case ι on both sides, then `congrArg (min fs)` over the hypotheses | `D` and `S` are stuck at an open major; they agree only after ι |
| O8 `casesOn` (so matchers and Lean's helpers built on it) of a collapsed or lifted member | Lean's `casesOn` value over the packed image | the class's Ix `casesOn`, same arguments | `L … t mins = R … t mins`: case analysis with `ρ` at a Prop motive; each case `Eq.refl` (both sides `min_q fs` by δβι) | the packed side is stuck on `unwrap_p` at an open major |
| O9 `brecOn` over the component `{x}` of a split block with a cross field | the image's `brecOn` with Lean's handler `c._f` | `ρ.brecOn ps msel is t c._ix_retyped._f`, the handler re-typed over the Ix `below` and re-pathed (`.2ʲ.1.1 ↦ .2ʲ′.1.1`) | `B is t = B′ is t`: induction with `ρ`, both `brecOn` equation lemmas (Lean's `x.brecOn.eq`, Pass 2's), `congrArg` over the component's fields | the two `below` values have different layouts (Lean's has the cross leaves) |
| O10 `brecOn` over a collapsed, unsplit block, motives and re-typed handlers agreeing per class | the image's `brecOn` | `ρ_x.brecOn ps P⃗ is t F⃗′`, one motive and one handler per class (the twin's single function) | `B_i t = B′_k t`: simultaneous induction with `ρ` and both equation lemmas | as O7, through the packed `below` |
| O12 `brecOn` over a collapsed pair (one class of two) with different arms | the image's `brecOn` | `(fg t).(pos x)`, `fg := λ t. ρ.brecOn Pair t ⟨F′₀, F′₁⟩`, the pair ordered by content | `(fg t).1 = B₀ t ∧ (fg t).2 = B₁ t`: joint induction with `ρ` | `fg` builds a pair Lean's term never builds |
| O11b `noConfusionType`/`noConfusion` of a split-off one-constructor enumeration (unit pass) | Lean's general form | the enumeration form `λ P x y. P → P`, `λ h p. p` (the latter typed over `T.noConfusionType._ix`) | `G = E` by `funext` and case analysis (`Eq.refl` per constructor); `g` and `ε` agree along it (`subst`, case analysis) | `G` and `E` differ at variables (`T.casesOn` is stuck) |

Side conditions and fallbacks are in the modules. When a side condition fails, no `_ix` form is
emitted for that occurrence (the faithful baseline stays everywhere). O11b with two or more
constructors declines (`PENDING-NOCONFUSION`: the enumeration form needs `T.ctorIdx`,
`noConfusionTypeEnum` scheduled before the constant, an edge the input graph lacks). O12 declines
for classes of three or more.

#### 1.6.2 Interaction with the clique hook (found in M1-b)

On this line the A5 clique hook runs before the occurrence passes (`Driver.prepareBlock`) and
transports a structural clique over a changed block under its Lean names (D2). A transported
member's value contains no image occurrence, so O9, O10 and O12 never fire on it: they fire only on
a structural function whose clique the hook leaves in Lean's form, and on explicit `brecOn` uses
that are no clique. Measured on the fixtures with the clique hook deciding from the clique's own unit
(M1-a, no demotion): all six cliques of `O10O12Collapse` (C5 `A.h`/`B.k`, `A.f`/`B.g`, the permuted
`Perm.A.f`/`Perm.B.g`, C8's `A.f`/`B.f`/`C.f` and `A.h`/`B.h`/`C.h`, and the canonical presentation's
`C8.Can.X.h`/`C.h`) are transported, so O10 and O12 do not fire there (their collapsed twins' single
functions need the deferred O17, recorded `PENDING-COLLAPSE`); `O9Split` has no clique of two or more
members (`A.len`, `A.sum` are single functions, and Lean compiles `B.cnt b` inside `A.cnt` as a call,
so `A.cnt` is no clique with `B.cnt`), so the hook has nothing to transport there and O9 fires on
`A.len`, `A.sum`, `A.cnt`: removing the demotion did not change that. An explicit `brecOn` with hand-written handlers does not reach O10 either: the
elaborator writes a `below` projection as `PProd.fst` over the unfolded `below` (a raw Lean
recursor), which the re-typing does not follow (measured, then dropped from the fixture). So **O10 and
O12 have no firing fixture on this line**; O9 fires on single structural functions over a split block
(no clique). Whether O9, O10 and O12 are still wanted next to the transport and
O17 is an open question for the orchestrator.

#### 1.6.3 Measured
Library (the `jcb/ix-cc-m1b` gate run, Lean 4.34.1): Init+Std with the switch on is **byte-identical to
the base line's switch-on output** (sha256 `a2e22ee7…`, 256,128,289 bytes, 115,942 blocks), so these
passes touch **0** Init+Std names and add **0** `_ix` constants there (no collapsed block, no split
block with a cross-field structural recursion or a one-constructor enumeration member); with the
switch off both compilers give `468ad7ae…` (ALIGNED).

Fixtures (`Tests/Ix/Compile/Pass/{O7Collapse,O8Cases,O9Split,O10O12Collapse,O11bNoConfusion}.lean`,
the `pass3` suite): 17 `_ix` twin pairs byte-equal with the switch on (O7 3, O8 5, O9 5, O11b 2, plus
two untouched constants); every Lean name keeps the pre-pass baseline (by construction; cross-check:
`PassO8.Src.A.isNil'` has the address the A6p branch recorded for its demoted, i.e. baseline, form);
value pins by `rfl`; with the switch on the certified checker accepts every constant, `_ix` included;
decompile complete. The switch-on non-canonical set of the passes (`nonCanonicalPasses`, exact): 13
`PJ-FORM-<pass>`, 12 `INHERITED`, 7 `PENDING-COLLAPSE` (O10/O12 under the clique hook), 2
`PENDING-NOCONFUSION`, 2 `ORDER-STMT` (Lean's `_f` over Lean's `below`).
---

## 2. Canonical form, defined

What a compiled name denotes, case by case, and what a checker may rely on is §11 (the output contract);
this section defines the canonical form those cases refer to.

### 2.1 Components (Def 2.1)

- **Graph.** There is an edge `x → y` when the constant `y` occurs in `x`:
  - for an inductive: in its type, plus an edge to each constructor name;
  - for a constructor: in its type, plus an edge to its inductive;
  - for a definition, theorem or opaque: in its type or its value;
  - for a recursor: in its type, plus edges to the rule constructors and to the constants of the
    right-hand sides;
  - a projection `proj S i e` gives an edge to `S` (`Ix/GraphM.lean:26-71`; Rust
    `get_constant_info_references`).
- **Components.** The SCCs of this graph, by Tarjan, now the total `Ix.Compile.Canon.condensation` (`Ix/Compile/Canon/Graph.lean:173`), presented through `Ix/CondenseM.lean:43-86` byte for byte as before.
  - For an inductive block, the inductive → constructor → (constructor-type references) path makes the
    component of `T` exactly the SCC of Def 2.1's member graph: there is an edge `Tᵢ → Tⱼ` when `Tⱼ`
    occurs in the type of `Tᵢ` or of one of its constructors [argued]. Lean declarations cannot
    reference a later declaration, so a member is reachable only from its own block.
  - Recursors are never in a member's component: nothing in the block references them.
- **Kinds.** Lean's mutual declarations are kind-homogeneous: all inductives, or all definitions, of
  one safety. A safe constant cannot reference a `partial` or `unsafe` one. Hence every SCC of Lean
  input is kind-homogeneous and safety-homogeneous [argued]. §3 relies on this.
- **Unaffected by traversal order.** The *set* of members of a component does not depend on the
  traversal order. The SCC *representative* `lo` (the Tarjan root) does
  (`Ix/CondenseM.lean:1-22, 43-86`), and so does the member iteration order (a `Set`): neither may reach
  the output (§6).
- **Definitions.** Safe structural and well-founded cliques are acyclic after elaboration: each
  member is a non-recursive definition over `brecOn`, `WellFounded.fix` or `Lean.Order.fix` (MUT
  §2). So definition SCCs come only from `partial`/`unsafe` blocks and their `_unsafe_rec`
  companions. Safe cliques are canonicalised on their specifications (§2.7), not on the graph.

### 2.2 Classes (Def 2.2) and the structural key

A partition `P` of a component `K` is **consistent** when any two members in one class are equal
under the **structural key** once every occurrence of a member of `K` is replaced by its class and
every other constant by its address. The **classes** are the coarsest consistent partition.

The key compares, lexicographically, in this order.

**Kind tag:** definition < inductive < recursor.
- Rust implements this (`crates/compile/src/compile.rs:3586-3592, 3618`).
- Lean does not (defect C1, §3.4); fixed in A2.

**Definition** (`Ix/CompileM.lean:2153-2158`; `compile.rs:3369-3405`): `DefKind`, universe-parameter
count, type, value. Safety and hints are not compared. Hints are per name in `Named.hints`.

**Inductive** (`Ix/CompileM.lean:2181-2192`; `compile.rs:3468-3530`):
- universe-parameter count, parameter count, index count, constructor count, type;
- then the constructors pairwise (`Ix/CompileM.lean:2162-2178`): universe count, constructor index,
  parameters, fields, type;
- Rust additionally compares `is_rec` and `is_unsafe` first (C6, §3.4). The canonical key is
  content-only, and Rust drops both keys at catch-up (owner decision on Q4).

**Recursor** (`Ix/CompileM.lean:2199-2212`; `compile.rs:3536-3580`): universe count, parameters,
indices, motives, minors, `k`, type, rules (field count, right-hand side).

**Expression** (`Ix/CompileM.lean:2054-2140`; `compile.rs:3232-3365`): a structural walk with the
constructor-tag order mdata(semantic) > … and bvar < sort < const < app < lam < forallE < letE < lit
< proj. Within it:
- binder names and binder info are ignored;
- non-semantic `mdata` is stripped;
- semantic-contract `mdata` compares by `Contract.orderKey` (`Ix/SemanticContract.lean:53`), then by
  its body;
- `bvar` by index;
- levels by `compareLevel`: zero < succ < max < imax < param, with parameters by position in each
  side's own list (`Ix/CompileM.lean:1983-2009`);
- **constants**: level arguments first, then equal names are equal, then
  - two in-block names compare by current class index. This is the **weak** comparison: its
    result is flagged `strong = false`;
  - an in-block name is less than an external one;
  - two externals compare by compiled address (`Ix/CompileM.lean:2085-2104`). An unresolved address
    is an error, never a fallback to the name (`compile.rs:3206-3227`);
- projections compare the structure the same way, then the field index, then the body
  (`Ix/CompileM.lean:2122-2135`).

**Context.** The context is `MutConst.ctx` (`Ix/Mutual.lean:95-121`):
- member ↦ index of its class;
- constructor ↦ `#classes + offset`, with offsets reserved per class by the class's maximum
  constructor count.

Lean blocks never reference their own constructors inside member or constructor types, so
constructor entries never decide a comparison [argued].

**Phase A decision: levels are compared after `canonUniv`.**
- Today `compareLevel` reads syntax, while compilation canonicalises afterwards
  (`Ix/CompileM.lean:417`).
- So two members equal after canonicalisation but spelled differently fall in different classes.
  That is a gap in minimality, and the order between them follows the spelling.
- Comparing `canonUniv u` (`Ix/IxonUniv.lean:379`) with parameters by position makes collapse
  coincide with equality of compiled content [argued].
- This holds whether or not `canonUniv` is complete for level equivalence; completeness is [open]
  and is not needed here.

### 2.3 Canonical order (Def 2.3), as a procedure

**Definition (refinement).** Let `seed` be a total order on the members of `K` (§2.8 fixes it). Then:

```
classes₀ := [K sorted by seed]
classes_{n+1} := concat over C in classes_n (in order) of
                   if |C| = 1 then [C]
                   else groups(sortBy (cmp_{ctx(classes_n)}) C)   -- stable; groups of equal neighbours,
                                                                   -- each group in seed order
stop at the first n with classes_{n+1} = classes_n
```
- The canonical order of `K`'s classes is the final list.
- The representative of a class is its first member in seed order.
- **Seed (Phase A, unchanged from today):** the blake3 hash of the name
  (`Ix/Environment.lean:148-153`; `compile.rs:3734`), so the representative is the member with the
  least name hash.
  - The owner decided to keep this (2026-10-03). Collapse makes member order irrelevant for
    anonymous constants, and the representative decides only metadata. Names belong in metadata,
    not source order.
  - §3.3 shows that the class order does not depend on the seed.

- `cmp_ctx` is the key of §2.2 under the context `ctx`.

Today's implementation:
- Lean `sortConsts` (`Ix/CompileM.lean:2246-2353`): the stopping rule is an unchanged class count,
  with fuel `|K| + 1`;
- Rust `sort_consts` (`compile.rs:3723-3790`): the stopping rule is an unchanged class list;
- the two rules agree, because refinement only splits classes and keeps each group in place [argued].

**Not a declarative fixed point.** The order is the *history* of the splits: once two classes are
separated, their relative order is never revisited. In general the final list is not the result of
sorting the final classes by `cmp_{ctx(final)}`. A declarative definition ("an ordered partition
fixed by sorting under its own indices") can have several solutions: two classes whose contents
mention each other symmetrically can be self-consistent in either order. The refinement picks one of
them deterministically. **The canonical order is therefore defined as the output of this procedure**,
and Phase B proves properties of the procedure, not of a declarative characterisation [argued].

**Consequence for the kernels (BELOW-ORDER, A6f).** The symmetric case can also be inconsistent in
*both* orders: when two members differ first in a mutual cross reference (compared weakly, by class
index) and only later in a strong position, the cross references compare weakly `Greater` under the
final classes whichever member comes first, while the refinement ordered the pair by the strong
difference it met in the round where both were one class. The kernels' single-pass canonicity gate
(`validateCanonicalBlockSinglePass` in `Ix.Tc`, `validate_canonical_block_single_pass` in
`crates/kernel`) formerly accepted a strong `Less`, fell back to the full refinement on a weak
`Less`, and rejected every `Greater`. It therefore rejected such blocks in every stored order,
against this section's definition. Reproducer `Tests/Ix/Compile/ValidateLeanSwap.lean`
(`SA | mk : SB → Nat → SA`, `SB | mk : SA → Bool → SB`): the Rust producer with the switch off emits
it, and `ix check-rs` and `ix check-lean` reject it in meta mode ("adjacent pair at position 0
compares Greater"), anonymous mode passes [historical measurement, A6f]. The approved repair makes
weak `Greater` fall back to full refinement in both executable kernels, just as weak `Less` does.
The fallback accepts only singleton classes in precisely the stored order; strong `Greater` and
uncollapsed equal members still reject. Rust and Lean unit tests cover these negative cases and the
canonical cross-reference pair; `ValidateLeanSwap` and `PropCollapse` pass phase 4 in both switch
states [measured, Phase A A5R]. `IxC/Kernel/**` has no corresponding fast path and is unchanged.
The separate `Ix/Ixon/BlockOrder` adapter already uses full refinement for structural primary-block
order and motive order for all-recursor blocks; nested auxiliary discovery order is unchanged.

**Phase A decision: addresses at the first difference (today's comparator).** An external reference
compares by address wherever two members first differ (`Ix/CompileM.lean:2098-2104`), interleaved
with the structure. The order therefore depends on the Ixon format version whenever the first
difference is an external constant.

The owner accepts this: a format-version change is a breaking change anyway, and the single-key
comparison is faster.

*Considered and rejected:* a two-key comparator `(k₀, k₁)`.
- `k₀` treats every external constant as equal; `k₁` is today's key.
- It leaves the partition unchanged and moves only the order.
- Measured effect [A1C §1.3]: 0 member orders move in Mathlib or Init+Std, but 59 of 170 specified
  Mathlib clique orders move (4 of 9 in Init+Std), because clique bodies mention external constants
  early.

### 2.4 Member content (Def 2.4; D3/D16)

The canonical declaration of a class is its representative's declaration, changed as follows:
- **universe parameters:** the Lean block's whole list, in order;
- **parameter count:** the block's;
- **result sort:** as declared;
- **references:** to other members of the component by class; to everything else by address.

Elimination universe, `K` target, `isRec`, reflexivity and structure-likeness are computed by the
kernel on the Ix block, never inherited from Lean.

Nothing is pruned. A split member is therefore not the same constant as that member declared alone
when it ignores a block universe or parameter, or when its declared sort is larger than needed (ORA
split cause (a), `UnivSplit` [measured]).

The content does not depend on which member represents the class [argued]. Members of one class are
equal under the key, and every compared datum has a canonical compiled form:
- levels by position, after canonicalisation;
- in-block references by class;
- externals by address;
- binder names and non-semantic `mdata` are metadata.

### 2.5 Nested auxiliaries in discovery order (Def 2.5; D2)

Lean's kernel replaces nested occurrences by auxiliary inductive types in `elim_nested_inductive`
(C++ `src/kernel/inductive.cpp:985-1180` at v4.34.1, read by A1C; the ports cite it as `:963-1077`).
 Ix ports it twice:
- Lean: `Ix/AuxGen/Nested.lean:485-729`;
- Rust: `crates/compile/src/compile/aux_gen/nested.rs:172-700`.

Both claim to mirror it line by line (`nested.rs:239, 486-487, 1070-1073`).

**Definition (discovery order).** Input:
- members `m₁ … m_n` in a fixed order;
- the block's `np` parameters and levels.

Procedure:
- Let `Q := [m₁, …, m_n]`, a queue of types, and `seen` an empty map from occurrences to
  auxiliaries.
- For `q = 0, 1, …` while `q < |Q|`, for each constructor `c` of `Q[q]` in constructor order:
  1. instantiate the first `np` binders of `c`'s type with the block parameters;
  2. walk the remaining type **pre-order**:
     - application: function, then argument;
     - binder: domain, then body;
     - `let`: type, value, body;
     - `proj`: the body;
     - `mdata`: the body;
     - a node that was replaced is not descended into (`Nested.lean:596-627`; `nested.rs:172-238`);
  3. at a node `e = I As idx` that is an **occurrence**, replace `e` (rules below);
  4. replace `c`'s type by the rewritten type.
- A node is an occurrence when all of the following hold (`Nested.lean:485-516`):
  - `I` is an inductive whose name is not in `Q`;
  - `|As| ≥ np(I)`;
  - some parameter argument mentions a name in `Q`;
  - the parameter arguments, rewritten into block-parameter space, contain no loose bound variable
    and no free variable other than a block parameter. A parameter that depends on a constructor
    field disqualifies the node.
- **Replacing an occurrence:**
  - if `I As` (the key, in block-parameter space) is in `seen`, replace `e` by `seen[I As]` applied
    to the block parameters and `idx`;
  - otherwise, for each `J` in `I.all`, in order: append to `Q` the auxiliary type
    `aux_k := J.{lvls} As`, with `J`'s constructors specialised, result heads renamed to the
    auxiliaries, and `k` a global counter. Record `seen[J As] := aux_J` for **every** `J` (Lean's rule; see below). Replace `e` by `I`'s
    auxiliary (`Nested.lean:526-590`).
- The **discovery order** of the auxiliaries is their order in `Q` after the members. Lean names the
  recursor of the `k`-th as `m₁.rec_k`.

Two consequences:
- An auxiliary's own constructors are walked only when the queue reaches it. Auxiliaries found
  inside auxiliaries therefore come after every auxiliary found from an earlier queue entry.
- The order is breadth-first over types and pre-order within one constructor. **The old plan's
  "depth first into new auxiliaries" (Def 2.5) is incorrect** and is replaced by this definition.

**Discovery order over the canonical block.** Run the definition with:
- `m₁ … m_n` := the class representatives of one component, in canonical order;
- every reference to a non-representative member rewritten to its representative first
  (`aliasToRep`, `Nested.lean:678-696`);
- members of other components counted as external: they are not in `Q`;
- an external group opened by a new occurrence `I As` taken as **`I`'s canonical component**: its
  class representatives in canonical order, every name of a class registered as seen (A2-order).
  This is what the kernels can recompute from the stored Ixon, where `I`'s block holds exactly
  that component in that order and Lean's `I.all` is not available. It equals `I.all` whenever
  `I`'s block is an identity block (no split, no collapse, Lean's order). In Init, Std and
  Mathlib the choice moves nothing [measured, A2-order: Init+Std is byte-identical and every
  Mathlib root of the address diff lies in the 16 predicted blocks]. Where it differs, the nesting block's permutation
  records the difference and the block is not an identity block. A Lean group that Ix splits
  opens only `I`'s component, so Lean's auxiliaries for the other components have no canonical
  position (`computePerm` refuses such a block; none occurs in the libraries).
- occurrences deduplicated **up to compiled addresses** (`Canon.addrKey`: every constant outside
  `Q` replaced by its address, binder names and `mdata` erased), so that `List C₁` and `List C₂`
  with `C₁`, `C₂` collapsed or content-equal share one auxiliary, as in the kernels' walk, which
  sees only addresses (A2-order). The structural sort merged such auxiliaries before; Lean's walk
  keeps both, and the permutation maps both of Lean's positions to the one canonical auxiliary.
  `computePerm` matches an exact spelling before an address-equal one.

Consequences:
- two occurrences `List A` and `List B` with `A ≅ B` become one key, so one auxiliary (merged nested
  auxiliaries);
- an occurrence whose parameters mention only other components is not an occurrence (evaporation,
  §2.6);
- for a block whose canonical order is Lean's `all` order, with no split and no collapse, the
  procedure is Lean's own, so the block is an identity block [argued].

Evidence:
- [measured] CEN:28: every unchanged block's regenerated auxiliaries are α-equal to Lean's, 21,136 of
  21,136 in Mathlib's closure, including nested blocks whose structural order coincided with Lean's.
  This is indirect evidence that the port's source walk reproduces Lean's numbering. The direct gate
  is the oracle on every nested fixture (Phase A §5.3).

**Deduplication of sibling occurrences: Lean registers every `J As`.**
- Lean's kernel records `seen[J As]` for every member `J` of the external group
  (`m_nested_aux.push_back` per `J`, `src/kernel/inductive.cpp`, v4.34.1) [A1C §4 item 4]. The
  definition above is corrected accordingly: **record `seen[J As] := aux_J` for every `J`**, not
  only for `I`.
- Both Ix ports register only the head `I As` (`Nested.lean:542-546`; `nested.rs:369-373`).
  - On `T | mk : Tree T → T`, with `Tree/Forest` mutual, they create 4 auxiliaries where Lean has 2.
  - Production `ix compile` rejects the block (`InvalidMutualBlock`, `numNested` 2 against 4)
    [measured, A1C item 7].
  - No library block contains such an occurrence [measured, A1C §4].
- The fix is assigned to A0 (owner decision on Q5).

**Validation** [measured, A1C §0.3–0.5, §1.3]:
- The corrected definition was checked against `elim_nested_inductive_fn`
  (`src/kernel/inductive.cpp:985-1180`, v4.34.1).
- It matches `all₀.rec_N` in auxiliary count, heads, levels and parameters on 98 of 98 nested
  blocks: 55 fixtures, 3 in Init+Std, 40 in Mathlib.
- Under discovery order, Mathlib's changed blocks fall from 20 today to 6.

**What changed (A2-order, 2026-10-03).** Discovery order replaced the structural sort everywhere:
- the Lean compiler: `Rules.compiler := Rules.phaseA`; `sortAuxByPartitionRefinement` takes
  `Canon.canonicalAuxOrder`, the identity on the canonical expansion (`expandNestedBlock … true`,
  external groups from `CompileEnv.blocks`); `computeAuxPerm`, the stored `AuxLayout.perm`, the
  `rec_{j+1}` registration, evaporation and the call-site plan predicate follow unchanged;
- Rust `sort_aux_by_partition_refinement` returns the identity on `expand_nested_block_canonical`'s
  output (the identity-marker sort is deleted);
- the kernels: `canonical_aux_order` (Rust) and `canonicalAuxOrder` (`Ix/Tc/Inductive.lean`) are
  deleted; `build_flat_block`/`buildFlatBlock` open a new occurrence's whole stored block in
  canonical order (Lean's rule) when checking a compiled environment, and the flat block is used
  in discovery order;
- the certified modeller's "largest family first" accepts discovery order unchanged (its comment
  is updated); the certified `BlockOrder` variant checks a recursor block in motive order and never
  encoded the auxiliary order, so it is unchanged and its audit is not re-recorded.

**Lean-generated inductive blocks: the `IndPredBelow` family (A3V-IPB; decided in A6f).** For a
Prop block, Lean's `IndPredBelow` declares one `below` inductive per motive of the block's recursor
(`x.below` per member, then `all₀.below_j` per nested auxiliary) as one mutual block, with its own
recursors and `casesOn`. Pass 2 builds the Ix family over the canonical block in motive order, and
Pass 1 then orders the family as a block of its own. On nested shapes Pass 1's order differs from
Lean's even when the parent is unchanged (`Tests/Ix/Compile/ValidateLeanIPB.lean`: Lean
`[A.below, B.below, A.below_1]`, Ix `[A.below, A.below_1, B.below]`), so the family is a *permuted*
Lean-generated block, and before A6f Lean's `A.below.rec` named an Ix recursor of another type (the
validator's oracle leg found it).
- *Choice.* Keeping Lean's order for Lean-generated families is excluded: the kernels check every
  all-inductive block against the comparator order (§2.3), so the family stored in Lean's order is
  rejected exactly where Pass 1 orders it differently. Treating the family as a **changed block** keeps
  the Ix family canonical (a function of the canonical parent, then of Pass 1) and byte-identical to
  the switch-off output, and moves only names (Q2). By §0.1 this is the choice.
- *Rule (under the switch).* Pass 3's changed-block predicate covers the family: when the stored
  positions of Lean's family names are not Lean's order, the family's inductives and constructors
  keep Lean's names (as members of any permuted block do), its Ix `.rec`/`.casesOn` are displayed
  `x.below._ix.rec`/`x.below._ix.casesOn`, and Lean's `.rec`/`.casesOn` denote their images
  (`Ix.Compile.Pass.editPermutedBelowFamily`). A changed Prop parent was already covered (its
  canonical family moves to display names and Lean's own family compiles as its own block, which is
  then a changed block by the same predicate).
- *Switch off.* Unchanged (Rust is not mirrored for Pass 3): the defect stays recorded as A3V-IPB
  until the switch flips.
- [measured, A6f] With the switch on, `ix validate-lean --local` passes every phase on
  `ValidateLeanIPB` (phase 7: 2 changed blocks, 10 images, 7 rules by `rfl`) and on `Neighbours`
  (7 changed blocks, 88 images, 30 rules). WB-B6 (`RecAlias.PA.below`) and WB-B9
  (`UnsafeI.UNestNeg.rec`) are single-member blocks and do not share the cause: WB-B6 is Pass 2's
  generator form (a recursive field behind a reducible alias), WB-B9 the recursor block's packaging.

**Default path: the CORPUS-IPB refusal (`REFUSED-IPB-COLLAPSE`; owner, 2026-10-06, option 1; M1-j).**
With the switch off, the stored meaning of a Lean `IndPredBelow` name is its `Named.original`: the
promotion compile of Lean's own `.below` block (`compileConstNoAuxPure`, Rust `compile_const_no_aux`,
provenance only) with each `.below` head's call-site plan applied, and each plan keeps the motive of
its own member. When a collapse merges members whose `.below` inductives are alpha-equivalent before
surgery (`M3_P_alpha2p1`: `A`, `B` = `z | s : C → _`, so `A.below` ≅ `B.below`; `M4_P_mixed`), the
promotion compile puts those `.below` inductives in one class, whose payload is the representative's
data: the other member's constructors then read back with the representative's motive
(`A.below.z : A.below motive_2 motive_2 motive_3 A.z`, Lean's `A.below motive_1 motive_2 motive_3
A.z`). All kernels accept that type, and no call site exists for D13 to check.
- *Rule (switch off, both compilers).* In the promotion compile, an inductive member of an
  equivalence class must compile to its representative's data; otherwise the block is refused with
  `REFUSED-IPB-COLLAPSE: collapsed Prop members' IndPredBelow family would be stored with one
  member's motives: '<member>' and its class representative '<rep>' compile to different data in
  Lean's original form of the block` (`Ix.CompileM.refuseIpbCollapse`; Rust `compile_mutual`), a block
  failure of the `.below` block, as D13's refusals are.
- *Scope.* A collapsed Prop pair whose `.below` members stay distinct (`PropCollapse`: `P.step : Q →
  P`, `Q.step : P → Q`; the all-alpha ring) and the `Type` version of the shape (`F1_Collapse2p1`,
  whose `.below` are definitions) compile as before; a Prop block that collapses nothing never has a
  multi-member class there. Fixtures: `aux-cert` `IPBCollapse2p1`, `IPBMixed` (refused) and
  `IPBCollapseNone` (valid neighbour).
- *Switch on.* Unchanged: a changed block registers no surgery plan, so the check cannot fire; Pass 3's
  images refuse both corpus shapes (`image: hypothesis motive N not in its slot's class`), which is
  a Pass 3 item of M1. The shape does not occur in Init+Std or Mathlib (byte-identical outputs).

### 2.6 Evaporation

After a split, Lean's auxiliary for `I As` **evaporates** from component `K` when `As` mentions no
member of `K`. By §2.5 it is then not an occurrence in `K`'s walk.

Its Lean recursor `rec_j` has no Ix counterpart in `K`. Its image eliminates with `elim(t)` of Def
3.3:
- the recursor of another component whose expansion contains `tr_N(t)`;
- else that of a container inside `t`;
- else that of `t`'s head.

Census (`exp-census-1.md:24`) [measured]: no evaporation in Init, Std, Lean, Batteries or Mathlib.

### 2.7 Definition cliques (M.1–M.6)

- **M.1, clique.**
  - For structural and well-founded recursion: `EqnInfo.declNames` (`.../Structural/Eqns.lean`,
    `.../WF/Eqns.lean:18-46`).
  - For a `partial` or `unsafe` block: the block, or its `_unsafe_rec` companions. These are
    canonicalised as SCCs (§2.1) and need no specification.
  - `partial_fixpoint`: its `EqnInfo` (`.../PartialFixpoint/Main.lean:220`).
- **No specification** for theorems or Prop-valued definitions. `EqnInfo` is not registered for them
  (`.../Structural/Main.lean:202-213`; `.../WF/Eqns.lean:41-42`), and `abstractNestedProofs` skips
  theorems (`.../PreDefinition/Basic.lean:120-128`).
- **M.2, specification.** For a member `f`: (kind and safety, universe count, type, method, value,
  pinned choices). The value is `EqnInfo.value`, after nested-proof abstraction for definitions.
  Recursive calls are references to clique members. The pinned choices are:
  - structural: `recArgPos` per function;
  - well-founded: the per-function measure term chosen by `termination_by` or GuessLex.

  GuessLex attaches function-index measures to each function as literals:
  `.func i` becomes `if i = funIdx then 1 else 0` inside *that function's* tuple
  (`.../WF/GuessLex.lean:762-774`). Re-indexing therefore happens automatically when the measure
  travels with its function.
- **M.3, classes and order.** §2.2–2.3 applied to specifications, with "constructors" replaced by
  "value and pinned choices".
  - **Phase A decision (Q8, owner 2026-10-03):** the pinned choices compare *last*.
 A GuessLex or
    `recArgPos` tie-break that differs between presentations then changes the order only when
    everything else ties.
  - Matchers in values are compared by address. Original matchers are content-canonical; only their
    owning name follows elaboration order (`src/lean/Lean/Meta/Match/Match.lean:1074-1122`, per MUT
    §1.6) [measured: MUT, F9 `names.tsv`].
- **M.4, canonical clique.** One representative per class, in canonical order, with member
  references redirected to the representatives.
- **M.5, canonical elaboration.** **Defined as the output of Ix's repacking function** (§5), which is
  the plan's Δ8. Lean's pre-definition pipeline run on the canonical twin is the oracle.
  - Structural: the packing within each type former in canonical order (`Positions.groupAndSort`,
    `.../Structural/Basic.lean:59-66`); fixed parameters from the first canonical member
    (`.../FixedParams.lean:256-299`).
  - Well-founded: `PSum` summands in canonical order, Lean's per-function measures, and re-stated
    decreasing obligations.
  - `partial_fixpoint`: `PProd` factors in canonical order.
  - New constants carry the reserved `_ix` component (D14).
- **M.6, changed clique.** A clique is changed when any of these holds:
  - Lean's clique order differs from the canonical order;
  - a class has two members;
  - the clique ranges over a changed inductive block.

  Lean's clique order is Tarjan's DFS push order from the first member in source order
  (`src/lean/Lean/Util/SCC.lean:69-106`, per MUT §1.1).

### 2.8 The Phase A decisions, with reasons

| Decision | Today | Phase A | Reason |
|---|---|---|---|
| Level comparison | syntactic (`CompileM.lean:1983-2009`) | after `canonUniv`, parameters by position | collapse = equal compiled content; no level-spelling dependence (§2.2) |
| Seed order | blake3 of the name (`Ix/Environment.lean:148-153`; `compile.rs:3734`) | **unchanged** | the seed affects only the order inside a class, i.e. metadata (§3.3), and names belong in metadata. Seed-independence measured [A1C §1.3] |
| Representative | least name hash (`compile.rs:4318-4330`) | **unchanged** | equal content within a class (§2.4); metadata only |
| Address use | first differing external (§2.3) | **unchanged** | faster; format-version flips accepted. `(k₀, k₁)` considered and rejected (§2.3) |
| Kind tag | Lean: none (C1) | definition < inductive < recursor | antisymmetry on all inputs (§3.4) |
| Cache | Lean: unnormalised (C2) | stored for `(min, max)`, with the result reversed when swapped, as in Rust | latent-bug fix, no byte change (§3.4) |
| `is_rec`/`is_unsafe` keys | Rust only (C6) | none: content-only key | the flags are block-wide [measured, A1C §0.8]; Rust drops them at catch-up |
| Nested order | structural sort | discovery order over the canonical block (§2.5) | equals Lean on identity blocks; address-free |
| Packaging | one block per auxiliary kind | one constant per auxiliary (D6); recursor blocks of Lean's form in flat order | minimality; packaging-only differences 382 + 28 before [measured, CEN:27, v3], 363 + 28 at `v4341`, **0 + 0** after [measured, A2 migration, `canon-census --originals`] |

**The A2 migration (2026-10-03).** The rows "Level comparison", "Nested order" and "Packaging" are
implemented in both producers and landed in one migration commit. Library sha256 (`ix compile` and
`ix compile-lean --rust-check`, byte-identical; Lean 4.34.1):

| | before (`*-v4341.ixe`) | after (`*-a2.ixe`) | moved names (packaging / nested order / cascade) |
|---|---|---|---|
| Init+Std | `adb7e1840b27…` | `468ad7ae6a5a…` | 28 (28 / 0 / 0) |
| Mathlib | `d1aa3de54004…` | `0758ba0507a7…` | 16,321 (920 / 765 / 15,106; 470 of the 1,215 roots are both) |

The level rule moves nothing. No pinned Init address and no `Tests/Fixtures/ixon-v4` address
moves; the certificate environment is unchanged. `canon-census`: 6 changed Mathlib blocks, 0 in
Init+Std.

**Status of the decisions at `564d03f0`:**
- **Kept** (owner Q1/Q2): today's comparator (first-difference addresses), the name-hash seed and
  the least-name-hash representative.
- **Fixed in the Lean compiler:** C1 and C2, through Pass 1's `portFixes` (A2O §1.1).
- **Still in Rust:** C6 (`is_rec`/`is_unsafe`, `crates/compile/src/compile.rs:3780`), until the
  catch-up PR.
- **Done:** D2 (discovery order) and D6 (one constant per auxiliary) [measured, A2M].
- **Packaging detail** [A2P §0; measured, A2M]: every regenerated auxiliary definition is compiled
  as one SCC per auxiliary (`auxComponents`/`aux_components`); every SCC measured is a singleton.
  - The recursor family (`rec`, `rec_N`) stays one block, because its members reference one another.
    So does the Prop `.below` family with `.below.rec`.
  - A recursor block compiled from Lean's declarations (the compile of originals, and decompile's
    verification recompile) is laid out in its family's flat order (`orderRecursorFamily` /
    `order_recursor_family`). No stored recursor address moves.
- **New references:** `initstd-a2.ixe`, `mathlib-a2.ixe` and `links-a2/` [A2M §0].

---

## 3. The comparator is a total preorder

### 3.1 What runs today

| Element | Lean | Rust |
|---|---|---|
| Level order | `compareLevel`, `Ix/CompileM.lean:1983-2009` | `compare_level`, `compile.rs:3153-3205` |
| Expression order | `compareExpr`, `CompileM.lean:2054-2140` (well-founded on `compareExprSize`) | `compare_expr`, `compile.rs:3232-3365` |
| Strength | `SOrder` with `cmp`/`cmpM`/`zipM` (`Ix/SOrder.lean:6-60`) | `SOrd::try_compare`/`try_zip` |
| Kind dispatch | `compareConstBody`, `CompileM.lean:2215-2224` | `compare_const`, `compile.rs:3597-3623` (tag order `:3586-3592`) |
| Cache | `cmpCache : HashMap (Name×Name) Ordering` (`CompileM.lean:156`), key `comparisonCacheKey` (`:2147-2151`), strong results only (`:2163-2177, 2226-2236`) | `cache.cmps`, key `(min,max)` with `reversed` flag (`compile.rs:3442-3459, 3602-3622`) |
| Sort | natural merge sort `sortByM` (`Ix/Common.lean:122-199`) | top-down merge sort `sort_by_compare` (`compile.rs:3667-3721`) |
| Grouping | `groupByM` of adjacent `eqConst` (`Common.lean:211-219`) | `group_by` (`compile.rs:3640-3665`) |
| Refinement | `sortConstsLoop`/`sortConsts` (`CompileM.lean:2315-2342`), groups re-sorted by name (`:2290-2299`) | `sort_consts` loop (`compile.rs:3739-3787`), groups keep the stable order |
| Seed | name-hash order (`CompileM.lean:2272-2286`, `Ix/Environment.lean:148-153`) | `sort_by_key(name)` (`compile.rs:3734`), the same hash order |

Context: `MutConst.ctx` (`Ix/Mutual.lean:109-121`), rebuilt at every round from that round's classes
(`CompileM.lean:2320`; `compile.rs:3744`).

### 3.2 At a fixed context, the key is a total preorder [proved: `compareFresh_total`]

[proved] for the Lean compiler (M7 L1, `plans/review2/M7-L1-pass1.md` §2–§2.1): `compareFresh_total`
(`Ix/CompileCert/Canon/Cache.lean`) states that the comparison the code runs, Pass 1's cached
`compareFresh` (equal to the uncached `constOrd`, `compareFresh_eq`), is a total preorder on a
component's members at a fixed context, for every tie-break and both level rules, given
`portFixes = true` (the compiler's rules), `AddrCongr` (the address map answers alike for `==` names)
and distinct member names (`NameInj`). The Lean compiler sorts with it: `Ix/CompileM.lean`'s
`sortConsts` calls `Ix.Compile.Canon.sortClasses Rules.compiler`. The theorems are roots of
`l1Roots` in the tracked audit `Ix/CompileCert/Audit.lean`, on the three standard axioms. What
follows is the paper argument; the Rust port (`compile.rs`) is not proved.

Fix a round's context `ctx`. Then `cmp_ctx` is a lexicographic comparison of finite trees, and each
leaf is compared by a total preorder.

**Leaves:**
- binder index: `Nat`;
- level trees under positional parameters: a lexicographic tree order with tag order
  zero < succ < max < imax < param;
- literals: the derived order on literals;
- semantic contracts: `orderKey : Nat`, injective on decodable contracts
  (`Ix/SemanticContract.lean:43-53`);
- constant references: the map `κ(n) = (0, ctx n)` when `n` is in the block, `(1, addr n)` otherwise.
  A total preorder on names; equal names have equal `κ`.

**Inner nodes:**
- a node is first ordered by its tag (the fixed tag order of §2.2);
- equal tags compare their children left to right;
- lists (`zipM`, `try_zip`) compare lexicographically, a shorter list first.

**`mdata`:**
- non-semantic `mdata` is removed before comparison, on either side and in any combination of
  wrapping;
- semantic `mdata` is a node whose tag exceeds every other tag. Lean checks it first:
  `Ix/CompileM.lean:2061-2081`; Rust: `compile.rs:3249-3279`.

A lexicographic product of total preorders is a total preorder. Its equivalence is equality of the
normalised trees under `κ`. Reflexivity, transitivity and totality follow by induction on
`compareExprSize x + compareExprSize y`, the comparator's own termination measure
(`CompileM.lean:2136-2140`).

**The kind dispatch** must be the tag order for this to extend to members: Rust does this; Lean does
not (C1).

**Strength.** A result is *strong* when no leaf read through `ctx`'s indices contributed to it:
- `cmp ⟨true, eq⟩ y = y`;
- `cmp ⟨false, eq⟩ y = ⟨false, y.ord⟩`;
- a first non-equal component is returned with its own strength (`Ix/SOrder.lean:12-25`).

So a strong result is the same under every context of the same block [proved: `constP_strong`,
`Ix/CompileCert/Canon/Rel.lean`]: the in-block versus
external split is fixed, and only the class indices vary. Caching strong results across rounds is
therefore sound, **provided the cached value is read back in the orientation it was stored in** (C2).

### 3.3 The refinement computes the coarsest consistent partition, and its class order does not depend on the seed [proved: `sortClasses_coarsest`, `sortClasses_setEq`]

[proved] for the Lean compiler's refinement, `Ix.Compile.Canon.sortClasses` (M7 L1, report §6–§7;
roots of `l1Roots`, three standard axioms): the classes it returns are the coarsest consistent
partition (`sortClasses_coarsest`, `Ix/CompileCert/Canon/Coarsest.lean`); the classes and their
order do not depend on the seed, the representative rule or the input order, and only the order
inside a class can change (`sortClasses_setEq`, `SeedFree.lean`); under the compiler's name-hash seed
the whole output is the same for every input order (`sortClasses_perm`, `Seed.lean`). Hypotheses:
`portFixes = true`, `AddrCongr`, member and constructor names distinct under `==` (`KeysDistinct`).
What follows is the paper argument; the Rust port is not proved.

**(a) Every round splits correctly.** At round `n` the context is fixed, so `cmp_n` is a total
preorder (§3.2). A correct merge sort followed by grouping of adjacent equals then yields exactly the
equivalence classes of `cmp_n` on that class, ordered by `cmp_n`.
- Equal elements are contiguous after sorting.
- Every adjacent output pair of a merge sort was compared directly (by induction over merges), so
  `groupBy`'s comparisons are among the sort's.

**(b) The result is the coarsest partition.** Let `Q` be any consistent partition. Assume `Q` refines
`classes_n`.
- Two `Q`-equivalent members have equal keys under `Q`'s class map.
- `classes_n`'s map factors through `Q`'s, so their keys are equal under `classes_n` too.
- So they stay together in `classes_{n+1}`.

`classes₀ = {K}` is refined by every `Q`, so by induction every `classes_n` is.
- At the fixed point, members of one class are `cmp`-equal under the final context, so the final
  partition is consistent.
- Being refined by every consistent `Q`, it is the coarsest. This is old plan Prop 2.1.

Termination:
- every non-final round increases the class count, which is at most `|K|`;
- so at most `|K|` rounds run, and `|K| + 1` fuel suffices (`CompileM.lean:2310-2314`).

**(c) The class order does not depend on the seed.** By induction on `n`: the ordered list of classes
at round `n`, each class as a *set*, is a function of the content alone.
- Base: `classes₀` is one set.
- Step: the context's index of a member is the position of its *class*, a function of the ordered
  set-list.
  - Constructor offsets depend on the classes' maximum constructor counts, again content.
  - Within one class, `cmp_n` is a total preorder that depends only on content and the context. So
    the ordered list of its equivalence classes does not depend on the input order of the class.
  - The concatenation keeps the old order of the classes.

The seed determines only the order of members *inside* each set: stable sorts preserve input order
among ties. Lean also re-sorts groups by name (`CompileM.lean:2296-2299`); Rust does not
(`compile.rs:3772-3783`). Both therefore keep seed order inside a class, and the Rust comment's worry
about a "name-dependent canonical order" does not arise. Inside a class the order selects only the
representative, which is metadata (§2.4).

Hence the partition and the class order are seed-independent, and the representative is the only
seed-dependent output [proved: `sortClasses_setEq`].

### 3.4 Where transitivity or antisymmetry could fail

| # | Site | Property at risk | Lean | Rust | Reachable on Lean input? | Fix in A2 |
|---|---|---|---|---|---|---|
| C1 | kind dispatch | antisymmetry | `compareConstBody` returns `lt` for **every** pair of different kinds: `.defn _, _`, `.indc _, _` and `.recr _, _` all give `lt` (`CompileM.lean:2215-2224`), so `defn < indc` and `indc < defn` | tag order (`compile.rs:3586-3592, 3618`) | No. SCCs are kind-homogeneous (§2.1) and `MutConst`s are built per SCC (`CompileDriver.lean:82-90`) [argued] | tag order, as Rust |
| C2 | cache orientation | antisymmetry: a cached `lt` read back for the swapped pair | key `(min,max)` by name hash, but the value stored is `ord` of the *call's* orientation, and the read returns it unchanged (`CompileM.lean:2147-2151, 2163-2177, 2226-2236`) | normalised: `stored = reversed ? ord.reverse : ord` and the read is reversed back (`compile.rs:3442-3459, 3602-3622`) | **Not today** [argued]. Every class handed to `sortByM` is in name-hash order. `sortByM` (runs, then merges of adjacent runs) only calls `cmp a b` with `a` earlier in the input (`Common.lean:122-199`), so the call orientation equals the key orientation. `groupByM` calls `eqConst later earlier` (`Common.lean:211-215`), but only on adjacent pairs that the sort already compared (§3.3(a)): a strong pair is a cache hit whose sign `eqConst` ignores, and a weak pair is never stored. The constructor cache (`:2163-2177`) inherits its parent's orientation. It would become reachable under any seed that is not name-sorted; Phase A keeps the name-hash seed, so the fix is for a latent bug [measured: A1C §4, 0 reversed non-equal hits inside the sort] | store normalised, as Rust |

| C3 | strength flag | soundness of caching | `SOrder` (`Ix/SOrder.lean:12-60`) | `SOrd` | — sound (§3.2) [argued] | none |
| C4 | syntactic levels | not a preorder failure: minimality, and order follows level spelling | `CompileM.lean:1983-2009` | `compile.rs:3153-3205` | in principle yes. Library population: 0 member orders move in Mathlib and Init+Std, and 0 clique orders [measured, A1C §1.3] | compare `canonUniv` forms (§2.2) |

| C5 | address interleaving | not a preorder failure: order depends on the format version beyond full ties | `CompileM.lean:2098-2104, 2129-2133` | `compile.rs:3210-3227, 3344-3356` | yes: 1/16 member and 4/33 nested sorts in Mathlib involve addresses [measured, CEN Q5] | none: kept by owner decision (§2.3) |

| C6 | `is_rec`, `is_unsafe` | Lean/Rust parity, not order | absent (`CompileM.lean:2181-2192`) | first keys (`compile.rs:3468-3471`) | No. Both flags are block-wide: a non-recursive member of a split block still has `isRec = true` [measured, A1C §0.8], and safety is uniform within a block | the canonical key compares content only; the Rust catch-up drops both keys |

| C7 | constructor indices in `ctx` | none at a fixed context | `Mutual.lean:109-121` | same | constructor references never occur in Lean member or constructor types [argued] | none |
| C8 | semantic `mdata` | totality | orderKey, then body | same | Ix-internal only (source contracts) | none |
| C9 | declarative "fixed point" | uniqueness of the specification | — | — | yes, as a definition (§2.3) | define the order as the procedure |
| C10 | stopping rules | agreement | count unchanged | list unchanged | agree, since refinement only splits [argued] | none |

**Verdict.**
- At every round, the key restricted to one SCC of Lean input is a total preorder, in both
  implementations [argued].
- The fixed point is the coarsest consistent partition. Its class order does not depend on the seed;
  only the representative does [argued].
- C1 and C2 are defects of the Lean port that today's inputs do not reach. Both are fixed in A2's
  migration commit, and neither fix moves a byte. C2 is a latent-bug fix. It is a precondition of
  nothing, since the seed stays name-hash.
- C4 and C5 are not preorder failures.
  - C4 (`canonUniv` levels) is adopted. It moved 0 orders in the libraries [measured, A1C §1.3].
  - C5 (first-difference addresses) is kept by owner decision.
- C6 has no byte effect, because the flags are block-wide [measured, A1C §0.8]. The key becomes
  content-only.
- Measured: 0 preorder violations at the fixed point on every fixture component and on 17 Mathlib
  components of up to 40 members, under both rule sets [A1C §1.3, §4 item 8].

### 3.5 Phase A's comparator, stated for Phase B

`cmpA_ctx(x, y)` is today's key of §3.2, external references by address at the first difference,
with three changes:
- levels are compared as `canonUniv` forms;
- the kind tag comes first (C1);
- the key is content-only, without `is_rec` or `is_unsafe` (C6).

The cache is normalised (C2), which changes no result. `cmpA_ctx` is a total preorder [argued; 0
violations measured, A1C §1.3]. The strong flag is computed as today.

Phase B's L1 statements:
- (i) `cmpA_ctx` is a total preorder for every `ctx`;
- (ii) the refinement terminates and returns the coarsest `cmpA`-consistent partition;
- (iii) the ordered partition is invariant under permutation of the input list;
- (iv) the canonical declaration of a class is invariant under the choice of representative.

### 3.6 The exhaustive test (A1 study; A2 gate)

**Corpus:**
- every fixture block and clique: the whitebox (28) and blackbox (10) reproducers with their
  neighbours, and the ~120-namespace shape matrix;
- every library block with two or more classes (16 member sorts and 33 nested sorts in Mathlib's
  closure [measured, CEN Q5]).

**Legs:**
1. **All permutations.** For every block with `|K| ≤ 7` (5,040 presentations), every permutation of
   its members in Lean's `all`, re-elaborated as Lean source.
2. **Random presentations.** For larger blocks (Cutsat has 12 members), 1,000 random presentations
   per block. Each draws a member permutation and a renaming of members, constructors and binders.
   A presentation may also respell universe levels (`max u v` ↔ `max v u`, `succ (max …)` forms)
   and split its components into separate declarations with the block's universes, parameters and
   sort.
3. **Seed sweep, no recompilation.** On each block's prepared `MutConst` list, run the refinement
   under the identity, reverse, name-hash and ten random seeds, with the C2 fix on. Require identical
   class lists, as sets, in identical order.
   - First run [measured, A1C §1.3]: 0 differences on 145 fixture components, 17 Mathlib components
     and 170 Mathlib cliques.

4. **Property check per round.** At every round of every run, evaluate `cmpA_ctx` on all ordered pairs
   and triples of the class being refined. Require reflexivity, antisymmetry up to equality, and
   transitivity, with the cache on and off. For `|K| ≤ 12` this costs at most 1,728 triples per round.
   - First run [measured, A1C §1.3]: 0 violations.

5. **Compile and compare.** For legs 1 and 2, compile each presentation and require all of:
   - the Ix block bytes and every Ix auxiliary are identical;
   - `N` sends corresponding names to corresponding canonical positions;
   - every other constant is byte-identical except the entries of the non-canonical set (§7.2).

   Presentations that change the addresses of external constants, such as another format version,
   are out of scope: the order may then flip by design (§2.3).

6. **Lean/Rust.** Run the seed sweep on Rust's `sort_consts` through `rs_compile_phases` until the
   catch-up PR. It gates the Rust catch-up's `canonUniv` levels and its removal of `is_rec` and
   `is_unsafe`.

**Failure policy.** Any failure of leg 3 or leg 4 is a comparator defect and stops A2. A leg 5
difference outside the non-canonical set is a canonicity defect of a later pass.

---

## 4. The image construction

For each Lean recursor `r` of a changed block (Def 3.1), Pass 3 builds an **image** `img(r)`: a
closed Ix term with Lean's type `tr_N(type r)` that computes as `r` does. The image is built from the
*types* of the Ix recursors and from the specifications. It uses no reduction, unlike the prototype,
which used `MetaM` (`plans/review/auxgen-certify/exp-prototype/CertProto/Lib.lean`, 516 lines).

*A3I* below means `plans/wave1/a3i.md` (untracked): the image generator `Ix/Compile/Image/**`, written
as total pure functions. Its measurements:
- 38/38 images, 62/62 rules by `rfl` and 45/45 bridges under Lean's kernel;
- 36/38 images α-equal to the prototype's (the other 2 are C3b, see §4.2);
- 154/154 inline call sites equal to the original by `rfl`.

**Term representation** [measured, A3I §1, §4 item 1]. The generator builds `Ix.Expr`, the hashed
mirror of `Lean.Expr` with the same constructors, not `Lean.Expr`. `CompileM`, `AuxGen` and Pass 1
already work on `Ix.Expr`, so building `Lean.Expr` would force a conversion in both directions at
every call site. Everything in this section applies unchanged to `Ix.Expr`.

*This departs from a stated requirement.* The old plan's Def 2.9 asks generators to be pure over
`Ix.Kernel.Expr`, the certified kernel's term language. `Ix.Expr` is not that language. A conversion
`Ix.Expr → Ix.Kernel.Expr` is needed before Phase B can prove anything about the generator [open; for
A3 proper and Phase B].

### 4.1 Eliminator choice (Def 3.3)

Let `t` be a Lean motive type: a member or an auxiliary, at parameters `ps`. Then `elim(t)` is the
first Ix recursor whose motive types contain `tr_N(t)` at some slot `j`, taken from these candidate
lists in order:
1. the recursors of the Ix blocks occurring in `tr_N(t)`, nested auxiliaries included;
2. the recursors of the other inductives occurring strictly inside `tr_N(t)`, outermost first;
3. the recursor of `tr_N(t)`'s head.

The prototype's `findElim` (`Lib.lean:184-219`) takes the candidates of list 2 in the order of
`Expr.getUsedConstants`, which is first occurrence in a pre-order walk, at the parameters of the first
occurrence (`T.find?`). A3 uses that exact rule, which makes "outermost first" precise.

The order matters because it makes the choice *consistent*: if `t′` is a recursive field of a
constructor of `t` and `elim(t)` has `t′` among its motive types, then `elim(t′) = elim(t)`
[argued]. Choosing the head first breaks this: `List (Rose B)` would get `List.rec` instead of
`Rose.rec_1`, and the computation rules then fail [measured: PRO correction 1, ablation `C4b-naive`
rejected at `A2.rec_1.iota_node`, plus 4 `.go`, 4 `.eq` and `_sizeOf_3_eq`].

### 4.2 The image of a recursor (Def 3.4)

Fix `r` with parameters `ps`, motives `m₁ … m_M` over Lean motive types `t_i`, minors, indices `is`
and major `x : t_maj`. Let `ρ = elim(t_maj)` have motive slots `1 … K`.

**Step 1: slot classes.** For each slot `j`, `C_j` is the set of Lean motives `i` with
`elim(t_i) = ρ` and `tr_N(t_i)` at slot `j`, listed in Lean's order. The prototype finds it by
comparing *stripped* motive types, with the sort replaced by `Sort 0` (`Lib.lean:125-129, 245-246`).
- Every slot has a non-empty class [argued: Lean's nested expansion is closed under the
  containers' own expansion; measured: PRO, 38/38 images built].
- The prototype throws when a class is empty (`Lib.lean:247-248`); A3 does the same, as an error
  naming the block.

**Step 2: the level.** Let `u` be the universe of Lean's motives (`motiveLevel`, `Lib.lean:131-134`).
- If some `|C_j| ≥ 2` and `u` is not always zero, instantiate `ρ` at `ℓ := max 1 u`, normalised.
  Otherwise `ℓ := u` (`Lib.lean:249-251`).
- **Prop member that gained large elimination:** if `ρ` has an elimination universe and Lean's `r`
  does not, then `u = 0` and `ℓ = 0`. This instantiates `ρ.{0}`.
- If `ρ` eliminates only into Prop while `ℓ ≠ 0`, it is an error (`Lib.lean:255-256`). This never
  happens [argued: splitting and collapsing only remove the conditions that restrict elimination].

**Step 3: packing each slot.**
- *single* (`|C_j| = 1`, and no lift needed): the motive is `m_i`, η-contracted (`Lib.lean:265-271`).
- *tuple* (`|C_j| = k ≥ 2`): the motive is `λ ys. m_{i₁} ys ×' … ×' m_{i_k} ys`, nested to the right.
  - `PProd` is used at level `ℓ`; `And` replaces it exactly when Lean's motives are propositions
    (`PProdN.pack`, `src/lean/Lean/Meta/PProdN.lean:94-114`).
  - [measured: PRO, C3b and C7 at level 0. Under Pass 1, C3b is a split (see "What is established"
    below), so C7 is the collapse case.]

- *lifted* (`|C_j| = 1`, but some other slot is a tuple and `u` is not always zero): the motive is
  `λ ys. PProd.{u,0} (m_i ys) True`, of sort `Sort (max 1 u)` (`Lib.lean:227-238`).
  - Without the lift, `ρ.{max 1 u}` cannot take a `Sort u` motive.
  - [measured: PRO correction 2. Ablation `C8-nolift`: all 3 transports and 70 dependents
    rejected. `PLift` lands in `Type u`, also rejected.]
- **Unwrapping.** `unwrap_p` projects component `p` of a tuple (`PProdN.proj`, primitive `.proj`
  projections: `PProdN.lean:55-79, 123-145`), takes `.1` of a lifted slot, and is the identity on a
  single slot (`Lib.lean:221-225`).

**Step 4: minors.** For each Ix minor of slot `j` and its constructor `c`, with fields `fs` and Ix
hypotheses `ihs`:
1. For each `i ∈ C_j`, take Lean's minor for `(i, c′)`, where `c′` is the Lean constructor that
   corresponds to `c` by position (`Lib.lean:296-300`).
2. Apply it to `fs`, then to one hypothesis per Lean IH binder. For a binder over field `f` with Lean
   motive type `t′`:
   - **if `f` has an Ix hypothesis** (it is recursive for `ρ`): take `unwrap_pos (ih ys)`, where
     `pos` is the position of `t′` in the hypothesis's class (`Lib.lean:311-315`);
   - **otherwise: a relocated hypothesis.** Take the image construction for `t′` applied to `f` and
     its indices: an explicit call of `elim(t′)`, another Ix recursor, with Lean's motives and minors
     (`Lib.lean:316-318`, recursive, under the reflexive binders `ys`). This covers the split case and
     the evaporated case.
3. Pack the results of all `i ∈ C_j` like the motive: `v`, `⟨v₁, …⟩`, or `⟨v, True.intro⟩`
   (`Lib.lean:234-238, 322`). Then η-contract (`Lib.lean:324`).

**Relocation terminates** [argued, old plan Prop 3.1 lemma]. A relocated field's type lies either in
an Ix block strictly below `ρ`'s block in the condensation DAG, or in a container instance finitely
nested in the field type. The prototype's fuel of 64 (`Lib.lean:241, 355`) is replaced in A3.

*Implemented* [measured, A3I §4 item 2]. The generator recurses structurally on the bound (number of
Lean motives + 1) and raises an error naming the block when it runs out. Along one relocation chain
the eliminators are pairwise distinct, and each is `elim(t)` for a distinct Lean motive `t`, so the
bound loses no terminating case [argued, A3I]. This departs from this section's earlier wording,
which asked for structural recursion on (DAG height, nesting depth). That wording was a suggestion
about the measure, not a requirement; the requirement is termination without fuel, and the new bound
meets it.

**Unused Lean motives.** A Lean motive that lies in no slot of the chosen eliminator is simply not
used. Examples are C3b's `motive_2` and the split cases. This follows from the construction [A3I §4
item 6].

**Step 5: the result.**
`img(r) := λ ps ms mins is x. unwrap_{pos(t_maj)} (ρ.{ℓ, us} ps motives′ minors′ is x)`
(`Lib.lean:325-327`), followed by the development of §4.3.
- The prototype applies `Core.betaReduce` to the whole term (`Lib.lean:357`), plus `.eta` on each
  motive and minor.
- The levels `us` are the block's universe arguments, after `canonUniv`. Under D3/D16 the level
  selection σ is the identity.

**Composition.** Def 3.4 computes the image of `τ_order ∘ τ_collapse ∘ τ_split` directly. Nothing
downstream depends on how an image was built: it is checked by its type and its computation rules.

**What is established.** Images are well typed, and Lean's computation rules hold against them:
- old plan Prop 3.1 and Prop 3.2 [argued];
- 38/38 images typed at Lean's type and 62/62 iota rules by `Eq.refl` in Lean's kernel, over 15
  sub-cases: permutation, split with and without a cross field, Prop split and collapse, evaporated
  `List`, `Rose`, collapse, nested collapse, `IndPredBelow`, mixed class, parameters, universes and
  reflexive fields [measured: PRO, `out/results.tsv`; reproduced by the pure generator, A3I].
- **C3b is now a Prop split, not a collapse.** The prototype hand-collapsed C3b's independent,
  α-equivalent Prop pair `Q1`, `Q2`. Under Pass 1 they never reference each other, so they form two
  components, and classes are formed within components (§2.1–2.2). C3b therefore tests a Prop split,
  in which each member gains large elimination. C7, with `P` and `Q` mutually recursive, still tests
  a real Prop collapse [measured, A3I §3 item 1].

### 4.3 The development

Substituting an image term creates redexes. "Develop" means: contract exactly the redexes that the
construction or the substitution created, and leave every redex the user wrote. Precisely:

1. **At the image (P3a).**
   - Contract the β-redexes formed by applying the image's own motive and minor λs.
   - Contract the η-redexes `λ ys. m ys` and `λ fs ihs. g fs ihs` that the construction produced.
   - These are a finite set and their residuals, so a complete development, which is finite by the
     finite-developments theorem.
2. **At a call site (P3b, §4.5): hereditary substitution.** The occurrence `img(a) args` with
   `|args| ≥ arity(img a)` is replaced by `body[params := args]`.
   - Wherever a parameter that received a λ-argument occurs at the head of an application inside
     `body`, the created β-redex is contracted, and so on hereditarily.
   - So are projection-of-constructor redexes `(⟨a, b⟩).1 ↦ a` (`PProd`, `And`), and η-redexes,
     created at those positions.
   - *Implemented, and narrower* [measured, A3I §4 item 3]. η is contracted only where the head is
     the directly substituted value. The result of a hereditary β-step is not η-contracted, so a
     user-written η-redex survives (unit check 5).
     - This narrows the sentence above. It is consistent with Q10's decision ("η at the substituted
       variables") and with the rule that user redexes are left alone. The rule is pinned this way.
   - At the image (P3a), the motive and minor wrappers are η-contracted with Lean's `Expr.eta`, as
     in the prototype.
   - **[open] Reflexive-field wrappers.** In C9 and C9b, the reflexive-hypothesis wrappers
     `fun a => a_ih a` are kept in the image, to match the prototype. Whether to contract them is
     canonical-neutral, and it is decided by A3 proper before A4 pins the twins.

   - Termination [argued]: each hereditary step substitutes at a strictly smaller type, namely a
     motive's or minor's codomain, which is finitely nested in Lean's recursor type.
   - Redexes inside the user's arguments are not touched unless the substitution itself formed
     them.
   - ι-redexes are **not** contracted. `ρ … (c fs)` arising from a user-written `T.rec … (c fs)` is a
     residual of the user's redex.

The development is part of the canonical form, because O1–O6's outputs must equal the twin's terms
[measured: 53/53 on DQReord, a pure permutation, where the rewrite creates no λ-substitution]. A3 must
pin the hereditary rule with fixtures in which the user's motives and minors are λs (they always are
when elaborated from `match` or `induction`) and compare against the twin.

### 4.4 The two prototype corrections

1. **Container rule.** A nested Lean type is eliminated with the outermost block that has it as a
   motive type: canonical blocks first, then containers inside the type, then the head (§4.1). For
   `List (Rose B)`: `Rose.rec_1`, not `List.rec` [measured: PRO correction 1].
2. **Mixed collapse class.** When some slot is a tuple at `max 1 u`, every singleton slot of the same
   eliminator is lifted with `PProd (m x) True` (§4.2, step 3) [measured: PRO correction 2].

A third rule, `And` exactly at Prop motives, was in the design already and was confirmed [measured:
PRO].

### 4.5 Call sites: inline rewrite or image constant

For every occurrence of a Lean auxiliary `a` of a changed block in a compiled constant. `a` ranges
over `rec`, `rec_N`, `recOn`, `casesOn`, `below*`, `brecOn*`, `.go`, `.eq` and `_N`.

- **Fully applied** (at least the image's arity in arguments): **inline**. Replace the occurrence by
  `img(a)`'s body with the arguments substituted, then develop (§4.3). Arguments beyond the arity stay
  applied. **Nothing that is used is dropped:**
  - every motive and minor that the major premise can reach appears in the result, permuted, paired
    or relocated;
  - the arguments that belong to members of other components vanish. Those members cannot occur in
    the major's type, so their motives and minors are absent from the image body, and hereditary
    substitution discards the user's arguments for them.
    - Example: C2b, `A.rec ↦ fun … nil cons leaf two t => Gen.A.rec nil cons t` [measured, A3I §4
      item 4].
    - This is definitionally harmless: 154/154 inline sites equal the original by `rfl` [measured,
      A3I].
    - The rule that matters is the old surgery's defect, dropping *used* minors, and that cannot
      happen here.
  - O7/O10/O12 are the only passes that may later remove duplicates, and only under their side
    conditions.

- **Bare or partial** (`def r := @A.rec`, `List.map A.casesOn`, `@f._mutual`): reference the
  **image constant** `img(a)`.
  - It has Lean's type exactly and is a λ over Lean's telescope, so it *is* the eta adapter. A
    partial application `img(a) a₁ … a_k` is well typed with Lean's type, and no separate adapter
    constant is generated.
  - The alternative, an inline η-expansion `λ ys. inline(a, args ++ ys)`, duplicates the image per
    occurrence and is no more canonical: the type is Lean's, which follows the grouping. It is not
    used (Q11, §8).
  - **Decision (orchestrator, 2026-10-03; A3M decision 3): images are always stored, and the Lean
    names of a changed block's image-kind auxiliaries denote their images.**
    - Each image is an ordinary definition under the Lean name, with `Named.original` set to Lean's
      form compiled without any rewrite.
    - So a bare or partial occurrence keeps the Lean name and needs no record. The "residual image"
      of the first draft (`a._ix`) no longer exists.
    - The Ix auxiliaries carry `_ix` display names (§4.8).
    - D7 may move the images to a separate file in Phase B.

  - Library population: 0 bare or partial applications in Init+Std, Lean, Batteries and Mathlib
    [measured: CEN:33].
- **`casesOn` and `recOn` keep Lean's arity.**
  - The Lean names are images, so their types are Lean's.
  - `casesOn` has one motive and its own constructors' minors, so its image is the Ix `casesOn` of
    the class with the same arguments (O3).
  - `recOn` takes all of Lean's motives, so its image goes through `img(rec)` (Def 3.5).

### 4.6 Lean's other auxiliaries over images (Def 3.5) and the baseline (Def 3.6)

**Def 3.5.** For a Lean auxiliary `a` of a changed block that is a definition or a theorem,
`img(a) := tr_N(value a)` with every reference to an auxiliary `a′` of a changed block replaced by
`img(a′)`. The kinds are `casesOn`, `recOn`, `below`, `below_N`, `brecOn`, `brecOn_N`, `.go` and
`.eq`.
- No regeneration over images is needed: 836/836 of Lean's other auxiliaries, copied verbatim under
  renaming, type-check over the images [measured: PRO claim 2].
- The kinds covered: `casesOn`, `recOn`, `below*`, `brecOn*` with `.go`/`.eq`; matchers, splitters,
  `match_N.eq_N`; `_sparseCasesOn` and `.else_eq`; the `noConfusion` family; `inj`/`injEq`;
  `ctorIdx`/`ctorElim`; the `sizeOf` family; `eq_N`, `eq_def`, `_f`, `_sunfold`, `_unsafe_rec`.
- Two copying details apply. Private splitter names are renamed through `privateToUserName?`
  (`Lib.lean:47`). Mutual `_unsafe_rec` definitions are added together as one `mutualDefnDecl`
  (`Lib.lean:403-410`).

**Lean's `IndPredBelow` families of a changed Prop block** are inductive types, so they have no
closed-term image. They are compiled as blocks by Passes 1–3, are themselves canonicalised, and get
images when changed (old plan §2.9). They are the one non-canonical, non-image kind of constant in
`E`.
- The prototype's single checker reject came from this (PropSplit inside the view: PRO claim 6,
  caveat 1).
- None exist in the measured libraries [measured: CEN:24, 0 Prop members gaining large elimination;
  Mathlib has 0 Prop-valued nested inductives, `polish/nestedprop/README.md`].

**Def 3.6, baseline.** For every other constant `c`, `base(c) := tr_N(c)` with every reference to an
auxiliary of a changed block replaced by its image, inline at full applications (§4.5).
- Theorem statements are translated exactly.
- `base(c)` is well typed whenever Lean's derivation of `c` unfolds no theorem [argued: old plan
  Prop 3.3].
- A derivation that unfolds a theorem has no Ix counterpart. This is a *certification* totality
  failure: the checker rejects or declines. The compiler cannot detect it (A Δ11).

### 4.7 The six ways a split differs from Lean's elaboration, and their Phase A treatment

From ORA, split row [measured], on `SurgSplit`, `DQSplit`, `DQMut`, `EvapClosure`, `NestRoseSplit`,
`PropSplit`, `SurgIdx`, `UnivSplit` and `Grind.Arith.Linear`:

| Cause | What differs | Phase A |
|---|---|---|
| (a) | The split member keeps the block's universe list (`UnivSplit`: `lvls = 1` against `0`) | By design (D3/D16, §2.4). Faithful but not canonical against a separate declaration with fewer universes. It is not an entry of the non-canonical set, since Def 4.3 excludes such presentations
 |
| (b) | `below`/`brecOn` generated for a split member that is no longer recursive | Fixed. Pass 2 decides existence by Lean's conditions on the Ix block (old plan Def 2.7), never by names or by the Lean block |
| (c) | Lean's `noConfusion` takes the enumeration form only for `numTypeFormers == 1 && !isRec` (`src/lean/Lean/MonadEnv.lean:198`, per ORA) | Lean's form compiles by baseline (faithful); O11b rewrites users onto the canonical `noConfusion` (proof-justified) |
| (d) | Lean's mutual `_sizeOf_N` inlines the block recursor, while the separate form goes through the instance | Baseline; O11a if one `rfl` on `Linear.EqCnstr` confirms it is definitional [open] |
| (e) | Leftover reference and sharing-table entries from dropped arguments change addresses | Removed by construction. P3 builds each term afresh and P5 derives the tables from the final term only (`preseedExprTables`, `Ix/CompileM.lean:1672-1690, 1929`) [argued; v4 sharing was rewritten in `1965df06` and this was not re-measured, D §3.2] |
| (f) | Open defects: SurgSplit (wrong IH projection), PropSplit (missing universe), SurgIdx (eta adapter) | Retired with surgery (A3). Images take the IH projection from the slot class (§4.2, step 4), the universe from the level rule (step 2), and partial occurrences from the image constant (§4.5) |

Two neighbouring findings:
- For user structural recursion over a split block, the only term difference is the path into
  `below` (`x_below.2.1` against `.1`) plus the leftover entries [measured: ORA §3, `A.len._f`]. That
  is O9's re-pathing.
- For collapse, functions cannot agree with the twin by rewriting [measured: ORA §3; PRO, B2 table].
  That is O10/O12's territory.

---

### 4.8 Pass 3 as built (A3W, A3M)

Everything here is [measured, A3W/A3M] unless marked. The figures come from the gates of `ca90424b`
(A3M) and of the A3W chain.

**Switch.** Pass 3 is **the default** since the flip (M6, 2026-10-06; the migration is §7.4). The
mode is read from `IX_PASS3` by the drivers that read the environment (`compileEnvParallelAux`,
so `ix compile-lean`, `ix validate-lean` and `compileLeanInput`), or given by their `pass3?`
argument; the pure sequential driver `compileEnvAux` takes `pass3`, defaulting to Pass 3
(`Ix.Compile.Pass.switchDefault`). The values:
- unset or `IX_PASS3=images`: Pass 3;
- `IX_PASS3=off`: the legacy call-site surgery, kept as the comparison mode for the gates against
  the Rust compiler's default until M6R slice 6;
- any other value: refused (`switchFromEnv`), so a mistyped value never selects a mode silently.

**The Rust compiler** reads the same variable with the same values and the same refusal
(`switch_from_env`, `crates/compile/src/compile/pass3/names.rs`, read once per compile in
`compile_env_with_profile`, `crates/compile/src/compile/env.rs`, which `ix compile`, `ix validate`
and the Rust compile of `ix compile-lean --rust-check` all reach). It implements Pass 3: on the main
line, M6R slices 1–4 (the driver and images; O1–O6/O11a; the clique transport; O7–O12/O11b in the D1
form). Only its default differs, until M6R slice 6: unset is the surgery (`SWITCH_DEFAULT = false`).
In each mode its output equals Lean's byte for byte where measured:
- `IX_PASS3=images`: Init+Std `a2e22ee7…ba676` from both compilers (landing gate of `5d0e493a`,
  `ix-cc-proof/out/land-m6r.log`: Rust `IX_PASS3=images ix compile` and Lean's default
  `ix compile-lean` both hash to `initstd-a3.ixe`; `pass3-rust-parity`: 0 defects on the fixtures and
  on Init+Std, "BYTE-IDENTICAL"); Mathlib `d0427adf…f6db` (Rust `IX_PASS3=images` equal to
  `mathlib-a3.ixe`, `cmp` identical, and the per-name parity run 0 defects:
  `plans/review2/M6R-4-rust-pj.md`, log 10:31 UTC, on the slice-4 tree, whose Rust code the main line
  carries unchanged);
- `IX_PASS3=off`: `ix compile-lean --rust-check` ALIGNED on Init+Std, `468ad7ae…` = `initstd-a2.ixe`
  (`[compile-lean] ALIGNED: 254684853 bytes byte-identical with Rust` in every landing gate, e.g.
  `ix-cc-proof2/out/land-wpe.log` at `6634c58f`); Mathlib: Rust's default output `0758ba05…` =
  `mathlib-a2.ixe`, the legacy reference (the same M6R-4 run).

So `--rust-check` compares one mode only when `IX_PASS3` is set. Unset, Lean compiles Pass 3 and Rust
the surgery, and the outputs differ wherever a block or clique changes (Init+Std: `a2e22ee7…` against
`468ad7ae…`). The images-mode identity above was measured by hash and by `pass3-rust-parity`; no
`--rust-check` run in that mode is recorded.

The surgery and its default-path defects (WB-B2, WB-B3, KF-O1, KF-C7, KF-O1C, the CORPUS-IPB
refusal) stay in the compiler, and in the records under the `off` switch state, until M6R deletes
the surgery from both compilers.

Under the switch no call-site surgery plan is registered. Pass 3 then works as follows:
- a full application of a changed block's `rec`, `rec_N`, `casesOn`, `recOn`, `below*`, `brecOn*`,
  `.go` or `.eq` is inlined from its image by hereditary substitution (§4.3, Q10);
- `casesOn`, `recOn` and the `below`/`brecOn` family are expanded to Lean's own values, rewritten
  (Def 3.5);
- other Lean auxiliaries (`noConfusion`, `sizeOf`, matchers, …) are baselines.

**Modules** (`Ix/Compile/Pass/`):

| Module | Content |
|---|---|
| `Names` | the switch; the reserved `_ix` component (D14); display names; image kinds |
| `Translate` | `base(c)`, memoised over shared subterms |
| `ImageView` | Pass 1's form, Pass 2's recursors renamed into the generator's view, `imageOf` |
| `SideCar` | the `_ix` display entries and metadata renaming |
| `Driver` | the two hooks: after a changed block's aux tail, and before a block compiles |

**Names (D14).**
- Pass 2's auxiliaries of a changed block are registered under `_ix` display names: `A._ix.rec`,
  `A._ix.casesOn`, nested ones by canonical position (`rep₀._ix.rec_i`).
- The `Muts` member lists follow, so terms reference them by `_ix` names [A3M decision 3].
- An input name with a component starting `_ix` is rejected under the switch; negative control:
  `Tests/Ix/Compile/AuxCert/ReservedIx.lean`.
- The canonical `IndPredBelow` family of a changed Prop block moves to its display names, so Lean's
  own `IndPredBelow` block compiles as an ordinary block (§4.6).

**Images are always stored** (decision 3, §4.5).
- `Driver.compileImageBlock` / `CompileDriver.runImageBlock` compile Lean's own block of image-kind
  auxiliaries to the images under the Lean names.
- `Named.original` holds Lean's form compiled without any rewrite.
- One stored image per Lean auxiliary of each changed block.
- The `below`/`brecOn` family counts as image-kind only for a recursive block (Lean's rule).

**The seam.**
- The generator, the rewrite and the compiler all work on `Ix.Expr` (§4).
- Images are λs over Lean's telescope with Lean's level parameters. At a call site `substLevels`
  instantiates them before the development, and the compiler canonicalises the levels as usual.
- `Develop` is memoised per node, because user arguments are DAG-shaped proofs.
- Two compile-order rules:
  - images are built only over components already compiled (`canonBlockCompiled`), because the
    comparator reads addresses;
  - `And` is pre-compiled with the aux-gen seeds (`PProd`, `True`, `Eq` already were).

**Side-car record of an inline rewrite.**
- The arena node is wrapped in `mdata [(_ix.inline, s), (_ix.inline_meta, m)]`. `metaSharing[s]` is
  the compiled source occurrence with the user's arguments unrewritten, and `m` is its arena root.
- Decompile replays the record. The kernels see an ordinary `mdata`. No new Ixon tag is needed.
- Cost: a rewritten constant's metadata holds its source call sites once more.

**Decompile.** In a Pass 3 environment no plan is installed, so verification recompiles run
un-surgered. `decompile-diff` is 0 on every complete unit.

**Counts.**
- **Switch off:** no byte moved. Init+Std and Mathlib are identical to the references in both
  compilers, and all fixtures are `ALIGNED`.
- **Switch on, Init+Std:** at A3M, before the clique transport and O1–O12 were wired, identical to
  the reference (`468ad7ae…` on the migrated head) [A3M]. Today it is not: Init+Std has no changed
  inductive block, but 5 of its 7 definition cliques are transported, so the default output is
  `initstd-a3.ixe`, 256,128,289 B, sha256 `a2e22ee7…ba676`, 115,942 blocks, 0 block failures, and
  against `initstd-a2.ixe` (the legacy mode) 41 names move and 19 are added (§7.4) [measured: landing
  gate of `6634c58f`, `ix-cc-proof2/out/land-wpe.log`, "initstd-a3 IDENTICAL", and its changed-set
  record, "0 changed blocks, 7 cliques", 5 of them `transported` and 2 `baseline`].
- **Switch on, Mathlib**, on the pre-migration base [A3W §4]:
  - it compiles completely (772,896 blocks, 29 min);
  - 4,467 names move: 278 roots and 4,189 ripples, all in the cones of the 20 changed blocks;
  - of the **242** surgery-rewritten library constants, **109** are byte-identical (pure
    permutations, nested-order moves) and **133** differ: they are the baseline, which A4's O1–O6
    bring back. That covers `_sparseCasesOn_N` (O3), `Linear.EqCnstr._sizeOf_1..7` (O2/O11a), and
    the `Ring` structural functions and their `_f` (O4).
  - Today (the default since the flip): `mathlib-a3.ixe`, 2,376,572,399 B, sha256 `d0427adf…f6db`,
    772,896 blocks, 0 block failures; against `mathlib-a2.ixe` 783 names move, 356 are added, 0 are
    removed, 0 unexplained (§7.4) [measured, `plans/review2/M6-flip.md` §9, on the flip's commit].
- **Fixtures:** the `pass3` suite has 67 units and 0 problems on the main line (`[pass3] 67 units, 0
  problem(s)`, `ix-cc-proof2/out/land-wpe.log`). At A3M it had 53 units, whose 535 images and 885
  rule statements held by `rfl` in Ix.Tc, the Rust kernel and the certified checker [A3M].
  - Every switch-off kernel failure caused by surgery passes with the switch on: SurgSplit,
    SurgAlias, SurgIdx, C2Split, PropSplit, Coind, twins 496 of 511.
  - Every A0 collapse refusal compiles faithfully over the paired image [A3W §0].

**The suite's exemption rule** (orchestrator, A3; BELOW-ORDER removed by A5R). A meta-mode kernel
failure in a unit with a collapsed block (BB-F7, BB-F1) is accepted only where the certified checker
accepts the same constant, and it is named
by defect id in the output. REFUSED-SIBLING consequences are listed per unit (§7.3).

**The surgery is the legacy mode until M6R slice 6.** Since the flip (§7.4) the surgery is not the
compiler's form of anything in the default output: it runs only under `IX_PASS3=off`, as the comparison
mode against the Rust compiler, whose default is still the surgery. The Rust compiler implements Pass 3
under `IX_PASS3=images` (M6R slices 1–4 on the main line: the driver and images, O1–O6/O11a, the clique
transport, O7–O12/O11b; "Switch" above); slice 6 deletes the surgery from both compilers and flips
Rust's default, keeping the split-minor helpers O2 and O11a share with it (`Ix/CallSiteSurgery.lean`'s
`sourceCtorForMinor`, `sourceMinorType`, `peelBinders`, `findSourceRecTarget`, `auxMotiveSigs`). Until
then `--rust-check` compares one mode only with `IX_PASS3` set (the landing gates use `off`), and text
in this document that describes the surgery as what the compiler does (the measured counts of §4.8 and
§9 taken with the switch off, A3W, A3M) describes that legacy mode. Rust's reader accepts Pass 3's
output.

## 5. Transport of proof terms

### 5.0 The common frame

**Setting.**
- A changed clique has Lean order `f_0 … f_{n-1}`, which is Tarjan order (M.6).
- The canonical order is given by `σ : Fin n → Fin n`: Lean index `i` goes to canonical position
  `σ i` (M.3).
- Lean's pre-definition pipeline encodes the clique as `Enc_L`. The canonical elaboration (M.5) is
  `Enc_C`: the same encoding run on the canonical order, with Lean's pinned choices.
- **Transport** is a map `Φ_σ` from terms in the image of `Enc_L` to terms of `Enc_C`.

`Φ_σ` is the identity on every subterm the encoding did not generate: user bodies, external
constants, and the per-function data the encoding carries along with each function (measures,
`recArgPos`, arities). It acts by four kinds of step:

| Kind | What it does | Example |
|---|---|---|
| **(R) renaming** | Lean's encoding constants become canonical ones with the `_ix` component | `f₀._mutual ↦ g._ix._mutual`; `_mutual.proof_k ↦ proof′_k`; transformed `match_N ↦` canonical transformed matcher |
| **(A) re-association** | right-nested `PSum`/`PProd` types, their introductions and eliminations are rebuilt for the order `σ` | `PSum a (PSum b c) ↦ PSum b (PSum a c)`; `inr (inl v) ↦ inl v`; case trees with leaves moved; projection paths `.2.1 ↦ .1` |
| **(S) re-statement** | an obligation whose statement mentions the packing becomes the obligation over the canonical packing | `∀ ctx, rel (inj_b ⟨…⟩) (inj_a ⟨…⟩) ↦ ∀ ctx, rel′ (inj′_{σb} ⟨…⟩) (inj′_{σa} ⟨…⟩)` |
| **(G) regeneration** | a sub-proof whose *shape* depends on a projection path is rebuilt by Lean's own deterministic recipe for the new path | the monotonicity proof of `f.2.1` against `f.1` (§5.2) |

**No encoding is a pure renaming.** All three use (A), because the packing nests binary type formers
and a permutation changes the nesting depth of a summand or factor. Well-founded recursion adds (S);
`partial_fixpoint` adds (S) and (G).

**Why `Φ_σ(p)` proves `Φ_σ(T)` when `p : T`** [argued]:
- `Φ_σ` is a homomorphism on term structure, except at encoding-generated constructs.
- At those it maps each construct to the corresponding construct of `Enc_C`: a type former to a type
  former, an introduction to an introduction, an elimination to an elimination.
- So every typing-rule instance in `p`'s derivation maps to an instance of the same rule.
- Every conversion step that involves the encoding maps to the same kind of step: ι of a case tree on
  an injection, projection of a tuple, δ of an encoding constant.
- (G) replaces a sub-proof by another proof of the *mapped* sub-statement.

**Precondition: the grammar.** Every occurrence of an encoding type in `p` must be in a recognised
position: one of the constructs above, or a copy of a statement produced by the encoding. A
recogniser decides this. When it fails, the fallback of each encoding applies. That fallback is the
faithful form (§0.1), and the constant enters the non-canonical set with cause `SHAPE` (§7.2).

*As implemented* [measured, A5T]: a construct counts as recognised only if a re-implementation of
Lean's own construction rebuilds it exactly.

**Faithfulness never depends on transport.**
- Theorem statements and definition types are translated exactly.
- A transported proof is a proof of the canonical obligation.
- The correspondence between a canonical member and Lean's member is O14–O16's business, not
  transport's.

### 5.1 Well-founded recursion

**Lean's encoding** (4.34.0, `src/lean/Lean/...`):
- **Fixed parameters.** `getFixedParamPerms` (`Elab/PreDefinition/FixedParams.lean:271-301`). The
  fixed parameters appear in the *first* function's order, so the `_mutual` telescope depends on
  which function is first (`:259-263`). Under `σ` this is a permutation of binders, which is O13b
  (definitional).
- **Domain.** `α = PSum D₀ (PSum D₁ … D_{n-1})`, in clique order (`Meta/ArgsPacker.lean:248-253`).
  Each `D_i` is the `PSigma` tuple of `f_i`'s varying arguments (`:64-77`).
- **Injections.** `inj_i v = inr^i (inl v)`, or `inr^{n-1} v` for the last summand
  (`ArgsPacker.lean:270-289`).
- **Motive.** The codomain motive is a `PSum.casesOn` tree over `α` (`mkCodomain`, `:313-344`).
- **The unary function.** `packMutual` (`Elab/PreDefinition/WF/PackMutual.lean:79-104`) builds
  `f₀._mutual` (`:66-73`). Its value is `ArgsPacker.uncurry` of the bodies, a case tree with
  `PSigma.casesOn` per arity, and recursive calls are packed.
- **Relation.** `elabWFRel` builds `wfRel` from the per-function measures. Each measure is a tuple per
  function. GuessLex fills it with `measures[k].fn` and the function-index literals
  (`WF/GuessLex.lean:762-774`). The measures are combined by a case tree over `α`.
- **Fixpoint.** `mkFix` (`WF/Fix.lean:289-319`) builds one of two forms:
  - `WellFounded.Nat.fix α motive measure F` when `wfRel` is `invImage f Nat.lt_wfRel` (`:281-287,
    300-301`);
  - otherwise `WellFounded.fix α motive wfRel.1 (opaqueId wfRel.2) F` (`:302-306`).
- **Case refinement.** `F := λ x F. …`. The packed argument `x` is refined by `processSumCasesOn` and
  `processPSigmaCasesOn` (`:159-203`).
- **Recursive calls.** Each becomes `F arg h` with `h` a goal of type `rel arg x`, the binding domain
  of `F arg`'s type (`:78-87`).
- **Goals.** Goals are grouped per function by `ArgsPacker.unpack` (`:239-248`) and closed by
  `clean_wf` (`src/lean/Init/WFTactics.lean:28-31`) and `decreasing_tactic`, or by the function's
  `decreasing_by` (`Fix.lean:250-279`). Goals with equal types and nested contexts are merged first
  (`assignSubsumed`, `:216-230`).
- **Abstraction.** `addPreDefsFromUnary (cacheProofs := false)` (`WF/Main.lean:82`) runs
  `abstractNestedProofs`, which turns each decreasing proof of a *definition* into a theorem
  `f₀._mutual.proof_k : ∀ ctx, rel y x` (`Elab/PreDefinition/Basic.lean:120-128`). For a theorem,
  abstraction is skipped (`:121-122`) and the proofs stay inline.
- **Members.** `f_i := λ params. f₀._mutual fixed (curryProj … i)` (`WF/PackMutual.lean:127-143`).
- **Equations.** `EqnInfo` records `argsPacker` and `fixedParamPerms` (`WF/Main.lean:86`). Then come
  `_mutual.eq_unfold` and the per-member unfold lemmas (`:88-94`).

**Transport `Φ_σ`:**
- **(R).** `f₀._mutual ↦ g._ix._mutual`, where `g` is the first canonical member.
  `f₀._mutual.proof_k ↦ proof′_k`, numbered in the canonical traversal order; the numbering is
  metadata. References to members go through `N`.
- **(A).**
  - `α ↦ α′`, with `D_i` at summand `σ i`.
  - `inj_i ↦ inj′_{σ i}`.
  - Every `PSum.casesOn` tree over `α` becomes the canonical tree with leaf `i` at position `σ i`. The
    trees are the motive, the body's case split, the measure's case split and `F`'s refinement. The
    motives inside the trees are rebuilt by `mkCodomain`'s rule.
  - `PSigma` parts are per function and are unchanged.
  - The fixed-parameter telescope is reordered to the first canonical member's order.
  - The fixed-parameter binders of the abstracted `proof_k` theorems are reordered the same way
    [measured, A5T; omitted from the first draft].

- **(S).** Each `proof_k : ∀ ctx, wfRel.rel y x` becomes `proof′_k : ∀ ctx′, wfRel′.rel y′ x′`.
  `wfRel′` combines the *same* per-function measures by the canonical case tree (D22: Lean's measure,
  pinned and re-indexed). `y′` and `x′` are the canonical injections of the same tuples.
- **Proof bodies.** The value of `proof′_k` is `Φ_σ(p_k)` when `p_k` passes the grammar check;
  otherwise it is `p_k` **verbatim**.

**Why both are proofs of the re-stated obligation** [argued]. `Φ_σ(T)` and `T` reduce to the same
proposition:
- δ of `invImage`, then the `WellFoundedRelation.rel` projection, then δ of `InvImage`;
- β;
- ι of the case trees on injections, then of `PSigma.casesOn` on `PSigma.mk`.

Both end at `r.rel (m_b c⃗) (m_a a⃗)`, with `r` the same lexicographic instance (GuessLex pads every
tuple to one length). The kernel's definitional-equality check performs exactly these steps, and none
unfolds a theorem, which Ix never does. So `p_k : T` is accepted at `Φ_σ(T)` by conversion.
`Φ_σ(p_k) : Φ_σ(T)` holds by the homomorphism argument of §5.0.

What `p_k` typically contains: the cleanup is a `simp only` over definitions (`clean_wf`), and the
default tactic works on the cleaned goal, which mentions only measures. So the packing typically
occurs in `p_k` only in copies of the goal: `Eq.mpr`/`id` annotations and motives of the rewrites.
Those are recognised by the grammar.

[measured, A1G] On every well-founded fixture, the bodies of the `_mutual._proof_k` decreasing
proofs differed between presentations only in the `id` goal copies, so the grammar must recognise
`@id T p`. The same fixtures show three further features:
- when the measure is lexicographic, the relation's own well-foundedness proof is abstracted as
  `_proof_1`, and it is equal across presentations (`W3`);
- both fixpoint routes occur: `WellFounded.Nat.fix` for a single `Nat` measure, `WellFounded.fix`
  otherwise;
- some theorem cliques that look structural take the well-founded route (`TS`).

**Closed values.**
- On the `Nat.fix` route (single `Nat` measure), `WellFounded.Nat.fix` is a fuel-driven `Nat.rec`
  marked `@[implicit_reducible]` (`src/lean/Init/WF.lean:470-499`). Canonical and Lean members
  therefore agree on closed arguments by evaluation.
- On the `WellFounded.fix` route they never meet by conversion: `fix` goes through `Acc.rec` on a
  proof (`Init/WF.lean:125-137`).
- Either way, open arguments need O15's correspondence: `WellFounded.induction` and `fix_eq`/
  `Nat.fix_eq` once on each side (`Init/WF.lean:139-142, 513-517`) [argued, MUT §4.1].

### 5.2 `partial_fixpoint`

**Lean's encoding** (`Elab/PreDefinition/PartialFixpoint/Main.lean`):
- **Instances.** Per function, `CCPO (∀ x⃗, r_i x⃗)` (or `CompleteLattice` for `inductive_fixpoint`/
  `coinductive_fixpoint`) (`:87-113`).
- **Packing.** `packedType := PProdN.pack 0 types`, in clique order (`:125`), with
  `packedInst := mkPackedPPRodInstance` (`:135`).
- **Functionals.** `F_i := λ f. body_i`, with each recursive call replaced by
  `PProdN.proj n idx t f` applied to the varying arguments (`replaceRecApps`, `:24-30`).
- **Goals.** One per function: `monotone (α := packedType) packedPartialOrderInst type_i inst_i F_i`,
  proved by `solveMono` or by the user's term (`hints[i].term?`) (`:167-186`).
- **Combination.** `PProdN.genMk mkMonoPProd` combines the proofs with `PProd.monotone_mk`, in clique
  order (`:65-75, 187`).
- **Value.** `mkFixOfMonFun packedType packedInst hmono` gives `Lean.Order.fix`
  (`Init/Internal/Order/Basic.lean:452`). It is named `f₀.mutual` (`:189-197`).
- **Members.** `f_i := PProdN.proj n i packedType (f₀.mutual fixed) varying` (`:205-216`).

**The recursive-call sub-proofs.** `solveMonoCall` (`src/lean/Lean/Elab/Tactic/Monotonicity.lean:
84-106`) builds the monotonicity proof of a call `f.p₁….p_k a⃗` *inside out*:
- `monotone_id` for `f`;
- then one `PProd.monotone_fst` or `PProd.monotone_snd` per projection step, instantiated at that
  step's intermediate `PProd` type and instance;
- then one `monotone_apply` per argument.

**Transport `Φ_σ`:**
- **(R).** `f₀.mutual ↦ g._ix.mutual`.
- **(A).**
  - `packedType`, `packedInst` and the `PProd.monotone_mk` tree are rebuilt in canonical order.
  - In each `F_i`, `PProdN.proj n idx ↦ PProdN.proj n (σ idx)`.
  - The members project at `σ i`.
- **(S).** Each goal mentions `packedType` and `F_i`, and becomes the canonical goal.
- **(G).** In each `hmono_i`, the sub-proof for a recursive call through path `π_idx` is replaced by
  `solveMonoCall`'s recipe for the path `π_{σ idx}`.
  - The paths can have different lengths: `.2.1` against `.1`. So the number of `monotone_fst`/
    `monotone_snd` applications changes. This is regeneration, not renaming.
  - The recipe is deterministic and term-level: `whnfUntil` to the `PProd` instance, then lemma
    application. No search runs.
  - Every other part of `hmono_i` (`monotone_const`, the `ite`, `bind` and `match` lemmas of
    `solveMonoStep`) mentions the packing only as the domain and its instance, and is (A).

**Fallback** (user-supplied monotonicity terms, or anything that fails the grammar check):
`hmono′_i := monotone_compose (mono φ) hmono_i`.
- Here `φ : packedType′ → packedType` is the re-association `f′ ↦ ⟨f′.π_{σ 0}, …⟩`.
- `F′_i ≡ F_i ∘ φ` holds by β and projection of a constructor [argued].
- `monotone_compose` is at `Init/Internal/Order/Basic.lean:209` in the 4.33.1 tree that could be read;
  its 4.34 location is [open].
- `mono φ` is a `PProd.monotone_mk` tree over projection-path proofs, built by (G).
- The fallback embeds Lean's `hmono_i`, whose content follows Lean's packing. It therefore enters the
  non-canonical set (cause `SHAPE`), but it is always a proof (§0.1).

**Faithfulness of the members** is O16: `Lean.Order.fix` commutes with an order isomorphism of the
product.

**[proved], A5F:** `Ix/Compile/Clique/FixPerm.lean` (bookmark `jcb/ix-cc-a5f`) proves it with no
`sorry` and only the standard axioms:
- `fix_iso`: `fix` commutes with an order isomorphism;
- `lfp_monotone_iso`: the lattice variant;
- the `PProd` re-associations, as order isomorphisms;
- `fix_iso_proj`: the member correspondence `f_i = (fix F′).π_{σ i}`, directly, up to a definitional
  conversion (β and projection of a constructor) that `fix_swap` checks.

The module needs `import all Init.Internal.Order.Basic`, because `admissible` and `fix` are not
exposed. Phase B's audit must account for this.

### 5.3 Structural recursion

**Lean's encoding** (`Elab/PreDefinition/Structural/`):
- **Grouping.** `Positions.groupAndSort` groups the functions by the type former of their recursive
  argument (`Main.lean:46`; `Basic.lean:59-66`):
  - the groups are in the inductive's `all` order, nested auxiliaries included;
  - **within a group, the functions are in clique order.**
- **Motives.** One per function (`mkBRecOnMotive`, `BRecOn.lean:213-219`). Each group's motives are
  packed by `PProdN.packLambdas`, giving `P₁ x ×' P₂ x …`, or `PUnit` for an empty group
  (`mkBRecOnConst`, `:243-260`).
- **Functionals.** `mkBRecOnF` with `replaceRecApps` (`BRecOn.lean:125-206`):
  - a recursive call becomes a path into the `below` dictionary, found by `searchPProd` over `.proj
    PProd i` and `.proj And i` (`:25-35, 120-123`);
  - under a `match`, `MatcherApp.addArg? below` creates a **transformed matcher**: a new constant
    whose type carries `below`'s type, and so the packed motives (`:186-201`).
- **`_f`.** Each functional is extracted as an `.abbrev` definition `f._f := λ xs. F_i` (`Main.lean:
  89-107`), whose *type* mentions `T.below` at the packed motives.
- **Packed functionals.** They are packed per group by `PProdN.mkLambdas` (`Main.lean:113-114`).
- **Values.** `f_i := λ ys. PProdN.projM size idx (T.brecOn_k ps packedMotives is x packedFs) rest`
  (`mkBRecOnApp`, `BRecOn.lean:289-300`).
- **Inductive predicates.**
  - The result types are let-bound as `funType_1 … funType_n` in clique order (`withFunTypes`,
    `IndPred.lean:105-120`), and the value is wrapped in them (`BRecOn.lean:300`).
  - "below" matchers are created by `IndPredBelow.mkBelowMatcher` under the function's name
    (`IndPred.lean:84-91, 150-155`).
- **Fixed parameters.** In the first function's order (`FixedParams.lean:259-263`).

**Transport `Φ_σ`.** Only the order *within a type-former group* depends on the clique. Across groups
the order is the inductive's `all` order; when the block itself changed, O4 handles it. Let `σ_k` be
the restriction of `σ` to group `k`.
- **(R).**
  - `f._f ↦ g._ix._f`.
  - Each transformed matcher becomes a canonical transformed matcher, itself transported by (A).
  - Each IndPred "below" matcher is *transported* by (A) on its `funType` binders, not regenerated
    [measured, A5T; this corrects the first draft].

- **(A).**
  - The packed motive of group `k` is rebuilt in the order `σ_k`, and so is the packed functional
    tuple.
  - The final projection `projM size idx ↦ projM size (σ_k idx)`.
  - In each functional, every path into `below` splits in two. The prefix walks the inductive's
    `below` structure for the recursive field: it does not depend on the clique and is unchanged. The
    suffix is the position inside the group's packed motive: it is re-associated.
  - The `_f` type follows.
  - `let funType_i` is re-ordered. That is ζ-equivalent, i.e. O13a, definitional.
- **No (S) and no (G).** A structural definition carries no separate proof obligation: its
  "decreasing" evidence *is* the `below` path, which is a term.

**The fallback is the baseline, the faithful form of §0.1.** If a functional uses a packed value outside the grammar (passes a
`below` dictionary to a helper other than a transformed matcher), the whole clique keeps its baseline.
That is faithful.

**Carried equation lemmas of a repacked group (D-M5-1, 2026-10-07).** A member's `eq_def` unfolds the
member through the encoding. Lean's proof (`Structural.mkUnfoldEq`) carries the group's packed values
through `brecOn.go` and `brecOn.eq`, the β-reduced packed functional and tuple, a λ over a packed value
(`congrArg`'s motive) and the `below` dictionary unfolded by `whnf` in the splitter's motive. (A)
re-associates none of these: transported as members are, the lemma does not type-check (the certified
checker rejected such `eq_def`s with "application type mismatch"). So when some group of two or more
functions is repacked (`σ_k` not the identity), a carried lemma that mentions an encoding constant (a
functional `_f`, a "below" matcher, a `below`/`brecOn` constant of the block or a constant under one) is
outside the grammar and the clique keeps its baseline, cause `SHAPE`
(`Clique.transportStructural`, `StructLayout.repacks`). Every carried lemma of a structural clique
mentions a functional (that is what makes it carried, `Pass.scheduleCliques`), so a repacked structural
clique whose members' equation lemmas are realised (by `eq_def`, `unfold`, `simp [f]` or an `eq_N`)
stays in Lean's form. When no group is repacked (groups of one function, or a group already in the
canonical order) no packed value moves and the lemmas are transported with the members (fixture
`Tests/Ix/Compile/CliqueOwnership/Lemmas.lean`, suite `clique-ownership`). Carrying a repacked group's
unfolding proof (an extension of (A) to the shapes above, or regenerating the proof, decision 3) is not
done.

**The correspondence is not definitional.** The canonical and Lean members are stuck `brecOn`
applications at a variable. It is O14: joint induction with the block's recursor, where the repacking
map on the `below` dictionaries closes each case [argued, old plan §3.5].

### 5.4 Theorems proved by mutual recursion

There are three routes:
- structural over data: the `brecOn` route, with `_f` still added;
- structural over an inductive predicate: the IndPred route;
- well-founded: the theorem `_mutual` itself, with its decreasing proofs inline because
  `abstractNestedProofs` skips theorems (`Basic.lean:121-122`).

For all three, Lean records no `EqnInfo` (§2.7).

**What transport gives.** The transported body is `Φ_σ` of Lean's body, by §5.1 or §5.3. It proves
`tr_N(φ)`, the theorem's translated statement, which never mentions the encoding [argued]. Lean's
own body proves the same statement, so **the fallback for a theorem is its baseline**, always valid.
For theorems, transport matters only for the canonicity of the theorem's address.

**What transport needs.** A canonical order for the theorem clique. Without a specification, only two
sources exist:
- (i) the statements;
- (ii) a **recovered specification**: the inverse of the encoding applied to Lean's bodies. That
  means reading recursive calls back from `F (inj_j ⟨a⃗⟩) h` for well-founded recursion, and from
  `below` paths against the packed motives for structural recursion. The result is checked by
  re-encoding it and comparing with Lean's bytes.

Decision (Q6, owner 2026-10-03): (i) first, then (ii) for statement ties. Otherwise Lean's form (the
baseline) is used, recorded with cause `NOSPEC`.

**As implemented** [measured, A5F]. `Recover.lean` builds source (ii):
- It reads the recursive calls back from Lean's bodies.
- It accepts them only if rebuilding by Lean's own construction gives Lean's term back.
- It orders the clique by Pass 1's classes.

Results:
- TR and TQ come out distinct.
- Wherever statements decide (TS, TM, TW, TP), it agrees with statement order.
- The inductive-predicate route is not recovered, so IP falls back to `NOSPEC`.
- **A complete tie** (TN: one class) is ordered by Pass 1's seed, the same rule as blocks (Q2), and
  is not recorded `NOSPEC` (orchestrator's decision).

`NOSPEC` therefore remains only where recovery fails.

**Equation lemmas of definitions** (`eq_N`, `eq_def`, `_mutual.eq_unfold`) have proofs that unfold
Lean's encoding. When a member maps to the canonical form, a member's own equation lemma is carried
with the clique (it is in the clique's unit) and regenerated over the canonical form; the clique stays
in Lean's form only if one of its own lemmas cannot be carried. Any other constant that unfolds Lean's
encoding of a transported clique is refused with a named error naming it and the clique (§6.3, "callers
adapt"; `Pass/Cliques.lean`, `cliqueCallers`); the clique is never demoted for a caller. The
equations are realised lazily (MUT §1.2), so which of them exist varies between builds (A Δ13). The
canonicity claim excludes them (§7.1).

**The plan is computed once** (M6 precondition, `Pass/Cliques.lean`, `cliquePlanFor`). A clique's plan
(its order, ownership, transport, carried lemmas and record: `planClique`) is needed by every block of
its unit that the hook visits: each member's block, each carried lemma's block (each its own block), and
each caller's block for the refusal check. It is a function of the clique, its own logical unit and its
dependencies only: the input constants it reads are the members, their encoding constants, carried
lemmas, matchers and `below` definitions, and the addresses it reads are those of the members'
references, which `scheduleCliques`' edges compile before any block that plans the clique. So every such
block computes the same plan, and the compiler computes it once: the first block that needs it puts it in
the block state, the driver merges it into a table keyed by the clique (`all₀`;
`CompileEnv.p3CliquePlans`, merged like the other Pass 3 tables, the first entry of a key kept), and later
blocks read it from there. The table is a memo of that function, not a new input: it reads no caller and
no schedule (which block filled an entry, or whether a block of the same wave had to compute the plan
again, changes no byte and no record, only the time). `IX_PASS3_CHECK_PLANS=1` recomputes every plan the
table supplies and fails the compile on any difference (suite `pass3-plan-cache`).

### 5.5 The non-canonical set: where two presentations can still give different transported terms

These are the causes that the non-canonical set must be able to record (§7.2).

| Cause | Mechanism | Encoding |
|---|---|---|
| `TACTIC-ASYM` | Lean's proof for presentation `P₁`, transported, differs from Lean's proof for `P₂`, because the tactic's output depends on the order beyond the packing. Candidates: user `decreasing_by` or monotonicity scripts that depend on goal order *across* functions; `simp` traces when the goal still contains packed structure; proof terms mentioning the packed type through generic lemmas (`PSum.inr.injEq`, `sizeOf` of a `PSum`). Goals are grouped per function (`Fix.lean:239-248`) and merged only when their types are equal (`:216-230`), so the default path is symmetric [argued]. On probe WA (a `decreasing_by` depending on goal order) the transported proofs are exact [measured, A5T]. **Observed on WH** [measured, A5F]: `assumption` and `omega` take the most recent `1 < k`, and the fixed parameters in that context follow the first function's order | WF, `partial_fixpoint`, theorems |

| `SHAPE` | The grammar check fails, so the fallback (verbatim proof, composition with `φ`, or the baseline) carries Lean's packing in its content | all |
| `GUESSLEX` | GuessLex enumerates measure combinations in function order, uniform ones first; function-index measures `.func i` come last, in index order; it takes the first that works (`GuessLex.lean:524-629`). Two presentations may pick different per-function tuples. Pinning (D22) keeps each faithful, but the canonical functionals then differ | WF |
| `RECARG` | Structural `allCombinations` takes the first working combination in clique order (`FindRecArg.lean:228-310`, per MUT §1.2). **Observed on RA** [measured, A5F]: Lean recurses on `x` under one order and on `x_1` under the other | structural |

| `ORDER-STMT` | Statements that follow the order: `_mutual.eq_unfold`, `mutual_induct`, `induct`, bare `@f._mutual`. These are faithful only | all |
| `NOSPEC` | A theorem clique whose order cannot be determined (§5.4): recovery of the specification fails. Observed on IP, the inductive-predicate route, which is not recovered. TN's complete tie is now ordered by the seed [measured, A5F] | theorems |

| `LAZY` | The equation lemmas Lean realises lazily (`f.eq_def`, `eq_N`, `eq_unfold`) are excluded from the canonicity claim, because which of them exist varies between builds (A Δ13). Their proofs also unfold the encoding | all |

The numbering of `proof_N`, `match_N` and `_f` names, and which declaration owns a shared matcher,
are names only. They are metadata, not members of the non-canonical set.

### 5.6 What is measured about cliques

**The first measurement under permutation (A1G).**
- *A1G* is `plans/wave1/a1g.md` (untracked); the compared terms are in `a1g-clique-terms.txt` beside
  it.
- 51 twin families, 58 presentation pairs, 422 differences. Every difference is recorded, with cause
  and evidence, in `Tests/Ix/Compile/NonCanonical.lean` [measured].
- **When A1G measured, the compiler did nothing to definition cliques**, so every difference between
  presentations was a difference in Lean's own output. That is no longer so: since the flip the clique
  hook (`Ix/Compile/Pass/Cliques.lean`, §5.7, §1.6.2) transports definition cliques by default.
  Init+Std: 5 of its 7 definition cliques are transported (the changed-set record of the landing gate
  of `6634c58f`, `ix-cc-proof2/out/land-initstd-on.changed.json`: 5 `transported`, 2 `baseline`).
  Mathlib: 9 of 21, of which the 7 well-founded ones move bytes and the 2 structural `Ring` cliques
  compile to the same addresses as under `IX_PASS3=off` [measured, M1-g §2–§3,
  `plans/review2/M1-g-mathlib-measurement.md`]. The twins' differences under the default are the 959
  of `Tests/Ix/Compile/NonCanonicalDefault.lean` (`[twins] (default) 959 differences; 0 unrecorded, 0
  stale entries`, same gate; §7.4).

**Already canonical** [measured, A1G]:
- structural recursion with one function per type former;
- theorems proved by structural recursion over a mutual inductive;
- renamings of members and binders;
- permutations that keep each type-former group's clique order;
- `partial def` cliques, a kernel SCC that Ix sorts.

This agrees with ORA (DQReord 53/53) and with MUT §1.7.

**Packing order only, 93 constants: what transport fixes** [measured, A1G].
- The families cover structural, well-founded (including theorem cliques), `partial_fixpoint` and
  inductive-predicate encodings: `SA`, `S3`, `SX`, `TP`, `SP`, `WD`, `W3`, `WT`, `WB`, `WP`, `TS`, `TW`,
  `PF`, `IP`.
- The differences are exactly those §5.1–5.3 predict:
  - `PSum`/`PProd` order in domains, motives, case trees, measure trees and tuples;
  - injections and projection paths (A);
  - decreasing obligations re-stated over the packing (S), with bodies differing only in `id` goal
    copies;
  - the `monotone_fst`/`monotone_snd` chains of the monotonicity proofs (G);
  - the `let funType_i` order and the "below" matchers' `funType` binders (O13a);
  - the fixed-parameter telescope in the first function's order (O13b).
- `IP` keeps the inductive fixed and so separates MUT's F9 confound: the predicate order is not
  involved.

**`GUESSLEX`, 3 constants: the first measured case** [measured, A1G family `WG`].
- GuessLex measures `ga` by `x` under one order and by `y` under the other.
- So the canonical functional itself differs. Transport cannot fix this; D22 keeps each presentation
  faithful.
- The decreasing proofs are identical with their roles swapped.

**Faithful only** [measured, A1G]:
- 18 `LAZY` (`f.eq_def`);
- 8 `ORDER-STMT` (`f._mutual.eq_def`).

**Inherited, 17.** Value theorems and `_sunfold` that reference a differing member.

**Not seen** [measured, A1G]: `TACTIC-ASYM`, `SHAPE`, `RECARG`, `NOSPEC`.
- `omega`, `simp`, `decreasing_tactic` and an explicit `decreasing_by omega` all gave proofs equal up
  to the packing.
- Function-index measures travel with their functions (`TS`).
- Three families that would provoke the unseen causes are still to be written:
  - a `decreasing_by` that depends on goal order;
  - an ambiguous recursive argument (`RECARG`);
  - a theorem clique with tied statements (`NOSPEC`).

**Related gates** [measured, A1G]:
- **Auxiliary oracle:** 1,501 of 1,908 auxiliary pairs are byte-equal to Lean's own constructions,
  and every exception falls in an expected class. A further 268 auxiliaries of mutual blocks cannot
  be compared by address with Lean's form until D6 (one constant per auxiliary).
  After the A2 migration [measured, A2 migration]: 1,772 of 1,908 are byte-equal. The 136 that differ
  are all in the split classes of §4.7 ((d) 111, (c) 14, (a) 9, (f) 2), and 300 one-sided
  auxiliaries are class (b).
  `PACKAGING` went from 268 to 0 with D6, and `NESTED-ORDER` (the 84 Cutsat rows whose nested
  auxiliaries were in the structural order) went to 0 with discovery order. Both classes now fail the
  suite.
- **Schedule identity (§6):** the sequential driver, the wave driver at 1, 4 and 16 workers, and
  `compile-lean` at 1, 4 and 16 workers give identical bytes (14,854,564 B on the fixture closure).

**Earlier measurements, still valid:**
- the theorems of a mutual structural pair change address when the definitions are reordered
  [measured: old plan §4.6];
- about 5 order-dependent safe `mutual` definition cliques across all libraries, of which about 2–3
  would reorder [estimate, MUT §5.1];
- four well-founded `_mutual` in an Init-sized environment [measured: MUT §5.1].

### 5.7 The transport as implemented (A5T)

*A5T* is `plans/wave1/a5t.md` (untracked). The code is at `Ix/Compile/Clique/**` on the A5-core
workspace. Everything in this subsection is [measured, A5T] unless marked otherwise.

**Scope.**
- About 2,400 lines, total and pure over `Ix.Expr`.
- It covers well-founded, structural (including the inductive-predicate route) and
  `partial_fixpoint` cliques, and theorem cliques on all three routes.

**Exact oracle.**
- Transporting presentation P₁ onto P₂'s order reproduces P₂'s constants exactly for 100 of 100
  constants. These are A1G's 93 packing-order-only constants plus 7 of the new family WA.
- Lean's `addDecl` accepts 130 of 130 transported constants.
- Negative controls:
  - a wrong permutation fails the oracle;
  - a stray partial injection gives the verbatim fallback, recorded `SHAPE`, kernel-accepted;
  - a stray projection gives the composition fallback, recorded `SHAPE`, kernel-accepted.

**Residual causes.**
- **`GUESSLEX`** is confirmed on WG. The members transport exactly, and `_mutual` and both proofs
  are equal once the measure is masked. The *caller* decides `GUESSLEX`, because it needs both
  presentations.
- **`TACTIC-ASYM`** was not observed on the probe WA. Lean groups the decreasing goals per function,
  so the transported proofs are exact. A5F then observed it on WH (below).
- **`NOSPEC`**: `Canon.statementOrder` implements Q6's first source, statements. Under statement
  order, both presentations of TS, TM, TW, IP and TP give identical constants. The recovered
  specification came with A5F (§5.4).

**Fallbacks.** These are implemented as §5.1–5.4 say, each recorded `SHAPE`:
- the verbatim proof under the re-stated obligation;
- `monotone_compose (mono φ) h`;
- the whole clique in Lean's form.

**Deviations from §5.1–5.3:**
- splitting a structural path needs the environment, to unfold `below`; the transport is therefore
  not purely syntactic;
- the fixed-parameter binders of abstracted proofs are reordered (now in §5.1);
- the inductive-predicate "below" matchers are transported, not regenerated (now in §5.3);
- in `partial_fixpoint`, instance trees and application-form paths are re-associated as well;
- the canonical name of the packed constant is an *input* to the transport.

### 5.8 The fixture families closing the open items (A5F)

*A5F* is `plans/wave1/a5f.md` (untracked); the code is on bookmark `jcb/ix-cc-a5f`. Everything in
this subsection is [measured, A5F] unless marked otherwise.

**New families.** Ten new twin families, with 2–3 presentations each:

| Family | What it probes |
|---|---|
| RF | reflexive structural recursion |
| NS | nested structural recursion |
| LI, LC | lattice fixpoints (`inductive_fixpoint`, `coinductive_fixpoint`) |
| PU | a user-written monotonicity proof |
| RA | the recursive-argument choice |
| WH | a `decreasing_by` that depends on hypothesis order |
| TR, TQ, WU | theorem and well-founded families |

They add 70 recorded differences. The twins gate now stands at 497 differences, 0 unrecorded and 0
stale.

**Causes measured for the first time:**
- `RECARG` on RA;
- `TACTIC-ASYM` on WH;
- `SHAPE` on PU: user monotonicity proofs take the composition fallback, and the kernel accepts it.

**Three silent holes in the transport, found and fixed:**
1. **A well-typed miscompile.** An untransported reflexive path produced a term the kernel
   accepted: `(x 0).1.2` where `.1.1` was meant. It shows why transport must fail closed.
2. A user proof rearranged piece by piece came out ill-typed.
3. A user's own `PSum` value was moved.

**Grammar changes:**
- structural paths through applications of reflexive fields are followed;
- a path the walk cannot follow now **fails** instead of passing unchanged;
- lattice fixpoints spell components as `ImplicationOrder`/`ReverseImplicationOrder` in some
  positions and as `Prop` in others, and the grammar handles each position separately;
- user proofs are detected and sent to the fallback;
- the well-founded grammar is restricted by position. WU is the negative control, 5/5 exact. This
  settles the positional question of §5.7.

**Oracle.**
- The exact oracle is now 147/147: wave 1 97/97, WA 7/7, the new families 43/43.
- The kernel accepts 189/189 transported constants.

**Still open:**
- the kernel evidence for the 70 new entries is not measured;
- the composition fallback is untested on a lattice clique with a user proof.

---

## 6. Determinism: the compiler as a function of the closure

### 6.1 Global reads and order dependences: the A7 worklist

A7S §4 refreshes the first draft's inventory. Lines are at `b86e2043`.

Columns:
- **Reach** is where the dependence lands: **content** (a stored address), **side-car** (metadata,
  `Named.original`, hints, names) or **neither** (not serialized).
- **Measured** means it reaches nothing today on Init+Std, Mathlib or the fixtures: Lean and Rust
  agree byte for byte there (A7S).

| # | Site | Dependence | Reach | Removed by |
|---|---|---|---|---|
| D1 | merges in both drivers (`CompileDriver.lean:265-318`, `mergeCompiledBlock`) | last-wins name, aux and plan claims | would have, on a conflict | **Done** [measured, A7S]: insert-once with Rust's `conflicting claims for name` error in both Lean drivers, cross-SCC and prereq paths included (`checkBlockClaims`, `Ix/CompileDriver.lean:367` at `564d03f0`). Pass 3's three merges are insert-once too [A3M]. `Named` stays last-wins by design |
| D2a | promotion path (sequential `:519-610`; wave `auxBlockOutcome` `:692-735`, applied `:738-819`) | a block already claimed by a prereq or by another block's tail takes the promotion route | content and side-car (`Named.original`) | A7: each auxiliary compiled with its owning block; may move side-car bytes |
| D2b | `precompileAuxGenPrereqs` (`:380-434`) | the seed closure is compiled before the schedule, then re-promoted | side-car, possibly | A7: seeds are ordinary dependencies |
| D2c | `compileConstNoAuxPure` (`:156-240`) | reads the global `auxGenExtraNames`; `leanAll` comes from the first match in `Set` order | side-car | A7, with D2a |
| D2d | scheduler asymmetry (`resolveAddrPure acc.cenv lo`, `:519`/`:694`) | if aux-gen claims a name first, a user block of that name is promoted; in the other order it is a conflict (now raised) | content and side-car, on such input only | A7: claim set = f(block) (D11) |
| D3 | `surgeryFree` (`Ix/CompileM.lean:722-728`, dispatch `:1770-1778`) | one of two expression compilers, chosen by whether any plan exists anywhere | content in principle | A3 (one compiler) |
| D3b | `compilingIsAuxRegen` (`CompileM.lean:1040-1051`, `:1320-1336`) | whether a constant is a regenerated auxiliary, read from global maps | content (surgery) | A3 |
| D4 | `nameForAddr` (`Ix/AuxGen/Kernel.lean:729-745`) | `HashMap` scan picks among aliases | side-car only [measured: none] | A7: anonymous mode and the canonical alias |
| D5 | provisional name-hash addresses (`Kernel.lean:59-77`; `CompileAux.lean:37-46`) | an unresolved name is keyed by its hash | none measured; leak [open] | A7: ingress from the closure only |
| D6 | synthetic primitive names (`Kernel.lean:150-156`) | display names | measured none | A7 |
| D7 | kernel intern history (`CompileDriver.lean:118`) | binder and alias names | display; mitigated | A7, by anonymous mode |
| D8 | `]!` sites | panic, print, continue with `default` | if one fires; 0 `PANIC` on Init+Std | A7: total code or named errors |
| D9 | SCC keying (`Ix/CondenseM.lean:43-86`); `readyQueue.back!` `:516`; `unresolvedNames[0]!` `:548`/`:717` | `lo` and `Set` order | neither [argued] | A7 |
| D10 | seed and representative (`Ix/Environment.lean:149-153`) | name hash | side-car only | **kept** (Q2) |
| D11 | aux-gen claim set (`Patches.lean:302-318`; `registerAuxAliases` `CompileAux.lean:367-405`) | the alias pass skips names already resolved globally and clones `Named` from the global registry | side-car, possibly | A7: claims and alias metadata from the block |
| D12 | in-block plan checks (`CompileAux.lean:1018-1090`) | checked against the snapshot only; Rust inserts as it goes | content, on such input only | A3 (plans retire) |
| D13 | global registries read by generators (`Nested.lean:1059`; `BRecOn.lean:1815, 1855`; `Below.lean:1194`) | the class ordering of another block (closure-determined); dead reads on the compile path | content (layout), closure-determined | A7: pass the closure in |
| D14 | `assembleEnv` `addrToName` (`CompileDriver.lean:439-442`) | last-wins over `HashMap` order | neither | A7 |
| D15 | which block reports a wave conflict | arrival order | neither | inherent; the error itself is schedule-free |
| D16 | Rust keeps a refused block's primary claims (`compile.rs:4740-4800`) | dependents compile against leftovers | content (partial output), Rust only | Rust catch-up |
| D17 | `exprCompileDepth` (A3W §3.6) | fuel sizing by a tree walk, exponential on DAG-shaped proofs; one Mathlib block stalled 20+ min under Pass 3, because plan-free compiles take the ordinary compiler | time only (no bytes) | **Fixed** [A3M]: `@[implemented_by exprCompileDepthImpl]`, a per-node memoised height (`Ix/CompileM.lean:835-857` at `564d03f0`). The structural definition stays for the proofs. Verified on Init+Std and the fixtures; Mathlib was not rerun. The runtime implementation is a `partial def` (`exprCompileDepthMemo`) |

`]!` count [measured, A7S]:
- in the first draft's scope: 251 lines and 278 occurrences at `b86e2043` (252 lines at `f829b760`);
- in `Ix/Compile/**` (the Phase A code itself): a further 173 lines and 245 occurrences, most of
  them in `Clique/*`.

A7's order: D8; then D9/D14; D13; D11+D2d; D2a–c (the side-car migration, if any); D4–D7 with
anonymous mode.

**Schedule identity** [measured, A7S and A1G2]. `compile-schedule-identity` runs seven schedules:
sequential, wave 1/4/16, and `compile-lean` 1/4/16. It requires identical bytes, and identical
refusals equal to the closure's `expectedRefusals`, with their messages. At `de10a62e` all seven
gave 14,835,441 B and the same 12 refusals.

### 6.2 The definition Phase A adopts

**Definition.** `compile(L) := foldl step ∅ (blocks L)` where:
- `blocks L` lists the components and cliques (§2.1, §2.7) in a **topological order of the
  condensation DAG**, with ties broken by a fixed key. The key may be the Lean name of the block's
  first member in Lean order; by the theorem below, the choice cannot affect the output.
- `step acc B := acc ∪ out(B)`, where
  `out(B) := compileBlock(input(B), {(n, addr n, plan n) | n ∈ closure(B)})`.
  - `input(B)` is the prepared Lean data of `B`'s members. For an inductive block this includes its
    Lean auxiliaries, whose images are compiled with the block.
  - `closure(B)` is the set of constants `B` references, transitively through types, values and
    rules (Def 1.3), **together with the auxiliaries of every block reached and of `B` itself**
    (the logical units of §6.3). The closure carries resolved addresses and, for changed blocks, the
    plans (images, `N`, `σ`).
- `∪` is a disjoint union of per-name maps. A name assigned twice is an **error** unless both
  assignments are equal. Content-keyed tables (blobs, shared subterms) are unioned by content.

**Theorem to state and prove (Phase B L1; A7 gate):** `out(B)` reads nothing outside
`input(B) ∪ closure(B)`. Consequently `compile(L)` is the same for every topological order, every
wave partition and every worker count, and a closure compile of `X` agrees with the whole compile on
every constant in `X`'s closure [argued].

**What the definition removes:**
- **D1, D2:** no promotion, no pre-compilation by another block, no live reads. Every block is
  compiled by its own `step`. An auxiliary of a block is compiled with that block (one constant per
  auxiliary, D6), never by another block's tail.
- **D3:** one expression compiler. The no-plan path is the special case "every plan is the identity",
  stated per block from the block's own closure.
- **D4:** the generators' display metadata is taken from the block's own Lean declarations.
  - Kernel queries run in **anonymous mode** (Phase A §3.2), so the result of a query never supplies
    a name.
  - Ingress through an alias needs *some* name with that address, and all aliases have equal content.
  - Where a name must be recorded, the **canonical alias** is the alias whose defining block comes
    first in the fold order, then the first in canonical position, then the first in seed order.
- **D5:** kernel ingress resolves addresses from the closure only. A constant outside the closure is
  never ingressed, so no provisional address exists.
- **D6:** each primitive's display name is the real Lean name chosen by the canonical alias rule.
  Primitives are recognised by address and shape, never by name.
- **D7:** subsumed by anonymous mode plus metadata from the source declarations.
- **D8:** every `]!` is replaced by total code or by a named error that reports the block.
- **D9, D10:** the seed stays the name hash (§2.3, owner decision); it affects only metadata (§3.3). `lo` and `Set` order are never observed.

**What the wave and speculative drivers must satisfy.** They are optimisations of the fold, gated by
schedule identity: byte-equal output for every driver, every worker count, and closure against whole.
Three conditions together suffice [argued]:
- (i) a worker computes `out(B)` on a snapshot that contains `closure(B)`;
- (ii) merges are the disjoint union of §6.2;
- (iii) no worker reads anything outside its snapshot's closure.

A speculative driver that compiles `B` before its closure is complete must discard the result unless
the closure it read equals the final closure.

### 6.3 The block rule: what a block may read

§6.2 says the compiler is a fold over blocks and that each step reads only its input and its closure.
This section fixes what "input" and "closure" contain. It is the owner's rule, in the owner's words
(2026-10-04 and 2026-10-05):

> We should never use caller information to determine how we compile constants. Doing that would break
> the DAG and impact our ability to parallelize. We should be able to make local compilation choices
> using only the constant and its dependencies. This may require further changes to callers though,
> and that's fine.
>
> The rule about compilation only with the constant or its dependencies includes anything in the
> constant's block.
>
> Dependency is block by block, not constant by constant.
>
> Auxiliaries for a block can depend on other auxiliaries for the block, even if not in the same block
> per se, they're still in the same logical unit.
>
> Furthermore, a constant can look at the auxiliaries for any block it depends on.

**Terms.**

- A constant *references* another when its type, value or rules mention it.
- A **block** is a strongly connected component of the reference graph: a group of mutually recursive
  inductive types with their constructors, a clique of mutually recursive definitions or theorems, or a
  single constant. After Pass 1 "block" means the canonical component, so one Lean `mutual` declaration
  can become several blocks (§2.1).
- The **auxiliaries** of a block are the constants Lean generates mechanically from it.
  - For an inductive block: the recursors, `casesOn`, `recOn`, `below`, `brecOn`, `noConfusionType`,
    `noConfusion`, the size functions `_sizeOf_N`, the instances `_sizeOf_inst`, and their own helpers.
  - For a definition clique: Lean's encoding constants (`_unary`, `_mutual`, `_f`, the `_proof_k`),
    matchers, and the equation and unfolding lemmas.
  - Some are generated **eagerly**, with the declaration. Others are generated **on demand**, when a
    later declaration first asks for them (equation lemmas, `_arg_pusher` lemmas, splitters).
- The **logical unit** of a block is the block together with all of its auxiliaries. Whether the
  compiler schedules an auxiliary with its block (the auxiliary tail of an inductive block) or as a
  block of its own (a size function, an equation lemma) does not matter to the rule.
- Block `B` **depends on** block `C` when some constant of `B` references some constant of `C`, directly
  or through other blocks. Dependency is between blocks; a block depends on all of a block or none of
  it.

**The rule.** Everything about how a block compiles (each byte of its output, its records, and whether
it is refused) is a function of:

1. the block itself;
2. the rest of its own logical unit;
3. every block it depends on, each with its whole logical unit.

Nothing else may be read. In particular:

- not a block that depends on it (a **caller**), nor whether any caller exists;
- not a constant outside 1–3, nor any table over the whole environment (which names exist, which names
  share an address, what some other block claimed);
- not the schedule: what has been compiled so far, in what order, by how many workers.

**Callers adapt.** A block is compiled after its dependencies and sees how they were compiled: their
addresses and their records (a block was permuted, split or collapsed; its Lean auxiliaries denote
images; a clique was transported with a given permutation). When a dependency's compiled form is not
what Lean's term expects, the dependent block changes its own term. The dependency is never changed for
the sake of a dependent. If a dependent cannot be made to fit, that is reported against the dependent.

**Two graphs, kept apart.** The rule is about *visibility*. Scheduling is finer.

- The scheduling graph is over blocks, and it must be acyclic. Its edges are Lean's references plus
  every reference a pass's *output* has that Lean's term did not.
- Logical units are not scheduling nodes, because units can be mutually visible while their blocks are
  not mutually dependent. Measured on Lean 4.34.1: `Nat.below` mentions `PProd`, and `PProd._sizeOf_1`
  mentions `Nat`. Each unit has an auxiliary that uses the other's block, and the block graph is still
  acyclic.
- Reading the Lean *source* of a visible constant needs no edge. Using its *compiled form* (its
  address, its records) does: it must have been compiled first.

**Memo tables are not reads.** A table the driver carries from one block to later ones is allowed when
its entries are values of a function of a unit and the unit's compiled dependencies, every block that
reads an entry would compute the same value, and an entry is entered only under a condition that makes
that so. Pass 3 has two (`CompileEnv.p3Views`, `CompileEnv.p3ImageExps`): a changed block's view, entered
only when built with every member of the block compiled, and the image blocks' rewritten expansions of
its heads, entered only from image blocks whose views all were. Which block filled an entry changes no
byte, only the time. With the plan table (§5.4) that makes three; all three share the check mode
`IX_PASS3_CHECK_PLANS=1`, which recomputes every entry a table supplies and fails the compile on a
difference (`BlockView.same`, `Expansion.same`, `CliqueOutcome.same`): a view taken from the table is built
again, a recursor's expansion taken from the table is looked up again, and an image block starts its
rewrite without the expansion table and compares every expansion it computes with the table's entry.

**Obligations of a pass whose output adds a reference.** All four, argued in the pass's docstring:

1. the target is visible by the rule (the pass's own unit, or the unit of a block it depends on);
2. the reference is declared, so that the scheduler has the edge and every closure producer
   (`collectDeps`, `--consts`, `--local`) carries the target;
3. the graph with the new edge is still acyclic (the scheduler fails closed on a cycle, so a wrong
   argument shows as a refusal, never as a wrong output);
4. if the target is absent from the input, the pass declines with a recorded cause; it never silently
   takes another form.

**On-demand auxiliaries.** They are ordinary members of the unit. Whether Lean generated one was
decided at elaboration time, so by the time the compiler runs it is a fixed part of the input; reading
it breaks neither the DAG nor parallel compilation (owner, 2026-10-05). A block may therefore read
whichever of its unit's on-demand auxiliaries exist, and may take a different form when one exists
than when it does not. Two things follow, and both are accepted:
- the address of a block can differ between two environments that differ only in whether some later
  declaration made Lean generate one of its on-demand auxiliaries;
- a closure producer must carry a block's on-demand auxiliaries with it, like its eager ones.

What stays forbidden is reading a dependent that is *not* an auxiliary of the unit.

**Allowed, with the reason.**

| Case | Why it is inside the rule |
|---|---|
| `brecOn` refers to `below`; a recursor image refers to the Ix recursor | auxiliaries of one unit |
| O11a: the size function of a split member refers to `T._sizeOf_inst`, the size instance of a lower component of the same declaration | an auxiliary referring to another auxiliary of the same Lean declaration; the edge is declared, acyclic, and the instance is carried by closures |
| A definition over a changed inductive block has its `rec`, `casesOn`, `below`, `brecOn` call sites rewritten (images, O1–O6) | a block reading the auxiliaries of a block it depends on |
| An equation lemma of a transported clique is regenerated over the canonical clique | the lemma is compiled after the clique and reads the clique's record |
| A clique reads its own equation and unfolding lemmas when planning its transport, and stays in Lean's form if one of them cannot be carried (`Pass/Cliques.lean`: `memberEqLemmas` and `scheduleCliques` find them by name; `planClique` carries them, and keeps the members of an O17 class that owns one apart) | on-demand auxiliaries of the clique's own unit |
| A block that references a member and one of Lean's encoding constants of a clique it depends on is refused by name when that clique is transported (`Pass/Cliques.lean`, `cliqueCallers`) | a block reading the record of a block it depends on; the dependency is not changed |
| O7, O8, O10, O12 (§1.6): the canonical form `c._ix` of a definition `c` over a collapsed block refers to the Ix recursor, `casesOn`, `recOn` or `brecOn`/`below` of the class (`Opt/O7.lean`, `O8.lean`, `O10.lean`, `O12.lean`) | a block reading the auxiliaries of a block it depends on (as the images, O1–O6); the decision reads the occurrence, the block's Pass 1 record and the images only |
| O9 (§1.6): `c._ix` refers to the Ix `brecOn`/`below` of the component and to the re-typed handler `c._ix_retyped._f`, emitted with `c` (`Opt/O9.lean`) | the Ix auxiliaries of a dependency; the handler is a member of `c`'s own unit (generated from `c`'s own `_f`) |
| O11b (§1.6): `T.noConfusionType._ix`, `T.noConfusion._ix` in enumeration form, the latter typed over the former (`Opt/O11b.lean`, `Driver.unitPasses`) | auxiliaries of one unit (`T`'s `noConfusion` family); decided from `T` and its Pass 1 classes |
| O10/O12 (D1) compare re-typed handlers through the canonical forms `d._ix` of the constants they reference (`OptEnv.canonAddrOf`, `Driver.ixFormOf`) | reads the compiled form of a dependency (`d` is referenced, so its block, which emits `d._ix`, compiled first); never a caller |

**Not allowed.** No entry of this table exists in the code; the rows marked "Removed" record what was taken out and by which milestone.

| Case | Why it breaks the rule |
|---|---|
| Removed (M1-a): a clique was demoted because some later declaration that is not an equation lemma depended on it (`scheduleCliques`: `blocking`, `reason`, at `340f67b2`). Such a declaration is now refused by name instead (above) | read a caller |
| Removed (M1-b): a proof-justified pass declined because a dependent mentioned both the definition and a recursor-family auxiliary (the dependents rule of branch `jcb/ix-cc-a6p`, `Opt/Packed.lean`). The Lean name now keeps the faithful form and the canonical form is stored under `c._ix` (D1), so no pass reads a dependent | read a caller |
| Choosing among names that share an address by hash-map order (D4) | reads a whole-environment table |
| A form that depends on whether another block has been compiled yet | reads the schedule |

**Why the rule.** The fold stays a fold over a DAG, so blocks compile in parallel. A constant's address
is a function of its own closure, which is what content addressing means. A closure compile agrees with
a whole compile. Certification can state one obligation per block.

**How it is checked.**

- Schedule identity (§6.1): byte-equal output across every driver and worker count, switch off and on.
- Closure against whole: every constant of a closure compile has the address the whole compile gives it.
- Whole units in every closure producer (M1-d, M1-h, M6R slice 5): the selected closures of the input
  (`Ix.EnvScope.collectSelectedDeps`, `withUnits`) carry the unit of every declaration they reach, and the
  Rust compiler's output on such a closure is the Lean compiler's, byte for byte (`compile-closure-whole`,
  `compiler-selected-closure-e2e`); `ix pack` completes the units of a compiled environment read from its names
  and metadata (`Ix.Cli.PackCmd.packWholeUnits` over `ixonUnitView`), Pass 3's reserved names (`_ix`, `_ix_*`)
  belonging to the declaration they hang under (§11.2 case 4), and the Rust completion (`ix pack --rust-units`,
  `ixon::unit`) gives the same bundle byte for byte (`pack-units`, `pass3-rust-parity` step 5).
- **Caller independence** (to add): compile an environment, then the same environment with extra
  dependents and extra unrelated constants appended; every constant of the first must keep its bytes and
  its records. The appended dependents must not be auxiliaries of an existing unit: making Lean
  generate an on-demand auxiliary changes that unit, and the unit may then compile differently.

---

## 7. What is canonical and what is only faithful; the non-canonical set

§11 states the same classes as the output contract: what each Lean name denotes in the default mode
(§11.2), the records the output carries, including the compile-time decline map and the changed-set record
(§11.3, §11.5), and the identity requirements (§11.4).

### 7.1 The table (Phase A §3.4.5, made precise)

"Canonical" means invariant, in bytes, under the presentations of Def 4.3:
- for blocks: member reorder; separate declaration of components with the block's universes,
  parameters and sort; collapse;
- for cliques: permutation, regrouping, renaming, equal members.

| Source constant | Compiled by | Canonical? | Non-canonical cause if not |

|---|---|---|---|
| Ix blocks and every Ix auxiliary | P1, P2 | **yes** [argued; leg 5 of §3.6] | — |
| Anything over an unchanged block or clique | identity translation | **yes** | — |
| `rec`/`recOn`/`casesOn`/`below`/`brecOn` users over a permuted block | O1–O6 | **yes** [measured, ORA DQReord 53/53] | — |
| The same over a split block, including relocated calls | O2, O3 | **yes** [argued; PRO B1/B2 `rfl` for `rec` and `casesOn` users] | — |
| Structural recursion over a split block with a cross field | O9 | the `_ix` form: **yes** once the reference tables are derived from the final term (§4.7 (e)) [argued] | the Lean name: `PJ-FORM-O9` (D1, §1.6) |
| `noConfusion` in enumeration form; mutual `_sizeOf` over a split block | O11b; O11a | O11b: the `_ix` forms **yes**, the Lean names `PJ-FORM-O11b` (D1); O11a: **yes** | O11a: run since A6f with its scheduling edges (§1.5); where it declines, the decline is recorded (`O11A-PENDING`, `CompileEnv.p3NonCanonical`, §11.3) |
| `rec` users of a collapsed block that do not distinguish members | O7 | the `_ix` form: **yes** | the Lean name: `PJ-FORM-O7` (D1) |
| `casesOn` and matchers over a collapsed or lifted member | O8 | the `_ix` form: **yes** | the Lean name: `PJ-FORM-O8` (D1); its callers that no pass rewrote: `INHERITED` |
| Two functions over a collapsed pair, equal arms | O10 | the `_ix` form: **yes** (the twin's single function) | the Lean names: `PJ-FORM-O10` (D1); a transported clique: `PENDING-COLLAPSE` (§1.6.2) |
| Two functions over a collapsed pair, different arms | O12 | the shared helper `fg` and the `_ix` forms only | `COLLAPSE-ARMS` (the Lean names `A.f`, `B.g`; `PJ-FORM-O12` against the permuted presentation, D1) |
| A changed structural clique | O13, O14 | **yes** | `RECARG` (an ambiguous recursive argument) |
| A changed well-founded clique | O15 + §5.1 | functional: **yes**. Proofs: yes when transported | `GUESSLEX`, `TACTIC-ASYM`, `SHAPE` |
| A changed `partial_fixpoint` clique | O16 + §5.2 (O16's lemma [proved], §5.2) | as above | `TACTIC-ASYM`, `SHAPE` |

| Clique members in one class | O17 | **yes** | — |
| Theorems proved by mutual recursion | §5.4 | statement **yes**; proof when transported | `NOSPEC`, `TACTIC-ASYM`, `SHAPE` |
| Statements following the order (`mutual_induct`, `induct`, `_mutual.eq_unfold`) | baseline | faithful only | `ORDER-STMT` |
| Bare or partial auxiliary occurrences (`def r := @A.rec`, `@f._mutual`) | residual image | faithful only: the type is Lean's | `BARE` |
| Lean `IndPredBelow` families of a changed Prop block | own block (§4.6) | faithful only | `INDPRED-BELOW` |
| Lazily realised equation lemmas (`eq_N`, `eq_def`, `eq_unfold`) | baseline, or carried with the clique | existence varies with the build (A Δ13) | excluded from the claim; `LAZY` if listed |
| A split member against the member declared alone with fewer universes, parameters or a smaller sort | — | not a presentation under Def 4.3 | not recorded |
| Theorem proofs in general | any | not promised (M7) | not recorded unless the theorem is in a clique fixture |

### 7.2 The non-canonical set (tracked fixture)

**Location.** The fixture is tracked at `Tests/Ix/Compile/NonCanonical.lean`, as Lean data, because

tooling is in Lean. The twins gate (Phase A §5.2) reads it.

**Format.**

```lean
inductive NonCanonicalCause where
  | tacticAsym | shape | guessLex | recArg | orderStmt | bare | collapseArms
  | indPredBelow | noSpec | lazy | o11aPending
  -- differences that a later package removes (A1G's extension):
  | pendingTransport | pendingSplitAux | pendingNoConfusion | pendingSurgery | pendingCollapse
  -- a difference inherited from a non-canonical dependency:
  | inherited

  deriving Repr, BEq

structure NonCanonicalEvidence where
  addrA       : String          -- hex address under presentation A
  addrB       : String          -- hex address under presentation B
  firstDiff   : String          -- path to the first differing node of the decoded terms, e.g. "value.app.arg.3.proj"
  kernelsA    : Bool × Bool × Bool  -- accepted by Ix.Tc, the Rust kernel, the certified checker
  kernelsB    : Bool × Bool × Bool
  note        : String          -- one line; for TACTIC-ASYM the tactic or lemma responsible

structure NonCanonicalEntry where
  fixture     : Lean.Name       -- the fixture module, e.g. `Tests.Ix.Compile.Fixtures.WFPair`
  presA       : String          -- presentation id, e.g. "orig"
  presB       : String          -- e.g. "perm[1,0]", "regroup:where", "rename"
  constant    : Lean.Name       -- the constant's name in presentation A
  canonical   : String          -- its canonical position (block or clique, class, role)
  cause       : NonCanonicalCause
  evidence    : NonCanonicalEvidence

def nonCanonical : List NonCanonicalEntry := [ ... ]
```

**Gate semantics.** The fixture is **exact** in both directions:
- every byte difference between twins must match an entry by `(fixture, presA, presB, constant)`;
- every entry must still match a difference;
- a stale entry fails the gate.

Entries change only in a commit that states the cause.

**Markers.** Besides the causes of §5.5 and §7.1, the fixture uses two kinds of marker
[A1G §3].
- **`pending*`** marks a difference that a later package removes:
  - `pendingTransport`: A5, O13–O16;
  - `pendingSplitAux`: §4.7 (b);
  - `pendingNoConfusion`: §4.7 (c) and O11b;
  - `pendingSurgery`: O2/O9 and the surgery defects of §4.7 (e)/(f), in A3/A6;
  - `pendingCollapse`: O7–O12, in A6.

  When that package lands, its entries must disappear; the exactness rule above enforces this.
- **`inherited`** marks a constant whose Lean terms are equal under the name map, but which
  references a constant that is itself in the set. It disappears when its dependency does.
- **`pjForm <pass>`** (`PJ-FORM-<pass>`, decision 5, D1) marks the Lean name of a constant that a
  proof-justified pass (O7–O12) rewrote: the Lean name keeps the faithful form, the canonical form
  is `c._ix` and is what the twins compare. It is permanent, not a pending marker (switch-on
  fixtures, `nonCanonicalPasses`).

**Policy.** Recording is the Phase A policy (Q-A5), following the principle of §0.1. A
`TACTIC-ASYM` or `SHAPE` entry on library code is reported in the migration's PR text.

### 7.3 Current state (wave 2)

**The twins gate.** Recorded differences:
- 427 measured through the A2 migration [measured, A2M: 0 unrecorded, 0 stale, no evidence drift];
- plus A5F's 70, giving **497** [measured, A5F: 0 unrecorded, 0 stale].

The total has not yet been re-measured on `564d03f0`, where the gate is running [open]. The causes
are those of §5.5/§7.2: the permanent ones and the `pending*`/`inherited` markers. Two features
came in wave 1:
- `TN` moved from `NOSPEC` to `pendingTransport`, since the recovered specification orders it
  (§5.4);
- **`expectedRefusals`** lists the 12 constants that A0 refuses (WB-B4 collapse call sites, F4's
  partial `@A.rec`, C7's IndPred "below" matchers, and their users). The gates require exactly
  these refusals in both directions, and the constants are not canonicity data [measured, A1G2].

**The `pass3` suite (switch on)** keeps its own recorded classes, by defect id. These are switch-on
consequences, not entries of the twins fixture:
- **BB-F7 / BB-F1.** These are meta-mode kernel ingress failures on collapsed blocks. The suite
  accepts them only where the certified checker accepts the same constant (orchestrator, A3).
- **BELOW-ORDER** [historical, A3W §5.3; cause A6f; repaired A5R, no exemption].
  - Pass 1 orders Lean's own `IndPredBelow` block of a collapsed Prop pair `[P.below, Q.below]`.
    The first round decides it on a bound variable, but under the final classes the cross
    references compare, weakly, the other way, in either order.
  - The old executable single-pass gate rejected every `Greater`, weak or not; the certified
    checker accepted the block. Both executable kernels now defer weak `Greater` to full refinement.
  - Cause: the kernels' gate, not Pass 1 (§2.3, "Consequence for the kernels"): user blocks of the
    same shape were rejected with the switch off, from both compilers (`ValidateLeanSwap`). The
    reproducer now passes in both switch states; the suite class and moved-below exemption are removed.
  - No library has such a `below` block.
- **REFUSED-SIBLING** [measured, A3M]. A0 refuses some components in both modes: evaporation in
  C4Evap, F3, NestRoseSplit, NestMutExt and NestMutExtA. Under decision 3 a sibling auxiliary *is*
  its image, so its type mentions the refused member and it cannot compile. This costs 2–11
  constants per unit, listed per unit as consequences.
- **REFUSED-IPB-COLLAPSE** (M1-j, §2.5 "Default path"). The default path refuses Lean's
  `IndPredBelow` block of a collapse that merges alpha-equivalent `.below` members (`IPBCollapse2p1`,
  `IPBMixed`); the switch-on path refuses the same units in Pass 3's images.

Units: 53, with 0 problems; 535 images and 885 rule statements hold by `rfl`, with 0 kernel
failures [measured, A3M].

### 7.4 The flip: Pass 3 by default (M6, 2026-10-06)

**What changed.** Pass 3 is the compiler's default mode (§4.8, "Switch"); `IX_PASS3=off` selects the
legacy surgery, which stays as the comparison mode against the Rust compiler until M6R (owner,
2026-10-06). The flip changes the default only: the two modes compile exactly as before, each
byte-identical to its pre-flip output (Init+Std, switch on: sha256 `a2e22ee7…ba676`; switch off:
the `-a2` references). The owner accepted that the flip moves bytes, with stated causes, on the
condition that no address pinned by the certified checker moves (decision log, 2026-10-04); the
condition is checked on Init+Std (`plans/review2/M6-flip.md`, the pin check).

**What moved, by class** (the switch-on output against the switch-off reference; classes as in the
M1-g measurement, every moved name resolving to an input name, 0 unexplained):

| class | why it moves | Init+Std | Mathlib |
|---|---|---|---|
| image head | a Lean auxiliary name (`rec`, `below`, `brecOn` with `.go`/`.eq`, `recOn`) of a changed inductive block denotes its image (Def 3.4, decision 3), not the surgered Ix auxiliary; `casesOn` heads whose image equals the canonical constant keep their address | 0 | 297 |
| image unit, other | O11a/`sizeOf` of the changed blocks (`_sizeOf_inst`, `sizeOf_spec`, `_sizeOf_N`): their terms reference the faithful images instead of the surgery's canonical calls | 0 | 46 |
| cone of the images | dependents of the changed blocks' `sizeOf` | 0 | 6 |
| transported clique member | members of the transported well-founded cliques (§5, the clique transport) | 12 | 16 |
| carried lemma | the transported String cliques' `eq_def`s, regenerated with the clique | 4 | 4 |
| clique unit, other | Lean's encoding constants of transported theorem cliques (`._mutual`) | 1 | 2 |
| cone of the transported cliques | dependents of moved members (mostly the docstring path through `String.removeNumLeadingSpaces`/`findLeadingSpacesSize`) | 24 | 412 |
| **moved, total** | | **41** | **783** |
| added: `_ix` canonical forms of image heads | Lean's name keeps the image, the canonical constant is stored under `_ix` (D14) | 0 | 329 |
| added: canonical constants of transported cliques | `…._ix._mutual` with its `_proof_N`/`eq_def`, `…._ix._f` | 19 | 27 |
| removed | — | 0 | 0 |

Sources: Init+Std, the M1-g trial (`ixe-diff` against `initstd-a2.ixe`: 41 changed, 19 added, 0
removed); Mathlib, M1-g §3 (783 changed, 356 added, 0 removed; one synthetic block name re-addressed).
The certified checker over the switch-on Mathlib output: 669,942 accept, 4,030 decline, 0 reject; the
68 extra declines are the image heads of the unsafe Aesop block (unsafe definitions, a documented
decline class) and 1 is a re-addressed `_unsafe_rec` block (M1-g §4b). 9 of the 21 Mathlib definition
cliques and 5 of the 7 Init+Std ones are transported; the rest stay in Lean's form with their causes
(M1-g §2). Of Mathlib's 9, the 7 well-founded ones move bytes (their 16 members are the "transported
clique member" row); the 6 members of the 2 structural `Ring` cliques
(`{ExBase,ExSum,ExProd}.{evalIntCast,cast}`, over the changed block `Ring.Common.ExBase`) compile to the
same addresses as under `IX_PASS3=off`, so they are not among the moved names, while their canonical
`…._ix._f` constants are among the 27 added (M1-g §3).

**References.** The switch-on outputs replace the default-path references under new names (`-a3`); the
`-a2` (switch-off) references stay for the gates that run the legacy mode against Rust.
At the flip: `initstd-a3.ixe` 256,128,289 B, sha256 `a2e22ee7…ba676` (certified checker 97,041 accept, 902
decline, 0 reject); `mathlib-a3.ixe` 2,376,572,399 B, sha256 `d0427adf…f6db` (669,942 accept, 4,030 decline,
0 reject, the counts of M1-g; `ixe-diff` against `mathlib-a2.ixe`: 783 changed, 356 added, 0 removed, the
classes above). `IX_PASS3=off` on Init+Std stays byte-identical to Rust and to `initstd-a2.ixe`.

**Images keep Lean's kind (owner, 2026-10-06).** The image of a Lean theorem is stored as a theorem
(`Ix.Compile.Pass.imageInfo`): every `brecOn.eq` and the `brecOn` of a Prop family. The Lean kind is
part of what the name denotes, and the adversarial matrix refuses a forged kind. This moves no Init+Std
byte (Init+Std has no changed inductive block) and no pin; on Mathlib it changes the bytes of the 53
`brecOn.eq` image heads and of their dependents, all in the image class above.

**Records.** Records kept per switch state (`Pass3Kernels`, `validate-lean`'s pins, the corpus harness's
modes, `nonCanonicalOn`, `nonCanonicalPasses`) keep both states: `off` is now `IX_PASS3=off`, the same
compile as the former unset switch. The twins' non-canonical set is kept in two records: the legacy one
(`NonCanonical.nonCanonicalOff`, the 497 differences of the surgery, checked against the twins'
`IX_PASS3=off` compile, read by `clique-transport` and by `validate-lean-nc`'s switch-off runs) and the
default's (`NonCanonicalDefault.nonCanonical`, 959 differences of the Pass 3 compile, each with its cause:
`IMAGE` 493 (the Lean name of an image-kind head, a new cause), `INHERITED` 155, `ORDER-STMT` 86, the
remaining 225 under the §7.1 causes, the legacy `pending*` causes where Pass 3 has not removed the
difference either, by role, or by hand). Suites that compare the Lean compiler with the Rust compiler
(`twins`' Lean/Rust leg, `aux-cert`, `aux-gen-diff`, `compile`, the contract pipeline, the corpus
harness's Rust and parity phases) run the legacy mode explicitly until M6R; `aux-oracle` too (its classes
describe Ix auxiliaries under Lean names; M6R slice 6).

---

## 8. Decisions (owner, 2026-10-03)

These are the first draft's questions with the owner's answers. The text above has been revised to
match.

| # | Question | Decision |
|---|---|---|
| Q1 | Two-key comparator `(k₀, k₁)`, addresses only on full ties | **Not adopted.** Today's first-difference comparator is the Phase A comparator. Format-version flips are accepted as part of a breaking change, and the single key is faster (§2.3, §3.5) |
| Q2 | Name-free seed and representative | **Not adopted.** The name-hash seed and the least-name-hash representative stay. Collapse makes member order irrelevant for anonymous constants, and names belong in metadata (§2.3, §2.8) |
| Q3 | Fix C1 (kind tag) and C2 (cache orientation) in the Lean port | **Yes**, in A2's migration commit, with no byte change. C2 is a latent-bug fix |
| Q4 | `is_rec`/`is_unsafe` in Rust's key | **Content-only key.** Rust drops both keys at catch-up. `isRec` is block-wide [measured, A1C §0.8] |
| Q5 | Sibling deduplication in nested expansion | **Fix**, assigned to A0. Ix gives 4 auxiliaries where Lean has 2, and production rejects the block [measured, A1C item 7] |
| Q6 | Order of theorem cliques without a specification | Statements first, then the recovered specification for ties, otherwise Lean's form, the baseline (§5.4). A complete tie is ordered by the seed, as for blocks (orchestrator, after A5F) |

| Q7 | Well-founded `proof_k` | Re-state the obligation. Use the transported term when recognised, else Lean's term verbatim. Never re-run a tactic (§5.1) |
| Q8 | Pinned choices in M.3 | Compare last (§2.7) |
| Q9 | `partial_fixpoint` monotonicity | Regenerate the path sub-proofs with `solveMonoCall`'s recipe; fall back to `monotone_compose (mono φ) hmono_i` (§5.2). O16's lemma is written once, in A5 |
| Q10 | The development | Hereditary substitution of the image's parameters: β, projection and η at the substituted variables, never ι (§4.3) |
| Q11 | Bare and partial occurrences | Reference the image constant, which serves as the eta adapter (§4.5) |
| Q12 | Old Def 2.5 wording | Replaced by the FIFO-queue definition of §2.5, confirmed against `inductive.cpp:985-1180` [A1C]. `docs/ix_canonicity.md` follows at A8 |

**Phase A §7, updated.**
- **Q-A2 (discovery order): confirmed.**
  - Mathlib's changed blocks fall from 20 to 6 [measured, A1C §0.4–0.5].
  - `canonical_aux_order` (`crates/kernel/src/inductive.rs:1284-1450`), `Ix/Tc/CanonicalCheck.lean`,
    the certified modeller's nested adaptation and `BlockOrder` are re-recorded in the migration.
- **Q-A5 (policy for the non-canonical set): accept and record**, following §0.1. §5 confines the set
  to three kinds:
  - (a) proof internals that the grammar does not recognise;
  - (b) order-dependent choices (`GUESSLEX`, `RECARG`);
  - (c) statements that follow the order.
- **Q-A6 (scope O1–O17): all**, in the order of §1.4. O16's lemma is [proved] (A5F), so
  O16 needs no deferral.
- **Q-A9 (generator totality):** the sibling-deduplication defect (Q5) is added to the list and
  assigned to A0.

---

## 9. The validators

**Validator of record** (Phase A plan, package A3v). For Phase A it is **`ix validate-lean`**,
extended in Lean with five legs:
- the oracle leg for unchanged blocks;
- the image computation rules for changed blocks;
- the provenance rule for images (`Named.original` against Lean's form);
- the decompile round trip, images and inline records included;
- the kernel round trips, with the phase-4 collapsed-block failure (BB-F7) fixed or routed through
  anonymous mode.

It runs on Init+Std at every integration. The Rust `ix validate` (8 phases) is rewritten to the same
phase list in the Rust catch-up PR; until then it runs with the switch off only. In Phase B the
certifier is the validator.

**Phase table with the switch on** [measured, A3W §7.1; A3M]. `ix validate-lean`:

| input | 1 compile | 2 serde | 3 kernel anon | 4 kernel meta | 5 decompile |
|---|---|---|---|---|---|
| Init+Std | PASS | PASS | PASS | PASS | PASS (117,694) |
| SurgSplit, C1Perm | PASS | PASS | PASS | PASS (rewritten constants skipped as altering) | PASS |
| SurgCollapse, F4FlatAlphaUsers, C8Collapse3 | PASS | PASS | PASS | FAIL 4–13 (BB-F7/BB-F1, as with the switch off) | PASS |
| PropCollapse | PASS | PASS | PASS | FAIL 492 (BELOW-ORDER) | PASS |
| `Canonicity`, `Mutual` corpus files | PASS | PASS | PASS | FAIL (BB-F7, plus BELOW-ORDER on PropCollapseA/B) | PASS |

These historical rows predate A5R: BELOW-ORDER is now repaired and has no suite exemption.
The collapsed-block BB-F7 route remains separately documented.

**What A3v must add to phase 4** [A3W §7.1]:
- (i) compare a rewritten constant through its `_ix.inline` record, not skip it;
- (ii) check stored images by their computation rules;
- (iii) treat `_ix` entries as aliases of the Ix auxiliaries;
- (iv) check an image's `Named.original` against Lean's form.

**Whether Rust's `ix validate` holds on Pass 3 output is unmeasured.** It compiles the input itself
through the Rust compiler (`rs_compile_validate_aux`, `crates/ffi/src/lean_env.rs`, with
`CompileOptions::default()`), so it runs in the mode `IX_PASS3` selects: unset, Rust's default, the
legacy surgery until M6R slice 6; `images`, Rust's Pass 3 (M6R slices 1–4, byte-identical to Lean's
default output on Init+Std and Mathlib, §4.8). No run of it under `IX_PASS3=images` is recorded in the
M6R reports. By its phase definitions, on Pass 3 output [argued, not run]:
- phase 3 ("an original's bytes are never stored") would fail on every stored image;
- phases 2 and 6 would see the `_ix` entries as unknown auxiliaries;
- phases 5, 7 and 7b need the inline-record replay.

These are what a Pass 3 `ix validate` must handle.

**`aux-cert`** [measured, CI]:
- It now compiles each fixture's local closure (`ix compile --local`). That takes 19 s at 4-way,
  against 39 min 41 s before, with identical verdicts on all 42 fixtures.
- `AUX_CERT_WHOLE=1` restores the whole-file compiles plus a bridge checking `--local` against them.
  It runs per checkpoint.

**Open:** the `--consts` closure producers omit the recursors of the inductives they carry, so the
certified checker declines those blocks [CI §7]. Not fixed.

## 10. Performance

All measurements were taken on the shared box under load (load 15–80). Read the shares, not the
seconds.

**Profile of the Lean compiler on Mathlib** [measured, CI §3.2]: `IX_PHASE_TIMERS=1`, 32 workers,
25.6 min wall, before the writer port. The flag changes no byte.

| Phase | Share | Notes |
|---|---|---|
| sharing construction | **70%** of block-compile thread time (5,609 of 8,002 thread-s) | 81% on Init+Std |
| `serEnv` (2.36 GB) | **25% of wall** (367 s), single-threaded | |
| eager kernel ingress | 5.2% of thread time (417 s) | 3.6 M constants ingested, of which 0.7% were ever looked up |
| driver merge | 357 s | on the driving thread, so it serialises against the waves |
| source-contract preparation and semantic inspection | 92 s | sequential, before Pass 1 |

Lazy ingress through `Ix.Tc`'s `lazyFault` would remove most of the ingress cost [CI; argued].

**The perf ports** [measured, PERF] (owner: the proof-carrying area search and the proof-neutral
environment writer; no Rust work):
- **Area search.** Ported as is: no statement or audit root changed, and the bytes are identical.
- **Environment writer, bytewise sort.** Landed.
- **`TagN` writer.** Inlined on the host side only, through one `@[csimp]` proved by `rfl`.
  - Inlining in the codec would change two frozen runtime-closure records, because the codec belongs
    to the certified checker's package.
  - So the decode side (`deEnv`) keeps its cost.
- **`BEq ByteArray`.** A `@[csimp]` to core's `ByteArray.beq`.
- **Sharing audit:** 111 roots / 19 csimps before, **113 / 21** after.
- **Effects:**
  - Init+Std `[compile-lean] serialize`: 31.3 s → **9.4 s**.
  - Pure `serEnv` of the decoded reference: about 31–40 s → about **6 s**, bytes identical.
  - On the migrated head, Init+Std `serEnv` takes 9.1 s, the compile 51.8 s, and sharing 80.5% of
    worker thread time [CI §7, light load].
- Mathlib was not re-profiled after the ports [open].

## 11. The output contract

This section states what a compiled artifact means, for the reader that checks it (the certifier,
`docs/compiler-certification.md`; the validators of §9). It replaces the interim contract of the proof
session's handoff. It describes the compiler's **default mode**, Pass 3 (§4.8, §7.4); with `IX_PASS3=off`
(the legacy surgery, kept until the Rust compiler drops it in M6R slice 6) none of §11.2's Pass 3 cases
applies and no changed-set record is written. Every statement cites the code that makes it true at
`jcb/ix-certify-compile` = `36778059` plus this section's commit; where the code is not uniform the
inconsistency is listed in §11.6, not smoothed over.

Vocabulary (§2, §6.3): a *block* is a component of the reference graph after Pass 1; a block is
*changed* when its canonical classes differ from Lean's `all` or a nested auxiliary moved or evaporated
(Def 3.1, `Ix.Compile.Pass.isChanged`); the *logical unit* of a block is the block with all its
auxiliaries. "The independent export of `c`" is Lean's declaration of `c` compiled alone, with every
reference resolved by name in the same artifact.

### 11.1 Names, addresses and kinds

The artifact is an `Ixon.Env`: anonymous constants by address (`consts`) and a name table (`named`:
name ↦ `Named`, §11.3). A Lean constant `c` that compiled is a name of the table; its `Named.addr` is the
address of its Ix constant. Several names can share one address (alpha-equal constants, a collapsed
class); the reverse index names an address by its canonical alias (`insertCanonicalAlias`, earliest in
seed order). A name never denotes two constants: name claims are insert-once (`checkBlockClaims`; a
second claim at another address fails the block).

### 11.2 What the Ix constant under a Lean name denotes, by case

| # | Case (how the compiler decides it) | The Ix constant under `c`'s name | Code |
|---|---|---|---|
| 1 | **Unchanged block, no reference to a changed block's auxiliary, not a clique member.** | Lean's declaration of `c`: its kind, universe parameters, type and value (rules for a recursor), with binder names, binder infos, `mdata` and level spellings moved to the metadata (`ConstantMeta`), member order and nested-auxiliary order of its block canonical (Pass 1, §2.3–§2.5), sharing canonical (`Ix/Sharing`). This is the independent export. | `Driver.prepareBlock` returns the input unchanged when the block references no head; `Cliques.prepareCliques` when no member is in the clique table |
| 1b | **Lean auxiliary of an unchanged inductive block** (`rec`, `rec_N`, `casesOn`, `recOn`, `below*`, `brecOn*` with `.go`/`.eq`). | The constant Pass 2 generates for it (one constant per auxiliary, D6), registered under the Lean name by the block's aux tail; `Named.original` records Lean's own form, compiled by the promotion pass. On Init+Std W accepts these as the independent export (M4-d §6). | `compileMutualAuxTail`; `promoteAuxDriver`, `compileConstNoAuxPure` in the drivers |
| 2 | **Inductive type or constructor of a changed block.** | The canonical Ix inductive or constructor of its class: a projection of the canonical block (Pass 1's classes in canonical order). The members of one collapsed class share one address. | `compileBlockWithAux`, Pass 1 (`Ix/Compile/Canon/**`) |
| 3 | **Image-kind auxiliary of a changed block** (`x.rec`, `x.casesOn`, `x.recOn`, `x.below`, `x.brecOn`, `x.brecOn.go`, `x.brecOn.eq`, and `all₀.rec_j`, `all₀.below_j`, `all₀.brecOn_j` with `.go`/`.eq`, restricted to the names Lean has; the `below`/`brecOn` family only for a recursive block). | Its **image**: for a recursor the generated image (Def 3.4), for the others Lean's own value with every head rewritten (Def 3.5); a λ over Lean's telescope with Lean's universe parameters, computing as Lean's auxiliary (its rules hold by `rfl`, `pass3` suite). **Type:** Lean's type with every head occurrence in it rewritten as in values (`imageDeclWith` rewrites the type with `rw`, the hereditary substitution of case 5), so where Lean's type mentions a head the stored type has that head's image inlined: the `brecOn` family's types mention `below` (`x.brecOn`, `.go`, `.eq`), and their stored types are convertible to Lean's, not equal (W+ accepts them through type rows, `docs/compiler-certification.md` §1.3); a type that mentions no head is Lean's. **Kind (F1):** a theorem if Lean's `c` is a theorem (every `brecOn.eq`, the `brecOn` of a Prop family), otherwise a definition (so the image of a Lean recursor is a definition, `hints := abbrev`, Lean's safety). `Named.original` is Lean's form compiled without any rewrite. Not the independent export. | `Names.imageKinds`; `Driver.editChangedBlock` (records the heads); `Driver.isImageBlock`, `compileImageBlock`, `imageDeclWith`, `imageInfo`; `CompileDriver.runImageBlock` (the originals) |
| 3b | **Lean's other auxiliaries of a changed block** (`noConfusionType`/`noConfusion`, the `sizeOf` family, matchers, `inj`, `ctorIdx`, …, and Lean's `IndPredBelow` inductive family of a Prop block). | Case 5: Lean's declaration with its call sites rewritten (§4.6). Lean's `IndPredBelow` family is an ordinary block of its own (the canonical family moved to `_ix` display names). | `Driver.editChangedBlock`, `editPermutedBelowFamily`; §4.6 |
| 4 | **Canonical constants** (reserved names, D14): a changed block's Pass 2 auxiliaries under display names (`x._ix.rec`, `x._ix.casesOn`, …; nested ones by canonical position `rep₀._ix.rec_i`); the canonical `IndPredBelow` family; a transported clique's `g._ix._mutual` (and `_proof_k`, regenerated `eq_*`), `g._ix.mutual`, `x._ix._f`, `x._ix.match_N`; a proof-justified pass's `c._ix` and its helpers (`p._ix_retyped.s`, O12's helper); O11b's `T.noConfusionType._ix`, `T.noConfusion._ix`. | Ix constants with **no Lean counterpart**. The image terms (case 3) reference Pass 2's recursors by these display names. A canonical constant refers to its dependencies by their Lean names. A reserved name already bound must be bound to the same bytes. | `Names.ixAuxName`, `Driver.moveToDisplay`; `Cliques.planClique`, `prepareCliques`, `canonConst`; `Driver.compileCanon`, `unitPasses`; `CompileDriver.checkBlockClaims` (reserved names insert-once) |
| 5 | **A constant whose block references an image-kind head** (call-site rewrite, Def 3.6). | Lean's declaration with every **full application** of a head inlined from its image (hereditary substitution, no ι) unless a definitional pass (O1–O6, O11a; §1.5) gives the term first; a **bare or partial** occurrence is left as written, the Lean name denoting the image (no `a._ix` constant exists). Definitionally equal to Lean's term with each head replaced by its image; every outermost rewritten occurrence carries an `_ix.inline` record holding the source occurrence. Kind, universe parameters and Lean's statement up to the same rewrite. Not the independent export. | `Driver.prepareBlock`, `Translate.rewriteBlock`/`rw`, `Driver.optLookup`, `Opt/Engine.lean`; recorded in `CompileEnv.p3Rewritten` |
| 5b | **O11a declines** at the recursion of Lean's `sizeOf` family of a split block. | O2's relocated-recursor form (faithful, not canonical), with the cause recorded (§11.3, the decline map). | `Opt.O11a.declineCause?`, `Driver.declineLookup`; `CompileEnv.p3NonCanonical` |
| 6 | **O7–O12 and O11b** (proof-justified passes, decision 5, D1). | The Lean name keeps the faithful form (case 5's baseline); the canonical form is stored under `c._ix` (case 4), cause `PJ-FORM-<pass>`. Callers that reference `c` keep referencing `c` (cause `INHERITED` in the twins' vocabulary): no reference is renamed to `c._ix`. A proof-justified pass fires only in the value of a definition. None fires on Init+Std or Mathlib today (M1-b, M1-g). | `Translate.RwState.site`/`inPlace`/`pjFired`; `Driver.compileCanon`, `unitPasses`, `ixFormOf`; recorded in `CompileEnv.p3PjForms` |
| 7 | **Member of a transported definition clique** (an input clique, `Cliques.inputCliques`: Lean's `all` of two or more safe definitions or theorems, each its own block, referencing an encoding marker; its plan `.transported`: `σ` not the identity, or O17 classes merge). | **Lean's kind, universe parameters and type** (checked, α-equal up to `mdata`) with the transported value `Φ_σ` (§5; WF, `partial_fixpoint`, structural), whose root carries an `_ix.inline` record holding Lean's value. An O17 alias member is the representative's transported constant under its own name. Not the independent export. | `Cliques.planClique` (type check, aliases), `prepareCliques` (`withValue`, the record), `Clique.transport` |
| 7b | **Equation lemma carried with a transported clique** (a member's own `eq_def`/`eq_unfold`/`eq_N` whose block references a member and one of Lean's encoding constants). | A theorem with Lean's statement and a transported proof (the same as case 7). The packed constant's lemmas it reaches are regenerated under canonical names (case 4). A structural clique with a repacked group carries none: it keeps Lean's form (case 7d, `SHAPE`; §5.3, D-M5-1). | `Cliques.scheduleCliques` (the carried set), `memberEqLemmas`, `packedLemmas`, `planClique`; `Clique.transportStructural` (`StructLayout.repacks`) |
| 7c | **Lean's encoding constants of a transported clique** (`all₀._mutual`, `all₀.mutual` with everything under them, `m._f`). | Lean's form under Lean's names (case 1; their statements follow Lean's order: `ORDER-STMT`); Lean's equation lemmas that are not carried refer to them. | `Cliques.isEncodingName`, `encodingOwner?` |
| 7d | **A clique kept in Lean's form**: plan `.baseline` (`NOSPEC`: the order is undetermined; `SHAPE`: the transport left Lean's form), `.unchanged` (`σ` the identity, no alias), `.notEncoded` (one member, an unsafe or partial or kernel mutual block, no encoding recognised). | Case 1 (or 5). Faithful; for `.baseline` non-canonical with the cause. | `Cliques.planClique`; `Clique/Plan.lean` (`CliqueOutcome`) |
| 8 | **A caller refused**: a block outside a transported clique's unit that references a member and one of Lean's encoding constants. | **Nothing**: the block fails with the named error `Pass 3 cliques: caller refused (block rule, callers adapt): …`; the clique is never changed for it. On Init+Std and Mathlib no such caller exists (M1-a, M1-g). | `Cliques.cliqueCallers`, `callerRefusalPrefix` |
| 9 | **A failed block** (any compile error of the block, a conflicting claim, a refused caller, a missing dependency). | **Nothing**: its members are recorded in `CompileEnv.ungrounded` with the message and no name of the block, no constant and no record of it (declines, plans, views, heads) is merged; dependents fail with a missing constant. In the promotion path (case 1b) a failure of the original-form compile marks the members failed although their names were already bound by the inductive's aux tail and are still promoted (the exception, §11.6 item 4). `ix compile-lean` is fail-closed: with any failure it writes no `.ixe` unless `--allow-partial`. | `mergeCompiledBlock` is called only on success (every driver); the `fail` paths of `compileEnvAux`/`compileEnvParallelAux`; `CompileLeanCmd` |
| 10 | **An input name with a reserved component** (`_ix`, or any component starting with `_ix`). | Under Pass 3 the whole compile is refused, the message naming the least such name by pretty form, in both compilers (D14). Scope: the names of the condensation the driver is given (§11.6 item 3). | `Names.reservedInput?`, `CompileDriver.pass3ReservedInput?` |

### 11.3 The records the output carries

**In the artifact.**
- **`Named`** (per name): `addr`; `constMeta` (the metadata of §11.2 case 1: names, binder infos, `mdata`,
  level spellings, the `_ix.inline` records, the `Muts` member lists and aux layout); `original` (an image,
  case 3, and a regenerated auxiliary promoted from its original-form compile, case 1b: Lean's form
  compiled without rewrite, address and metadata); `hints` (exact per-name reducibility hints).
- **`_ix.inline`, `_ix.inline_meta`** (§4.8, "Side-car record"): an `mdata` node in a constant's metadata
  arena wrapping a rewritten occurrence; `_ix.inline` is the index of the source occurrence in the
  constant's `metaSharing`, `_ix.inline_meta` its arena root. On every rewritten constant (case 5) and on
  the root of every transported member and carried lemma (cases 7, 7b: the source is Lean's value).
  Decompile replays them (`decompile-diff` 0 on every unit); the kernels see an ordinary `mdata`.
- **`_ix.clique`**: an `mdata` string on the value of a transported clique's canonical functional(s)
  (`CliquePlan.functionals`), `CliquePlan.record`: `<encoding>; lean order [..]; sigma [..]; order by
  <source>; classes [[..]]; aliases (O17) [..]; causes [..]`.

**Beside the artifact.**
- **The decline map** `CompileEnv.p3NonCanonical` (compile-time, not serialised in the `.ixe`; written to
  the changed-set record): constant ↦ cause, today O11a's declines only. **Rule for a constant with two
  causes: the last wins** — a block's declines are `(member, cause)` pairs in rewrite order, each pair
  once (`Translate.rewriteBlock`), folded into the map by `insert` (`mergeCompiledBlock`), so the cause the
  member's rewrite met last is kept. The Rust compiler mirrors it. No fixture has two.
- **The changed-set record** `<stem>.changed.json` (§11.5).
- **The measured non-canonical records** (tests, not compiler output; §7.2): the default's
  `Tests.Ix.Compile.NonCanonicalDefault.nonCanonical` (959 twin differences, one cause each, exact in
  both directions), using **16 causes**: `IMAGE` 493, `INHERITED` 155, `ORDER-STMT` 86,
  `PENDING-SPLIT-AUX` 55, `O11A-PENDING` 42, `PENDING-COLLAPSE` 30, `LAZY` 24, `INDPRED-BELOW` 21,
  `PENDING-SURGERY` 16, `PENDING-NOCONFUSION` 14, `COLLAPSE-ARMS` 11, `RECARG` 5, `GUESSLEX` 2, `SHAPE` 2,
  `TACTIC-ASYM` 2, `BARE` 1; the legacy `nonCanonicalOff` (497) and the switch-on fixture records
  `nonCanonicalOn`/`nonCanonicalPasses` (where `PJ-FORM-<pass>` appears). The vocabulary is
  `NonCanonicalCause.tag` (19 tags). A measured record holds one cause per (fixture, presentation pair,
  constant), the key its exactness check matches on.

### 11.4 Identity requirements a checker may rely on

1. **The full `ConstantInfo`, kind included.** Every Lean name's Ix constant has Lean's kind, universe
   parameters and type (up to the rewrite of heads in the statement, cases 3 and 5: convertible, not equal, where the type mentions a head), with exactly two kinds of exception,
   both recorded: the image of a Lean recursor is a definition (case 3; a theorem stays a theorem, F1), and
   a name that failed has no constant (cases 8–9). A transported member keeps Lean's `ConstantInfo` except
   its value (`withValue`: hints, safety, `all` are Lean's). A checker may therefore refuse any other kind
   change, and does (the adversarial matrix's kind-forgery row).
2. **Binder ownership by source identity, never by type or position.** The clique transport touches only
   what Lean's encoding introduced: the decoded recursion binder of the root functional and its
   eliminator-threaded copies (WF), the root functional's exact binder (`partial_fixpoint`), `brecOn` at a
   member's root and paths read off owned dictionaries (structural), and recovery reads recursive calls
   only from owned dictionaries (`plans/review2/FIX-pfwf.md`). A user binder, relation or value shaped like
   the encoding keeps its meaning (`clique-ownership`, 43 value-checked cases; `validate-lean` phase 9).
   A checker may rely on: a transported member's value is a function of Lean's encoding of *that*
   clique, and its `_ix.inline` record is Lean's value.
3. **What is canonical, what is faithful only, and why** (§7.1, with the causes of §7.2): canonical are
   the Ix blocks and every Ix auxiliary (cases 2, 4), everything over unchanged blocks (case 1), the
   definitional passes' output (case 5 where O1–O6/O11a fire), a transported clique (case 7, outside
   `GUESSLEX`/`RECARG`/`TACTIC-ASYM`/`SHAPE`/`NOSPEC`), the `_ix` forms of O7–O12/O11b. Faithful only:
   the images under Lean's names (`IMAGE`: Lean's names denote Lean's grouping, by decision 3), the
   baseline where no pass fires, the Lean names of a proof-justified pass's constants (`PJ-FORM-<pass>`)
   and their callers (`INHERITED`), Lean's encoding constants (`ORDER-STMT`), O11a's declines
   (`O11A-PENDING`), cliques kept in Lean's form (`NOSPEC`, `SHAPE`), bare occurrences (`BARE`), Lean's
   `IndPredBelow` family (`INDPRED-BELOW`), lazily realised lemmas (`LAZY`).
4. **Not promised:** theorem proofs in general (M7); a canonical address for a constant whose presentation
   is outside Def 4.3; the address of a block whose unit gains an on-demand auxiliary (§6.3).

### 11.5 The changed-set record

`ix compile-lean` (Pass 3) writes, next to the `.ixe`, `<stem>.changed.json` (`foo.ixe` ↦
`foo.changed.json`; `Ix.Compile.ChangedSet.pathFor`): every name whose Ix constant the compiler made
intentionally other than the independent export, and the faithful non-canonical names it knows about, each
with the compiler's reason. It is a pure function of the final driver state
(`Ix.Compile.ChangedSet.ofCompile`, available to every driver: `compileEnvAux`, `compileEnvParallelAux` and
`compileLeanInput` all return the `CompileEnv`), read from the compiler's own tables, never from a symptom
of the output. No byte of the `.ixe` depends on it. Under `IX_PASS3=off` none is written.

**Format** (`ix-changed-set/1`; JSON, one element per line, every array sorted by name, then name hash,
change, cause, ref):

```
{"format":"ix-changed-set/1",
"mode":"pass3",
"counts":{"image":…,"rewritten":…,"decline":…,"transported":…,"carried":…,"canonical":…,"pj-form":…,"inherited":…,"lean-form":…,"refused":…,"failed":…},
"blocks":[ {"key":…,"all":[{"name":…,"hash":…,"addr":…}…],"heads":[…]} … ],
"cliques":[ {"key":…,"all":[…],"outcome":"transported|baseline|unchanged|not-encoded|unplanned","encoding":…,"cause":…,"why":…,
             "sigma":[…],"carried":[…],"aliases":[[m,rep]…],"record":…,"canonical":[{"name":…,"hash":…,"addr":…,"transports":…}…]} … ],
"entries":[ {"name":…,"hash":…,"change":…,"differs":true|false,"cause":…|null,"addr":…|null,"original":…|null,"ref":…|null,"detail":…} … ]}
```

- `name` is the name's pretty form, `hash` its Ix name hash (the identity: pretty forms can collide);
  `addr`/`original` are hex addresses (`Named.addr`, `Named.original`).
- `blocks`: the changed inductive blocks (`p3Blocks`), Lean's `all` with their Ix addresses, and their
  image-kind heads (`p3Heads`). `cliques`: every input clique of the clique table (`p3Cliques`) with the
  plan its blocks used (`p3CliquePlans`); `record` is the `_ix.clique` string the functionals carry;
  `canonical` the clique's canonical constants that were stored (only those a member or a carried lemma
  reaches).
- `entries`, one claim per (name, change, cause): `change` and its source table, `differs` (the claim that
  the constant is **not** the independent export), `cause` (§7.1/§7.2 vocabulary):

| change | differs | cause | source | `ref` |
|---|---|---|---|---|
| `image` | yes | `IMAGE` | `p3Heads` | block key |
| `rewritten` | yes | — | `p3Rewritten` | — |
| `decline` | yes | `O11A-PENDING` (cause text in `detail`) | `p3NonCanonical` (last cause wins) | — |
| `transported` | yes | the transport's cause for the constant, if any | plan `.transported` | clique key |
| `carried` | yes | as above | `p3Cliques` (carried lemmas) | clique key |
| `canonical` | yes (no Lean declaration) | — | plan `.canon`; the artifact's reserved names | clique key, block key, or the `c` of `c._ix` |
| `pj-form` | no | `PJ-FORM-<pass>` | `p3PjForms` | `c._ix` |
| `inherited` | no | `INHERITED` | Lean constants whose input references a `pj-form` name (computed only when `p3PjForms` is non-empty) | the first such name |
| `lean-form` | no | `NOSPEC`/`SHAPE` (plan `.baseline`), `ORDER-STMT` (Lean's encoding constants of a transported clique) | `p3CliquePlans`, `p3CliqueRoots` | clique key |
| `refused` | — | — | `ungrounded` with `callerRefusalPrefix` | — |
| `failed` | — | — | `ungrounded` | — |

A name failed or refused appears only under that change (no address). A constant the pre-compile
groundedness scan rejects (a reference missing from the input, or to a constant that is itself rejected;
an out-of-scope level or variable; a metavariable) is a failure of the compile with its named refusal
`UNGROUNDED-INPUT: …` (`Ix.GroundError.refusal`, recorded in `CompileEnv.ungrounded` by
`compileDecoratedConsts`; the Rust compiler records the same text, `ground::refusal`), so it is a `failed`
entry and `ix compile-lean` is fail-closed on it. Before 2026-10-07 the Lean compiler dropped such a
constant without a record (only a count); the adversarial matrix's row 11 is the control.

**Sample** (Init+Std, the default compile: the `cliques` row of the transported theorem clique
`bitblast.goCache_decl_eq`/`go_decl_eq` and three of its `entries`; Init+Std's record has 58 entries: 12
`transported`, 4 `carried`, 19 `canonical`, 23 `lean-form`, matching §7.4's measured classes):

```
{"key":"Std.Tactic.BVDecide.BVExpr.bitblast.goCache_decl_eq","all":["Std.Tactic.BVDecide.BVExpr.bitblast.goCache_decl_eq","Std.Tactic.BVDecide.BVExpr.bitblast.go_decl_eq"],"outcome":"transported","encoding":"well-founded","cause":null,"why":"","sigma":[1,0],"carried":[],"aliases":[],"record":"well-founded; lean order #[Std.Tactic.BVDecide.BVExpr.bitblast.goCache_decl_eq, Std.Tactic.BVDecide.BVExpr.bitblast.go_decl_eq]; sigma #[1, 0]; order by statements (WF ownership: leaf recursive binder differs from root telescope); classes #[#[Std.Tactic.BVDecide.BVExpr.bitblast.go_decl_eq], #[Std.Tactic.BVDecide.BVExpr.bitblast.goCache_decl_eq]]; aliases (O17) #[]; causes #[]","canonical":[{"name":"Std.Tactic.BVDecide.BVExpr.bitblast.go_decl_eq._ix._mutual","hash":"93a4abba071de3d85db24018e89f30e037d70818e37c8055760b314c42456d49","addr":"c67e8fbee5fc40a22dc2336754f1e76ba6b4068f531ba6035e83f25a42e76c19","transports":"Std.Tactic.BVDecide.BVExpr.bitblast.goCache_decl_eq._mutual"}]},
{"name":"Std.Tactic.BVDecide.BVExpr.bitblast.goCache_decl_eq._mutual","hash":"a273aaead978cb71f16442c58d197fa66c3ab8d2ede7492125cfb20409e9338c","change":"lean-form","differs":false,"cause":"ORDER-STMT","addr":"f86bda02b570721115105946a0bcc0feae6bf9e36ccefa29687fc8dbe029f203","original":null,"ref":"Std.Tactic.BVDecide.BVExpr.bitblast.goCache_decl_eq","detail":"Lean's encoding constant of a transported clique (Lean's form)"},
{"name":"Std.Tactic.BVDecide.BVExpr.bitblast.go_decl_eq","hash":"c1a416a9d5782fe5c3a8b600cec90bc5b39f79f743a8de140c38266187908262","change":"transported","differs":true,"cause":null,"addr":"c91a6bc085704963b303bbc02361b212e5c5026fc0d7aaa59fab3e65352585e9","original":null,"ref":"Std.Tactic.BVDecide.BVExpr.bitblast.goCache_decl_eq","detail":"well-founded; sigma #[1, 0]"},
{"name":"Std.Tactic.BVDecide.BVExpr.bitblast.go_decl_eq._ix._mutual","hash":"93a4abba071de3d85db24018e89f30e037d70818e37c8055760b314c42456d49","change":"canonical","differs":true,"cause":null,"addr":"c67e8fbee5fc40a22dc2336754f1e76ba6b4068f531ba6035e83f25a42e76c19","original":null,"ref":"Std.Tactic.BVDecide.BVExpr.bitblast.goCache_decl_eq","detail":"canonical constant of the clique, transports Std.Tactic.BVDecide.BVExpr.bitblast.goCache_decl_eq._mutual; carries the `_ix.clique` record"},
```

**What the record is for, what a checker can verify from it and what it trusts.** The record is a
diagnostic side file. The certifier does not read it: W+ (`docs/compiler-certification.md` §1.3)
decides every changed constant directly, by the equation and type rows the certified checker accepts
(a constant passes by `direct`/`raw` or by a W+ route, or is Rejected or Unsupported with its
diagnosis), so listing a name never makes it Certified, and an unlisted changed constant is not
Rejected for being unlisted. (Before W+ the record was planned as a certifier input that would turn
"value differs" on a `differs: true` name into Unsupported(changed); M5 superseded that.) A reader can
verify, from the artifact and Lean's environment alone:
- every `addr` is the `Named.addr` of the name and a constant of the artifact (the `changed-set` suite
  asserts it); `refused`/`failed` names are absent, except a block that failed in the promotion path
  (case 9, §11.6 item 4);
- `image`: the name is in `imageKinds` of Lean's block `ref` (a function of Lean's constants), the
  constant has Lean's type up to the rewrite of heads in it (case 3) and Lean's kind or, for a recursor,
  a definition, and `original` is the export of Lean's declaration;
- `rewritten`, `transported`, `carried`: the metadata carries `_ix.inline` records whose replay
  (decompile) is Lean's term; `transported`/`carried` names are the `all`/`carried` of the clique row,
  which is Lean's `all` and Lean's lemma names; the type is Lean's (for `rewritten`, up to the rewrite
  of heads in it, case 5);
- `canonical`: the name has a reserved component, so no Lean declaration is affected; for a clique, the
  functional's `_ix.clique` string equals the row's `record`;
- completeness against the artifact: every name with an `_ix.inline` record has a `differs` claim, every
  reserved name a `canonical` one (both asserted by the suite).

A reader of the record trusts: that a block is *changed* (Def 3.1, Pass 1's classes) and a clique
*transported* (the plan); that a `differs` claim's value is the intended one (which W+ establishes for
the certifier independently of the record, by rows); the cause texts of declines and plans.
`differs: false` entries are information only.

### 11.6 Inconsistencies found while writing this section, and their resolution (2026-10-07)

1. **O11a's scheduling edges** are added under Pass 3 only by `compileEnvAux` and `compileEnvParallelAux`,
   and in both modes by `compileDecoratedConsts` (`compileLeanInput`, `ix compile-lean`), which then calls
   `compileEnvParallelAux` (adding them again under Pass 3, idempotently); the Rust compiler under Pass 3
   only. **Resolved by the text** (the code is right: edges only order blocks, so no byte depends on where
   they are added, and the schedule-identity gate holds): §1.5, the O11a docstring and
   `prepareSizeOfScheduling`'s docstring say what each driver does.
2. **O11a's decline cause "the constructor and minor type of minor `j` cannot be read"** is the split-minor
   helpers (`sourceCtorForMinor`, `sourceMinorType`, `peelBinders`, shared with the surgery) failing to place
   the minor, measured on split blocks with an evaporated nested auxiliary; the minor itself can be read.
   **Resolved by the text** (§1.5, the O11a docstring): the wording is the code's and stays (it is a record
   text both compilers emit; the decline is faithful, O2's form, and recorded).
3. **D14's naming.** With several reserved names the Lean compiler named the first in
   `CondensedBlocks.blocks`' iteration order, the Rust compiler the least by pretty form, so the two could
   name different constants. **Resolved in the code**: `CompileDriver.pass3ReservedInput?` names the least
   message, so the least name, as `pass3::driver::reserved_input_in` does (control: the `pass3` suite's
   `ReservedIx` unit has three reserved names and checks that both compilers name `ReservedIx.A._ix.g`).
   The scope is unchanged: the check runs over the condensation the driver is given, in `ix compile-lean`
   the grounded one; an ungrounded input name is not D14-checked but is a named failure of the compile
   (`UNGROUNDED-INPUT`, §11.5), so the compile is refused either way.
4. **Failed blocks in the promotion path** (case 9): when the original-form compile of a block whose
   auxiliaries Pass 2 regenerated fails (`compileConstNoAuxPure`, e.g. `REFUSED-IPB-COLLAPSE`), the
   members are recorded as failed, but their names, bound by the block's aux tail, are still promoted
   (`promoteRemaining`; Rust `compile_env`, the same), against case 9's "no name of the block is merged"
   and §11.5's "`refused`/`failed` names are absent". Both compilers behave alike; `ix compile-lean` is
   fail-closed, so no artifact written without `--allow-partial` carries it. **Not changed**: making the
   path publish nothing (skip the promotion when the original-form compile failed, in both compilers)
   moves the outcome of existing fixtures (the IPB refusal fixtures' dependents would fail with a missing
   constant), which re-records `aux-cert` and `validate-lean` pins; that is a decision for the owner of the
   records (FU report, open item). Until then the exception is the contract: case 9 and §11.5 name it.
5. Stale docstrings fixed with this section (no code change): `ImageView` (the image terms reference
   Pass 2's recursors by their `_ix` display names, not by Lean's names), `Translate`/`Driver`/`Names` (no
   `a._ix` image constant exists for bare or partial occurrences), the decline map's docstring (the last
   cause wins; all O11a declines, not only absent instances).

---

## Appendix: what is still not established

**Settled since the first draft** by A1C's measurements:
- `isRec` is block-wide;
- Lean registers every `J As` when deduplicating siblings;
- the discovery-order definition matches Lean's `rec_N` on 98 of 98 nested blocks;
- `canonUniv` levels move 0 orders;
- the seed sweep found 0 differences, and the preorder check 0 violations;
- Mathlib has 20 changed blocks today and 6 under discovery order.

**Still open:**
- **Lean source version.** The elaborator sources (`src/lean/Lean/...`) were read at 4.34.0; the
  4.34.1 line numbers of those citations are [open]. The C++ kernel citations are at 4.34.1 (A1C).
- **The grammar's coverage** beyond the fixtures. On them it is exact, 147/147 (§5.8), now including
  reflexive and nested structural recursion, lattice fixpoints and user monotonicity proofs. Library
  cliques are not yet measured [open].

- **Leaks of provisional addresses into output** (D5) [open].
- **O11a's `rfl`** on `Linear.EqCnstr` [open].
- **O16's lemma**: [proved], A5F (`FixPerm.lean`). The `import all Init.Internal.Order.Basic` it
  requires is to be noted in Phase B's audit.

- **Cause (e) of §4.7** has not been re-measured at v4 [open].
- **Wave 2** (§0.2, §4.8, §6, §7.3, §9, §10):
  - the twins total (497) and Pass 3 with the switch on, on Mathlib, have not been re-measured on
    `564d03f0` [open];
  - BELOW-ORDER was the kernels' single-pass canonicity gate rejecting a weak `Greater` (A6f);
    repaired in both executable kernels by A5R, with full-refinement and negative regression tests;
  - BB-F7/BB-F1, the meta-mode ingress of collapsed blocks, is with A3v [open];
  - REFUSED-SIBLING follows A0's evaporation refusal and lasts as long as that refusal does;
  - [superseded] neither the clique transport nor the optimisation passes were wired into the compiler
    (both are, under Pass 3, the default since the flip, §7.4);
  - [superseded] Rust stays on surgery: it implements Pass 3 slice by slice (M6R) and keeps the surgery as
    its default until slice 6 (§4.8, "The surgery is the legacy mode");
  - C6 remains in Rust until the catch-up PR;
  - A7's items D2a–D16 are open, and D2a may move side-car bytes;
  - the `exprCompileDepth` fix has not been rerun on Mathlib;
  - the `--consts` closure producers omit recursors;
  - Mathlib has not been re-profiled after the perf ports.
- **Remaining transport gaps** (§5.8):

  - kernel evidence for A5F's 70 new entries;
  - the composition fallback on a lattice clique with a user proof;
  - recovery of the inductive-predicate route, without which IP stays `NOSPEC`.
