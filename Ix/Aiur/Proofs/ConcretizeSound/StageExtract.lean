module
public import Ix.Aiur.Proofs.ConcretizeSound
public import Ix.Aiur.Proofs.ConcretizeSound.RefsDt

/-!
Concretize stage extraction + sub-lemmas for `concretize_preserves_runFunction`
+ PLAN_3B Phase A.1 (source↔typed ctor kind correspondence). Extracted from
`ConcretizeSound.lean` 2026-04-29.
-/

public section

namespace Aiur

open Source

/-! ### Phase 3 — `typFlatSize` preservation across concretize (main theorem). -/

-- `Typ.typFlatSize_across_concretize` DELETED: FALSE as stated. `rewriteTyp`
-- maps `.app g args → .ref concName` when mono has an entry, but
-- `typFlatSize decls {} (.ref concName) ≠ typFlatSize decls {} (.app g args)
-- = typFlatSize decls {} (.ref g)` in general (concName looks up a different
-- datatype in decls, if it's even a key). Needs either a two-decls
-- formulation (RHS evaluated in `monoDecls` where concName resolves) or a
-- restrictive hypothesis ("top-level input types are `.app`-free"). Orphan
-- at deletion time — no caller. Reintroduce with a correct signature when a
-- concrete consumer needs it.

/-! ## Concretize stage extraction

These lemmas expose internals of `Typed.Decls.concretize`'s do-block so
downstream proofs (`CompilerPreservation.concretize_keys_of_mono`) can access
specific stage outputs. Sorried until `concretize`'s imperative body is
refactored into extractable form. -/

/-- Step 4 of `Typed.Decls.concretize` is key-preserving: any insert-only step
function `lower` that inserts under `.fst` gives `monoDecls`-keys ↔ `concDecls`-keys. -/
theorem concretize_step_4_keys_of_fold
    {monoDecls : Typed.Decls} {concDecls : Concrete.Decls}
    (lower : Concrete.Decls → Global × Typed.Declaration →
             Except ConcretizeError Concrete.Decls)
    (hlower_insert : ∀ acc x r, lower acc x = .ok r →
      ∀ g, r.containsKey g ↔ acc.containsKey g ∨ (x.fst == g) = true)
    (hfold : monoDecls.foldlM (init := default) lower = .ok concDecls) :
    ∀ g, monoDecls.containsKey g ↔ concDecls.containsKey g := by
  intro g
  rw [IndexMap.containsKey_iff_exists_pair monoDecls g,
      ← IndexMap.indexMap_foldlM_insertKey_default_iff monoDecls lower hlower_insert g
        concDecls hfold]

/-- `step4Lower` is insert-only in its input's `.fst`. -/
theorem step4Lower_inserts :
    ∀ acc x r, step4Lower acc x = .ok r →
      ∀ g, r.containsKey g ↔ acc.containsKey g ∨ (x.fst == g) = true := by
  intro acc x r hstep g
  obtain ⟨name, d⟩ := x
  unfold step4Lower at hstep
  simp only at hstep
  cases d with
  | function f =>
    simp only [bind, Except.bind, pure, Except.pure] at hstep
    split at hstep
    · contradiction
    split at hstep
    · contradiction
    split at hstep
    · contradiction
    simp only [Except.ok.injEq] at hstep
    subst hstep
    exact IndexMap.containsKey_insert_iff_or acc name g _
  | dataType dt =>
    simp only [bind, Except.bind, pure, Except.pure] at hstep
    split at hstep
    · contradiction
    simp only [Except.ok.injEq] at hstep
    subst hstep
    exact IndexMap.containsKey_insert_iff_or acc name g _
  | constructor dt c =>
    simp only [bind, Except.bind, pure, Except.pure] at hstep
    split at hstep
    · contradiction
    split at hstep
    · contradiction
    simp only [Except.ok.injEq] at hstep
    subst hstep
    exact IndexMap.containsKey_insert_iff_or acc name g _

/-- Existence of the `monoDecls` witness for `step4Lower`'s fold. Closed by
unfolding `Typed.Decls.concretize` — its final action is
`monoDecls.foldlM (init := default) step4Lower` for `monoDecls = concretizeBuild …`. -/
theorem step4_monoDecls_exists
    {typedDecls : Typed.Decls} {concDecls : Concrete.Decls}
    (hconc : typedDecls.concretize = .ok concDecls) :
    ∃ (monoDecls : Typed.Decls),
      monoDecls.foldlM (init := default) step4Lower = .ok concDecls := by
  unfold Typed.Decls.concretize at hconc
  simp only [bind, Except.bind] at hconc
  split at hconc
  · contradiction
  · rename_i drained hdrain
    exact ⟨concretizeBuild typedDecls drained.mono drained.newFunctions drained.newDataTypes,
           hconc⟩

/-- Step 4 `foldlM` extraction: composed from `step4_monoDecls_exists` +
`step4Lower_inserts`. -/
theorem concretize_step_4_extract
    {typedDecls : Typed.Decls} {concDecls : Concrete.Decls}
    (_hconc : typedDecls.concretize = .ok concDecls) :
    ∃ (monoDecls : Typed.Decls)
      (lower : Concrete.Decls → Global × Typed.Declaration →
               Except ConcretizeError Concrete.Decls),
      (∀ acc x r, lower acc x = .ok r →
        ∀ g, r.containsKey g ↔ acc.containsKey g ∨ (x.fst == g) = true) ∧
      monoDecls.foldlM (init := default) lower = .ok concDecls := by
  obtain ⟨monoDecls, hfold⟩ := step4_monoDecls_exists _hconc
  exact ⟨monoDecls, step4Lower, step4Lower_inserts, hfold⟩

/-! ### Sub-lemmas for `concretize_preserves_runFunction`

The concretize preservation theorem decomposes into (A) `Typ.instantiate` /
`substInTypedTerm` are value-level identity, (B) `rewriteTypedTerm` preserves
`Source.Eval` denotation
modulo funcIdx remap, (C) 40-arm structural induction on `Typed.Term`.

These stubs name the pieces so future work can attack them individually. -/

/-! **Placeholder obligations (A) and (B)**: value-level denotation is
preserved by `substInTypedTerm` / `rewriteTypedTerm` respectively. Both
operate on `Typed.Term` while `Source.Eval.interp` operates on `Source.Term`,
so the precise statements require either (a) a `Typed.interp` evaluator
mirroring `Source.Eval.interp` and a compilation bridge, or (b) a
`decls`-modification construct (`decls[name.body := rewrite name.body]`)
that threads the rewrite through the source evaluator.

Both route to the heart theorem `concretize_preserves_runFunction`
(below). Stating them precisely is itself concretize-preservation groundwork
— see the `concretize_preserves_runFunction` per-arm plan for the proper
framing (37-arm induction quotients out the rename). **These stubs are
intentionally *not* stated as theorems**: expressing them requires
infrastructure that isn't in place. They live here only as documentation
anchors for future `BLOCKED ON:` references. -/

/-- Bridge: `funcIdx` maps source globals and their concretized images to the
same slot. Required so `flattenValue` of `.fn g` and `.fn (concretizeName g args)`
agree. Discharged by the top-level caller via `ct.nameMap` composition with the mono-map. -/
@[expose]
def FuncIdxRespectsConcretize
    (mono : Std.HashMap (Global × Array Typ) Global)
    (funcIdx : Global → Option Nat) : Prop :=
  ∀ (g : Global) (args : Array Typ) (g' : Global),
    mono[(g, args)]? = some g' → funcIdx g = funcIdx g'

/-- Bridge: `decls : Source.Decls` and `typedDecls : Typed.Decls` share
declaration skeleton — every source name resolves in both. Typically
discharged from `checkAndSimplify = .ok typedDecls`. -/
@[expose]
def SourceTypedCompatible
    (decls : Source.Decls) (typedDecls : Typed.Decls) : Prop :=
  ∀ name, decls.getByKey name = none ↔ typedDecls.getByKey name = none

-- `ValueRelByConcretize` + `flattenValue_of_ValueRel` DELETED: speculative
-- infrastructure for a possible future upgraded signature of
-- `concretize_preserves_runFunction`. Current signature uses
-- `Concrete.flattenValue concDecls` on the RHS and bridges to source
-- `flattenValue decls` via `flatten_agree_under_fullymono` for composition
-- with the bytecode chain.

/-- Bridge: under `FullyMonomorphic t` (which forces every datatype/function
parameter list to be empty, hence `concretizeName g #[] = g` for all globals),
source-decls `flattenValue` and concrete-decls `Concrete.flattenValue` agree
pointwise on every value. Required to compose
`concretize_preserves_runFunction`'s new RHS form
(`Concrete.flattenValue concDecls`) back into the bytecode chain (which uses
`flattenValue decls` everywhere through `InterpResultEq`).

Proof obligation: under FullyMono + `mkDecls = .ok decls` +
`checkAndSimplify = .ok typedDecls` + `concretize = .ok concDecls`:
- For every ctor name `g`, `decls.getByKey g = some (.constructor dt₁ ctor₁)`
  iff `concDecls.getByKey g = some (.constructor dt₂ ctor₂)` with corresponding
  `dt`/`ctor` shapes (the `nameHead` agreement and ctor-arg-list shape).
- `dataTypeFlatSize` agrees on the corresponding `dt`s (constructors' arg-types
  rewrite to concretized variants but preserve flat size under FullyMono since
  args are empty).

Discharged via the per-decl reflection lemmas in CheckSound + the
`concretizeName g #[] = g` lemma (`concretizeName_empty_args`) under
FullyMono. -/
-- Pointwise flatMap helper. -/
theorem flatten_attach_flatMap_eq_pw {vs : Array Value}
    {g₁ g₂ : Value → Array G}
    (h : ∀ v ∈ vs, g₁ v = g₂ v) :
    vs.attach.flatMap (fun ⟨v, _⟩ => g₁ v) =
    vs.attach.flatMap (fun ⟨v, _⟩ => g₂ v) := by
  congr 1
  funext ⟨v, hv⟩
  exact h v hv

/-! ### PLAN_3B Phase A.1 — source↔typed ctor kind correspondence (forward).

Given source `(.constructor dt c)` at key g, typed `(.constructor _ _)` at the
same key g. Derived from `FnMatchP_checkAndSimplify` (typed→source) by case-
analysis on what `tds.getByKey g` could be: rule out `none`/`.function`/
`.dataType` via key-set preservation + FnMatchP backward direction. -/
theorem checkAndSimplify_preserves_ctor_kind_fwd
    {t : Source.Toplevel} {decls : Source.Decls} {typedDecls : Typed.Decls}
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok typedDecls)
    {g : Global} {dt : DataType} {c : Constructor}
    (hsrc : decls.getByKey g = some (.constructor dt c)) :
    ∃ td_dt td_c, typedDecls.getByKey g = some (.constructor td_dt td_c) := by
  have hkeys := checkAndSimplify_keys_local hdecls hts g
  have hsrc_ne : decls.getByKey g ≠ none := by rw [hsrc]; simp
  have htd_ne : typedDecls.getByKey g ≠ none := hkeys.mp hsrc_ne
  have hP := FnMatchP_checkAndSimplify hdecls hts
  match htd : typedDecls.getByKey g with
  | none => exact absurd htd htd_ne
  | some (.function tf) =>
    exfalso
    obtain ⟨_, hfsrc, _⟩ := (hP g).1 tf htd
    rw [hsrc] at hfsrc; cases hfsrc
  | some (.dataType dt') =>
    exfalso
    have := (hP g).2.1 dt' htd
    rw [hsrc] at this; cases this
  | some (.constructor td_dt td_c) =>
    exact ⟨td_dt, td_c, rfl⟩

-- `flatten_agree_under_fullymono` + Phase B/C sub-sorries placed after Phase A.4
-- below (they all need the Phase A.4 lemma which is defined post-`PhaseA2`).

-- MOVED to Scratch.lean 2026-04-30: `concretize_preserves_runFunction`
-- (orphan, FullyMonomorphic-dependent — replaced by entry-restricted variant
-- `concretize_preserves_runFunction_entry` in CompilerPreservation.lean).

-- DELETED 2026-04-28: `Typed.Decls.concretize_preservation` (FullyMono
-- predecessor wrapper of S3, `concretize_preserves_runFunction`). Only caller
-- was the deleted `Toplevel.compile_preservation`; the entry chain
-- (`compile_preservation_entry` → `concretize_preserves_runFunction_entry` →
-- `concretize_runFunction_simulation`) replaces this wrapper.

-- `MvarFreeDecls` + `AllConcretizeReady` DELETED (orphan, only consumed by
-- the deleted `concretize_ok_of_invariants`).

-- `concretize_ok_of_invariants` DELETED: orphan speculative infra. Only used
-- by the equally-orphan `Typed.Decls.concretize_progress` wrapper below
-- (also deleted). Top-level `Toplevel.compile_progress` gets
-- `∃ concDecls, typedDecls.concretize = .ok concDecls` directly from
-- `WellFormed.monoTerminates` — no need for an intermediate wrapper.
-- Reintroduce if a proof for `Typed.Decls.concretize`'s internal invariants
-- is needed (4-phase decomposition: seed / drain / rewrite / lower).


end Aiur

end -- public section
