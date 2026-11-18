import IxVMRefinement.Assembly.NativeAliasOpenTrace
import IxVMRefinement.Assembly.NativeAliasTrace
import IxVMRefinement.Core.Det
import IxVMRefinement.Core.Steps.Whnf

/-! # Two worked alias telescopes

Checked instances of the opened-body telescope walk, in environments that store one definition.

**A relation alias.** `def Rel (α : Type) := α → α → Prop` and a family declared at
`∀ (α : Type), Rel α`, with three binders. The circuit's builder substitutes the argument `α`
with lifting, so its telescope is `∀ (α : Type) (a : α) (b : α), Prop`, whose third domain is the
variable two binders up. `rel_openBinderTrace` shows that the opened-body walk builds exactly
that telescope. The walk on unopened bodies builds a different one, whose third domain is the
second binder (`rel_unopened_trace`), and does not relate the declared type to the circuit's
telescope at all (`rel_unopened_trace_false`).

**A universe-polymorphic alias under level instantiation.** `def Pred.{w} (α : Type w) :=
α → Prop` and a family declared at `∀ (α : Type (max u u)), Pred.{max u u} α`, with two binders.
A recursor that eliminates into every sort renames the family's level parameter `u` from
position `0` to position `1` before the telescope is rebuilt. `foo_openBinderTrace_renamed` is
the walk from the renamed declared type, obtained from the walk of the block run by the
commutation with level instantiation, and `foo_renamed_unique` says that every walk from the
renamed declared type builds the renamed telescope of the block run. The circuit's level
instantiation also simplifies `max u u`, so the heap term it builds has first domain
`Sort (u + 1)` where the renamed telescope has `Sort (max u u + 1)`: the two terms differ and are
equal up to the semantic equality of levels (`fooTele_renamed_lvEq_circuit`), which is the
equality the term seam reads levels up to. -/

set_option linter.unusedVariables false

namespace IxVM.Refinement.Decl.AliasTelescopeExamples

open Ix.Kernel
open IxVM.Refinement.Core
open Ix.Kernel.HeadDeltaBeta (Trace Step DefnLevelsClosed)

/-- The binder datum of a binder whose codomain is never a proposition. -/
abbrev nv : BinderMeta := BinderMeta.leanNever

/-- Level instantiation keeps that datum. -/
theorem nv_instantiate (ks : List LevelParam) (us : List Level) :
    ({ nv with pw := Level.substPW ks us nv.pw } : BinderMeta) = nv := by
  simp [nv, BinderMeta.leanNever, Ix.Kernel.Level.substPW_never]

/-- An environment that stores one definition finds it at its name. -/
theorem find_singleton (n : Key .anon) (lps : List LevelParam) (ty value : KExpr)
    (hint : ReducibilityHint) :
    (⟨[.defnInfo ⟨n, lps, ty⟩ value hint]⟩ : Env .anon).find? n =
      some (.defnInfo ⟨n, lps, ty⟩ value hint) :=
  Env.find?_cons_self (.defnInfo ⟨n, lps, ty⟩ value hint) Env.empty

/-- In an environment that stores one definition, definitions mention only their own level
parameters as soon as that one does. -/
theorem defnLevelsClosed_singleton {n : Key .anon} {lps : List LevelParam} {ty value : KExpr}
    {hint : ReducibilityHint} (hv : value.allLevelParamsDefined lps = true) :
    DefnLevelsClosed (⟨[.defnInfo ⟨n, lps, ty⟩ value hint]⟩ : Env .anon) := by
  intro k cv v h hf
  have hmem : ConstantInfo.defnInfo cv v h ∈
      [ConstantInfo.defnInfo (md := .anon) ⟨n, lps, ty⟩ value hint] := by
    unfold Env.find? at hf
    exact List.mem_of_find?_eq_some hf
  rw [List.mem_singleton] at hmem
  obtain ⟨rfl, rfl, rfl⟩ := ConstantInfo.defnInfo.inj hmem
  exact hv

/-! ## A relation alias: `def Rel (α : Type) := α → α → Prop` -/

/-- `Type`. -/
abbrev type0 : KExpr := .sort (.succ .zero)

/-- The free variable that opens the first binder, `α : Type`. -/
abbrev relVar : KExpr := .fvar 0 type0

/-- `fun (α : Type) => α → α → Prop`. -/
def relValue : KExpr :=
  .lam type0 (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero) nv) nv) nv

/-- An environment that stores `Rel` with that value. -/
def relEnv (Rel : Key .anon) : Env .anon :=
  ⟨[.defnInfo ⟨Rel, [], .forallE type0 type0 nv⟩ relValue .abbrev]⟩

/-- The declared type of the family: `∀ (α : Type), Rel α`. -/
def relFormer (Rel : Key .anon) : KExpr :=
  .forallE type0 (.app (.const Rel []) (.bvar 0)) nv

/-- The circuit's telescope: `∀ (α : Type) (a : α) (b : α), Prop`. The third domain is the
variable two binders up. -/
def relTele : KExpr :=
  .forallE type0 (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero) nv) nv) nv

/-- The term the walk on unopened bodies builds: its third domain is the second binder. -/
def relTeleUnopened : KExpr :=
  .forallE type0 (.forallE (.bvar 0) (.forallE (.bvar 0) (.sort .zero) nv) nv) nv

theorem rel_unfold (Rel : Key .anon) :
    unfoldDefinition (relEnv Rel) (.const Rel []) = some relValue := by
  have hfind := find_singleton Rel [] (.forallE type0 type0 nv) relValue .abbrev
  have h := unfold_const_mkAppN (us := []) [] hfind rfl
  have hv : relValue.instantiateLevelParams [] [] = relValue :=
    Expr.instantiateLevelParams_self [] relValue
  exact (show unfoldDefinition (relEnv Rel) (.const Rel []) =
    some (relValue.instantiateLevelParams [] []) from h).trans (congrArg some hv)

/-- The head trace of `Rel x` at a free variable `x`: one definition, one beta. -/
theorem rel_head_trace (Rel : Key .anon) (x : KExpr) :
    Trace (relEnv Rel) (.app (.const Rel []) x)
      ((Expr.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero) nv) nv : KExpr).instantiate1 x) :=
  .cons (.appFn (.delta (rel_unfold Rel)))
    (.cons (Step.beta (ty := type0)
      (body := .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero) nv) nv) (a := x) (mb := nv))
      .refl)

/-- **The opened-body walk builds the circuit's telescope.** -/
theorem rel_openBinderTrace (Rel : Key .anon) :
    OpenBinderTrace (relEnv Rel) 0 3 (relFormer Rel) relTele := by
  have h3 : OpenBinderTrace (relEnv Rel) 3 0 (.sort .zero) (.sort .zero) := .done
  have h2 : OpenBinderTrace (relEnv Rel) 2 1 (.forallE relVar (.sort .zero) nv)
      (.forallE relVar (.sort .zero) nv) :=
    OpenBinderTrace.step (d := 2) (n := 0) (E := .forallE relVar (.sort .zero) nv)
      (T := relVar) (B := .sort .zero) (R := .sort .zero) (bm := nv) .refl h3
  have h1 : OpenBinderTrace (relEnv Rel) 1 2 (.app (.const Rel []) relVar)
      (.forallE relVar (.forallE relVar (.sort .zero) nv) nv) :=
    OpenBinderTrace.step (d := 1) (n := 1) (E := .app (.const Rel []) relVar) (T := relVar)
      (B := .forallE relVar (.sort .zero) nv) (R := .forallE relVar (.sort .zero) nv)
      (bm := nv) (rel_head_trace Rel relVar) h2
  exact OpenBinderTrace.step (d := 0) (n := 2) (E := relFormer Rel) (T := type0)
    (B := .app (.const Rel []) (.bvar 0))
    (R := .forallE relVar (.forallE relVar (.sort .zero) nv) nv) (bm := nv) .refl h1

/-- The result-sort walk of the family ends in `Prop`. -/
theorem rel_openSortTrace (Rel : Key .anon) :
    OpenSortTrace (relEnv Rel) 0 3 (relFormer Rel) .zero := by
  have h3 : OpenSortTrace (relEnv Rel) 3 0 (.sort .zero) .zero := .done .refl
  have h2 : OpenSortTrace (relEnv Rel) 2 1 (.forallE relVar (.sort .zero) nv) .zero :=
    OpenSortTrace.step (d := 2) (n := 0) (E := .forallE relVar (.sort .zero) nv) (T := relVar)
      (B := .sort .zero) (bm := nv) .refl h3
  have h1 : OpenSortTrace (relEnv Rel) 1 2 (.app (.const Rel []) relVar) .zero :=
    OpenSortTrace.step (d := 1) (n := 1) (E := .app (.const Rel []) relVar) (T := relVar)
      (B := .forallE relVar (.sort .zero) nv) (bm := nv) (rel_head_trace Rel relVar) h2
  exact OpenSortTrace.step (d := 0) (n := 2) (E := relFormer Rel) (T := type0)
    (B := .app (.const Rel []) (.bvar 0)) (bm := nv) .refl h1

/-- The walk on unopened bodies builds the term whose third domain is the second binder. -/
theorem rel_unopened_trace (Rel : Key .anon) :
    BinderTrace (relEnv Rel) 3 (relFormer Rel) relTeleUnopened := by
  have h3 : BinderTrace (relEnv Rel) 0 (.sort .zero) (.sort .zero) := .done .refl
  have h2 : BinderTrace (relEnv Rel) 1 (.forallE (.bvar 0) (.sort .zero) nv)
      (.forallE (.bvar 0) (.sort .zero) nv) :=
    BinderTrace.step (E := .forallE (.bvar 0) (.sort .zero) nv) (T := .bvar 0)
      (B := .sort .zero) (R := .sort .zero) (bm := nv) .refl h3
  have h1 : BinderTrace (relEnv Rel) 2 (.app (.const Rel []) (.bvar 0))
      (.forallE (.bvar 0) (.forallE (.bvar 0) (.sort .zero) nv) nv) :=
    BinderTrace.step (E := .app (.const Rel []) (.bvar 0)) (T := .bvar 0)
      (B := .forallE (.bvar 0) (.sort .zero) nv) (R := .forallE (.bvar 0) (.sort .zero) nv)
      (bm := nv) (rel_head_trace Rel (.bvar 0)) h2
  exact BinderTrace.step (E := relFormer Rel) (T := type0)
    (B := .app (.const Rel []) (.bvar 0))
    (R := .forallE (.bvar 0) (.forallE (.bvar 0) (.sort .zero) nv) nv) (bm := nv) .refl h1

/-- **The walk on unopened bodies does not relate the declared type to the circuit's
telescope.** -/
theorem rel_unopened_trace_false (Rel : Key .anon) :
    ¬ BinderTrace (relEnv Rel) 3 (relFormer Rel) relTele := by
  intro h
  have hpre : PrefixEq 3 relTele relTeleUnopened :=
    h.prefixEq (fun _ _ hf => hf) (rel_unopened_trace Rel)
  have hdom : (Expr.bvar 1 : KExpr) = Expr.bvar 0 := hpre.2.2.2.2.1
  exact absurd (Expr.bvar.inj hdom) (by decide)

/-- The record of a registered family holds at this former and this telescope, which are
different terms. The record's other data is arbitrary: this is the statement about the traces,
not an accepted block. -/
theorem rel_formerOpenTraceAt (Rel : Key .anon) (p : Semantics.NativeParts .anon) :
    ∃ fam : Semantics.NativeFam .anon,
      Typing.FormerOpenTraceAt (relEnv Rel) fam ∧ fam.cvS.type = relFormer Rel ∧
        fam.cvTa.type = relTele ∧ fam.cvTa ≠ fam.cvS := by
  let cvS : ConstantVal .anon := { p.cvT with type := relFormer Rel }
  let cvTa : ConstantVal .anon := { p.cvT with type := relTele }
  let p' : Semantics.NativeParts .anon := { p with nP := 1, nIdx := 2, resSort := .zero }
  refine ⟨⟨p', cvS, cvTa, []⟩,
    ⟨TracedBinders.intro (rel_openBinderTrace Rel) (PrefixEq.of_strip 3 (E := relTele) rfl),
      TracedSort.intro (rel_openSortTrace Rel) (LvEq.refl _)⟩, rfl, rfl, ?_⟩
  intro heq
  have hty : relTele = relFormer Rel := congrArg ConstantVal.type heq
  have hb := (Expr.forallE.inj hty).2.1
  simp only [reduceCtorEq] at hb

/-! ## A universe-polymorphic alias: `def Pred.{w} (α : Type w) := α → Prop` -/

/-- `fun (α : Type l) => α → Prop`. -/
def predValueAt (l : Level) : KExpr :=
  .lam (.sort (.succ l)) (.forallE (.bvar 0) (.sort .zero) nv) nv

/-- An environment that stores `Pred` with one level parameter and that value. -/
def predEnv (Pred : Key .anon) : Env .anon :=
  ⟨[.defnInfo ⟨Pred, [0], .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0))) nv⟩
    (predValueAt (.param 0)) .abbrev]⟩

/-- The declared type of the family at the level `l`: `∀ (α : Type l), Pred.{l} α`. -/
def fooFormerAt (Pred : Key .anon) (l : Level) : KExpr :=
  .forallE (.sort (.succ l)) (.app (.const Pred [l]) (.bvar 0)) nv

/-- The free variable that opens the first binder, `α : Type l`. -/
abbrev fooVar (l : Level) : KExpr := .fvar 0 (.sort (.succ l))

/-- The telescope at the level `l`: `∀ (α : Type l) (a : α), Prop`. -/
def fooTeleAt (l : Level) : KExpr :=
  .forallE (.sort (.succ l)) (.forallE (.bvar 0) (.sort .zero) nv) nv

/-- The family's own level, with its parameter at position `0`: `max u u`. -/
abbrev fooLevel : Level := .max (.param 0) (.param 0)

/-- The same level with the parameter renamed to position `1`, as substitution builds it. -/
abbrev fooLevelRenamed : Level := .max (.param 1) (.param 1)

theorem predValue_instantiate (l : Level) :
    (predValueAt (.param 0)).instantiateLevelParams [0] [l] = predValueAt l := by
  simp [predValueAt, Expr.instantiateLevelParams, Level.subst, Level.subst.go, nv_instantiate]

theorem pred_unfold (Pred : Key .anon) (l : Level) :
    unfoldDefinition (predEnv Pred) (.const Pred [l]) = some (predValueAt l) := by
  have hfind := find_singleton Pred [0]
    (.forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0))) nv)
    (predValueAt (.param 0)) .abbrev
  have h := unfold_const_mkAppN (us := [l]) [] hfind rfl
  exact (show unfoldDefinition (predEnv Pred) (.const Pred [l]) =
    some ((predValueAt (.param 0)).instantiateLevelParams [0] [l]) from h).trans
      (congrArg some (predValue_instantiate l))

theorem pred_defnLevelsClosed (Pred : Key .anon) : DefnLevelsClosed (predEnv Pred) :=
  defnLevelsClosed_singleton (by
    simp [predValueAt, Expr.allLevelParamsDefined, Level.allParamsDefined, nv,
      BinderMeta.leanNever])

/-- **The walk of the block run**, at any level: the declared type builds the telescope. -/
theorem foo_openBinderTrace (Pred : Key .anon) (l : Level) :
    OpenBinderTrace (predEnv Pred) 0 2 (fooFormerAt Pred l) (fooTeleAt l) := by
  have h2 : OpenBinderTrace (predEnv Pred) 2 0 (.sort .zero) (.sort .zero) := .done
  have ht : Trace (predEnv Pred) (.app (.const Pred [l]) (fooVar l))
      (.forallE (fooVar l) (.sort .zero) nv) :=
    .cons (.appFn (.delta (pred_unfold Pred l)))
      (.cons (Step.beta (ty := .sort (.succ l)) (body := .forallE (.bvar 0) (.sort .zero) nv)
        (a := fooVar l) (mb := nv)) .refl)
  have h1 : OpenBinderTrace (predEnv Pred) 1 1 (.app (.const Pred [l]) (fooVar l))
      (.forallE (fooVar l) (.sort .zero) nv) :=
    OpenBinderTrace.step (d := 1) (n := 0) (E := .app (.const Pred [l]) (fooVar l))
      (T := fooVar l) (B := .sort .zero) (R := .sort .zero) (bm := nv) ht h2
  exact OpenBinderTrace.step (d := 0) (n := 1) (E := fooFormerAt Pred l) (T := .sort (.succ l))
    (B := .app (.const Pred [l]) (.bvar 0)) (R := .forallE (fooVar l) (.sort .zero) nv)
    (bm := nv) .refl h1

/-- Renaming the level parameter from position `0` to position `1`, as the recursor run of a
family with one level parameter does when the recursor eliminates into every sort. -/
theorem fooFormer_renamed (Pred : Key .anon) :
    posOf [1, 0] (fooFormerAt Pred fooLevel) = fooFormerAt Pred fooLevelRenamed := by
  have hpos : posLevels [1, 0] = [Level.param 0, Level.param 1] := rfl
  simp [posOf, hpos, fooFormerAt, fooLevel, fooLevelRenamed, Expr.instantiateLevelParams,
    Level.subst, Level.subst.go, nv_instantiate]

theorem fooTele_renamed :
    posOf [1, 0] (fooTeleAt fooLevel) = fooTeleAt fooLevelRenamed := by
  have hpos : posLevels [1, 0] = [Level.param 0, Level.param 1] := rfl
  simp [posOf, hpos, fooTeleAt, fooLevel, fooLevelRenamed, Expr.instantiateLevelParams,
    Level.subst, Level.subst.go, nv_instantiate]

/-- **The walk of the recursor run, from the commutation with level instantiation**: the
renamed declared type builds the renamed telescope of the block run. -/
theorem foo_openBinderTrace_renamed (Pred : Key .anon) :
    OpenBinderTrace (predEnv Pred) 0 2 (posOf [1, 0] (fooFormerAt Pred fooLevel))
      (posOf [1, 0] (fooTeleAt fooLevel)) :=
  (foo_openBinderTrace Pred fooLevel).instantiateLevelParams (pred_defnLevelsClosed Pred)
    [1, 0] (posLevels [1, 0])

/-- **Every walk from the renamed declared type builds the renamed telescope of the block
run.** -/
theorem foo_renamed_unique (Pred : Key .anon) {Y : KExpr}
    (hY : OpenBinderTrace (predEnv Pred) 0 2 (posOf [1, 0] (fooFormerAt Pred fooLevel)) Y) :
    Y = fooTeleAt fooLevelRenamed :=
  (hY.unique (fun _ _ hf => hf) (foo_openBinderTrace_renamed Pred)).trans fooTele_renamed

/-- **What a registered family records serves the recursor run**: from the traced binders of
the declared type alone, every walk from the renamed declared type builds the renaming of one
telescope with the registered binder prefix. -/
theorem foo_registered_reads (Pred : Key .anon) :
    ∃ X, (X.stripPis 2).isSome = true ∧ PrefixEq 2 X (fooTeleAt fooLevel) ∧
      ∀ {Y : KExpr},
        OpenBinderTrace (predEnv Pred) 0 2 (posOf [1, 0] (fooFormerAt Pred fooLevel)) Y →
          Y = posOf [1, 0] X :=
  (TracedBinders.intro (foo_openBinderTrace Pred fooLevel)
    (PrefixEq.of_strip 2 (E := fooTeleAt fooLevel) rfl)).instantiated
    (pred_defnLevelsClosed Pred) [1, 0] (posLevels [1, 0])

/-- The telescope with the simplified level the circuit's level instantiation writes:
`∀ (α : Type u) (a : α), Prop` with `u` at position `1`. -/
abbrev fooTeleCircuit : KExpr := fooTeleAt (.param 1)

/-- The renamed telescope and the circuit's are different terms. -/
theorem fooTele_renamed_ne_circuit : fooTeleAt fooLevelRenamed ≠ fooTeleCircuit := by
  intro h
  simp [fooTeleAt, fooLevelRenamed] at h

/-- **They are equal up to the semantic equality of levels.** -/
theorem fooTele_renamed_lvEq_circuit :
    ExprLvEq (fooTeleAt fooLevelRenamed) fooTeleCircuit := by
  have hlv : LvEq (.succ fooLevelRenamed) (.succ (.param 1)) := by
    intro φ
    simp [Ix.Kernel.Level.eval, fooLevelRenamed]
  exact .forallE (.sort hlv) (.forallE .bvar (.sort (LvEq.refl _)))

end IxVM.Refinement.Decl.AliasTelescopeExamples
