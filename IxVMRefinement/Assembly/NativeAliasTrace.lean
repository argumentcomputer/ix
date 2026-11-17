import IxVMRefinement.Assembly.NativeAliasRecPrefix
import IxVMRefinement.Assembly.LateRegistry
import IxC.Kernel.Model.HeadDeltaBeta

/-! # Operational telescope evidence for a stored native family

The binder builder and result-sort walk have different terminal behavior. `BinderTrace` keeps
the finite head traces at each consumed binder and permits a traced residual. `SortTrace` keeps
the separate result-sort walk. Head-trace determinism compares independent computations across
lookup-preserving extensions: binder prefixes agree, and the result sorts agree.

`FormerTraceAt` is a proposed internal replacement for identifying the stored former with its
built telescope. Ordinary syntactic entries produce it from their existing fields; an alias
producer must retain operational traces from its actual checks. The delta/beta trace relation
here is not asserted for arbitrary circuit whnf paths. In particular, typing or definitional
equality alone is not a producer of either trace.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel
open IxVM.Refinement.Core
open Ix.Kernel.HeadDeltaBeta (Trace)

/-- A telescope builder consumes `n` head-normalized binders and may reduce its residual. -/
inductive BinderTrace (env : Env .anon) : Nat → KExpr → KExpr → Prop
  | done {E R} : Trace env E R → BinderTrace env 0 E R
  | step {n E T B R bm} : Trace env E (.forallE T B bm) → BinderTrace env n B R →
      BinderTrace env (n + 1) E (.forallE T R bm)

/-- The result-sort walk follows the same heads, then head-normalizes to a sort. -/
inductive SortTrace (env : Env .anon) : Nat → KExpr → Level → Prop
  | done {E s} : Trace env E (.sort s) → SortTrace env 0 E s
  | step {n E T B bm s} : Trace env E (.forallE T B bm) → SortTrace env n B s →
      SortTrace env (n + 1) E s

theorem BinderTrace.mono {env env' : Env .anon}
    (hext : ∀ k ci, env.find? k = some ci → env'.find? k = some ci)
    {n : Nat} {E R : KExpr} (h : BinderTrace env n E R) : BinderTrace env' n E R := by
  induction h with
  | done ht => exact .done (ht.mono hext)
  | step ht _ ih => exact .step (ht.mono hext) ih

theorem SortTrace.mono {env env' : Env .anon}
    (hext : ∀ k ci, env.find? k = some ci → env'.find? k = some ci)
    {n : Nat} {E : KExpr} {s : Level} (h : SortTrace env n E s) : SortTrace env' n E s := by
  induction h with
  | done ht => exact .done (ht.mono hext)
  | step ht _ ih => exact .step (ht.mono hext) ih

/-- Independent builders agree on every consumed binder, even if their residuals differ. -/
theorem BinderTrace.prefixEq {env env' : Env .anon}
    (hext : ∀ k ci, env.find? k = some ci → env'.find? k = some ci) :
    ∀ {n : Nat} {E A B : KExpr}, BinderTrace env n E A → BinderTrace env' n E B → PrefixEq n A B
  | 0, _, _, _, .done _, .done _ => trivial
  | _ + 1, _, _, _, .step hh ha, .step hh' hb => by
    obtain ⟨rfl, rfl, rfl⟩ := hh.forall_unique hext hh'
    exact ⟨rfl, rfl, BinderTrace.prefixEq hext ha hb⟩

/-- The two result-sort walks agree exactly, rather than only on zero-ness. -/
theorem SortTrace.unique {env env' : Env .anon}
    (hext : ∀ k ci, env.find? k = some ci → env'.find? k = some ci) :
    ∀ {n : Nat} {E : KExpr} {s s' : Level}, SortTrace env n E s → SortTrace env' n E s' → s = s'
  | 0, _, _, _, .done h, .done h' => h.sort_unique hext h'
  | _ + 1, _, _, _, .step hh hs, .step hh' hs' => by
    obtain ⟨rfl, rfl, rfl⟩ := hh.forall_unique hext hh'
    exact SortTrace.unique hext hs hs'

/-- Syntactic binders require no head steps. -/
theorem BinderTrace.of_strip (env : Env .anon) :
    ∀ {n : Nat} {E R : KExpr} {bs : List (KExpr × BinderMeta)},
      E.stripPis n = some (bs, R) → BinderTrace env n E E
  | 0, _, _, _, _ => .done .refl
  | n + 1, E, R, bs, h => by
    cases E <;> simp only [Expr.stripPis, Option.map_eq_some_iff, reduceCtorEq] at h
    rename_i T B bm
    obtain ⟨⟨bs', R'⟩, hr, -⟩ := h
    exact .step .refl (BinderTrace.of_strip env hr)

/-- A syntactic telescope ending in a sort supplies its result-sort trace. -/
theorem SortTrace.of_strip (env : Env .anon) :
    ∀ {n : Nat} {E : KExpr} {s : Level} {bs : List (KExpr × BinderMeta)},
      E.stripPis n = some (bs, .sort s) → SortTrace env n E s
  | 0, E, s, bs, h => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    rw [h.2]
    exact .done .refl
  | n + 1, E, s, bs, h => by
    cases E <;> simp only [Expr.stripPis, Option.map_eq_some_iff, reduceCtorEq] at h
    rename_i T B bm
    obtain ⟨⟨bs', R'⟩, hr, heq⟩ := h
    obtain ⟨-, rfl⟩ := Prod.mk.inj heq
    exact .step .refl (SortTrace.of_strip env hr)

/-- A nonzero common prefix can have distinct residuals: one builder reduces the beta redex,
the other leaves it. Both select the same binder and the same result sort. -/
theorem binderTrace_distinct_residual_inhabited (env : Env .anon) :
    ∃ E A B : KExpr, BinderTrace env 1 E A ∧ BinderTrace env 1 E B ∧ A ≠ B ∧
      SortTrace env 1 E .zero := by
  let residual : KExpr := .app (.lam (.sort (.succ .zero)) (.bvar 0) .leanNever) (.sort .zero)
  let E : KExpr := .forallE (.sort .zero) residual .leanNever
  let A : KExpr := .forallE (.sort .zero) (.sort .zero) .leanNever
  have ht : Trace env residual (.sort .zero) := .cons .beta .refl
  refine ⟨E, A, E, .step .refl (.done ht), .step .refl (.done .refl), ?_,
    .step .refl (.done ht)⟩
  intro heq
  have hb := (Expr.forallE.inj heq).2.1
  cases hb

end IxVM.Refinement.Decl

namespace IxVM.Refinement.Typing

open Ix.Kernel
open Ix.Kernel.Semantics
open Ix.Kernel.Model

/-- The telescope information needed in addition to the registered family's existing stored
metadata. Operational evidence replaces equality of the built and stored former. -/
structure FormerTraceAt (env : Env .anon) (fam : NativeFam .anon) : Prop where
  arity : ArRes env fam.cvTa.type
  binders : Decl.BinderTrace env (fam.p.nP + fam.p.nIdx) fam.cvS.type fam.cvTa.type
  result : Decl.SortTrace env (fam.p.nP + fam.p.nIdx) fam.cvS.type fam.p.resSort

/-- The contract carries through preservation of existing lookups. -/
theorem FormerTraceAt.mono {env env' : Env .anon} {fam : NativeFam .anon}
    (hext : ∀ k ci, env.find? k = some ci → env'.find? k = some ci)
    (h : FormerTraceAt env fam) : FormerTraceAt env' fam :=
  ⟨h.arity.mono (fun {k ci} hk => hext k ci hk), h.binders.mono hext, h.result.mono hext⟩

/-- Existing syntactic registry entries produce the contract, using their stored type's arity. -/
theorem FormerTraceAt.of_native {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {env : Env .anon} {fam : NativeFam .anon} (h : LateFamAt t E env fam)
    (ha : StoreArR env) : FormerTraceAt env fam := by
  obtain ⟨bs, hs⟩ := h.sort
  rw [h.tele] at hs
  refine ⟨?_, ?_, Decl.SortTrace.of_strip env hs⟩
  · rw [h.tele]
    exact (ha.const h.stored.former).type
  · rw [h.tele]
    exact Decl.BinderTrace.of_strip env hs

/-- The late-recursion arity preservation needs the new arity field, with no telescope equality. -/
theorem FormerTraceAt.storeArR_late {env env' : Env .anon} {fam : NativeFam .anon}
    {cvR : ConstantVal .anon} {mI rP : Nat} {rules : List (RecRule .anon)}
    (h : FormerTraceAt env fam) (ha : StoreArR env)
    (hlps : fam.cvS.levelParams = fam.p.cvT.levelParams)
    (hrun : DeclNativeRecLateRunJ rulesJ env fam cvR mI rP rules env') : StoreArR env' :=
  storeArR_nativeRecLateTa ha h.arity hlps hrun

end IxVM.Refinement.Typing
