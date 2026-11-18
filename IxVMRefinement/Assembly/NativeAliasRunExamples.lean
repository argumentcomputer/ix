import IxVMRefinement.Assembly.NativeAliasRunTrace
import IxVMRefinement.Assembly.NativeAliasOpenTraceExamples

/-! # The relation alias, from the runs of the block check

`rel_block_runs`: in any scoped context whose environment stores
`Rel := fun (α : Type) => α → α → Prop`, take an observed run of the result-sort walk and an
observed run of the block's telescope builder for three binders, each on a pointer that
represents the declared type `∀ (α : Type), Rel α`. Then the builder's output represents
`∀ (α : Type) (a : α) (b : α), Prop` with the third domain the variable two binders up
(`relTele`), the walk's level is `Prop`'s, and the family with that stored former type, that
telescope constant type and that sort has the record `FormerOpenTraceAt`.

Nothing here says what the heap telescope is: `relTele` is the conclusion, derived from the
observations through the head-trace specification of `KernelGuard::head` and the determinism
of the telescope walk. -/

set_option linter.unusedVariables false

namespace IxVM.Refinement.Decl.AliasTelescopeExamples

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM.Refinement.Core
open Ix.Kernel (Expr Level Env Key ConstantInfo ConstantVal BinderMeta NativeParts)

/-- The stored definition of `Rel`. -/
def relConst (Rel : Key .anon) : ConstantInfo .anon :=
  .defnInfo ⟨Rel, [], .forallE type0 type0 nv⟩ relValue .abbrev

/-- An environment that stores `Rel` so keeps every lookup of the one-definition
environment. -/
theorem relEnv_le {env : Env .anon} {Rel : Key .anon}
    (hRel : env.find? Rel = some (relConst Rel)) :
    ∀ k ci, (relEnv Rel).find? k = some ci → env.find? k = some ci := by
  intro k ci hf
  have hcons : (relEnv Rel).find? k = if Rel = k then some (relConst Rel) else none :=
    Ix.Kernel.Env.find?_cons (c := relConst Rel) (env := Env.empty) (n := k)
  rw [hcons] at hf
  by_cases hk : Rel = k
  · rw [ite_eq_left hk] at hf
    have hci : relConst Rel = ci := Option.some.inj hf
    subst hci
    subst hk
    exact hRel
  · rw [ite_eq_right hk] at hf
    cases hf

/-- **The record of a registered family, from the runs of the block check on the relation
alias.** -/
theorem rel_block_runs {c : ScopedCtx} (hc : ScopedCoreFacts c) {Rel : Key .anon}
    (hRel : c.env.find? Rel = some (relConst Rel))
    {rc₁ pe₁ types₁ rc₂ pe₂ types₂ ps r : SourceValue F} {h₁ h₁' h₂ h₂' : Heap F}
    {cs₁ cs₂ : List (Call F)}
    (hrc₁ : RCRep c.t c.lim h₁ rc₁) (hty₁ : TypesRep c.κ (fun _ => default) h₁ 0 types₁)
    (hg₁ : CoreGood c cs₁) (hS₁ : Tm c.κ 0 (fun _ => default) h₁ 0 (relFormer Rel) pe₁)
    (evs : ObsFn W "KernelCheck::get_result_sort_level"
      [rc₁, pe₁, .field ((3 : Nat) : F), types₁] h₁ ps h₁' cs₁)
    (hext : Heap.Extends h₁' h₂)
    (hrc₂ : RCRep c.t c.lim h₂ rc₂) (hty₂ : TypesRep c.κ (fun _ => default) h₂ 0 types₂)
    (hg₂ : CoreGood c cs₂) (hS₂ : Tm c.κ 0 (fun _ => default) h₂ 0 (relFormer Rel) pe₂)
    (evt : ObsFn W "KernelCheck::former_tele_at"
      [rc₂, pe₂, .field ((3 : Nat) : F), types₂, ps] h₂ r h₂' cs₂)
    (p : NativeParts .anon) :
    ∃ fam : Ix.Kernel.Semantics.NativeFam .anon,
      fam.cvS.type = relFormer Rel ∧ fam.cvTa.type = relTele ∧ fam.p.resSort = .zero ∧
      Tm c.κ 0 (fun _ => default) h₂' 0 fam.cvTa.type r ∧
      Typing.FormerOpenTraceAt c.env fam := by
  obtain ⟨Z, s, bs, hZ, hstrip, hbind, hsort⟩ :=
    alias_block_runs_traced hc (n := 3) (by omega) hrc₁ hty₁ hg₁ hS₁ evs hext hrc₂ hty₂ hg₂
      hS₂ evt
  have hle := relEnv_le hRel
  have hs : s = .zero :=
    hsort.unique (fun _ _ hf => hf) ((rel_openSortTrace Rel).mono hle)
  subst hs
  have hpre : PrefixEq 3 Z relTele :=
    hbind.prefixEq (fun _ _ hf => hf)
      (TracedBinders.intro ((rel_openBinderTrace Rel).mono hle)
        (PrefixEq.of_strip 3 (E := relTele) rfl))
  have hZeq : Z = relTele :=
    PrefixEq.eq_of_stripPis (bs' := [(type0, nv), (.bvar 0, nv), (.bvar 1, nv)]) hpre hstrip rfl
  subst hZeq
  exact ⟨⟨{ p with nP := 1, nIdx := 2, resSort := .zero },
      { p.cvT with type := relFormer Rel }, { p.cvT with type := relTele }, []⟩,
    rfl, rfl, rfl, hZ, ⟨hbind, TracedSort.intro hsort (LvEq.refl _)⟩⟩

end IxVM.Refinement.Decl.AliasTelescopeExamples
