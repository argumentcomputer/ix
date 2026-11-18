import IxVMRefinement.FamilyGraph.Composition
import IxVMRefinement.FamilyGraph.InnerChecked

/-! # Row `innerChecked` from what the family checks check

`InnerCheckedRow` asks, of the records a family check checks (`FamilyRun.innerCall`), four
facts. Two are read off the observations of functions the circuit batch does not change, or that
are proved already:

* `checked`: an advice record declaring one constant (`Decl.adviceRecord_checked`), an advice
  block (`Decl.adviceBlock_checked`: every member through `check_muts_all`), a container's
  recursor (`Decl.containerRec_checked`: `run_check`);
* `blocks`, its route part: the advice block's dispatch answered `0`
  (`Decl.adviceBlock_checked`); a container's recursor is no block
  (`Decl.containerRec_checked`).

The others are what the batch's assertions in the family check give of an inner record's used
references (`InnerRefsChecked`, a premise): no inert reference, a covered or `NeedOk` reference
(`assert_inner_refs_safe`: `assert_safe_used_refs` and `assert_not_block_ref`, in
`check_advice_record` and `container_refs_check`), none of the record's own constant addresses
(an advice record is no witnessed reference, earlier advice excludes the record itself, a
container's witnessed reference is no recursor). With the graph's `innerClosed` they give
`notInert` and `refsBelow`. The shape part of `blocks` (one inductive) is the premise
`AdviceBlockShape`, read off `check_advice_record`'s block arm (all members inductive,
`block_is_modeled = 0`). -/

namespace IxVM.Refinement.Typing

open IxVM.Consistency
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open FamilyAlias (FamilyCallAtLim)

/-- **What the batch's assertions in a family check give of the used references of a record it
checks** (premise; producer: the batch's `assert_inner_refs_safe` in `check_advice_record` and
`container_refs_check`, the batch's "an advice record is no witnessed reference" in
`check_advice_record`, and "a container recursor's witnessed reference is no recursor" in
`container_refs_ok`): no inert reference, a covered or `NeedOk` reference, none of the record's
own constant addresses. -/
def InnerRefsChecked : Prop :=
  ∀ (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (lim : Option Nat)
    (bAddr B rb : _root_.Address) (cs : List (Call F)) (a : _root_.Address),
    LoadedReads.RunStore calls E₀ → FamilyCallAtLim calls bAddr t B rb lim cs →
    ((AdviceCheckIn cs bAddr t lim a ∧ ∀ c, recordOf E₀ a = some c → ¬ IsProj c) ∨
      ContainerRecCheckIn cs bAddr t lim a) →
    ∀ x, UsedRef E₀ a x →
      ¬ InertAt t x ∧ (Covered t x ∨ NeedOk E₀ x) ∧
      ∀ c, recordOf E₀ a = some c → ¬ ConstAddrOf a c x

/-- **An advice block a family check checked is one inductive type** (premise; read off
`check_advice_record`'s block arm: every member inductive, `muts_indc_count` against the
length, and the dispatch `block_is_modeled` answering `0`, which it does for two or more
inductive types only with `1`). -/
def AdviceBlockShape : Prop :=
  ∀ (calls cs : List (Call F)) (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (lim : Option Nat)
    (bAddr a : _root_.Address) (c : Ixon.Constant) (ms : Array Ixon.MutConst),
    LoadedReads.RunStore calls E₀ → (∀ cl ∈ cs, cl ∈ calls) → AdviceCheckIn cs bAddr t lim a →
    recordOf E₀ a = some c → c.info = .muts ms → ms.size ≠ 0 →
    ∃ ind : Ixon.Inductive, ms = #[.indc ind]

/-- **Row `innerChecked`**, from the two premises. -/
theorem innerCheckedRow_of (refs : InnerRefsChecked) (shape : AdviceBlockShape) :
    InnerCheckedRow := by
  intro calls t seeds E₀ lim Top rank hWalk R envT fam twin adv Inner hFR
  obtain ⟨bAddr, hcall⟩ := hFR.innerCall
  obtain ⟨bW, hW, hG⟩ := hWalk
  have hS := hW.runStore
  refine ⟨bAddr, ⟨?_, ?_, ?_, ?_⟩⟩
  · intro a c hI hc
    obtain ⟨B, rb, cs, -, hfc, hk⟩ := hcall a hI
    have hcs : ∀ cl ∈ cs, cl ∈ calls := by
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hsub⟩ := hfc
      exact hsub
    rcases hk with ⟨⟨h, h', rc, xa, seen, wset, r, cs₁, hrc, ⟨ab, hab, rfl⟩, ev, hsub₁⟩, hnp⟩ |
      ⟨h, h', rc, xa, ib, r, cs₁, hrc, haddr, ev, hsub₁⟩
    · rcases kind_cases c with hsa | hpr | ⟨ms, hms⟩
      · exact Or.inr (Decl.adviceRecord_checked hS hrc hab ev (fun cl h => hcs cl (hsub₁ cl h))
          hc hsa)
      · exact absurd hpr (hnp c hc)
      · exact Or.inl ⟨ms, hms, (Decl.adviceBlock_checked hS hrc hab ev
          (fun cl h => hcs cl (hsub₁ cl h)) hc hms).1⟩
    · exact Or.inr (Decl.containerRec_checked hS hrc haddr ev
        (fun cl h => hcs cl (hsub₁ cl h))).1
  · intro a x hI hu
    obtain ⟨B, rb, cs, -, hfc, hk⟩ := hcall a hI
    exact (refs calls t E₀ lim bAddr B rb cs a hS hfc hk x hu).1
  · intro a x hI hu
    obtain ⟨B, rb, cs, -, hfc, hk⟩ := hcall a hI
    obtain ⟨-, hcov | hok, hnown⟩ := refs calls t E₀ lim bAddr B rb cs a hS hfc hk x hu
    · exact Or.inr (Or.inl hcov)
    · rcases hFR.graph.innerClosed a x hI hu hok with hst | hcov | ⟨c, hc, hx⟩ | hob
      · exact Or.inl hst
      · exact Or.inr (Or.inl hcov)
      · exact absurd hx (hnown c hc)
      · exact Or.inr (Or.inr ⟨hok, hob⟩)
  · intro a c ms hI hU htw hc hms hnd h0
    obtain ⟨B, rb, cs, -, hfc, hk⟩ := hcall a hI
    have hcs : ∀ cl ∈ cs, cl ∈ calls := by
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hsub⟩ := hfc
      exact hsub
    rcases hk with ⟨hadv, hnp⟩ | ⟨h, h', rc, xa, ib, r, cs₁, hrc, haddr, ev, hsub₁⟩
    · refine ⟨shape calls cs t E₀ lim bAddr a c ms hS hcs hadv hc hms h0, ?_⟩
      obtain ⟨h, h', rc, xa, seen, wset, r, cs₁, hrc, ⟨ab, hab, rfl⟩, ev, hsub₁⟩ := hadv
      exact (Decl.adviceBlock_checked hS hrc hab ev (fun cl h => hcs cl (hsub₁ cl h)) hc hms).2
    · exact absurd hms ((Decl.containerRec_checked hS hrc haddr ev
        (fun cl h => hcs cl (hsub₁ cl h))).2 c hc ms)

end IxVM.Refinement.Typing

namespace IxVM.Refinement.Typing

/-- **An advice block a family check checked is one inductive type**: read off the observed
advice-record check (`Decl.adviceBlock_shape`). -/
theorem adviceBlockShape_holds : AdviceBlockShape := by
  intro calls cs t E₀ lim bAddr a c ms hS hcs hadv hc hms h0
  obtain ⟨h, h', rc, xa, seen, wset, r, cs₁, hrc, ⟨ab, hab, rfl⟩, ev, hsub₁⟩ := hadv
  exact Decl.adviceBlock_shape hS hab ev (fun cl h => hcs cl (hsub₁ cl h)) hc hms h0

/-- **Row `innerChecked`**, from what the batch's assertions give of the inner records' used
references alone. -/
theorem innerCheckedRow_of_refs (refs : InnerRefsChecked) : InnerCheckedRow :=
  innerCheckedRow_of refs adviceBlockShape_holds

end IxVM.Refinement.Typing
