import IxVMRefinement.Claim.TopStanding

/-! # The concrete typing claim export with standing and reference safety

The observation produces the guarded walk. Restriction to seed reachability supplies origins;
its stored guard clause propagates safety; actual axiom/quotient checks supply standing.
No standing, origin or edge-safety premise is requested from the caller.
-/

namespace IxVM.Refinement.Claim
open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM.Refinement.Core
open IxVM.Consistency
open IxVM (F)

/-- The accepted run supplies the exact ClaimExport consumed by the typing skeleton. -/
theorem claimPhase_typing {d : Digest} {value : SourceValue F} {heap : Heap F}
    {calls : List (Call F)}
    (ev : ObsFn W verifyClaim [digestValue d] [] value heap calls) :
    Typing.ClaimExport (TopWalk calls) calls d := by
  intro bytes c hde hpack hscope V seeds hseeds ctx hctx tb t hadm
  rcases claimPhase_typing_walk ev hde hpack hscope hseeds hctx hadm with
    hcol | ⟨lim, E₀, Top, rank, hW⟩
  · exact Or.inl hcol
  · exact Or.inr ⟨E₀, lim, TopReach t E₀ seeds, rank, hW.runStore,
      ctx.binding, hW.restrictReach, hW.reach_graph hW.safeRefs⟩

/-- The concrete walk supplies the cover adapter's exact NeedOk premise for every unit. -/
theorem TopWalk.need {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {seeds : List _root_.Address} {E₀ : Ixon.Env} {lim : Option Nat}
    {Top : _root_.Address → Prop} {rank : _root_.Address → Nat}
    (hw : TopWalk calls t seeds E₀ lim Top rank)
    {a : _root_.Address} {c : Ixon.Constant}
    (ha : Top a) (hc : recordOf E₀ a = some c) (hk : Typing.UnitKind c) (hl : InLogic c) :
    ∀ i ∈ usedRefIdxs c, ∀ x, c.refs.toList[i]? = some x →
      inertKey (IxVM.Consistency.keyOf t x) = false → ¬ Typing.Covered t x →
        Typing.NeedOk E₀ x := by
  obtain ⟨_, hW, _⟩ := hw
  exact hW.need_of_safe_edges hW.safeRefs ha hc hk hl

/-- The concrete walk retains the unchanged assembly graph. -/
theorem TopWalk.graph {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {seeds : List _root_.Address} {E₀ : Ixon.Env} {lim : Option Nat}
    {Top : _root_.Address → Prop} {rank : _root_.Address → Nat}
    (hw : TopWalk calls t seeds E₀ lim Top rank) : Typing.TopGraph t E₀ seeds Top rank := by
  obtain ⟨_, _, hg⟩ := hw
  exact hg

end IxVM.Refinement.Claim
