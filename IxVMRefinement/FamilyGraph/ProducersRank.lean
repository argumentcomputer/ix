import IxVMRefinement.Claim.TopExport

/-! # The walk's rank is read only between top-walked addresses

`Claim.TopWalk` constrains its rank only by comparisons between two top-walked addresses (a used
reference and its user, a projection record and its block). So any rank that keeps those strict
comparisons is the rank of the same walk (`topWalk_of_rankOrder`). In particular the walk's rank
spread out by a factor (`topWalk_scale`) leaves room below every top-walked address for records
a family check checks, which the walk does not reach: their ranks are not the walk's to give. -/

namespace IxVM.Refinement.Typing

open IxVM (F)
open Aiur.Generic.SourceSemantics (Call)

/-- **A rank that keeps the walk's strict comparisons between top-walked addresses is a rank of
the same walk.** -/
theorem topWalk_of_rankOrder {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {seeds : List _root_.Address} {E₀ : Ixon.Env} {lim : Option Nat}
    {Top : _root_.Address → Prop} {rank rank' : _root_.Address → Nat}
    (h : Claim.TopWalk calls t seeds E₀ lim Top rank)
    (hord : ∀ a x, Top a → Top x → rank x < rank a → rank' x < rank' a) :
    Claim.TopWalk calls t seeds E₀ lim Top rank' := by
  obtain ⟨bAddr, hW, hG⟩ := h
  refine ⟨bAddr, ⟨hW.topLim, hW.table, hW.runStore, hW.hashedStored, hW.seedsTop, hW.record,
    ?_, ?_, hW.seedLogic, hW.seedNotInert, hW.checked, hW.refsNotInert, hW.refsNotBlock,
    hW.safeRefs, hW.quotBound⟩, ⟨hG.seedsTop, hG.record, ?_, ?_, hG.members, hG.projMember, hG.standing,
    hG.seedLogic⟩⟩
  · intro a x hT hu
    rcases hW.closed a x hT hu with ⟨hx, hr⟩ | hc
    · exact Or.inl ⟨hx, hord a x hT hx hr⟩
    · exact Or.inr hc
  · intro a c hT hc hp
    obtain ⟨ho, hr⟩ := hW.owner a c hT hc hp
    exact ⟨ho, hord a _ hT ho hr⟩
  · intro a x hT hu
    rcases hG.closed a x hT hu with ⟨hx, hr⟩ | hc
    · exact Or.inl ⟨hx, hord a x hT hx hr⟩
    · exact Or.inr hc
  · intro a c hT hc hp
    obtain ⟨ho, hr⟩ := hG.owner a c hT hc hp
    exact ⟨ho, hord a _ hT ho hr⟩

/-- **The walk's rank spread out by `k + 1`** is a rank of the same walk: between two
top-walked ranks it leaves `k` free ranks. -/
theorem topWalk_scale {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {seeds : List _root_.Address} {E₀ : Ixon.Env} {lim : Option Nat}
    {Top : _root_.Address → Prop} {rank : _root_.Address → Nat}
    (h : Claim.TopWalk calls t seeds E₀ lim Top rank) (k : Nat) :
    Claim.TopWalk calls t seeds E₀ lim Top (fun a => (k + 1) * rank a) :=
  topWalk_of_rankOrder h fun _ _ _ _ hr =>
    Nat.mul_lt_mul_of_pos_left hr (Nat.succ_pos k)

end IxVM.Refinement.Typing
