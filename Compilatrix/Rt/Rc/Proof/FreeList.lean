import Compilatrix.Rt.Rc.Proof.Recycle

namespace Compilatrix.Rt.Rc.Procs
open Lir
open Compilatrix.Rt.Proof

def FreeChain (mem : X86.Memory) : List Word → Prop
  | [] => True
  | address :: tail => WordAt mem address (tail.headD 0) ∧ FreeChain mem tail

/-- Concrete stores preserve an existing class list when neither the new
dead header nor the context head overlaps any existing link word. -/
theorem FreeChain.recycle_frame {mem : X86.Memory} {context cls address oldHead : Word}
    {chain : List Word} (h : FreeChain mem chain)
    (ha : address.toNat+8 ≤ 2^64)
    (hh : (freeHeadAddress context cls).toNat+8 ≤ 2^64)
    (hfit : ∀ a ∈ chain, a.toNat+8 ≤ 2^64)
    (hsep : ∀ a ∈ chain,
      (a.toNat+8 ≤ address.toNat ∨ address.toNat+8 ≤ a.toNat) ∧
      (a.toNat+8 ≤ (freeHeadAddress context cls).toNat ∨
        (freeHeadAddress context cls).toNat+8 ≤ a.toNat)) :
    FreeChain (recycleParent mem context cls address oldHead) chain := by
  induction chain with
  | nil => trivial
  | cons a tail ih =>
    obtain ⟨hw, ht⟩ := h
    have hs := hsep a (by simp)
    refine ⟨(hw.write_disjoint ha (hfit a (by simp)) hs.1).write_disjoint
      hh (hfit a (by simp)) hs.2, ?_⟩
    exact ih ht (fun b hb => hfit b (by simp [hb])) (fun b hb => hsep b (by simp [hb]))

theorem FreeChain.recycle_push {mem : X86.Memory} {context cls address : Word}
    {chain : List Word} (h : FreeChain mem chain)
    (hr : ∀ j < 8, mem.readable (address+UInt64.ofNat j) = true)
    (ha : address.toNat+8 ≤ 2^64)
    (hh : (freeHeadAddress context cls).toNat+8 ≤ 2^64)
    (hac : address.toNat+8 ≤ (freeHeadAddress context cls).toNat ∨
      (freeHeadAddress context cls).toNat+8 ≤ address.toNat)
    (hfit : ∀ a ∈ chain, a.toNat+8 ≤ 2^64)
    (hsep : ∀ a ∈ chain,
      (a.toNat+8 ≤ address.toNat ∨ address.toNat+8 ≤ a.toNat) ∧
      (a.toNat+8 ≤ (freeHeadAddress context cls).toNat ∨
        (freeHeadAddress context cls).toNat+8 ≤ a.toNat)) :
    FreeChain (recycleParent mem context cls address (chain.headD 0)) (address :: chain) := by
  exact ⟨recycled_link hr ha hh hac, h.recycle_frame ha hh hfit hsep⟩



end Compilatrix.Rt.Rc.Procs
