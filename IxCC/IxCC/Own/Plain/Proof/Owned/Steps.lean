import IxCC.Own.Plain.Proof.Owned.Takes
import IxCC.Own.Plain.Proof.Actions
import IxCC.Own.Plain.Proof.Projection
import IxCC.Own.Plain.Proof.Scalars
import IxCC.Own.Plain.Proof.NonCall

/-! # One step of an accepted body: actions and bindings that call nothing

Each lemma takes the state before a checked step and gives the actual Own step and the state
after it. The heap facts are the existing ones (`inc_root`, `dropAll_retaining`, `alloc_sound`,
the projection and primitive lemmas); what is new is the token bookkeeping (a token taken from any
position, `SameRefs`), the borrowed mode (`CanDup` and the value kept by every step that releases
nothing), and the immediates a primitive's signature creates. -/

set_option autoImplicit false

namespace IxCC.Own.Plain

open Rc
open IxCC.Sem (Result)
open IxCC.Fir (Var Arg Rhs)

theorem Ctx.avail_known {Γ : Ctx} {y : Var} (h : Γ.avail y = true) : Γ.known y = true := by
  simp only [Ctx.avail_eq, Ctx.known_eq, Bool.or_eq_true, decide_eq_true_eq] at h ⊢
  rcases h with (h | h) | h
  · exact Or.inl (Or.inl h)
  · refine Or.inl (Or.inr ?_)
    rw [Ctx.tokens_eq] at h
    cases hg : Γ.own.get? y with
    | none => rw [hg] at h; simp at h
    | some n => simp [Src.NatMap.contains, hg]
  · refine Or.inr ?_
    simp only [Ctx.borrowed_eq, beq_iff_eq] at h
    simp [h]

theorem canDup_inc {H H' : Heap} {u v : RVal} (hv : CanDup H v) (hi : Rc.inc H u 1 = some H') :
    CanDup H' v := by
  cases u with
  | loc l =>
    cases hc : H.cell? l with
    | none => simp [Rc.inc, changeCount, hc] at hi
    | some c =>
      cases c with
      | dead => simp [Rc.inc, changeCount, hc] at hi
      | live rc m b =>
        cases m with
        | static =>
          simp only [Rc.inc, changeCount, hc, Option.some.injEq] at hi
          subst hi; exact hv
        | dyn =>
          by_cases hz : rc = 0
          · simp [Rc.inc, changeCount, hc, hz] at hi
          · have hp : 0 < rc := by omega
            rw [inc_dyn hc hp 1] at hi
            cases hi
            have hl : l < H.size := (Array.getElem?_eq_some_iff.mp hc).1
            cases v with
            | loc k =>
              change 0 < dynCount (setCell H l (.live (rc + 1) .dyn b)) k
              change 0 < dynCount H k at hv
              by_cases hk : l = k
              · subst hk
                simp [dynCount, setCell_cell H l _ hl]
              · simp only [dynCount, setCell_cell H l _ hl, if_neg hk]
                exact hv
            | lit _ | ctor0 _ | erased => trivial
  | lit _ | ctor0 _ | erased =>
    simp only [Rc.inc, changeCount, Option.some.injEq] at hi
    subst hi; exact hv

theorem canDup_alloc {H : Heap} {v : RVal} (hv : CanDup H v) (b : Body) :
    CanDup (H.alloc .rc b).2 v := by
  cases v with
  | loc k =>
    change 0 < dynCount (H.alloc .rc b).2 k
    change 0 < dynCount H k at hv
    rw [dynCount_alloc]
    split <;> omega
  | lit _ | ctor0 _ | erased => trivial

theorem den_imm {H H' : Heap} {v : RVal} {w : Fir.Val} (hv : ImmVal v) (hd : Proof.Den H v w) :
    Proof.Den H' v w := by
  change H'.value? v = some w
  rw [← value?_eq_of_immVal H H' hv]
  exact hd

end IxCC.Own.Plain
