module

public import IxC.Kernel.Model.Open.Motive

@[expose] public section

/-!
# The rules' soundness over the public `Model`: pairwise conversion

`DefEqList`'s motive: the two lists have one length, and framed, graded readings of them
agree pointwise.
-/

namespace Ix.Kernel.Open

open SetTheory Ix.Kernel.SetModel
open Ix.Kernel.Rules
open Ix.Kernel.Model.Rules (Frame LeavesSub)

universe w

variable {V : Type w} [SetTheory V] {env : Env md} {M : Model V env} {φ : LevelParam → Nat}

/-- **`DefEqList`'s motive.** -/
def DefEqListS (M : Model V env) (φ : LevelParam → Nat) (d : Nat) (as bs : List (Expr md)) :
    Prop :=
  as.length = bs.length ∧
    ((∀ x ∈ as, Frame d x) → (∀ x ∈ bs, Frame d x) → ∀ σ,
      (∀ x ∈ as, Ctx M φ σ x) → (∀ x ∈ bs, Ctx M φ σ x) →
      ∀ vs ws, List.Forall₂ (Den M φ σ) as vs → List.Forall₂ (Den M φ σ) bs ws →
        (∀ x ∈ as, Gr M φ σ x) → (∀ x ∈ bs, Gr M φ σ x) → vs = ws)

theorem DefEqList.nil_sound {d : Nat} : DefEqListS M φ d [] [] := by
  refine ⟨rfl, fun _ _ _ _ _ vs ws hvs hws _ _ => ?_⟩
  cases hvs
  cases hws
  rfl

theorem DefEqList.cons_sound {d : Nat} {a b : Expr md} {as bs : List (Expr md)}
    (h : DefEqS M φ d a b) (ht : DefEqListS M φ d as bs) :
    DefEqListS M φ d (a :: as) (b :: bs) := by
  refine ⟨by simp [ht.1], fun hfa hfb σ hCa hCb vs ws hvs hws hga hgb => ?_⟩
  cases hvs with
  | cons hv hvs =>
    cases hws with
    | cons hw hws =>
      rw [h (hfa _ List.mem_cons_self) (hfb _ List.mem_cons_self) σ (hCa _ List.mem_cons_self)
          (hCb _ List.mem_cons_self) _ _ hv hw (hga _ List.mem_cons_self)
          (hgb _ List.mem_cons_self),
        ht.2 (fun x hx => hfa x (List.mem_cons_of_mem _ hx))
          (fun x hx => hfb x (List.mem_cons_of_mem _ hx)) σ
          (fun x hx => hCa x (List.mem_cons_of_mem _ hx))
          (fun x hx => hCb x (List.mem_cons_of_mem _ hx)) _ _ hvs hws
          (fun x hx => hga x (List.mem_cons_of_mem _ hx))
          (fun x hx => hgb x (List.mem_cons_of_mem _ hx))]

end Ix.Kernel.Open
