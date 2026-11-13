import IxCCGrounding.GradedHead

/-!
# Arguments that fit, from a graded spine (`IxCCGrounding.WordFits`, step W)

`graded` (`GradedLaw`) says that in a stored term every application applies a function that lies in a
product to an argument in that product's domain (`SpineMem` along a spine, `spineMem_of_graded`).
When the head itself lies in the denotation of a `∀`-telescope whose binders are in the graph regime,
domain uniqueness (`piR_dom_unique`) identifies each such domain with the telescope's own binder
domain, so the arguments fit the telescope (`Fits`), and the spine applied lies in the telescope's
body (`fits_of_spineMem`). The word case reads it at the word tower's constructors inside the stored
bridge and at `LT.lt` inside `Fin.mk`'s type. No law beyond `Model.mem` where the head's membership
comes from it.
-/

namespace IxCC.Grounding

open Ix.Kernel
open Ix.Kernel.SetTheory
open Ix.Kernel.SetModel

universe w

variable {V : Type w} [Ix.Kernel.SetTheory V] {env : KEnv}

/-- `SpineMem` peels its first argument. -/
theorem spineMem_cons {H x : V} {xs : List V} (h : SpineMem H (x :: xs)) :
    (∃ (r : Nat) (A : V) (B : V → V), H ∈ˢ piR r A B ∧ x ∈ˢ A) ∧ SpineMem (app H x) xs := by
  refine ⟨?_, fun j hj => ?_⟩
  · obtain ⟨r, A, B, h1, h2⟩ := h 0 (by simp)
    exact ⟨r, A, B, by simpa using h1, by simpa using h2⟩
  obtain ⟨r, A, B, h1, h2⟩ := h (j + 1) (by simpa using hj)
  exact ⟨r, A, B, by simpa using h1, by simpa using h2⟩

/-- **Arguments along a graded spine fit the head's telescope** (graph-regime binders), and the spine
applied lies in the telescope's body at the arguments. -/
theorem fits_of_spineMem (M : Model V env) {φ : LevelParam → Nat} :
    ∀ (bs : List (KExpr × BinderMeta)) (C : KExpr) {ρ : BVarIdx → V} {H T : V} {xs : List V},
      Denotes M.cval env φ ρ (piTele bs C) T → H ∈ˢ T → SpineMem H xs → xs.length = bs.length →
      (∀ bm ∈ bs, regime φ bm.2.pw ≠ 0) →
      Fits M.cval env φ ρ (piTele bs C) xs (pushAll xs ρ) C ∧
        ∃ R, Denotes M.cval env φ (pushAll xs ρ) C R ∧ xs.foldl app H ∈ˢ R
  | [], C, ρ, H, T, [], hT, hH, _, _, _ => by
    rw [pushAll_nil]
    exact ⟨.nil, T, hT, hH⟩
  | [], _, _, _, _, _ :: _, _, _, _, hl, _ => by simp at hl
  | _ :: _, _, _, _, _, [], _, _, _, hl, _ => by simp at hl
  | (A, m) :: bs, C, ρ, H, T, x :: xs, hT, hH, hsp, hl, hreg => by
    have hv : regime φ m.pw ≠ 0 := hreg (A, m) (List.mem_cons_self ..)
    have hT' : Denotes M.cval env φ ρ (.forallE A (piTele bs C) m) T := hT
    obtain ⟨Ad, Bf, hAd, hBf, -, rfl⟩ := den_pi.mp hT'
    obtain ⟨⟨r, A', B', hm', hx'⟩, hrest⟩ := spineMem_cons hsp
    have hr : r ≠ 0 := by
      rintro rfl
      exact not_pt_mem_piR_pos hv (eq_pt_of_mem_piR_zero hm' ▸ hH)
    have hxA : x ∈ˢ Ad := by rw [piR_dom_unique hv hr hH hm']; exact hx'
    have happ : app H x ∈ˢ Bf x := app_mem_piR_pos hv hH hxA
    obtain ⟨hfit, R, hR, hmem⟩ := fits_of_spineMem M bs C (hBf x hxA) happ hrest
      (by simpa using hl) (fun bm hbm => hreg bm (List.mem_cons_of_mem _ hbm))
    rw [pushAll_cons]
    exact ⟨.cons hAd hxA hfit, R, hR, by simpa using hmem⟩

end IxCC.Grounding
