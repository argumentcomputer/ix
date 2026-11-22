import IxCC.Own.Plain.Proof.RhsShape
import IxCC.Own.Plain.Proof.Unfold

set_option autoImplicit false
namespace IxCC.Own.Plain
open Rc
open IxCC.Sem (Result later)

def ShapeResult (before : Heap) (result : Result (RVal × Heap)) : Prop :=
  ∀ v H', result = .ok (v, H') → HeapOk H' ∧ before.size ≤ H'.size ∧ Bounded H'.size v

theorem ShapeResult.preheap {H H' : Heap} {result : Result (RVal × Heap)}
    (h : ShapeResult H' result) (hs : H.size ≤ H'.size) : ShapeResult H result := by
  intro v after he
  obtain ⟨hh, hm, hb⟩ := h v after he
  exact ⟨hh, Nat.le_trans hs hm, hb⟩

theorem shape_bind {α : Type} {H : Heap} {r : Result α} {f : α → Result (RVal × Heap)}
    (h : ∀ a, r = .ok a → ShapeResult H (f a)) : ShapeResult H (r.bind f) := by
  cases r with
  | ok a => exact h a rfl
  | timeout | trap | resource _ | stuck => intro v H' he; cases he

theorem shape_ofOption {α : Type} {H : Heap} {o : Option α} {f : α → Result (RVal × Heap)}
    (h : ∀ a, o = some a → ShapeResult H (f a)) : ShapeResult H ((Result.ofOption o).bind f) := by
  cases ho : o with
  | none => intro v H' he; cases he
  | some a => exact h a ho

theorem shape_later {H : Heap} {k : Nat} {f : Nat → Result (RVal × Heap)}
    (h : ∀ j, j < k → ShapeResult H (f j)) : ShapeResult H (later k f) := by
  cases k with
  | zero => intro v H' he; cases he
  | succ k => exact h k (by omega)

def ShapeAtClock (P : Program) (k : Nat) : Prop :=
  ∀ (H : Heap) (ρ : Own.Env) (J : List JEntry) (c : Code),
    HeapOk H → EnvBounded H.size ρ → StackBounded H.size J → ShapeResult H (eval P k ρ J H c)

theorem call_shape_of_smaller {P : Program} {k : Nat}
    (smaller : ∀ j, j < k → ShapeAtClock P j) (f : Fir.FunId) (H : Heap) (vs : List RVal)
    (hh : HeapOk H) (hv : ValuesBounded H.size vs) : ShapeResult H (evalCall P k f vs H) := by
  rw [evalCall_eq]
  apply shape_ofOption
  intro fd _
  apply shape_ofOption
  intro body _
  unfold callFun
  split
  · apply shape_later
    intro j hj
    exact smaller j hj H _ [] body hh ((envBounded_empty H.size).bindAll _ hv)
      (by intro e he; cases he)
  · intro v H' he; cases he

end IxCC.Own.Plain
