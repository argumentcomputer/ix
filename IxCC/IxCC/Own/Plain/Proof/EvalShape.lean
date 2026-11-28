import IxCC.Own.Plain.Proof.ShapeResult
import IxCC.Own.Plain.Proof.Mono

/-! Shape preservation for actual successful target executions. This is
independent of the source lock theorem and applies to arbitrary plain code
from a bounded environment and older-field heap. -/

set_option autoImplicit false
namespace IxCC.Own.Plain
open Rc
open IxCC.Sem (Result)

section
variable {P : Program} {k : Nat} (smaller : ∀ j, j < k → ShapeAtClock P j)
include smaller

mutual
theorem eval_shape (H : Heap) (ρ : Own.Env) (J : List JEntry) (c : Code) (slots : Src.NatMap Own.RVal)
    (hh : HeapOk H) (henv : EnvBounded H.size ρ) (hstack : StackBounded H.size J)
    (hslots : EnvBounded H.size slots) :
    ShapeResult H (eval P k ρ J H c slots) := by
  match c with
  | .act a c' =>
    rw [eval_act]
    apply shape_bind
    intro H' hop
    obtain ⟨hh', hsize⟩ := action_shape hh hop
    have grows : H.size ≤ H'.size := Nat.le_of_eq hsize.symm
    exact (eval_shape H' ρ J c' slots hh' (henv.mono grows)
      (hstack.mono grows) (hslots.mono grows)).preheap grows
  | .bind x r c' =>
    by_cases hc : ∃ f args, r = .call f args
    · obtain ⟨f, args, rfl⟩ := hc
      rw [eval_bindCall]
      apply shape_ofOption
      intro vs hvs
      have callShape := call_shape_of_smaller smaller f H vs hh (henv.args args hvs)
      apply shape_bind
      intro pair hp
      obtain ⟨v, H'⟩ := pair
      obtain ⟨hh', hsize, hv⟩ := callShape v H' hp
      exact (eval_shape H' (ρ.insert x v) J c' slots hh' ((henv.mono hsize).insert x hv)
        (hstack.mono hsize) (hslots.mono hsize)).preheap hsize
    · have hn : ∀ f args, r ≠ .call f args := fun f args h => hc ⟨f, args, h⟩
      rw [eval_bindRhs P k ρ J H x r c' hn]
      apply shape_bind
      intro pair hp
      obtain ⟨v, H'⟩ := pair
      obtain ⟨hh', hsize, hv⟩ := rhs_shape hh henv hp
      exact (eval_shape H' (ρ.insert x v) J c' slots hh' ((henv.mono hsize).insert x hv)
        (hstack.mono hsize) (hslots.mono hsize)).preheap hsize
  | .reset s x ctor fields uniq c' =>
    rw [eval_reset]
    apply shape_bind
    intro pair hp
    obtain ⟨sv, H'⟩ := pair
    obtain ⟨hh', hsize, hsv⟩ := resetMask_shape hh hp
    exact (eval_shape H' ρ J c' (slots.insert s sv) hh' (henv.mono hsize)
      (hstack.mono hsize) ((hslots.mono hsize).insert s hsv)).preheap hsize
  | .reuse x s ctor args uniq c' =>
    rw [eval_reuse]
    apply shape_ofOption
    intro sv _
    apply shape_bind
    intro pair hp
    obtain ⟨v, H'⟩ := pair
    obtain ⟨hh', hsize, hv⟩ := reuseVal_shape hh henv hp
    have hslots' : EnvBounded H'.size (slots.erase s) := fun k' w hk' => by
      have heq : (slots.erase s).get? k' = if k' = s then none else slots.get? k' :=
        Src.NatMap.get?_setF (s + 1) slots s none k' (Nat.lt_succ_self s)
      rw [heq] at hk'
      split at hk'
      · cases hk'
      · exact (hslots.mono hsize) k' w hk'
    exact (eval_shape H' (ρ.insert x v) J c' (slots.erase s) hh' ((henv.mono hsize).insert x hv)
      (hstack.mono hsize) hslots').preheap hsize
  | .dropSlot s c' =>
    rw [eval_dropSlot]
    apply shape_ofOption
    intro sv _
    apply shape_bind
    intro H' hp
    obtain ⟨hh', hsize⟩ := dropVal_shape hh hp
    have grows : H.size ≤ H'.size := Nat.le_of_eq hsize.symm
    have hslots' : EnvBounded H'.size (slots.erase s) := fun k' w hk' => by
      have heq : (slots.erase s).get? k' = if k' = s then none else slots.get? k' :=
        Src.NatMap.get?_setF (s + 1) slots s none k' (Nat.lt_succ_self s)
      rw [heq] at hk'
      split at hk'
      · cases hk'
      · exact (hslots.mono grows) k' w hk'
    exact (eval_shape H' ρ J c' (slots.erase s) hh' (henv.mono grows)
      (hstack.mono grows) hslots').preheap grows
  | .jp j ps captured rec body c' =>
    rw [eval_jp]
    apply eval_shape H ρ _ c' slots hh henv
    · intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact henv
      · exact hstack e he
    · exact hslots
  | .jmp j args =>
    rw [eval_jmp]
    apply shape_ofOption
    intro pair lookup
    obtain ⟨e, rest⟩ := pair
    obtain ⟨saved, tail⟩ := hstack.lookup lookup
    apply shape_ofOption
    intro vs values
    have entered := saved.bindAll e.params (henv.args args values)
    have afterStack := tail.after saved
    unfold jumpTo
    split
    · split
      · apply shape_later
        intro j hj
        exact smaller j hj H _ _ e.body .leaf hh entered afterStack (envBounded_empty H.size)
      · next uncharged =>
        have := jump_measure lookup (by simpa using uncharged)
        exact eval_shape H _ (e.after rest) e.body .leaf hh entered afterStack (envBounded_empty H.size)
    · intro v H' he; cases he
  | .case x alts d =>
    rw [eval_case]
    apply shape_ofOption
    intro v _
    cases hc : v.asCtor P.source.known H with
    | none => intro v H' he; cases he
    | some pair =>
      obtain ⟨key, fields⟩ := pair
      exact evalAlts_shape H ρ J key alts d slots hh henv hstack hslots
  | .ret a =>
    rw [eval_ret]
    apply shape_ofOption
    intro v hv
    intro w H' he
    cases he
    exact ⟨hh, Nat.le_refl _, henv.arg hv⟩
  | .tcall f args =>
    rw [eval_tcall]
    apply shape_ofOption
    intro vs hvs
    exact call_shape_of_smaller smaller f H vs hh (henv.args args hvs)
  | .trap =>
    rw [eval_trap]
    intro v H' he
    cases he
termination_by c.size + jweight J
decreasing_by
  all_goals simp_wf
  all_goals first
    | (simp only [Code.size]; omega)
    | (simp only [Code.size, jweight, JEntry.weight, Bool.false_eq_true, ↓reduceIte]; omega)
    | (simp only [Code.size] at this ⊢; omega)

theorem evalAlts_shape (H : Heap) (ρ : Own.Env) (J : List JEntry) (key : Key.CtorKey)
    (alts : List Alt) (d : Option Code) (slots : Src.NatMap Own.RVal)
    (hh : HeapOk H) (henv : EnvBounded H.size ρ) (hstack : StackBounded H.size J)
    (hslots : EnvBounded H.size slots) :
    ShapeResult H (evalAlts P k ρ J H key alts d slots) := by
  match alts, d with
  | [], some c =>
    rw [evalAlts_nil]
    exact eval_shape H ρ J c slots hh henv hstack hslots
  | [], none =>
    rw [evalAlts_nil]
    intro v H' he
    cases he
  | .mk key' body :: rest, d =>
    rw [evalAlts_cons]
    split
    · exact eval_shape H ρ J body slots hh henv hstack hslots
    · exact evalAlts_shape H ρ J key rest d slots hh henv hstack hslots
termination_by Code.altsSize alts + Code.optSize d + jweight J + 1
decreasing_by
  all_goals simp_wf
  all_goals simp only [Code.altsSize, Code.optSize]
  all_goals first
    | omega
    | (have := Code.size_pos body; omega)
end
end

theorem eval_heap_shape (P : Program) : ∀ k, ShapeAtClock P k := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih => exact eval_shape ih

theorem call_heap_shape (P : Program) (k : Nat) (f : Fir.FunId) (H : Heap) (vs : List RVal)
    (hh : HeapOk H) (hv : ValuesBounded H.size vs) : ShapeResult H (evalCall P k f vs H) :=
  call_shape_of_smaller (fun j _ => eval_heap_shape P j) f H vs hh hv

end IxCC.Own.Plain
