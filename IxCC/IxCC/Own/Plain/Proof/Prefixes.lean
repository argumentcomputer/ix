import IxCC.Own.Plain.Proof.Actions
import IxCC.Own.Plain.Proof.Environment
import IxCC.Own.Plain.Proof.Unfold

/-! Execution of the producer's action prefixes. Arguments are duplicated
per occurrence, including aliases; immediate arguments need no heap action.
The continuation retains precisely the source clock and environment. -/

set_option autoImplicit false

namespace IxCC.Own.Plain

open Rc
open IxCC.Sem (Result)

def evalActions (ρ : Own.Env) (H : Heap) : List Action → Result Heap
  | [] => .ok H
  | a :: acts => (evalAction ρ H a).bind fun H' => evalActions ρ H' acts

theorem eval_actionPrefix (P : Program) (k : Nat) (ρ : Own.Env) (J : List JEntry)
    (H : Heap) (acts : List Action) (c : Code) :
    eval P k ρ J H (actionPrefix acts c) =
      (evalActions ρ H acts).bind fun H' => eval P k ρ J H' c := by
  induction acts generalizing H with
  | nil => rfl
  | cons a acts ih =>
    rw [actionPrefix, eval_act]
    simp only [evalActions]
    cases ha : evalAction ρ H a <;> simp [Result.bind, ih]

def ArgsOwned (ρ : Own.Env) (args : List Fir.Arg) (roots : List RVal) : Prop :=
  ∀ x, Fir.Arg.var x ∈ args → ∃ v, ρ.get? x = some v ∧ v ∈ roots

theorem balance_rotate {H : Heap} {external : Nat → Nat}
    {values roots : List RVal} {v : RVal}
    (h : Balance H external (values ++ v :: roots)) :
    Balance H external (v :: values ++ roots) := by
  intro l
  have he := h l
  simp only [refsIn_append, refsIn] at *
  omega

theorem copies_sound (ρ : Own.Env) (H : Heap) (args : List Fir.Arg)
    {external : Nat → Nat} {roots values : List RVal}
    (hb : Balance H external roots) (ho : ArgsOwned ρ args roots)
    (ha : Own.evalArgs ρ args = some values) :
    ∃ H', evalActions ρ H (copies args) = .ok H' ∧
      Balance H' external (values ++ roots) ∧
      ∀ root, H.value? root = H'.value? root := by
  induction args generalizing H roots values with
  | nil =>
    have he : values = [] := by simpa [Own.evalArgs] using ha.symm
    subst values
    exact ⟨H, rfl, hb, fun _ => rfl⟩
  | cons arg args ih =>
    cases arg with
    | var x =>
      obtain ⟨v, hx, hm⟩ := ho x (by simp)
      cases hs : Own.evalArgs ρ args with
      | none => simp [Own.evalArgs, Own.evalArg, hx, hs] at ha
      | some vs =>
        have he : v :: vs = values := by simpa [Own.evalArgs, Own.evalArg, hx, hs] using ha
        subst values
        obtain ⟨H₁, hi, hb₁, hv₁⟩ := evalAction_inc_owned hx hb hm
        have ho₁ : ArgsOwned ρ args (v :: roots) := by
          intro y hy
          obtain ⟨w, hw, hm⟩ := ho y (List.mem_cons_of_mem _ hy)
          exact ⟨w, hw, List.mem_cons_of_mem _ hm⟩
        obtain ⟨H₂, hs₂, hb₂, hv₂⟩ := ih H₁ hb₁ ho₁ hs
        refine ⟨H₂, ?_, balance_rotate hb₂, fun root => (hv₁ root).trans (hv₂ root)⟩
        simp [copies, evalActions, hi, Result.bind, hs₂]
    | lit lit =>
      cases hs : Own.evalArgs ρ args with
      | none => simp [Own.evalArgs, Own.evalArg, hs] at ha
      | some vs =>
        have he : RVal.lit lit :: vs = values := by simpa [Own.evalArgs, Own.evalArg, hs] using ha
        subst values
        have ho₁ : ArgsOwned ρ args roots := by
          intro y hy
          exact ho y (List.mem_cons_of_mem _ hy)
        obtain ⟨H', hh, hb', hv⟩ := ih H hb ho₁ hs
        exact ⟨H', hh, by simpa [Balance, refsIn] using hb', hv⟩
    | erased =>
      cases hs : Own.evalArgs ρ args with
      | none => simp [Own.evalArgs, Own.evalArg, hs] at ha
      | some vs =>
        have he : RVal.erased :: vs = values := by simpa [Own.evalArgs, Own.evalArg, hs] using ha
        subst values
        have ho₁ : ArgsOwned ρ args roots := by
          intro y hy
          exact ho y (List.mem_cons_of_mem _ hy)
        obtain ⟨H', hh, hb', hv⟩ := ih H hb ho₁ hs
        exact ⟨H', hh, by simpa [Balance, refsIn] using hb', hv⟩

theorem evalArgs_cons_inv {ρ : Own.Env} {a : Fir.Arg} {as : List Fir.Arg} {values : List RVal}
    (h : Own.evalArgs ρ (a :: as) = some values) :
    ∃ v vs, Own.evalArg ρ a = some v ∧ Own.evalArgs ρ as = some vs ∧ values = v :: vs := by
  cases ha : Own.evalArg ρ a with
  | none => simp [Own.evalArgs, ha] at h
  | some v =>
    cases has : Own.evalArgs ρ as with
    | none => simp [Own.evalArgs, ha, has] at h
    | some vs =>
      exact ⟨v, vs, rfl, rfl, by simpa [Own.evalArgs, ha, has] using h.symm⟩

theorem heapArgs_sublist (imm : List Fir.Var) (args : List Fir.Arg) :
    (heapArgs imm args).Sublist args := by
  induction args with
  | nil => exact .slnil
  | cons a as ih =>
    dsimp only [heapArgs]
    cases isImmArg imm a
    · rw [if_neg Bool.false_ne_true]; exact ih.cons_cons _
    · rw [if_pos rfl]; exact ih.cons _

theorem heapArgs_scope {live : List Fir.Var} (imm : List Fir.Var) {args : List Fir.Arg}
    (hs : args.all (argIn live) = true) :
    (heapArgs imm args).all (argIn live) = true := by
  rw [List.all_eq_true] at hs ⊢
  intro a ha
  exact hs a ((heapArgs_sublist imm args).subset ha)

theorem refsIn_cons_imm {v : RVal} (vs : List RVal) (hv : ImmVal v) (location : Nat) :
    refsIn location (v :: vs) = refsIn location vs := by
  simp [refsIn, hv location]

theorem evalArgs_heapArgs {ρ : Own.Env} {imm : List Fir.Var} {args : List Fir.Arg} {values : List RVal}
    (himm : ImmEnv ρ imm) (ha : Own.evalArgs ρ args = some values) :
    ∃ heapValues,
      Own.evalArgs ρ (heapArgs imm args) = some heapValues ∧
      (∀ location, refsIn location values = refsIn location heapValues) ∧
      (∀ v, v ∈ values → v ∈ heapValues ∨ ImmVal v) := by
  induction args generalizing values with
  | nil =>
    have he : values = [] := by simpa [Own.evalArgs] using ha.symm
    subst values
    exact ⟨[], rfl, fun _ => rfl, fun _ hm => False.elim (List.not_mem_nil hm)⟩
  | cons a as ih =>
    obtain ⟨v, vs, hav, has, rfl⟩ := evalArgs_cons_inv ha
    obtain ⟨heapVs, hheap_as, hrefs_as, hmem_as⟩ := ih has
    dsimp only [heapArgs]
    cases h : isImmArg imm a with
    | false =>
      rw [if_neg Bool.false_ne_true]
      refine ⟨v :: heapVs, by simp [Own.evalArgs, hav, hheap_as], fun location => ?_, fun w hw => ?_⟩
      · dsimp only [refsIn]
        rw [hrefs_as location]
      · rcases List.mem_cons.mp hw with rfl | hw
        · exact Or.inl List.mem_cons_self
        · rcases hmem_as w hw with hm | himm_w
          · exact Or.inl (List.mem_cons_of_mem _ hm)
          · exact Or.inr himm_w
    | true =>
      rw [if_pos rfl]
      have hv_imm : ImmVal v := immVal_of_isImmArg himm h hav
      refine ⟨heapVs, hheap_as, fun location => ?_, fun w hw => ?_⟩
      · rw [refsIn_cons_imm vs hv_imm location, hrefs_as location]
      · rcases List.mem_cons.mp hw with rfl | hw
        · exact Or.inr hv_imm
        · exact hmem_as w hw

theorem copies_heapArgs_sound (ρ : Own.Env) (H : Heap) {imm : List Fir.Var} (args : List Fir.Arg)
    {external : Nat → Nat} {roots values : List RVal}
    (himm : ImmEnv ρ imm) (hb : Balance H external roots) (ho : ArgsOwned ρ args roots)
    (ha : Own.evalArgs ρ args = some values) :
    ∃ H', evalActions ρ H (copies (heapArgs imm args)) = .ok H' ∧
      Balance H' external (values ++ roots) ∧
      ∀ root, H.value? root = H'.value? root := by
  obtain ⟨heapValues, hheap, hrefs, _⟩ := evalArgs_heapArgs himm ha
  have ho_heap : ArgsOwned ρ (heapArgs imm args) roots :=
    fun x hx => ho x ((heapArgs_sublist imm args).subset hx)
  obtain ⟨H', hcopy, hb', hv⟩ := copies_sound ρ H (heapArgs imm args) hb ho_heap hheap
  refine ⟨H', hcopy, ?_, hv⟩
  intro l
  have hbl := hb' l
  simp only [refsIn_append, ← hrefs l] at hbl ⊢
  exact hbl


end IxCC.Own.Plain
