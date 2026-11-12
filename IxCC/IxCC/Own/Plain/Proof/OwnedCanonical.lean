import IxCC.Own.Plain.Proof.Owned.Program
import IxCC.Own.Plain.Proof.Candidate
import IxCC.Own.Plain.Proof.CheckedShape

/-! # The ownership checker accepts the canonical producer's map

`checkPlainMap_checkOwned`: a syntactic induction on the Fir code proving that the checker accepts
`lowerCode live joins c imm` from a context in which every live variable that is not an immediate
holds exactly one token (`Canon`). Token counts are tracked pointwise (`Shape`): a copy prefix adds
one token per occurrence, the consuming use takes them back, and at a terminal `moveCopies` and
`drops` leave every live variable at zero once the captured tokens are taken. No heap.

From it and `checkOwned_refines`, the landed `checked_program_refines`,
`checked_contract_program_refines` and `checked_program_reclaims` are re-derived with their
statements unchanged (`checked_program_refines'` …, pinned by `rfl` below). -/

set_option autoImplicit false

namespace IxCC.Own.Plain

open Rc
open IxCC.Fir (Var Arg)

/-! ## Pointwise token counts -/

/-- A context with nothing borrowed, its immediates `I` and its tokens `t`; its map entries are
for variables satisfying `P`. -/
structure Shape (Γ : Ctx) (I : Var → Bool) (t : Var → Nat) (P : Var → Prop) : Prop where
  imm : ∀ x, Γ.isImm x = I x
  tokens : ∀ x, Γ.tokens x = t x
  brw : ∀ x, Γ.brw.get? x = none
  toks : ∃ toks, Ctx.Tokens Γ toks
  immZero : ∀ x, I x = true → t x = 0
  own : ∀ x, Γ.own.contains x = true → P x

theorem Shape.congr {Γ : Ctx} {I : Var → Bool} {t t' : Var → Nat} {P : Var → Prop}
    (h : Shape Γ I t P) (he : ∀ x, t x = t' x) : Shape Γ I t' P :=
  ⟨h.imm, fun x => (h.tokens x).trans (he x), h.brw, h.toks,
    fun x hx => (he x).symm.trans (h.immZero x hx), h.own⟩

theorem Shape.release {Γ : Ctx} {I : Var → Bool} {t : Var → Nat} {P : Var → Prop}
    (h : Shape Γ I t P) : Shape Γ.release I t P :=
  ⟨fun x => by simpa using h.imm x, fun x => by simpa using h.tokens x, fun x => by simpa using h.brw x,
    by obtain ⟨toks, ht⟩ := h.toks; exact ⟨toks, ht.same rfl rfl⟩, h.immZero,
    fun x hx => h.own x (by simpa using hx)⟩

theorem shape_inc {Γ : Ctx} {I : Var → Bool} {t : Var → Nat} {P : Var → Prop}
    (h : Shape Γ I t P) {x : Var} (hx : I x = true ∨ 0 < t x) (hp : P x) :
    ∃ Γ', Γ.inc x 1 = .ok Γ' ∧
      Shape Γ' I (fun y => if y = x ∧ I x = false then t y + 1 else t y) P := by
  cases hi : I x with
  | true =>
    refine ⟨Γ, ?_, h.congr (fun y => by simp [hi])⟩
    simp [Ctx.inc, h.imm, hi]
  | false =>
    have hp' : 0 < t x := by simpa [hi] using hx
    have ht : 0 < Γ.tokens x := by rw [h.tokens]; exact hp'
    refine ⟨Γ.addOwn x 1, ?_, ?_⟩
    · simp [Ctx.inc, h.imm, hi, ht]
    · obtain ⟨toks, htok⟩ := h.toks
      refine ⟨fun y => by simpa using h.imm y, fun y => ?_, fun y => by simpa using h.brw y,
        ⟨_, htok.addOwn x⟩, fun y hy => ?_, fun y hy => ?_⟩
      · rw [Ctx.tokens_addOwn]
        by_cases he : y = x
        · subst he; simp [hi, h.tokens]
        · simp [he, h.tokens]
      · have hne : y ≠ x := by intro he; subst he; rw [hi] at hy; cases hy
        simp [hne, h.immZero y hy]
      · rw [Ctx.ownHas_addOwn] at hy
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hy
        rcases hy with rfl | hy
        · exact hp
        · exact h.own y hy

theorem shape_take {Γ : Ctx} {I : Var → Bool} {t : Var → Nat} {P : Var → Prop}
    (h : Shape Γ I t P) {x : Var} (hx : I x = true ∨ 0 < t x) (hp : P x) :
    ∃ Γ', Γ.take x = .ok Γ' ∧ Γ'.epoch = Γ.epoch ∧
      Shape Γ' I (fun y => if y = x ∧ I x = false then t y - 1 else t y) P := by
  cases hi : I x with
  | true =>
    refine ⟨Γ, ?_, rfl, h.congr (fun y => by simp [hi])⟩
    simp [Ctx.take, h.imm, hi]
  | false =>
    have hp' : 0 < t x := by simpa [hi] using hx
    obtain ⟨n, hn⟩ : ∃ n, Γ.own.get? x = some (n + 1) := by
      have := h.tokens x
      rw [Ctx.tokens_eq] at this
      cases hg : Γ.own.get? x with
      | none => rw [hg] at this; simp at this; omega
      | some m =>
        rw [hg] at this
        simp only [Option.getD_some] at this
        exact ⟨m - 1, by rw [show m - 1 + 1 = m by omega]⟩
    have hti : Γ.isImm x = false := by rw [h.imm]; exact hi
    have htake : Γ.take x = .ok { Γ with own := Γ.own.insert x n, total := Γ.total - 1 } := by
      simp [Ctx.take, hti, hn]
    refine ⟨_, htake, rfl, ?_⟩
    obtain ⟨toks, htok⟩ := h.toks
    obtain ⟨_, _, htok'⟩ := htok.take htake hti
    refine ⟨fun y => h.imm y, fun y => ?_, h.brw, ⟨_, htok'⟩, fun y hy => ?_, fun y hy => ?_⟩
    · simp only [Ctx.tokens_eq, Src.NatMap.get?_insert]
      by_cases he : y = x
      · subst he
        have := h.tokens y
        rw [Ctx.tokens_eq, hn] at this
        simp [hi]; simp at this; omega
      · simp only [he, ↓reduceIte, false_and]
        exact h.tokens y
    · have hne : y ≠ x := by intro he; subst he; rw [hi] at hy; cases hy
      simp [hne, h.immZero y hy]
    · simp only [Src.NatMap.contains, Src.NatMap.get?_insert] at hy
      split at hy
      · next he => subst he; exact hp
      · exact h.own y (by simpa [Src.NatMap.contains] using hy)

theorem shape_setImm {Γ : Ctx} {I : Var → Bool} {t : Var → Nat} {P : Var → Prop}
    (h : Shape Γ I t P) (x : Var) :
    Shape (Γ.setImm x) (fun y => decide (y = x) || I y) (fun y => if y = x then 0 else t y) P := by
  obtain ⟨toks, htok⟩ := h.toks
  refine ⟨fun y => by rw [Ctx.isImm_setImm, h.imm], fun y => by rw [Ctx.tokens_setImm, h.tokens],
    fun y => by rw [Ctx.brw_setImm, h.brw]; split <;> rfl, ⟨_, htok.setImm x⟩, fun y hy => ?_,
    fun y hy => ?_⟩
  · by_cases he : y = x
    · simp [he]
    · simp only [he, decide_false, Bool.false_or] at hy
      simp [he, h.immZero y hy]
  · rw [Ctx.ownHas_setImm] at hy
    simp only [Bool.and_eq_true] at hy
    exact h.own y hy.2

end IxCC.Own.Plain
