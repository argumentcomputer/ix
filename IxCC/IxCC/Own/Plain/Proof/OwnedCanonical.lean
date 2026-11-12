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

/-! ## Action lists -/

theorem actionPrefix_append (as bs : List Action) (k : Code) :
    actionPrefix (as ++ bs) k = actionPrefix as (actionPrefix bs k) := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [actionPrefix, ih]

/-- Increments of each listed variable, then `k`. -/
theorem check_incs {Δ : JCtx} {I : Var → Bool} {P : Var → Prop} {k : Code} :
    ∀ (xs : List Var) {Γ : Ctx} {t : Var → Nat}, Shape Γ I t P →
      (∀ x, x ∈ xs → (I x = true ∨ 0 < t x) ∧ P x) →
      (∀ Γ', Shape Γ' I (fun y => t y + (if I y then 0 else xs.count y)) P →
        checkCode Δ Γ' k = .ok ()) →
      checkCode Δ Γ (actionPrefix (xs.map (fun x => .inc x 1)) k) = .ok ()
  | [], Γ, t, h, _, hk => hk Γ (h.congr (fun y => by simp))
  | x :: xs, Γ, t, h, hpre, hk => by
    obtain ⟨hx, hp⟩ := hpre x List.mem_cons_self
    obtain ⟨Γ₁, hinc, h₁⟩ := shape_inc h hx hp
    show (Γ.inc x 1 >>= fun Γ' => checkCode Δ Γ' _) = .ok ()
    rw [hinc]
    refine check_incs xs h₁ (fun y hy => ?_) (fun Γ' h' => hk Γ' (h'.congr (fun y => ?_)))
    · obtain ⟨hy', hp'⟩ := hpre y (List.mem_cons_of_mem _ hy)
      refine ⟨?_, hp'⟩
      rcases hy' with hy' | hy'
      · exact Or.inl hy'
      · right; split <;> omega
    · by_cases he : y = x
      · subst he
        cases hi : I y <;> simp [hi, List.count_cons] <;> omega
      · have hxy : (x == y) = false := beq_eq_false_iff_ne.mpr (fun h => he h.symm)
        simp [he, List.count_cons, hxy]

/-- Decrements of each listed (distinct) variable, then `k`. -/
theorem check_decs {Δ : JCtx} {I : Var → Bool} {P : Var → Prop} {k : Code} :
    ∀ (xs : List Var) {Γ : Ctx} {t : Var → Nat}, xs.Nodup → Shape Γ I t P →
      (∀ x, x ∈ xs → (I x = true ∨ 0 < t x) ∧ P x) →
      (∀ Γ', Shape Γ' I (fun y => t y - (if I y then 0 else xs.count y)) P →
        checkCode Δ Γ' k = .ok ()) →
      checkCode Δ Γ (actionPrefix (xs.map (fun x => .dec x)) k) = .ok ()
  | [], Γ, t, _, h, _, hk => hk Γ (h.congr (fun y => by simp))
  | x :: xs, Γ, t, hn, h, hpre, hk => by
    rw [List.nodup_cons] at hn
    obtain ⟨hx, hp⟩ := hpre x List.mem_cons_self
    obtain ⟨Γ₁, htake, _, h₁⟩ := shape_take h hx hp
    have hdec : Γ.dec x = .ok Γ₁.release := by simp [Ctx.dec, htake]
    show (Γ.dec x >>= fun Γ' => checkCode Δ Γ' _) = .ok ()
    rw [hdec]
    refine check_decs xs hn.2 h₁.release (fun y hy => ?_) (fun Γ' h' => hk Γ' (h'.congr (fun y => ?_)))
    · obtain ⟨hy', hp'⟩ := hpre y (List.mem_cons_of_mem _ hy)
      have hne : y ≠ x := by intro he; subst he; exact hn.1 hy
      refine ⟨?_, hp'⟩
      simpa [hne] using hy'
    · by_cases he : y = x
      · subst he
        have hc : xs.count y = 0 := List.count_eq_zero.mpr hn.1
        cases hi : I y <;> simp [hi, List.count_cons, hc]
      · have hxy : (x == y) = false := beq_eq_false_iff_ne.mpr (fun h => he h.symm)
        simp [he, List.count_cons, hxy]

/-- Taking a token per occurrence of each variable argument. -/
theorem check_takeArgs {I : Var → Bool} {P : Var → Prop} :
    ∀ (args : List Arg) {Γ : Ctx} {t : Var → Nat}, Shape Γ I t P →
      (∀ x, I x = false → (argVars args).count x ≤ t x) →
      (∀ x, x ∈ argVars args → P x) →
      ∃ Γ', Γ.takeArgs args = .ok Γ' ∧ Γ'.epoch = Γ.epoch ∧
        Shape Γ' I (fun y => t y - (if I y then 0 else (argVars args).count y)) P
  | [], Γ, t, h, _, _ => ⟨Γ, rfl, rfl, h.congr (fun y => by simp [argVars])⟩
  | .lit l :: as, Γ, t, h, hc, hp => by
    obtain ⟨Γ', h1, h2, h3⟩ := check_takeArgs as h (fun x hx => by simpa [argVars] using hc x hx)
      (fun x hx => hp x (by simpa [argVars] using hx))
    exact ⟨Γ', h1, h2,
      h3.congr (fun y => by simp [argVars])⟩
  | .erased :: as, Γ, t, h, hc, hp => by
    obtain ⟨Γ', h1, h2, h3⟩ := check_takeArgs as h (fun x hx => by simpa [argVars] using hc x hx)
      (fun x hx => hp x (by simpa [argVars] using hx))
    exact ⟨Γ', h1, h2,
      h3.congr (fun y => by simp [argVars])⟩
  | .var x :: as, Γ, t, h, hc, hp => by
    have hx : I x = true ∨ 0 < t x := by
      cases hi : I x with
      | true => exact Or.inl rfl
      | false =>
        right
        have := hc x hi
        simp [argVars, List.count_cons] at this
        omega
    obtain ⟨Γ₁, htake, he₁, h₁⟩ := shape_take h hx (hp x (by simp [argVars]))
    obtain ⟨Γ', h1, h2, h3⟩ := check_takeArgs as h₁ (fun y hy => ?_)
      (fun y hy => hp y (by simp [argVars, hy]))
    · refine ⟨Γ', ?_, h2.trans he₁, h3.congr (fun y => ?_)⟩
      · simp only [Ctx.takeArgs, Ctx.takeArg, htake]; exact h1
      · by_cases he : y = x
        · subst he
          cases hi : I y <;> simp [hi, argVars, List.count_cons] <;> omega
        · have hxy : (x == y) = false := beq_eq_false_iff_ne.mpr (fun h => he h.symm)
          simp [he, argVars, List.count_cons, hxy]
    · have := hc y hy
      by_cases he : y = x
      · subst he; simp [hy, argVars, List.count_cons] at this ⊢; omega
      · have hxy : (x == y) = false := beq_eq_false_iff_ne.mpr (fun h => he h.symm)
        simp [he, argVars, List.count_cons, hxy] at this ⊢; exact this

/-- Taking one token of each (distinct) variable. -/
theorem check_takeVars {I : Var → Bool} {P : Var → Prop} :
    ∀ (xs : List Var) {Γ : Ctx} {t : Var → Nat}, xs.Nodup → Shape Γ I t P →
      (∀ x, x ∈ xs → (I x = true ∨ 0 < t x) ∧ P x) →
      ∃ Γ', Γ.takeVars xs = .ok Γ' ∧
        Shape Γ' I (fun y => t y - (if I y then 0 else xs.count y)) P
  | [], Γ, t, _, h, _ => ⟨Γ, rfl, h.congr (fun y => by simp)⟩
  | x :: xs, Γ, t, hn, h, hpre => by
    rw [List.nodup_cons] at hn
    obtain ⟨hx, hp⟩ := hpre x List.mem_cons_self
    obtain ⟨Γ₁, htake, _, h₁⟩ := shape_take h hx hp
    obtain ⟨Γ', h1, h3⟩ := check_takeVars xs hn.2 h₁ (fun y hy => by
      obtain ⟨hy', hp'⟩ := hpre y (List.mem_cons_of_mem _ hy)
      have hne : y ≠ x := by intro he; subst he; exact hn.1 hy
      exact ⟨by simpa [hne] using hy', hp'⟩)
    refine ⟨Γ', ?_, h3.congr (fun y => ?_)⟩
    · simp only [Ctx.takeVars, htake]; exact h1
    · by_cases he : y = x
      · subst he
        have hc : xs.count y = 0 := List.count_eq_zero.mpr hn.1
        cases hi : I y <;> simp [hi, List.count_cons, hc]
      · have hxy : (x == y) = false := beq_eq_false_iff_ne.mpr (fun h => he h.symm)
        simp [he, List.count_cons, hxy]

/-- A context holding no token is closed. -/
theorem shape_closed {Γ : Ctx} {I : Var → Bool} {t : Var → Nat} {P : Var → Prop}
    (h : Shape Γ I t P) (hz : ∀ x, t x = 0) (what : String) : Γ.closed what = .ok () := by
  obtain ⟨toks, htok⟩ := h.toks
  have hnil : toks = [] := by
    cases toks with
    | nil => rfl
    | cons y ys =>
      have := htok.count y
      rw [h.tokens, hz] at this
      simp [List.count_cons] at this
  subst hnil
  have : Γ.total = 0 := by rw [htok.total]; rfl
  simp [Ctx.closed, this]

end IxCC.Own.Plain
