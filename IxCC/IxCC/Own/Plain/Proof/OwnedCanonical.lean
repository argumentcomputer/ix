import IxCC.Own.Plain.Proof.Owned.Program
import IxCC.Own.Plain.Proof.Program
import IxCC.Own.Plain.Proof.Admission

/-! # Counting tokens against the canonical producer's map

The machinery of canonical acceptance (`checkPlainMap_checkOwned`, in `OwnedAccepts.lean`): the
induction there shows that the checker accepts `lowerCode live joins c imm` from a context in
which every live variable that is not an immediate holds exactly one token (`Canon`, here).
Token counts are tracked pointwise (`Shape`): a copy prefix adds one token per occurrence, the
consuming use takes them back, and at a terminal `moveCopies` and `drops` leave every live
variable at zero once the captured tokens are taken (`canonical_transfer`). No heap. -/

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
    have hpre : ∀ y, I y = false →
        (argVars as).count y ≤ (fun z => if z = x ∧ I x = false then t z - 1 else t z) y := by
      intro y hy
      have := hc y hy
      by_cases he : y = x
      · subst he; simp [hy, argVars, List.count_cons] at this ⊢; omega
      · have hxy : (x == y) = false := beq_eq_false_iff_ne.mpr (fun h => he h.symm)
        simp [he, argVars, List.count_cons, hxy] at this ⊢; exact this
    obtain ⟨Γ', h1, h2, h3⟩ := check_takeArgs as h₁ hpre
      (fun y hy => hp y (by simp [argVars, hy]))
    refine ⟨Γ', ?_, h2.trans he₁, h3.congr (fun y => ?_)⟩
    · simp only [Ctx.takeArgs, Ctx.takeArg, htake]; exact h1
    · by_cases he : y = x
      · subst he
        cases hi : I y <;> simp [hi, argVars, List.count_cons] <;> omega
      · have hxy : (x == y) = false := beq_eq_false_iff_ne.mpr (fun h => he h.symm)
        simp [he, argVars, List.count_cons, hxy]

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

/-! ## The producer's action lists, counted -/

theorem copies_eq : ∀ as : List Arg, copies as = (argVars as).map (fun x => .inc x 1)
  | [] => rfl
  | .var x :: as => by simp [copies, argVars, copies_eq as]
  | .lit _ :: as => by simp [copies, argVars, copies_eq as]
  | .erased :: as => by simp [copies, argVars, copies_eq as]

theorem drops_eq (cap : List Var) : ∀ live : List Var,
    drops cap live = (live.filter (fun x => !cap.contains x)).map (fun x => .dec x)
  | [] => rfl
  | x :: xs => by
    by_cases h : x ∈ cap
    · simp [drops, h, drops_eq cap xs, List.filter_cons]
    · simp [drops, h, drops_eq cap xs, List.filter_cons]

/-- The variables `moveCopies` increments. -/
def moveVars (seen : List Var) : List Arg → List Var
  | [] => []
  | .var x :: as => if seen.contains x then x :: moveVars seen as else moveVars (x :: seen) as
  | _ :: as => moveVars seen as

theorem moveCopies_eq : ∀ (seen : List Var) (as : List Arg),
    moveCopies seen as = (moveVars seen as).map (fun x => .inc x 1)
  | _, [] => rfl
  | seen, .var x :: as => by
    by_cases h : x ∈ seen
    · simp [moveCopies, moveVars, h, moveCopies_eq seen as]
    · simp [moveCopies, moveVars, h, moveCopies_eq (x :: seen) as]
  | seen, .lit _ :: as => by simp [moveCopies, moveVars, moveCopies_eq seen as]
  | seen, .erased :: as => by simp [moveCopies, moveVars, moveCopies_eq seen as]

theorem moveVars_sub : ∀ (seen : List Var) (as : List Arg) (y : Var),
    y ∈ moveVars seen as → y ∈ argVars as
  | _, [], _, h => by simp [moveVars] at h
  | seen, .var x :: as, y, h => by
    simp only [moveVars] at h
    split at h
    · rcases List.mem_cons.mp h with rfl | h
      · simp [argVars]
      · exact List.mem_cons_of_mem _ (moveVars_sub seen as y h)
    · exact List.mem_cons_of_mem _ (moveVars_sub (x :: seen) as y h)
  | seen, .lit _ :: as, y, h => by simpa [argVars] using moveVars_sub seen as y h
  | seen, .erased :: as, y, h => by simpa [argVars] using moveVars_sub seen as y h

theorem moveVars_count : ∀ (seen : List Var) (as : List Arg) (y : Var),
    (moveVars seen as).count y + (if y ∉ seen ∧ y ∈ argVars as then 1 else 0) =
      (argVars as).count y
  | _, [], _ => by simp [moveVars, argVars]
  | seen, .var x :: as, y => by
    have ih₁ := moveVars_count seen as y
    have ih₂ := moveVars_count (x :: seen) as y
    by_cases hs : seen.contains x = true
    · have hx : x ∈ seen := by simpa using hs
      simp only [moveVars, hs, ↓reduceIte, argVars, List.count_cons]
      by_cases he : x = y
      · subst he
        simp only [hx, not_true_eq_false, false_and, ↓reduceIte, beq_self_eq_true] at ih₁ ⊢
        omega
      · have hxy : (x == y) = false := beq_eq_false_iff_ne.mpr he
        simp only [hxy, Bool.false_eq_true, ↓reduceIte, List.mem_cons, Ne.symm he, false_or]
        omega
    · have hx : x ∉ seen := by simpa using hs
      simp only [moveVars, hs, Bool.false_eq_true, ↓reduceIte, argVars, List.count_cons]
      by_cases he : x = y
      · subst he
        simp only [List.mem_cons, true_or, not_true_eq_false, false_and, ↓reduceIte,
          hx, not_false_eq_true, and_self, beq_self_eq_true] at ih₂ ⊢
        omega
      · have hxy : (x == y) = false := beq_eq_false_iff_ne.mpr he
        simp only [hxy, Bool.false_eq_true, ↓reduceIte, List.mem_cons, Ne.symm he, false_or,
          not_or] at ih₂ ⊢
        by_cases hy : y ∈ seen
        · simp [hy] at ih₂ ⊢; omega
        · simp [hy, Ne.symm he] at ih₂ ⊢; omega
  | seen, .lit _ :: as, y => moveVars_count seen as y
  | seen, .erased :: as, y => moveVars_count seen as y

theorem heapArgs_sub (imm : List Var) : ∀ (as : List Arg) (y : Var),
    y ∈ argVars (heapArgs imm as) → y ∈ argVars as
  | [], _, h => by simp [heapArgs, argVars] at h
  | a :: as, y, h => by
    simp only [heapArgs] at h
    split at h
    · cases a <;> simp [argVars, heapArgs_sub imm as y h]
    · cases a with
      | var x =>
        simp only [argVars, List.mem_cons] at h ⊢
        rcases h with h | h
        · exact Or.inl h
        · exact Or.inr (heapArgs_sub imm as y h)
      | lit _ | erased => simpa [argVars] using heapArgs_sub imm as y h

theorem heapArgs_count (imm : List Var) : ∀ (as : List Arg) (y : Var), y ∉ imm →
    (argVars (heapArgs imm as)).count y = (argVars as).count y
  | [], _, _ => rfl
  | a :: as, y, hy => by
    have ih := heapArgs_count imm as y hy
    simp only [heapArgs]
    split
    · next himm =>
      cases a with
      | var x =>
        have hx : x ∈ imm := by simpa [isImmArg] using himm
        have hxy : (x == y) = false := beq_eq_false_iff_ne.mpr (fun h => hy (h ▸ hx))
        simp [argVars, List.count_cons, hxy, ih]
      | lit _ | erased => simpa [argVars] using ih
    · cases a with
      | var x => simp [argVars, List.count_cons, ih]
      | lit _ | erased => simpa [argVars] using ih

theorem count_filter_nodup {xs : List Var} (hn : xs.Nodup) (p : Var → Bool) (y : Var) :
    (xs.filter p).count y = if y ∈ xs ∧ p y = true then 1 else 0 := by
  rw [Ctx.count_nodup (hn.filter p)]
  simp [List.mem_filter]

/-! ## The invariant against the canonical producer's state -/

/-- Every live variable that is not an immediate holds one token; the producer's immediates are
immediates; the join context is the producer's join list. -/
structure Canon (Γ : Ctx) (Δ : JCtx) (live : List Var) (joins : Joins) (imm : List Var)
    (arities : JoinArities) : Prop where
  shape : Shape Γ (fun x => Γ.isImm x) (fun x => if x ∈ live ∧ Γ.isImm x = false then 1 else 0)
    (· ∈ live)
  immSub : ∀ x, x ∈ imm → Γ.isImm x = true
  immIn : ∀ x, Γ.isImm x = true → x ∈ live
  jctx : ∀ j, Δ.get? j = joins.lookup j
  capIn : ∀ j C, joins.lookup j = some C → C.Sublist live
  arity : ∀ j n, arities.lookup j = some n → ∃ C, joins.lookup j = some C
  nodup : live.Nodup

theorem Shape.mono {Γ : Ctx} {I : Var → Bool} {t : Var → Nat} {P Q : Var → Prop}
    (h : Shape Γ I t P) (hpq : ∀ x, P x → Q x) : Shape Γ I t Q :=
  ⟨h.imm, h.tokens, h.brw, h.toks, h.immZero, fun x hx => hpq x (h.own x hx)⟩

/-- Re-establish the canonical shape for a new scope. -/
theorem Shape.canon {Γ : Ctx} {I : Var → Bool} {t : Var → Nat} {P : Var → Prop} {live : List Var}
    (h : Shape Γ I t P) (ht : ∀ x, t x = if x ∈ live ∧ I x = false then 1 else 0)
    (hp : ∀ x, P x → x ∈ live) :
    Shape Γ (fun x => Γ.isImm x) (fun x => if x ∈ live ∧ Γ.isImm x = false then 1 else 0)
      (· ∈ live) := by
  refine ⟨fun x => rfl, fun x => ?_, h.brw, h.toks, fun x hx => ?_, fun x hx => hp x (h.own x hx)⟩
  · rw [h.tokens, ht, h.imm]
  · simp [hx]

/-- The terminal's transfer: afterwards every live non-immediate holds exactly the tokens its
argument occurrences and its capture will take. -/
theorem canonical_transfer {Γ : Ctx} {Δ : JCtx} {live : List Var} {joins : Joins}
    {imm : List Var} {arities : JoinArities} (h : Canon Γ Δ live joins imm arities)
    (C : List Var) (hC : C.Sublist live) (args : List Arg)
    (hargs : ∀ x, x ∈ argVars args → x ∈ live) (k : Code)
    (hk : ∀ Γ' t', Shape Γ' (fun x => Γ.isImm x) t' (· ∈ live) →
      (∀ y, Γ.isImm y = false → t' y = (argVars args).count y + C.count y) →
      checkCode Δ Γ' k = .ok ()) :
    checkCode Δ Γ (transfer live imm C args k) = .ok () := by
  have hCn : C.Nodup := hC.nodup h.nodup
  unfold transfer transferActions
  rw [actionPrefix_append, moveCopies_eq, drops_eq]
  apply check_incs _ h.shape
  · intro x hx
    have hl : x ∈ live := hargs x (heapArgs_sub imm args x (moveVars_sub _ _ x hx))
    refine ⟨?_, hl⟩
    cases hi : Γ.isImm x
    · right; simp [hl, hi]
    · left; rfl
  intro Γ₁ h₁
  apply check_decs _ (h.nodup.filter _) h₁
  · intro x hx
    have hl : x ∈ live := (List.mem_filter.mp hx).1
    refine ⟨?_, hl⟩
    cases hi : Γ.isImm x
    · right; simp [hl, hi] <;> omega
    · left; rfl
  intro Γ₂ h₂
  apply hk Γ₂ _ h₂
  intro y hy
  simp only [hy, Bool.false_eq_true, ↓reduceIte]
  have hyimm : y ∉ imm := fun hm => by rw [h.immSub y hm] at hy; cases hy
  have hmc := moveVars_count (C ++ imm) (heapArgs imm args) y
  have hhc := heapArgs_count imm args y hyimm
  rw [count_filter_nodup h.nodup]
  rw [Ctx.count_nodup hCn]
  by_cases hl : y ∈ live
  · by_cases hc : y ∈ C
    · have hin : y ∈ C ++ imm := List.mem_append_left _ hc
      simp only [hin, not_true_eq_false, false_and, ↓reduceIte] at hmc
      simp [hl, hc, hin, hy]
      omega
    · have hin : y ∉ C ++ imm := by simp [hc, hyimm]
      by_cases hh : y ∈ argVars (heapArgs imm args)
      · have hpos : 0 < (argVars (heapArgs imm args)).count y := List.count_pos_iff.mpr hh
        simp only [hin, not_false_eq_true, hh, and_self, ↓reduceIte] at hmc
        simp [hl, hc, hyimm, hh, hy]
        omega
      · have hz : (argVars (heapArgs imm args)).count y = 0 := List.count_eq_zero.mpr hh
        simp only [hh, and_false, ↓reduceIte] at hmc
        simp [hl, hc, hyimm, hh, hy]
        omega
  · have ha : (argVars args).count y = 0 :=
      List.count_eq_zero.mpr (fun hm => hl (hargs y hm))
    have hc : y ∉ C := fun hm => hl (hC.subset hm)
    have hm0 : (moveVars (C ++ imm) (heapArgs imm args)).count y = 0 := by omega
    simp [hl, hc, hm0, ha]

/-! ## Small facts about the checker's steps -/

theorem except_bind_of_ok {ε α β : Type} {m : Except ε α} {f : α → Except ε β} {a : α} {b : β}
    (hm : m = .ok a) (hf : f a = .ok b) : (m >>= f) = .ok b := by
  rw [hm]; exact hf

theorem need_ok {Γ : Ctx} {x : Var} (h : Γ.avail x = true) (w : String) : Γ.need x w = .ok () := by
  simp [Ctx.need, h]

theorem needArgs_ok {Γ : Ctx} : ∀ {args : List Arg}, (∀ x, Arg.var x ∈ args → Γ.avail x = true) →
    Γ.needArgs args = .ok ()
  | [], _ => rfl
  | .var x :: as, h => by
    simp only [Ctx.needArgs]
    exact except_bind_of_ok (need_ok (h x List.mem_cons_self) _)
      (needArgs_ok (fun y hy => h y (List.mem_cons_of_mem _ hy)))
  | .lit _ :: as, h => needArgs_ok (args := as) (fun y hy => h y (List.mem_cons_of_mem _ hy))
  | .erased :: as, h => needArgs_ok (args := as) (fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem needCaptured_ok {Γ : Ctx} {j : Fir.JoinId} : ∀ {cs : List Var},
    (∀ c, c ∈ cs → Γ.avail c = true) → Γ.needCaptured j cs = .ok ()
  | [], _ => rfl
  | c :: cs, h => by
    simp only [Ctx.needCaptured]
    exact except_bind_of_ok (need_ok (h c List.mem_cons_self) _)
      (needCaptured_ok (fun y hy => h y (List.mem_cons_of_mem _ hy)))

theorem nodupFrom_of : ∀ {seen : Src.NatSet} {xs : List Var}, xs.Nodup →
    (∀ y, y ∈ xs → seen.contains y = false) → nodupFrom seen xs = true
  | _, [], _, _ => rfl
  | seen, x :: xs, hn, hs => by
    rw [List.nodup_cons] at hn
    simp only [nodupFrom, hs x List.mem_cons_self, Bool.not_false, Bool.true_and]
    apply nodupFrom_of hn.2
    intro y hy
    have hne : y ≠ x := fun he => hn.1 (he ▸ hy)
    simp only [Src.NatSet.insert, Src.NatMap.contains, Src.NatMap.get?_insert, hne, ↓reduceIte]
    simpa [Src.NatMap.contains] using hs y (List.mem_cons_of_mem _ hy)

theorem primImmArgs_eq (op : Lam.Prim) (n : Nat) : primImmArgs op n = List.replicate n true := by
  cases op <;> rfl

theorem shape_addOwn {Γ : Ctx} {I : Var → Bool} {t : Var → Nat} {P : Var → Prop}
    (h : Shape Γ I t P) {x : Var} (hx : I x = false) :
    Shape (Γ.addOwn x 1) I (fun y => if y = x then t y + 1 else t y) (fun y => P y ∨ y = x) := by
  obtain ⟨toks, htok⟩ := h.toks
  refine ⟨fun y => by simpa using h.imm y, fun y => ?_, fun y => by simpa using h.brw y,
    ⟨_, htok.addOwn x⟩, fun y hy => ?_, fun y hy => ?_⟩
  · rw [Ctx.tokens_addOwn]; split <;> (rename_i he; first | (subst he; rw [h.tokens]) | rw [h.tokens])
  · have hne : y ≠ x := by intro he; subst he; rw [hx] at hy; cases hy
    simp [hne, h.immZero y hy]
  · rw [Ctx.ownHas_addOwn] at hy
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hy
    rcases hy with hy | hy
    · exact Or.inr hy
    · exact Or.inl (h.own y hy)

theorem shape_avail {Γ : Ctx} {I : Var → Bool} {t : Var → Nat} {P : Var → Prop}
    (h : Shape Γ I t P) {x : Var} (hx : I x = true ∨ 0 < t x) : Γ.avail x = true := by
  rcases hx with hx | hx
  · simp [Ctx.avail_eq, h.imm, hx]
  · simp [Ctx.avail_eq, h.tokens, hx]

theorem shape_unknown {Γ : Ctx} {I : Var → Bool} {t : Var → Nat} {live : List Var}
    (h : Shape Γ I t (· ∈ live)) {x : Var} (hx : x ∉ live) (hi : I x = false) :
    Γ.known x = false := by
  have ho : Γ.own.contains x = false := by
    cases hc : Γ.own.contains x
    · rfl
    · exact absurd (h.own x hc) hx
  simp [Ctx.known_eq, h.imm, hi, ho, h.brw]

/-! ## Binding a fresh variable, in the canonical shape -/

section
variable {Γ Γ₂ : Ctx} {Δ : JCtx} {live : List Var} {joins : Joins} {imm : List Var}
  {arities : JoinArities} {x : Var} {I₂ : Var → Bool}

theorem canon_bindImm (h : Canon Γ Δ live joins imm arities) (hx : x ∉ live)
    (h₂ : Shape Γ₂ I₂ (fun z => if z ∈ live ∧ I₂ z = false then 1 else 0) (· ∈ live))
    (hI : ∀ z, I₂ z = true → z ∈ live) (imm' : List Var)
    (himm : ∀ z, z ∈ imm' → I₂ z = true ∨ z = x) :
    Canon (Γ₂.setImm x) Δ (live ++ [x]) joins imm' arities := by
  have hs := shape_setImm h₂ x
  have hi : ∀ z, (Γ₂.setImm x).isImm z = (decide (z = x) || I₂ z) := hs.imm
  refine ⟨hs.canon (fun z => ?_) (fun z hz => List.mem_append_left _ hz), fun z hz => ?_,
    fun z hz => ?_, h.jctx, fun j C hj => (h.capIn j C hj).trans (List.sublist_append_left _ _),
    h.arity, fresh_nodup_append h.nodup (by simp [fresh, hx])⟩
  · by_cases he : z = x
    · subst he; simp
    · simp [he]
  · rw [hi]; rcases himm z hz with h' | h' <;> simp [h']
  · rw [hi] at hz
    by_cases he : z = x
    · subst he; exact List.mem_append_right _ (List.mem_singleton_self _)
    · simp only [he, decide_false, Bool.false_or] at hz
      exact List.mem_append_left _ (hI z hz)

theorem canon_bindOwn (h : Canon Γ Δ live joins imm arities) (hx : x ∉ live)
    (h₂ : Shape Γ₂ I₂ (fun z => if z ∈ live ∧ I₂ z = false then 1 else 0) (· ∈ live))
    (hI : ∀ z, I₂ z = true → z ∈ live) (imm' : List Var) (himm : ∀ z, z ∈ imm' → I₂ z = true) :
    Canon (Γ₂.addOwn x 1) Δ (live ++ [x]) joins imm' arities := by
  have hx₂ : I₂ x = false := by
    cases hc : I₂ x
    · rfl
    · exact absurd (hI x hc) hx
  have hs := shape_addOwn h₂ hx₂
  have hi : ∀ z, (Γ₂.addOwn x 1).isImm z = I₂ z := hs.imm
  refine ⟨hs.canon (fun z => ?_) (fun z hz => ?_), fun z hz => ?_, fun z hz => ?_, h.jctx,
    fun j C hj => (h.capIn j C hj).trans (List.sublist_append_left _ _), h.arity,
    fresh_nodup_append h.nodup (by simp [fresh, hx])⟩
  · by_cases he : z = x
    · subst he; simp [hx, hx₂]
    · simp [he]
  · rcases hz with hz | hz
    · exact List.mem_append_left _ hz
    · subst hz; exact List.mem_append_right _ (List.mem_singleton_self _)
  · rw [hi]; exact himm z hz
  · rw [hi] at hz; exact List.mem_append_left _ (hI z hz)

end

end IxCC.Own.Plain
