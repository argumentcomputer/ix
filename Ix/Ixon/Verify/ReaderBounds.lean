/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Ixon.Bounded.Size
import Ix.Ixon.Verify.BoundedConstant

/-! # Structural bounds from production-reader byte consumption

These proofs concern the actual readers on arbitrary successful input,
including noncanonical spellings and nonzero starting cursors. No parser
implementation is replaced, and no decoded-tree traversal is introduced.
Two structural units per consumed byte cover telescope-compressed expression
constructors and universe-index slots. Universe successor expansion uses its
separate explicit node budget.
-/

namespace Ix.Ixon.Verify.ReaderBounds

open _root_.Ixon

/-- A successful read preserves the buffer, advances within it, and obtains
at most two structural units from each byte consumed. -/
structure Span (start finish : GetState) (units : Nat) : Prop where
  bytes : finish.bytes = start.bytes
  monotone : start.idx ≤ finish.idx
  within : finish.idx ≤ start.bytes.size
  bound : units + 2 * start.idx ≤ 2 * finish.idx

theorem Span.valid {start finish : GetState} {units : Nat} (h : Span start finish units) :
    finish.idx ≤ finish.bytes.size := by simpa [h.bytes] using h.within

theorem Span.refl (state : GetState) (valid : state.idx ≤ state.bytes.size) : Span state state 0 :=
  ⟨rfl, Nat.le_refl _, valid, by omega⟩

theorem Span.weaken {start finish : GetState} {units fewer : Nat}
    (h : Span start finish units) (le : fewer ≤ units) : Span start finish fewer :=
  ⟨h.bytes, h.monotone, h.within, by have := h.bound; omega⟩

theorem Span.trans {start middle finish : GetState} {first second : Nat}
    (left : Span start middle first) (right : Span middle finish second) :
    Span start finish (first + second) :=
  ⟨right.bytes.trans left.bytes, Nat.le_trans left.monotone right.monotone,
    by simpa [left.bytes] using right.within,
    by have := left.bound; have := right.bound; omega⟩

theorem Span.units_le {start finish : GetState} {units : Nat} (h : Span start finish units) :
    units ≤ 2 * (finish.idx - start.idx) := by
  have := h.monotone
  have := h.bound
  omega

/-- A bound on every successful execution from a valid cursor. -/
def ReaderBound (reader : GetM α) (units : α → Nat) : Prop :=
  ∀ start finish value, start.idx ≤ start.bytes.size →
    reader start = .ok value finish → Span start finish (units value)

theorem ReaderBound.weaken {reader : GetM α} {units : α → Nat} (bound : ReaderBound reader units)
    (cost : α → Nat) (le : ∀ value, cost value ≤ units value) : ReaderBound reader cost :=
  fun _ _ value valid read => (bound _ _ _ valid read).weaken (le value)

theorem pure_bound (value : α) : ReaderBound (pure value) (fun _ => 0) := by
  intro start finish output valid read
  cases read
  exact Span.refl start valid

theorem throw_bound (reason : String) (units : α → Nat) :
    ReaderBound (throw reason : GetM α) units := by
  intro start finish output valid read
  cases read

theorem bind_ok {reader : GetM α} {next : α → GetM β} {start finish : GetState} {value : β} :
    (reader >>= next) start = .ok value finish ↔
      ∃ head middle, reader start = .ok head middle ∧ next head middle = .ok value finish := by
  cases read : reader start with
  | error reason state => simp [bind, EStateM.bind, read]
  | ok head middle =>
    simp only [bind, EStateM.bind, read]
    constructor
    · intro tail
      exact ⟨head, middle, rfl, tail⟩
    · rintro ⟨head', middle', same, tail⟩
      cases same
      exact tail

theorem ReaderBound.map {reader : GetM α} {units : α → Nat} (h : ReaderBound reader units)
    (f : α → β) (cost : β → Nat) (le : ∀ a, cost (f a) ≤ units a) :
    ReaderBound (f <$> reader) cost := by
  intro start finish value valid read
  change EStateM.map f reader start = _ at read
  cases parsed : reader start with
  | error reason state => simp [EStateM.map, parsed] at read
  | ok output state =>
    simp only [EStateM.map, parsed, EStateM.Result.ok.injEq] at read
    rcases read with ⟨rfl, rfl⟩
    exact (h _ _ _ valid parsed).weaken (le output)

theorem ReaderBound.bind {reader : GetM α} {next : α → GetM β}
    {leftUnits : α → Nat} {rightUnits : α → β → Nat}
    (left : ReaderBound reader leftUnits) (right : ∀ a, ReaderBound (next a) (rightUnits a))
    (cost : β → Nat) (le : ∀ a b, cost b ≤ leftUnits a + rightUnits a b) :
    ReaderBound (reader >>= next) cost := by
  intro start finish value valid read
  obtain ⟨head, middle, first, second⟩ := bind_ok.mp read
  have firstSpan := left _ _ _ valid first
  have secondSpan := right head _ _ _ firstSpan.valid second
  exact (firstSpan.trans secondSpan).weaken (le head value)

theorem ReaderBound.skip {reader : GetM α} {next : α → GetM β}
    {leftUnits : α → Nat} {units : β → Nat}
    (left : ReaderBound reader leftUnits) (right : ∀ a, ReaderBound (next a) units) :
    ReaderBound (reader >>= next) units :=
  left.bind right _ (fun _ _ => by omega)

theorem ReaderBound.bind_map {reader : GetM α} {next : α → GetM β}
    {leftUnits : α → Nat} {rightUnits : α → β → Nat}
    (left : ReaderBound reader leftUnits) (right : ∀ a, ReaderBound (next a) (rightUnits a))
    (f : α → β → γ) (cost : γ → Nat) (le : ∀ a b, cost (f a b) ≤ leftUnits a + rightUnits a b) :
    ReaderBound (do let a ← reader; let b ← next a; pure (f a b)) cost := by
  intro start finish value valid read
  obtain ⟨head, middle, first, read⟩ := bind_ok.mp read
  have firstSpan := left _ _ _ valid first
  obtain ⟨tail, final, second, result⟩ := bind_ok.mp read
  have secondSpan := right head _ _ _ firstSpan.valid second
  cases result
  exact (firstSpan.trans secondSpan).weaken (le head tail)

theorem getU8_bound : ReaderBound getU8 (fun _ => 2) := by
  intro start finish value _ read
  unfold getU8 at read
  change (EStateM.bind EStateM.get _) start = _ at read
  simp only [EStateM.bind, EStateM.get] at read
  split at read
  next fits =>
    change (EStateM.bind (EStateM.set _) _) start = _ at read
    simp only [EStateM.bind, EStateM.set] at read
    change EStateM.Result.ok _ _ = .ok value finish at read
    cases read
    exact ⟨rfl, by simp, by dsimp; omega, by simp; omega⟩
  next => cases read

theorem getBytes_bound (count : Nat) : ReaderBound (getBytes count) (fun _ => 2 * count) := by
  intro start finish value _ read
  unfold getBytes at read
  change (EStateM.bind EStateM.get _) start = _ at read
  simp only [EStateM.bind, EStateM.get] at read
  split at read
  next fits =>
    change (EStateM.bind (EStateM.set _) _) start = _ at read
    simp only [EStateM.bind, EStateM.set] at read
    change EStateM.Result.ok _ _ = .ok value finish at read
    cases read
    exact ⟨rfl, by simp, fits, by simp; omega⟩
  next => cases read

theorem getU64TrimmedLEAux_bound (count : Nat) :
    ReaderBound (getU64TrimmedLEAux count) (fun _ => 2 * count) := by
  induction count with
  | zero => exact pure_bound 0
  | succ count ih =>
    unfold getU64TrimmedLEAux
    apply getU8_bound.bind (rightUnits := fun _ _ => 2 * count)
      (fun low => ?_) _ (fun _ _ => by omega)
    exact ih.bind (fun high => pure_bound (low.toUInt64 ||| (high <<< 8)))
      (fun _ => 2 * count) (fun _ _ => by omega)

theorem getU64TrimmedLE_bound (count : Nat) :
    ReaderBound (getU64TrimmedLE count) (fun _ => 2 * count) := by
  unfold getU64TrimmedLE
  split
  · exact throw_bound _ _
  · simpa using getU64TrimmedLEAux_bound count

/-- Ixon v3's canonical-width check: a rejected integer stops the read. -/
theorem reject_bound (bad : Bool) (reason : String) (value : α) :
    ReaderBound (if bad = true then (throw reason : GetM PUnit) >>= (fun _ => pure value)
      else pure value) (fun _ => 0) := by
  cases bad
  · exact pure_bound value
  · exact (throw_bound reason (fun _ => 0)).bind (fun _ => pure_bound value) (fun _ => 0)
      (fun _ _ => by omega)

/-- `checkCount` reads the cursor and consumes nothing. -/
theorem checkCount_bound (count : UInt64) (minBytes : Nat) :
    ReaderBound (checkCount count minBytes) (fun _ => 0) := by
  intro start finish value valid read
  unfold checkCount at read
  change (EStateM.bind EStateM.get _) start = _ at read
  simp only [EStateM.bind, EStateM.get] at read
  split at read
  · cases read
  · cases read
    exact Span.refl start valid

theorem getBinderContract_bound : ReaderBound getBinderContract (fun _ => 2) := by
  intro start finish value valid read
  unfold getBinderContract at read
  obtain ⟨bits, middle, bitsRead, read⟩ := bind_ok.mp read
  have bitsSpan := getU8_bound _ _ _ valid bitsRead
  cases decoded : BinderContract.ofBits? bits with
  | none => simp only [decoded] at read; cases read
  | some contract =>
    simp only [decoded] at read
    cases read
    exact bitsSpan

theorem getTag0_bound : ReaderBound getTag0 (fun _ => 2) := by
  unfold getTag0
  apply getU8_bound.bind (rightUnits := fun _ _ => 0) (fun byte => ?_) _ (fun _ _ => by omega)
  by_cases large : (byte &&& 128 != 0) = true
  · simp only [large, ite_true]
    exact (getU64TrimmedLE_bound _).bind (fun value => reject_bound _ _ (Tag0.mk value))
      (fun _ => 0) (fun _ _ => by omega)
  · simp only [large]
    exact (pure_bound _).bind (fun value => pure_bound (Tag0.mk value))
      (fun _ => 0) (fun _ _ => by omega)

theorem getTag2_bound : ReaderBound getTag2 (fun _ => 2) := by
  unfold getTag2
  apply getU8_bound.bind (rightUnits := fun _ _ => 0) (fun byte => ?_) _ (fun _ _ => by omega)
  by_cases large : (byte &&& 32 != 0) = true
  · simp only [large, ite_true]
    exact (getU64TrimmedLE_bound _).bind (fun value => reject_bound _ _ (Tag2.mk _ value))
      (fun _ => 0) (fun _ _ => by omega)
  · simp only [large]
    exact (pure_bound _).bind (fun value => pure_bound (Tag2.mk _ value))
      (fun _ => 0) (fun _ _ => by omega)

theorem getTag4_bound : ReaderBound getTag4 (fun _ => 2) := by
  unfold getTag4
  apply getU8_bound.bind (rightUnits := fun _ _ => 0) (fun byte => ?_) _ (fun _ _ => by omega)
  by_cases large : (byte &&& 8 != 0) = true
  · simp only [large, ite_true]
    exact (getU64TrimmedLE_bound _).bind (fun value => reject_bound _ _ (Tag4.mk _ value))
      (fun _ => 0) (fun _ _ => by omega)
  · simp only [large]
    exact (pure_bound _).bind (fun value => pure_bound (Tag4.mk _ value))
      (fun _ => 0) (fun _ _ => by omega)

theorem address_bound : ReaderBound (Serialize.get : GetM Address) (fun _ => 64) :=
  (getBytes_bound 32).map Address.mk _ (fun _ => Nat.le_refl _)

theorem resourceSize_pos (expr : Expr) : 0 < expr.resourceSize := by
  cases expr <;> simp [Expr.resourceSize] <;> omega

theorem getTag0Sizes_spec (count : Nat) (start finish : GetState) (values : List UInt64)
    (valid : start.idx ≤ start.bytes.size)
    (read : getTag0Sizes count start = .ok values finish) :
    values.length = count ∧ Span start finish (2 * count) := by
  induction count generalizing start finish values with
  | zero =>
    cases read
    exact ⟨rfl, Span.refl _ valid⟩
  | succ count ih =>
    rw [getTag0Sizes] at read
    obtain ⟨tag, middle, tagRead, read⟩ := bind_ok.mp read
    have tagSpan := getTag0_bound _ _ _ valid tagRead
    obtain ⟨tail, final, tailRead, result⟩ := bind_ok.mp read
    obtain ⟨length, tailSpan⟩ := ih _ _ _ tagSpan.valid tailRead
    change EStateM.Result.ok _ _ = .ok values finish at result
    cases result
    exact ⟨by simp [length], by simpa [Nat.mul_add, Nat.add_comm] using tagSpan.trans tailSpan⟩

theorem getArray_spec (reader : GetM α) (units : α → Nat) (bound : ReaderBound reader units)
    (count : Nat) (start finish : GetState) (values : Array α)
    (valid : start.idx ≤ start.bytes.size) (read : getArray reader count start = .ok values finish) :
    values.size = count ∧ Span start finish (values.toList.map units).sum := by
  induction count generalizing start finish values with
  | zero =>
    rw [BoundedConstant.getArray_zero] at read
    cases read
    exact ⟨rfl, Span.refl _ valid⟩
  | succ count ih =>
    rw [BoundedConstant.getArray_succ] at read
    obtain ⟨head, middle, headRead, read⟩ := bind_ok.mp read
    have headSpan := bound _ _ _ valid headRead
    obtain ⟨tail, final, tailRead, result⟩ := bind_ok.mp read
    obtain ⟨length, tailSpan⟩ := ih _ _ _ headSpan.valid tailRead
    change EStateM.Result.ok _ _ = .ok values finish at result
    cases result
    exact ⟨by simp [length, Nat.add_comm], by simpa using headSpan.trans tailSpan⟩

theorem sum_const (value : Nat) (values : List α) :
    (values.map (fun _ => value)).sum = value * values.length := by
  induction values with
  | nil => simp
  | cons _ _ ih => simp [ih, Nat.mul_add, Nat.add_comm]

theorem getArray_bound (reader : GetM α) (units : α → Nat) (bound : ReaderBound reader units)
    (count : Nat) : ReaderBound (getArray reader count) (fun values => (values.toList.map units).sum) :=
  fun _ _ _ valid read => (getArray_spec _ _ bound _ _ _ _ valid read).2

theorem getArray_count_bound (reader : GetM α) (bound : ReaderBound reader (fun _ => 2))
    (count : Nat) : ReaderBound (getArray reader count) (fun _ => 2 * count) := by
  intro start finish values valid read
  obtain ⟨length, span⟩ := getArray_spec _ _ bound _ _ _ _ valid read
  simpa [sum_const, length] using span

/-- A failing counted-array read consists of a successful prefix followed
by the first failing element read. The declared count cannot force further
iterations after failure. -/
theorem getArray_error_prefix (reader : GetM α) (count : Nat) (start finish : GetState)
    (reason : String) (read : getArray reader count start = .error reason finish) :
    ∃ parsed values middle, parsed < count ∧ values.size = parsed ∧
      getArray reader parsed start = .ok values middle ∧ reader middle = .error reason finish := by
  induction count generalizing start finish with
  | zero => rw [BoundedConstant.getArray_zero] at read; cases read
  | succ count ih =>
    rw [BoundedConstant.getArray_succ] at read
    cases headRead : reader start with
    | error error state =>
      simp only [bind, EStateM.bind, headRead] at read
      cases read
      exact ⟨0, #[], start, by omega, rfl,
        by simp [BoundedConstant.getArray_zero, pure, EStateM.pure], headRead⟩
    | ok head middle =>
      simp only [bind, EStateM.bind, headRead] at read
      cases tailRead : getArray reader count middle with
      | ok tail state => simp [tailRead, pure, EStateM.pure] at read
      | error error state =>
        simp only [tailRead] at read
        cases read
        obtain ⟨parsed, values, final, fewer, length, prefixRead, failed⟩ := ih _ _ tailRead
        refine ⟨parsed + 1, #[head] ++ values, final, by omega, by simp [length, Nat.add_comm], ?_, failed⟩
        simp [BoundedConstant.getArray_succ, bind, EStateM.bind, headRead, prefixRead, pure, EStateM.pure]

/-- When each successful element consumes at least one byte, the number of
successful iterations before failure is bounded by the available payload,
even if the wire count is `UInt64.max`. The final failing element is one
additional invocation of the element reader. -/
theorem getArray_error_work (reader : GetM α) (bound : ReaderBound reader (fun _ => 2))
    (count : Nat) (start finish : GetState) (reason : String)
    (valid : start.idx ≤ start.bytes.size)
    (read : getArray reader count start = .error reason finish) :
    ∃ parsed values middle, parsed < count ∧ parsed ≤ start.bytes.size - start.idx ∧
      values.size = parsed ∧ getArray reader parsed start = .ok values middle ∧
      reader middle = .error reason finish := by
  obtain ⟨parsed, values, middle, fewer, length, prefixRead, failed⟩ :=
    getArray_error_prefix _ _ _ _ _ read
  have span := getArray_count_bound _ bound _ _ _ _ valid prefixRead
  have work : 2 * parsed + 2 * start.idx ≤ 2 * middle.idx := span.bound
  have := span.within
  exact ⟨parsed, values, middle, fewer, by omega, length, prefixRead, failed⟩

theorem getArray_tooMany (reader : GetM α) (bound : ReaderBound reader (fun _ => 2))
    (count : Nat) (start : GetState) (valid : start.idx ≤ start.bytes.size)
    (tooMany : start.bytes.size - start.idx < count) (values : Array α) (finish : GetState) :
    getArray reader count start ≠ .ok values finish := by
  intro read
  have span := getArray_count_bound _ bound _ _ _ _ valid read
  have work : 2 * count + 2 * start.idx ≤ 2 * finish.idx := span.bound
  have := span.within
  omega

theorem getExprAppArgs_spec (recur : GetM Expr)
    (bound : ReaderBound recur (fun e => e.resourceSize + 1))
    (count : Nat) (base : Expr) (start finish : GetState) (value : Expr)
    (valid : start.idx ≤ start.bytes.size)
    (read : getExprAppArgs recur count base start = .ok value finish) :
    base.resourceSize ≤ value.resourceSize ∧
      Span start finish (value.resourceSize - base.resourceSize) := by
  induction count generalizing base start finish value with
  | zero =>
    cases read
    exact ⟨Nat.le_refl _, by simpa using Span.refl start valid⟩
  | succ count ih =>
    rw [getExprAppArgs] at read
    obtain ⟨arg, middle, argRead, tailRead⟩ := bind_ok.mp read
    have argSpan := bound _ _ _ valid argRead
    obtain ⟨larger, tailSpan⟩ := ih _ _ _ _ argSpan.valid tailRead
    simp only [Expr.resourceSize] at larger tailSpan
    exact ⟨by omega, (argSpan.trans tailSpan).weaken (by dsimp; omega)⟩

def lamUnits (binders : List (BinderContract × Expr)) : Nat :=
  (binders.map (fun binder => binder.2.resourceSize + 1)).sum

def allUnits (binders : List (BinderContract × ValueContract × Expr)) : Nat :=
  (binders.map (fun binder => binder.2.2.resourceSize + 1)).sum

theorem lamUnits_fold (binders : List (BinderContract × Expr)) (body : Expr) :
    (binders.foldr (fun (uses, type) rest => .lam uses type rest) body).resourceSize =
      lamUnits binders + body.resourceSize := by
  induction binders with
  | nil => simp [lamUnits]
  | cons head tail ih =>
    simp only [List.foldr_cons, Expr.resourceSize, ih, lamUnits, List.map_cons, List.sum_cons]
    omega

theorem allUnits_fold (binders : List (BinderContract × ValueContract × Expr)) (body : Expr) :
    (binders.foldr (fun (uses, owned, type) rest => .all uses owned type rest) body).resourceSize =
      allUnits binders + body.resourceSize := by
  induction binders with
  | nil => simp [allUnits]
  | cons head tail ih =>
    rcases head with ⟨uses, owned, type⟩
    simp [Expr.resourceSize, ih, allUnits, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem getExprLamBinders_bound (recur : GetM Expr)
    (bound : ReaderBound recur (fun e => e.resourceSize + 1)) (count : Nat) :
    ReaderBound (getExprLamBinders recur count) lamUnits := by
  induction count with
  | zero =>
    intro start finish values valid read
    cases read
    exact Span.refl start valid
  | succ count ih =>
    intro start finish values valid read
    rw [getExprLamBinders] at read
    obtain ⟨contract, modeState, modeRead, read⟩ := bind_ok.mp read
    have modeSpan := getBinderContract_bound _ _ _ valid modeRead
    obtain ⟨type, typeState, typeRead, read⟩ := bind_ok.mp read
    have typeSpan := bound _ _ _ modeSpan.valid typeRead
    obtain ⟨tail, final, tailRead, result⟩ := bind_ok.mp read
    have tailSpan := ih _ _ _ typeSpan.valid tailRead
    change EStateM.Result.ok _ _ = .ok values finish at result
    cases result
    exact ((modeSpan.trans typeSpan).trans tailSpan).weaken (by simp [lamUnits])

theorem getExprAllBinders_bound (recur : GetM Expr)
    (bound : ReaderBound recur (fun e => e.resourceSize + 1)) (count : Nat) :
    ReaderBound (getExprAllBinders recur count) allUnits := by
  induction count with
  | zero =>
    intro start finish values valid read
    cases read
    exact Span.refl start valid
  | succ count ih =>
    intro start finish values valid read
    rw [getExprAllBinders] at read
    obtain ⟨bits, modeState, modeRead, read⟩ := bind_ok.mp read
    have modeSpan := getU8_bound _ _ _ valid modeRead
    cases decoded : unpackAllContract? bits with
    | none => simp only [decoded] at read; cases read
    | some contracts =>
      rcases contracts with ⟨contract, result⟩
      simp only [decoded] at read
      obtain ⟨type, typeState, typeRead, read⟩ := bind_ok.mp read
      have typeSpan := bound _ _ _ modeSpan.valid typeRead
      obtain ⟨tail, final, tailRead, result⟩ := bind_ok.mp read
      have tailSpan := ih _ _ _ typeSpan.valid tailRead
      change EStateM.Result.ok _ _ = .ok values finish at result
      cases result
      exact ((modeSpan.trans typeSpan).trans tailSpan).weaken (by simp [allUnits])

theorem getExprFromTag_bound (recur : GetM Expr)
    (bound : ReaderBound recur (fun e => e.resourceSize + 1)) (tag : Tag4) :
    ReaderBound (getExprFromTag recur tag) (fun e => e.resourceSize - 1) := by
  intro start finish value valid read
  by_cases sortTag : tag.flag = 0
  · simp only [getExprFromTag, sortTag] at read
    cases read
    exact Span.refl start valid
  by_cases varTag : tag.flag = 1
  · simp only [getExprFromTag, varTag] at read
    cases read
    exact Span.refl start valid
  by_cases refTag : tag.flag = 2
  · simp only [getExprFromTag, refTag] at read
    obtain ⟨index, middle, indexRead, read⟩ := bind_ok.mp read
    have indexSpan := getTag0_bound _ _ _ valid indexRead
    obtain ⟨_, checked, checkRead, read⟩ := bind_ok.mp read
    have checkSpan := checkCount_bound _ _ _ _ _ indexSpan.valid checkRead
    obtain ⟨levels, final, levelsRead, result⟩ := bind_ok.mp read
    obtain ⟨length, levelsSpan⟩ := getTag0Sizes_spec _ _ _ _ checkSpan.valid levelsRead
    change EStateM.Result.ok _ _ = .ok value finish at result
    cases result
    exact ((indexSpan.trans checkSpan).trans levelsSpan).weaken
      (by simp [Expr.resourceSize, length]; omega)
  by_cases recurTag : tag.flag = 3
  · simp only [getExprFromTag, recurTag] at read
    obtain ⟨index, middle, indexRead, read⟩ := bind_ok.mp read
    have indexSpan := getTag0_bound _ _ _ valid indexRead
    obtain ⟨_, checked, checkRead, read⟩ := bind_ok.mp read
    have checkSpan := checkCount_bound _ _ _ _ _ indexSpan.valid checkRead
    obtain ⟨levels, final, levelsRead, result⟩ := bind_ok.mp read
    obtain ⟨length, levelsSpan⟩ := getTag0Sizes_spec _ _ _ _ checkSpan.valid levelsRead
    change EStateM.Result.ok _ _ = .ok value finish at result
    cases result
    exact ((indexSpan.trans checkSpan).trans levelsSpan).weaken
      (by simp [Expr.resourceSize, length]; omega)
  by_cases projectionTag : tag.flag = 4
  · simp only [getExprFromTag, projectionTag] at read
    obtain ⟨index, middle, indexRead, read⟩ := bind_ok.mp read
    have indexSpan := getTag0_bound _ _ _ valid indexRead
    obtain ⟨inner, final, innerRead, result⟩ := bind_ok.mp read
    have innerSpan := bound _ _ _ indexSpan.valid innerRead
    change EStateM.Result.ok _ _ = .ok value finish at result
    cases result
    exact (indexSpan.trans innerSpan).weaken (by simp [Expr.resourceSize]; omega)
  by_cases stringTag : tag.flag = 5
  · simp only [getExprFromTag, stringTag] at read
    cases read
    exact Span.refl start valid
  by_cases naturalTag : tag.flag = 6
  · simp only [getExprFromTag, naturalTag] at read
    cases read
    exact Span.refl start valid
  by_cases appTag : tag.flag = 7
  · simp only [getExprFromTag, appTag] at read
    by_cases empty : (tag.size == 0) = true
    · simp only [ite_eq_left empty] at read
      cases read
    · simp only [ite_eq_right empty] at read
      obtain ⟨_, checked, checkRead, read⟩ := bind_ok.mp read
      have checkSpan := checkCount_bound _ _ _ _ _ valid checkRead
      obtain ⟨base, middle, baseRead, read⟩ := bind_ok.mp read
      have baseSpan := bound _ _ _ checkSpan.valid baseRead
      have argsRead : getExprAppArgs recur tag.size.toNat base middle = .ok value finish := by
        cases base <;> first | exact read | cases read
      obtain ⟨larger, argsSpan⟩ := getExprAppArgs_spec _ bound _ _ _ _ _ baseSpan.valid argsRead
      exact ((checkSpan.trans baseSpan).trans argsSpan).weaken (by dsimp; omega)
  by_cases lamTag : tag.flag = 8
  · simp only [getExprFromTag, lamTag] at read
    by_cases empty : (tag.size == 0) = true
    · simp only [ite_eq_left empty] at read
      cases read
    · simp only [ite_eq_right empty] at read
      obtain ⟨_, checked, checkRead, read⟩ := bind_ok.mp read
      have checkSpan := checkCount_bound _ _ _ _ _ valid checkRead
      obtain ⟨binders, middle, bindersRead, read⟩ := bind_ok.mp read
      have bindersSpan := getExprLamBinders_bound _ bound _ _ _ _ checkSpan.valid bindersRead
      obtain ⟨body, final, bodyRead, result⟩ := bind_ok.mp read
      have bodySpan := bound _ _ _ bindersSpan.valid bodyRead
      have same : value = binders.foldr (fun (uses, type) rest => .lam uses type rest) body ∧
          finish = final := by
        cases body <;> cases result <;> exact ⟨rfl, rfl⟩
      rcases same with ⟨rfl, rfl⟩
      exact ((checkSpan.trans bindersSpan).trans bodySpan).weaken
        (by dsimp only; rw [lamUnits_fold]; omega)
  by_cases allTag : tag.flag = 9
  · simp only [getExprFromTag, allTag] at read
    by_cases empty : (tag.size == 0) = true
    · simp only [ite_eq_left empty] at read
      cases read
    · simp only [ite_eq_right empty] at read
      obtain ⟨_, checked, checkRead, read⟩ := bind_ok.mp read
      have checkSpan := checkCount_bound _ _ _ _ _ valid checkRead
      obtain ⟨binders, middle, bindersRead, read⟩ := bind_ok.mp read
      have bindersSpan := getExprAllBinders_bound _ bound _ _ _ _ checkSpan.valid bindersRead
      obtain ⟨body, final, bodyRead, result⟩ := bind_ok.mp read
      have bodySpan := bound _ _ _ bindersSpan.valid bodyRead
      have same : value = binders.foldr (fun (uses, owned, type) rest => .all uses owned type rest) body ∧
          finish = final := by
        cases body <;> cases result <;> exact ⟨rfl, rfl⟩
      rcases same with ⟨rfl, rfl⟩
      exact ((checkSpan.trans bindersSpan).trans bodySpan).weaken
        (by dsimp only; rw [allUnits_fold]; omega)
  by_cases letTag : tag.flag = 10
  · simp only [getExprFromTag, letTag] at read
    by_cases badFlags : tag.size > 3
    · simp only [ite_eq_left badFlags] at read
      cases read
    · simp only [ite_eq_right badFlags] at read
      obtain ⟨binder, binderState, binderRead, read⟩ := bind_ok.mp read
      have binderSpan := getBinderContract_bound _ _ _ valid binderRead
      cases decoded : LetContract.ofFlags? tag.size binder with
      | none => simp only [decoded] at read; cases read
      | some contract =>
        simp only [decoded] at read
        obtain ⟨type, typeState, typeRead, read⟩ := bind_ok.mp read
        have typeSpan := bound _ _ _ binderSpan.valid typeRead
        obtain ⟨inner, innerState, innerRead, read⟩ := bind_ok.mp read
        have innerSpan := bound _ _ _ typeSpan.valid innerRead
        obtain ⟨body, final, bodyRead, result⟩ := bind_ok.mp read
        have bodySpan := bound _ _ _ innerSpan.valid bodyRead
        change EStateM.Result.ok _ _ = .ok value finish at result
        cases result
        exact (((binderSpan.trans typeSpan).trans innerSpan).trans bodySpan).weaken
          (by simp [Expr.resourceSize]; omega)
  by_cases shareTag : tag.flag = 11
  · simp only [getExprFromTag, shareTag] at read
    cases read
    exact Span.refl start valid
  simp only [getExprFromTag] at read
  cases read

/-- Every successful production expression parse is linear in consumed bytes
in structural units, even for compressed telescopes and large index vectors.
The bound applies at the caller's actual fuel, without requiring canonical
bytes or a wire-well-formedness hypothesis. -/
theorem getExprFuel_bound (fuel : Nat) :
    ReaderBound (getExprFuel fuel) (fun expr => expr.resourceSize + 1) := by
  induction fuel with
  | zero => exact throw_bound _ _
  | succ fuel ih =>
    exact getTag4_bound.bind (fun tag => getExprFromTag_bound _ ih tag) _
      (fun _ expr => by have := resourceSize_pos expr; omega)

theorem getExpr_bound : ReaderBound getExpr (fun expr => expr.resourceSize + 1) := by
  intro start finish value valid read
  change getExprFuel (start.bytes.size - start.idx + 1) start = .ok value finish at read
  exact getExprFuel_bound _ _ _ _ valid read

theorem ReaderBound.runGetExact {reader : GetM α} {units : α → Nat}
    (bound : ReaderBound reader units) (bytes : ByteArray) (value : α)
    (read : runGetExact reader bytes = .ok value) : units value ≤ 2 * bytes.size := by
  unfold _root_.Ixon.runGetExact at read
  simp only [EStateM.run] at read
  cases parsed : reader { bytes := bytes } with
  | error reason state => simp [parsed] at read
  | ok output state =>
    simp only [parsed] at read
    split at read
    next consumed =>
      cases read
      have span := bound _ _ _ (Nat.zero_le _) parsed
      simpa [consumed] using span.bound
    next => cases read

theorem deExpr_resource_bound (bytes : ByteArray) (value : Expr)
    (read : deExpr bytes = .ok value) : value.resourceSize + 1 ≤ 2 * bytes.size :=
  getExpr_bound.runGetExact bytes value read

end Ix.Ixon.Verify.ReaderBounds
