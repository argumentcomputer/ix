/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Ixon.Verify.WorkTags

namespace Ix.Ixon.Verify.Work

open _root_.Ixon

/-! Expression accounting includes list cells and tuples, array materialization,
and telescope folds, in addition to byte/tag work. Collection readers retain
credit proportional to their actual successful output, never the wire's claimed
count. Failed children retain all earlier work and construct no pending suffix.

Four credits from each complete expression can pay a surrounding table or
telescope step. Sixteen units per consumed byte fund the grammar, including
noncanonical encodings and every error path. These are abstract parser units;
arithmetic bit complexity and runtime allocation behavior are not modeled.
-/

def tag0Sizes : Nat → M (List UInt64)
  | 0 => pure []
  | count + 1 => do
    let head ← tag0
    let tail ← tag0Sizes count
    charged 1 (pure (head.size :: tail))

def appArgs (recur : M Expr) : Nat → Expr → M Expr
  | 0, result => pure result
  | count + 1, result => do
    let arg ← recur
    charged 2 (appArgs recur count (.app result arg))

def lamBinders (recur : M Expr) : Nat → M (List (Uses × Expr))
  | 0 => pure []
  | count + 1 => do
    let mode ← u8
    let some uses := Uses.ofBits? mode
      | fail s!"getExpr: invalid lambda mode {mode}"
    let ty ← recur
    let tail ← lamBinders recur count
    charged 2 (pure ((uses, ty) :: tail))

def allBinders (recur : M Expr) : Nat → M (List (Uses × Owned × Expr))
  | 0 => pure []
  | count + 1 => do
    let mode ← u8
    if mode > 7 then
      fail s!"getExpr: invalid forall mode {mode}"
    else do
      let some uses := Uses.ofBits? (mode &&& 0x03)
        | fail s!"getExpr: invalid forall usage mode {mode}"
      let some owned := Owned.ofBits? ((mode >>> 2) &&& 0x01)
        | fail s!"getExpr: invalid forall ownership mode {mode}"
      let ty ← recur
      let tail ← allBinders recur count
      charged 3 (pure ((uses, owned, ty) :: tail))

def exprFromTag (recur : M Expr) (tag : Tag4) : M Expr := do
  match tag.flag with
  | 0x0 => charged 1 (pure (.sort tag.size))
  | 0x1 => charged 1 (pure (.var tag.size))
  | 0x2 => do
    let refIdx ← tag0
    let univIdxs ← tag0Sizes tag.size.toNat
    charged (2 * univIdxs.length + 1) (pure (.ref refIdx.size univIdxs.toArray))
  | 0x3 => do
    let recIdx ← tag0
    let univIdxs ← tag0Sizes tag.size.toNat
    charged (2 * univIdxs.length + 1) (pure (.recur recIdx.size univIdxs.toArray))
  | 0x4 => do
    let typeRefIdx ← tag0
    let val ← recur
    charged 1 (pure (.prj typeRefIdx.size tag.size val))
  | 0x5 => charged 1 (pure (.str tag.size))
  | 0x6 => charged 1 (pure (.nat tag.size))
  | 0x7 =>
    if tag.size == 0 then fail "getExpr: empty app spine"
    else do
      let base ← recur
      match base with
      | .app .. => fail "getExpr: non-canonical app base"
      | _ => appArgs recur tag.size.toNat base
  | 0x8 =>
    if tag.size == 0 then fail "getExpr: Lam with zero binders"
    else do
      let binders ← lamBinders recur tag.size.toNat
      let body ← recur
      match body with
      | .lam .. => fail "getExpr: non-canonical lam telescope"
      | _ =>
        charged (2 * binders.length)
          (pure (binders.foldr (fun (uses, ty) result => .lam uses ty result) body))
  | 0x9 =>
    if tag.size == 0 then fail "getExpr: All with zero binders"
    else do
      let binders ← allBinders recur tag.size.toNat
      let body ← recur
      match body with
      | .all .. => fail "getExpr: non-canonical all telescope"
      | _ =>
        charged (2 * binders.length)
          (pure (binders.foldr (fun (uses, owned, ty) result => .all uses owned ty result) body))
  | 0xA =>
    if tag.size > 1 then fail s!"getExpr: invalid letE nonDep {tag.size}"
    else do
      let ty ← recur
      let val ← recur
      let body ← recur
      charged 1 (pure (.letE (tag.size == 1) ty val body))
  | 0xB => charged 1 (pure (.share tag.size))
  | f => fail s!"getExpr: invalid flag {f}"

def exprFuel : Nat → M Expr
  | 0 => fail "getExpr: recursion budget exhausted"
  | fuel + 1 => bind tag4 (exprFromTag (exprFuel fuel))

def expr : M Expr := fun state => exprFuel (state.bytes.size - state.idx + 1) state

theorem tag0Sizes_erases (count : Nat) : Erases (tag0Sizes count) (getTag0Sizes count) := by
  induction count with
  | zero => exact pure_erases []
  | succ count ih =>
    unfold tag0Sizes getTag0Sizes
    exact tag0_erases.bind fun _ => ih.bind fun _ => (pure_erases _).charged 1

theorem appArgs_erases {recur : M Expr} {reader : GetM Expr} (same : Erases recur reader)
    (count : Nat) (base : Expr) : Erases (appArgs recur count base) (getExprAppArgs reader count base) := by
  induction count generalizing base with
  | zero => exact pure_erases base
  | succ count ih =>
    unfold appArgs getExprAppArgs
    exact same.bind fun _ => (ih _).charged 2

theorem lamBinders_erases {recur : M Expr} {reader : GetM Expr} (same : Erases recur reader)
    (count : Nat) : Erases (lamBinders recur count) (getExprLamBinders reader count) := by
  induction count with
  | zero => exact pure_erases []
  | succ count ih =>
    unfold lamBinders getExprLamBinders
    apply u8_erases.bind
    intro mode
    cases Uses.ofBits? mode with
    | none => exact fail_erases _
    | some uses => exact same.bind fun _ => ih.bind fun _ => (pure_erases _).charged 2

theorem allBinders_erases {recur : M Expr} {reader : GetM Expr} (same : Erases recur reader)
    (count : Nat) : Erases (allBinders recur count) (getExprAllBinders reader count) := by
  induction count with
  | zero => exact pure_erases []
  | succ count ih =>
    unfold allBinders getExprAllBinders
    apply u8_erases.bind
    intro mode
    split
    · exact fail_erases _
    · cases Uses.ofBits? (mode &&& 0x03) with
      | none => exact fail_erases _
      | some uses =>
        cases Owned.ofBits? ((mode >>> 2) &&& 0x01) with
        | none => exact fail_erases _
        | some owned => exact same.bind fun _ => ih.bind fun _ => (pure_erases _).charged 3

theorem tag0Sizes_bound (count : Nat) :
    Bound (tag0Sizes count) 16 0 (fun values => 2 * values.length) := by
  induction count with
  | zero => exact pure_bound 16 0 _ [] (Nat.le_refl _)
  | succ count ih =>
    unfold tag0Sizes
    apply (tag0_bound 16 (by decide)).bind
    intro head
    apply (ih.frame 14).bind
    intro tail
    apply charged_pure_bound
    simp only [List.length_cons]
    omega

theorem appArgs_bound {recur : M Expr} (bound : Bound recur 16 0 (fun _ => 4))
    (count : Nat) (base : Expr) : Bound (appArgs recur count base) 16 0 (fun _ => 0) := by
  induction count generalizing base with
  | zero => exact pure_bound 16 0 _ base (Nat.le_refl _)
  | succ count ih =>
    unfold appArgs
    apply bound.bind
    intro arg
    exact ((ih _).charged 2).weaken (by decide) (fun _ => Nat.le_refl _)

theorem lamBinders_bound {recur : M Expr} (bound : Bound recur 16 0 (fun _ => 4))
    (count : Nat) : Bound (lamBinders recur count) 16 0 (fun values => 2 * values.length) := by
  induction count with
  | zero => exact pure_bound 16 0 _ [] (Nat.le_refl _)
  | succ count ih =>
    unfold lamBinders
    apply (u8_bound 16 (by decide)).bind
    intro mode
    cases Uses.ofBits? mode with
    | none => exact fail_bound _ _ _ _
    | some uses =>
      apply (bound.frame 15).bind
      intro ty
      apply (ih.frame 19).bind
      intro tail
      apply charged_pure_bound
      simp only [List.length_cons]
      omega

theorem allBinders_bound {recur : M Expr} (bound : Bound recur 16 0 (fun _ => 4))
    (count : Nat) : Bound (allBinders recur count) 16 0 (fun values => 2 * values.length) := by
  induction count with
  | zero => exact pure_bound 16 0 _ [] (Nat.le_refl _)
  | succ count ih =>
    unfold allBinders
    apply (u8_bound 16 (by decide)).bind
    intro mode
    split
    · exact fail_bound _ _ _ _
    · cases Uses.ofBits? (mode &&& 0x03) with
      | none => exact fail_bound _ _ _ _
      | some uses =>
        cases Owned.ofBits? ((mode >>> 2) &&& 0x01) with
        | none => exact fail_bound _ _ _ _
        | some owned =>
          apply (bound.frame 15).bind
          intro ty
          apply (ih.frame 19).bind
          intro tail
          apply charged_pure_bound
          simp only [List.length_cons]
          omega

theorem exprFromTag_erases {recur : M Expr} {reader : GetM Expr}
    (same : Erases recur reader) (tag : Tag4) :
    Erases (exprFromTag recur tag) (getExprFromTag reader tag) := by
  unfold exprFromTag getExprFromTag
  split <;> simp_all only
  · exact (pure_erases _).charged 1
  · exact (pure_erases _).charged 1
  · exact tag0_erases.bind fun _ => (tag0Sizes_erases _).bind fun _ =>
      (pure_erases _).charged _
  · exact tag0_erases.bind fun _ => (tag0Sizes_erases _).bind fun _ =>
      (pure_erases _).charged _
  · exact tag0_erases.bind fun _ => same.bind fun _ => (pure_erases _).charged 1
  · exact (pure_erases _).charged 1
  · exact (pure_erases _).charged 1
  · split
    · exact fail_erases _
    · apply same.bind
      intro base
      cases base <;> first | exact fail_erases _ | exact appArgs_erases same _ _
  · split
    · exact fail_erases _
    · apply (lamBinders_erases same _).bind
      intro binders
      apply same.bind
      intro body
      cases body <;> first | exact fail_erases _ | exact (pure_erases _).charged _
  · split
    · exact fail_erases _
    · apply (allBinders_erases same _).bind
      intro binders
      apply same.bind
      intro body
      cases body <;> first | exact fail_erases _ | exact (pure_erases _).charged _
  · split
    · exact fail_erases _
    · exact same.bind fun _ => same.bind fun _ => same.bind fun _ => (pure_erases _).charged 1
  · exact (pure_erases _).charged 1
  · exact fail_erases _

theorem exprFuel_erases (fuel : Nat) : Erases (exprFuel fuel) (getExprFuel fuel) := by
  induction fuel with
  | zero => exact fail_erases _
  | succ fuel ih => exact tag4_erases.bind (exprFromTag_erases ih)

theorem expr_erases : Erases expr getExpr := by
  funext state
  exact congrFun (exprFuel_erases _) state

theorem exprFromTag_bound {recur : M Expr} (bound : Bound recur 16 0 (fun _ => 4))
    (tag : Tag4) : Bound (exprFromTag recur tag) 16 14 (fun _ => 4) := by
  unfold exprFromTag
  split
  · exact charged_pure_bound _ _ _ _ _ (by decide)
  · exact charged_pure_bound _ _ _ _ _ (by decide)
  · apply ((tag0_bound 16 (by decide)).frame 14).bind
    intro refIdx
    apply ((tag0Sizes_bound _).frame 28).bind
    intro univIdxs
    exact charged_pure_bound _ _ _ _ _ (by omega)
  · apply ((tag0_bound 16 (by decide)).frame 14).bind
    intro recIdx
    apply ((tag0Sizes_bound _).frame 28).bind
    intro univIdxs
    exact charged_pure_bound _ _ _ _ _ (by omega)
  · apply ((tag0_bound 16 (by decide)).frame 14).bind
    intro typeRefIdx
    apply (bound.frame 28).bind
    intro val
    exact charged_pure_bound _ _ _ _ _ (by decide)
  · exact charged_pure_bound _ _ _ _ _ (by decide)
  · exact charged_pure_bound _ _ _ _ _ (by decide)
  · split
    · exact fail_bound _ _ _ _
    · apply (bound.frame 14).bind
      intro base
      cases base <;> first
      | exact fail_bound _ _ _ _
      | exact ((appArgs_bound bound _ _).frame 18).weaken (by decide) (fun _ => by decide)
  · split
    · exact fail_bound _ _ _ _
    · apply ((lamBinders_bound bound _).frame 14).bind
      intro binders
      apply (bound.carry (2 * binders.length + 14)).bind
      intro body
      cases body <;> first
      | exact fail_bound _ _ _ _
      | exact charged_pure_bound _ _ _ _ _ (by omega)
  · split
    · exact fail_bound _ _ _ _
    · apply ((allBinders_bound bound _).frame 14).bind
      intro binders
      apply (bound.carry (2 * binders.length + 14)).bind
      intro body
      cases body <;> first
      | exact fail_bound _ _ _ _
      | exact charged_pure_bound _ _ _ _ _ (by omega)
  · split
    · exact fail_bound _ _ _ _
    · apply (bound.frame 14).bind
      intro ty
      apply (bound.frame 18).bind
      intro val
      apply (bound.frame 22).bind
      intro body
      exact charged_pure_bound _ _ _ _ _ (by decide)
  · exact charged_pure_bound _ _ _ _ _ (by decide)
  · exact fail_bound _ _ _ _

theorem exprFuel_bound (fuel : Nat) : Bound (exprFuel fuel) 16 0 (fun _ => 4) := by
  induction fuel with
  | zero => exact fail_bound _ _ _ _
  | succ fuel ih => exact (tag4_bound 16 (by decide)).bind (exprFromTag_bound ih)

/-- Includes arbitrary nonzero valid cursors and all malformed/truncated reads.
The production reader executes no accounting state. -/
theorem expr_bound : Bound expr 16 0 (fun _ => 4) := by
  intro state valid
  exact exprFuel_bound _ state valid

end Ix.Ixon.Verify.Work
