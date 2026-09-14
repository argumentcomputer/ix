/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.ExpressionGraph
import Ix.Aiur.Proofs.OperationRows

/-!
Smart expression construction, evaluated metadata and scalar operation emission.
The operators mirror the pinned native frontend's folds. Evaluation is preserved
for working operations satisfying the stated algebra laws, which are proved for
Goldilocks. A preserved check excluding negated constant nodes makes syntactic
constant flags precise, independently of conservative degree bookkeeping.

The addition, subtraction, multiplication and equality-test emitters reflect
the valued operation model, including allocated columns and every equation. Native comparison
checks actual expression trees and operation emission. Rust execution refinement,
remaining operation forms, graph compilation and cryptographic acceptance
are separate obligations.
-/

namespace Aiur

theorem G.sub_zero (value : G) : value - 0 = value := by
  apply G.ext_n
  simp only [G.n_sub, show (0 : G).n = 0 from rfl, Nat.sub_zero, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (UInt64.lt_iff_toNat_lt.mp value.property)

theorem G.neg_neg (value : G) : 0 - (0 - value) = value := by
  have bound := UInt64.lt_iff_toNat_lt.mp value.property
  apply G.ext_n
  simp only [G.n_sub, show (0 : G).n = 0 from rfl, Nat.zero_add]
  change value.n < gSize.toNat at bound
  by_cases zero : value.n = 0
  · simp only [zero, Nat.sub_zero, Nat.mod_self]
  · have inside : gSize.toNat - value.n < gSize.toNat := by omega
    rw [Nat.mod_eq_of_lt inside]
    have cancel : gSize.toNat - (gSize.toNat - value.n) = value.n := by omega
    rw [cancel, Nat.mod_eq_of_lt bound]

namespace NativeAIR

def Expr.isConstant : Expr → Bool
  | .konst _ => true
  | _ => false

def Expr.constantValue : Expr → Option G
  | .konst value => some value
  | _ => none

def Expr.frontNeg : Expr → Expr
  | .konst value => .konst (0 - value)
  | .neg value => value
  | value => .neg value

def Expr.frontAdd (left right : Expr) : Expr :=
  match left.constantValue, right.constantValue with
  | some a, some b => .konst (a + b)
  | some a, none => if a == 0 then right else .add left right
  | none, some b => if b == 0 then left else .add left right
  | none, none => .add left right

def Expr.frontSub (left right : Expr) : Expr :=
  match left.constantValue, right.constantValue with
  | some a, some b => .konst (a - b)
  | none, some b => if b == 0 then left else .sub left right
  | some a, none => if a == 0 then right.frontNeg else .sub left right
  | none, none => .sub left right

def Expr.frontMul (left right : Expr) : Expr :=
  match left.constantValue, right.constantValue with
  | some a, some b => .konst (a * b)
  | some a, none => if a == 0 then .konst 0 else if a == 1 then right else .mul left right
  | none, some b => if b == 0 then .konst 0 else if b == 1 then left else .mul left right
  | none, none => .mul left right

structure EvalLaws (ops : EvalOps W) : Prop where
  konst_add : ∀ a b, ops.konst (a + b) = ops.add (ops.konst a) (ops.konst b)
  konst_sub : ∀ a b, ops.konst (a - b) = ops.sub (ops.konst a) (ops.konst b)
  konst_mul : ∀ a b, ops.konst (a * b) = ops.mul (ops.konst a) (ops.konst b)
  konst_neg : ∀ a, ops.konst (0 - a) = ops.neg (ops.konst a)
  add_zero : ∀ a, ops.add a (ops.konst 0) = a
  zero_add : ∀ a, ops.add (ops.konst 0) a = a
  sub_zero : ∀ a, ops.sub a (ops.konst 0) = a
  zero_sub : ∀ a, ops.sub (ops.konst 0) a = ops.neg a
  mul_zero : ∀ a, ops.mul a (ops.konst 0) = ops.konst 0
  zero_mul : ∀ a, ops.mul (ops.konst 0) a = ops.konst 0
  mul_one : ∀ a, ops.mul a (ops.konst 1) = a
  one_mul : ∀ a, ops.mul (ops.konst 1) a = a
  neg_neg : ∀ a, ops.neg (ops.neg a) = a

def Expr.noConstantNegs : Expr → Bool
  | .neg child => !child.isConstant && child.noConstantNegs
  | .add a b | .sub a b | .mul a b => a.noConstantNegs && b.noConstantNegs
  | _ => true

theorem Expr.isConstant_eq (expr : Expr) : expr.isConstant = expr.constantValue.isSome := by
  cases expr <;> rfl

theorem Expr.frontNeg_noConstantNegs {expr : Expr} (valid : expr.noConstantNegs = true) :
    expr.frontNeg.noConstantNegs = true := by
  cases expr <;> simp_all only [Expr.noConstantNegs, Expr.frontNeg, Expr.isConstant,
    Bool.not_false, Bool.true_and, Bool.and_eq_true]

theorem Expr.frontNeg_isConstant {expr : Expr} (valid : expr.noConstantNegs = true) :
    expr.frontNeg.isConstant = expr.isConstant := by
  cases expr <;> try rfl
  case neg child =>
    simp only [Expr.noConstantNegs, Bool.and_eq_true, Bool.not_eq_true'] at valid
    exact valid.1

theorem Expr.frontAdd_isConstant (left right : Expr) :
    (left.frontAdd right).isConstant = (left.isConstant && right.isConstant) := by
  have leftC := left.isConstant_eq
  have rightC := right.isConstant_eq
  cases hl : left.constantValue <;> cases hr : right.constantValue
  all_goals simp only [hl, hr, Option.isSome_none, Option.isSome_some] at leftC rightC
  · rw [leftC, rightC]; simp only [Expr.frontAdd, hl, hr]; rfl
  · rename_i c
    by_cases zero : c = 0
    · simp only [Expr.frontAdd, hl, hr, beq_iff_eq, if_pos zero, leftC, rightC, Bool.false_and]
    · rw [leftC, rightC]; simp only [Expr.frontAdd, hl, hr, beq_iff_eq, if_neg zero]; rfl
  · rename_i c
    by_cases zero : c = 0
    · simp only [Expr.frontAdd, hl, hr, beq_iff_eq, if_pos zero, leftC, rightC, Bool.true_and]
    · rw [leftC, rightC]; simp only [Expr.frontAdd, hl, hr, beq_iff_eq, if_neg zero]; rfl
  · rw [leftC, rightC]; simp only [Expr.frontAdd, hl, hr]; rfl

theorem Expr.frontSub_isConstant (left right : Expr) (valid : right.noConstantNegs = true) :
    (left.frontSub right).isConstant = (left.isConstant && right.isConstant) := by
  have leftC := left.isConstant_eq
  have rightC := right.isConstant_eq
  cases hl : left.constantValue <;> cases hr : right.constantValue
  all_goals simp only [hl, hr, Option.isSome_none, Option.isSome_some] at leftC rightC
  · rw [leftC, rightC]; simp only [Expr.frontSub, hl, hr]; rfl

  · rename_i c
    by_cases zero : c = 0
    · simp only [Expr.frontSub, hl, hr, beq_iff_eq, if_pos zero, leftC, rightC, Bool.false_and]
    · rw [leftC, rightC]; simp only [Expr.frontSub, hl, hr, beq_iff_eq, if_neg zero]; rfl
  · rename_i c
    by_cases zero : c = 0
    · simp only [Expr.frontSub, hl, hr, beq_iff_eq, if_pos zero, Expr.frontNeg_isConstant valid,
        leftC, rightC, Bool.true_and]
    · rw [leftC, rightC]; simp only [Expr.frontSub, hl, hr, beq_iff_eq, if_neg zero]; rfl
  · rw [leftC, rightC]; simp only [Expr.frontSub, hl, hr]; rfl

theorem Expr.frontAdd_noConstantNegs {left right : Expr}
    (leftValid : left.noConstantNegs = true) (rightValid : right.noConstantNegs = true) :
    (left.frontAdd right).noConstantNegs = true := by
  have raw : (Expr.add left right).noConstantNegs = true := by
    simp only [Expr.noConstantNegs, leftValid, rightValid, Bool.true_and]
  unfold Expr.frontAdd
  cases hl : left.constantValue <;> cases hr : right.constantValue
  · exact raw
  · rename_i c
    by_cases zero : c = 0
    · simp only [beq_iff_eq, if_pos zero]; exact leftValid
    · simp only [beq_iff_eq, if_neg zero]; exact raw
  · rename_i c
    by_cases zero : c = 0
    · simp only [beq_iff_eq, if_pos zero]; exact rightValid
    · simp only [beq_iff_eq, if_neg zero]; exact raw
  · rfl

theorem Expr.frontSub_noConstantNegs {left right : Expr}
    (leftValid : left.noConstantNegs = true) (rightValid : right.noConstantNegs = true) :
    (left.frontSub right).noConstantNegs = true := by
  have raw : (Expr.sub left right).noConstantNegs = true := by
    simp only [Expr.noConstantNegs, leftValid, rightValid, Bool.true_and]
  unfold Expr.frontSub
  cases hl : left.constantValue <;> cases hr : right.constantValue
  · exact raw
  · rename_i c
    by_cases zero : c = 0
    · simp only [beq_iff_eq, if_pos zero]; exact leftValid
    · simp only [beq_iff_eq, if_neg zero]; exact raw
  · rename_i c
    by_cases zero : c = 0
    · simp only [beq_iff_eq, if_pos zero]; exact Expr.frontNeg_noConstantNegs rightValid
    · simp only [beq_iff_eq, if_neg zero]; exact raw
  · rfl

theorem Expr.frontMul_noConstantNegs {left right : Expr}
    (leftValid : left.noConstantNegs = true) (rightValid : right.noConstantNegs = true) :
    (left.frontMul right).noConstantNegs = true := by
  have raw : (Expr.mul left right).noConstantNegs = true := by
    simp only [Expr.noConstantNegs, leftValid, rightValid, Bool.true_and]
  unfold Expr.frontMul
  cases hl : left.constantValue <;> cases hr : right.constantValue
  · exact raw
  · rename_i c
    by_cases zero : c = 0
    · simp only [beq_iff_eq, if_pos zero]; rfl
    · by_cases one : c = 1
      · simp only [beq_iff_eq, if_neg zero, if_pos one]; exact leftValid
      · simp only [beq_iff_eq, if_neg zero, if_neg one]; exact raw
  · rename_i c
    by_cases zero : c = 0
    · simp only [beq_iff_eq, if_pos zero]; rfl
    · by_cases one : c = 1
      · simp only [beq_iff_eq, if_neg zero, if_pos one]; exact rightValid
      · simp only [beq_iff_eq, if_neg zero, if_neg one]; exact raw
  · rfl

theorem Expr.frontNeg_eval {ops : EvalOps W} (laws : EvalLaws ops) (values : Values W) {expr : Expr} {value : W}
    (evaluated : expr.eval ops values = some value) :
    expr.frontNeg.eval ops values = some (ops.neg value) := by
  have raw : (Expr.neg expr).eval ops values = some (ops.neg value) := by
    change (expr.eval ops values).bind (fun c => some (ops.neg c)) = _
    rw [evaluated]; rfl
  cases expr <;> try exact raw
  case konst c =>
    change some (ops.konst c) = some value at evaluated
    cases evaluated
    exact congrArg some (laws.konst_neg c)
  case neg expr =>
    change (expr.eval ops values).bind (fun c => some (ops.neg c)) = some value at evaluated
    cases inner : expr.eval ops values with
    | none => simp only [inner, Option.bind_none, reduceCtorEq] at evaluated
    | some result =>
      simp only [inner, Option.bind_some, Option.some.injEq] at evaluated
      subst value
      simpa only [Expr.frontNeg, laws.neg_neg] using inner

theorem Expr.eval_constantValue (ops : EvalOps W) (values : Values W) {expr : Expr} {value : W} {constant : G}
    (evaluated : expr.eval ops values = some value)
    (known : expr.constantValue = some constant) : ops.konst constant = value := by
  cases expr <;> simp only [Expr.constantValue, reduceCtorEq] at known
  case konst c => cases known; exact Option.some.inj evaluated

theorem Expr.frontAdd_eval {ops : EvalOps W} (laws : EvalLaws ops) (values : Values W) {left right : Expr} {a b : W}
    (leftEval : left.eval ops values = some a)
    (rightEval : right.eval ops values = some b) :
    (left.frontAdd right).eval ops values = some (ops.add a b) := by
  have raw : (Expr.add left right).eval ops values = some (ops.add a b) := by
    change (left.eval ops values).bind (fun x =>
      (right.eval ops values).bind (fun y => some (ops.add x y))) = _
    rw [leftEval, Option.bind_some, rightEval]; rfl
  unfold Expr.frontAdd
  cases hl : left.constantValue <;> cases hr : right.constantValue
  · exact raw
  · rename_i c
    have equal := Expr.eval_constantValue ops values rightEval hr
    subst b
    by_cases zero : c = 0
    · simp only [beq_iff_eq, zero, laws.add_zero]; exact leftEval
    · simp only [beq_iff_eq, if_neg zero]; exact raw
  · rename_i c
    have equal := Expr.eval_constantValue ops values leftEval hl
    subst a
    by_cases zero : c = 0
    · simp only [beq_iff_eq, zero, laws.zero_add]; exact rightEval
    · simp only [beq_iff_eq, if_neg zero]; exact raw
  · rename_i c d
    have leftEq := Expr.eval_constantValue ops values leftEval hl
    have rightEq := Expr.eval_constantValue ops values rightEval hr
    subst a; subst b
    exact congrArg some (laws.konst_add c d)

theorem Expr.frontSub_eval {ops : EvalOps W} (laws : EvalLaws ops) (values : Values W) {left right : Expr} {a b : W}
    (leftEval : left.eval ops values = some a)
    (rightEval : right.eval ops values = some b) :
    (left.frontSub right).eval ops values = some (ops.sub a b) := by
  have raw : (Expr.sub left right).eval ops values = some (ops.sub a b) := by
    change (left.eval ops values).bind (fun x =>
      (right.eval ops values).bind (fun y => some (ops.sub x y))) = _
    rw [leftEval, Option.bind_some, rightEval]; rfl
  unfold Expr.frontSub
  cases hl : left.constantValue <;> cases hr : right.constantValue
  · exact raw
  · rename_i c
    have equal := Expr.eval_constantValue ops values rightEval hr
    subst b
    by_cases zero : c = 0
    · simp only [beq_iff_eq, zero, laws.sub_zero]; exact leftEval
    · simp only [beq_iff_eq, if_neg zero]; exact raw
  · rename_i c
    have equal := Expr.eval_constantValue ops values leftEval hl
    subst a
    by_cases zero : c = 0
    · simp only [beq_iff_eq, zero, laws.zero_sub]; exact Expr.frontNeg_eval laws values rightEval
    · simp only [beq_iff_eq, if_neg zero]; exact raw
  · rename_i c d
    have leftEq := Expr.eval_constantValue ops values leftEval hl
    have rightEq := Expr.eval_constantValue ops values rightEval hr
    subst a; subst b
    exact congrArg some (laws.konst_sub c d)

theorem Expr.frontMul_eval {ops : EvalOps W} (laws : EvalLaws ops) (values : Values W) {left right : Expr} {a b : W}
    (leftEval : left.eval ops values = some a)
    (rightEval : right.eval ops values = some b) :
    (left.frontMul right).eval ops values = some (ops.mul a b) := by
  have raw : (Expr.mul left right).eval ops values = some (ops.mul a b) := by
    change (left.eval ops values).bind (fun x =>
      (right.eval ops values).bind (fun y => some (ops.mul x y))) = _
    rw [leftEval, Option.bind_some, rightEval]; rfl
  unfold Expr.frontMul
  cases hl : left.constantValue <;> cases hr : right.constantValue
  · exact raw
  · rename_i c
    have equal := Expr.eval_constantValue ops values rightEval hr
    subst b
    by_cases zero : c = 0
    · simp only [beq_iff_eq, zero, laws.mul_zero]; rfl
    · by_cases one : c = 1
      · simp only [beq_iff_eq, one, laws.mul_one]; exact leftEval
      · simp only [beq_iff_eq, if_neg zero, if_neg one]; exact raw
  · rename_i c
    have equal := Expr.eval_constantValue ops values leftEval hl
    subst a
    by_cases zero : c = 0
    · simp only [beq_iff_eq, zero, laws.zero_mul]; rfl
    · by_cases one : c = 1
      · simp only [beq_iff_eq, one, laws.one_mul]; exact rightEval
      · simp only [beq_iff_eq, if_neg zero, if_neg one]; exact raw
  · rename_i c d
    have leftEq := Expr.eval_constantValue ops values leftEval hl
    have rightEq := Expr.eval_constantValue ops values rightEval hr
    subst a; subst b
    exact congrArg some (laws.konst_mul c d)

theorem goldilocks_add_zero (a : G) : goldilocksOps.add a (goldilocksOps.konst 0) = a := G.add_zero a
theorem goldilocks_zero_add (a : G) : goldilocksOps.add (goldilocksOps.konst 0) a = a := G.zero_add a
theorem goldilocks_sub_zero (a : G) : goldilocksOps.sub a (goldilocksOps.konst 0) = a := G.sub_zero a
theorem goldilocks_zero_sub (a : G) : goldilocksOps.sub (goldilocksOps.konst 0) a = goldilocksOps.neg a := rfl
theorem goldilocks_mul_zero (a : G) : goldilocksOps.mul a (goldilocksOps.konst 0) = goldilocksOps.konst 0 := G.mul_zero a
theorem goldilocks_zero_mul (a : G) : goldilocksOps.mul (goldilocksOps.konst 0) a = goldilocksOps.konst 0 :=
  (G.mul_comm 0 a).trans (G.mul_zero a)
theorem goldilocks_mul_one (a : G) : goldilocksOps.mul a (goldilocksOps.konst 1) = a := G.mul_one a
theorem goldilocks_one_mul (a : G) : goldilocksOps.mul (goldilocksOps.konst 1) a = a :=
  (G.mul_comm 1 a).trans (G.mul_one a)
theorem goldilocks_neg_neg (a : G) : goldilocksOps.neg (goldilocksOps.neg a) = a := G.neg_neg a

theorem goldilocks_konst_add (a b : G) : goldilocksOps.konst (a + b) = goldilocksOps.add (goldilocksOps.konst a) (goldilocksOps.konst b) := rfl
theorem goldilocks_konst (a : G) : goldilocksOps.konst a = a := rfl
theorem goldilocks_add (a b : G) : goldilocksOps.add a b = a + b := rfl
theorem goldilocks_sub (a b : G) : goldilocksOps.sub a b = a - b := rfl
theorem goldilocks_mul (a b : G) : goldilocksOps.mul a b = a * b := rfl
theorem goldilocks_konst_sub (a b : G) : goldilocksOps.konst (a - b) = goldilocksOps.sub (goldilocksOps.konst a) (goldilocksOps.konst b) := calc
  _ = a - b := goldilocks_konst _
  _ = goldilocksOps.konst a - goldilocksOps.konst b :=
    (congrArg (fun x : G => x - b) (goldilocks_konst a).symm).trans
      (congrArg (fun y : G => goldilocksOps.konst a - y) (goldilocks_konst b).symm)
  _ = _ := (goldilocks_sub _ _).symm
theorem goldilocks_konst_mul (a b : G) : goldilocksOps.konst (a * b) = goldilocksOps.mul (goldilocksOps.konst a) (goldilocksOps.konst b) := rfl
theorem goldilocks_konst_neg (a : G) : goldilocksOps.konst (0 - a) = goldilocksOps.neg (goldilocksOps.konst a) := rfl

theorem goldilocksLaws : EvalLaws goldilocksOps where
  konst_add := goldilocks_konst_add
  konst_sub := goldilocks_konst_sub
  konst_mul := goldilocks_konst_mul
  konst_neg := goldilocks_konst_neg
  add_zero := goldilocks_add_zero
  zero_add := goldilocks_zero_add
  sub_zero := goldilocks_sub_zero
  zero_sub := goldilocks_zero_sub
  mul_zero := goldilocks_mul_zero
  zero_mul := goldilocks_zero_mul
  mul_one := goldilocks_mul_one
  one_mul := goldilocks_one_mul
  neg_neg := goldilocks_neg_neg

theorem Expr.constantValue_eq_of_eval (values : Values G) {expr : Expr} {value constant : G}
    (evaluated : expr.eval goldilocksOps values = some value)
    (known : expr.constantValue = some constant) : constant = value :=
  (goldilocks_konst constant).symm.trans (Expr.eval_constantValue goldilocksOps values evaluated known)

theorem Expr.frontMul_isConstant (values : Values G) {left right : Expr} {a b : G}
    (leftEval : left.eval goldilocksOps values = some a)
    (rightEval : right.eval goldilocksOps values = some b) :
    (left.frontMul right).isConstant =
      ((left.isConstant && right.isConstant) || (left.isConstant && a == 0) ||
        (right.isConstant && b == 0)) := by
  have leftC := left.isConstant_eq
  have rightC := right.isConstant_eq
  cases hl : left.constantValue <;> cases hr : right.constantValue
  all_goals simp only [hl, hr, Option.isSome_none, Option.isSome_some] at leftC rightC
  all_goals rw [leftC, rightC]
  · simp only [Expr.frontMul, hl, hr]; rfl
  · rename_i c
    have equal := Expr.constantValue_eq_of_eval values rightEval hr
    subst b
    by_cases zero : c = 0
    · simp [Expr.frontMul, hl, hr, zero, Expr.isConstant]
    · have eqZero : (c == 0) = false := by simpa only [beq_eq_false_iff_ne] using zero
      by_cases one : c = 1
      · simp only [Expr.frontMul, hl, hr, eqZero, Bool.false_eq_true, if_false, beq_iff_eq,
          if_pos one, leftC, Bool.false_and, Bool.true_and, Bool.false_or]
      · simp only [Expr.frontMul, hl, hr, eqZero, Bool.false_eq_true, if_false, beq_iff_eq,
          if_neg one, Bool.false_and, Bool.true_and, Bool.false_or]; rfl
  · rename_i c
    have equal := Expr.constantValue_eq_of_eval values leftEval hl
    subst a
    by_cases zero : c = 0
    · simp [Expr.frontMul, hl, hr, zero, Expr.isConstant]
    · have eqZero : (c == 0) = false := by simpa only [beq_eq_false_iff_ne] using zero
      by_cases one : c = 1
      · simp only [Expr.frontMul, hl, hr, eqZero, Bool.false_eq_true, if_false, beq_iff_eq,
          if_pos one, rightC, Bool.false_and, Bool.true_and, Bool.false_or]
      · simp only [Expr.frontMul, hl, hr, eqZero, Bool.false_eq_true, if_false, beq_iff_eq,
          if_neg one, Bool.false_and, Bool.true_and, Bool.false_or]; rfl
  · simp [Expr.frontMul, hl, hr, Expr.isConstant]

structure RowExpr where
  expr : Expr
  degree : Nat
  deriving Repr, DecidableEq

def RowExpr.konst (value : G) : RowExpr := ⟨.konst value, 0⟩
def RowExpr.variable (column : ColRef) : RowExpr := ⟨.var column, 1⟩
def RowExpr.add (left right : RowExpr) : RowExpr :=
  ⟨left.expr.frontAdd right.expr, max left.degree right.degree⟩
def RowExpr.sub (left right : RowExpr) : RowExpr :=
  ⟨left.expr.frontSub right.expr, max left.degree right.degree⟩
def RowExpr.mul (left right : RowExpr) : RowExpr :=
  ⟨left.expr.frontMul right.expr, left.degree + right.degree⟩

def RowExpr.eval (values : Values G) (expr : RowExpr) : Option AIR.RowValue := do
  let value ← expr.expr.eval goldilocksOps values
  return ⟨value, expr.degree, expr.expr.isConstant⟩

def RowExpr.Reflects (values : Values G) (expr : RowExpr) (value : AIR.RowValue) : Prop :=
  expr.expr.eval goldilocksOps values = some value.value ∧
    expr.degree = value.degree ∧ expr.expr.isConstant = value.constant

theorem RowExpr.reflects_iff_eval (values : Values G) (expr : RowExpr) (value : AIR.RowValue) :
    expr.Reflects values value ↔ expr.eval values = some value := by
  unfold RowExpr.Reflects RowExpr.eval
  cases h : expr.expr.eval goldilocksOps values with
  | none => simp only [bind, Option.bind_none, reduceCtorEq, false_and]
  | some output =>
    cases value
    simp only [Option.some.injEq, bind, Option.bind_some, pure, AIR.RowValue.mk.injEq]

theorem RowExpr.konst_reflects (values : Values G) (value : G) :
    (RowExpr.konst value).Reflects values (AIR.RowValue.konst value) := ⟨rfl, rfl, rfl⟩

theorem RowExpr.variable_reflects (values : Values G) {column : ColRef} {value : G}
    (read : (values.columns column.source column.offset)[column.index]? = some value) :
    (RowExpr.variable column).Reflects values (AIR.RowValue.variable value) := ⟨read, rfl, rfl⟩

theorem RowExpr.add_reflects (values : Values G) {left right : RowExpr} {a b : AIR.RowValue}
    (leftRef : left.Reflects values a) (rightRef : right.Reflects values b) :
    (left.add right).Reflects values (a.add b) := by
  refine ⟨Expr.frontAdd_eval goldilocksLaws values leftRef.1 rightRef.1, ?_, ?_⟩
  · change max left.degree right.degree = max a.degree b.degree
    rw [leftRef.2.1, rightRef.2.1]
  · change (left.expr.frontAdd right.expr).isConstant = (a.constant && b.constant)
    rw [Expr.frontAdd_isConstant, leftRef.2.2, rightRef.2.2]

theorem RowExpr.sub_reflects (values : Values G) {left right : RowExpr} {a b : AIR.RowValue}
    (leftRef : left.Reflects values a) (rightRef : right.Reflects values b)
    (rightValid : right.expr.noConstantNegs = true) :
    (left.sub right).Reflects values (a.sub b) := by
  refine ⟨Expr.frontSub_eval goldilocksLaws values leftRef.1 rightRef.1, ?_, ?_⟩
  · change max left.degree right.degree = max a.degree b.degree
    rw [leftRef.2.1, rightRef.2.1]
  · change (left.expr.frontSub right.expr).isConstant = (a.constant && b.constant)
    rw [Expr.frontSub_isConstant _ _ rightValid, leftRef.2.2, rightRef.2.2]

theorem RowExpr.mul_reflects (values : Values G) {left right : RowExpr} {a b : AIR.RowValue}
    (leftRef : left.Reflects values a) (rightRef : right.Reflects values b) :
    (left.mul right).Reflects values (a.mul b) := by
  refine ⟨Expr.frontMul_eval goldilocksLaws values leftRef.1 rightRef.1, ?_, ?_⟩
  · change left.degree + right.degree = a.degree + b.degree
    rw [leftRef.2.1, rightRef.2.1]
  · change (left.expr.frontMul right.expr).isConstant =
      ((a.constant && b.constant) || (a.constant && a.value == 0) || (b.constant && b.value == 0))
    rw [Expr.frontMul_isConstant values leftRef.1 rightRef.1, leftRef.2.2, rightRef.2.2]

structure ScalarEmission where
  output : RowExpr
  used : Nat := 0
  equations : List Expr := []

def ScalarEmission.eval (values : Values G) (emission : ScalarEmission) : Option AIR.OpEmission := do
  let output ← emission.output.eval values
  let equations ← emission.equations.mapM (Expr.eval goldilocksOps values)
  return { outputs := #[output], used := emission.used, equations }

theorem ScalarEmission.eval_of (values : Values G) {output : RowExpr} {value : AIR.RowValue}
    {used : Nat} {equations : List Expr} {results : List G}
    (reflected : output.Reflects values value)
    (evaluated : equations.mapM (Expr.eval goldilocksOps values) = some results) :
    (ScalarEmission.mk output used equations).eval values =
      some { outputs := #[value], used, equations := results } := by
  have outputEval := (RowExpr.reflects_iff_eval values output value).mp reflected
  simp only [ScalarEmission.eval, outputEval, evaluated, bind, Option.bind, pure]

def mainCurrent (index : Nat) : RowExpr := .variable ⟨.main, .current, index⟩

def eqZeroRegular (selector : Expr) (first : Nat) (input : RowExpr) : ScalarEmission :=
  let d := mainCurrent first
  let x := mainCurrent (first + 1)
  ⟨x, 2, [(selector.frontMul input.expr).frontMul x.expr,
    selector.frontMul (((input.expr.frontMul d.expr).frontAdd x.expr).frontSub (.konst 1))]⟩

def emitEqZero (selector : Expr) (first : Nat) (input : RowExpr) : ScalarEmission :=
  match input.expr.constantValue, input.degree with
  | some value, 0 => ⟨.konst (G.eqZero value), 0, []⟩
  | _, _ => eqZeroRegular selector first input

theorem eqZeroRegular_reflects (values : Values G) (row : Nat → G) {selector : Expr} {s : G}
    {first : Nat} {input : RowExpr} {value : AIR.RowValue}
    (selectorEval : selector.eval goldilocksOps values = some s)
    (inputRef : input.Reflects values value)
    (firstRead : (values.columns .main .current)[first]? = some (row 0))
    (secondRead : (values.columns .main .current)[first + 1]? = some (row 1)) :
    (eqZeroRegular selector first input).eval values =
      some { outputs := #[AIR.RowValue.variable (row 1)], used := 2, equations :=
        [s * value.value * row 1, s * (value.value * row 0 + row 1 - 1)] } := by
  have dRef := RowExpr.variable_reflects values (column := ⟨.main, .current, first⟩) firstRead
  have xRef := RowExpr.variable_reflects values (column := ⟨.main, .current, first + 1⟩) secondRead
  have oneEval : (Expr.konst 1).eval goldilocksOps values = some 1 := rfl
  have firstEval := Expr.frontMul_eval goldilocksLaws values
    (Expr.frontMul_eval goldilocksLaws values selectorEval inputRef.1) xRef.1
  have secondEval := Expr.frontMul_eval goldilocksLaws values selectorEval
    (Expr.frontSub_eval goldilocksLaws values
      (Expr.frontAdd_eval goldilocksLaws values
        (Expr.frontMul_eval goldilocksLaws values inputRef.1 dRef.1) xRef.1) oneEval)
  apply ScalarEmission.eval_of values xRef
  simp only [mainCurrent, List.mapM_cons, List.mapM_nil, firstEval, secondEval, bind, Option.bind, pure]
  simp only [goldilocks_add, goldilocks_sub, goldilocks_mul, AIR.RowValue.variable]

theorem emitEqZero_reflects (values : Values G) (row : Nat → G) {selector : Expr} {s : G}
    {first : Nat} {input : RowExpr} {value : AIR.RowValue}
    (selectorEval : selector.eval goldilocksOps values = some s)
    (inputRef : input.Reflects values value)
    (reads : ∀ index < (emitEqZero selector first input).used,
      (values.columns .main .current)[first + index]? = some (row index)) :
    (emitEqZero selector first input).eval values = AIR.emitOp row s 0 (.eqZero 0) #[value] := by
  have known := input.expr.isConstant_eq
  have constant := inputRef.2.2
  have degree := inputRef.2.1
  cases hc : input.expr.constantValue with
  | none =>
    have notConstant : value.constant = false := by
      rw [hc] at known
      exact constant.symm.trans known
    simp only [emitEqZero, hc]
    simp only [AIR.emitOp, Array.getElem?_singleton, if_true, bind, Option.bind_some, notConstant,
      Bool.false_and, Bool.false_eq_true, if_false]
    apply eqZeroRegular_reflects values row selectorEval inputRef
    · simpa only [Nat.add_zero] using reads 0 (by simp only [emitEqZero, hc, eqZeroRegular]; decide)
    · exact reads 1 (by simp only [emitEqZero, hc, eqZeroRegular]; decide)
  | some c =>
    have isConstant : value.constant = true := by
      rw [hc] at known
      exact constant.symm.trans known
    have valueEq := Expr.constantValue_eq_of_eval values inputRef.1 hc
    cases hd : input.degree with
    | zero =>
      have zeroDegree : value.degree = 0 := degree.symm.trans hd
      simp only [emitEqZero, hc, hd]
      simp only [AIR.emitOp, Array.getElem?_singleton, if_true, bind, Option.bind_some, isConstant,
        zeroDegree, beq_self_eq_true, Bool.true_and, if_true]
      rw [valueEq]
      exact ScalarEmission.eval_of values (RowExpr.konst_reflects values _) rfl
    | succ n =>
      have positiveDegree : value.degree = n + 1 := degree.symm.trans hd
      simp only [emitEqZero, hc, hd]
      simp only [AIR.emitOp, Array.getElem?_singleton, if_true, bind, Option.bind_some, isConstant,
        positiveDegree, Nat.succ_ne_zero, beq_iff_eq, Bool.true_and, if_false]
      apply eqZeroRegular_reflects values row selectorEval inputRef
      · simpa only [Nat.add_zero] using reads 0 (by simp only [emitEqZero, hc, hd, eqZeroRegular]; decide)
      · exact reads 1 (by simp only [emitEqZero, hc, hd, eqZeroRegular]; decide)

def mulRegular (selector : Expr) (first : Nat) (product : RowExpr) : ScalarEmission :=
  let output := mainCurrent first
  ⟨output, 1, [selector.frontMul (output.expr.frontSub product.expr)]⟩

def emitMul (selector : Expr) (first : Nat) (left right : RowExpr) : ScalarEmission :=
  let product := left.mul right
  if product.degree < 2 then ⟨product, 0, []⟩ else mulRegular selector first product

theorem mulRegular_reflects (values : Values G) (row : Nat → G) {selector : Expr} {s : G}
    {first : Nat} {product : RowExpr} {value : AIR.RowValue}
    (selectorEval : selector.eval goldilocksOps values = some s)
    (productRef : product.Reflects values value)
    (read : (values.columns .main .current)[first]? = some (row 0)) :
    (mulRegular selector first product).eval values =
      some { outputs := #[AIR.RowValue.variable (row 0)], used := 1, equations := [s * (row 0 - value.value)] } := by
  have outputRef := RowExpr.variable_reflects values (column := ⟨.main, .current, first⟩) read
  have equationEval := Expr.frontMul_eval goldilocksLaws values selectorEval
    (Expr.frontSub_eval goldilocksLaws values outputRef.1 productRef.1)
  apply ScalarEmission.eval_of values outputRef
  simp only [mainCurrent, List.mapM_cons, List.mapM_nil, equationEval, bind, Option.bind, pure]
  simp only [goldilocks_mul, goldilocks_sub, AIR.RowValue.variable]

theorem emitMul_reflects (values : Values G) (row : Nat → G) {selector : Expr} {s : G}
    {first : Nat} {left right : RowExpr} {a b : AIR.RowValue}
    (selectorEval : selector.eval goldilocksOps values = some s)
    (leftRef : left.Reflects values a) (rightRef : right.Reflects values b)
    (reads : ∀ index < (emitMul selector first left right).used,
      (values.columns .main .current)[first + index]? = some (row index)) :
    (emitMul selector first left right).eval values = AIR.emitOp row s 0 (.mul 0 1) #[a, b] := by
  have productRef := RowExpr.mul_reflects values leftRef rightRef
  simp only [AIR.emitOp, show (#[a, b][0]?) = some a from rfl,
    show (#[a, b][1]?) = some b from rfl, bind, Option.bind_some]
  rw [← productRef.2.1]
  unfold emitMul
  split
  next small =>
    rw [if_pos small]
    exact ScalarEmission.eval_of values productRef rfl
  next large =>
    rw [if_neg large]
    apply mulRegular_reflects values row selectorEval productRef
    simpa only [Nat.add_zero] using reads 0 (by simp only [emitMul, if_neg large, mulRegular]; decide)

theorem emitEqZero_noConstantNegs (selector : Expr) (first : Nat) (input : RowExpr) :
    (emitEqZero selector first input).output.expr.noConstantNegs = true := by
  unfold emitEqZero
  cases input.expr.constantValue <;> cases input.degree <;> rfl

theorem emitMul_noConstantNegs (selector : Expr) (first : Nat) {left right : RowExpr}
    (leftValid : left.expr.noConstantNegs = true) (rightValid : right.expr.noConstantNegs = true) :
    (emitMul selector first left right).output.expr.noConstantNegs = true := by
  unfold emitMul
  dsimp only
  split
  · exact Expr.frontMul_noConstantNegs leftValid rightValid
  · rfl

theorem emitAdd_reflects (values : Values G) (row : Nat → G) (selector rank : G)
    {left right : RowExpr} {a b : AIR.RowValue}
    (leftRef : left.Reflects values a) (rightRef : right.Reflects values b) :
    (ScalarEmission.mk (left.add right) 0 []).eval values =
      AIR.emitOp row selector rank (.add 0 1) #[a, b] := by
  simp only [AIR.emitOp, show (#[a, b][0]?) = some a from rfl,
    show (#[a, b][1]?) = some b from rfl, bind, Option.bind_some]
  exact ScalarEmission.eval_of values (RowExpr.add_reflects values leftRef rightRef) rfl

theorem emitSub_reflects (values : Values G) (row : Nat → G) (selector rank : G)
    {left right : RowExpr} {a b : AIR.RowValue}
    (leftRef : left.Reflects values a) (rightRef : right.Reflects values b)
    (rightValid : right.expr.noConstantNegs = true) :
    (ScalarEmission.mk (left.sub right) 0 []).eval values =
      AIR.emitOp row selector rank (.sub 0 1) #[a, b] := by
  simp only [AIR.emitOp, show (#[a, b][0]?) = some a from rfl,
    show (#[a, b][1]?) = some b from rfl, bind, Option.bind_some]
  exact ScalarEmission.eval_of values (RowExpr.sub_reflects values leftRef rightRef rightValid) rfl

end NativeAIR
end Aiur
