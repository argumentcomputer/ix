/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.FrontendExpressions

/-!
Value preservation for base expression graph compilation. A linear structural
interner models the native hash table's insertion order. Smart graph operators
fold constants, share nodes, sort commutative operands and cancel equal ids.
Successful compilation preserves earlier node values, constraint satisfaction,
and ordered lookup multiplicities and arguments. The required working algebra
laws are proved for Goldilocks.

The model uses natural-number node indices. Native comparison checks actual
base graphs and compilation rejections. Rust execution and hash-table refinement,
machine bounds, extension-coordinate expansion, and cryptographic acceptance
remain separate obligations.
-/

namespace Aiur

theorem G.sub_self (value : G) : value - value = 0 := by
  apply G.ext_n
  simp only [G.n_sub, show (0 : G).n = 0 from rfl]
  rw [show value.n + gSize.toNat - value.n = gSize.toNat from by omega]
  exact Nat.mod_self _

namespace NativeAIR

structure GraphEvalLaws (ops : EvalOps W) : Prop extends EvalLaws ops where
  add_comm : ∀ a b, ops.add a b = ops.add b a
  mul_comm : ∀ a b, ops.mul a b = ops.mul b a
  sub_self : ∀ a, ops.sub a a = ops.konst 0

theorem goldilocksGraphLaws : GraphEvalLaws goldilocksOps where
  toEvalLaws := goldilocksLaws
  add_comm := G.add_comm
  mul_comm := G.mul_comm
  sub_self := G.sub_self

namespace Compiler

def Extends (before after : Array W) : Prop :=
  ∀ (index : Nat) (value : W), before[index]? = some value → after[index]? = some value

theorem Extends.refl (buffer : Array W) : Extends buffer buffer := fun _ _ read => read

theorem Extends.trans {first second third : Array W}
    (left : Extends first second) (right : Extends second third) : Extends first third :=
  fun index value read => right index value (left index value read)

theorem Extends.push (buffer : Array W) (value : W) : Extends buffer (buffer.push value) := by
  intro index old read
  have bound := (Array.getElem?_eq_some_iff.mp read).1
  rw [Array.getElem?_push_lt bound, (Array.getElem?_eq_some_iff.mp read).2]

theorem eval_extends (ops : EvalOps W) (values : Values W) {before after : Array W}
    (growth : Extends before after) (node : Node) {value : W}
    (evaluated : node.eval ops values before = some value) :
    node.eval ops values after = some value := by
  cases node <;> simp only [Node.eval] at evaluated ⊢
  all_goals try exact evaluated
  case add a b | sub a b | mul a b =>
    cases ha : before[a]? <;> cases hb : before[b]? <;>
      simp only [ha, hb, bind, Option.bind, pure, reduceCtorEq] at evaluated
    all_goals
      rename_i va vb
      simpa only [growth a va ha, growth b vb hb, bind, Option.bind, pure] using evaluated
  case neg a =>
    cases ha : before[a]? <;>
      simp only [ha, bind, Option.bind, pure, reduceCtorEq] at evaluated
    rename_i va
    simpa only [growth a va ha, bind, Option.bind, pure] using evaluated

structure Evaluation (ops : EvalOps W) (values : Values W) (nodes : List Node)
    (buffer : Array W) : Prop where
  size : buffer.size = nodes.length
  sweep : sweepFrom ops values nodes #[] = some buffer
  cached : ∀ (index : Nat) (node : Node), nodes[index]? = some node → node.eval ops values buffer = buffer[index]?

theorem Evaluation.empty (ops : EvalOps W) (values : Values W) :
    Evaluation ops values [] #[] := ⟨rfl, rfl, fun _ _ read => by cases read⟩

theorem Evaluation.push {ops : EvalOps W} {values : Values W} {nodes : List Node} {buffer : Array W}
    (valid : Evaluation ops values nodes buffer) (node : Node) (value : W)
    (evaluated : node.eval ops values buffer = some value) :
    Evaluation ops values (nodes ++ [node]) (buffer.push value) := by
  refine ⟨by simp only [Array.size_push, List.length_append, List.length_singleton, valid.size], ?_, ?_⟩
  · simp only [sweepFrom_append, valid.sweep, sweepFrom, evaluated, bind, Option.bind]
  · intro index old found
    by_cases bound : index < nodes.length
    · rw [List.getElem?_append_left bound] at found
      have bnd : index < buffer.size := by rw [valid.size]; exact bound
      have read := Array.getElem?_eq_getElem bnd
      have oldEval := (valid.cached index old found).trans read
      exact (eval_extends ops values (Extends.push buffer value) old oldEval).trans
        (Array.getElem?_push_lt bnd).symm
    · rw [List.getElem?_append_right (by omega)] at found
      have pos : index = nodes.length := by
        have bnd := (List.getElem?_eq_some_iff.mp found).1
        simp only [List.length_singleton] at bnd
        omega
      subst index
      simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at found
      subst old
      simpa only [← valid.size, Array.getElem?_push_size] using
        eval_extends ops values (Extends.push buffer value) node evaluated

def intern (nodes : List Node) (node : Node) : List Node × Nat :=
  match nodes.findIdx? (fun old => decide (old = node)) with
  | some index => (nodes, index)
  | none => (nodes ++ [node], nodes.length)

def asConst (nodes : List Node) (index : Nat) : Option G :=
  match nodes[index]? with
  | some (.konst value) => some value
  | _ => none

def Result (ops : EvalOps W) (values : Values W) (before : Array W)
    (result : List Node × Nat) (value : W) : Prop :=
  ∃ after, Evaluation ops values result.1 after ∧ Extends before after ∧ after[result.2]? = some value

theorem result_same {ops : EvalOps W} {values : Values W} {nodes : List Node} {buffer : Array W}
    (valid : Evaluation ops values nodes buffer) {index : Nat} {value : W}
    (read : buffer[index]? = some value) : Result ops values buffer (nodes, index) value :=
  ⟨buffer, valid, Extends.refl buffer, read⟩

theorem intern_reflects {ops : EvalOps W} {values : Values W} {nodes : List Node} {buffer : Array W}
    (valid : Evaluation ops values nodes buffer) (node : Node) {value : W}
    (evaluated : node.eval ops values buffer = some value) :
    Result ops values buffer (intern nodes node) value := by
  unfold intern
  split
  next index found =>
    obtain ⟨bound, equal, _⟩ := List.findIdx?_eq_some_iff_getElem.mp found
    simp only [decide_eq_true_eq] at equal
    have nodeRead : nodes[index]? = some node := by rw [List.getElem?_eq_getElem bound, equal]
    exact result_same valid ((valid.cached index node nodeRead).symm.trans evaluated)
  next =>
    exact ⟨buffer.push value, valid.push node value evaluated, Extends.push buffer value,
      by simp only [← valid.size, Array.getElem?_push_size]⟩

theorem asConst_reflects {ops : EvalOps W} {values : Values W} {nodes : List Node} {buffer : Array W}
    (valid : Evaluation ops values nodes buffer) {index : Nat} {constant : G}
    (found : asConst nodes index = some constant) : buffer[index]? = some (ops.konst constant) := by
  unfold asConst at found
  split at found
  next value nodeRead =>
    cases found
    exact (valid.cached index (.konst constant) nodeRead).symm
  next => cases found

theorem asConst_value {ops : EvalOps W} {values : Values W} {nodes : List Node} {buffer : Array W}
    (valid : Evaluation ops values nodes buffer) {index : Nat} {constant : G} {value : W}
    (found : asConst nodes index = some constant) (read : buffer[index]? = some value) :
    value = ops.konst constant := Option.some.inj (read.symm.trans (asConst_reflects valid found))

def neg (nodes : List Node) (a : Nat) : List Node × Nat :=
  match asConst nodes a with
  | some value => intern nodes (.konst (0 - value))
  | none => match nodes[a]? with
    | some (.neg inner) => (nodes, inner)
    | _ => intern nodes (.neg a)

def sortedAdd (nodes : List Node) (a b : Nat) : List Node × Nat :=
  intern nodes (if a ≤ b then .add a b else .add b a)

def sortedMul (nodes : List Node) (a b : Nat) : List Node × Nat :=
  intern nodes (if a ≤ b then .mul a b else .mul b a)

def add (nodes : List Node) (a b : Nat) : List Node × Nat :=
  match asConst nodes a, asConst nodes b with
  | some x, some y => intern nodes (.konst (x + y))
  | some x, none => if x == 0 then (nodes, b) else sortedAdd nodes a b
  | none, some y => if y == 0 then (nodes, a) else sortedAdd nodes a b
  | none, none => sortedAdd nodes a b

def sub (nodes : List Node) (a b : Nat) : List Node × Nat :=
  if a = b then intern nodes (.konst 0) else
  match asConst nodes a, asConst nodes b with
  | some x, some y => intern nodes (.konst (x - y))
  | none, some y => if y == 0 then (nodes, a) else intern nodes (.sub a b)
  | some x, none => if x == 0 then neg nodes b else intern nodes (.sub a b)
  | none, none => intern nodes (.sub a b)

def mul (nodes : List Node) (a b : Nat) : List Node × Nat :=
  match asConst nodes a, asConst nodes b with
  | some x, some y => intern nodes (.konst (x * y))
  | some x, none => if x == 0 then (nodes, a) else if x == 1 then (nodes, b) else sortedMul nodes a b
  | none, some y => if y == 0 then (nodes, b) else if y == 1 then (nodes, a) else sortedMul nodes a b
  | none, none => sortedMul nodes a b

theorem konst_reflects {ops : EvalOps W} {values : Values W} {nodes : List Node} {buffer : Array W}
    (valid : Evaluation ops values nodes buffer) (value : G) :
    Result ops values buffer (intern nodes (.konst value)) (ops.konst value) :=
  intern_reflects valid (.konst value) rfl

theorem neg_reflects {ops : EvalOps W} (laws : EvalLaws ops)
    {values : Values W} {nodes : List Node} {buffer : Array W}
    (valid : Evaluation ops values nodes buffer) {a : Nat} {value : W}
    (read : buffer[a]? = some value) : Result ops values buffer (neg nodes a) (ops.neg value) := by
  unfold neg
  split
  next constant found =>
    rw [asConst_value valid found read, ← laws.konst_neg]
    exact konst_reflects valid _
  next =>
    split
    next inner found =>
      have evaluated := (valid.cached a (.neg inner) found).trans read
      cases innerRead : buffer[inner]? with
      | none => simp only [Node.eval, innerRead, bind, Option.bind, reduceCtorEq] at evaluated
      | some child =>
        simp only [Node.eval, innerRead, bind, Option.bind, pure, Option.some.injEq] at evaluated
        rw [← evaluated, laws.neg_neg]
        exact result_same valid innerRead
    next =>
      exact intern_reflects valid (.neg a) (by simp only [Node.eval, read, bind, Option.bind, pure])

theorem sortedAdd_reflects {ops : EvalOps W} (laws : GraphEvalLaws ops)
    {values : Values W} {nodes : List Node} {buffer : Array W}
    (valid : Evaluation ops values nodes buffer) {a b : Nat} {left right : W}
    (leftRead : buffer[a]? = some left) (rightRead : buffer[b]? = some right) :
    Result ops values buffer (sortedAdd nodes a b) (ops.add left right) := by
  unfold sortedAdd
  split <;> apply intern_reflects valid <;>
    simp only [Node.eval, leftRead, rightRead, bind, Option.bind, pure]
  exact congrArg some (laws.add_comm right left)

theorem sortedMul_reflects {ops : EvalOps W} (laws : GraphEvalLaws ops)
    {values : Values W} {nodes : List Node} {buffer : Array W}
    (valid : Evaluation ops values nodes buffer) {a b : Nat} {left right : W}
    (leftRead : buffer[a]? = some left) (rightRead : buffer[b]? = some right) :
    Result ops values buffer (sortedMul nodes a b) (ops.mul left right) := by
  unfold sortedMul
  split <;> apply intern_reflects valid <;>
    simp only [Node.eval, leftRead, rightRead, bind, Option.bind, pure]
  exact congrArg some (laws.mul_comm right left)

theorem add_reflects {ops : EvalOps W} (laws : GraphEvalLaws ops)
    {values : Values W} {nodes : List Node} {buffer : Array W}
    (valid : Evaluation ops values nodes buffer) {a b : Nat} {left right : W}
    (leftRead : buffer[a]? = some left) (rightRead : buffer[b]? = some right) :
    Result ops values buffer (add nodes a b) (ops.add left right) := by
  cases ha : asConst nodes a <;> cases hb : asConst nodes b
  all_goals simp only [add, ha, hb]
  · exact sortedAdd_reflects laws valid leftRead rightRead
  · rename_i y
    split
    next zero =>
      have zero : y = 0 := beq_iff_eq.mp zero
      rw [asConst_value valid hb rightRead, zero, laws.add_zero]
      exact result_same valid leftRead
    next => exact sortedAdd_reflects laws valid leftRead rightRead
  · rename_i x
    split
    next zero =>
      have zero : x = 0 := beq_iff_eq.mp zero
      rw [asConst_value valid ha leftRead, zero, laws.zero_add]
      exact result_same valid rightRead
    next => exact sortedAdd_reflects laws valid leftRead rightRead
  · rw [asConst_value valid ha leftRead, asConst_value valid hb rightRead, ← laws.konst_add]
    exact konst_reflects valid _

theorem sub_reflects {ops : EvalOps W} (laws : GraphEvalLaws ops)
    {values : Values W} {nodes : List Node} {buffer : Array W}
    (valid : Evaluation ops values nodes buffer) {a b : Nat} {left right : W}
    (leftRead : buffer[a]? = some left) (rightRead : buffer[b]? = some right) :
    Result ops values buffer (sub nodes a b) (ops.sub left right) := by
  have raw : Result ops values buffer (intern nodes (.sub a b)) (ops.sub left right) :=
    intern_reflects valid (.sub a b) (by simp only [Node.eval, leftRead, rightRead, bind, Option.bind, pure])
  unfold sub
  split
  next equal =>
    subst b
    have equal := Option.some.inj (leftRead.symm.trans rightRead)
    rw [equal, laws.sub_self]
    exact konst_reflects valid _
  next =>
    cases ha : asConst nodes a <;> cases hb : asConst nodes b
    all_goals dsimp only
    · exact raw
    · rename_i y
      split
      next zero =>
        have zero : y = 0 := beq_iff_eq.mp zero
        rw [asConst_value valid hb rightRead, zero, laws.sub_zero]
        exact result_same valid leftRead
      next => exact raw
    · rename_i x
      split
      next zero =>
        have zero : x = 0 := beq_iff_eq.mp zero
        rw [asConst_value valid ha leftRead, zero, laws.zero_sub]
        exact neg_reflects laws.toEvalLaws valid rightRead
      next => exact raw
    · rw [asConst_value valid ha leftRead, asConst_value valid hb rightRead, ← laws.konst_sub]
      exact konst_reflects valid _

theorem mul_reflects {ops : EvalOps W} (laws : GraphEvalLaws ops)
    {values : Values W} {nodes : List Node} {buffer : Array W}
    (valid : Evaluation ops values nodes buffer) {a b : Nat} {left right : W}
    (leftRead : buffer[a]? = some left) (rightRead : buffer[b]? = some right) :
    Result ops values buffer (mul nodes a b) (ops.mul left right) := by
  cases ha : asConst nodes a <;> cases hb : asConst nodes b
  all_goals simp only [mul, ha, hb]
  · exact sortedMul_reflects laws valid leftRead rightRead
  · rename_i y
    split
    next zero =>
      have zero : y = 0 := beq_iff_eq.mp zero
      rw [asConst_value valid hb rightRead, zero, laws.mul_zero]
      exact result_same valid (by simpa only [zero] using asConst_reflects valid hb)
    next =>
      split
      next one =>
        have one : y = 1 := beq_iff_eq.mp one
        rw [asConst_value valid hb rightRead, one, laws.mul_one]
        exact result_same valid leftRead
      next => exact sortedMul_reflects laws valid leftRead rightRead
  · rename_i x
    split
    next zero =>
      have zero : x = 0 := beq_iff_eq.mp zero
      rw [asConst_value valid ha leftRead, zero, laws.zero_mul]
      exact result_same valid (by simpa only [zero] using asConst_reflects valid ha)
    next =>
      split
      next one =>
        have one : x = 1 := beq_iff_eq.mp one
        rw [asConst_value valid ha leftRead, one, laws.one_mul]
        exact result_same valid rightRead
      next => exact sortedMul_reflects laws valid leftRead rightRead
  · rw [asConst_value valid ha leftRead, asConst_value valid hb rightRead, ← laws.konst_mul]
    exact konst_reflects valid _

def compileExpr (widths : GraphWidths) (allowStage2 : Bool) : Expr → List Node → Option (List Node × Nat)
  | .konst value, nodes => some (intern nodes (.konst value))
  | .var column, nodes =>
    if (column.source != .stage2 || allowStage2) && column.index < widths.width column.source then
      some (intern nodes (.var column))
    else none
  | .publicInput index, nodes =>
    if index < widths.publics then some (intern nodes (.publicInput index)) else none
  | .isFirstRow, nodes => some (intern nodes .isFirstRow)
  | .isLastRow, nodes => some (intern nodes .isLastRow)
  | .isTransition, nodes => some (intern nodes .isTransition)
  | .add left right, nodes => do
    let (nodes, a) ← compileExpr widths allowStage2 left nodes
    let (nodes, b) ← compileExpr widths allowStage2 right nodes
    return add nodes a b
  | .sub left right, nodes => do
    let (nodes, a) ← compileExpr widths allowStage2 left nodes
    let (nodes, b) ← compileExpr widths allowStage2 right nodes
    return sub nodes a b
  | .mul left right, nodes => do
    let (nodes, a) ← compileExpr widths allowStage2 left nodes
    let (nodes, b) ← compileExpr widths allowStage2 right nodes
    return mul nodes a b
  | .neg child, nodes => do
    let (nodes, a) ← compileExpr widths allowStage2 child nodes
    return neg nodes a

theorem result_prepend {ops : EvalOps W} {values : Values W} {before middle : Array W}
    (growth : Extends before middle) {result : List Node × Nat} {value : W}
    (reflected : Result ops values middle result value) : Result ops values before result value := by
  obtain ⟨after, valid, rest, read⟩ := reflected
  exact ⟨after, valid, growth.trans rest, read⟩

theorem compileExpr_reflects {ops : EvalOps W} (laws : GraphEvalLaws ops)
    {values : Values W} {widths : GraphWidths} (fits : values.Fits widths)
    (allowStage2 : Bool) (expr : Expr) {nodes : List Node} {buffer : Array W}
    (valid : Evaluation ops values nodes buffer) {result : List Node × Nat}
    (compiled : compileExpr widths allowStage2 expr nodes = some result) :
    ∃ value, expr.eval ops values = some value ∧ Result ops values buffer result value := by
  induction expr generalizing nodes buffer result with
  | konst value =>
    cases compiled
    exact ⟨_, rfl, konst_reflects valid value⟩
  | var column =>
    simp only [compileExpr] at compiled
    split at compiled
    next accepted =>
      cases compiled
      have bound : column.index < (values.columns column.source column.offset).size := by
        rw [fits.1]
        simp only [Bool.and_eq_true, decide_eq_true_eq] at accepted
        exact accepted.2
      have read := Array.getElem?_eq_getElem bound
      exact ⟨_, read, intern_reflects valid (.var column) read⟩
    next => cases compiled
  | publicInput index =>
    simp only [compileExpr] at compiled
    split at compiled
    next bound =>
      cases compiled
      have bound : index < values.publics.size := by rw [fits.2]; exact bound
      have read := Array.getElem?_eq_getElem bound
      exact ⟨_, read, intern_reflects valid (.publicInput index) read⟩
    next => cases compiled
  | isFirstRow | isLastRow | isTransition =>
    cases compiled
    exact ⟨_, rfl, intern_reflects valid _ rfl⟩
  | add left right ihLeft ihRight | sub left right ihLeft ihRight | mul left right ihLeft ihRight =>
    simp only [compileExpr] at compiled
    cases leftCompiled : compileExpr widths allowStage2 left nodes with
    | none => simp only [leftCompiled, bind, Option.bind, reduceCtorEq] at compiled
    | some leftResult =>
      cases rightCompiled : compileExpr widths allowStage2 right leftResult.1 with
      | none => simp only [leftCompiled, rightCompiled, bind, Option.bind, reduceCtorEq] at compiled
      | some rightResult =>
        simp only [leftCompiled, rightCompiled, bind, Option.bind, pure, Option.some.injEq] at compiled
        subst result
        obtain ⟨leftValue, leftEval, leftBuffer, leftValid, leftGrowth, leftRead⟩ := ihLeft valid leftCompiled
        obtain ⟨rightValue, rightEval, rightBuffer, rightValid, rightGrowth, rightRead⟩ := ihRight leftValid rightCompiled
        simp only [Expr.eval, leftEval, rightEval, bind, Option.bind, pure, Option.some.injEq]
        refine ⟨_, rfl, result_prepend (leftGrowth.trans rightGrowth) ?_⟩
        first
        | exact add_reflects laws rightValid (rightGrowth _ _ leftRead) rightRead
        | exact sub_reflects laws rightValid (rightGrowth _ _ leftRead) rightRead
        | exact mul_reflects laws rightValid (rightGrowth _ _ leftRead) rightRead
  | neg child ih =>
    simp only [compileExpr] at compiled
    cases childCompiled : compileExpr widths allowStage2 child nodes with
    | none => simp only [childCompiled, bind, Option.bind, reduceCtorEq] at compiled
    | some childResult =>
      simp only [childCompiled, bind, Option.bind, pure, Option.some.injEq] at compiled
      subst result
      obtain ⟨value, evaluated, childBuffer, childValid, growth, read⟩ := ih valid childCompiled
      exact ⟨ops.neg value, by simp only [Expr.eval, evaluated, bind, Option.bind, pure],
        result_prepend growth (neg_reflects laws.toEvalLaws childValid read)⟩

theorem compileExpr_sweep {ops : EvalOps W} (laws : GraphEvalLaws ops)
    {values : Values W} {widths : GraphWidths} (fits : values.Fits widths)
    (allowStage2 : Bool) (expr : Expr) {result : List Node × Nat}
    (compiled : compileExpr widths allowStage2 expr [] = some result) :
    ∃ buffer, sweepFrom ops values result.1 #[] = some buffer ∧
      buffer[result.2]? = expr.eval ops values := by
  obtain ⟨value, evaluated, buffer, valid, _, read⟩ :=
    compileExpr_reflects laws fits allowStage2 expr (Evaluation.empty ops values) compiled
  exact ⟨buffer, valid.sweep, read.trans evaluated.symm⟩

def compileExprs (widths : GraphWidths) (allowStage2 : Bool) :
    List Expr → List Node → Option (List Node × List Nat)
  | [], nodes => some (nodes, [])
  | expr :: exprs, nodes => do
    let (nodes, root) ← compileExpr widths allowStage2 expr nodes
    let (nodes, roots) ← compileExprs widths allowStage2 exprs nodes
    return (nodes, root :: roots)

inductive RootsReflect (ops : EvalOps W) (values : Values W) (buffer : Array W) :
    List Nat → List Expr → Prop where
  | nil : RootsReflect ops values buffer [] []
  | cons {root : Nat} {expr : Expr} {roots : List Nat} {exprs : List Expr}
      (head : ∃ value, expr.eval ops values = some value ∧ buffer[root]? = some value)
      (tail : RootsReflect ops values buffer roots exprs) :
      RootsReflect ops values buffer (root :: roots) (expr :: exprs)

theorem RootsReflect.grow {ops : EvalOps W} {values : Values W} {before after : Array W}
    (growth : Extends before after) {roots : List Nat} {exprs : List Expr}
    (reflected : RootsReflect ops values before roots exprs) : RootsReflect ops values after roots exprs := by
  induction reflected with
  | nil => exact .nil
  | cons head _ ih =>
    obtain ⟨value, evaluated, read⟩ := head
    exact .cons ⟨value, evaluated, growth _ _ read⟩ ih

theorem compileExprs_reflects {ops : EvalOps W} (laws : GraphEvalLaws ops)
    {values : Values W} {widths : GraphWidths} (fits : values.Fits widths)
    (allowStage2 : Bool) (exprs : List Expr) {nodes : List Node} {buffer : Array W}
    (valid : Evaluation ops values nodes buffer) {result : List Node × List Nat}
    (compiled : compileExprs widths allowStage2 exprs nodes = some result) :
    ∃ after, Evaluation ops values result.1 after ∧ Extends buffer after ∧
      RootsReflect ops values after result.2 exprs := by
  induction exprs generalizing nodes buffer result with
  | nil => cases compiled; exact ⟨buffer, valid, Extends.refl buffer, .nil⟩
  | cons expr exprs ih =>
    simp only [compileExprs] at compiled
    cases headCompiled : compileExpr widths allowStage2 expr nodes with
    | none => simp only [headCompiled, bind, Option.bind, reduceCtorEq] at compiled
    | some headResult =>
      cases restCompiled : compileExprs widths allowStage2 exprs headResult.1 with
      | none => simp only [headCompiled, restCompiled, bind, Option.bind, reduceCtorEq] at compiled
      | some restResult =>
        simp only [headCompiled, restCompiled, bind, Option.bind, pure, Option.some.injEq] at compiled
        subst result
        obtain ⟨value, evaluated, middle, middleValid, growth, read⟩ :=
          compileExpr_reflects laws fits allowStage2 expr valid headCompiled
        obtain ⟨after, afterValid, restGrowth, reflected⟩ := ih middleValid restCompiled
        exact ⟨after, afterValid, growth.trans restGrowth, .cons ⟨value, evaluated, restGrowth _ _ read⟩ reflected⟩

def evalExprs (ops : EvalOps W) (values : Values W) (exprs : List Expr) : Option (List W) :=
  exprs.mapM (Expr.eval ops values)

theorem RootsReflect.read {ops : EvalOps W} {values : Values W} {buffer : Array W}
    {roots : List Nat} {exprs : List Expr} (reflected : RootsReflect ops values buffer roots exprs) :
    ∃ result, evalExprs ops values exprs = some result ∧ readNodes buffer roots = some result := by
  induction reflected with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons head _ ih =>
    obtain ⟨value, evaluated, read⟩ := head
    obtain ⟨rest, restEval, restRead⟩ := ih
    refine ⟨value :: rest, ?_, ?_⟩
    · simp only [evalExprs, List.mapM_cons, evaluated, bind, Option.bind]
      change (evalExprs ops values _).bind _ = _
      rw [restEval]; rfl
    · simp only [readNodes, List.mapM_cons, read, bind, Option.bind]
      change (readNodes buffer _).bind _ = _
      rw [restRead]; rfl

structure ExprLookup where
  multiplicity : Expr
  args : List Expr
  deriving DecidableEq, Repr

def ExprLookup.exprs (lookup : ExprLookup) : List Expr := lookup.multiplicity :: lookup.args

def ExprLookup.eval (ops : EvalOps W) (values : Values W) (lookup : ExprLookup) : Option (W × List W) := do
  let multiplicity ← lookup.multiplicity.eval ops values
  let args ← evalExprs ops values lookup.args
  return (multiplicity, args)

def compileLookup (widths : GraphWidths) (lookup : ExprLookup) (nodes : List Node) :
    Option (List Node × Lookup) := do
  let (nodes, roots) ← compileExprs widths false lookup.exprs nodes
  match roots with
  | [] => none
  | root :: roots => return (nodes, ⟨root, roots⟩)

theorem compileLookup_reflects {ops : EvalOps W} (laws : GraphEvalLaws ops)
    {values : Values W} {widths : GraphWidths} (fits : values.Fits widths)
    (lookup : ExprLookup) {nodes : List Node} {buffer : Array W}
    (valid : Evaluation ops values nodes buffer) {result : List Node × Lookup}
    (compiled : compileLookup widths lookup nodes = some result) :
    ∃ after, Evaluation ops values result.1 after ∧ Extends buffer after ∧
      RootsReflect ops values after result.2.roots lookup.exprs := by
  simp only [compileLookup] at compiled
  cases exprsCompiled : compileExprs widths false lookup.exprs nodes with
  | none => simp only [exprsCompiled, bind, Option.bind, reduceCtorEq] at compiled
  | some rootsResult =>
    obtain ⟨after, afterValid, growth, reflected⟩ := compileExprs_reflects laws fits false lookup.exprs valid exprsCompiled
    cases rootsResult with
    | mk nodes roots =>
      cases roots with
      | nil => simp only [exprsCompiled, bind, Option.bind, reduceCtorEq] at compiled
      | cons root roots =>
        simp only [exprsCompiled, bind, Option.bind, pure, Option.some.injEq] at compiled
        subst result
        exact ⟨after, afterValid, growth, reflected⟩

theorem RootsReflect.readLookup {ops : EvalOps W} {values : Values W} {buffer : Array W}
    {lookup : Lookup} {exprs : ExprLookup}
    (reflected : RootsReflect ops values buffer lookup.roots exprs.exprs) :
    ∃ read, exprs.eval ops values = some read ∧ readLookup buffer lookup = some read := by
  cases reflected with
  | cons head tail =>
    obtain ⟨multiplicity, multiplicityEval, multiplicityRead⟩ := head
    obtain ⟨args, argsEval, argsRead⟩ := RootsReflect.read tail
    exact ⟨(multiplicity, args),
      by simp only [ExprLookup.eval, multiplicityEval, argsEval, bind, Option.bind, pure],
      by simp only [Aiur.NativeAIR.readLookup, multiplicityRead, argsRead, bind, Option.bind, pure]⟩

def compileLookups (widths : GraphWidths) : List ExprLookup → List Node → Option (List Node × List Lookup)
  | [], nodes => some (nodes, [])
  | lookup :: lookups, nodes => do
    let (nodes, root) ← compileLookup widths lookup nodes
    let (nodes, roots) ← compileLookups widths lookups nodes
    return (nodes, root :: roots)

inductive LookupsReflect (ops : EvalOps W) (values : Values W) (buffer : Array W) :
    List Lookup → List ExprLookup → Prop where
  | nil : LookupsReflect ops values buffer [] []
  | cons {lookup : Lookup} {expr : ExprLookup} {lookups : List Lookup} {exprs : List ExprLookup}
      (head : RootsReflect ops values buffer lookup.roots expr.exprs)
      (tail : LookupsReflect ops values buffer lookups exprs) :
      LookupsReflect ops values buffer (lookup :: lookups) (expr :: exprs)

theorem LookupsReflect.grow {ops : EvalOps W} {values : Values W} {before after : Array W}
    (growth : Extends before after) {lookups : List Lookup} {exprs : List ExprLookup}
    (reflected : LookupsReflect ops values before lookups exprs) : LookupsReflect ops values after lookups exprs := by
  induction reflected with
  | nil => exact .nil
  | cons head _ ih => exact .cons (head.grow growth) ih

theorem compileLookups_reflects {ops : EvalOps W} (laws : GraphEvalLaws ops)
    {values : Values W} {widths : GraphWidths} (fits : values.Fits widths)
    (lookups : List ExprLookup) {nodes : List Node} {buffer : Array W}
    (valid : Evaluation ops values nodes buffer) {result : List Node × List Lookup}
    (compiled : compileLookups widths lookups nodes = some result) :
    ∃ after, Evaluation ops values result.1 after ∧ Extends buffer after ∧
      LookupsReflect ops values after result.2 lookups := by
  induction lookups generalizing nodes buffer result with
  | nil => cases compiled; exact ⟨buffer, valid, Extends.refl buffer, .nil⟩
  | cons lookup lookups ih =>
    simp only [compileLookups] at compiled
    cases headCompiled : compileLookup widths lookup nodes with
    | none => simp only [headCompiled, bind, Option.bind, reduceCtorEq] at compiled
    | some headResult =>
      cases restCompiled : compileLookups widths lookups headResult.1 with
      | none => simp only [headCompiled, restCompiled, bind, Option.bind, reduceCtorEq] at compiled
      | some restResult =>
        simp only [headCompiled, restCompiled, bind, Option.bind, pure, Option.some.injEq] at compiled
        subst result
        obtain ⟨middle, middleValid, growth, reflected⟩ := compileLookup_reflects laws fits lookup valid headCompiled
        obtain ⟨after, afterValid, restGrowth, restReflected⟩ := ih middleValid restCompiled
        exact ⟨after, afterValid, growth.trans restGrowth, .cons (reflected.grow restGrowth) restReflected⟩

def recordZero (nodes : List Node) (root : Nat) : Option (List Nat) :=
  match asConst nodes root with
  | none => some [root]
  | some value => if value == 0 then some [] else none

def Vanishes (ops : EvalOps W) (buffer : Array W) (roots : List Nat) : Prop :=
  ∀ root ∈ roots, buffer[root]? = some (ops.konst 0)

def ExprsVanish (ops : EvalOps W) (values : Values W) (exprs : List Expr) : Prop :=
  ∀ expr ∈ exprs, expr.eval ops values = some (ops.konst 0)

theorem recordZero_reflects {ops : EvalOps W} {values : Values W} {nodes : List Node} {buffer after : Array W}
    (valid : Evaluation ops values nodes buffer) (growth : Extends buffer after) {root : Nat} {value : W}
    (read : buffer[root]? = some value) {roots : List Nat} (recorded : recordZero nodes root = some roots) :
    Vanishes ops after roots ↔ value = ops.konst 0 := by
  unfold recordZero at recorded
  cases found : asConst nodes root with
  | none =>
    simp only [found, Option.some.injEq] at recorded
    subst roots
    simp only [Vanishes, List.mem_singleton, forall_eq, growth root value read, Option.some.injEq]
  | some constant =>
    simp only [found] at recorded
    split at recorded
    next zero =>
      have zero : constant = 0 := beq_iff_eq.mp zero
      cases recorded
      rw [asConst_value valid found read, zero]
      simp only [Vanishes, List.not_mem_nil, false_implies, forall_const, iff_self]
    next => cases recorded

theorem Vanishes.append (ops : EvalOps W) (buffer : Array W) (left right : List Nat) :
    Vanishes ops buffer (left ++ right) ↔ Vanishes ops buffer left ∧ Vanishes ops buffer right := by
  simp only [Vanishes, List.mem_append, or_imp, forall_and]

theorem ExprsVanish.cons (ops : EvalOps W) (values : Values W) (head : Expr) (tail : List Expr) :
    ExprsVanish ops values (head :: tail) ↔ head.eval ops values = some (ops.konst 0) ∧ ExprsVanish ops values tail := by
  simp only [ExprsVanish, List.forall_mem_cons]

def compileZeros (widths : GraphWidths) : List Expr → List Node → Option (List Node × List Nat)
  | [], nodes => some (nodes, [])
  | expr :: exprs, nodes => do
    let (nodes, root) ← compileExpr widths false expr nodes
    let head ← recordZero nodes root
    let (nodes, roots) ← compileZeros widths exprs nodes
    return (nodes, head ++ roots)

theorem compileZeros_reflects {ops : EvalOps W} (laws : GraphEvalLaws ops)
    {values : Values W} {widths : GraphWidths} (fits : values.Fits widths)
    (exprs : List Expr) {nodes : List Node} {buffer : Array W}
    (valid : Evaluation ops values nodes buffer) {result : List Node × List Nat}
    (compiled : compileZeros widths exprs nodes = some result) :
    ∃ after, Evaluation ops values result.1 after ∧ Extends buffer after ∧
      (Vanishes ops after result.2 ↔ ExprsVanish ops values exprs) := by
  induction exprs generalizing nodes buffer result with
  | nil =>
    cases compiled
    exact ⟨buffer, valid, Extends.refl buffer, by constructor <;> intro _ _ member <;> cases member⟩
  | cons expr exprs ih =>
    simp only [compileZeros] at compiled
    cases headCompiled : compileExpr widths false expr nodes with
    | none => simp only [headCompiled, bind, Option.bind, reduceCtorEq] at compiled
    | some headResult =>
      cases recorded : recordZero headResult.1 headResult.2 with
      | none => simp only [headCompiled, recorded, bind, Option.bind, reduceCtorEq] at compiled
      | some headRoots =>
        cases restCompiled : compileZeros widths exprs headResult.1 with
        | none => simp only [headCompiled, recorded, restCompiled, bind, Option.bind, reduceCtorEq] at compiled
        | some restResult =>
          simp only [headCompiled, recorded, restCompiled, bind, Option.bind, pure, Option.some.injEq] at compiled
          subst result
          obtain ⟨value, evaluated, middle, middleValid, growth, read⟩ := compileExpr_reflects laws fits false expr valid headCompiled
          obtain ⟨after, afterValid, restGrowth, reflected⟩ := ih middleValid restCompiled
          refine ⟨after, afterValid, growth.trans restGrowth, ?_⟩
          rw [Vanishes.append, recordZero_reflects middleValid restGrowth read recorded, reflected,
            ExprsVanish.cons, evaluated, Option.some.injEq]

def canonicalZeros (roots : List Nat) : List Nat :=
  (roots.mergeSort (· ≤ ·)).eraseDups

theorem canonicalZeros_vanish (ops : EvalOps W) (buffer : Array W) (roots : List Nat) :
    Vanishes ops buffer (canonicalZeros roots) ↔ Vanishes ops buffer roots := by
  simp only [Vanishes, canonicalZeros, List.mem_eraseDups, List.mem_mergeSort]

structure BaseCompilation where
  graph : Graph
  lookupEnd : Nat
  deriving DecidableEq, Repr

def compileBase (widths : GraphWidths) (lookups : List ExprLookup) (constraints : List Expr) :
    Option BaseCompilation := do
  let (lookupNodes, lookups) ← compileLookups widths lookups []
  let (nodes, zeros) ← compileZeros widths constraints lookupNodes
  return ⟨⟨nodes, canonicalZeros zeros, lookups⟩, lookupNodes.length⟩

theorem compileBase_reflects {ops : EvalOps W} (laws : GraphEvalLaws ops)
    {values : Values W} {widths : GraphWidths} (fits : values.Fits widths)
    (lookups : List ExprLookup) (constraints : List Expr) {result : BaseCompilation}
    (compiled : compileBase widths lookups constraints = some result) :
    ∃ buffer, result.graph.sweep ops values = some buffer ∧
      LookupsReflect ops values buffer result.graph.lookups lookups ∧
      (Vanishes ops buffer result.graph.zeros ↔ ExprsVanish ops values constraints) := by
  simp only [compileBase] at compiled
  cases lookupsCompiled : compileLookups widths lookups [] with
  | none => simp only [lookupsCompiled, bind, Option.bind, reduceCtorEq] at compiled
  | some lookupResult =>
    cases zerosCompiled : compileZeros widths constraints lookupResult.1 with
    | none => simp only [lookupsCompiled, zerosCompiled, bind, Option.bind, reduceCtorEq] at compiled
    | some zeroResult =>
      simp only [lookupsCompiled, zerosCompiled, bind, Option.bind, pure, Option.some.injEq] at compiled
      subst result
      obtain ⟨middle, middleValid, _, lookupsReflected⟩ :=
        compileLookups_reflects laws fits lookups (Evaluation.empty ops values) lookupsCompiled
      obtain ⟨buffer, bufferValid, growth, zerosReflected⟩ :=
        compileZeros_reflects laws fits constraints middleValid zerosCompiled
      exact ⟨buffer, bufferValid.sweep, lookupsReflected.grow growth,
        (canonicalZeros_vanish ops buffer zeroResult.2).trans zerosReflected⟩

theorem LookupsReflect.read {ops : EvalOps W} {values : Values W} {buffer : Array W}
    {lookups : List Lookup} {exprs : List ExprLookup}
    (reflected : LookupsReflect ops values buffer lookups exprs) :
    ∃ result, exprs.mapM (ExprLookup.eval ops values) = some result ∧
      lookups.mapM (readLookup buffer) = some result := by
  induction reflected with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons head _ ih =>
    obtain ⟨value, evaluated, read⟩ := head.readLookup
    obtain ⟨rest, restEval, restRead⟩ := ih
    exact ⟨value :: rest,
      by simp only [List.mapM_cons, evaluated, restEval, bind, Option.bind, pure],
      by simp only [List.mapM_cons, read, restRead, bind, Option.bind, pure]⟩

theorem compileBase_satisfaction {ops : EvalOps W} (laws : GraphEvalLaws ops)
    {values : Values W} {widths : GraphWidths} (fits : values.Fits widths)
    (lookups : List ExprLookup) (constraints : List Expr) {result : BaseCompilation}
    (compiled : compileBase widths lookups constraints = some result) {buffer : Array W}
    (swept : result.graph.sweep ops values = some buffer) :
    (Vanishes ops buffer result.graph.zeros ↔ ExprsVanish ops values constraints) ∧
      result.graph.lookups.mapM (readLookup buffer) = lookups.mapM (ExprLookup.eval ops values) := by
  obtain ⟨actual, actualSweep, lookupsReflected, zerosReflected⟩ := compileBase_reflects laws fits lookups constraints compiled
  have equal := Option.some.inj (actualSweep.symm.trans swept)
  subst actual
  obtain ⟨reads, exprReads, graphReads⟩ := lookupsReflected.read
  exact ⟨zerosReflected, graphReads.trans exprReads.symm⟩

end Compiler
end NativeAIR
end Aiur
