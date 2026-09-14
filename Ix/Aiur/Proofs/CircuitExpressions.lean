/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.BlockLookups
import Ix.Aiur.Proofs.CircuitRows

/-!
Symbolic function-circuit emission, preserving the native ordering of member
constraints and shared lookup contributions. Members restart auxiliary and
lookup cursors while their selector tables occupy consecutive regions.
-/

namespace Aiur.NativeAIR.CircuitEmitter
open OpEmitter LookupEmitter BlockEmitter Compiler

def selectorExprs (base count : Nat) : Array Expr :=
  Array.ofFn fun index : Fin count => (mainCurrent (base + index.val)).expr

theorem selectorExprs_reads {values : Values G} (row : Nat → G) (base count : Nat)
    (reads : ∀ index < count,
      (values.columns .main .current)[base + index]? = some (row (base + index))) :
    SelectorReads values (selectorExprs base count) (fun index => row (base + index)) := by
  intro index expr present
  have bound : index < count := by
    have bound := (Array.getElem?_eq_some_iff.mp present).choose
    simpa only [selectorExprs, Array.size_ofFn] using bound
  have equal : (selectorExprs base count)[index]? = some (mainCurrent (base + index)).expr := by
    simp only [selectorExprs, Array.getElem?_ofFn, bound, dif_pos]
  rw [equal] at present
  cases present
  exact reads index bound

structure Member where
  functionIndex : Nat
  function : Bytecode.Function
  selectorBase : Nat
  entry : Expr
  body : BlockEmitter.Emission

def Member.readBound (member : Member) : Nat :=
  max member.function.layout.inputSize
    (max (member.selectorBase + member.function.layout.selectors) member.body.column)

def Member.eval (values : Values G) (member : Member) : Option AIR.MemberEmission := do
  let body ← member.body.eval values
  return ⟨member.functionIndex, member.function, member.selectorBase, body⟩

theorem Member.eval_of {values : Values G} {member : Member} {body : AIR.BlockEmission}
    (evaluated : member.body.eval values = some body) :
    member.eval values = some ⟨member.functionIndex, member.function, member.selectorBase, body⟩ := by
  simp only [Member.eval, evaluated, bind, Option.bind_some, pure]

theorem Member.eval_components {values : Values G} {member : Member} {result : AIR.MemberEmission}
    (evaluated : member.eval values = some result) :
    member.functionIndex = result.functionIndex ∧ member.function = result.function ∧
    member.selectorBase = result.selectorBase ∧ member.body.eval values = some result.body := by
  simp only [Member.eval, bind, Option.bind] at evaluated
  split at evaluated
  · cases evaluated
  rename_i body bodyEval
  cases evaluated
  exact ⟨rfl, rfl, rfl, bodyEval⟩

def emitMember (rank : Expr) (column lookup selectorBase : Nat)
    (program : Bytecode.Toplevel) (functionIndex : Nat)
    (callRanks : Array Bytecode.CallRank := #[]) : Option Member := do
  let function ← program.functions[functionIndex]?
  let selectors := selectorExprs selectorBase function.layout.selectors
  let entry ← blockSelector selectors function.body
  let body ← emitBlock selectors ⟨functionIndex, function.layout.inputSize, rank, callRanks⟩ entry
    (advice 0 function.layout.inputSize) column lookup function.body
  return ⟨functionIndex, function, selectorBase, entry, body⟩

def emitMembers (rank : Expr) (column lookup selectorBase : Nat)
    (program : Bytecode.Toplevel) : List Nat → Option (List Member)
  | [] => some []
  | index :: indices => do
    let member ← emitMember rank column lookup selectorBase program index
    let rest ← emitMembers rank column lookup (selectorBase + member.function.layout.selectors) program indices
    return member :: rest

def rankBytes (layout : Bytecode.FunctionLayout) : Fin 6 → Expr :=
  fun index => (mainCurrent (layout.inputSize + layout.selectors + 1 + index.val)).expr

def selectorEquations (layout : Bytecode.FunctionLayout) : List Expr :=
  (List.range layout.selectors).map fun index =>
    let selector := (mainCurrent (layout.inputSize + index)).expr
    selector.frontMul (selector.frontSub (.konst 1))

theorem selectorEquations_eval {values : Values G} (row : Nat → G) (layout : Bytecode.FunctionLayout)
    (reads : ∀ index < layout.selectors,
      (values.columns .main .current)[layout.inputSize + index]? = some (row (layout.inputSize + index))) :
    (selectorEquations layout).mapM (evalExpr values) = some
      ((List.range layout.selectors).map fun index => AIR.booleanConstraint (row (layout.inputSize + index))) := by
  apply list_mapM_of_map
  intro index member
  have evaluated : evalExpr values (mainCurrent (layout.inputSize + index)).expr =
      some (row (layout.inputSize + index)) := reads index (List.mem_range.mp member)
  exact Expr.frontMul_eval goldilocksLaws values evaluated
    (Expr.frontSub_eval goldilocksLaws values evaluated rfl)

structure Emission where
  members : List Member
  selector : Expr
  multiplicity : Expr
  rankBytes : Fin 6 → Expr
  width : Nat
  selectorStart : Nat
  selectorCount : Nat
  lookupCount : Nat
  branchless : Bool
  equations : List Expr
  queries : List QueryExpr
  returns : List ReturnExpr

def Emission.readBound (emission : Emission) : Nat :=
  emission.members.foldl (fun bound member => max bound member.readBound)
    (emission.selectorStart + emission.selectorCount + 1 + 6)

def circuitEmission (circuit : Bytecode.Circuit) (members : List Member) : Emission :=
  let selector := sum (members.map (·.entry))
  let multiplicity := (mainCurrent (circuit.layout.inputSize + circuit.layout.selectors)).expr
  let bytes := rankBytes circuit.layout
  { members, selector, multiplicity, rankBytes := bytes
    width := circuit.layout.width
    selectorStart := circuit.layout.inputSize
    selectorCount := circuit.layout.selectors
    lookupCount := circuit.layout.lookups
    branchless := Bytecode.circuitBranchless circuit.layout.selectors (members.map (·.function))
    equations := members.flatMap (·.body.equations) ++ selectorEquations circuit.layout ++
      (if 1 < circuit.members.size then [selector.frontMul ((Expr.konst 1).frontSub selector)] else []) ++
      [multiplicity.frontMul ((Expr.konst 1).frontSub selector)]
    queries := members.flatMap (·.body.queries) ++
      (if members.isEmpty then [] else queryParts 1 selector (rangeSix bytes))
    returns := members.flatMap (·.body.returns) }

def emitCircuit (program : Bytecode.Toplevel) (circuit : Bytecode.Circuit) : Option Emission := do
  let rank := packSix (rankBytes circuit.layout)
  let column := circuit.layout.inputSize + circuit.layout.selectors + 1 + 6
  let members ← emitMembers rank column 4 circuit.layout.inputSize program circuit.members.toList
  return circuitEmission circuit members

def Emission.lookup (emission : Emission) (slot : Nat) : ExprLookup :=
  if slot = 0 then ⟨emission.multiplicity.frontNeg, returnArgs emission.branchless emission.returns⟩
  else LookupEmitter.slot emission.branchless emission.queries slot

def Emission.lookups (emission : Emission) : List ExprLookup :=
  List.ofFn fun slot : Fin emission.lookupCount => emission.lookup slot.val

def evalFin (values : Values G) (expressions : Fin size → Expr) : Option (Fin size → G) := do
  let results ← (Array.ofFn expressions).mapM (evalExpr values)
  return fun index => results[index.val]?.getD 0

theorem evalFin_of {values : Values G} {expressions : Fin size → Expr} {results : Fin size → G}
    (evaluated : ∀ index, evalExpr values (expressions index) = some (results index)) :
    evalFin values expressions = some results := by
  have arrayEval := array_mapM_ofFn expressions results (evalExpr values) evaluated
  simp only [evalFin, arrayEval, bind, Option.bind_some, pure]
  congr 1
  funext index
  simp only [Array.getElem?_ofFn, index.isLt, dif_pos, Option.getD_some]

theorem evalFin_components {values : Values G} {expressions : Fin size → Expr} {results : Fin size → G}
    (evaluated : evalFin values expressions = some results) :
    ∀ index, evalExpr values (expressions index) = some (results index) := by
  simp only [evalFin, bind, Option.bind] at evaluated
  split at evaluated
  · cases evaluated
  rename_i array arrayEval
  cases evaluated
  intro index
  apply evaluated_read arrayEval
  simp only [Array.getElem?_ofFn, index.isLt, dif_pos]

def Emission.eval (values : Values G) (emission : Emission) : Option AIR.CircuitEmission := do
  let members ← emission.members.mapM (Member.eval values)
  let selector ← evalExpr values emission.selector
  let multiplicity ← evalExpr values emission.multiplicity
  let rankBytes ← evalFin values emission.rankBytes
  let equations ← emission.equations.mapM (evalExpr values)
  let queries ← emission.queries.mapM (QueryExpr.eval values)
  let returns ← emission.returns.mapM (ReturnExpr.eval values)
  return ⟨members, selector, multiplicity, rankBytes, emission.width, emission.selectorStart,
    emission.selectorCount, emission.lookupCount, emission.branchless, equations, queries, returns⟩

theorem Emission.eval_of {values : Values G} {emission : Emission} {result : AIR.CircuitEmission}
    (members : emission.members.mapM (Member.eval values) = some result.members)
    (selector : evalExpr values emission.selector = some result.selector)
    (multiplicity : evalExpr values emission.multiplicity = some result.multiplicity)
    (rankBytes : ∀ index, evalExpr values (emission.rankBytes index) = some (result.rankBytes index))
    (width : emission.width = result.width) (start : emission.selectorStart = result.selectorStart)
    (count : emission.selectorCount = result.selectorCount) (lookups : emission.lookupCount = result.lookupCount)
    (branchless : emission.branchless = result.branchless)
    (equations : emission.equations.mapM (evalExpr values) = some result.equations)
    (queries : emission.queries.mapM (QueryExpr.eval values) = some result.queries)
    (returns : emission.returns.mapM (ReturnExpr.eval values) = some result.returns) :
    emission.eval values = some result := by
  simp only [Emission.eval, members, selector, multiplicity, evalFin_of rankBytes, equations, queries, returns,
    width, start, count, lookups, branchless, bind, Option.bind_some, pure]

theorem Emission.eval_components {values : Values G} {emission : Emission} {result : AIR.CircuitEmission}
    (evaluated : emission.eval values = some result) :
    emission.members.mapM (Member.eval values) = some result.members ∧
    evalExpr values emission.selector = some result.selector ∧
    evalExpr values emission.multiplicity = some result.multiplicity ∧
    (∀ index, evalExpr values (emission.rankBytes index) = some (result.rankBytes index)) ∧
    emission.width = result.width ∧ emission.selectorStart = result.selectorStart ∧
    emission.selectorCount = result.selectorCount ∧ emission.lookupCount = result.lookupCount ∧
    emission.branchless = result.branchless ∧
    emission.equations.mapM (evalExpr values) = some result.equations ∧
    emission.queries.mapM (QueryExpr.eval values) = some result.queries ∧
    emission.returns.mapM (ReturnExpr.eval values) = some result.returns := by
  simp only [Emission.eval, bind, Option.bind] at evaluated
  split at evaluated
  · cases evaluated
  rename_i members membersEval
  dsimp only at evaluated
  split at evaluated
  · cases evaluated
  rename_i selector selectorEval
  dsimp only at evaluated
  split at evaluated
  · cases evaluated
  rename_i multiplicity multiplicityEval
  dsimp only at evaluated
  split at evaluated
  · cases evaluated
  rename_i bytes bytesEval
  dsimp only at evaluated
  split at evaluated
  · cases evaluated
  rename_i equations equationsEval
  dsimp only at evaluated
  split at evaluated
  · cases evaluated
  rename_i queries queriesEval
  dsimp only at evaluated
  split at evaluated
  · cases evaluated
  rename_i returns returnsEval
  cases evaluated
  exact ⟨membersEval, selectorEval, multiplicityEval, evalFin_components bytesEval,
    rfl, rfl, rfl, rfl, rfl, equationsEval, queriesEval, returnsEval⟩

theorem Emission.lookup_eval {values : Values G} {emission : Emission} {result : AIR.CircuitEmission}
    (evaluated : emission.eval values = some result) (slot : Nat) :
    (emission.lookup slot).eval goldilocksOps values = some (result.lookup slot) := by
  obtain ⟨_, _, multiplicity, _, _, _, _, _, branchless, _, queries, returns⟩ := Emission.eval_components evaluated
  by_cases zero : slot = 0
  · simp only [Emission.lookup, AIR.CircuitEmission.lookup, zero, if_true, ExprLookup.eval]
    have weight := Expr.frontNeg_eval goldilocksLaws values multiplicity
    change evalExpr values emission.multiplicity.frontNeg = some (0 - result.multiplicity) at weight
    change ((evalExpr values emission.multiplicity.frontNeg).bind fun weight =>
      ((returnArgs emission.branchless emission.returns).mapM (evalExpr values)).bind fun args => some (weight, args)) = _
    rw [weight, returnArgs_eval emission.branchless returns, branchless]
    rfl
  · simpa only [Emission.lookup, AIR.CircuitEmission.lookup, zero, if_false, branchless] using
      LookupEmitter.slot_eval emission.branchless queries slot

theorem Emission.lookups_eval {values : Values G} {emission : Emission} {result : AIR.CircuitEmission}
    (evaluated : emission.eval values = some result) :
    emission.lookups.mapM (ExprLookup.eval goldilocksOps values) = some
      (List.ofFn fun slot : Fin result.lookupCount => result.lookup slot.val) := by
  have lookups := (Emission.eval_components evaluated).2.2.2.2.2.2.2.1
  have reflected := list_mapM_ofFn (fun slot : Fin emission.lookupCount => emission.lookup slot.val)
    (fun slot => result.lookup slot.val) (ExprLookup.eval goldilocksOps values)
    (fun slot => Emission.lookup_eval evaluated slot.val)
  rw [← lookups]
  exact reflected

end Aiur.NativeAIR.CircuitEmitter
