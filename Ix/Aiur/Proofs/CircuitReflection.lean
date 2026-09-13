/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.CircuitExpressions

/-!
Reflection of complete symbolic function circuits into the valued circuit
model. The row premise covers the finite header and member allocations;
no equation values, query messages, or selected executions are assumed.
-/

namespace Aiur.NativeAIR.CircuitEmitter
open OpEmitter LookupEmitter BlockEmitter Compiler

theorem emitMember_reflects {values : Values G} (row : Nat → G) {rank : Expr} {r : G}
    {column lookup selectorBase : Nat} {program : Bytecode.Toplevel} {functionIndex : Nat} {member : Member}
    (rankEval : evalExpr values rank = some r)
    (emitted : emitMember rank column lookup selectorBase program functionIndex = some member)
    (reads : ∀ index < member.readBound, (values.columns .main .current)[index]? = some (row index)) :
    ∃ result, AIR.emitMember row r column lookup selectorBase program functionIndex = some result ∧
      member.eval values = some result ∧ evalExpr values member.entry = some (result.entry row) := by
  simp only [emitMember, bind, Option.bind] at emitted
  split at emitted
  · cases emitted
  rename_i function functionRead
  dsimp only at emitted
  split at emitted
  · cases emitted
  rename_i entry entryRead
  dsimp only at emitted
  split at emitted
  · cases emitted
  rename_i body bodyEmitted
  cases emitted
  dsimp only [Member.readBound] at reads
  have selectors : SelectorReads values (selectorExprs selectorBase function.layout.selectors)
      (fun index => row (selectorBase + index)) := selectorExprs_reads row selectorBase function.layout.selectors
    (fun index bound => reads (selectorBase + index) (by omega))
  have entryEval := blockSelector_reads selectors function.body entryRead
  have inputs := advice_absolute_eval row 0 function.layout.inputSize
    (fun index bound => by simpa only [Nat.zero_add] using reads index (by omega))
  obtain ⟨result, bodyRead, bodyEval⟩ := block_reflects values row selectors rankEval function.body
    entryEval inputs (advice_normal _ _) bodyEmitted (fun index _ bound => reads index (by omega))
  dsimp only [Context.valued] at bodyRead
  refine ⟨⟨functionIndex, function, selectorBase, result⟩, ?_, Member.eval_of bodyEval, entryEval⟩
  simp only [AIR.emitMember, functionRead, Bytecode.Function.emitRow, bodyRead, bind, Option.bind_some, pure]

theorem emitMembers_reflects {values : Values G} (row : Nat → G) {rank : Expr} {r : G}
    (column lookup selectorBase : Nat) (program : Bytecode.Toplevel) (indices : List Nat)
    {members : List Member} (rankEval : evalExpr values rank = some r)
    (emitted : emitMembers rank column lookup selectorBase program indices = some members)
    (reads : ∀ member ∈ members, ∀ index < member.readBound,
      (values.columns .main .current)[index]? = some (row index)) :
    ∃ results, AIR.emitMembers row r column lookup selectorBase program indices = some results ∧
      members.mapM (Member.eval values) = some results ∧
      (members.map Member.entry).mapM (evalExpr values) = some (results.map (·.entry row)) := by
  induction indices generalizing selectorBase members with
  | nil =>
    cases emitted
    exact ⟨[], rfl, rfl, rfl⟩
  | cons index indices ih =>
    simp only [emitMembers, bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    rename_i member memberEmitted
    dsimp only at emitted
    split at emitted
    · cases emitted
    rename_i tail tailEmitted
    cases emitted
    obtain ⟨result, memberRead, memberEval, entryEval⟩ := emitMember_reflects row rankEval memberEmitted
      (reads member List.mem_cons_self)
    obtain ⟨results, resultsRead, resultsEval, entriesEval⟩ := ih _ tailEmitted
      (fun member present => reads member (List.mem_cons_of_mem _ present))
    have function := (Member.eval_components memberEval).2.1
    refine ⟨result :: results, ?_, ?_, ?_⟩
    · simp only [AIR.emitMembers, memberRead, bind, Option.bind_some, ← function, resultsRead, pure]
    · simp only [List.mapM_cons, memberEval, resultsEval, bind, Option.bind_some, pure]
    · simp only [List.map_cons, List.mapM_cons, entryEval, entriesEval, bind, Option.bind_some, pure]

theorem circuitEmission_eval {values : Values G} (row : Nat → G) (circuit : Bytecode.Circuit)
    {members : List Member} {results : List AIR.MemberEmission}
    (membersEval : members.mapM (Member.eval values) = some results)
    (entriesEval : (members.map Member.entry).mapM (evalExpr values) = some (results.map (·.entry row)))
    (reads : ∀ index < circuit.layout.inputSize + circuit.layout.selectors + 1 + 6,
      (values.columns .main .current)[index]? = some (row index)) :
    (circuitEmission circuit members).eval values = some (AIR.circuitEmission row circuit results) := by
  have selectorEval := sum_eval entriesEval
  have rankEval (index : Fin 6) : evalExpr values (rankBytes circuit.layout index) =
      some (AIR.circuitRankBytes row circuit.layout index) :=
    reads (circuit.layout.inputSize + circuit.layout.selectors + 1 + index.val) (by omega)
  have multiplicityEval : evalExpr values (mainCurrent (circuit.layout.inputSize + circuit.layout.selectors)).expr =
      some (row (circuit.layout.inputSize + circuit.layout.selectors)) :=
    reads (circuit.layout.inputSize + circuit.layout.selectors) (by omega)
  have functions : members.map Member.function = results.map AIR.MemberEmission.function := by
    have relation := AIR.mapM_forall₂ membersEval (fun _ _ _ reflected => (Member.eval_components reflected).2.1)
    clear membersEval entriesEval selectorEval
    induction relation with
    | nil => rfl
    | cons equal _ ih => simp only [List.map_cons, equal, ih]
  have equations : (members.flatMap (·.body.equations)).mapM (evalExpr values) =
      some (results.flatMap (·.body.equations)) :=
    list_mapM_flatMap membersEval (fun member => member.body.equations) (fun result => result.body.equations)
      (evalExpr values) (fun _ _ reflected =>
        (BlockEmitter.Emission.eval_components (Member.eval_components reflected).2.2.2).2.2.2.1)
  have queries : (members.flatMap (·.body.queries)).mapM (QueryExpr.eval values) =
      some (results.flatMap (·.body.queries)) :=
    list_mapM_flatMap membersEval (fun member => member.body.queries) (fun result => result.body.queries)
      (QueryExpr.eval values) (fun _ _ reflected =>
        (BlockEmitter.Emission.eval_components (Member.eval_components reflected).2.2.2).2.2.2.2.1)
  have returns : (members.flatMap (·.body.returns)).mapM (ReturnExpr.eval values) =
      some (results.flatMap (·.body.returns)) :=
    list_mapM_flatMap membersEval (fun member => member.body.returns) (fun result => result.body.returns)
      (ReturnExpr.eval values) (fun _ _ reflected =>
        (BlockEmitter.Emission.eval_components (Member.eval_components reflected).2.2.2).2.2.2.2.2.1)
  have oneMinus := Expr.frontSub_eval goldilocksLaws values
    (show evalExpr values (.konst 1) = some 1 from rfl) selectorEval
  have exclusive := Expr.frontMul_eval goldilocksLaws values selectorEval oneMinus
  have activity := Expr.frontMul_eval goldilocksLaws values multiplicityEval oneMinus
  have selectors := selectorEquations_eval row circuit.layout
    (fun index bound => reads (circuit.layout.inputSize + index) (by omega))
  have rankQueries := queryParts_eval selectorEval (rangeSix_eval (rankBytes circuit.layout)
    (AIR.circuitRankBytes row circuit.layout) rankEval) 1
  apply Emission.eval_of
  · exact membersEval
  · exact selectorEval
  · exact multiplicityEval
  · exact rankEval
  · rfl
  · rfl
  · rfl
  · rfl
  · simp only [circuitEmission, AIR.circuitEmission, functions]
  · simp only [circuitEmission, AIR.circuitEmission, List.mapM_append]
    split <;> simp only [List.mapM_cons, List.mapM_nil, equations, selectors, exclusive, activity,
      bind, Option.bind_some, pure, goldilocks_mul, goldilocks_sub,
      AIR.oneSubBooleanConstraint, AIR.activityConstraint]
  · simp only [circuitEmission, AIR.circuitEmission, List.mapM_append, queries, rankQueries,
      bind, Option.bind_some, pure]
  · exact returns

theorem emitCircuit_reflects {values : Values G} (row : Nat → G) (program : Bytecode.Toplevel)
    (circuit : Bytecode.Circuit) {emission : Emission}
    (emitted : emitCircuit program circuit = some emission)
    (reads : ∀ index < emission.readBound, (values.columns .main .current)[index]? = some (row index)) :
    ∃ result, circuit.emitRow row program = some result ∧ emission.eval values = some result := by
  simp only [emitCircuit, bind, Option.bind] at emitted
  split at emitted
  · cases emitted
  rename_i members membersEmitted
  cases emitted
  have header := fold_max_start Member.readBound members
    (circuit.layout.inputSize + circuit.layout.selectors + 1 + 6)
  have headerReads : ∀ index < circuit.layout.inputSize + circuit.layout.selectors + 1 + 6,
      (values.columns .main .current)[index]? = some (row index) :=
    fun index bound => reads index (Nat.lt_of_lt_of_le bound header)
  have rankEval := packSix_eval values (rankBytes circuit.layout) (AIR.circuitRankBytes row circuit.layout)
    (fun index => headerReads (circuit.layout.inputSize + circuit.layout.selectors + 1 + index.val) (by omega))
  obtain ⟨results, resultsRead, resultsEval, entriesEval⟩ := emitMembers_reflects row
    (circuit.layout.inputSize + circuit.layout.selectors + 1 + 6) 4 circuit.layout.inputSize program circuit.members.toList
    rankEval membersEmitted (fun member present index bound => reads index
      (Nat.lt_of_lt_of_le bound (fold_max_member Member.readBound present _)))
  refine ⟨_, ?_, circuitEmission_eval row circuit resultsEval entriesEval headerReads⟩
  simp only [Bytecode.Circuit.emitRow, resultsRead, bind, Option.bind_some, pure]

end Aiur.NativeAIR.CircuitEmitter
