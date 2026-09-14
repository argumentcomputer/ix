/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.ComponentCircuitExpressions

/-! Expression reflection for mixed component circuits, including their
member-specific cursors and the selector that gates shared rank ranges. -/

namespace Aiur.NativeAIR.CircuitEmitter
open OpEmitter LookupEmitter BlockEmitter Compiler Bytecode

theorem emitComponentMember_fields {rank : Expr} {base selectorBase : Nat}
    {program : Toplevel} {functionIndex : Nat} {member : Member}
    (emitted : emitComponentMember rank base selectorBase program functionIndex = some member) :
    member.functionIndex = functionIndex ∧ program.functions[functionIndex]? = some member.function ∧
      member.selectorBase = selectorBase := by
  simp only [emitComponentMember, emitMember, bind, Option.bind] at emitted
  split at emitted
  · cases emitted
  rename_i function present
  dsimp only at emitted
  split at emitted
  · cases emitted
  dsimp only at emitted
  split at emitted
  · cases emitted
  cases emitted
  exact ⟨rfl, present, rfl⟩

theorem emitComponentMember_reflects {values : Values G} (row : Nat → G) {rank : Expr} {r : G}
    {base selectorBase : Nat} {program : Toplevel} {functionIndex : Nat} {member : Member}
    (rankEval : (program.componentFor functionIndex).ranked = true → evalExpr values rank = some r)
    (emitted : emitComponentMember rank base selectorBase program functionIndex = some member)
    (reads : ∀ index < member.readBound, (values.columns .main .current)[index]? = some (row index)) :
    ∃ result, AIR.emitComponentMember row r base selectorBase program functionIndex = some result ∧
      member.eval values = some result ∧ evalExpr values member.entry = some (result.entry row) := by
  have selected : evalExpr values (if (program.componentFor functionIndex).ranked then rank else .konst 0) =
      some (if (program.componentFor functionIndex).ranked then r else 0) := by
    cases ranked : (program.componentFor functionIndex).ranked
    · rfl
    · exact rankEval ranked
  exact emitMember_reflects row selected emitted reads

theorem emitComponentMembers_reflects {values : Values G} (row : Nat → G) {rank : Expr} {r : G}
    (base selectorBase : Nat) (program : Toplevel) (indices : List Nat) {members : List Member}
    (rankEval : ∀ member ∈ members, (program.componentFor member.functionIndex).ranked = true →
      evalExpr values rank = some r)
    (emitted : emitComponentMembers rank base selectorBase program indices = some members)
    (reads : ∀ member ∈ members, ∀ index < member.readBound,
      (values.columns .main .current)[index]? = some (row index)) :
    ∃ results, AIR.emitComponentMembers row r base selectorBase program indices = some results ∧
      members.mapM (Member.eval values) = some results ∧
      (members.map Member.entry).mapM (evalExpr values) = some (results.map (·.entry row)) ∧
      ((componentMembers program members).map Member.entry).mapM (evalExpr values) =
        some ((AIR.componentMembers program results).map (·.entry row)) := by
  induction indices generalizing selectorBase members with
  | nil => cases emitted; exact ⟨[], rfl, rfl, rfl, rfl⟩
  | cons index indices ih =>
    simp only [emitComponentMembers, bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    rename_i member memberEmitted
    dsimp only at emitted
    split at emitted
    · cases emitted
    rename_i tail tailEmitted
    cases emitted
    have indexEq := (emitComponentMember_fields memberEmitted).1
    obtain ⟨result, memberRead, memberEval, entryEval⟩ := emitComponentMember_reflects row
      (by rw [← indexEq]; exact rankEval member List.mem_cons_self) memberEmitted
      (reads member List.mem_cons_self)
    obtain ⟨results, resultsRead, resultsEval, entriesEval, rankedEval⟩ := ih _
      (fun member present => rankEval member (List.mem_cons_of_mem _ present)) tailEmitted
      (fun member present => reads member (List.mem_cons_of_mem _ present))
    have fields := Member.eval_components memberEval
    refine ⟨result :: results, ?_, ?_, ?_, ?_⟩
    · simp only [AIR.emitComponentMembers, memberRead, bind, Option.bind_some, ← fields.2.1, resultsRead, pure]
    · simp only [List.mapM_cons, memberEval, resultsEval, bind, Option.bind_some, pure]
    · simp only [List.map_cons, List.mapM_cons, entryEval, entriesEval, bind, Option.bind_some, pure]
    · simp only [componentMembers, AIR.componentMembers, List.filter_cons, fields.1]
      simp only [componentMembers, AIR.componentMembers] at rankedEval
      split
      · simp only [List.map_cons, List.mapM_cons, entryEval, bind, Option.bind_some]
        rw [rankedEval]
        rfl
      · exact rankedEval

theorem componentCircuitEmission_eval {values : Values G} (row : Nat → G) (program : Toplevel)
    (circuit : Circuit) {members : List Member} {results : List AIR.MemberEmission}
    (membersEval : members.mapM (Member.eval values) = some results)
    (entriesEval : (members.map Member.entry).mapM (evalExpr values) = some (results.map (·.entry row)))
    (rankedEval : ((componentMembers program members).map Member.entry).mapM (evalExpr values) =
      some ((AIR.componentMembers program results).map (·.entry row)))
    (reads : ∀ index < circuit.layout.inputSize + circuit.layout.selectors + 1 +
        (if (componentMembers program members).isEmpty then 0 else 6),
      (values.columns .main .current)[index]? = some (row index)) :
    (componentCircuitEmission program circuit members).eval values =
      some (AIR.componentCircuitEmission row program circuit results) := by
  have selectorEval := sum_eval entriesEval
  have rankSelectorEval := sum_eval rankedEval
  have empty : (componentMembers program members).isEmpty = (AIR.componentMembers program results).isEmpty := by
    have length := Bytecode.AIR.list_mapM_some_length _ _ _ rankedEval
    simp only [List.length_map] at length
    cases source : componentMembers program members <;>
      cases target : AIR.componentMembers program results <;> simp_all
  have physicalRanks (nonempty : (componentMembers program members).isEmpty = false) (index : Fin 6) :
      evalExpr values (rankBytes circuit.layout index) =
        some (AIR.circuitRankBytes row circuit.layout index) := by
    exact reads (circuit.layout.inputSize + circuit.layout.selectors + 1 + index.val) (by
      rw [nonempty]; simp only [Bool.false_eq_true, if_false]; omega)
  have ranks (index : Fin 6) :
      evalExpr values ((componentCircuitEmission program circuit members).rankBytes index) =
        some ((AIR.componentCircuitEmission row program circuit results).rankBytes index) := by
    cases present : (componentMembers program members).isEmpty
    · simpa only [componentCircuitEmission, AIR.componentCircuitEmission, ← empty, present,
        Bool.false_eq_true, if_false] using physicalRanks present index
    · simp only [componentCircuitEmission, AIR.componentCircuitEmission, ← empty, present, if_true]
      rfl
  have multiplicityEval : evalExpr values (mainCurrent (circuit.layout.inputSize + circuit.layout.selectors)).expr =
      some (row (circuit.layout.inputSize + circuit.layout.selectors)) :=
    reads (circuit.layout.inputSize + circuit.layout.selectors) (by omega)
  have functions : members.map Member.function = results.map AIR.MemberEmission.function := by
    have relation := AIR.mapM_forall₂ membersEval (fun _ _ _ reflected => (Member.eval_components reflected).2.1)
    clear membersEval entriesEval selectorEval rankedEval rankSelectorEval empty physicalRanks ranks reads
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
  apply Emission.eval_of membersEval selectorEval multiplicityEval ranks rfl rfl rfl rfl
  · simp only [componentCircuitEmission, AIR.componentCircuitEmission, circuitEmission, AIR.circuitEmission, functions]
  · simp only [componentCircuitEmission, AIR.componentCircuitEmission, circuitEmission, AIR.circuitEmission,
      List.mapM_append]
    split <;> simp only [List.mapM_cons, List.mapM_nil, equations, selectors, exclusive, activity,
      bind, Option.bind_some, pure, goldilocks_mul, goldilocks_sub,
      AIR.oneSubBooleanConstraint, AIR.activityConstraint]
  · cases present : (componentMembers program members).isEmpty
    · have rankQueries := queryParts_eval rankSelectorEval (rangeSix_eval (rankBytes circuit.layout)
        (AIR.circuitRankBytes row circuit.layout) (physicalRanks present)) 1
      simp only [componentCircuitEmission, AIR.componentCircuitEmission, ← empty, present,
        Bool.false_eq_true, if_false, List.mapM_append, queries, rankQueries, bind, Option.bind_some, pure]
    · simp only [componentCircuitEmission, AIR.componentCircuitEmission, ← empty, present, if_true,
        List.append_nil, queries]
  · exact returns

theorem emitComponentCircuit_reflects {values : Values G} (row : Nat → G) (program : Toplevel)
    (circuit : Circuit) {emission : Emission}
    (emitted : emitComponentCircuit program circuit = some emission)
    (reads : ∀ index < emission.componentReadBound program,
      (values.columns .main .current)[index]? = some (row index)) :
    ∃ result, circuit.emitComponentRow row program = some result ∧ emission.eval values = some result := by
  simp only [emitComponentCircuit, bind, Option.bind] at emitted
  split at emitted
  · cases emitted
  rename_i members membersEmitted
  cases emitted
  let start := circuit.layout.inputSize + circuit.layout.selectors + 1 +
    if (componentMembers program members).isEmpty then 0 else 6
  have header := fold_max_start Member.readBound members start
  have headerReads : ∀ index < start, (values.columns .main .current)[index]? = some (row index) :=
    fun index bound => reads index (Nat.lt_of_lt_of_le bound header)
  have rankEval : ∀ member ∈ members, (program.componentFor member.functionIndex).ranked = true →
      evalExpr values (packSix (rankBytes circuit.layout)) =
        some (AIR.packRank (AIR.circuitRankBytes row circuit.layout)) := by
    intro member present ranked
    have chosen : member ∈ componentMembers program members := List.mem_filter.mpr ⟨present, ranked⟩
    have nonempty : (componentMembers program members).isEmpty = false :=
      List.isEmpty_eq_false_iff.mpr (fun empty => by rw [empty] at chosen; cases chosen)
    apply packSix_eval
    intro index
    exact headerReads (circuit.layout.inputSize + circuit.layout.selectors + 1 + index.val) (by
      simp only [start, nonempty, Bool.false_eq_true, if_false]; omega)
  obtain ⟨results, resultsRead, resultsEval, entriesEval, rankedEval⟩ := emitComponentMembers_reflects row
    (circuit.layout.inputSize + circuit.layout.selectors + 1) circuit.layout.inputSize program circuit.members.toList
    rankEval membersEmitted (fun member present index bound => reads index
      (Nat.lt_of_lt_of_le bound (fold_max_member Member.readBound present start)))
  refine ⟨AIR.componentCircuitEmission row program circuit results, ?_,
    componentCircuitEmission_eval row program circuit resultsEval entriesEval rankedEval headerReads⟩
  simp only [Circuit.emitComponentRow, resultsRead, bind, Option.bind_some, pure]

end Aiur.NativeAIR.CircuitEmitter
