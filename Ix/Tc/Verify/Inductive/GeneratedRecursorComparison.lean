import Ix.Tc.Verify.Inductive.GeneratedRecursorSemantics

/-!
# Exhaustive generated-recursor comparison

The production recursor checker first selects one generated cache entry and
then compares it with a frozen snapshot of the stored declaration.  This
module exposes that second phase as a complete execution trace: every header
field agrees, the full types pass the actual `isDefEq` call, the rule arrays
have equal length, and every same-index rule has the same field count and
passes its own actual `isDefEq` call.

The trace deliberately retains the intermediate checker states.  A later
semantic layer can interpret only these concrete successful DefEq calls; it
does not receive an oracle for the comparison as a whole.
-/

namespace Ix.Tc

/-- Exact successful executions of the positional generated/stored rule
comparisons, including all state changes made by DefEq. -/
inductive GeneratedRuleComparisonTrace
    (generatedRules storedRules : Array (RecRule m))
    (methods : Methods m) : Nat → Nat → TcState m → TcState m → Prop
  | nil (index state) :
      GeneratedRuleComparisonTrace generatedRules storedRules methods index 0
        state state
  | cons {index remaining before afterComparison final}
      (fields : generatedRules[index]!.fields = storedRules[index]!.fields)
      (comparison :
        (RecM.isDefEq generatedRules[index]!.rhs storedRules[index]!.rhs).run
          methods before = .ok true afterComparison)
      (tail : GeneratedRuleComparisonTrace generatedRules storedRules methods
        (index + 1) remaining afterComparison final) :
      GeneratedRuleComparisonTrace generatedRules storedRules methods index
        (remaining + 1) before final

/-- Complete data retained from a successful selected-candidate comparison. -/
def GeneratedRecursorCandidateTrace
    (ty : KExpr m) (declaredLvls : UInt64) (declaredIsUnsafe : Bool)
    (params motives minors indices : UInt64)
    (storedRules : Array (RecRule m)) (generated : GeneratedRecursor m)
    (methods : Methods m) (initial final : TcState m) : Prop :=
  declaredLvls = generated.lvls ∧
    declaredIsUnsafe = generated.isUnsafe ∧
    params = generated.params ∧ motives = generated.motives ∧
    minors = generated.minors ∧ indices = generated.indices ∧
    ∃ afterType,
      (RecM.isDefEq generated.ty ty).run methods initial =
          .ok true afterType ∧
        generated.rules.size = storedRules.size ∧
        GeneratedRuleComparisonTrace generated.rules storedRules methods 0
          generated.rules.size afterType final

/-- Complete successful cache-selection boundary.  It identifies the exact
array position and candidate that reached exhaustive comparison, together
with the state after all signature-selection callbacks. -/
def GeneratedRecursorCacheTrace
    (recBlock id : KId m) (ty : KExpr m) (declaredLvls : UInt64)
    (declaredIsUnsafe : Bool) (params motives minors indices : UInt64)
    (indId : KId m) (storedRules : Array (RecRule m))
    (generated : Array (GeneratedRecursor m)) (methods : Methods m)
    (initial final : TcState m) : Prop :=
  ∃ index selected afterSelection,
    (RecM.selectGeneratedRecursorIndex recBlock id ty params motives minors
      indId generated).run methods initial = .ok (some index) afterSelection ∧
    generated[index]? = some selected ∧
    (RecM.checkGeneratedRecursorCandidate ty declaredLvls declaredIsUnsafe
      params motives minors indices storedRules selected).run methods
        afterSelection = .ok () final

namespace RecM

/-- Expose one concrete checker bind while decomposing comparison traces. -/
private theorem runTcBind {α β : Type}
    (x : TcM m α) (k : α → TcM m β) (state : TcState m) :
    (x >>= k) state = match x state with
      | .ok value after => k value after
      | .error err after => .error err after := by
  show EStateM.bind x k state = _
  unfold EStateM.bind
  cases x state <;> rfl

/-- A successful production rule loop exposes every same-index field equality
and successful RHS DefEq call. -/
theorem checkGeneratedRecursorRules_success
    (generatedRules storedRules : Array (RecRule m))
    (methods : Methods m) :
    ∀ {index remaining : Nat} {initial final : TcState m},
      (checkGeneratedRecursorRules generatedRules storedRules index remaining).run
          methods initial = .ok () final →
      GeneratedRuleComparisonTrace generatedRules storedRules methods index
        remaining initial final
  | _, 0, initial, final, hrun => by
      simp only [checkGeneratedRecursorRules, pure, ReaderT.run] at hrun
      cases hrun
      exact .nil _ _
  | index, remaining + 1, initial, final, hrun => by
      rw [checkGeneratedRecursorRules] at hrun
      cases hfields :
          (generatedRules[index]!.fields !=
            storedRules[index]!.fields) with
      | false =>
          have fields :
              generatedRules[index]!.fields =
                storedRules[index]!.fields := by
            simpa using hfields
          simp only [hfields, Bool.false_eq_true, if_false, pure_bind,
            ReaderT.run_bind, runTcBind] at hrun
          generalize hcomparison :
              (isDefEq generatedRules[index]!.rhs
                storedRules[index]!.rhs).run methods initial =
                  comparisonResult at hrun
          cases comparisonResult with
          | error err afterComparison => contradiction
          | ok answer afterComparison =>
              cases answer with
              | false =>
                  simp only [Bool.not_false, if_true, throw, ReaderT.run]
                    at hrun
                  contradiction
              | true =>
                  simp only [Bool.not_true] at hrun
                  exact .cons fields hcomparison
                    (checkGeneratedRecursorRules_success generatedRules
                      storedRules methods hrun)
      | true =>
          simp only [hfields, if_true, throw, ReaderT.run] at hrun
          contradiction

/-- Every successful selected-candidate comparison takes all guards and
produces the complete type-and-rule trace. -/
theorem checkGeneratedRecursorCandidate_success
    {ty : KExpr m} {declaredLvls : UInt64} {declaredIsUnsafe : Bool}
    {params motives minors indices : UInt64}
    {storedRules : Array (RecRule m)} {generated : GeneratedRecursor m}
    {methods : Methods m} {initial final : TcState m}
    (hrun : (checkGeneratedRecursorCandidate ty declaredLvls declaredIsUnsafe
      params motives minors indices storedRules generated).run methods initial =
        .ok () final) :
    GeneratedRecursorCandidateTrace ty declaredLvls declaredIsUnsafe params
      motives minors indices storedRules generated methods initial final := by
  unfold checkGeneratedRecursorCandidate at hrun
  cases hlevels : (declaredLvls != generated.lvls) with
  | true =>
      simp only [hlevels, if_true, throw, ReaderT.run] at hrun
      contradiction
  | false =>
      have levels : declaredLvls = generated.lvls := by
        simpa using hlevels
      simp only [hlevels, Bool.false_eq_true, if_false, pure_bind] at hrun
      cases hsafety : (declaredIsUnsafe != generated.isUnsafe) with
      | true =>
          simp only [hsafety, if_true, throw, ReaderT.run]
            at hrun
          contradiction
      | false =>
          have safety : declaredIsUnsafe = generated.isUnsafe := by
            simpa using hsafety
          simp only [hsafety, Bool.false_eq_true, if_false] at hrun
          cases hmetadata :
              (params != generated.params || motives != generated.motives ||
                minors != generated.minors || indices != generated.indices) with
          | true =>
              simp only [hmetadata, if_true, throw, ReaderT.run]
                at hrun
              contradiction
          | false =>
              have metadata :
                  ((params = generated.params ∧
                      motives = generated.motives) ∧
                    minors = generated.minors) ∧
                  indices = generated.indices := by
                simpa using hmetadata
              simp only [hmetadata, Bool.false_eq_true, if_false,
                ReaderT.run_bind, runTcBind] at hrun
              generalize htype :
                  (isDefEq generated.ty ty).run methods initial = typeResult
                    at hrun
              cases typeResult with
              | error err afterType => contradiction
              | ok answer afterType =>
                  cases answer with
                  | false =>
                      simp only [Bool.not_false, if_true, throw, ReaderT.run]
                        at hrun
                      contradiction
                  | true =>
                      simp only [Bool.not_true] at hrun
                      cases hmissing :
                          (generated.rules.isEmpty && !storedRules.isEmpty) with
                      | true =>
                          simp only [hmissing, if_true, throw,
                            ReaderT.run] at hrun
                          contradiction
                      | false =>
                          simp only [hmissing, Bool.false_eq_true, if_false]
                            at hrun
                          cases hstoredMissing :
                              (!generated.rules.isEmpty &&
                                storedRules.isEmpty) with
                          | true =>
                              simp only [hstoredMissing, if_true,
                                throw, ReaderT.run] at hrun
                              contradiction
                          | false =>
                              simp only [hstoredMissing, Bool.false_eq_true,
                                if_false] at hrun
                              cases hcount :
                                  (generated.rules.size != storedRules.size) with
                              | true =>
                                  simp only [hcount, if_true,
                                    throw, ReaderT.run] at hrun
                                  contradiction
                              | false =>
                                  have count :
                                      generated.rules.size =
                                        storedRules.size := by
                                    simpa using hcount
                                  simp only [hcount, Bool.false_eq_true,
                                    if_false] at hrun
                                  refine ⟨levels, safety, metadata.1.1.1,
                                    metadata.1.1.2, metadata.1.2,
                                    metadata.2, afterType, htype, count, ?_⟩
                                  exact checkGeneratedRecursorRules_success
                                    generated.rules storedRules methods hrun

/-- A successful frozen-cache check exposes the exact selected array entry
and the complete exhaustive comparison execution that followed selection. -/
theorem checkGeneratedRecursorFromCache_success
    {recBlock id : KId m} {ty : KExpr m} {declaredLvls : UInt64}
    {declaredIsUnsafe : Bool} {params motives minors indices : UInt64}
    {indId : KId m} {storedRules : Array (RecRule m)}
    {generated : Array (GeneratedRecursor m)} {methods : Methods m}
    {initial final : TcState m}
    (hrun : (checkGeneratedRecursorFromCache recBlock id ty declaredLvls
      declaredIsUnsafe params motives minors indices indId storedRules
      generated).run methods initial = .ok () final) :
    GeneratedRecursorCacheTrace recBlock id ty declaredLvls declaredIsUnsafe
      params motives minors indices indId storedRules generated methods initial
        final := by
  unfold checkGeneratedRecursorFromCache at hrun
  rw [ReaderT.run_bind, runTcBind] at hrun
  generalize hselection :
      (selectGeneratedRecursorIndex recBlock id ty params motives minors indId
        generated).run methods initial = selectionResult at hrun
  cases selectionResult with
  | error error afterSelection => contradiction
  | ok selectedIndex afterSelection =>
      cases selectedIndex with
      | none =>
          simp only [Option.bind_none, throw, ReaderT.run] at hrun
          contradiction
      | some index =>
          cases hlookup : generated[index]? with
          | none =>
              simp only [Option.bind_some, hlookup, throw, ReaderT.run] at hrun
              contradiction
          | some selected =>
              simp only [Option.bind_some, hlookup] at hrun
              exact ⟨index, selected, afterSelection, hselection, hlookup,
                hrun⟩

end RecM

end Ix.Tc
