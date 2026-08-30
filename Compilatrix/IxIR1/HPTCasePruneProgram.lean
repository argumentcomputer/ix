import Compilatrix.IxIR1.HPTCasePrune
import Compilatrix.IxIR1.ReaddressAllSim

/-!
# Whole-program semantic support for HPT case simplification

`HPTCasePrune` proves one supplied fragment equivalent while the declaration
environment stays fixed.  Rewriting stored function bodies changes the
environment itself: direct calls and PAP application subsequently enter the
rewritten definitions.  This module closes that recursive seam by a common
fuel induction over every evaluator entry point.

The result is still a logical, old-keyed environment.  A production artifact
must readdress `rewriteEntries`; that content-address rebuild is kept separate
so no theorem silently treats changed declaration bytes as retaining their old
identity.
-/

namespace Compilatrix.IxIR1.HPT.CasePrune

private theorem runCode_case_rewriteCtx_eq
    {before after : Ctx} {fuel : Nat}
    (ih : ∀ (current : FnDef) (store : Store)
      (environment : List RVal) (input : Code),
      runCode after fuel current store environment input =
        runCode before fuel current store environment input)
    (current : FnDef) (store : Store) (environment : List RVal)
    (scrutinee : Atom) (peelNat : Bool) (alternatives : Array Alt) :
    runCode after (fuel + 1) current store environment
        (.case scrutinee peelNat alternatives) =
    runCode before (fuel + 1) current store environment
        (.case scrutinee peelNat alternatives) := by
  simp only [runCode]
  cases hscrutinee : resolveAtom environment scrutinee with
  | error error => simp [bind, Except.bind]
  | ok value =>
      simp only [bind, Except.bind]
      cases value with
      | erased => simp
      | lit literal =>
          cases literal with
          | str value => simp
          | nat value =>
              simp only
              cases peelNat with
              | false => simp
              | true =>
                  simp only
                  cases value with
                  | zero =>
                      simp only
                      cases hfind : alternatives.find?
                          (fun alternative => alternative.cidx == 0) with
                      | none => simp
                      | some alternative =>
                          cases alternative with
                          | mk cidx fields body =>
                              cases fields with
                              | zero =>
                                  simpa using
                                    ih current store environment body
                              | succ fields => simp
                  | succ value =>
                      simp only
                      cases hfind : alternatives.find?
                          (fun alternative => alternative.cidx == 1) with
                      | none => simp
                      | some alternative =>
                          cases alternative with
                          | mk cidx fields body =>
                              cases fields with
                              | zero => simp
                              | succ fields =>
                                  cases fields with
                                  | zero =>
                                      simpa using ih current store
                                        (.lit (.nat value) :: environment)
                                        body
                                  | succ fields => simp
      | loc location =>
          simp only
          cases hget : store.get? location with
          | none => simp
          | some box =>
              simp only
              cases hnode : box.node with
              | papN function arity arguments => simp
              | ctorN identity fields =>
                  simp only
                  cases hfind : alternatives.find?
                      (fun alternative =>
                        alternative.cidx == identity.cidx) with
                  | none => simp
                  | some alternative =>
                      cases alternative with
                      | mk cidx fieldCount body =>
                          by_cases hfields : fields.size = fieldCount
                          · simpa [hfields] using
                              ih current store
                                (fields.foldl
                                  (fun result field => field :: result)
                                  environment) body
                          · simp [hfields]

/-- All mutually recursive evaluator entries agree after logically replacing
every stored function body by `runRecursive`.  Calls are the substantive
case; store-only recursion is bundled because `applyGo` and memory operations
share the evaluator's fuel index. -/
private structure EvalRewriteAt
    (declarations : DeclEnv) (summaries : SummaryEnv)
    (before : Ctx) (fuel : Nat) : Prop where
  runCode : ∀ (current : FnDef) (store : Store)
      (environment : List RVal) (input : Code),
    runCode (rewriteCtx declarations summaries before) fuel current store
        environment input =
      runCode before fuel current store environment input
  runOp : ∀ (current : FnDef) (store : Store)
      (environment : List RVal) (operation : Op),
    runOp (rewriteCtx declarations summaries before) fuel current store
        environment operation =
      runOp before fuel current store environment operation
  invoke : ∀ (function : Compilatrix.Ixon.Address)
      (arguments : List RVal) (store : Store),
    IxIR1.invoke (rewriteCtx declarations summaries before) fuel function
        arguments store =
      IxIR1.invoke before fuel function arguments store
  applyGo : ∀ (store : Store) (function : RVal)
      (arguments : List RVal),
    IxIR1.applyGo (rewriteCtx declarations summaries before) fuel store
        function arguments =
      IxIR1.applyGo before fuel store function arguments
  dropVal : ∀ (store : Store) (value : RVal),
    IxIR1.dropVal (rewriteCtx declarations summaries before) fuel store value =
      IxIR1.dropVal before fuel store value
  dropMany : ∀ (store : Store) (values : List RVal),
    IxIR1.dropMany (rewriteCtx declarations summaries before) fuel store
        values =
      IxIR1.dropMany before fuel store values
  dropUVal : ∀ (store : Store) (value : RVal),
    IxIR1.dropUVal (rewriteCtx declarations summaries before) fuel store value =
      IxIR1.dropUVal before fuel store value
  dropManyU : ∀ (store : Store) (values : List RVal),
    IxIR1.dropManyU (rewriteCtx declarations summaries before) fuel store
        values =
      IxIR1.dropManyU before fuel store values

private theorem evalRewriteAt
    {declarations : DeclEnv} {summaries : SummaryEnv}
    (hpost : LocalPostFixpoint declarations summaries)
    {before : Ctx} (hbefore : before.decls = declarations) :
    ∀ fuel, EvalRewriteAt declarations summaries before fuel := by
  intro fuel
  induction fuel with
  | zero =>
      constructor <;> intros <;>
        simp [runCode, runOp, IxIR1.invoke, IxIR1.applyGo,
          IxIR1.dropVal, IxIR1.dropMany, IxIR1.dropUVal,
          IxIR1.dropManyU]
  | succ fuel smaller =>
      refine {
        runCode := ?_
        runOp := ?_
        invoke := ?_
        applyGo := ?_
        dropVal := ?_
        dropMany := ?_
        dropUVal := ?_
        dropManyU := ?_ }
      · intro current store environment input
        cases input with
        | ret atom => simp [runCode]
        | letOp operation rest =>
            simp only [runCode]
            rw [smaller.runOp current store environment operation]
            cases hoperation : runOp before fuel current store environment
                operation with
            | error error => rfl
            | ok output =>
                rcases output with ⟨next, value⟩
                exact smaller.runCode current next (value :: environment) rest
        | case scrutinee peelNat alternatives =>
            exact runCode_case_rewriteCtx_eq smaller.runCode current store
              environment scrutinee peelNat alternatives
      · intro current store environment operation
        cases operation with
        | pure atom => simp [runOp]
        | alloc world identity arguments => simp [runOp]
        | reuse target identity arguments => simp [runOp]
        | free target => simp [runOp]
        | dup target => simp [runOp]
        | drop target =>
            simp only [runOp]
            cases htarget : resolveAtom environment target with
            | error error => simp [bind, Except.bind]
            | ok value =>
                simp only [bind, Except.bind]
                cases value with
                | lit literal => rfl
                | erased => rfl
                | loc location =>
                    change (do
                        let next ← IxIR1.dropVal
                          (rewriteCtx declarations summaries before) fuel
                          store (.loc location)
                        .ok (next, RVal.erased)) =
                      (do
                        let next ← IxIR1.dropVal before fuel store
                          (.loc location)
                        .ok (next, RVal.erased))
                    rw [smaller.dropVal store (.loc location)]
        | dropU target =>
            simp only [runOp]
            cases htarget : resolveAtom environment target with
            | error error => simp [bind, Except.bind]
            | ok value =>
                simp only [bind, Except.bind]
                cases value with
                | lit literal => rfl
                | erased => rfl
                | loc location =>
                    change (do
                        let next ← IxIR1.dropUVal
                          (rewriteCtx declarations summaries before) fuel
                          store (.loc location)
                        .ok (next, RVal.erased)) =
                      (do
                        let next ← IxIR1.dropUVal before fuel store
                          (.loc location)
                        .ok (next, RVal.erased))
                    rw [smaller.dropUVal store (.loc location)]
        | fetch target field => simp [runOp]
        | call function atoms =>
            simp only [runOp]
            cases harguments : resolveAtoms environment atoms with
            | error error => rfl
            | ok arguments =>
                exact smaller.invoke function arguments store
        | callSelf atoms =>
            simp only [runOp]
            cases harguments : resolveAtoms environment atoms with
            | error error => simp [bind, Except.bind]
            | ok arguments =>
                simp only [bind, Except.bind]
                by_cases harity : arguments.length = current.arity
                · simp only [harity]
                  rw [smaller.runCode current store arguments.reverse
                    current.body]
                · simp [harity]
        | papp function atoms =>
            simp only [runOp]
            cases harguments : resolveAtoms environment atoms with
            | error error => simp [bind, Except.bind]
            | ok arguments =>
                simp only [bind, Except.bind]
                rw [hbefore]
                cases hdeclaration : declarations function with
                | none => simp [rewriteCtx, rewriteDeclEnv, hdeclaration]
                | some declaration =>
                    simp [rewriteCtx, rewriteDeclEnv, hdeclaration,
                      declArity_rewriteDeclaration]
        | apply function atoms =>
            simp only [runOp]
            cases hfunction : resolveAtom environment function with
            | error error => rfl
            | ok value =>
                cases harguments : resolveAtoms environment atoms with
                | error error => rfl
                | ok arguments =>
                    exact smaller.applyGo store value arguments
        | extern function atoms =>
            simp [runOp, rewriteCtx, callScalarOracle]
      · intro function arguments store
        simp only [IxIR1.invoke, rewriteCtx, rewriteDeclEnv]
        rw [hbefore]
        cases hdeclaration : declarations function with
        | none => simp
        | some declaration =>
            cases declaration with
            | extern arity =>
                simp [rewriteDeclaration, callScalarOracle]
            | fn definition =>
                simp only [Option.map_some,
                  rewriteDeclaration]
                by_cases harity : arguments.length = definition.arity
                · have harityBool :
                      (arguments.length != definition.arity) = false := by
                    simp [harity]
                  simp only [rewriteCurrent, harityBool,
                    Bool.false_eq_true, ↓reduceIte]
                  have hbody :
                      runCode before fuel
                          (rewriteCurrent declarations summaries definition)
                          store arguments.reverse
                          (rewriteCurrent declarations summaries
                            definition).body =
                        runCode before fuel definition store arguments.reverse
                          definition.body := by
                    calc
                      runCode before fuel
                          (rewriteCurrent declarations summaries definition)
                          store arguments.reverse
                          (rewriteCurrent declarations summaries
                            definition).body =
                        runCode before fuel
                          (rewriteCurrent declarations summaries definition)
                          store arguments.reverse
                          (runRecursive declarations summaries
                            definition.body).code := rfl
                      _ = runCode before fuel definition store
                          arguments.reverse definition.body :=
                        runCode_runRecursive_rewriteCurrent_eq hpost hbefore
                  have hcombined :=
                    (smaller.runCode
                      (rewriteCurrent declarations summaries definition) store
                      arguments.reverse
                      (rewriteCurrent declarations summaries definition).body).trans
                        hbody
                  simpa only [rewriteCtx, rewriteCurrent, bind,
                    Except.bind] using
                    congrArg
                      (fun output =>
                        output >>= checkResultWorld definition.result)
                      hcombined
                · simp [rewriteCurrent, harity]
      · intro store function arguments
        cases function with
        | lit literal => simp [IxIR1.applyGo]
        | erased =>
            simp only [IxIR1.applyGo]
            rw [smaller.dropMany store arguments]
        | loc location =>
            simp only [IxIR1.applyGo]
            cases hbox : store.get? location with
            | none => simp
            | some box =>
                simp only
                cases hnode : box.node with
                | ctorN identity fields => simp
                | papN called arity captured =>
                    simp only
                    cases hdup : dupVals store captured.toList with
                    | error error => simp [bind, Except.bind]
                    | ok duplicated =>
                        simp only [bind, Except.bind]
                        rw [smaller.dropVal duplicated (.loc location)]
                        cases hdrop : IxIR1.dropVal before fuel duplicated
                            (.loc location) with
                        | error error => rfl
                        | ok dropped =>
                            let total := captured.toList ++ arguments
                            change (if total.length < arity then
                                let (next, fresh) := dropped.allocNode .shared
                                  (.papN called arity total.toArray)
                                .ok (next, .loc fresh)
                              else if total.length == arity then
                                IxIR1.invoke
                                  (rewriteCtx declarations summaries before)
                                  fuel called total dropped
                              else do
                                let (next, value) ← IxIR1.invoke
                                  (rewriteCtx declarations summaries before)
                                  fuel called (total.take arity) dropped
                                IxIR1.applyGo
                                  (rewriteCtx declarations summaries before)
                                  fuel next value (total.drop arity)) =
                              (if total.length < arity then
                                let (next, fresh) := dropped.allocNode .shared
                                  (.papN called arity total.toArray)
                                .ok (next, .loc fresh)
                              else if total.length == arity then
                                IxIR1.invoke before fuel called total dropped
                              else do
                                let (next, value) ← IxIR1.invoke before fuel
                                  called (total.take arity) dropped
                                IxIR1.applyGo before fuel next value
                                  (total.drop arity))
                            by_cases hless : total.length < arity
                            · simp [hless]
                            · simp only [hless]
                              by_cases hequal : total.length == arity
                              · simp only [hequal]
                                exact smaller.invoke called total dropped
                              · simp only [hequal]
                                rw [smaller.invoke called (total.take arity)
                                  dropped]
                                cases hinvoke : IxIR1.invoke before fuel called
                                    (total.take arity) dropped with
                                | error error => rfl
                                | ok output =>
                                    rcases output with ⟨next, value⟩
                                    exact smaller.applyGo next value
                                      (total.drop arity)
      · intro store value
        cases value with
        | lit literal => simp [IxIR1.dropVal]
        | erased => simp [IxIR1.dropVal]
        | loc location =>
            simp only [IxIR1.dropVal]
            cases hbox : store.get? location with
            | none => simp
            | some box =>
                simp only
                cases hworld : box.world with
                | unique => simp
                | shared =>
                    simp only
                    by_cases hone : box.rc == 1
                    · simp only [hone, ↓reduceIte]
                      cases hnode : box.node with
                      | ctorN identity fields =>
                          simpa [hnode] using smaller.dropMany
                            (store.rcTick.kill location) fields.toList
                      | papN function arity arguments =>
                          simpa [hnode] using smaller.dropMany
                            (store.rcTick.kill location) arguments.toList
                    · simp [hone]
      · intro store values
        cases values with
        | nil => simp [IxIR1.dropMany]
        | cons value rest =>
            simp only [IxIR1.dropMany]
            rw [smaller.dropVal store value]
            cases hdrop : IxIR1.dropVal before fuel store value with
            | error error => rfl
            | ok next => exact smaller.dropMany next rest
      · intro store value
        cases value with
        | lit literal => simp [IxIR1.dropUVal]
        | erased => simp [IxIR1.dropUVal]
        | loc location =>
            simp only [IxIR1.dropUVal]
            cases hbox : store.get? location with
            | none => simp
            | some box =>
                simp only
                cases hworld : box.world with
                | shared => simp
                | unique =>
                    simp only
                    cases hnode : box.node with
                    | ctorN identity fields =>
                        simpa [hnode] using smaller.dropManyU
                          (store.kill location) fields.toList
                    | papN function arity arguments => simp
      · intro store values
        cases values with
        | nil => simp [IxIR1.dropManyU]
        | cons value rest =>
            simp only [IxIR1.dropManyU]
            rw [smaller.dropUVal store value]
            cases hdrop : IxIR1.dropUVal before fuel store value with
            | error error => rfl
            | ok next => exact smaller.dropManyU next rest

/-- Replacing every declaration body under the existing keys is evaluator
equivalent for arbitrary code and dynamic current frames. -/
theorem runCode_rewriteCtx_eq
    {declarations : DeclEnv} {summaries : SummaryEnv}
    (hpost : LocalPostFixpoint declarations summaries)
    {ctx : Ctx} {current : FnDef} {store : Store}
    {environment : List RVal} {input : Code} {fuel : Nat}
    (hctx : ctx.decls = declarations) :
    runCode (rewriteCtx declarations summaries ctx) fuel current store
        environment input =
      runCode ctx fuel current store environment input :=
  (evalRewriteAt hpost hctx fuel).runCode current store environment input

/-- Logical whole-program rewrite: declaration bodies and the main/current
frame are pruned together, with exact equality of successes and every error. -/
theorem runMain_rewriteProgram_eq
    {declarations : DeclEnv} {summaries : SummaryEnv}
    (hpost : LocalPostFixpoint declarations summaries)
    {ctx : Ctx} {input : Code} {fuel : Nat}
    (hctx : ctx.decls = declarations) :
    runMain (rewriteCtx declarations summaries ctx)
        (runRecursive declarations summaries input).code fuel =
      runMain ctx input fuel := by
  calc
    runMain (rewriteCtx declarations summaries ctx)
        (runRecursive declarations summaries input).code fuel =
      runMain ctx (runRecursive declarations summaries input).code fuel := by
        simpa [runMain] using
          (runCode_rewriteCtx_eq hpost
            (current := ⟨0, .shared,
              (runRecursive declarations summaries input).code⟩)
            (store := {}) (environment := [])
            (input := (runRecursive declarations summaries input).code)
            (fuel := fuel) hctx)
    _ = runMain ctx input fuel := runMain_runRecursive_eq hpost hctx

private theorem find?_rewriteEntries
    (declarations : DeclEnv) (summaries : SummaryEnv)
    (address : Compilatrix.Ixon.Address) :
    ∀ entries : List (Compilatrix.Ixon.Address × Decl),
      (rewriteEntries declarations summaries entries).find?
          (fun entry => entry.1 == address) =
        (entries.find? (fun entry => entry.1 == address)).map
          (fun entry =>
            (entry.1,
              rewriteDeclaration declarations summaries entry.2)) := by
  intro entries
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨entryAddress, declaration⟩
      simp only [rewriteEntries, List.map_cons, List.find?_cons]
      by_cases hsame : entryAddress == address
      · simp [hsame]
      · simp only [hsame]
        exact ih

/-- Mapping the declarations in a concrete list realizes exactly the logical
environment transformer used by the semantic theorem. -/
theorem envOfList_rewriteEntries
    (declarations : DeclEnv) (summaries : SummaryEnv)
    (entries : List (Compilatrix.Ixon.Address × Decl)) :
    Env.ofList (rewriteEntries declarations summaries entries) =
      fun address =>
        (Env.ofList entries address).map
          (rewriteDeclaration declarations summaries) := by
  funext address
  unfold Env.ofList
  rw [find?_rewriteEntries]
  cases hentry : entries.find? (fun entry => entry.1 == address) with
  | none => rfl
  | some entry =>
      rcases entry with ⟨entryAddress, declaration⟩
      rfl

/-! ## Content-addressed program rebuild -/

/-- Collect all pass-attributed counters from one stored declaration with one
recursive syntax traversal. -/
def declarationChanges (declarations : DeclEnv)
    (summaries : SummaryEnv) : Decl → Changes
  | .fn function =>
      (runRecursive declarations summaries function.body).changes
  | .extern _ => {}

/-- Sum declaration-body changes in original row order. -/
def declarationsChanges (declarations : DeclEnv)
    (summaries : SummaryEnv)
    (entries : List (Compilatrix.Ixon.Address × Decl)) : Changes :=
  entries.foldl (fun total entry =>
    total.add (declarationChanges declarations summaries entry.2)) {}

/-- Observable result of simplifying every function body and the main, then
rebuilding the complete content-addressed declaration graph. -/
structure ProgramOutcome where
  result : ReaddressAll.Result
  removedAlternatives : Nat
  collapsedCases : Nat
  materializedFetches : Nat

/-- Readdress a complete already-addressed program after recursive HPT case
simplification.  This low-level operation consumes supplied summaries; checked
pipeline entry points first validate those summaries against `program`. -/
def rebuildProgram (reserved : List Compilatrix.Ixon.Address)
    (program : List ReaddressAll.Artifact) (summaries : SummaryEnv)
    (main : Code) : Except String ProgramOutcome := do
  let declarations := programDeclEnv program
  let entries := declarationEntries program
  let rewritten := rewriteEntries declarations summaries entries
  let rewrittenMain := runRecursive declarations summaries main
  let declarationChanges := declarationsChanges declarations summaries entries
  let result ← ReaddressAll.rebuild reserved rewritten rewrittenMain.code
  return ⟨result, rewrittenMain.removedAlternatives +
      declarationChanges.removedAlternatives,
    rewrittenMain.collapsedCases +
      declarationChanges.collapsedCases,
    rewrittenMain.materializedFetches +
      declarationChanges.materializedFetches⟩

theorem rebuild_of_rebuildProgram_eq_ok
    {reserved : List Compilatrix.Ixon.Address}
    {program : List ReaddressAll.Artifact} {summaries : SummaryEnv}
    {main : Code} {outcome : ProgramOutcome}
    (hrun : rebuildProgram reserved program summaries main = .ok outcome) :
    ReaddressAll.rebuild reserved
        (rewriteEntries (programDeclEnv program) summaries
          (declarationEntries program))
        (runRecursive (programDeclEnv program) summaries main).code =
      .ok outcome.result := by
  unfold rebuildProgram at hrun
  simp only [bind, Except.bind] at hrun
  cases hrebuild : ReaddressAll.rebuild reserved
      (rewriteEntries (programDeclEnv program) summaries
        (declarationEntries program))
      (runRecursive (programDeclEnv program) summaries main).code with
  | error message =>
      rw [hrebuild] at hrun
      contradiction
  | ok result =>
      rw [hrebuild] at hrun
      have houtcome :
          (⟨result,
            (runRecursive (programDeclEnv program) summaries main).removedAlternatives +
              (declarationsChanges (programDeclEnv program) summaries
                (declarationEntries program)).removedAlternatives,
            (runRecursive (programDeclEnv program) summaries main).collapsedCases +
              (declarationsChanges (programDeclEnv program) summaries
                (declarationEntries program)).collapsedCases,
            (runRecursive (programDeclEnv program) summaries main).materializedFetches +
              (declarationsChanges (programDeclEnv program) summaries
                (declarationEntries program)).materializedFetches⟩ :
              ProgramOutcome) =
            outcome := by
        injection hrun
      have hresult : result = outcome.result :=
        congrArg ProgramOutcome.result houtcome
      exact congrArg Except.ok hresult

/-- The HPT program environment is the transparent first-binding-wins lookup
of the same declaration rows passed to the rebuild. -/
theorem envOfList_declarationEntries
    (program : List ReaddressAll.Artifact) :
    Env.ofList (declarationEntries program) = programDeclEnv program := by
  exact (AddressEnv.lookup_build (declarationEntries program)).symm

/-- Old-keyed context paired with the oracle pullback of an exact rebuild.
Its declaration environment is the unmodified program environment. -/
def rebuildOriginalCtx (result : ReaddressAll.Result)
    (rewritten : List (Compilatrix.Ixon.Address × Decl))
    (declarations : DeclEnv)
    (oracle : Compilatrix.Ixon.Address → List RVal → Option RVal) : Ctx :=
  { decls := declarations
    oracle := (result.rebuildSourceCtx rewritten oracle).oracle }

/-- Rebuilding the logically rewritten graph transports the complete
evaluator result from the exact old-keyed program context. -/
theorem runMain_rebuild_rewriteProgram
    {reserved : List Compilatrix.Ixon.Address}
    {entries : List (Compilatrix.Ixon.Address × Decl)}
    {declarations : DeclEnv} {summaries : SummaryEnv} {main : Code}
    {result : ReaddressAll.Result}
    (hentries : Env.ofList entries = declarations)
    (hpost : LocalPostFixpoint declarations summaries)
    (hrebuild : ReaddressAll.rebuild reserved
      (rewriteEntries declarations summaries entries)
      (runRecursive declarations summaries main).code = .ok result)
    (oracle : Compilatrix.Ixon.Address → List RVal → Option RVal :=
      fun _ _ => none)
    (fuel : Nat := 100000) :
    runMain (result.addressedCtx oracle) result.main fuel =
      Readdress.mapRunResult
        (result.rebuildRename
          (rewriteEntries declarations summaries entries))
        (runMain
          (rebuildOriginalCtx result
            (rewriteEntries declarations summaries entries)
            declarations oracle)
          main fuel) := by
  let rewritten := rewriteEntries declarations summaries entries
  let before := rebuildOriginalCtx result rewritten declarations oracle
  have hbefore : before.decls = declarations := rfl
  have hctx : rewriteCtx declarations summaries before =
      result.rebuildSourceCtx rewritten oracle := by
    simp [rewriteCtx, before, rewritten, rebuildOriginalCtx,
      ReaddressAll.Result.rebuildSourceCtx,
      envOfList_rewriteEntries, hentries]
    funext address
    rfl
  rw [ReaddressAll.runMain_exact_of_rebuild_eq_ok hrebuild oracle fuel]
  apply congrArg (Readdress.mapRunResult
    (result.rebuildRename rewritten))
  rw [← hctx]
  exact runMain_rewriteProgram_eq hpost hbefore

/-- Successful HPT checking plus successful graph rebuilding authorizes the
exact whole-program evaluator transport theorem. -/
theorem runMain_rebuildProgram_of_runWith_eq_ok
    {limits : Limits} {reserved : List Compilatrix.Ixon.Address}
    {program : List ReaddressAll.Artifact} {certificate : Certificate}
    {analysis : HPT.Result} {main : Code} {outcome : ProgramOutcome}
    (hcheck : HPT.runWith limits program certificate = .ok analysis)
    (hrebuild : rebuildProgram reserved program certificate.summaryEnv main =
      .ok outcome)
    (oracle : Compilatrix.Ixon.Address → List RVal → Option RVal :=
      fun _ _ => none)
    (fuel : Nat := 100000) :
    runMain (outcome.result.addressedCtx oracle) outcome.result.main fuel =
      Readdress.mapRunResult
        (outcome.result.rebuildRename
          (rewriteEntries (programDeclEnv program) certificate.summaryEnv
            (declarationEntries program)))
        (runMain
          (rebuildOriginalCtx outcome.result
            (rewriteEntries (programDeclEnv program) certificate.summaryEnv
              (declarationEntries program))
            (programDeclEnv program) oracle)
          main fuel) := by
  apply runMain_rebuild_rewriteProgram
  · exact envOfList_declarationEntries program
  · exact localPostFixpoint_of_postFixpoint
      (postFixpoint_of_runWith_eq_ok hcheck)
  · exact rebuild_of_rebuildProgram_eq_ok hrebuild

/-- With the closed default oracle, the source side is exactly the ordinary
old addressed program context. -/
theorem runMain_rebuildProgram_of_runWith_eq_ok_defaultOracle
    {limits : Limits} {reserved : List Compilatrix.Ixon.Address}
    {program : List ReaddressAll.Artifact} {certificate : Certificate}
    {analysis : HPT.Result} {main : Code} {outcome : ProgramOutcome}
    (hcheck : HPT.runWith limits program certificate = .ok analysis)
    (hrebuild : rebuildProgram reserved program certificate.summaryEnv main =
      .ok outcome)
    (fuel : Nat := 100000) :
    runMain (outcome.result.addressedCtx (fun _ _ => none))
        outcome.result.main fuel =
      Readdress.mapRunResult
        (outcome.result.rebuildRename
          (rewriteEntries (programDeclEnv program) certificate.summaryEnv
            (declarationEntries program)))
        (runMain { decls := programDeclEnv program } main fuel) := by
  simpa [rebuildOriginalCtx, ReaddressAll.Result.rebuildSourceCtx] using
    (runMain_rebuildProgram_of_runWith_eq_ok hcheck hrebuild
      (fun _ _ => none) fuel)

/-- Checked whole-program specialization.  The result is the exact logical
semantics of the old-keyed declaration list and pruned main, immediately
before content-address rebuilding. -/
theorem runMain_rewriteProgram_eq_of_postFixpoint
    {program : List ReaddressAll.Artifact} {certificate : Certificate}
    (hcertificate : certificate.postFixpoint program = true)
    {ctx : Ctx} {input : Code} {fuel : Nat}
    (hctx : ctx.decls = programDeclEnv program) :
    runMain
        (rewriteCtx (programDeclEnv program) certificate.summaryEnv ctx)
        (runRecursive (programDeclEnv program) certificate.summaryEnv
          input).code fuel =
      runMain ctx input fuel := by
  exact runMain_rewriteProgram_eq
    (localPostFixpoint_of_postFixpoint hcertificate) hctx

/-- Successful configurable checking authorizes simultaneous rewriting of
the complete logical declaration environment and main/current frame. -/
theorem runMain_rewriteProgram_eq_of_runWith_eq_ok
    {limits : Limits} {program : List ReaddressAll.Artifact}
    {certificate : Certificate} {result : Result}
    (hcheck : HPT.runWith limits program certificate = .ok result)
    {ctx : Ctx} {input : Code} {fuel : Nat}
    (hctx : ctx.decls = programDeclEnv program) :
    runMain
        (rewriteCtx (programDeclEnv program) certificate.summaryEnv ctx)
        (runRecursive (programDeclEnv program) certificate.summaryEnv
          input).code fuel =
      runMain ctx input fuel := by
  exact runMain_rewriteProgram_eq_of_postFixpoint
    (postFixpoint_of_runWith_eq_ok hcheck) hctx

end Compilatrix.IxIR1.HPT.CasePrune
