import Ix.Compiler.IxIR1.HPTCasePrune
import Ix.Compiler.IxIR1.EvalRewrite
import Ix.Compiler.IxIR1.ReaddressAllSim

/-!
# Whole-program semantic support for HPT case simplification

`HPTCasePrune` proves supplied fragments equivalent in a fixed environment and
proves each owner-sensitive, fact-propagated function rewrite equivalent in
its original frame.  Rewriting every stored function changes the environment
itself: direct calls and PAP application subsequently enter the rewritten
definitions.  This module discharges the generic exact-environment contract;
`EvalRewrite` closes that recursive seam once by a common fuel induction over
every evaluator entry point.

The result is still a logical, old-keyed environment.  A production artifact
must readdress `rewriteEntries`; that content-address rebuild is kept separate
so no theorem silently treats changed declaration bytes as retaining their old
identity.
-/

namespace Ix.Compiler.IxIR1.HPT.CasePrune

/-- The logical case-pruned declaration environment preserves misses, externs,
calling conventions, and exact source-context behavior for every function. -/
theorem exactEnvironment_rewriteCtx
    {declarations : DeclEnv} {summaries : SummaryEnv}
    (hpost : LocalPostFixpoint declarations summaries)
    {ctx : Ctx} (hctx : ctx.decls = declarations) :
    Sim.ExactEnvironment ctx (rewriteCtx declarations summaries ctx) := by
  constructor
  · rfl
  · intro address hsource
    have hdeclaration : declarations address = none := by
      rw [← hctx]
      exact hsource
    simp [rewriteCtx, rewriteDeclEnv, hdeclaration]
  · intro address arity hsource
    have hdeclaration : declarations address = some (.extern arity) := by
      rw [← hctx]
      exact hsource
    simp [rewriteCtx, rewriteDeclEnv, hdeclaration, rewriteDeclarationAt]
  · intro address source hsource
    have hdeclaration : declarations address = some (.fn source) := by
      rw [← hctx]
      exact hsource
    refine ⟨rewriteCurrentAt declarations summaries address source, ?_,
      rfl, rfl, rfl, ?_⟩
    · simp [rewriteCtx, rewriteDeclEnv, hdeclaration, rewriteDeclarationAt]
    · intro fuel store environment hlength
      have henvironment : EnvironmentHolds declarations store
          (List.replicate source.arity Fact.top) environment := by
        simpa [hlength] using
          (EnvironmentHolds.top_replicate declarations store environment)
      exact runCode_rewriteCurrentAt_body_eq hpost hctx hdeclaration
        henvironment

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
  Sim.runCode_exactEnvironment_eq (exactEnvironment_rewriteCtx hpost hctx)

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
            (current := ⟨0, .shared, false,
              (runRecursive declarations summaries input).code⟩)
            (store := {}) (environment := [])
            (input := (runRecursive declarations summaries input).code)
            (fuel := fuel) hctx)
    _ = runMain ctx input fuel := runMain_runRecursive_eq hpost hctx

private theorem find?_rewriteEntries
    (declarations : DeclEnv) (summaries : SummaryEnv)
    (address : Ix.Compiler.Ixon.Address) :
    ∀ entries : List (Ix.Compiler.Ixon.Address × Decl),
      (rewriteEntries declarations summaries entries).find?
          (fun entry => entry.1 == address) =
        (entries.find? (fun entry => entry.1 == address)).map
          (fun entry =>
            (entry.1,
              rewriteDeclarationAt declarations summaries entry.1
                entry.2)) := by
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
    (entries : List (Ix.Compiler.Ixon.Address × Decl)) :
    Env.ofList (rewriteEntries declarations summaries entries) =
      fun address =>
        (Env.ofList entries address).map
          (rewriteDeclarationAt declarations summaries address) := by
  funext address
  unfold Env.ofList
  rw [find?_rewriteEntries]
  cases hentry : entries.find? (fun entry => entry.1 == address) with
  | none => rfl
  | some entry =>
      rcases entry with ⟨entryAddress, declaration⟩
      have hsame := List.find?_some hentry
      have haddress : entryAddress = address := beq_iff_eq.mp hsame
      subst entryAddress
      rfl

/-! ## Content-addressed program rebuild -/

/-- Collect all pass-attributed counters from one stored declaration with its
owner-sensitive fact traversal. -/
def declarationChanges (declarations : DeclEnv)
    (summaries : SummaryEnv) (owner : Ix.Compiler.Ixon.Address) :
    Decl → Changes
  | .fn function =>
      (runFunction declarations summaries owner function).changes
  | .extern _ => {}

/-- Sum declaration-body changes in original row order. -/
def declarationsChanges (declarations : DeclEnv)
    (summaries : SummaryEnv)
    (entries : List (Ix.Compiler.Ixon.Address × Decl)) : Changes :=
  entries.foldl (fun total entry =>
    total.add
      (declarationChanges declarations summaries entry.1 entry.2)) {}

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
def rebuildProgram (reserved : List Ix.Compiler.Ixon.Address)
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
    {reserved : List Ix.Compiler.Ixon.Address}
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
    (rewritten : List (Ix.Compiler.Ixon.Address × Decl))
    (declarations : DeclEnv)
    (oracle : Ix.Compiler.Ixon.Address → List RVal → Option RVal) : Ctx :=
  { decls := declarations
    oracle := (result.rebuildSourceCtx rewritten oracle).oracle }

/-- Rebuilding the logically rewritten graph transports the complete
evaluator result from the exact old-keyed program context. -/
theorem runMain_rebuild_rewriteProgram
    {reserved : List Ix.Compiler.Ixon.Address}
    {entries : List (Ix.Compiler.Ixon.Address × Decl)}
    {declarations : DeclEnv} {summaries : SummaryEnv} {main : Code}
    {result : ReaddressAll.Result}
    (hentries : Env.ofList entries = declarations)
    (hpost : LocalPostFixpoint declarations summaries)
    (hrebuild : ReaddressAll.rebuild reserved
      (rewriteEntries declarations summaries entries)
      (runRecursive declarations summaries main).code = .ok result)
    (oracle : Ix.Compiler.Ixon.Address → List RVal → Option RVal :=
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
    {limits : Limits} {reserved : List Ix.Compiler.Ixon.Address}
    {program : List ReaddressAll.Artifact} {certificate : Certificate}
    {analysis : HPT.Result} {main : Code} {outcome : ProgramOutcome}
    (hcheck : HPT.runWith limits program certificate = .ok analysis)
    (hrebuild : rebuildProgram reserved program certificate.summaryEnv main =
      .ok outcome)
    (oracle : Ix.Compiler.Ixon.Address → List RVal → Option RVal :=
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
    {limits : Limits} {reserved : List Ix.Compiler.Ixon.Address}
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

end Ix.Compiler.IxIR1.HPT.CasePrune
