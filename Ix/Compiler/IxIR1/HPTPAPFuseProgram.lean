import Ix.Compiler.IxIR1.HPTCasePruneProgram
import Ix.Compiler.IxIR1.HPTDestroy
import Ix.Compiler.IxIR1.Reachability

/-!
# One-rebuild composition of checked HPT consumers

Case simplification, scalar fetch forwarding, shape-specialized destruction,
and local PAP fusion all consume the same old-keyed HPT certificate.
Readdressing between them would invalidate those keys.  This module therefore
composes their logical declaration/main rewrites first and performs one
complete content-address rebuild.

Case simplification runs first.  Its unary collapse retains binder depth by
materializing a fetch.  Fetch forwarding then replaces only certified scalar
allocation/reuse projections, destruction removes certified scalar work and
specializes exact unique leaves, and PAP fusion analyzes the resulting code
with the same owner, arity, and entry fact environment.
-/

namespace Ix.Compiler.IxIR1.HPT.OptimizeProgram

open Ix.Compiler.Ixon (Address)
open Ix.Compiler.IxIR1.Sim

structure Passes where
  casePrune : Bool := true
  fetchForward : Bool := true
  destroy : Bool := true
  papFuse : Bool := true
  reachability : Bool := true
  roots : List Address := []
  deriving BEq, Repr

structure Changes where
  casePrune : CasePrune.Changes := {}
  fetchForward : FetchForward.Changes := {}
  destroy : Destroy.Changes := {}
  papFuse : PAPFuse.Changes := {}
  removedDeclarations : Nat := 0

def Changes.add (left right : Changes) : Changes :=
  { casePrune := left.casePrune.add right.casePrune
    fetchForward := left.fetchForward.add right.fetchForward
    destroy := left.destroy.add right.destroy
    papFuse := left.papFuse.add right.papFuse
    removedDeclarations :=
      left.removedDeclarations + right.removedDeclarations }

structure CodeOutcome where
  code : Code
  changes : Changes := {}

def rewriteCode (passes : Passes) (declarations : DeclEnv)
    (summaries : SummaryEnv) (owner : Address) (current : FnDef)
    (facts : List Fact) (input : Code) : CodeOutcome :=
  let pruned : CasePrune.Outcome :=
    if passes.casePrune then
      CasePrune.runWithFacts declarations summaries owner current facts input
    else
      { code := input, removedAlternatives := 0, collapsedCases := 0,
        materializedFetches := 0 }
  let forwarded : FetchForward.Outcome :=
    if passes.fetchForward then
      FetchForward.runWithFacts declarations summaries owner current facts
        pruned.code
    else
      { code := pruned.code, changes := {} }
  let destroyed : Destroy.Outcome :=
    if passes.destroy then
      Destroy.runWithFacts declarations summaries owner current facts
        forwarded.code
    else
      { code := forwarded.code, changes := {} }
  let fused : PAPFuse.Outcome :=
    if passes.papFuse then
      PAPFuse.runWithFacts declarations summaries owner current facts
        destroyed.code
    else
      { code := destroyed.code, changes := {} }
  { code := fused.code
    changes :=
      { casePrune := pruned.changes
        fetchForward := forwarded.changes
        destroy := destroyed.changes
        papFuse := fused.changes } }

def rewriteDeclaration (passes : Passes)
    (declarations : DeclEnv) (summaries : SummaryEnv)
    (owner : Address) : Decl → Decl × Changes
  | .extern arity => (.extern arity, {})
  | .fn function =>
      let rewritten := rewriteCode passes declarations summaries owner function
        (List.replicate function.arity Fact.top) function.body
      (.fn { function with body := rewritten.code }, rewritten.changes)

/-- Logical old-keyed declaration environment for the composed consumers. -/
def rewriteDeclEnv (passes : Passes) (declarations : DeclEnv)
    (summaries : SummaryEnv) : DeclEnv :=
  fun owner => (declarations owner).map fun declaration =>
    (rewriteDeclaration passes declarations summaries owner declaration).1

/-- Retain the oracle while installing the composed logical environment. -/
def rewriteCtx (passes : Passes) (declarations : DeclEnv)
    (summaries : SummaryEnv) (ctx : Ctx) : Ctx :=
  { ctx with decls := rewriteDeclEnv passes declarations summaries }

@[simp] theorem declArity_rewriteDeclaration
    (passes : Passes) (declarations : DeclEnv) (summaries : SummaryEnv)
    (owner : Address) (declaration : Decl) :
    declArity
        (rewriteDeclaration passes declarations summaries owner declaration).1 =
      declArity declaration := by
  cases declaration <;> rfl

/-- All checked consumers compose under the original owner/current analysis
frame.  Case pruning and fetch forwarding are exact; destruction preserves
successful outcomes and PAP fusion may change allocation history. -/
theorem rewriteCode_staticBodyRefines
    {passes : Passes} {declarations : DeclEnv} {summaries : SummaryEnv}
    (hpost : LocalPostFixpoint declarations summaries)
    {ctx : Ctx} {owner : Address} {current : FnDef}
    (hctx : ctx.decls = declarations)
    (hcurrent : declarations owner = some (.fn current)) :
    StaticFunctionBodyRefines ctx current
      { current with body :=
          (rewriteCode passes declarations summaries owner current
            (List.replicate current.arity Fact.top) current.body).code } := by
  intro fuel store environment sourceOut base hlength henvironment hrun
  let facts := List.replicate current.arity Fact.top
  let pruned : CasePrune.Outcome :=
    if passes.casePrune then
      CasePrune.runWithFacts declarations summaries owner current facts
        current.body
    else
      { code := current.body, removedAlternatives := 0, collapsedCases := 0,
        materializedFetches := 0 }
  have htop : EnvironmentHolds declarations store facts environment := by
    simpa [facts, hlength] using
      (EnvironmentHolds.top_replicate declarations store environment)
  have hpruned : runCode ctx fuel current store environment pruned.code =
      .ok sourceOut := by
    cases hcase : passes.casePrune with
    | false => simpa [pruned, hcase] using hrun
    | true =>
        have heq := CasePrune.runCode_runWithFacts_eq hpost hctx hcurrent htop
          (input := current.body) (fuel := fuel)
        simpa [pruned, hcase] using heq.trans hrun
  let forwarded : FetchForward.Outcome :=
    if passes.fetchForward then
      FetchForward.runWithFacts declarations summaries owner current facts
        pruned.code
    else
      { code := pruned.code, changes := {} }
  have hforwarded :
      runCode ctx fuel current store environment forwarded.code =
        .ok sourceOut := by
    cases hfetch : passes.fetchForward with
    | false => simpa [forwarded, hfetch] using hpruned
    | true =>
        have heq := FetchForward.runCode_runWithFacts_eq hpost hctx hcurrent
          htop (input := pruned.code) (fuel := fuel)
        simpa [forwarded, hfetch] using heq.trans hpruned
  let destroyed : Destroy.Outcome :=
    if passes.destroy then
      Destroy.runWithFacts declarations summaries owner current facts
        forwarded.code
    else
      { code := forwarded.code, changes := {} }
  have hdestroyed :
      runCode ctx fuel current store environment destroyed.code =
        .ok sourceOut := by
    cases hdestroy : passes.destroy with
    | false => simpa [destroyed, hdestroy] using hforwarded
    | true =>
        have hrefines := Destroy.runCode_runWithFacts_success hpost hctx
          hcurrent htop hforwarded
        simpa [destroyed, hdestroy] using hrefines
  cases hpap : passes.papFuse with
  | false =>
      obtain ⟨targetOut, htargetRun, hiso⟩ :=
        runCode_historyIso base henvironment hdestroyed
      exact ⟨targetOut, by
        simpa [rewriteCode, facts, pruned, forwarded, destroyed, hpap]
          using htargetRun, hiso⟩
  | true =>
      obtain ⟨targetOut, htargetRun, hiso⟩ :=
        PAPFuse.runCode_runWithFacts_refines hpost hctx hcurrent base
          henvironment htop hdestroyed
      exact ⟨targetOut, by
        simpa [rewriteCode, facts, pruned, forwarded, destroyed, hpap]
          using htargetRun, hiso⟩

/-- Closing the rewritten current-frame fixed point turns the composed local
rewrite into the function obligation required by `AbstractEnvironment`. -/
theorem rewriteCode_bodyRefines
    {passes : Passes} {declarations : DeclEnv} {summaries : SummaryEnv}
    (hpost : LocalPostFixpoint declarations summaries)
    {ctx : Ctx} {owner : Address} {current : FnDef}
    (hctx : ctx.decls = declarations)
    (hcurrent : declarations owner = some (.fn current)) :
    FunctionBodyRefines ctx current
      { current with body :=
          (rewriteCode passes declarations summaries owner current
            (List.replicate current.arity Fact.top) current.body).code } :=
  FunctionBodyRefines.ofStatic
    (rewriteCode_staticBodyRefines hpost hctx hcurrent) rfl rfl

/-- Every old-keyed declaration lookup is preserved by the composed logical
environment, with rewritten functions related by their local body theorem. -/
theorem abstractEnvironment_rewriteCtx
    {passes : Passes} {declarations : DeclEnv} {summaries : SummaryEnv}
    (hpost : LocalPostFixpoint declarations summaries)
    {ctx : Ctx} (hctx : ctx.decls = declarations) :
    AbstractEnvironment ctx (rewriteCtx passes declarations summaries ctx) := by
  constructor
  · rfl
  · intro address arity hsource
    have hdeclaration : declarations address = some (.extern arity) := by
      rw [← hctx]
      exact hsource
    simp [rewriteCtx, rewriteDeclEnv, hdeclaration, rewriteDeclaration]
  · intro address source hsource
    have hdeclaration : declarations address = some (.fn source) := by
      rw [← hctx]
      exact hsource
    let target : FnDef :=
      { source with body :=
          (rewriteCode passes declarations summaries address source
            (List.replicate source.arity Fact.top) source.body).code }
    refine ⟨target, ?_, rfl, rfl, rfl, ?_⟩
    · simp [rewriteCtx, rewriteDeclEnv, hdeclaration,
        rewriteDeclaration, target]
    · exact rewriteCode_bodyRefines hpost hctx hdeclaration

/-- Successful evaluation is preserved after logically replacing every
stored function by the composed owner-sensitive rewrite. -/
theorem runCode_rewriteCtx_refines
    {passes : Passes} {declarations : DeclEnv} {summaries : SummaryEnv}
    (hpost : LocalPostFixpoint declarations summaries)
    {ctx : Ctx} {current : FnDef} {left right : Store} {fuel : Nat}
    {leftEnvironment rightEnvironment : List RVal}
    {input : Code} {sourceOut : Store × RVal}
    (hctx : ctx.decls = declarations)
    (heap : HeapHistoryIso left right)
    (henvironments : RValsIso heap.locRel
      leftEnvironment rightEnvironment)
    (hrun : runCode ctx fuel current left leftEnvironment input =
      .ok sourceOut) :
    ∃ targetOut,
      runCode (rewriteCtx passes declarations summaries ctx) fuel current right
          rightEnvironment input = .ok targetOut ∧
        RunHistoryIso heap sourceOut targetOut :=
  runCode_abstractEnvironment
    (abstractEnvironment_rewriteCtx hpost hctx) heap henvironments hrun

def rewriteEntries (passes : Passes) (declarations : DeclEnv)
    (summaries : SummaryEnv) (entries : List (Address × Decl)) :
    List (Address × Decl) :=
  entries.map fun entry =>
    (entry.1,
      (rewriteDeclaration passes declarations summaries entry.1 entry.2).1)

def declarationsChanges (passes : Passes) (declarations : DeclEnv)
    (summaries : SummaryEnv) (entries : List (Address × Decl)) : Changes :=
  entries.foldl
    (fun total entry =>
      total.add
        (rewriteDeclaration passes declarations summaries entry.1 entry.2).2)
    {}

private theorem find?_rewriteEntries
    (passes : Passes) (declarations : DeclEnv) (summaries : SummaryEnv)
    (address : Address) :
    ∀ entries : List (Address × Decl),
      (rewriteEntries passes declarations summaries entries).find?
          (fun entry => entry.1 == address) =
        (entries.find? (fun entry => entry.1 == address)).map
          (fun entry =>
            (entry.1,
              (rewriteDeclaration passes declarations summaries address
                entry.2).1)) := by
  intro entries
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨entryAddress, declaration⟩
      simp only [rewriteEntries, List.map_cons, List.find?_cons]
      by_cases hsame : entryAddress == address
      · have haddress : entryAddress = address := beq_iff_eq.mp hsame
        subst entryAddress
        simp
      · simp only [hsame]
        exact ih

/-- Mapping a concrete declaration list realizes the composed logical
old-keyed environment. -/
theorem envOfList_rewriteEntries
    (passes : Passes) (declarations : DeclEnv) (summaries : SummaryEnv)
    (entries : List (Address × Decl)) :
    Env.ofList (rewriteEntries passes declarations summaries entries) =
      fun address =>
        (Env.ofList entries address).map
          (fun declaration =>
            (rewriteDeclaration passes declarations summaries address
              declaration).1) := by
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

/-- Main code has no stored declaration owner.  Case pruning retains its
fixed-environment compatibility traversal.  Fetch forwarding, destruction,
and PAP fusion use the all-zero address only as the fail-soft `callSelf`
analysis owner; ordinary heap operations, direct calls, PAPs, and applies are
unaffected by that placeholder. -/
def rewriteMain (passes : Passes) (declarations : DeclEnv)
    (summaries : SummaryEnv) (main : Code) : CodeOutcome :=
  let pruned : CasePrune.Outcome :=
    if passes.casePrune then
      CasePrune.runRecursive declarations summaries main
    else
      { code := main
        removedAlternatives := 0
        collapsedCases := 0
        materializedFetches := 0 }
  let current : FnDef := ⟨0, .shared, false, pruned.code⟩
  let forwarded : FetchForward.Outcome :=
    if passes.fetchForward && (summaries default).isNone then
      FetchForward.runWithFacts declarations summaries default current []
        pruned.code
    else
      { code := pruned.code, changes := {} }
  let destroyed : Destroy.Outcome :=
    if passes.destroy && (summaries default).isNone then
      Destroy.runWithFacts declarations summaries default current []
        forwarded.code
    else
      { code := forwarded.code, changes := {} }
  let fused : PAPFuse.Outcome :=
    if passes.papFuse && (summaries default).isNone then
      PAPFuse.runWithFacts declarations summaries default current []
        destroyed.code
    else
      { code := destroyed.code, changes := {} }
  { code := fused.code
    changes :=
      { casePrune := pruned.changes
        fetchForward := forwarded.changes
        destroy := destroyed.changes
        papFuse := fused.changes } }

/-- The canonical entry history for a fresh top-level execution. -/
def emptyHistoryIso : HeapHistoryIso ({} : Store) {} :=
  HeapHistoryIso.refl {} (by
    intro location box hbox
    simp [Store.get?] at hbox)

/-- After recursive case pruning, the guarded owner-sensitive phases are
static rewrites of the zero-arity main frame.  If the sentinel owner has a
summary, all three phases are skipped; otherwise successful self analysis is
impossible and their general owner-compatible theorems apply. -/
theorem rewriteMain_staticBodyRefines
    {passes : Passes} {declarations : DeclEnv} {summaries : SummaryEnv}
    (hpost : LocalPostFixpoint declarations summaries)
    {ctx : Ctx} {main : Code}
    (hctx : ctx.decls = declarations) :
    let pruned : CasePrune.Outcome :=
      if passes.casePrune then
        CasePrune.runRecursive declarations summaries main
      else
        { code := main
          removedAlternatives := 0
          collapsedCases := 0
          materializedFetches := 0 }
    let source : FnDef := ⟨0, .shared, false, pruned.code⟩
    StaticFunctionBodyRefines ctx source
      { source with body :=
          (rewriteMain passes declarations summaries main).code } := by
  let pruned : CasePrune.Outcome :=
    if passes.casePrune then
      CasePrune.runRecursive declarations summaries main
    else
      { code := main
        removedAlternatives := 0
        collapsedCases := 0
        materializedFetches := 0 }
  let source : FnDef := ⟨0, .shared, false, pruned.code⟩
  change StaticFunctionBodyRefines ctx source
    { source with body :=
        (rewriteMain passes declarations summaries main).code }
  intro fuel store environment sourceOut base hlength henvironment hrun
  have hempty : environment = [] := by
    cases environment with
    | nil => rfl
    | cons value rest => simp at hlength
  subst environment
  cases hsummary : summaries default with
  | some summary =>
      obtain ⟨targetOut, htargetRun, hiso⟩ :=
        runCode_historyIso base henvironment hrun
      exact ⟨targetOut, by
        simpa [rewriteMain, source, pruned, hsummary] using htargetRun, hiso⟩
  | none =>
      let forwarded : FetchForward.Outcome :=
        if passes.fetchForward then
          FetchForward.runWithFacts declarations summaries default source []
            pruned.code
        else
          { code := pruned.code, changes := {} }
      have hforwarded :
          runCode ctx fuel source store [] forwarded.code = .ok sourceOut := by
        cases hfetch : passes.fetchForward with
        | false => simpa [forwarded, hfetch] using hrun
        | true =>
            have heq :=
              FetchForward.runCode_runWithFacts_eq_ownerCompatible hpost hctx
                (.inr hsummary) EnvironmentHolds.nil
                (current := source) (store := store)
                (input := pruned.code) (fuel := fuel)
            simpa [forwarded, hfetch] using heq.trans hrun
      let destroyed : Destroy.Outcome :=
        if passes.destroy then
          Destroy.runWithFacts declarations summaries default source []
            forwarded.code
        else
          { code := forwarded.code, changes := {} }
      have hdestroyed :
          runCode ctx fuel source store [] destroyed.code = .ok sourceOut := by
        cases hdestroy : passes.destroy with
        | false => simpa [destroyed, hdestroy] using hforwarded
        | true =>
            have hrefines :=
              Destroy.runCode_runWithFacts_success_ownerCompatible hpost hctx
                (.inr hsummary) EnvironmentHolds.nil hforwarded
            simpa [destroyed, hdestroy] using hrefines
      cases hpap : passes.papFuse with
      | false =>
          obtain ⟨targetOut, htargetRun, hiso⟩ :=
            runCode_historyIso base henvironment hdestroyed
          exact ⟨targetOut, by
            simpa [rewriteMain, source, pruned, forwarded, destroyed, hpap,
              hsummary] using htargetRun, hiso⟩
      | true =>
          obtain ⟨targetOut, htargetRun, hiso⟩ :=
            PAPFuse.runCode_runWithFacts_refines_ownerCompatible hpost hctx
              (.inr hsummary) base henvironment EnvironmentHolds.nil
              hdestroyed
          exact ⟨targetOut, by
            simpa [rewriteMain, source, pruned, forwarded, destroyed, hpap,
              hsummary] using htargetRun, hiso⟩

/-- Rewriting top-level main preserves every successful fresh execution,
including dynamic re-entry through `callSelf`. -/
theorem runMain_rewriteMain_refines
    {passes : Passes} {declarations : DeclEnv} {summaries : SummaryEnv}
    (hpost : LocalPostFixpoint declarations summaries)
    {ctx : Ctx} {main : Code} {fuel : Nat} {sourceOut : Store × RVal}
    (hctx : ctx.decls = declarations)
    (hrun : runMain ctx main fuel = .ok sourceOut) :
    ∃ targetOut,
      runMain ctx (rewriteMain passes declarations summaries main).code fuel =
          .ok targetOut ∧
        RunHistoryIso emptyHistoryIso sourceOut targetOut := by
  let pruned : CasePrune.Outcome :=
    if passes.casePrune then
      CasePrune.runRecursive declarations summaries main
    else
      { code := main
        removedAlternatives := 0
        collapsedCases := 0
        materializedFetches := 0 }
  have hpruned : runMain ctx pruned.code fuel = .ok sourceOut := by
    cases hcase : passes.casePrune with
    | false => simpa [pruned, hcase] using hrun
    | true =>
        have heq := CasePrune.runMain_runRecursive_eq hpost
          (input := main) (fuel := fuel) hctx
        simpa [pruned, hcase] using heq.trans hrun
  let source : FnDef := ⟨0, .shared, false, pruned.code⟩
  let target : FnDef :=
    { source with body :=
        (rewriteMain passes declarations summaries main).code }
  have hstatic : StaticFunctionBodyRefines ctx source target := by
    change StaticFunctionBodyRefines ctx source target
    exact rewriteMain_staticBodyRefines (passes := passes) hpost
      (main := main) hctx
  have hbody : FunctionBodyRefines ctx source target :=
    FunctionBodyRefines.ofStatic hstatic rfl rfl
  obtain ⟨targetOut, htargetRun, hiso⟩ :=
    hbody emptyHistoryIso rfl RValsIso.nil
      (by simpa [runMain, source] using hpruned)
  exact ⟨targetOut, by
    simpa [runMain, target] using htargetRun, hiso⟩

private theorem emptyHistoryIso_compose_extends :
    emptyHistoryIso.Extends (emptyHistoryIso.trans emptyHistoryIso) := by
  intro left right hrel
  have hbound := emptyHistoryIso.left_bound hrel
  simp at hbound

/-- Logical whole-program refinement before content readdressing.  Main and
all stored declarations are rewritten together; successful results are
preserved modulo allocation history. -/
theorem runMain_rewriteProgram_refines
    {passes : Passes} {declarations : DeclEnv} {summaries : SummaryEnv}
    (hpost : LocalPostFixpoint declarations summaries)
    {ctx : Ctx} {main : Code} {fuel : Nat} {sourceOut : Store × RVal}
    (hctx : ctx.decls = declarations)
    (hrun : runMain ctx main fuel = .ok sourceOut) :
    ∃ targetOut,
      runMain (rewriteCtx passes declarations summaries ctx)
          (rewriteMain passes declarations summaries main).code fuel =
        .ok targetOut ∧
      RunHistoryIso emptyHistoryIso sourceOut targetOut := by
  obtain ⟨middleOut, hmiddleRun, hmainIso⟩ :=
    runMain_rewriteMain_refines (passes := passes) hpost hctx hrun
  obtain ⟨targetOut, htargetRun, hctxIso⟩ :=
    runCode_rewriteCtx_refines (passes := passes) hpost hctx emptyHistoryIso
      RValsIso.nil (by simpa [runMain] using hmiddleRun)
  refine ⟨targetOut, by simpa [runMain] using htargetRun, ?_⟩
  exact RunHistoryIso.weaken emptyHistoryIso_compose_extends
    (hmainIso.trans hctxIso)

structure Outcome where
  result : ReaddressAll.Result
  changes : Changes

/-- Apply checked rooted reachability after all body rewrites but before the
single content-address rebuild.  A disabled pass retains every row. -/
def selectReachable (passes : Passes) (entries : List (Address × Decl))
    (main : Code) : Reachability.Outcome :=
  if passes.reachability then
    Reachability.run passes.roots entries main
  else
    { entries
      certificate := Reachability.produce entries main passes.roots
      accepted := false
      removedDeclarations := 0 }

/-- Checked reachability preserves the complete logical-program result; the
disabled branch is literal equality. -/
theorem runMain_selectReachable_eq (passes : Passes)
    (entries : List (Address × Decl)) (main : Code)
    (oracle : Address → List RVal → Option RVal := fun _ _ => none)
    (fuel : Nat := 100000) :
    runMain
        { decls := Env.ofList (selectReachable passes entries main).entries
          oracle }
        main fuel =
      runMain { decls := Env.ofList entries, oracle } main fuel := by
  cases hreach : passes.reachability with
  | false => simp [selectReachable, hreach]
  | true =>
      simpa [selectReachable, hreach] using
        Reachability.runMain_run_eq passes.roots entries main oracle fuel

/-- Compose enabled checked consumers and rebuild the addressed graph once. -/
def rebuildProgram (passes : Passes) (reserved : List Address)
    (program : List ReaddressAll.Artifact) (summaries : SummaryEnv)
    (main : Code) : Except String Outcome := do
  let declarations := declarationEntries program
  let environment := programDeclEnv program
  let rewritten := rewriteEntries passes environment summaries declarations
  let declarationDelta :=
    declarationsChanges passes environment summaries declarations
  let rewrittenMain := rewriteMain passes environment summaries main
  let reachable := selectReachable passes rewritten rewrittenMain.code
  let result ← ReaddressAll.rebuild reserved reachable.entries
    rewrittenMain.code
  return ⟨result,
    (declarationDelta.add rewrittenMain.changes).add
      { removedDeclarations := reachable.removedDeclarations }⟩

/-- Project the exact graph-rebuild equation from a successful composed pass. -/
theorem rebuild_of_rebuildProgram_eq_ok
    {passes : Passes} {reserved : List Address}
    {program : List ReaddressAll.Artifact} {summaries : SummaryEnv}
    {main : Code} {outcome : Outcome}
    (hrun : rebuildProgram passes reserved program summaries main =
      .ok outcome) :
    ReaddressAll.rebuild reserved
        (selectReachable passes
          (rewriteEntries passes (programDeclEnv program) summaries
            (declarationEntries program))
          (rewriteMain passes (programDeclEnv program) summaries main).code).entries
        (rewriteMain passes (programDeclEnv program) summaries main).code =
      .ok outcome.result := by
  unfold rebuildProgram at hrun
  simp only [bind, Except.bind] at hrun
  cases hrebuild : ReaddressAll.rebuild reserved
      (selectReachable passes
        (rewriteEntries passes (programDeclEnv program) summaries
          (declarationEntries program))
        (rewriteMain passes (programDeclEnv program) summaries main).code).entries
      (rewriteMain passes (programDeclEnv program) summaries main).code with
  | error message =>
      rw [hrebuild] at hrun
      contradiction
  | ok result =>
      rw [hrebuild] at hrun
      have houtcome :
          (⟨result,
            ((declarationsChanges passes (programDeclEnv program) summaries
              (declarationEntries program)).add
              (rewriteMain passes (programDeclEnv program) summaries
                main).changes).add
              { removedDeclarations :=
                  (selectReachable passes
                    (rewriteEntries passes (programDeclEnv program) summaries
                      (declarationEntries program))
                    (rewriteMain passes (programDeclEnv program) summaries
                      main).code).removedDeclarations }⟩ : Outcome) = outcome := by
        injection hrun
      have hresult : result = outcome.result :=
        congrArg Outcome.result houtcome
      exact congrArg Except.ok hresult

/-- The concrete declaration rows used by rebuilding implement the HPT
program environment. -/
theorem envOfList_declarationEntries
    (program : List ReaddressAll.Artifact) :
    Env.ofList (declarationEntries program) = programDeclEnv program :=
  CasePrune.envOfList_declarationEntries program

/-- Old-keyed source context paired with the oracle pullback of an exact
rebuild. -/
def rebuildOriginalCtx (result : ReaddressAll.Result)
    (rewritten : List (Address × Decl)) (declarations : DeclEnv)
    (oracle : Address → List RVal → Option RVal) : Ctx :=
  { decls := declarations
    oracle := (result.rebuildSourceCtx rewritten oracle).oracle }

/-- One successful logical rewrite followed by one exact content-address
rebuild preserves the source result modulo heap allocation history and maps
the rewritten store's embedded declaration addresses into the rebuilt graph. -/
theorem runMain_rebuild_rewriteProgram
    {passes : Passes} {reserved : List Address}
    {entries : List (Address × Decl)}
    {declarations : DeclEnv} {summaries : SummaryEnv} {main : Code}
    {result : ReaddressAll.Result} {sourceOut : Store × RVal}
    (hentries : Env.ofList entries = declarations)
    (hpost : LocalPostFixpoint declarations summaries)
    (hrebuild : ReaddressAll.rebuild reserved
      (selectReachable passes
        (rewriteEntries passes declarations summaries entries)
        (rewriteMain passes declarations summaries main).code).entries
      (rewriteMain passes declarations summaries main).code = .ok result)
    (oracle : Address → List RVal → Option RVal := fun _ _ => none)
    (fuel : Nat := 100000)
    (hrun : runMain
      (rebuildOriginalCtx result
        (selectReachable passes
          (rewriteEntries passes declarations summaries entries)
          (rewriteMain passes declarations summaries main).code).entries
        declarations oracle)
      main fuel = .ok sourceOut) :
    ∃ targetOut,
      runMain (result.addressedCtx oracle) result.main fuel =
          .ok
            (Readdress.Store.mapAddresses
              (result.rebuildRename
                (selectReachable passes
                  (rewriteEntries passes declarations summaries entries)
                  (rewriteMain passes declarations summaries main).code).entries)
              targetOut.1,
            targetOut.2) ∧
        RunHistoryIso emptyHistoryIso sourceOut targetOut := by
  let rewritten := rewriteEntries passes declarations summaries entries
  let rewrittenMain := rewriteMain passes declarations summaries main
  let reachable := selectReachable passes rewritten rewrittenMain.code
  let before := rebuildOriginalCtx result reachable.entries declarations oracle
  have hbefore : before.decls = declarations := rfl
  have hctx : rewriteCtx passes declarations summaries before =
      { decls := Env.ofList rewritten, oracle := before.oracle } := by
    simp [rewriteCtx, before, rewritten, rebuildOriginalCtx,
      envOfList_rewriteEntries, hentries]
    funext address
    rfl
  obtain ⟨targetOut, htargetRun, hiso⟩ :=
    runMain_rewriteProgram_refines (passes := passes) hpost hbefore hrun
  have hfullSource :
      runMain { decls := Env.ofList rewritten, oracle := before.oracle }
          rewrittenMain.code fuel = .ok targetOut := by
    rw [← hctx]
    simpa [rewrittenMain] using htargetRun
  have hfilteredSource :
      runMain
          { decls := Env.ofList reachable.entries, oracle := before.oracle }
          rewrittenMain.code fuel = .ok targetOut := by
    exact (runMain_selectReachable_eq passes rewritten rewrittenMain.code
      before.oracle fuel).trans hfullSource
  have htargetSource :
      runMain (result.rebuildSourceCtx reachable.entries oracle)
          rewrittenMain.code fuel = .ok targetOut := by
    simpa [before, reachable, rebuildOriginalCtx,
      ReaddressAll.Result.rebuildSourceCtx] using hfilteredSource
  refine ⟨targetOut, ?_, hiso⟩
  exact ReaddressAll.runMain_exact_success_of_rebuild_eq_ok hrebuild oracle
    htargetSource

/-- A successful HPT check and successful composed rebuild authorize the
whole-program refinement theorem exposed by the optimizer pipeline. -/
theorem runMain_rebuildProgram_of_runWith_eq_ok
    {passes : Passes} {limits : Limits} {reserved : List Address}
    {program : List ReaddressAll.Artifact} {certificate : Certificate}
    {analysis : HPT.Result} {main : Code} {outcome : Outcome}
    {sourceOut : Store × RVal}
    (hcheck : HPT.runWith limits program certificate = .ok analysis)
    (hrebuild : rebuildProgram passes reserved program certificate.summaryEnv
      main = .ok outcome)
    (oracle : Address → List RVal → Option RVal := fun _ _ => none)
    (fuel : Nat := 100000)
    (hrun : runMain
      (rebuildOriginalCtx outcome.result
        (selectReachable passes
          (rewriteEntries passes (programDeclEnv program)
            certificate.summaryEnv (declarationEntries program))
          (rewriteMain passes (programDeclEnv program)
            certificate.summaryEnv main).code).entries
        (programDeclEnv program) oracle)
      main fuel = .ok sourceOut) :
    ∃ targetOut,
      runMain (outcome.result.addressedCtx oracle) outcome.result.main fuel =
          .ok
            (Readdress.Store.mapAddresses
              (outcome.result.rebuildRename
                (selectReachable passes
                  (rewriteEntries passes (programDeclEnv program)
                    certificate.summaryEnv (declarationEntries program))
                  (rewriteMain passes (programDeclEnv program)
                    certificate.summaryEnv main).code).entries)
              targetOut.1,
            targetOut.2) ∧
        RunHistoryIso emptyHistoryIso sourceOut targetOut := by
  apply runMain_rebuild_rewriteProgram
  · exact envOfList_declarationEntries program
  · exact localPostFixpoint_of_postFixpoint
      (postFixpoint_of_runWith_eq_ok hcheck)
  · exact rebuild_of_rebuildProgram_eq_ok hrebuild
  · exact hrun

/-- Closed-oracle specialization: the source is the ordinary old addressed
program context. -/
theorem runMain_rebuildProgram_of_runWith_eq_ok_defaultOracle
    {passes : Passes} {limits : Limits} {reserved : List Address}
    {program : List ReaddressAll.Artifact} {certificate : Certificate}
    {analysis : HPT.Result} {main : Code} {outcome : Outcome}
    {sourceOut : Store × RVal}
    (hcheck : HPT.runWith limits program certificate = .ok analysis)
    (hrebuild : rebuildProgram passes reserved program certificate.summaryEnv
      main = .ok outcome)
    (fuel : Nat := 100000)
    (hrun : runMain { decls := programDeclEnv program } main fuel =
      .ok sourceOut) :
    ∃ targetOut,
      runMain (outcome.result.addressedCtx (fun _ _ => none))
          outcome.result.main fuel =
        .ok
          (Readdress.Store.mapAddresses
            (outcome.result.rebuildRename
              (selectReachable passes
                (rewriteEntries passes (programDeclEnv program)
                  certificate.summaryEnv (declarationEntries program))
                (rewriteMain passes (programDeclEnv program)
                  certificate.summaryEnv main).code).entries)
            targetOut.1,
          targetOut.2) ∧
      RunHistoryIso emptyHistoryIso sourceOut targetOut := by
  simpa [rebuildOriginalCtx, ReaddressAll.Result.rebuildSourceCtx] using
    (runMain_rebuildProgram_of_runWith_eq_ok hcheck hrebuild
      (fun _ _ => none) fuel hrun)

end Ix.Compiler.IxIR1.HPT.OptimizeProgram
