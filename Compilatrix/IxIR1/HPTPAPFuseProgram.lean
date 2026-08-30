import Compilatrix.IxIR1.HPTCasePruneProgram
import Compilatrix.IxIR1.HPTPAPFuse

/-!
# One-rebuild composition of checked HPT consumers

Case simplification and local PAP fusion both consume the same old-keyed HPT
certificate.  Readdressing between them would invalidate those keys.  This
module therefore composes their logical declaration/main rewrites first and
performs one complete content-address rebuild.

Case simplification runs first.  Its unary collapse retains binder depth by
materializing a fetch, so PAP fusion can analyze the resulting code with the
same owner, arity, and entry fact environment.
-/

namespace Compilatrix.IxIR1.HPT.OptimizeProgram

open Compilatrix.Ixon (Address)

structure Passes where
  casePrune : Bool := true
  papFuse : Bool := false
  deriving BEq, Repr

structure Changes where
  casePrune : CasePrune.Changes := {}
  papFuse : PAPFuse.Changes := {}

def Changes.add (left right : Changes) : Changes :=
  { casePrune := left.casePrune.add right.casePrune
    papFuse := left.papFuse.add right.papFuse }

structure CodeOutcome where
  code : Code
  changes : Changes := {}

private def rewriteCode (passes : Passes) (declarations : DeclEnv)
    (summaries : SummaryEnv) (owner : Address) (current : FnDef)
    (facts : List Fact) (input : Code) : CodeOutcome :=
  let pruned : CasePrune.Outcome :=
    if passes.casePrune then
      CasePrune.runWithFacts declarations summaries owner current facts input
    else
      { code := input, removedAlternatives := 0, collapsedCases := 0,
        materializedFetches := 0 }
  let prunedCurrent := { current with body := pruned.code }
  let fused : PAPFuse.Outcome :=
    if passes.papFuse then
      PAPFuse.runWithFacts declarations summaries owner prunedCurrent facts
        pruned.code
    else
      { code := pruned.code, changes := {} }
  { code := fused.code
    changes :=
      { casePrune := pruned.changes
        papFuse := fused.changes } }

private def rewriteDeclaration (passes : Passes)
    (declarations : DeclEnv) (summaries : SummaryEnv)
    (owner : Address) : Decl → Decl × Changes
  | .extern arity => (.extern arity, {})
  | .fn function =>
      let rewritten := rewriteCode passes declarations summaries owner function
        (List.replicate function.arity Fact.top) function.body
      (.fn { function with body := rewritten.code }, rewritten.changes)

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

/-- Main code has no stored declaration owner.  Case pruning retains its
fixed-environment compatibility traversal.  PAP fusion uses the all-zero
address only as the fail-soft `callSelf` analysis owner; ordinary direct
calls, PAPs, and applies are unaffected by that placeholder. -/
private def rewriteMain (passes : Passes) (declarations : DeclEnv)
    (summaries : SummaryEnv) (main : Code) : CodeOutcome :=
  let pruned : CasePrune.Outcome :=
    if passes.casePrune then
      CasePrune.runRecursive declarations summaries main
    else
      { code := main
        removedAlternatives := 0
        collapsedCases := 0
        materializedFetches := 0 }
  let current : FnDef := ⟨0, .shared, pruned.code⟩
  let fused : PAPFuse.Outcome :=
    if passes.papFuse then
      PAPFuse.runWithFacts declarations summaries default current [] pruned.code
    else
      { code := pruned.code, changes := {} }
  { code := fused.code
    changes :=
      { casePrune := pruned.changes
        papFuse := fused.changes } }

structure Outcome where
  result : ReaddressAll.Result
  changes : Changes

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
  let result ← ReaddressAll.rebuild reserved rewritten rewrittenMain.code
  return ⟨result, declarationDelta.add rewrittenMain.changes⟩

end Compilatrix.IxIR1.HPT.OptimizeProgram
