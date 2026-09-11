import Ix.Compiler.Recursion.Observations

/-! Adversarial proposals use copies of the actual source erasure. They check
the recognizer/checker boundary, first-binding lookup, fresh naming, source
rejection, and a real CFG resource failure that retains the literal artifact.
-/

namespace Ix.Compiler.Recursion.Examples

open Ix.Compiler.Ixon (Address)
open Ix.Compiler.IxIR0.Recursion

private def need (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def replace (entries : List (Address × IxIR0.Decl)) (address : Address)
    (replacement : IxIR0.Decl) : List (Address × IxIR0.Decl) :=
  entries.map fun entry => if entry.1 == address then (entry.1, replacement) else entry

private def rejected (name : String) (entries : List (Address × IxIR0.Decl))
    (main : IxIR0.Expr) (proposal : Option Plan) (reason : IxIR0.Recursion.Skip) : Except String Unit := do
  let selection := selectWith entries main proposal
  match selection with
  | .recovered _ => throw s!"{name}: unsafe recovery accepted"
  | .literal actual => need (actual == reason) s!"{name}: wrong skip reason {repr actual}"
  need (selection.declarations == entries && selection.main == main)
    s!"{name}: literal fallback changed the input"

private def changedStep (s : Schema) (body : IxIR0.Expr) : IxIR0.Decl :=
  .defn .shared (.lam .many (.lam .many (.lam .many
    (packExpr s (ghost (.lam .many body)) (.var 0)))))

def rejectionChecks : Except String (List String) := do
  let fixture ← source [1, 2, 3] false
  let compilation ← (compileValidated fixture.constants fixture.root fixture.config).mapError
    (fun error => s!"rejection fixture: {repr error}")
  let .recovered recovery lowered := compilation.outcome | throw "rejection fixture was not recovered"
  let entries := compilation.source.erasure.result.raw
  let main : IxIR0.Expr := .ref fixture.root
  let plan := recovery.checked.plan
  let s := plan.schema
  let .recursor _ _ rules := literalRecursor s | throw "invalid reference recursor"
  let mutations : List (String × Address × IxIR0.Decl) := [
    ("recursive-arity", s.recursor, .recursor 3 false rules),
    ("nat-peeling", s.recursor, .recursor 2 true rules),
    ("extra-constructor-rule", s.recursor,
      .recursor 2 false (rules.push { fields := 0, rhs := .var 0 })),
    ("non-immediate-recursion", s.recursor,
      .recursor 2 false (rules.set! 1 { fields := 2, rhs := .app (.var 4) (.proj 1 (.var 0)) })),
    ("wrong-constructor-layout", s.cons, .ctor 1 3),
    ("wrong-constructor-tag", s.cons, .ctor 0 2),
    ("wrong-base-function", s.base, .defn .shared
      (packExpr s (ghost (.lam .many (.var 1))) (ghost (.ref s.unit)))),
    ("below-escape", s.step, changedStep s (.var 2)),
    ("below-data-projection", s.step,
      changedStep s (.app (.proj 1 (.var 2)) (consExpr s (.var 4) (.var 0)))),
    ("course-of-values-projection", s.step,
      changedStep s (.app (.proj 0 (.proj 1 (.var 2))) (consExpr s (.var 4) (.var 0)))),
    ("changed-accumulator", s.step,
      changedStep s (.app (.proj 0 (.var 2)) (consExpr s (.var 4) (.var 3)))),
    ("returned-below-tuple", fixture.root, .defn .shared (.ref s.base)),
    ("extra-entry-use", fixture.root, .defn .shared (.letE .many (.ref s.base) plan.literalMain)),
    ("unique-entry-result", fixture.root, .defn .unique plan.literalMain)]
  for (name, address, declaration) in mutations do
    rejected name (replace entries address declaration) main (some plan) .rejectedProposal
  rejected "changed-proposal-input" entries main (some { plan with values := [3, 2, 1] }) .rejectedProposal
  rejected "unrecognized-entry" entries (.app main .erased) none .unrecognized
  need ((propose entries (.app main .erased)).isNone) "unrecognized entry was proposed"
  rejected "first-binding-shadow" ((s.cons, .ctor 1 7) :: entries) main (some plan) .rejectedProposal
  rejected "fresh-address-conflict" (entries ++ [(recovery.address, .defn .shared .erased)])
    main (some plan) .addressConflict
  let common := lowered.compilation
  let certificateRejections : List (String × List (Address × IxIR0.Decl) × List (Address × IxIR1.Decl)) :=
    [("lowering-shadowed-source", (s.cons, .ctor 1 7) :: common.declarations, common.targetDecls),
     ("lowering-source-extern", replace common.declarations s.cons (.extern 2), common.targetDecls),
     ("lowering-target-extern", common.declarations, (s.cons, .extern 2) :: common.targetDecls)]
  for (name, source, target) in certificateRejections do
    match Pipeline.checkLoweringCertificate source target with
    | .error _ => pure ()
    | .ok _ => throw s!"{name}: invalid common lowering certificate accepted"
  let fallback ← (compileValidated fixture.constants fixture.root fixture.config
    1000 1000 1000 1000 0).mapError (fun error => s!"source rejected at optional CFG limit: {repr error}")
  match fallback.outcome with
  | .literal (.cfgLowering (.resources _)) => pure ()
  | _ => throw "zero CFG depth did not retain the literal backend with its exact resource error"
  need (fallback.outcome.selected.declarations == entries && fallback.outcome.selected.main == main &&
    Coverage.ir1Entries fallback.source.artifact.targetDecls ==
      Coverage.ir1Entries compilation.source.artifact.targetDecls &&
    fallback.source.artifact.main.bytes == compilation.source.artifact.main.bytes)
    "CFG failure changed the checked literal artifact"
  let scalar ← Coverage.scalar "fallback" 42 true
  let scalarResult ← (compileValidated scalar.constants scalar.root scalar.config 100 100 100 100).mapError
    (fun error => s!"scalar fallback failed: {repr error}")
  match scalarResult.outcome with
  | .literal (.recovery .unrecognized) => pure ()
  | _ => throw "ordinary scalar source did not retain its literal compilation"
  let (scalarStore, scalarValue) ←
    (IxIR1.runOwnedMain { decls := scalarResult.source.artifact.targetDeclEnv }
      .shared scalarResult.source.artifact.main 1000).mapError (fun error => s!"scalar fallback run: {repr error}")
  need (scalarValue == .lit (.nat 42) && scalarStore.live == 0) "scalar fallback result changed"
  let bare ← Coverage.bareLiteral
  match compileValidated bare.constants bare.root bare.config 100 100 100 100 with
  | .error (.usage _ .freezeNeeded) => pure ()
  | _ => throw "source freeze rejection was weakened by optional recovery"
  let external ← Coverage.externSource
  match compileValidated external.constants external.root external.config 100 100 100 100 with
  | .error (.validate _ "validated extern ownership ABI rejects this declaration") => pure ()
  | _ => throw "source extern rejection was weakened by optional recovery"
  return mutations.map (·.1) ++ ["changed-proposal-input", "unrecognized-entry", "first-binding-shadow",
    "fresh-address-conflict", "cfg-resource-fallback", "scalar-literal-fallback", "source-freeze-rejection",
    "source-extern-rejection"] ++ certificateRejections.map (·.1)

def runAll : Except String (List CaseResult × List String) := do
  let rejected ← rejectionChecks
  let results ← cases.mapM fun (name, values, aliased) =>
    (runCase name values aliased).mapError (fun error => s!"{name}: {error}")
  return (results, rejected)

def report (results : List CaseResult) (rejections : List String) : Lean.Json :=
  Lean.Json.mkObj [
    ("format", Lean.toJson "compilatrix/source-recursion-report/1"),
    ("source_origin", Lean.toJson "canonical synthetic Ixon"),
    ("recovery_policy", Lean.toJson "immediate-list-below/1"),
    ("cases", Lean.toJson (results.map (·.summary))),
    ("rejection_checks", Lean.toJson rejections)]

end Ix.Compiler.Recursion.Examples
