/-
  `#ixeval`: evaluate a term through the ix pipeline and surface the
  content-addressed evaluation claim.

  `#ixeval t` elaborates `t`, normalizes it (`Meta.reduce`, the same
  normalization the ZkVoting prover flow uses to fix claim outputs),
  compiles the term's reference closure with the Rust compiler, and
  builds an `Ix.Claim.eval` from the input and output content
  addresses (`Ix.Commit.evalClaim`). The reduced value, the claim, and
  its digest (blake3 of the serialized claim — the public input
  `verify_claim` consumes) are reported.

  This is the evaluation surface for `import_ixe`-materialized
  constants, which carry no compiled code and so are invisible to
  `#eval`: `#ixeval` reduces them kernel-style and anchors the result
  in ix's content addressing. The compile is scoped to the term's
  transitive reference closure, not the whole environment, so cost
  tracks the term.

  Proving the claim is out-of-band (`ix prove --claim <digest>`); the
  IxVM `run_eval` arm is still landing, so today the claim is the
  commitment artifact, not yet a proven one.

  Note on qualification: bare `Name`/`Expr` inside the `Ix` namespace
  resolve to ix's own mirror types, so Lean's are `Lean.`-qualified
  explicitly throughout (repo convention).
-/
module

public import Lean
public meta import Ix.Catalog
public meta import Ix.CompileM
public meta import Ix.Commit

public section

namespace Ix.IxEval

/-- `#ixeval t`: reduce `t`, compile its reference closure, and report
    the value plus the content-addressed evaluation claim. -/
syntax (name := ixEval) "#ixeval " term : command

open Lean Elab Command in
@[command_elab ixEval]
meta def elabIxEval : CommandElab := fun stx => do
  match stx with
  | `(command| #ixeval $t:term) =>
    let (outFmt, claimLine, digestLine) ← liftTermElabM do
      let input ← Term.elabTerm t none
      Term.synthesizeSyntheticMVarsNoPostponing
      let input ← Lean.instantiateMVars input
      if input.hasMVar then
        throwError "#ixeval: term has unresolved metavariables"
      if input.hasFVar then
        throwError "#ixeval: term has free variables"
      let output ← Lean.Meta.reduce input
      let type ← Lean.Meta.inferType input
      let lvls := (Lean.collectLevelParams default input).params.toList
      -- Closure-scoped compile: every constant reachable from the
      -- input, output, or type.
      let env ← getEnv
      let roots := Ix.Catalog.expressionReferences input
        ++ Ix.Catalog.expressionReferences output
        ++ Ix.Catalog.expressionReferences type
      let mut seen : Lean.NameSet := {}
      let mut work : Array Lean.Name := roots.toArray
      let mut closure : List (Lean.Name × Lean.ConstantInfo) := []
      while !work.isEmpty do
        let n := work.back!
        work := work.pop
        if seen.contains n then continue
        seen := seen.insert n
        let some ci := env.find? n
          | throwError "#ixeval: unknown constant {n}"
        closure := (n, ci) :: closure
        for r in Ix.Catalog.constantInfoReferences ci do
          unless seen.contains r do
            work := work.push r
      let phases ← Ix.CompileM.rsCompilePhasesOf closure
      let compileEnv := Ix.Commit.mkCompileEnv phases
      let claim ← match Ix.Commit.evalClaim compileEnv lvls input output
          type with
        | .ok claim => pure claim
        | .error e => throwError "#ixeval: claim build failed: {e}"
      let digest := Address.blake3 (Ix.Claim.ser claim)
      return (← Lean.Meta.ppExpr output, s!"{claim}", s!"{digest}")
    logInfo m!"{outFmt}\n{claimLine}\ndigest {digestLine}"
  | _ => throwUnsupportedSyntax

end Ix.IxEval

end
