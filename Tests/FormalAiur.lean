import Ix.Cli.FormalAiur
import Tests.Ix.LegacyIxVM

/-! Real claim fixtures shared with legacy tests, plus independently specified
evaluation inputs. Run through the new Rust host, without invoking old execution. -/
open Lean LegacyIxVM.ClaimHarness

private def caseJson (label : String) (w : ClaimWitness) (accept : Bool := true) : Json :=
  Json.mkObj [("label", toJson label), ("accept", toJson accept),
    ("invocation", Ix.Cli.FormalAiur.invocation w.input w.inputIOBuffer)]

private def evalCases : Except String (Array Json) := do
  let ty : Ixon.Expr := .leanAll (.sort 0) (.leanAll (.var 0) (.var 1))
  let value : Ixon.Expr := .leanLam (.sort 0) (.leanLam (.var 0) (.var 0))
  let beta : Ixon.Expr := .app (.leanLam ty (.var 0)) value
  let constant v : Ixon.Constant := ⟨.defn ⟨.defn, .safe, 0, ty, v⟩, #[], #[], #[.zero]⟩
  let input := constant beta
  let output := constant value
  let ia := Address.blake3 (Ixon.ser input)
  let oa := Address.blake3 (Ixon.ser output)
  let env := ({} : Ixon.Env).storeConst ia input |>.storeConst oa output
  let env := { env with anonHints := env.anonHints.insert ia (.regular 0) |>.insert oa (.regular 0) }
  let good ← buildClaimWitness env (.eval ia oa none)
  let unreduced ← buildClaimWitness env (.eval ia ia none)
  return #[caseJson "Eval beta normal form" good,
    caseJson "Eval rejects an unreduced claimed result" unreduced false]

/-- Small, dependency-bearing environment for the orchestration gate. This
exercises real IxVM checking and cross-record calls without importing Init. -/
private def controllerEnv : Ixon.Env := Id.run do
  let ty : Ixon.Expr := .leanAll (.sort 0) (.leanAll (.var 0) (.var 1))
  let value : Ixon.Expr := .leanLam (.sort 0) (.leanLam (.var 0) (.var 0))
  let mut env : Ixon.Env := {}
  let mut prior : Option Address := none
  for i in [:3] do
    let body := if i == 0 then value else if i == 1 then .ref 0 #[]
      else .app (.leanLam ty (.var 0)) (.ref 0 #[])
    let c : Ixon.Constant := ⟨.defn ⟨.defn, .safe, 0, ty, body⟩,
      #[], prior.toArray, #[.zero]⟩
    let addr := Address.blake3 (Ixon.ser c)
    env := env.storeConst addr c
    env := { env with anonHints := env.anonHints.insert addr (.regular 0) }
    prior := some addr
  return env

def main (args : List String) : IO Unit := do
  let path := args.headD "/tmp/ix-formal-claims.json"
  let env ← get_env!
  let fixture ← loadIxonEnv ``Nat.add_comm env
  IO.FS.writeBinFile (path ++ ".ixe") (← IO.ofExcept (Ixon.serEnv fixture))
  IO.FS.writeBinFile (path ++ ".controller.ixe") (← IO.ofExcept (Ixon.serEnv controllerEnv))
  let mut cases := ← IO.ofExcept evalCases
  for build in [claimCheckWithAsm,
      claimCheckEnvFull, claimCheckEnvFrontier,
      claimRevealDefnFields, claimRevealDefnExpr,
      claimRevealCPrj] do
    let test ← build fixture
    cases := cases.push (caseJson test.label
      { funcName := test.functionName, input := test.input, inputIOBuffer := test.inputIOBuffer })
  for test in [← claimContains, ← claimRevealBinderModes] do
    cases := cases.push (caseJson test.label
      { funcName := test.functionName, input := test.input, inputIOBuffer := test.inputIOBuffer })
  IO.FS.writeFile path (toJson cases).compress
  IO.println s!"Wrote {cases.size} production claim cases and .ixe fixture to {path}"
