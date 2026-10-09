/-
  Qualified phase-9 inverse correspondence controls. Run with
  `lake test -- --ignored clique-values-inverse` after building IxTests.

  The ordinary SM.P0 compile is the production-path neighbour: every
  selected member and every reached recursor must be checked. Separate
  controls exercise the exact inverse constructor on a Bool recursor:
  exchanging the two same-typed, closed minors is kernel-well-typed but
  must fail phase 9's value comparison. This does not claim that Bool is
  a permuted compiler block or that the correspondence is an inverse proof.
  No validator records or compiler fixture expectations are rerecorded.
-/
import Ix.Cli.ValidateLeanCmd
import Tests.Ix.Compile.Pass3

open Lean Meta

namespace Tests.Ix.Compile.InverseRecursor

open IxCliqueValues.InverseRecursor

def require (label : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"[clique-values-inverse] FAIL {label}")
  IO.println s!"[clique-values-inverse] PASS {label}"

def metaIO (env : Environment) (body : MetaM α) : IO α := do
  let ctx : Core.Context := { fileName := "<inverse correspondence controls>", fileMap := default, maxHeartbeats := 0 }
  let (a, _) ← (body.run' {} : CoreM α).toIO ctx { env }
  return a

def rejected (body : MetaM α) : MetaM Bool := do
  try
    discard body
    return false
  catch _ => return true

/-! A lower-level control with a deliberately non-involutive permutation
also checks which direction the array means. -/

def arrayControls : IO Unit := do
  require "inverse-direction" ((inverse #[2, 0, 1]).toOption == some #[1, 2, 0])
  require "duplicate-rejected" (!(inverse #[0, 0, 2]).isOk)
  require "out-of-range-rejected" (!(inverse #[0, 1, 3]).isOk)

/-- Two kernel-checked scratch definitions on Bool. Both use the production
inverse application constructor; only the inverse permutation is changed.
The source selects 11 for false and 29 for true. -/
def closedValueControl (wrong : Bool) : MetaM IxCliqueValues.Verdict := do
  let name := `Tests.Ix.Compile.InverseRecursor.Control.select
  let motive := mkLambda `b .default (mkConst ``Bool) (mkConst ``Nat)
  let p : Permutation := { args := #[0, 2, 1, 3], levels := #[0] }
  let chosen := if wrong then { p with args := #[0, 1, 2, 3] } else p
  let ty ← mkArrow (mkConst ``Bool) (mkConst ``Nat)
  let sourceBody ← withLocalDeclD `b (mkConst ``Bool) fun b =>
    mkLambdaFVars #[b] (mkAppN (mkConst ``Bool.rec [.succ .zero])
      #[motive, mkNatLit 11, mkNatLit 29, b])
  let compiledBody ← withLocalDeclD `b (mkConst ``Bool) fun b => do
    let value ← ofExcept (applyInverse ``Bool.rec chosen #[.succ .zero]
      #[motive, mkNatLit 29, mkNatLit 11, b])
    check value
    mkLambdaFVars #[b] value
  for (n, value) in #[(name, sourceBody), (IxCliqueValues.scratchName name, compiledBody)] do
    let d : DefinitionVal := { name := n, levelParams := [], type := ty, value,
      hints := .abbrev, safety := .safe, all := [n] }
    if let some e ← IxCliqueValues.kernelAdd (.defnDecl d) then
      throwError "closed permutation control is not kernel-well-typed: {e}"
  IxCliqueValues.checkMember #[name] "structural" #[0] name

def valueControls (env : Environment) : IO Unit := do
  let good ← metaIO env (closedValueControl false)
  require "closed-neighbour-two-values" (match good with | .checked 2 0 0 => true | _ => false)
  let bad ← metaIO env (closedValueControl true)
  require "wrong-permutation-value-rejected" (match bad with
    | .failed errors => errors.size == 2 && errors.all (fun e => e.startsWith "WRONG MEANING:")
    | _ => false)

/-- The full image reader and dependent inverse definition, with Bool's two
minor positions reversed in the canonical telescope. The neighbour is
kernel-checked; repeated image arguments and a well-formed but wrong inverse
minor permutation are rejected by the same production helpers. -/
def dependentControls (env : Environment) : IO Unit := do
  let results ← metaIO env do
    let some (.recInfo source) := (← getEnv).find? ``Bool.rec
      | throwError "Bool.rec is absent"
    let canonName := `Tests.Ix.Compile.InverseRecursor.Control._ix.rec
    let p : Permutation := { args := #[0, 2, 1, 3], levels := #[0] }
    let us := source.levelParams.map Level.param
    let (ty, imageValue) ← forallTelescope source.type fun xs result => do
      unless xs.size == p.args.size do throwError "Bool.rec telescope changed"
      let ty ← mkForallFVars (p.args.map (xs[·]!)) result
      let v ← mkLambdaFVars xs (mkAppN (mkConst canonName us) (p.args.map (xs[·]!)))
      return (ty, v)
    let canonical : RecursorVal := { source with name := canonName, type := ty }
    let image : DefinitionVal := { source.toConstantVal with value := imageValue,
      hints := .abbrev, safety := .safe, all := [source.name] }
    let read ← readPermutation source canonical image
    let exact := read.args == p.args && read.levels == p.levels
    let goodDecl ← definition source canonical read
    let accepted := (← IxCliqueValues.kernelAdd (.defnDecl goodDecl)).isNone
    let duplicateValue ← lambdaTelescope image.value fun xs body => do
      let args := body.getAppArgs
      mkLambdaFVars xs (mkAppN body.getAppFn (args.set! 2 args[1]!))
    let duplicate ← rejected (readPermutation source canonical { image with value := duplicateValue })
    let wrong ← rejected (definition source canonical { read with args := #[0, 1, 2, 3] })
    let foreignLevels ← rejected (definition source canonical { read with levels := #[1] })
    return (exact, accepted, duplicate, wrong, foreignLevels)
  require "image-derived-neighbour" results.1
  require "inverse-definition-kernel-neighbour" results.2.1
  require "image-duplicate-rejected" results.2.2.1
  require "dependent-wrong-permutation-rejected" results.2.2.2.1
  require "universe-permutation-rejected" results.2.2.2.2

/-- One existing ordinary fixture, through the default compiler and phase 9.
No skipped recursor or not-checkable member can satisfy this neighbour. -/
def compiledControls (env : Environment) : IO Unit := do
  let members := #[`Tests.Ix.Compile.Twins.Cliques.SM.P0.szTr,
    `Tests.Ix.Compile.Twins.Cliques.SM.P0.szFo]
  let u : Pass3.CUnit := { name := "phase9-inverse-SM.P0", env, seeds := members,
    closure := Pass3.closureOf env members.toList }
  let out ← Pass3.compileUnit u
  require "fixture-no-refusal" out.cenv.ungrounded.isEmpty
  let cliques := Ix.Cli.ValidateLeanCmd.transportedCliques out.cenv
  let selected := cliques.filter (fun cl => cl.any members.contains)
  require "fixture-whole-clique" (selected.size == 1 && selected[0]!.size == members.size &&
    members.all selected[0]!.contains)
  let cs ← IO.ofExcept (IxCliqueValues.compiledClosure out.env selected[0]!)
  let recs := cs.filterMap fun c => match c with | .recInfo rv => some rv | _ => none
  require "fixture-reaches-recursor" (!recs.isEmpty)
  let (built, allSourceMembers) ← metaIO env do
    let mut built := 0
    let mut allSourceMembers : List Name := []
    for rv in recs do
      let bridge ← build out.env (IxCliqueValues.decompileCompiled out.env) rv
      let some (.recInfo source) := (← getEnv).find? bridge.source
        | throwError "bridge source is not a recursor"
      allSourceMembers := source.all
      unless (← IxCliqueValues.kernelAdd (.defnDecl bridge.decl)).isNone do
        throwError "actual inverse definition rejected"
      built := built + 1
    return (built, allSourceMembers)
  require "fixture-all-recursor-neighbours" (built == recs.size)
  require "fixture-permuted-neighbour" (requirePermuted out.env allSourceMembers).isOk
  -- Forge only the second member's projection association. This is neither
  -- a different compile nor permission to omit either original member.
  let some a := allSourceMembers[0]? | throw (IO.userError "fixture has no first source member")
  let some b := allSourceMembers[1]? | throw (IO.userError "fixture has no second source member")
  let some nd := out.env.named.get? (Pass3.ixN a) | throw (IO.userError "fixture first member missing")
  let forged := { out.env with named := out.env.named.insert (Pass3.ixN b) nd }
  require "collapsed-association-rejected" (match requirePermuted forged allSourceMembers with
    | .error e => e == "inverse correspondence: collapsed block is unsupported"
    | _ => false)
  let report ← IxCliqueValues.run env out.env selected
  let (failed, detail, lines) := IxCliqueValues.summarize report
  for line in lines do IO.println s!"[clique-values-inverse] {line}"
  IO.println s!"[clique-values-inverse] {detail}"
  require "fixture-every-member-checked-relative" (!failed && report.cliques.size == 1 &&
    report.cliques.all fun row => row.failure.isNone && row.reason.isNone &&
      row.inverseBridges.size == recs.size && row.members.size == members.size &&
      row.members.all fun (_, v) => match v with | .checked n 0 _ => n > 0 | _ => false)
  require "qualified-report" ((detail.splitOn "relative to image-derived inverse correspondence").length == 2)

def run : IO UInt32 := do
  try
    let env ← get_env!
    arrayControls
    valueControls env
    dependentControls env
    compiledControls env
    IO.println "[clique-values-inverse] 18 controls passed; inverse-correspondence-relative, no inverse proof"
    return 0
  catch e =>
    IO.eprintln s!"[clique-values-inverse] FAIL {e}"
    return 1

end Tests.Ix.Compile.InverseRecursor
