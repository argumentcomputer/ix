import IxCCTests.Pipeline.Rc.Support
import IxCCTests.Exe.Support

/-! # Constructors of more than 31 scanned fields under plain RC

The counted heap allocates constructors of up to 254 scanned fields (heap stage 1: the general cell
layouts, `Rt.Rc.Gen`). Two registered roots with wider constructors, `Limits.fields254` (254
fields, the most a header counts, `phase1-boundary`) and bigctor's `entry` (70 fields,
`phase1-scalar`), compile under `--rc auto` to plain RC (before the switch, the bounded route
declined them and `--rc auto` fell back to the immortal policy); natively, each case gives the value
its manifest records (Lean's, the `lean-run` oracle), and the one value at or above 2⁶³ fails
`natOverflow` (status 3), as every policy does. -/

set_option autoImplicit false
namespace IxCCTests.Pipeline.Rc.Wide
open IxCC

structure Fixture where
  dir : String
  name : String
  root : String
  /-- Arguments, and the expected value (`none`: `natOverflow`). -/
  cases : List (List Nat × Option Nat)

/-- The cases of the corpus manifests (`fixtures/corpus/*/corpus.json`). -/
def fixtures : List Fixture :=
  [{ dir := "fixtures/corpus/phase1-boundary", name := "fields254", root := "Limits.fields254"
     cases := [([5, 3], some 258), ([0, 0], some 253), ([1000, 10], some 1253),
       ([9223372036854775554, 1], some 9223372036854775807), ([9223372036854775807, 1], none)] },
   { dir := "fixtures/corpus/phase1-scalar", name := "bigctor", root := "entry"
     cases := [([10], some 10), ([9223372036854775807], some 9223372036854775807)] }]

def check (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError s!"FAIL: {label}")

/-- Each fixture compiles to plain RC under `--rc auto`; with `work`, each case also runs natively as
the standalone executable IxCC writes. -/
def run (work : Option System.FilePath) : IO Unit := do
  for f in fixtures do
    let bytes ← IO.FS.readBinFile s!"{f.dir}/{f.name}.ixe"
    let eqs ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile s!"{f.dir}/{f.name}.equations.json"))
    let inp ← IO.ofExcept ((Recheck.ingress bytes eqs [f.root]).mapError (·.message))
    let cfg : Recheck.Config := { names := [f.root] }
    match Recheck.RcReplay.produceAuto cfg inp with
    | .error e => throw (IO.userError s!"FAIL: {f.name}: {e.render}")
    | .ok (.zeroRc ..) => throw (IO.userError s!"FAIL: {f.name}: zero RC, expected plain RC")
    | .ok (.immortal _ _ _ reason) =>
      throw (IO.userError s!"FAIL: {f.name}: immortal fallback, expected plain RC ({reason.render})")
    | .ok (.plainRc cert artifact _) =>
      IO.println s!"PASS {f.name}: --rc auto compiles {f.root} to plain RC, replay accepted"
      if let some dir := work then
        IO.FS.createDirAll dir
        let art ← IO.ofExcept ((Recheck.RcReplay.Artifact.toRecheckArtifact cert artifact).mapError (·.render))
        let exe := dir / s!"wide-{f.name}"
        match ← IxCCTests.Exe.build exe art {} with
        | .error e => throw (IO.userError s!"FAIL: {f.name}: executable: {e.render}")
        | .ok () =>
          for (args, want) in f.cases do
            let r ← IxCCTests.Exe.run exe (args.map toString)
            let label := s!"{f.name} {args}"
            match want with
            | some v => check s!"{label}: {r.outcome} {r.obs}, expected {v}" (r.outcome == "ok" && r.obs == toString v)
            | none => check s!"{label}: {r.outcome}, expected natOverflow" (r.outcome == "status 3")
            IO.println s!"PASS {label}: {r.outcome} {r.obs}"

end IxCCTests.Pipeline.Rc.Wide
