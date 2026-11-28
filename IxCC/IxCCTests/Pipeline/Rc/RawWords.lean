import IxCCTests.Pipeline.Rc.Support
import IxCCTests.Exe.Support

/-! # Raw 64-bit words under plain RC (VS0)

`phase1-boundary`'s `vs0` (`Vs0.vs0`): a `UInt64` loop whose value has its top bit set on most
iterations. Under `--rc on` (`RcReplay.produce`) the loop holds the `UInt64` in a raw 64-bit
register: the layout the replay infers (`Cfg.Rc.Raw.withLayout`) names raw registers, and the
replay accepts it. Natively each case gives the value the manifest records (Lean's interpreter;
`vs0 1` is `0x9E3779B97F4A7C15 >>> 1`), where a tagged word fails `natOverflow` (the immortal
route's cases are `allow`ed that failure in the manifest). -/

set_option autoImplicit false
namespace IxCCTests.Pipeline.Rc.RawWords
open IxCC

def dir : String := "fixtures/corpus/phase1-boundary"
def root : String := "Vs0.vs0"

/-- The manifest's cases. -/
def cases : List (List Nat × Nat) :=
  [([0], 0), ([1], 5700357409661599242), ([5], 4534217853761136988),
   ([100], 6003660798864633857), ([1000], 3519181292577463013)]

def check (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError s!"FAIL: {label}")

/-- VS0 compiles to plain RC with raw registers; with `work`, each case also runs natively as the
standalone executable IxCC writes. -/
def run (work : Option System.FilePath) : IO Unit := do
  let bytes ← IO.FS.readBinFile s!"{dir}/vs0.ixe"
  let eqs ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile s!"{dir}/vs0.equations.json"))
  let inp ← IO.ofExcept ((Recheck.ingress bytes eqs [root]).mapError (·.message))
  let cfg : Recheck.Config := { names := [root] }
  match Recheck.RcReplay.produce cfg inp with
  | .error e => throw (IO.userError s!"FAIL: vs0: {e.render}")
  | .ok (cert, artifact) =>
    let raws := artifact.front.cfg.raw.vars.toList.foldl (fun n entry => n + entry.2.length) 0
    check "vs0: the replayed layout names no raw register" (raws > 0)
    IO.println s!"PASS vs0: --rc on compiles {root} to plain RC with {raws} raw registers, replay accepted"
    if let some d := work then
      IO.FS.createDirAll d
      let art ← IO.ofExcept ((Recheck.RcReplay.Artifact.toRecheckArtifact cert artifact).mapError (·.render))
      let exe := d / "raw-vs0"
      match ← IxCCTests.Exe.build exe art {} with
      | .error e => throw (IO.userError s!"FAIL: vs0: executable: {e.render}")
      | .ok () =>
        for (args, want) in cases do
          let r ← IxCCTests.Exe.run exe (args.map toString)
          let label := s!"vs0 {args}"
          check s!"{label}: {r.outcome} {r.obs}, expected {want}"
            (r.outcome == "ok" && r.obs == toString want)
          IO.println s!"PASS {label}: {r.outcome} {r.obs}"

end IxCCTests.Pipeline.Rc.RawWords
