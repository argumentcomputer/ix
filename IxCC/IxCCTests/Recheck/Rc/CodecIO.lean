import IxCCTests.Recheck.Rc.CodecControls
import IxCCTests.Recheck.Rc.Fixtures
import IxCC.Cfg.Rc.Native
import IxCC.Cfg.Rc.Scoped
import IxCC.Recheck.Produce
import IxCCTests.Rt.Native

set_option autoImplicit false
namespace IxCCTests.Recheck.Rc.CodecIO
open IxCC Lean System
open IxCCTests.Recheck.Rc.Fixtures IxCCTests.Recheck.Rc.CodecControls

def manifestFiles (bundle : FilePath) : Array String :=
  (#[(fixtureRoot / "anonymous.ixe").toString, (fixtureRoot / "consumer.equations.json").toString] ++
    (roots.flatMap fun root => [(bundle / s!"{root}.cert.json").toString,
      (bundle / s!"{root}.own.json").toString]).toArray)

def write (bundle : FilePath) : IO Unit := do
  for root in roots do
    let inp ← source root
    let cfg : Recheck.Config := { names := [root] }
    let (cert, artifact) ← IO.ofExcept ((Recheck.compileInput cfg inp).mapError (·.message))
    IO.FS.writeFile (bundle / s!"{root}.cert.json") (cert.toText ++ "\n")
    IO.FS.writeFile (bundle / s!"{root}.own.json")
      (Own.Plain.Certificate.toText (Own.Plain.Program.canonical artifact.fir).bodies ++ "\n")
    IO.println s!"WROTE {root}: base certificate and explicit ownership overlay"
  let hashes ← IO.Process.output { cmd := "sha256sum", args := manifestFiles bundle }
  unless hashes.exitCode == 0 do throw (IO.userError "certificate bundle hash failed")
  IO.FS.writeFile (bundle / "bundle.sha256") hashes.stdout

def listObs (xs : List Nat) : Sem.Obs :=
  xs.foldr (fun n tail => .ctor 1 [.nat n, tail]) (.ctor 0 [])
def expected (root : String) (n seed : Nat) : Sem.Obs :=
  let ascending := (List.range n).map (seed + ·)
  if root == "sharedReverse" then
    .ctor 0 [listObs ((List.range n).map fun i => seed + (n - 1 - i)), listObs ascending]
  else if root == "reverseRepeated" then listObs (List.replicate n seed)
  else listObs ascending

def read (bundle logs : FilePath) : IO Unit := do
  let checked ← IO.Process.output {
    cmd := "sha256sum", args := #["--status", "--check", (bundle / "bundle.sha256").toString] }
  unless checked.exitCode == 0 do throw (IO.userError "source/certificate bundle changed")
  syntheticControls
  for root in roots do
    let inp ← source root
    let cfg : Recheck.Config := { names := [root] }
    let cert ← IO.ofExcept ((Recheck.Cert.ofText (← IO.FS.readFile
      (bundle / s!"{root}.cert.json"))).mapError (·.message))
    let prior ← IO.ofExcept ((Recheck.runLir cfg inp.program cert).mapError (·.message))
    let ownText ← IO.FS.readFile (bundle / s!"{root}.own.json")
    let own ← IO.ofExcept (Own.Plain.Certificate.ofText prior.fir ownText)
    unless Own.Plain.bodyMapEq own.bodies (Own.Plain.Program.canonical prior.fir).bodies do
      throw (IO.userError "decoded body map differs from exact complete source-bound map")
    negatives prior.fir (← IO.ofExcept (Json.parse ownText))
    let some candidate := Cfg.Rc.generate prior.fir own.bodies |
      throw (IO.userError "decoded candidate declined by Cfg")
    unless Cfg.Rc.checkScopedProgram prior.fir own.bodies candidate do
      throw (IO.userError "fresh decoded candidate fails exact scoped/dense-source gate")
    let lowered ← IO.ofExcept (Cfg.Rc.Native.lower { names := [root] } prior.fir own.bodies candidate)
    let artifact ← IO.ofExcept ((lowered.compile (.ixir1Policy (Ixon.Address.replicate 0x55) 1 4)).mapError toString)
    let some (_, symbol) := lowered.roots.head? | throw (IO.userError "missing native root")
    let some (_, c) := inp.program.roots.head? | throw (IO.userError "missing source root")
    let some (sig, ty) := Recheck.rootTy prior.src candidate.base c |
      throw (IO.userError "missing full result type")
    let exe ← IxCCTests.Rt.Native.link
      { work := logs }
      s!"certificate-{root}" artifact.object symbol
    let cases := [(0, 7), (4, 3), (32, 11)]
    let rows ← IxCCTests.Rt.Native.run exe
      { region := 131072, stack := 1048576, ty := some (sig, ty), dump := true }
      (cases.map fun (n, seed) => [n, seed])
    let mut observations : Array Json := #[]
    for ((n, seed), row) in cases.zip rows do
      let want := expected root n seed
      unless row.status == 0 && row.ok && !row.init && row.obs == some (Rt.renderObs want) &&
          row.readback 131072 sig ty == some want do
        throw (IO.userError s!"{root} {n} {seed}: full native observation mismatch")
      let some dump := row.dump | throw (IO.userError "missing fresh native dump")
      observations := observations.push (Json.mkObj [
        ("n", toJson n), ("seed", toJson seed), ("value", toJson row.value.toNat),
        ("full_observation", toJson (Rt.renderObs want)),
        ("base", toJson dump.base.toNat), ("start", toJson dump.start.toNat),
        ("bump", toJson dump.bump.toNat), ("bytes", toJson (dump.bytes.map UInt8.toNat))])
    IO.FS.writeFile (logs / s!"{root}.observations.json") ((toJson observations).pretty ++ "\n")
    let hashes ← IO.Process.output {
      cmd := "sha256sum", args := #[exe.toString, (logs / s!"certificate-{root}.o").toString] }
    unless hashes.exitCode == 0 do throw (IO.userError "native artifact hash failed")
    IO.FS.writeFile (logs / s!"{root}.artifacts.sha256") hashes.stdout
    IO.println s!"PASS fresh-process {root}: exact complete map, nine refusals, scoped gate, three full native values by two decoders"
  IO.println s!"PASS codec read{← IxCCTests.Rt.Native.agreement}"
  IO.FS.writeFile (logs / "result.txt") "Three fresh source/certificate rechecks,27 actual-source corruptions plus13 synthetic decoder controls refused,9 full native values. This codec gate uses the existing backend producer; the separate complete replay gate validates serialized RC backend decisions.\n"

end IxCCTests.Recheck.Rc.CodecIO
