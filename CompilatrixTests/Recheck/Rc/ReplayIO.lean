import Compilatrix.Recheck.Rc.Produce
import CompilatrixTests.Recheck.Rc.Fixtures
import CompilatrixTests.Rt.Native
import CompilatrixTests.Rt.Rc.ReuseSupport

set_option autoImplicit false
namespace CompilatrixTests.Recheck.Rc.ReplayIO
open Compilatrix Lean System
open CompilatrixTests.Recheck.Rc.Fixtures

def config (root : String) : Recheck.Config := { names := [root] }

def files (bundle : FilePath) : Array String :=
  #[(fixtureRoot / "anonymous.ixe").toString, (fixtureRoot / "consumer.equations.json").toString] ++
    (roots.flatMap fun root => [(bundle / s!"{root}.rc.json").toString,
      (bundle / s!"{root}.producer.o").toString]).toArray

def write (bundle : FilePath) : IO Unit := do
  for root in roots do
    let input ← source root
    let (cert, artifact) ← IO.ofExcept ((Recheck.RcReplay.produce (config root) input).mapError (·.message))
    IO.FS.writeFile (bundle / s!"{root}.rc.json") (cert.toText ++ "\n")
    IO.FS.writeBinFile (bundle / s!"{root}.producer.o") artifact.backend.object
    IO.println s!"WROTE {root}: ownership plus{cert.base.alloc.length} allocation/{cert.base.frames.length} frame decisions; complete checked ELF"
  let hashes ← IO.Process.output { cmd := "sha256sum", args := files bundle }
  unless hashes.exitCode == 0 do throw (IO.userError "RC bundle hash failed")
  IO.FS.writeFile (bundle / "bundle.sha256") hashes.stdout

def refused (cfg : Recheck.Config) (P : Src.Program) (c : Recheck.RcReplay.Cert)
    (label : String) (stage : Recheck.Stage) : IO Unit := do
  match Recheck.RcReplay.run cfg P c with
  | .ok _ => throw (IO.userError s!"corrupt RC certificate accepted: {label}")
  | .error err =>
    unless err.stage == stage do
      throw (IO.userError s!"{label}: expected {stage.name}, got {err.stage.name}: {err.message}")
    IO.println s!"PASS {label}: {err.stage.name}/{err.code}"

def listObs (xs : List Nat) : Sem.Obs :=
  xs.foldr (fun n tail => .ctor 1 [.nat n, tail]) (.ctor 0 [])
def expected (root : String) (n seed : Nat) : Sem.Obs :=
  let ascending := (List.range n).map (seed + ·)
  if root == "sharedReverse" then
    .ctor 0 [listObs ((List.range n).map fun i => seed + (n - 1 - i)), listObs ascending]
  else if root == "reverseRepeated" then listObs (List.replicate n seed)
  else listObs ascending

def read (bundle logs : FilePath) : IO Unit := do
  let guard ← IO.Process.output {
    cmd := "sha256sum", args := #["--status", "--check", (bundle / "bundle.sha256").toString] }
  unless guard.exitCode == 0 do throw (IO.userError "RC source/certificate/object bundle changed")
  let mut reuseReports : Array Json := #[]
  for root in roots do
    let input ← source root
    let cfg := config root
    let cert ← IO.ofExcept (Recheck.RcReplay.Cert.ofText (← IO.FS.readFile (bundle / s!"{root}.rc.json")))
    let artifact ← IO.ofExcept ((Recheck.RcReplay.run cfg input.program cert).mapError (·.message))
    let some drop := artifact.front.lowered.program.funcs[artifact.front.drop]? |
      throw (IO.userError "public release entry is absent")
    unless drop.name == "cx_drop" && drop.conv == .sysvExport "cx_drop" &&
        drop.params == [0] && drop.results == 1 && artifact.front.reps artifact.front.drop == some [.word] do
      throw (IO.userError "release entry does not have the raw-word ownership ABI")
    unless artifact.backend.object == (← IO.FS.readBinFile (bundle / s!"{root}.producer.o")) do
      throw (IO.userError s!"{root}: fresh validated ELF differs byte-for-byte from producer ELF")
    unless !cert.base.alloc.isEmpty && !cert.base.frames.isEmpty && !cert.base.order.isEmpty do
      throw (IO.userError "positive RC certificate lacks backend decisions")
    refused cfg input.program { cert with base := { cert.base with alloc := [] } } "missing-allocation" .alloc
    refused cfg input.program { cert with base := { cert.base with alloc := cert.base.alloc ++ cert.base.alloc } }
      "extra-allocation" .alloc
    refused cfg input.program { cert with base := { cert.base with frames := [] } } "missing-frames" .stacking
    refused cfg input.program { cert with base := { cert.base with order := [] } } "missing-order" .layout
    refused cfg input.program { cert with own := .null } "missing-ownership" .cert
    let some entry := artifact.roots.head? | throw (IO.userError "missing actual RC root")
    let some (sig, ty) := entry.ty | throw (IO.userError "missing complete result signature")
    let exe ← CompilatrixTests.Rt.Native.link { work := logs }
      s!"replayed-{root}" artifact.backend.object entry.symbol
    let cases := if root == "reverseRepeated" then
      [(0, 9), (1, 2), (5, 7), (64, 3)]
      else [(0, 7), (1, 42), (4, 3), (7, 0), (32, 11), (128, 100)]
    let rows ← CompilatrixTests.Rt.Native.run exe
      { region := 131072, stack := 1048576, ty := some (sig, ty), dump := true }
      (cases.map fun (n, seed) => [n, seed])
    let mut observations : Array Json := #[]
    for ((n, seed), row) in cases.zip rows do
      let want := expected root n seed
      unless row.status == 0 && row.ok && !row.init && row.obs == some (Rt.renderObs want) &&
          row.readback 131072 sig ty == some want do
        throw (IO.userError s!"{root} {n} {seed}: fresh RC certificate native value differs")
      let some dump := row.dump | throw (IO.userError "missing RC replay memory dump")
      if row.value &&& 1 == 0 then
        unless ((dump.memory 131072).read64 row.value) >>> 32 == 0 do
          throw (IO.userError "replayed result is not dynamically unique")
      observations := observations.push (Json.mkObj [
        ("n", toJson n), ("seed", toJson seed), ("value", toJson row.value.toNat),
        ("full_observation", toJson (Rt.renderObs want)),
        ("base", toJson dump.base.toNat), ("start", toJson dump.start.toNat),
        ("bump", toJson dump.bump.toNat), ("bytes", toJson (dump.bytes.map UInt8.toNat))])
    IO.FS.writeFile (logs / s!"{root}.observations.json") ((toJson observations).pretty ++ "\n")
    let hashes ← IO.Process.output {
      cmd := "sha256sum", args := #[exe.toString, (logs / s!"replayed-{root}.o").toString] }
    unless hashes.exitCode == 0 do throw (IO.userError "RC replay artifact hashing failed")
    IO.FS.writeFile (logs / s!"{root}.artifacts.sha256") hashes.stdout
    unless (List.range artifact.front.cfg.base.size).all (fun f =>
        ((artifact.front.cfg.base.fun? f).map fun fd =>
          fd.blocks.all fun b => b.body.all CompilatrixTests.Rt.Rc.ReuseSupport.class3Allocation).getD false) do
      throw (IO.userError "independent free-address oracle needs two-field actual allocations")
    let reuseExe ← CompilatrixTests.Rt.Rc.ReuseSupport.link logs root entry.symbol artifact.backend.object
    reuseReports := reuseReports.push (← CompilatrixTests.Rt.Rc.ReuseSupport.runDriver logs reuseExe root sig ty)
    IO.println s!"PASS fresh complete RC recheck {root}: exact ELF bytes, five stage-specific refusals, {cases.length} full C+Lean values"
  IO.FS.writeFile (logs / "reuse-results.json") ((toJson reuseReports).pretty ++ "\n")
  IO.FS.writeFile (logs / "result.txt") "Three fresh complete RC certificate rechecks with public raw-word cx_drop; exact producer ELF bytes;15 stage-specific malformed-decision refusals;16 full native C+Lean observations and dynamic result counts;168 same-arena calls/output drops with full values and exact reclamation.\n"

end CompilatrixTests.Recheck.Rc.ReplayIO
