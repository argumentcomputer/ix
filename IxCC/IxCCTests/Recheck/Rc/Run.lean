import IxCCTests.Recheck.Rc.CodecIO
import IxCCTests.Recheck.Rc.ReplayIO
import IxCCTests.Recheck.Rc.FreshIO

namespace IxCCTests.Recheck.Rc
open IxCC Lean System

/-- Verify that `RcReplay.produce` / `Own.Plain.Program.canonicalForSrc` honors
`Src` and `Src.Resource` contract annotations (`borrowed` -> `.borrow`,
`once`/`unique` -> `.unique`) and that `selectPolicy` / `produceAuto` select
`.zeroRc` vs `.plainRc` in a single front-end pass. -/
def verifyContractsAndPolicy : IO Unit := do
  let input ← Fixtures.source "reverseList"
  let cfg := ReplayIO.config "reverseList"
  let p ← IO.ofExcept ((Recheck.RcReplay.produceWith cfg input).mapError (·.message))
  let (cert, artifact) ← IO.ofExcept ((Recheck.RcReplay.produce cfg input).mapError (·.message))
  unless cert.toText == p.cert.toText do
    throw (IO.userError "single-pass produceWith and produce certificates differ")
  let some rootFun := p.front.fir.exports.head? |
    throw (IO.userError "reverseList: missing exported FIR function")
  let some (_, rootCId) := p.front.src.roots.head? |
    throw (IO.userError "reverseList: missing Src root")
  unless p.own.funParamModes rootFun == [.shared, .shared] do
    throw (IO.userError s!"reverseList unannotated param modes: {repr (p.own.funParamModes rootFun)}")
  let annotatedSrc : Src.Program :=
    { p.front.src with
      resource := some
        { address := default
          bytes := .empty
          pairs :=
            [ { definition := p.front.src.addr rootCId
                equation := default
                profile := default
                contracts :=
                  [ { position := 0, contract := { value := .localShared } },
                    { position := 1, contract := { uses := .linear, value := .unique } } ] } ] } }
  let contractOwn := Own.Plain.Program.canonicalForSrc annotatedSrc p.front.fir
  unless contractOwn.funParamModes rootFun == [.borrow, .unique] do
    throw (IO.userError
      s!"canonicalForSrc did not map borrowed/unique contracts: got {repr (contractOwn.funParamModes rootFun)}")
  unless contractOwn.funParamSigs rootFun ==
      [ { mode := .borrowed false, kind := .shared, rep := .tobj },
        { mode := .owned, kind := .unique true, rep := .tobj } ] do
    throw (IO.userError
      s!"canonicalForSrc PSigs mismatch: got {repr (contractOwn.funParamSigs rootFun)}")
  unless Own.Plain.bodyMapEq contractOwn.bodies p.own.bodies do
    throw (IO.userError "canonicalForSrc bodies differ from canonical bodies")
  let pol ← IO.ofExcept ((Recheck.RcReplay.selectPolicy cfg input).mapError (·.message))
  unless pol == .plainRc do
    throw (IO.userError s!"reverseList selectPolicy expected .plainRc, got {repr pol}")
  match ← IO.ofExcept ((Recheck.RcReplay.produceAuto cfg input).mapError (·.message)) with
  | .plainRc autoCert autoArt _ =>
    unless autoCert.toText == cert.toText && autoArt.backend.object == artifact.backend.object do
      throw (IO.userError "produceAuto (.plainRc) differs from produce")
  | .zeroRc .. =>
    throw (IO.userError "reverseList produceAuto unexpectedly selected .zeroRc")
  | .immortal _ _ _ reason =>
    throw (IO.userError s!"reverseList produceAuto fell back to .immortal: {reason.render}")
  let gcdBytes ← IO.FS.readBinFile "fixtures/ixon-v4/bench-k1/gcd.ixe"
  let gcdEqs ← IO.ofExcept (Json.parse (← IO.FS.readFile "fixtures/ixon-v4/bench-k1/gcd.equations.json"))
  let gcdInput ← IO.ofExcept ((Recheck.ingress gcdBytes gcdEqs ["entry"] false).mapError (·.message))
  let gcdCfg : Recheck.Config := { names := ["gcd"] }
  let gcdPol ← IO.ofExcept ((Recheck.RcReplay.selectPolicy gcdCfg gcdInput).mapError (·.message))
  unless gcdPol == .zeroRc do
    throw (IO.userError s!"gcd selectPolicy expected .zeroRc, got {repr gcdPol}")
  match ← IO.ofExcept ((Recheck.RcReplay.produceAuto gcdCfg gcdInput).mapError (·.message)) with
  | .zeroRc zeroCert zeroArt _ =>
    let (wantCert, wantArt) ← IO.ofExcept ((Recheck.compileInput gcdCfg gcdInput).mapError (·.message))
    unless zeroCert.toText == wantCert.toText && zeroArt.object == wantArt.object do
      throw (IO.userError "gcd produceAuto (.zeroRc) differs from Recheck.compileInput")
  | .plainRc .. | .immortal .. =>
    throw (IO.userError "gcd produceAuto did not select .zeroRc")
  IO.println "PASS contract-aware canonicalForSrc (.borrow/.unique), selectPolicy, and single-pass produceAuto"

def run (args : List String) : IO Unit := do
  Fixtures.verify
  match args with
  | [] | ["--cc", _] =>
    verifyContractsAndPolicy
    IO.FS.withTempDir fun logs => FreshIO.run logs
  | ["fresh", logs] =>
    verifyContractsAndPolicy
    FreshIO.run logs
  | [mode, phase, bundle, logs] =>
    IO.FS.createDirAll bundle
    IO.FS.createDirAll logs
    match mode, phase with
    | "codec", "write" => CodecIO.write bundle
    | "codec", "read" => CodecIO.read bundle logs
    | "replay", "write" => ReplayIO.write bundle
    | "replay", "read" => ReplayIO.read bundle logs
    | _, _ => throw (IO.userError "expected codec/replay write/read BUNDLE LOGDIR")
  | _ => throw (IO.userError "expected [--cc CC], fresh LOGDIR, or codec/replay write/read BUNDLE LOGDIR")
  Fixtures.verify

end IxCCTests.Recheck.Rc
