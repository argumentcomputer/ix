import Compilatrix.Ixby.Lean
import Compilatrix.Ixby.Runtime.Wire
import Compilatrix.Ixby.Runtime.Execute
import Compilatrix.Ixby.Runtime.Report
import Compilatrix.Tools.Check
import Compilatrix.Ixon.Hash
import Ix.MultiStark.Verify.Source

open Lean Compilatrix.Tools.Check Compilatrix.Ixby.LeanFrontend
open Compilatrix.Ixby.Runtime

private def limits : Ix.Ixby.Limits := {
  functions := 65536, constructors := 4096, blocks := 65536, locals := 8192,
  operands := 1024, continuations := 65536, inputNodes := 65536,
  natBits := 4096, stringBytes := 65536, byteArrayBytes := 16777216 }

private def frozenGuest (ixvm aggregate : Array UInt8) : BuildM Unit := do
  discard <| defineFunction `Ixby.Runtime.Stage2Guest 2 do
    let child ← packedBytes ixvm
    let key ← packedBytes aggregate
    let aggregate ← make `MultiStark.Verify.AggregateConfig.mk
      [child, ← number 755, key, ← number 243]
    let decode ← make `MultiStark.Verify.DecodeLimits.mk
      [← number 16777216, ← number 1048576, ← number 2097152]
    let transcript ← make `MultiStark.Verify.Transcript.Limits.mk [← number 16777216, ← number 64]
    let verifier ← make `MultiStark.Verify.Fri.Limits.mk [← number 1024, ← number 256, transcript]
    let config ← make `MultiStark.Verify.SourceConfig.mk [aggregate, decode, verifier]
    let pack (value : Ix.Ixby.Operand) : CodeM Ix.Ixby.Operand := do
      let length ← primitive .bytesLength [value]
      make `Ixby.Runtime.Bytes [value, ← call `Ixby.Runtime.fromWord [length]]
    let publicClaim ← pack (.local 0)
    let proof ← pack (.local 1)
    let result ← call `MultiStark.Verify.claimBytesWrapper [config, publicClaim, proof]
    caseCtor result #[
      (`Option.none, 0, fun _ => ret .erased),
      (`Option.some, 1, fun fields => tailCall `Ixby.Runtime.toBytes [fields[0]!])]

private def buildImage (directory : System.FilePath) : IO Image := do
  let ixvm ← IO.FS.readBinFile (directory / "ixvm.vk")
  let aggregate ← IO.FS.readBinFile (directory / "aggr.vk")
  need (ixvm.size == 744159 && (Compilatrix.Ixon.Address.blake3 ixvm).toHex ==
    "3983867e9f70a82d990ea65e15265da105617317b95b4b1482e7a7b854ca8063") "fixed IxVM key differs"
  need (aggregate.size == 181630 && (Compilatrix.Ixon.Address.blake3 aggregate).toHex ==
    "75452941bc0dbe4a861c88c792067f34d7864f0460f305858a0a004ec409406e") "fixed aggregate key differs"
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Ix.MultiStark.Verify.Source }] {}
  let job : CoreM (Except String Image) := do
    let result ← compile `MultiStark.Verify.claimBytesWrapper limits (setup := buildWire)
    match result with
    | .error message => return .error message
    | .ok image =>
      let built ← ((do
        frozenGuest ixvm.data aggregate.data
        finishProgram (← functionId `Ixby.Runtime.Stage2Guest) : BuildM Ix.Ixby.Program).run image.state).run
      return built.map fun (program, state) => { image with program, state }
  let (result, _) ← job.toIO
    { fileName := "Stage2 typed Ixby compilation", fileMap := default, maxRecDepth := 32768, maxHeartbeats := 0 }
    { env }
  checked result

private def execute (image : Image) (input : Array Ix.Ixby.Value) : IO (Ix.Ixby.Value × Nat) := do
  let mut state ← checked <| (Ix.Ixby.initialState limits image.program input).mapError reprStr
  let mut steps := 0
  for chunk in [:16000] do
    let (result, count) ← checked <| (runChunk limits image.program 1000000 state 0).mapError reprStr
    steps := steps + count
    match result with
    | .inl value => return (value, steps)
    | .inr next => state := next
    if chunk % 10 == 0 then
      let location := match state.control with
        | .eval frame => toString image.state.functions[frame.function]!.name
        | .ret _ => "return"
        | .apply _ _ => "apply"
      IO.println s!"stage2-ixby steps={steps}; {location}"
      if chunk % 100 == 0 then
        let callers := state.continuation.toList.filterMap fun continuation =>
          match continuation with
          | .resume frame =>
            let name := toString image.state.functions[frame.function]!.name
            if name.startsWith "MultiStark.Verify." then some name else none
          | _ => none
        IO.println s!"stage2-ixby callers: {String.intercalate " > " (callers.take 8)}"
        if let some frame := state.continuation.toList.reverse.findSome? (fun continuation =>
            match continuation with
            | .resume frame =>
              if image.state.functions[frame.function]!.name == `MultiStark.Verify.Fri.reduceQueries then
                some frame else none
            | _ => none) then
          if let .ok query := image.decodeNumber (frame.locals[4]?.getD .erased) then
            if let .ok remaining := image.decodeNumber (frame.locals[5]?.getD .erased) then
              IO.println s!"stage2-ixby FRI query {query + 1}/{query + remaining}"
      (← IO.getStdout).flush
  throw (IO.userError "Stage2 Ixby step limit")

def main (args : List String) : IO UInt32 := cli "stage2-ixby" do
  let (directory, name, report) ← match args with
    | [directory, name] => pure (directory, name, none)
    | [directory, "compile", report] => pure (directory, "compile", some report)
    | _ => throw (IO.userError "usage: stage2-ixby <fixture-directory> <compile [inventory.json]|case>")
  let directory : System.FilePath := directory
  let image ← buildImage directory
  let blocks := image.program.functions.foldl (fun n f => n + f.blocks.size) 0
  IO.println s!"stage2-ixby compiled: {image.program.functions.size} functions; {blocks} blocks; {image.program.constructors.size} constructors; reference only; source refinement uncertified"
  (← IO.getStdout).flush
  if name == "compile" then
    if let some path := report then IO.FS.writeFile path (image.report.pretty ++ "\n")
    return
  need (["valid", "claim-mismatch", "empty-proof", "truncated-proof", "trailing-public",
    "trailing-proof", "wrong-claim-kind", "malformed-proof"].contains name) "unknown Stage2 case"
  let publicClaim ← IO.FS.readBinFile (directory / "smoke-public.claim")
  let expectedClaim ← checked (unhex "e571cbf135649af05f7cce8ba201a48e46556de51483f690cc6ec500a65530059c00")
  need (publicClaim == expectedClaim) "Stage2 claim differs"
  IO.FS.withTempDir fun temporary => do
    let archive := temporary / "proof.bin.gz"
    IO.FS.writeBinFile archive (← IO.FS.readBinFile (directory / "smoke-native-proof.bin.gz"))
    let _ ← run "gzip" #["-d", archive.toString]
    let digest := (words (← run "sha256sum" #[(temporary / "proof.bin").toString])).headD ""
    need (digest == "c495ab47db90bdb3b245391c18967e7c264ffb8d51c4c39605ee6f47cd0e7bb9") "Stage2 proof differs"
    let proof ← IO.FS.readBinFile (temporary / "proof.bin")
    let claim := match name with
      | "claim-mismatch" => publicClaim.data.set! 1 (publicClaim.data[1]! ^^^ 1)
      | "trailing-public" => publicClaim.data.push 0
      | "wrong-claim-kind" => publicClaim.data.set! 0 0xe4
      | _ => publicClaim.data
    let proof := match name with
      | "empty-proof" => #[]
      | "truncated-proof" => proof.data.extract 0 (proof.size - 1)
      | "trailing-proof" => proof.data.push 0
      | "malformed-proof" => #[0xff, 0xff]
      | _ => proof.data
    let (output, steps) ← execute image #[.scalar (.bytes claim), .scalar (.bytes proof)]
    let expected : Ix.Ixby.Value := if name == "valid" then .scalar (.bytes publicClaim.data) else .erased
    need (output == expected) s!"Stage2 Ixby result differs in {name}: {reprStr output}"
    IO.println s!"stage2-ixby ok: {name}; {steps} reference steps; source refinement uncertified"
