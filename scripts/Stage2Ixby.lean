import Compilatrix.Ixby.Runtime.Native.Image
import Compilatrix.Ixby.Inline.Image
import Compilatrix.Ixby.Runtime.Wire
import Compilatrix.Ixby.Runtime.Field
import Compilatrix.Ixby.Binary
import Compilatrix.Ixby.Runtime.Report
import Compilatrix.Ixby.Stage2.FriSound
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

private def buildImage (directory : System.FilePath) (fuseFri : Bool) : IO Image := do
  let ixvm ← IO.FS.readBinFile (directory / "ixvm.vk")
  let aggregate ← IO.FS.readBinFile (directory / "aggr.vk")
  need (ixvm.size == 744159 && (Compilatrix.Ixon.Address.blake3 ixvm).toHex ==
    "3983867e9f70a82d990ea65e15265da105617317b95b4b1482e7a7b854ca8063") "fixed IxVM key differs"
  need (aggregate.size == 181630 && (Compilatrix.Ixon.Address.blake3 aggregate).toHex ==
    "75452941bc0dbe4a861c88c792067f34d7864f0460f305858a0a004ec409406e") "fixed aggregate key differs"
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Ix.MultiStark.Verify.Source },
    { module := `Compilatrix.Ixby.Stage2.FriSound }] {}
  let job : CoreM (Except String Image) := do
    let result ← compile `MultiStark.Verify.claimBytesWrapper limits (setup := buildWire)
      (sourceEqualities := if fuseFri then #[``Compilatrix.Ixby.Stage2.Fri.reducePoints_eq] else #[])
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
  let image ← checked result
  need image.state.sourceReplacementRejection.isNone "FRI source replacement was rejected"
  need (image.state.sourceReplacements.size == if fuseFri then 1 else 0)
    "FRI source replacement count differs"
  for replacement in image.state.sourceReplacements do
    let target := image.state.functionNames[replacement.target]?
    need (target.isSome && image.state.functionNames[replacement.source]? == target)
      "FRI source replacement was not used by compilation"
  discard <| checked image.certifyWireRuntime
  return image

def main (args : List String) : IO UInt32 := cli "stage2-ixby" do
  let (directory, name, path) ← match args with
    | [directory, name] => pure (directory, name, none)
    | [directory, name, path] => pure (directory, name, some path)
    | _ => throw (IO.userError "usage: stage2-ixby <fixture-directory> <compile|compile-no-fri|compile-baseline|case> [program.ixby]")
  let directory : System.FilePath := directory
  let programPath : System.FilePath := path.getD (directory / "stage2.ixby").toString
  if name == "compile" || name == "compile-no-fri" || name == "compile-baseline" then
    let original ← buildImage directory (name == "compile")
    let policy : Compilatrix.Ixby.Inline.Policy := {
      enabled := name != "compile-baseline", protectedPrefix := 110 }
    let selected ← checked (Compilatrix.Ixby.Inline.optimizeImage original policy)
    let image := selected.image
    discard <| checked image.certifyWireRuntime
    let artifact : Compilatrix.Ixby.Binary.Artifact := {
      limits := image.state.limits, maxSteps := 16000000000, program := image.program }
    let encoded ← checked (Compilatrix.Ixby.Binary.encode artifact |>.mapError reprStr)
    let decoded ← checked (Compilatrix.Ixby.Binary.decode encoded |>.mapError reprStr)
    need (decoded.value == artifact) "serialized Stage2 image changed during decoding"
    discard <| checked (Compilatrix.Ixby.Inline.check decoded.value.limits
      original.program decoded.value.program policy.protectedPrefix)
    discard <| checked ({ image with program := decoded.value.program } : Image).certifyWireRuntime
    if let some parent := programPath.parent then IO.FS.createDirAll parent
    IO.FS.writeBinFile programPath ⟨encoded⟩
    let metadata := Json.mkObj [
      ("format", toJson "compilatrix-ixby-binary/1"),
      ("program_semantics", toJson Compilatrix.Ixby.Binary.semantics),
      ("bytes", toJson encoded.size), ("sha256", toJson (← sha256 programPath)),
      ("max_steps", toJson artifact.maxSteps)]
    let fields ← checked image.report.getObj?
    let baseline ← checked (Compilatrix.Ixby.Binary.encode
      { artifact with program := original.program } |>.mapError reprStr)
    let optimization := Json.mkObj [
      ("pass", toJson "ordinary-leaf-inlining"), ("version", toJson policy.version),
      ("enabled", toJson policy.enabled), ("status", toJson (reprStr selected.selected.status)),
      ("protected_prefix", toJson policy.protectedPrefix),
      ("scan_work", toJson (Compilatrix.Ixby.Inline.work original.program)),
      ("max_work", toJson policy.maxWork),
      ("original_binary_blake3", toJson (Compilatrix.Ixon.Address.blake3 ⟨baseline⟩).toHex),
      ("decoded_program_certificate_checked", toJson true)]
    let sourceOptimizations := image.state.sourceReplacements.map fun replacement => Json.mkObj [
      ("source", toJson replacement.source.toString),
      ("target", toJson replacement.target.toString),
      ("equality", toJson replacement.equality.toString),
      ("scope", toJson "kernel-source-equality; LCNF lowering remains experimental")]
    let report := Json.mkObj (("artifact", metadata) :: ("optimization", optimization) ::
      ("source_optimizations", toJson sourceOptimizations) :: fields.toList)
    IO.FS.writeFile (programPath.toString ++ ".json") (report.pretty ++ "\n")
    IO.println s!"stage2-ixby compiled: {image.program.functions.size} functions; {encoded.size} binary bytes; {programPath}"
    return
  need (["valid", "claim-mismatch", "empty-proof", "truncated-proof", "trailing-public",
    "trailing-proof", "wrong-claim-kind", "malformed-proof"].contains name) "unknown Stage2 case"
  let image ← checked (Compilatrix.Ixby.Binary.decode (← IO.FS.readBinFile programPath).data |>.mapError reprStr)
  IO.println s!"stage2-ixby loaded: {programPath}; {image.value.program.functions.size} functions"
  (← IO.getStdout).flush
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
    let input ← checked (Compilatrix.Ixby.Binary.encodeInput image.value
      #[.scalar (.bytes claim), .scalar (.bytes proof)] |>.mapError reprStr)
    let inputPath := temporary / "input.ixbi"
    let outputPath := temporary / "output.ixbo"
    let statsPath := temporary / "execution.json"
    IO.FS.writeBinFile inputPath ⟨input⟩
    let executable := ((← IO.appPath).parent.getD ".") / "ixby-exec"
    let child ← IO.Process.spawn {
      cmd := executable.toString
      args := #[programPath.toString, inputPath.toString, outputPath.toString, statsPath.toString]
      stdout := .inherit, stderr := .inherit }
    need ((← child.wait) == 0) "binary executor failed"
    let output ← checked (Compilatrix.Ixby.Binary.decodeOutput image.value
      (← IO.FS.readBinFile outputPath).data |>.mapError reprStr)
    let expected : Ix.Ixby.Value := if name == "valid" then .scalar (.bytes publicClaim.data) else .erased
    need (output.value == expected) s!"Stage2 Ixby result differs in {name}: {reprStr output.value}"
    let stats ← readJson statsPath
    let steps ← nat (← field stats "reference_transitions")
    IO.println s!"stage2-ixby ok: {name}; {steps} reference transitions; executed serialized binary"
