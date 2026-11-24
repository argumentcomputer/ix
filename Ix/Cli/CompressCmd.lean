module
public import Cli
public import Ix.Cli.Compression
public import Ix.Cli.CompressionCmd
public import Ix.Cli.StarkShrinker
public import Ix.Cli.FormalAggregate
public import Ix.Cli.FormalCompress
public import Ix.Cli.AiurCompression
public import Ix.Cli.ClaimPolicy

public section
namespace Ix.Cli.CompressCmd

/-- Selected compression output: the curve backend (for KZG/SNARK), the proof
system, and the setup policy.
`finalProof`: 0 = kzg, 1 = plonk, 2 = groth16, 3 = stark-128 (v6), 4 = stark-128-zk (v6-zk). -/
structure Options where
  curve : String := "bn254"
  finalProof : UInt8 := 0
  compact : Bool := false
  devKzgSrs : Bool := false
  devFinalSrs : Bool := false
  out : Option String := none
  rootVk : Option String := none
  fresh : Bool := false
  aiur : Option AiurCompression.Options := none

/-- Resolve `--curve`, `--bn254`, and `--bls12-381` flags cleanly, rejecting
conflicting or unknown curve selections. -/
def resolveCurve (p : Cli.Parsed) : Except String String := do
  let hasBn := p.hasFlag "bn254"
  let hasBls := p.hasFlag "bls12-381"
  if hasBn && hasBls then
    throw "choose at most one of --bn254 and --bls12-381"
  let explicit? := (p.flag? "curve").map (·.as! String)
  let normalized? ← match explicit? with
    | none => pure none
    | some "bn254" => pure (some "bn254")
    | some "bls12-381" | some "bls12_381" => pure (some "bls12-381")
    | some other =>
      throw s!"unknown compression curve {other}: expected bn254 or bls12-381"
  match hasBn, hasBls, normalized? with
  | true, false, some "bls12-381" => throw "--bn254 conflicts with --curve bls12-381"
  | false, true, some "bn254" => throw "--bls12-381 conflicts with --curve bn254"
  | false, true, _ => pure "bls12-381"
  | true, false, _ => pure "bn254"
  | false, false, some c => pure c
  | false, false, none => pure "bn254"
  | true, true, _ => throw "choose at most one of --bn254 and --bls12-381"

private def outputDirectory (opts : Options) (addr : Address) : IO String := do
  match opts.out with
  | some path => return path
  | none => return ((← StoreIO.toIO Store.getHomeDir) / ".ix/compression" / toString addr).toString

/-- Whether `finalProof` selects Endpoint 1 native `Fp^3` STARK shrinking. -/
def isNativeStark (finalProof : UInt8) : Bool :=
  finalProof == 3 || finalProof == 4

/-- Select the proof system independently of its setup policy. -/
def finalOf : String → Except String UInt8
  | "kzg" => .ok 0
  | "plonk" => .ok 1
  | "groth16" => .ok 2
  | "stark-128" => .ok 3
  | "stark-128-zk" => .ok 4
  | other => .error s!"unknown compression output {other}: expected kzg, plonk, groth16, stark-128 or stark-128-zk"

/-- Check what can be checked before proving: the setup is configured and
authenticates, and the options are consistent. Returns the setup description. -/
def preflight (p : Cli.Parsed) (opts : Options) : IO String := do
  if isNativeStark opts.finalProof then
    if opts.aiur.isSome then
      throw <| IO.userError "--aiur-gl / --aiur-chain cannot be combined with --stark-128 / --stark-128-zk"
    if p.hasFlag "curve" || p.hasFlag "bn254" || p.hasFlag "bls12-381" then
      throw <| IO.userError "--curve, --bn254 and --bls12-381 are not used with --stark-128 / --stark-128-zk"
    if opts.devKzgSrs || opts.devFinalSrs || opts.fresh || opts.out.isSome then
      throw <| IO.userError "--dev-kzg-srs, --dev-final-srs, --fresh and --out are not used with --stark-128 / --stark-128-zk"
    let paramsDesc := if opts.compact then
      "1-circuit Plonkish ULTRA_COMPACT_400KB_ZK (lb=4, q=55, qpow=30, mla=3, lfp=8, 137.53b Johnson, ~344-389 KiB)"
    else
      "1-circuit Plonkish COMPACT_400KB_BALANCED (lb=4, q=58, qpow=28, mla=3, lfp=8, 141.39b Johnson, ~361-405 KiB)"
    if opts.finalProof == 4 then
      return s!"Endpoint 1 native Fp^3 STARK shrinker (--stark-128-zk, Protocol v6-zk, zero-knowledge, transparent, {paramsDesc})"
    else
      return s!"Endpoint 1 native Fp^3 STARK shrinker (--stark-128, Protocol v6, transparent NON-ZK, {paramsDesc})"
  if opts.compact then
    throw <| IO.userError "--compact requires --stark-128 or --stark-128-zk"
  if opts.aiur.isSome && (opts.finalProof != 0 || opts.rootVk.isSome || opts.devFinalSrs || opts.curve != "bn254") then
    throw (IO.userError "Aiur compression currently produces BN254 KZG proofs; --bls12-381, --plonk, --groth16, --root-vk and --dev-final-srs are incompatible")
  if let some aiur := opts.aiur then
    let _ ← AiurCompression.preflightOptions aiur opts.devKzgSrs
  Compression.describeSetupForCurve opts.curve opts.devKzgSrs opts.devFinalSrs opts.finalProof

/-- Refuse an input other than an uncompressed proof of a `CheckEnv` (or `Catalog`
for native STARK shrinking) claim. -/
private def checkInput (wrapper : Ixon.Proof) (nativeStark : Bool := false) : IO Unit := do
  if Compression.isCompressed wrapper.proof || StarkShrinker.isShrunk wrapper.proof then
    throw <| IO.userError "proof is already compressed or shrunk"
  match wrapper.claim with
  | .checkEnv .. => pure ()
  | .catalog _ =>
    unless nativeStark do
      throw <| IO.userError "KZG/SNARK compression requires an aggregate CheckEnv proof"
  | _ => throw <| IO.userError "compression requires an aggregate CheckEnv proof"

/-- Compress the aggregate root `addr`, persist the compressed proof under the
same claim and return its address. -/
private def compressProof (p : Cli.Parsed) (addr : Address) (wrapper : Ixon.Proof)
    (opts : Options) (setup : String) : IO Address := do
  let nativeStark := isNativeStark opts.finalProof
  checkInput wrapper nativeStark
  unless FormalCompress.isFormalRoot wrapper.proof do
    throw <| IO.userError "compression requires a formal aggregate root (IXAGGR2); legacy Aiur roots are retired"
  -- The statement comes from the same backend `ix verify --aggregate` uses;
  -- a trusted root key only replaces the verifying key the outer verifier checks.
  let ctx ← FormalAggregate.context p
  let statement := FormalAggregate.statementBytes ctx.toKeys wrapper.claim
  let vk ← match opts.rootVk with
    | some path => IO.FS.readBinFile path
    | none => pure ctx.aggr.key
  if nativeStark then
    let isZk := opts.finalProof == 4
    let device? := (p.flag? "gpu-device").map (·.as! Nat)
    let (hasDevice, deviceU32) := match device? with
      | some d => (true, d.toUInt32)
      | none => (false, (0 : UInt32))
    let proof ← match wrapper.claim with
      | .checkEnv .. => do
        let layout ← Compression.releaseRootLayout vk
        IO.eprintln s!"Normalizing aggregate root {addr} for Plonkish STARK shrinking."
        let root ← FormalCompress.normalize p ctx wrapper layout
        Compression.releaseGpuMemory
        IO.eprintln s!"Shrinking aggregate root {addr} with {setup}."
        StarkShrinker.shrinkFixedRootRaw vk layout root statement
          isZk opts.compact hasDevice deviceU32
      | .catalog _ => do
        let verifierPath ← FormalAiur.verifierArtifactPath p
        let pinnedDigest ← StarkShrinker.pinnedVerifierDigest
        let rawAggr ← FormalAggregate.rawProof .aggr wrapper.proof
        IO.eprintln s!"Shrinking catalog aggregate root {addr} with {setup} (v1 Aiur verifier)."
        StarkShrinker.shrinkRaw verifierPath pinnedDigest vk statement rawAggr
          isZk opts.compact hasDevice deviceU32
      | _ => throw <| IO.userError "native STARK shrinking requires a CheckEnv or Catalog claim"
    let shrunk : Ixon.Proof := { claim := wrapper.claim, proof }
    return ← StoreIO.toIO (Store.write (Ixon.Proof.ser shrunk))
  Compression.checkClaim (Ix.Claim.ser wrapper.claim) statement
  let out ← outputDirectory opts addr
  if opts.fresh then IO.eprintln s!"[compress] fresh: replacing stage artifacts in {out}"
  if let some aiur := opts.aiur then
    let raw ← FormalAggregate.rawProof .aggr wrapper.proof
    Compression.releaseGpuMemory
    IO.eprintln s!"Compressing raw aggregate root {addr} with {aiur.label} and {setup}."
    let proof ← AiurCompression.runOptions aiur ctx.aggr.key raw (Ix.Claim.ser wrapper.claim) statement
      out opts.devKzgSrs opts.fresh
    let compressed : Ixon.Proof := { claim := wrapper.claim, proof }
    return ← StoreIO.toIO (Store.write (Ixon.Proof.ser compressed))
  -- Every root is normalized to the release's one layout, whose keys the
  -- compression verifier is derived for; the statement must belong to them.
  let layout ← Compression.releaseRootLayout vk
  Compression.checkReleaseStatement (Ix.Claim.ser wrapper.claim) statement
  -- A root normalized earlier into `<out>/root` (`ix compress normalize`, for
  -- instance by a CPU build when the wrap exceeds one device) is reused; the
  -- pipeline refuses a `root/` whose key, statement or layout differ from
  -- this proof's.
  let normalized := System.FilePath.mk out / "root" / "root-proof.bin"
  let isolatedStage := match ← IO.getEnv "IX_COMPRESS_STAGE" with
    | some s => !s.isEmpty
    | none => false
  let root ← if (!opts.fresh || isolatedStage) && (← normalized.pathExists) then do
      IO.eprintln s!"Reusing the normalized root in {normalized}."
      IO.FS.readBinFile normalized
    else do
      IO.eprintln s!"Normalizing aggregate root {addr} for compression."
      FormalCompress.normalize p ctx wrapper layout
  Compression.releaseGpuMemory
  IO.eprintln s!"Compressing aggregate root {addr} with {setup}."
  let proof ← Compression.compressForCurve vk root (Ix.Claim.ser wrapper.claim) statement
    layout out (← Compression.cacheDir).toString opts.curve
    opts.devKzgSrs opts.devFinalSrs opts.finalProof opts.fresh
  let compressed : Ixon.Proof := { claim := wrapper.claim, proof }
  StoreIO.toIO (Store.write (Ixon.Proof.ser compressed))

/-- Compress a stored aggregate proof and return the compressed proof address. -/
def compressRoot (p : Cli.Parsed) (addr : Address) (opts : Options) : IO Address := do
  if opts.fresh && opts.aiur.isSome then AiurCompression.resetOutput (← outputDirectory opts addr)
  let setup ← preflight p opts
  compressProof p addr (← Compression.readProof addr) opts setup

def runCompressCmd (p : Cli.Parsed) : IO UInt32 := do
  try
    if p.hasFlag "fresh" && AiurCompression.selected p then
      if let some out := p.flag? "out" then AiurCompression.resetOutput (out.as! String)
      else if let some addr := Address.fromString (p.positionalArg! "proof" |>.as! String) then
        AiurCompression.resetOutput (← outputDirectory {} addr)
    let modeFlags := #["plonk", "groth16", "stark-128", "stark-128-zk"].filter p.hasFlag
    if modeFlags.size > 1 then
      throw <| IO.userError "choose at most one of --plonk, --groth16, --stark-128, and --stark-128-zk"
    let curve ← IO.ofExcept (resolveCurve p)
    let finalProof : UInt8 :=
      if p.hasFlag "stark-128-zk" then 4
      else if p.hasFlag "stark-128" then 3
      else if p.hasFlag "groth16" then 2
      else if p.hasFlag "plonk" then 1
      else 0
    let aiur ← if AiurCompression.selected p then some <$> AiurCompression.options p else pure none
    let opts : Options := {
      curve
      finalProof
      compact := p.hasFlag "compact"
      fresh := p.hasFlag "fresh"
      devKzgSrs := p.hasFlag "dev-kzg-srs"
      devFinalSrs := p.hasFlag "dev-final-srs"
      out := (p.flag? "out").map (·.as! String)
      rootVk := (p.flag? "root-vk").map (·.as! String)
      aiur }
    let input := p.positionalArg! "proof" |>.as! String
    if opts.aiur.isSome then
      let (addr, wrapper) ← Compression.readProofInput input
      if opts.fresh then AiurCompression.resetOutput (← outputDirectory opts addr)
      let setup ← preflight p opts
      let result ← compressProof p addr wrapper opts setup
      IO.println (toString result)
      return 0
    let setup ← preflight p opts
    let (addr, wrapper) ← Compression.readProofInput input
    -- the input's shape before the policy, which then sees only `CheckEnv` (or `Catalog`) claims
    checkInput wrapper (isNativeStark opts.finalProof)
    let statement ← ClaimPolicy.admit p wrapper.claim
    IO.eprintln s!"Compressing a proof of claim {Address.blake3 (Ix.Claim.ser wrapper.claim)}:\n\
      {statement}"
    let result ← compressProof p addr wrapper opts setup
    IO.println (toString result)
    return 0
  catch e =>
    IO.eprintln s!"compress: {e}"
    return 1

end Ix.Cli.CompressCmd

open Ix.Cli.CompressCmd in
def compressCmd : Cli.Cmd := `[Cli|
  compress VIA runCompressCmd;
  "Compress an aggregate CheckEnv proof; preserve its claim and print the new proof address."
  FLAGS:
    "aiur-chain" : String; "Use the trusted GL-to-BN chain manifest with independently pinned artifacts and keys."
    "aiur-chain-blake3" : String; "Independent BLAKE3 pin for the exact --aiur-chain manifest bytes."
    "aiur-gl" : String; "Use the Aiur CompressGL KZG stage with this independently trusted compiler artifact."
    "aiur-gl-blake3" : String; "Independent BLAKE3 pin for --aiur-gl."
    "aiur-kzg-key" : String; "Independently trusted CompressGL KZG verifier key."
    "aiur-kzg-key-blake3" : String; "Independent BLAKE3 pin for --aiur-kzg-key."
    "aiur-max-log-height" : Nat; "Fixed public Aiur trace-height bound (default 24)."
    "aiur-quotient-degree" : Nat; "Fixed public Aiur quotient-degree budget (default 2)."
    "aiur-artifact" : String; "Trusted exported formal IxVM artifact; otherwise compile/cache local sources."
    "aiur-artifact-digest" : String; "Require the IxVM artifact's BLAKE3 digest to equal these 64 hex digits (or IX_AIUR_ARTIFACT_DIGEST)."
    "aggr-artifact" : String; "Trusted formal aggregation artifact; otherwise compile/cache local sources."
    "aggr-artifact-digest" : String; "Require the aggregation artifact's BLAKE3 digest to equal these 64 hex digits (or IX_AGGR_ARTIFACT_DIGEST)."
    "verifier-artifact" : String; "Trusted formal recursive verifier artifact for --stark-128 / --stark-128-zk; otherwise compile/cache local sources."
    "verifier-artifact-digest" : String; "Require the recursive verifier artifact's BLAKE3 digest to equal these 64 hex digits (or IX_VERIFIER_ARTIFACT_DIGEST)."
    "fresh"; "Replace prior compression stages in --out (or the default output) with newly generated proofs. Reuse parameters, proving keys and fixed preprocessing."
    "out" : String; "Output directory for stage proofs (default ~/.ix/compression/<root>). Aiur runs require --fresh when the directory is nonempty."
    "root-vk" : String; "Trusted root verifier key; omit to use the current aggregate backend."
    "max-ram" : Nat; "RAM budget in GiB for native root normalization; does not cap Aiur KZG workspaces (default MemTotal less 20%)."
    "gpu-device" : Nat; "Prove the normalized root or native STARK shrinker on this CUDA device (requires a CUDA build)."
    "dev-kzg-srs"; "Generate local development parameters for inner KZG. With --groth16 or --plonk, also requires --dev-final-srs."
    "dev-final-srs"; "Generate and cache local development Groth16 or PLONK keys for the selected inner verifier. With --dev-kzg-srs, no ceremony parameters are required."
    "curve" : String; "Pairing curve backend: bn254 (default, ~100b classical / 0b PQ, Ignition SRS) or bls12-381 (~126–128b classical / 0b PQ, EIP-2537, Filecoin challenge_19 SRS)."
    "bn254"; "Use the BN254 pairing curve backend (default, ~100b classical / 0b PQ, Ignition SRS)."
    "bls12-381"; "Use the BLS12-381 pairing curve backend (~126–128b classical / 0b PQ, EIP-2537, Filecoin challenge_19 SRS)."
    "plonk"; "Add a final PLONK proof using the selected curve and setup."
    "groth16"; "Add a final Groth16 proof using the selected curve and prepared, independently admitted circuit keys."
    "stark-128"; "Endpoint 1: shrink into a compact (~361 KiB) transparent post-quantum 128-bit 1-circuit Plonkish Protocol v6 (Fp^3) STARK (zero trusted setup, NON-ZK)."
    "stark-128-zk"; "Endpoint 1: shrink into a compact (~405 KiB) zero-knowledge post-quantum 128-bit 1-circuit Plonkish Protocol v6-zk (Fp^3) STARK (zero trusted setup, 128-bit hiding PCS)."
    "compact"; "With --stark-128 or --stark-128-zk: use 1-circuit Plonkish ULTRA_COMPACT_400KB_ZK (lb=4, q=55, qpow=30, mla=3, lfp=8, ~344-389 KiB; default COMPACT_400KB_BALANCED lb=4, q=58, qpow=28, mla=3, lfp=8, ~361-405 KiB)."
    "binding-env" : String; "An `.ixe` whose role binding is the claim's table, with the records it binds and its evidence theorems: the kernel admits the table over them (once per table; recorded in `~/.ix/cache/table-admission`)."
    "allow-custom-binding"; "Compress a claim relative to a role binding the kernel does not admit here, or to a literal class (outside the IxVM consistency theorem)."
    "allow-axioms"; "Compress a claim that depends on axioms beyond the standard three."
    "allow-assumed-binding"; "Compress a claim that assumes its role binding meets the specifications."
    "allow-assumptions"; "Compress a claim conditional on typing assumptions (assumed leaves)."
  ARGS:
    proof : String; "Aggregate Ixon.Proof file (including its claim), or its 64-character content address in the ix store. A hexadecimal filename needs a ./ prefix."

  SUBCOMMANDS:
    Ix.Cli.AiurCompression.keyCmd;
    Ix.Cli.AiurCompression.checkCmd;
    Ix.Cli.AiurCompression.chainKeyCmd;
    Ix.Cli.CompressionCmd.layoutCmd;
    Ix.Cli.CompressionCmd.normalizeCmd;
    Ix.Cli.CompressionCmd.setupCmd
]
end
