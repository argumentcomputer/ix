module
public import Ix.Cli.CompressCmd
public import Ix.Cli.Compression
public import Ix.Cli.FormalAggregate

public section
namespace Tests.CompressionCli

private def putProof (home : System.FilePath) (bytes : ByteArray) : IO Address := do
  let addr := Address.blake3 bytes
  let hex := toString addr
  let path := home / ".ix/store" / (hex.take 2).toString /
    ((hex.drop 2).take 2).toString / ((hex.drop 4).take 2).toString
  IO.FS.createDirAll path
  IO.FS.writeBinFile (path / (hex.drop 6).toString) bytes
  return addr

private def invoke (home : System.FilePath) (args : Array String)
    (setupEnv : Array (String × Option String) := #[]) : IO IO.Process.Output := do
  let ix ← IO.FS.realPath ".lake/build/bin/ix"
  IO.Process.output { cmd := ix.toString, args, env := #[("HOME", some home.toString),
    ("IX_KZG_SRS", none), ("IX_KZG_SRS_CACHE", none),
    ("IX_PARAMS_DIR", some (home / "params").toString),
    ("IX_GROTH16_ARTIFACTS", none)] ++ setupEnv }

private def rejects (home : System.FilePath) (args : Array String) (message : String)
    (setupEnv : Array (String × Option String) := #[]) : IO Unit := do
  let out ← invoke home args setupEnv
  unless out.exitCode != 0 && (out.stderr.splitOn message).length > 1 do
    throw <| IO.userError s!"expected rejection ({message}): {args}\n{out.stdout}\n{out.stderr}"

/-- A recursive KZG proof of `Nat.add_comm`'s aggregate root under the bundled
keys, a serialized `Ixon.Proof` with its claim (see `PROVENANCE.md` beside it). -/
private def compressedFixture : System.FilePath :=
  "Tests/Fixtures/Compression/nat-add-comm.ixon-proof"

/-- The bundled release keys belong to the current formal backends.

- `ix compress` accepts the formal aggregation key: the
  release has a layout (`.ixl`) for it, and a formal statement carries the
  release's statement prefix, the checks it makes before proving. Another
  IxVM backend's statement is refused.
- `ix verify` accepts a compressed proof of a formal aggregate root under the
  bundled keys, and refuses the same proof under another claim.

The IxVM and aggregation artifacts are `IX_AIUR_ARTIFACT` and
`IX_AGGR_ARTIFACT`, or the checkout's cached exports. -/
def releaseAccepts (home : System.FilePath) : IO Unit := do
  let ctx ← Ix.Cli.FormalAggregate.context default
  let layout ← Ix.Cli.Compression.releaseRootLayout ctx.aggr.key
  unless layout.extract 0 8 == "IXROOTL\x00".toUTF8 do
    throw <| IO.userError "the release root layout is not an .ixl file"
  let testHash := Address.blake3 "release".toUTF8
  -- a claim the claim policy admits, so that `ix verify` refuses it in the verifier
  let claimCtx ← IO.ofExcept Ix.ClaimContext.ofDefaultTable
  let claim := Ix.Claim.checkEnv claimCtx testHash none
  Ix.Cli.Compression.checkReleaseStatement (Ix.Claim.ser claim)
    (Ix.Cli.FormalAggregate.statementBytes ctx.toKeys claim)
  let other := { ctx with
    allowed := Aggr.allowedBlob ctx.ixvm.key (ctx.ixvm.index + 1) ctx.aggr.key ctx.aggr.index }
  let refused ←
    try
      Ix.Cli.Compression.checkReleaseStatement (Ix.Claim.ser claim)
        (Ix.Cli.FormalAggregate.statementBytes other.toKeys claim)
      pure false
    catch _ => pure true
  unless refused do
    throw <| IO.userError "the release accepted another backend's statement"
  let bytes ← IO.FS.readBinFile ((← Ix.Cli.FormalAiur.repoRoot) / compressedFixture)
  let fixture ← IO.ofExcept (Ixon.Proof.de bytes)
  unless Ix.Cli.Compression.isCompressed fixture.proof do
    throw <| IO.userError s!"{compressedFixture} is not a compressed proof"
  let addr ← putProof home bytes
  let out ← invoke home #["verify", toString addr]
  unless out.exitCode == 0 && (out.stdout.splitOn "Aztec Ignition").length > 1 do
    throw <| IO.userError s!"the bundled compressed proof did not verify:\n{out.stdout}\n{out.stderr}"
  let moved ← putProof home (Ixon.Proof.ser { fixture with claim := claim })
  let out ← invoke home #["verify", toString moved]
  unless out.exitCode != 0 && (out.stderr.splitOn "refused:").length == 1 do
    throw <| IO.userError s!"the bundled compressed proof verified another claim, or the claim \
      policy refused it before the verifier ran:\n{out.stdout}\n{out.stderr}"
  IO.println "compression CLI: the release keys accept the formal backends"

/-- Host-only compression CLI checks (BN254 curve, setup, and proof rejection).
Never invokes `FormalAggregate.context` or builds Mathlib/formal exporters, so
`host-test-cli` stays strictly Mathlib-free on `ci-host`. -/
public def runHost : IO Unit := do
  unless (← Ix.Cli.Compression.curve) == "bn254" do
    throw <| IO.userError "unexpected compression curve"
  for tag in ["IXCMP", "IXBN", "IXACG", "IXAUCH"] do
    unless Ix.Cli.Compression.isCompressed tag.toUTF8 do
      throw <| IO.userError s!"unrecognized compressed proof family: {tag}"
  let home ← IO.FS.createTempDir
  let setupError := "no BN254 Ignition SRS is installed; run `ix compress setup`"
  try
    let help ← invoke home #["compress", "--help"]
    unless help.exitCode == 0 && (help.stdout.splitOn "--root-vk").length > 1
        && (help.stdout.splitOn "COMPACT_400KB_BALANCED").length > 1
        && (help.stdout.splitOn "ULTRA_COMPACT_400KB_ZK").length > 1
        && (help.stdout.splitOn "IXL3BN1/IXL3BL1").length > 1
        && (help.stdout.splitOn "--l3-verifier").length > 1 do
      throw <| IO.userError s!"compress help failed: {help.stdout} {help.stderr}"
    let stagesHelp ← invoke home #["compress", "run-stages", "--help"]
    unless stagesHelp.exitCode == 0
        && (stagesHelp.stdout.splitOn "IXL3BN1/IXL3BL1").length > 1
        && (stagesHelp.stdout.splitOn "ix-l3-verifier-v1").length > 1 do
      throw <| IO.userError s!"compress run-stages help failed: {stagesHelp.stdout} {stagesHelp.stderr}"
    let verifyHelp ← invoke home #["verify", "--help"]
    unless verifyHelp.exitCode == 0
        && (verifyHelp.stdout.splitOn "--l3-verifier").length > 1
        && (verifyHelp.stdout.splitOn "--l3-verifier-blake3").length > 1 do
      throw <| IO.userError s!"verify help failed: {verifyHelp.stdout} {verifyHelp.stderr}"
    -- Endpoint 1 Plonkish STARK preflight descriptions and envelope version decoding
    let preV6 ← Ix.Cli.CompressCmd.preflight default { finalProof := 3 }
    unless (preV6.splitOn "COMPACT_400KB_BALANCED").length > 1
        && (preV6.splitOn "NON-ZK").length > 1 do
      throw <| IO.userError s!"unexpected --stark-128 preflight: {preV6}"
    let preZkCompact ← Ix.Cli.CompressCmd.preflight default { finalProof := 4, compact := true }
    unless (preZkCompact.splitOn "ULTRA_COMPACT_400KB_ZK").length > 1
        && (preZkCompact.splitOn "zero-knowledge").length > 1 do
      throw <| IO.userError s!"unexpected --stark-128-zk --compact preflight: {preZkCompact}"
    -- The setup banner states what development final keys are.
    let devPlonk := (Ix.Cli.CompressCmd.finalSetupNote { finalProof := 1, devFinalSrs := true }).getD ""
    let devGroth := (Ix.Cli.CompressCmd.finalSetupNote { finalProof := 2, devFinalSrs := true }).getD ""
    unless (devPlonk.splitOn "known-trapdoor development SRS").length > 1
        && (devPlonk.splitOn "never deploy").length > 1
        && (devGroth.splitOn "NOT production-secure").length > 1
        && (Ix.Cli.CompressCmd.finalSetupNote { finalProof := 1 }).isNone do
      throw <| IO.userError s!"--dev-final-srs banner note changed: {devPlonk} / {devGroth}"
    let v1Prefix := Ix.Cli.StarkShrinker.magic ++ ByteArray.mk #[1, 0]
    let v2Prefix := Ix.Cli.StarkShrinker.magic ++ ByteArray.mk #[2, 0]
    let v3Prefix := Ix.Cli.StarkShrinker.magic ++ ByteArray.mk #[3, 0]
    unless Ix.Cli.StarkShrinker.envelopeVersion v1Prefix == some 1
        && Ix.Cli.StarkShrinker.envelopeVersion v2Prefix == some 2
        && Ix.Cli.StarkShrinker.envelopeVersion v3Prefix == some 3
        && Ix.Cli.StarkShrinker.envelopeVersion Ix.Cli.StarkShrinker.magic == none
        && Ix.Cli.StarkShrinker.envelopeVersion "IXCMP".toUTF8 == none do
      throw <| IO.userError "StarkShrinker.envelopeVersion decoding check failed"
    let testHash := Address.blake3 "test".toUTF8
    -- claims the claim policy admits, so that each rejection below is the one tested
    let ctx ← IO.ofExcept Ix.ClaimContext.ofDefaultTable
    let claim := Ix.Claim.checkEnv ctx testHash none
    let native : Ixon.Proof := { claim, proof := "native".toUTF8 }
    let compressed : Ixon.Proof := { claim, proof := "IXCMP".toUTF8 }
    let other : Ixon.Proof :=
      { claim := Ix.Claim.check ctx testHash none, proof := "native".toUTF8 }
    let old ← putProof home (Ixon.Proof.ser native)
    let addr ← putProof home (Ixon.Proof.ser compressed)
    let otherAddr ← putProof home (Ixon.Proof.ser other)
    rejects home #["compress", toString old, "--groth16", "--plonk"]
      "choose at most one"
    rejects home #["compress", toString old, "--stark-128", "--stark-128-zk"]
      "choose at most one"
    rejects home #["compress", toString old, "--stark-128", "--groth16"]
      "choose at most one"
    rejects home #["compress", toString old, "--bn254", "--bls12-381"]
      "choose at most one"
    rejects home #["compress", toString old, "--stark-128", "--bls12-381"]
      "not used with --stark-128 / --stark-128-zk"
    rejects home #["compress", toString old, "--stark-128", "--dev-kzg-srs"]
      "not used with --stark-128 / --stark-128-zk"
    rejects home #["compress", toString old, "--compact"]
      "--compact requires --stark-128 or --stark-128-zk"
    let shrunk : Ixon.Proof := { claim, proof := "IXSTARK6\x00".toUTF8 }
    let shrunkAddr ← putProof home (Ixon.Proof.ser shrunk)
    rejects home #["compress", toString shrunkAddr, "--stark-128"]
      "already compressed or shrunk"
    rejects home #["compress", toString shrunkAddr, "--stark-128-zk"]
      "already compressed or shrunk"
    -- Truncated and unknown-version IXSTARK6 envelopes fail closed before loading formal artifacts
    rejects home #["verify", toString shrunkAddr]
      "truncated or malformed IXSTARK6 envelope header"
    let shrunkV3 : Ixon.Proof := { claim, proof := v3Prefix }
    let shrunkV3Addr ← putProof home (Ixon.Proof.ser shrunkV3)
    rejects home #["verify", toString shrunkV3Addr]
      "unsupported IXSTARK6 envelope version 3"
    -- Plonkish v2 envelope paired with a Catalog claim is rejected fail-closed
    let v2CatalogRejected ←
      try
        let _ ← Ix.Cli.FormalAggregate.verifyShrunkProof default shrunkV3Addr
          { claim := Ix.Claim.catalog testHash, proof := v2Prefix } ""
        pure false
      catch e =>
        pure (decide (((toString e).splitOn "Plonkish v2 shrunk STARK proof").length > 1))
    unless v2CatalogRejected do
      throw <| IO.userError "verifyShrunkProof did not reject v2 Plonkish envelope for a Catalog claim"
    rejects home #["compress", toString old, "--aiur-chain", "missing-chain.json",
      "--aiur-gl", "gl.ixa", "--dev-kzg-srs"] "cannot be combined"
    rejects home #["verify", toString old, "--aiur-chain", "missing-chain.json"]
      "requires --aggregate"
    rejects home #["prove", "--ixe", "missing.ixe", "--ixes", "missing.ixes",
      "--compress", "fri"] "unknown compression output"
    rejects home #["compress", toString old, "--dev-final-srs"]
      "--dev-final-srs requires a final proof system"
    for finalFlag in #["--plonk", "--groth16"] do
      rejects home #["compress", toString old, finalFlag, "--dev-kzg-srs"]
        "development inner KZG requires --dev-final-srs with a final proof"
    unless old != addr && native.claim == compressed.claim do
      throw <| IO.userError "compression must preserve claim identity and change proof identity"
    rejects home #["compress", toString old] setupError
    rejects home #["compress", toString old, "--dev-kzg-srs", "--out", (home / "run").toString]
      "formal aggregate root"
    rejects home #["compress", toString otherAddr, "--dev-kzg-srs", "--out", (home / "run").toString]
      "aggregate CheckEnv proof"
    unless !(← (home / "run").pathExists) do
      throw <| IO.userError "unsupported input created output"
    let fileProof : Ixon.Proof := { other with proof := "file-native".toUTF8 }
    let fileBytes := Ixon.Proof.ser fileProof
    let filePath := home / "aggregate-proof.bin"
    IO.FS.writeBinFile filePath fileBytes
    let (fileAddr, loaded) ← Ix.Cli.Compression.readProofInput filePath.toString
    unless fileAddr == Address.blake3 fileBytes && Ixon.Proof.ser loaded == fileBytes do
      throw <| IO.userError "file input changed the proof or its content address"
    rejects home #["compress", filePath.toString, "--dev-kzg-srs", "--out", (home / "file-run").toString]
      "aggregate CheckEnv proof"
    let fileHex := toString fileAddr
    let storedFile := home / ".ix/store" / (fileHex.take 2).toString /
      ((fileHex.drop 2).take 2).toString / ((fileHex.drop 4).take 2).toString /
      (fileHex.drop 6).toString
    unless !(← storedFile.pathExists) && !(← (home / "file-run").pathExists) do
      throw <| IO.userError "file input was imported into the store or created output before validation"
    rejects home #["compress", toString addr, "--dev-kzg-srs"] "already compressed"
    let missingSrs := #[("IX_KZG_SRS", some (home / "missing-srs.bin").toString)]
    rejects home #["compress", toString addr] setupError missingSrs
    rejects home #["compress", toString addr, "--dev-kzg-srs"] "already compressed" missingSrs
    rejects home #["compress", toString addr, "--groth16", "--dev-final-srs"] setupError missingSrs
    for finalFlag in #["--plonk", "--groth16"] do
      rejects home #["compress", toString addr, finalFlag, "--dev-kzg-srs", "--dev-final-srs"]
        "already compressed" missingSrs
      rejects home #["compress", filePath.toString, finalFlag, "--dev-kzg-srs", "--dev-final-srs"]
        "aggregate CheckEnv proof" missingSrs
    rejects home #["prove", "--ixe", "missing.ixe", "--ixes", "missing.ixes",
      "--compress", "groth16", "--dev-final-srs"] setupError missingSrs
    rejects home #["verify", toString addr] "unsupported compressed proof version"
    rejects home #["verify", toString addr, "--dev-srs"] "unsupported compressed proof version"
    rejects home #["verify", toString addr, "--verifier-bundle", "/missing", "--dev-srs"]
      "must be supplied together"
    rejects home #["verify", toString addr, "--verifier-bundle", "/missing",
      "--verifier-bundle-blake3", String.ofList (List.replicate 64 '0')]
      "requires --dev-srs"

    let unknownKey := ByteArray.mk #[73, 88, 66, 78, 0, 0, 0, 1] ++
      ByteArray.mk (Array.replicate 32 0)
    let unknownAddr ← putProof home (Ixon.Proof.ser { claim, proof := unknownKey })
    rejects home #["verify", toString unknownAddr] "other than the"
    rejects home #["verify", toString unknownAddr, "--dev-srs"] "other than the"

    -- Aiur L3 proof envelope (`IXL3BN1\0` / `IXL3BL1\0`) classification, pin enforcement,
    -- and fail-closed verification checks
    unless Ix.Cli.FormalAggregate.isL3Proof Ix.Cli.FormalAggregate.l3Bn254ProofTag
        && Ix.Cli.FormalAggregate.isL3Proof Ix.Cli.FormalAggregate.l3Bls12381ProofTag
        && !Ix.Cli.FormalAggregate.isL3Proof "IXCMP".toUTF8
        && !Ix.Cli.FormalAggregate.isL3Proof "IXAGGR2\x00".toUTF8 do
      throw <| IO.userError "FormalAggregate.isL3Proof tag classification failed"
    let l3VkSha256 : ByteArray := ByteArray.mk #[
      0x96, 0xca, 0x1e, 0x8d, 0x17, 0x6b, 0x8f, 0x0f,
      0xb4, 0x1d, 0xc5, 0xa6, 0x6b, 0xdd, 0x55, 0x3b,
      0xa4, 0x80, 0x48, 0x93, 0x69, 0xab, 0xc3, 0x37,
      0xa7, 0xc5, 0xb3, 0x97, 0xd3, 0xc8, 0x27, 0x9d]
    let l3ProofBytes := Ix.Cli.FormalAggregate.l3Bn254ProofTag ++ l3VkSha256 ++ ByteArray.mk #[1, 2, 3, 4]
    let l3Serialized := Ixon.Proof.ser { claim, proof := l3ProofBytes }
    let l3Addr ← putProof home l3Serialized
    let l3File := home / "l3.ixon-proof"
    IO.FS.writeBinFile l3File l3Serialized
    rejects home #["compress", toString l3Addr, "--dev-kzg-srs"] "already compressed or shrunk"
    rejects home #["verify", toString l3Addr] "--l3-verifier"
    rejects home #["verify", "--aggregate", toString l3Addr] "--l3-verifier"
    rejects home #["verify", toString l3Addr, "--l3-verifier", "/missing"]
      "must be supplied together"
    rejects home #["verify", toString l3Addr, "--l3-verifier-blake3",
      String.ofList (List.replicate 64 '0')] "must be supplied together"
    let hexOf (c : Char) (n : Nat) := String.ofList (List.replicate n c)
    let l3BundleJson :=
      "{\"format\":\"ix-l3-verifier-v1\",\"curve\":\"bn254\",\"setup\":\"development\"," ++
      s!"\"root_vk_blake3\":\"{hexOf '1' 64}\"," ++
      "\"root_statement_prefix\":[1,0,2,3,4,5,6,7,8,9]," ++
      "\"wrap_policy\":{" ++
      s!"\"artifact_blake3\":\"{hexOf '1' 64}\"," ++
      s!"\"key_blake3\":\"{hexOf '2' 64}\"," ++
      s!"\"layout_blake3\":\"{hexOf '3' 64}\"," ++
      "\"claim_prefix\":[1,0]}," ++
      "\"terminal_vk_sha256\":\"96ca1e8d176b8f0fb41dc5a66bdd553ba480489369abc337a7c5b397d3c8279d\"," ++
      s!"\"terminal_vk_hex\":\"{hexOf '4' 128}\"," ++
      s!"\"anchors_hex\":\"{hexOf '5' 640}\"" ++ "}"
    let l3BundlePath := home / "l3-verifier.json"
    IO.FS.writeFile l3BundlePath l3BundleJson
    let l3BundlePin := toString (Address.blake3 l3BundleJson.toUTF8)
    rejects home #["verify", toString l3Addr, "--l3-verifier", l3BundlePath.toString,
      "--l3-verifier-blake3", hexOf '0' 64, "--dev-srs"] "differs from pinned"
    rejects home #["verify", toString l3Addr, "--l3-verifier", l3BundlePath.toString,
      "--l3-verifier-blake3", l3BundlePin] "development setup"
    rejects home #["verify", l3File.toString, "--l3-verifier", l3BundlePath.toString,
      "--l3-verifier-blake3", l3BundlePin] "development setup"
    rejects home #["verify", toString l3Addr, "--l3-verifier", l3BundlePath.toString,
      "--l3-verifier-blake3", l3BundlePin, "--verifier-bundle", "/x"]
      "cannot be combined with --verifier-bundle"
    rejects home #["verify", toString l3Addr, "--l3-verifier", l3BundlePath.toString,
      "--l3-verifier-blake3", l3BundlePin, "--dev-srs"] "L3"
    IO.println "compression CLI: BN254 setup and proof rejection checks passed"
  finally
    IO.FS.removeDirAll home

/-- Formal-artifact release-key acceptance check (`releaseAccepts`). Requires
`IX_AIUR_ARTIFACT` / `IX_AGGR_ARTIFACT` (or formal `.ixa` exports) and belongs
in formal CI (`ci:binding-proof` / `formal-check`), never on Mathlib-free
`host-test-cli`. -/
public def runRelease : IO Unit := do
  let home ← IO.FS.createTempDir
  try
    releaseAccepts home
  finally
    IO.FS.removeDirAll home

/-- Default entry used by `ci:cli` (`host-test-cli`): runs host-only checks. -/
public def run : IO Unit := runHost

end Tests.CompressionCli
end
