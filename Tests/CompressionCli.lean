module
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
  let claimCtx : Ix.ClaimContext := { spec := testHash, binding := testHash, axioms := none }
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
  unless out.exitCode != 0 do
    throw <| IO.userError s!"the bundled compressed proof verified another claim:\n{out.stdout}"
  IO.println "compression CLI: the release keys accept the formal backends"

public def run : IO Unit := do
  unless (← Ix.Cli.Compression.curve) == "bn254" do
    throw <| IO.userError "unexpected compression curve"
  for tag in ["IXCMP", "IXBN"] do
    unless Ix.Cli.Compression.isCompressed tag.toUTF8 do
      throw <| IO.userError s!"unrecognized compressed proof family: {tag}"
  let home ← IO.FS.createTempDir
  let setupError := "no BN254 Ignition SRS is installed; run `ix compress setup`"
  try
    let help ← invoke home #["compress", "--help"]
    unless help.exitCode == 0 && (help.stdout.splitOn "--root-vk").length > 1 do
      throw <| IO.userError s!"compress help failed: {help.stdout} {help.stderr}"
    let testHash := Address.blake3 "test".toUTF8
    let ctx : Ix.ClaimContext := { spec := testHash, binding := testHash, axioms := none }
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
    IO.println "compression CLI: BN254 setup and proof rejection checks passed"
    releaseAccepts home
  finally
    IO.FS.removeDirAll home

end Tests.CompressionCli
end
