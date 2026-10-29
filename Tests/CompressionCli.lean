module
public import Ix.Cli.Compression

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
    ("IX_KZG_IGNITION_CACHE", none), ("IX_KZG_IGNITION_CACHE_BLAKE3", none),
    ("IX_KZG_IGNITION_ADMISSION", none), ("IX_KZG_IGNITION_ADMISSION_BLAKE3", none),
    ("IX_PARAMS_DIR", some (home / "params").toString),
    ("IX_GROTH16_ARTIFACTS", none)] ++ setupEnv }

private def rejects (home : System.FilePath) (args : Array String) (message : String)
    (setupEnv : Array (String × Option String) := #[]) : IO Unit := do
  let out ← invoke home args setupEnv
  unless out.exitCode != 0 && (out.stderr.splitOn message).length > 1 do
    throw <| IO.userError s!"expected rejection ({message}): {args}\n{out.stdout}\n{out.stderr}"

public def run : IO Unit := do
  unless (← Ix.Cli.Compression.curve) == "bn254" do
    throw <| IO.userError "unexpected compression curve"
  for tag in ["IXCMP", "IXBN"] do
    unless Ix.Cli.Compression.isCompressed tag.toUTF8 do
      throw <| IO.userError s!"unrecognized compressed proof family: {tag}"
  let home ← IO.FS.createTempDir
  try
    let help ← invoke home #["compress", "--help"]
    unless help.exitCode == 0 && (help.stdout.splitOn "--root-vk").length > 1 do
      throw <| IO.userError s!"compress help failed: {help.stdout} {help.stderr}"
    unless (help.stdout.splitOn "--dev-groth16").length == 1 do
      throw <| IO.userError "compression help exposes a development proof-system selector"
    let claim := Ix.Claim.checkEnv (Address.blake3 "test".toUTF8) none
    let native : Ixon.Proof := { claim, proof := "native".toUTF8 }
    let compressed : Ixon.Proof := { claim, proof := "IXCMP".toUTF8 }
    let other : Ixon.Proof :=
      { claim := Ix.Claim.check (Address.blake3 "test".toUTF8) none, proof := "native".toUTF8 }
    let old ← putProof home (Ixon.Proof.ser native)
    let addr ← putProof home (Ixon.Proof.ser compressed)
    let otherAddr ← putProof home (Ixon.Proof.ser other)
    rejects home #["compress", toString old, "--groth16", "--plonk"]
      "choose at most one"
    rejects home #["compress", toString old, "--dev-groth16"]
      "Unknown flag"
    rejects home #["compress", toString old, "--dev-srs"] "Unknown flag"
    rejects home #["prove", "--ixe", "missing.ixe", "--ixes", "missing.ixes",
      "--compress", "dev-groth16"] "unknown compression output"
    rejects home #["compress", toString old, "--dev-final-srs"]
      "requires a final proof system"
    for finalFlag in #["--plonk", "--groth16"] do
      rejects home #["compress", toString old, finalFlag, "--dev-kzg-srs"]
        "requires --dev-final-srs"
    unless old != addr && native.claim == compressed.claim do
      throw <| IO.userError "compression must preserve claim identity and change proof identity"
    rejects home #["compress", toString old] "--dev-kzg-srs"
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
    let cacheVar := "IX_KZG_IGNITION_CACHE"
    let setupError := "incomplete BN254 Ignition configuration"
    let missingCache := #[(cacheVar, some (home / "missing-setup-cache").toString)]
    rejects home #["compress", toString addr] setupError missingCache
    rejects home #["compress", toString addr, "--dev-kzg-srs"] "already compressed" missingCache
    rejects home #["compress", toString addr, "--groth16", "--dev-final-srs"] setupError missingCache
    for finalFlag in #["--plonk", "--groth16"] do
      rejects home #["compress", toString addr, finalFlag, "--dev-kzg-srs", "--dev-final-srs"]
        "already compressed" missingCache
      rejects home #["compress", filePath.toString, finalFlag, "--dev-kzg-srs", "--dev-final-srs"]
        "aggregate CheckEnv proof" missingCache
    rejects home #["prove", "--ixe", "missing.ixe", "--ixes", "missing.ixes",
      "--compress", "groth16", "--dev-final-srs"] setupError missingCache
    rejects home #["verify", toString addr] "unsupported compressed proof version"
    rejects home #["verify", toString addr, "--dev-srs"] "unsupported compressed proof version"
    rejects home #["verify", toString addr, "--verifier-bundle", "/missing", "--dev-srs"]
      "must be supplied together"
    rejects home #["verify", toString addr, "--verifier-bundle", "/missing",
      "--verifier-bundle-blake3", String.ofList (List.replicate 64 '0')]
      "requires --dev-srs"
    let removed ← invoke home #["verifier", "import", "/missing"]
    unless removed.exitCode != 0 do
      throw <| IO.userError "external verifier import remains available"

    let unknownKey := ByteArray.mk #[73, 88, 66, 78, 0, 0, 0, 1] ++
      ByteArray.mk (Array.replicate 32 0)
    let unknownAddr ← putProof home (Ixon.Proof.ser { claim, proof := unknownKey })
    rejects home #["verify", toString unknownAddr] "other than the"
    rejects home #["verify", toString unknownAddr, "--dev-srs"] "other than the"
    IO.println "compression CLI: BN254 setup and proof rejection checks passed"
  finally
    IO.FS.removeDirAll home

end Tests.CompressionCli
end
