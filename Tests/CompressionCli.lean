module
public import Ix.Cli.Compression

public section
namespace Tests.CompressionCli

private def store (home : System.FilePath) (bytes : ByteArray) : IO Address := do
  let addr := Address.blake3 bytes
  let hex := toString addr
  let path := home / ".ix/store" / (hex.take 2).toString /
    ((hex.drop 2).take 2).toString / ((hex.drop 4).take 2).toString
  IO.FS.createDirAll path
  IO.FS.writeBinFile (path / (hex.drop 6).toString) bytes
  return addr

private def invoke (home : System.FilePath) (args : Array String) : IO IO.Process.Output := do
  let ix ← IO.FS.realPath ".lake/build/bin/ix"
  IO.Process.output { cmd := ix.toString, args, env := #[("HOME", some home.toString)] }

private def rejects (home : System.FilePath) (args : Array String) (message : String) : IO Unit := do
  let out ← invoke home args
  unless out.exitCode != 0 && (out.stderr.splitOn message).length > 1 do
    throw <| IO.userError s!"expected rejection ({message}): {args}\n{out.stdout}\n{out.stderr}"

public def run : IO Unit := do
  let home ← IO.FS.createTempDir
  try
    let help ← invoke home #["compress", "--help"]
    unless help.exitCode == 0 && (help.stdout.splitOn "--root-vk").length > 1 do
      throw <| IO.userError s!"compress help failed: {help.stdout} {help.stderr}"
    let claim := Ix.Claim.checkEnv (Address.blake3 "test".toUTF8) none
    let native : Ixon.Proof := { claim, proof := "native".toUTF8 }
    let compressed : Ixon.Proof := { claim, proof := "IXCMP".toUTF8 }
    let old ← store home (Ixon.Proof.ser native)
    let addr ← store home (Ixon.Proof.ser compressed)
    unless old != addr && native.claim == compressed.claim do
      throw <| IO.userError "compression must preserve claim identity and change proof identity"
    rejects home #["compress", toString old] "--dev-srs"
    rejects home #["compress", toString old, "--dev-srs", "--out", (home / "run").toString]
      "only the measured Init root claim"
    unless !(← (home / "run").pathExists) do
      throw <| IO.userError "unsupported input created checkpoints"
    rejects home #["compress", toString addr, "--dev-srs"] "already compressed"
    rejects home #["verify", toString addr] "--dev-srs"
    rejects home #["verify", toString addr, "--dev-srs"] "only the measured Init root claim"
    rejects home #["compress", toString old, "--dev-srs"] "only the measured Init root claim"
    rejects home #["verifier", "import", "/missing"] "--dev-srs"
    rejects home #["verifier", "import", "/missing", "--dev-srs"] "--digest"
    -- Optional verification of the measured full Init packet through the actual CLI.
    if let some root ← IO.getEnv "IX_COMPRESSION_TEST_ROOT" then
      let some profile ← IO.getEnv "IX_COMPRESSION_TEST_PROFILE"
        | throw <| IO.userError "IX_COMPRESSION_TEST_PROFILE required"
      let original ← IO.ofExcept (Ixon.Proof.de (← IO.FS.readBinFile root))
      let sourceAddr ← store home (Ixon.Proof.ser original)
      let badVk := home / "bad-vk.bin"
      IO.FS.writeBinFile badVk ByteArray.empty
      let defaultArgs := #["compress", toString sourceAddr, "--dev-srs", "--root-vk", badVk.toString]
      rejects home defaultArgs "compression fri failed"
      rejects home defaultArgs "compression fri failed"
      unless (← (home / ".ix/compression" / toString sourceAddr / "24/input-id.bin").pathExists) do
        throw <| IO.userError "default compression checkpoint path missing"
      let runDir := home / "run"
      let compressArgs := #["compress", toString sourceAddr, "--dev-srs", "--root-vk", badVk.toString,
        "--out", runDir.toString]
      rejects home compressArgs "compression fri failed"
      rejects home compressArgs "output already initialized"
      rejects home (compressArgs ++ #["--resume", "--log-height", "25"]) "resume input or compression profile differs"
      rejects home (compressArgs.push "--resume") "compression fri failed"
      unless !(← (runDir / "first-kzg").pathExists) do
        throw <| IO.userError "compression continued after failed source verification"
      let packet ← IO.FS.readBinFile (System.FilePath.mk profile / "kzg/packet.bin")
      let tag := ByteArray.mk #[73, 88, 67, 77, 80, 0, 0, 4]
      let proof := tag ++ packet
      let wrapped : Ixon.Proof := { claim := original.claim, proof }
      let compressedAddr ← store home (Ixon.Proof.ser wrapped)
      let args := #["verify", toString compressedAddr, "--dev-srs"]
      rejects home args "unknown compression verifier"
      let keyBytes ← IO.FS.readBinFile (System.FilePath.mk profile / "verifier.bin")
      let keyFile := home / "incoming-verifier.bin"
      IO.FS.writeBinFile keyFile keyBytes
      let keyDigest := Address.blake3 keyBytes
      let importArgs := #["verifier", "import", keyFile.toString, "--dev-srs", "--digest", toString keyDigest]
      rejects home (importArgs.set! 5 (toString (Address.blake3 "wrong".toUTF8))) "verifier digest mismatch"
      rejects home args "unknown compression verifier"
      let imported ← invoke home importArgs
      unless imported.exitCode == 0 do throw <| IO.userError s!"verifier import failed: {imported.stderr}"
      IO.FS.removeFile keyFile
      -- Registration copies the verifier; neither the original key file nor SRS is needed later.
      let alias := toString (Address.mk (packet.extract 0 32))
      let storedKey := home / ".ix/verifiers/development/keys" / s!"{keyDigest}.bin"
      IO.FS.writeBinFile storedKey (keyBytes.set! (keyBytes.size - 1) ((keyBytes.get! (keyBytes.size - 1)) ^^^ 1))
      rejects home args "registered verifier digest mismatch"
      IO.FS.writeBinFile storedKey keyBytes
      let mapping := home / ".ix/verifiers/development/profiles" / alias
      IO.FS.writeBinFile mapping (Address.blake3 "wrong mapping".toUTF8).hash
      let failed ← invoke home args
      unless failed.exitCode != 0 do throw <| IO.userError "wrong registry mapping accepted"
      IO.FS.writeBinFile mapping keyDigest.hash
      if let some runPath ← IO.getEnv "IX_COMPRESSION_TEST_RESUME" then
        let vkPath := (System.FilePath.mk root).parent.get! / "root-vk.bin"
        let vk ← IO.FS.readBinFile vkPath
        let le64 := fun (n : Nat) => ByteArray.mk <| (Array.range 8).map fun i =>
          ((n >>> (8 * i)) % 256).toUInt8
        let mut identity := "ix-compress-run/v1".toUTF8
        for bytes in [vk, original.proof, Ix.Claim.ser original.claim] do
          identity := identity ++ le64 bytes.size ++ bytes
        identity := identity ++ ByteArray.mk #[25, 0, 0, 0]
        IO.FS.writeBinFile (System.FilePath.mk runPath / "input-id.bin") (Address.blake3 identity).hash
        IO.FS.removeDirAll (home / ".ix/verifiers")
        let result ← invoke home #["compress", toString sourceAddr, "--dev-srs", "--resume",
          "--out", runPath, "--root-vk", vkPath.toString, "--log-height", "25"]
        unless result.exitCode == 0 && result.stdout.trimAscii.toString == toString compressedAddr do
          throw <| IO.userError s!"full pipeline resume did not produce expected proof address:\n{result.stdout}\n{result.stderr}"
        IO.println s!"Full Init pipeline resumed; ix compress printed {compressedAddr}."
      let verifyStarted ← IO.monoMsNow
      let out ← invoke home args
      IO.println s!"CLI verification: {(← IO.monoMsNow) - verifyStarted}ms; portable verifier: {keyBytes.size} bytes"
      unless out.exitCode == 0 do
        throw <| IO.userError s!"Init packet failed CLI verification:\n{out.stdout}\n{out.stderr}"
      IO.println out.stdout
      for bad in [proof.set! 7 2, proof.set! (proof.size - 1) ((proof.get! (proof.size - 1)) ^^^ 1)] do
        let badAddr ← store home (Ixon.Proof.ser { wrapped with proof := bad })
        let out ← invoke home (args.set! 1 (toString badAddr))
        unless out.exitCode != 0 do throw <| IO.userError "modified compressed packet accepted"
      let badClaim ← store home (Ixon.Proof.ser { wrapped with claim })
      rejects home (args.set! 1 (toString badClaim)) "only the measured Init root claim"
      IO.println s!"Init compressed wrapper: {(Ixon.Proof.ser wrapped).size} bytes; claim preserved."
    IO.println "compression CLI: identity, input validation, setup opt-in and verifier routing passed"
  finally
    IO.FS.removeDirAll home

end Tests.CompressionCli

end
