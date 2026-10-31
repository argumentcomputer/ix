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
    (filecoinCache : Option String := none) : IO IO.Process.Output := do
  let ix ← IO.FS.realPath ".lake/build/bin/ix"
  IO.Process.output { cmd := ix.toString, args, env := #[("HOME", some home.toString),
    ("IX_KZG_FILECOIN_CACHE", filecoinCache), ("IX_KZG_FILECOIN_MANIFEST", none)] }

private def rejects (home : System.FilePath) (args : Array String) (message : String)
    (filecoinCache : Option String := none) : IO Unit := do
  let out ← invoke home args filecoinCache
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
    let other : Ixon.Proof :=
      { claim := Ix.Claim.check (Address.blake3 "test".toUTF8) none, proof := "native".toUTF8 }
    let old ← putProof home (Ixon.Proof.ser native)
    let addr ← putProof home (Ixon.Proof.ser compressed)
    let otherAddr ← putProof home (Ixon.Proof.ser other)
    let compressionRoot := home / ".ix/compression"
    let firstRun ← Ix.Cli.Compression.newRunDir old 24 true (some compressionRoot)
    let secondRun ← Ix.Cli.Compression.newRunDir old 24 true (some compressionRoot)
    unless firstRun != secondRun && (← firstRun.isDir) && (← secondRun.isDir) do
      throw <| IO.userError "default compression runs must get separate directories"
    let firstParent := compressionRoot / "development/runs" / toString old / "24"
    unless firstRun.parent == some firstParent && secondRun.parent == some firstParent do
      throw <| IO.userError "development run directory is outside its default root"
    let productionRun ← Ix.Cli.Compression.newRunDir old 24 false (some compressionRoot)
    unless productionRun.parent == some (compressionRoot / "runs" / toString old / "24") do
      throw <| IO.userError "production run directory is outside its default root"
    unless old != addr && native.claim == compressed.claim do
      throw <| IO.userError "compression must preserve claim identity and change proof identity"
    rejects home #["compress", toString old] "--dev-srs"
    rejects home #["compress", toString otherAddr, "--dev-srs", "--out", (home / "run").toString]
      "aggregate CheckEnv proof"
    unless !(← (home / "run").pathExists) do
      throw <| IO.userError "unsupported input created output"
    rejects home #["compress", toString addr, "--dev-srs"] "already compressed"
    let missingCache := some (home / "missing-filecoin-cache").toString
    rejects home #["compress", toString addr] "does not name a file" missingCache
    rejects home #["compress", toString addr, "--dev-srs"] "already compressed" missingCache
    rejects home #["verify", toString addr] "unsupported compressed proof version"
    rejects home #["verify", toString addr, "--dev-srs"] "unsupported compressed proof version"
    let removed ← invoke home #["verifier", "import", "/missing"]
    unless removed.exitCode != 0 do
      throw <| IO.userError "external verifier import remains available"

    let fixtures : System.FilePath := "crates/proof-compression/tests/fixtures/aggregate-kzg"
    let expected ← IO.ofExcept (Ix.Claim.de (← IO.FS.readBinFile (fixtures / "filecoin-claim.bin")))
    let packet ← IO.FS.readBinFile (fixtures / "filecoin-v5-packet.bin")
    let tag := ByteArray.mk #[73, 88, 67, 77, 80, 0, 0, 4]
    let proof := tag ++ packet
    let wrapped : Ixon.Proof := { claim := expected, proof }
    let compressedAddr ← putProof home (Ixon.Proof.ser wrapped)
    let metadata ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile
      "crates/proof-compression/verifying-keys/aggregate-filecoin-v5.json"))
    let expectedAddr ← IO.ofExcept (metadata.getObjValAs? String "compressed_proof_address")
    unless toString compressedAddr == expectedAddr do
      throw <| IO.userError "production proof address differs from its metadata"
    let args := #["verify", toString compressedAddr]
    let out ← invoke home args
    unless out.exitCode == 0 && (out.stdout.splitOn "Filecoin").length > 1 do
      throw <| IO.userError s!"production Filecoin proof failed: {out.stdout} {out.stderr}"
    let aggregateArgs := #["verify", "--aggregate", toString compressedAddr]
    let aggregate ← invoke home aggregateArgs
    unless aggregate.exitCode == 0 && (aggregate.stdout.splitOn "Filecoin").length > 1 do
      throw <| IO.userError s!"production aggregate proof failed: {aggregate.stdout} {aggregate.stderr}"
    unless (aggregate.stdout.splitOn "aggregate backend setup").length == 1 do
      throw <| IO.userError "compressed aggregate verification constructed the native backend"
    rejects home (aggregateArgs ++ #["--ixe", "Tests/Fixtures/ixon-v4/handoff/accepted.ixe"])
      "does not match expected"
    unless !(← (home / ".ix/verifiers").pathExists) do
      throw <| IO.userError "verification created a filesystem verifier registry"

    -- A local registry cannot replace a verifier carried by the application.
    let alias := toString (Address.mk (packet.extract 0 32))
    let keys := home / ".ix/verifiers/filecoin/keys"
    IO.FS.createDirAll keys
    IO.FS.writeBinFile (keys / alias) "invalid registry entry".toUTF8
    let independent ← invoke home args
    unless independent.exitCode == 0 do
      throw <| IO.userError s!"verification read an external registry: {independent.stderr}"
    IO.FS.removeDirAll (home / ".ix/verifiers")

    let badClaim ← putProof home (Ixon.Proof.ser { wrapped with claim })
    rejects home (args.set! 1 (toString badClaim)) "packet statement differs"
    let unknown := proof.set! 8 ((proof.get! 8) ^^^ 1)
    let unknownAddr ← putProof home (Ixon.Proof.ser { wrapped with proof := unknown })
    rejects home (args.set! 1 (toString unknownAddr)) "unrecognized production verifying key"
    for bad in [proof.set! 7 2, proof.set! (proof.size - 1) ((proof.get! (proof.size - 1)) ^^^ 1)] do
      let badAddr ← putProof home (Ixon.Proof.ser { wrapped with proof := bad })
      let result ← invoke home (args.set! 1 (toString badAddr))
      unless result.exitCode != 0 do throw <| IO.userError "modified compact proof accepted"

    let devPacket ← IO.FS.readBinFile (fixtures / "development-v5-packet.bin")
    let devProof := tag ++ devPacket
    let devWrapped : Ixon.Proof := { claim := expected, proof := devProof }
    let devAddr ← putProof home (Ixon.Proof.ser devWrapped)
    let devMetadata ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile
      (fixtures / "development-v5.json")))
    let expectedDevAddr ← IO.ofExcept (devMetadata.getObjValAs? String "compressed_proof_address")
    unless toString devAddr == expectedDevAddr do
      throw <| IO.userError "development proof address differs from its metadata"
    let devKey := home / "development-verifier.bin"
    let devKeyBytes ← IO.FS.readBinFile (fixtures / "development-v5-verifier.bin")
    IO.FS.writeBinFile devKey devKeyBytes
    let devFlags := #["--dev-srs", "--dev-vk", devKey.toString]
    let badKey := home / "invalid-verifier.bin"
    IO.FS.writeBinFile badKey "invalid".toUTF8
    rejects home #["verify", toString devAddr, "--dev-srs"] "development verifying key not found"
    let backend ← IO.ofExcept (← Aggr.buildVerificationBackend Aggr.defaultRecursionParameters)
    let cachedKey ← Ix.Cli.Compression.cacheDevelopmentKey devProof (Ix.Claim.ser expected)
      (Ix.Cli.Compression.statementBytes backend expected) devKeyBytes (some compressionRoot)
    let keyId ← IO.ofExcept (Ix.Cli.Compression.verifyingKeyId devProof)
    unless cachedKey == compressionRoot / "development/verifying-keys" / s!"{keyId}.bin" do
      throw <| IO.userError "development key cache is not indexed by key ID"
    for aggregateFlag in [#[], #["--aggregate"]] do
      let devArgs := #["verify", toString devAddr] ++ aggregateFlag
      rejects home devArgs "unrecognized production verifying key"
      rejects home (devArgs ++ #["--dev-vk", devKey.toString]) "--dev-srs"
      let accepted ← invoke home (devArgs.push "--dev-srs")
      unless accepted.exitCode == 0 && (accepted.stdout.splitOn "development proof").length > 1 do
        throw <| IO.userError s!"development proof failed: {accepted.stdout} {accepted.stderr}"
      unless (accepted.stdout.splitOn "aggregate backend setup").length > 1 do
        throw <| IO.userError "development verification did not derive its program from the backend"
    rejects home #["verify", toString devAddr, "--dev-srs", "--dev-vk",
      "crates/proof-compression/verifying-keys/aggregate-filecoin-v5.bin"] "setup class differs"
    rejects home (#["verify", toString compressedAddr] ++ devFlags) "packet verifying key mismatch"
    let invalidKey ← invoke home #["verify", toString devAddr, "--dev-srs", "--dev-vk", badKey.toString]
    unless invalidKey.exitCode != 0 do
      throw <| IO.userError "development verification accepted a malformed verifying key"
    IO.FS.writeBinFile cachedKey "invalid".toUTF8
    let corruptCache ← invoke home #["verify", toString devAddr, "--dev-srs"]
    unless corruptCache.exitCode != 0 do
      throw <| IO.userError "development verification accepted a corrupt cached key"
    let explicit ← invoke home (#["verify", toString devAddr] ++ devFlags)
    unless explicit.exitCode == 0 do
      throw <| IO.userError "explicit development key did not override the cache"
    let production ← invoke home args
    unless production.exitCode == 0 do
      throw <| IO.userError "production verification consulted the development key cache"
    IO.FS.removeFile cachedKey
    let external ← invoke home (#["verify", toString devAddr] ++ devFlags)
    unless external.exitCode == 0 do
      throw <| IO.userError "explicit development key required a cached key"
    rejects home (#["verify", toString old] ++ devFlags) "requires a compressed aggregate proof"
    rejects home (#["verify", "--aggregate", toString devAddr] ++ devFlags ++
      #["--ixe", "Tests/Fixtures/ixon-v4/handoff/accepted.ixe"]) "does not match expected"
    let badVersion ← putProof home (Ixon.Proof.ser
      { devWrapped with proof := devProof.set! 7 2 })
    rejects home (#["verify", toString badVersion] ++ devFlags) "unsupported compressed proof version"
    let badDevClaim ← putProof home (Ixon.Proof.ser { devWrapped with claim })
    rejects home (#["verify", toString badDevClaim] ++ devFlags) "packet statement differs"
    let badDevPrefix ← putProof home (Ixon.Proof.ser
      { devWrapped with proof := devProof.set! 40 ((devProof.get! 40) ^^^ 1) })
    rejects home (#["verify", toString badDevPrefix] ++ devFlags) "packet statement differs"
    for index in [8 + 32 + 18 * 8, devProof.size - 1] do
      let bad ← putProof home (Ixon.Proof.ser
        { devWrapped with proof := devProof.set! index ((devProof.get! index) ^^^ 1) })
      let result ← invoke home (#["verify", toString bad] ++ devFlags)
      unless result.exitCode != 0 do
        throw <| IO.userError "development opt-in accepted a modified proof"
    IO.println "compression CLI: production keys, development defaults, key overrides and claim binding passed"
  finally
    IO.FS.removeDirAll home

end Tests.CompressionCli
end
