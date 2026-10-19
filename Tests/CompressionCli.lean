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
  for tag in ["IXCMP", "IXBN"] do
    unless Compression.isCompressed tag.toUTF8 do
      throw <| IO.userError s!"unrecognized compressed proof family: {tag}"
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
      throw <| IO.userError "bundled proof address differs from its metadata"
    let args := #["verify", toString compressedAddr]
    let out ← invoke home args
    unless out.exitCode == 0 && (out.stdout.splitOn "Filecoin").length > 1 do
      throw <| IO.userError s!"bundled Filecoin proof failed: {out.stdout} {out.stderr}"
    let aggregateArgs := #["verify", "--aggregate", toString compressedAddr]
    let aggregate ← invoke home aggregateArgs
    unless aggregate.exitCode == 0 && (aggregate.stdout.splitOn "Filecoin").length > 1 do
      throw <| IO.userError s!"bundled aggregate proof failed: {aggregate.stdout} {aggregate.stderr}"
    unless (aggregate.stdout.splitOn "aggregate backend setup").length == 1 do
      throw <| IO.userError "compressed aggregate verification constructed the native backend"
    rejects home (aggregateArgs ++ #["--ixe", "Tests/Fixtures/ixon-v4/handoff/accepted.ixe"])
      "does not match expected"
    unless !(← (home / ".ix/verifiers").pathExists) do
      throw <| IO.userError "verification created a filesystem verifier registry"

    -- A local registry cannot replace a verifier carried by the application.
    let alias := toString (Address.mk (packet.extract 0 32))
    let keys := home / ".ix/verifiers/filecoin/verifying-keys"
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
    rejects home (args.set! 1 (toString unknownAddr)) "not bundled with this application"
    for bad in [proof.set! 7 2, proof.set! (proof.size - 1) ((proof.get! (proof.size - 1)) ^^^ 1)] do
      let badAddr ← putProof home (Ixon.Proof.ser { wrapped with proof := bad })
      let result ← invoke home (args.set! 1 (toString badAddr))
      unless result.exitCode != 0 do throw <| IO.userError "modified compact proof accepted"

    let devPacket ← IO.FS.readBinFile (fixtures / "development-v5-packet.bin")
    let devProof := tag ++ devPacket
    let devWrapped : Ixon.Proof := { claim := expected, proof := devProof }
    let devAddr ← putProof home (Ixon.Proof.ser devWrapped)
    let devMetadata ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile
      "crates/proof-compression/verifying-keys/aggregate-development-v5.json"))
    let expectedDevAddr ← IO.ofExcept (devMetadata.getObjValAs? String "compressed_proof_address")
    unless toString devAddr == expectedDevAddr do
      throw <| IO.userError "bundled development proof address differs from its metadata"
    for aggregateFlag in [#[], #["--aggregate"]] do
      let devArgs := #["verify", toString devAddr] ++ aggregateFlag
      rejects home devArgs "--dev-srs"
      let accepted ← invoke home (devArgs.push "--dev-srs")
      unless accepted.exitCode == 0 && (accepted.stdout.splitOn "development proof").length > 1 do
        throw <| IO.userError s!"development proof failed: {accepted.stdout} {accepted.stderr}"
      unless (accepted.stdout.splitOn "aggregate backend setup").length == 1 do
        throw <| IO.userError "development verification constructed the native backend"
    let badDevClaim ← putProof home (Ixon.Proof.ser { devWrapped with claim })
    rejects home #["verify", toString badDevClaim, "--dev-srs"] "packet statement differs"
    let badDevPrefix ← putProof home (Ixon.Proof.ser
      { devWrapped with proof := devProof.set! 40 ((devProof.get! 40) ^^^ 1) })
    rejects home #["verify", toString badDevPrefix, "--dev-srs"] "packet statement differs"
    for index in [8 + 32 + 18 * 8, devProof.size - 1] do
      let bad ← putProof home (Ixon.Proof.ser
        { devWrapped with proof := devProof.set! index ((devProof.get! index) ^^^ 1) })
      let result ← invoke home #["verify", toString bad, "--dev-srs"]
      unless result.exitCode != 0 do
        throw <| IO.userError "development opt-in accepted a modified proof"
    IO.println "compression CLI: bundled proofs, claim binding and development opt-in passed"
  finally
    IO.FS.removeDirAll home

end Tests.CompressionCli
end
