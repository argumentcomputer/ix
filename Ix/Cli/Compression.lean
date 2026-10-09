module
public import Ix.Aggr.Backend
public import Ix.Aggr.Verification
public import Ix.Store

public section
namespace Ix.Cli.Compression

@[extern "rs_compression_setup"]
opaque setup (system : @& Aiur.AiurSystem) (dir srs : @& String)
    (devSrs : Bool) (rootLogHeight kzgLogHeight claimLen : UInt32) : IO String

@[extern "rs_compression_run"]
opaque compress (system : @& Aiur.AiurSystem) (allowed : @& ByteArray)
    (aggrIdx : @& Nat) (certificate proof : @& ByteArray) (dir : @& String) : IO ByteArray

@[extern "rs_compression_verify"]
opaque verify (rootVk proof : @& ByteArray) (claim : @& Array Aiur.G)
    (dir : @& String) : IO Unit

def directory : IO System.FilePath := do
  if let some path ← IO.getEnv "IX_COMPRESSION_HOME" then return path
  return (← StoreIO.toIO Store.getHomeDir) / ".ix/compression"

def requireSetup : IO System.FilePath := do
  let dir ← directory
  unless ← (dir / "default").pathExists do
    throw <| IO.userError "no active compression configuration; run `ix compression setup`"
  return dir

def isCompressed (proof : ByteArray) : Bool :=
  proof.extract 0 5 == "IXCMP".toUTF8

def readProof (addr : Address) : IO Ixon.Proof := do
  let bytes ← StoreIO.toIO (Store.read addr)
  IO.ofExcept (Aggr.decodeAggregateWrapperAt addr bytes)

end Ix.Cli.Compression
end
