module

public import Ix.Address
public import Ix.Address.Admission

public section

open System

inductive StoreError
| unknownAddress (a: Address)
| ioError (e: IO.Error)
| ixonError (e: String)
| noHome

def storeErrorToIOError : StoreError -> IO.Error
| .unknownAddress a => IO.Error.userError s!"unknown address {repr a}"
| .ioError e => e
| .ixonError e => IO.Error.userError s!"ixon error {e}"
| .noHome => IO.Error.userError s!"no HOME environment variable"

abbrev StoreIO := EIO StoreError

def StoreIO.toIO (sio: StoreIO α) : IO α :=
  EIO.toIO storeErrorToIOError sio

namespace Store

/-- Summary statistics of the process-wide `IxStore` (hot cache, memory-mapped
    `.ixpack` packfiles, and 1-level sharded loose objects). -/
structure StoreStats where
  hotEntries : UInt64
  packCount : UInt64
  packedObjects : UInt64
  packedBytes : UInt64
  looseObjects : UInt64
  looseBytes : UInt64
  deriving Repr, BEq, Inhabited

@[extern "rs_store_root"]
opaque rootDirFFI : IO String

@[extern "rs_store_contains"]
opaque containsFFI : @& Address → IO Bool

@[extern "rs_store_write"]
opaque writeFFI : @& ByteArray → IO Address

@[extern "rs_store_write_at"]
opaque writeAtFFI : @& Address → @& ByteArray → IO Unit

@[extern "rs_store_write_pack"]
opaque writePackFFI : @& Array (Address × ByteArray) → IO (Address × UInt64)

@[extern "rs_store_ingest_ixe"]
opaque ingestIxeFFI : @& String → IO (Address × UInt64)

@[extern "rs_store_read"]
opaque readFFI : @& Address → IO ByteArray

@[extern "rs_store_read_verified"]
opaque readVerifiedFFI : @& Address → IO ByteArray

@[extern "rs_store_compact"]
opaque compactFFI : IO (UInt64 × UInt64)

@[extern "rs_store_stats"]
opaque statsFFI : IO StoreStats

def getHomeDir : StoreIO FilePath := do
  match ← IO.getEnv "HOME" with
  | .some path => return ⟨path⟩
  | .none => throw .noHome

/-- Canonical store root (`$IX_STORE_DIR` or `~/.ix/store`). -/
def storeDir : StoreIO FilePath :=
  IO.toEIO .ioError (FilePath.mk <$> rootDirFFI)

/-- `~/.ix/cache/<namespace>` holds wipeable, keyed indexes into the
content-addressed store. Unlike `storeDir`, filenames here are caller-defined
lookup keys and their contents must always be treated as untrusted hints. -/
def cacheDir (namespace' : String) : StoreIO FilePath := do
  let home ← getHomeDir
  let path := home / ".ix" / "cache" / namespace'
  if !(<- path.pathExists) then
    IO.toEIO .ioError (IO.FS.createDirAll path)
  return path

/-- 1-level sharded loose object path: `<store>/objects/<aa>/<62-hex>`. -/
def storePath (addr: Address): StoreIO FilePath := do
  let store <- storeDir
  let hex := hexOfBytes addr.hash
  let s := hex.toSlice
  let dir1 := (s.take 2).toString
  let file := (s.drop 2).toString
  let path := store / "objects" / dir1
  if !(<- path.pathExists) then
    IO.toEIO .ioError (IO.FS.createDirAll path)
  return path / file

/-- Check whether `addr` is present in the hot cache, any `.ixpack`, or the
    loose object directory (`O(1)` in-memory or `stat()`). -/
def contains (addr : Address) : StoreIO Bool :=
  IO.toEIO .ioError (containsFFI addr)

/-- Hash `bytes` with `blake3`, short-circuit if already present in the hot
    cache, any `.ixpack`, or loose object shards, and otherwise atomically
    publish and cache the object. -/
def write (bytes: ByteArray) : StoreIO Address :=
  IO.toEIO .ioError (writeFFI bytes)

/-- Persist `bytes` keyed by an explicit caller-supplied address. Used
    for content whose canonical key isn't `blake3(bytes)` — e.g.
    `AssumptionTree` blobs that key by merkle root, not by their Ixon
    byte-serialization hash. Short-circuits if `addr` is already present. -/
def writeAt (addr: Address) (bytes: ByteArray) : StoreIO Unit :=
  IO.toEIO .ioError (writeAtFFI addr bytes)

/-- Write a batch of `(Address, ByteArray)` objects into a single immutable,
    memory-mapped `.ixpack` + `.ixidx` pair (2 fsyncs total regardless of
    object count). Returns `(packId, writtenObjectCount)`. -/
def writePack (entries : Array (Address × ByteArray)) : StoreIO (Address × UInt64) :=
  IO.toEIO .ioError (writePackFFI entries)

/-- Ingest a portable `.ixe` environment bundle (or a `.ixc/` catalog directory
    of `.ixe` member/chunk files) directly into `packs/` by hardlinking
    `env-<root>.ixe` (zero byte duplication) and generating a companion
    `env-<root>.ixidx` index over its §1 (`Blobs`) and §2 (`Constants`) windows.
    Returns `(envRoot, indexedObjectCount)`. -/
def ingestIxe (path : FilePath) : StoreIO (Address × UInt64) :=
  IO.toEIO .ioError (ingestIxeFFI path.toString)

/-- Read `addr` from the in-memory hot cache, a memory-mapped `.ixe`/`.ixpack`,
    or the 1-level loose object shard. -/
def read (a: Address) : StoreIO ByteArray :=
  IO.toEIO .ioError (readFFI a)

/-- Read `a` and verify `blake3(bytes) == a`. -/
def readVerified (a : Address) : StoreIO ByteArray :=
  IO.toEIO .ioError (readVerifiedFFI a)

/-- Compact all loose objects in `objects/<aa>/<62-hex>` into a single
    memory-mapped `.ixpack` + `.ixidx` and unlink the compacted loose files.
    Returns `(packedCount, unlinkedCount)`. -/
def compact : StoreIO (UInt64 × UInt64) :=
  IO.toEIO .ioError compactFFI

/-- Query statistics for the current store (`hotEntries`, `packCount`,
    `packedObjects`, `packedBytes`, `looseObjects`, `looseBytes`). -/
def stats : StoreIO StoreStats :=
  IO.toEIO .ioError statsFFI

end Store

end
