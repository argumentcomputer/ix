module

public import Ix.Address

public section

open System

inductive StoreError
| unknownAddress (a: Address)
| ioError (e: IO.Error)
| ixonError (e: String)
| noHome
| corrupt (expected actual : Address)

def storeErrorToIOError : StoreError -> IO.Error
| .unknownAddress a => IO.Error.userError s!"unknown address {repr a}"
| .ioError e => e
| .ixonError e => IO.Error.userError s!"ixon error {e}"
| .noHome => IO.Error.userError s!"no HOME environment variable"
| .corrupt e a =>
  IO.Error.userError
    s!"store corruption: content stored under {repr e} hashes to {repr a}"

abbrev StoreIO := EIO StoreError

def StoreIO.toIO (sio: StoreIO α) : IO α :=
  EIO.toIO storeErrorToIOError sio

namespace Store

def getHomeDir : StoreIO FilePath := do
  match ← IO.getEnv "HOME" with
  | .some path => return ⟨path⟩
  | .none => throw .noHome

-- TODO: make this the default dir for the store, but customizable
def storeDir : StoreIO FilePath := do
  let home ← getHomeDir
  let path := home / ".ix" / "store"
  if !(<- path.pathExists) then
    IO.toEIO .ioError (IO.FS.createDirAll path)
  return path

def storePath (addr: Address): StoreIO FilePath := do
  let store <- storeDir
  let hex := hexOfBytes addr.hash
  let s := hex.toSlice
  let dir1 := (s.take 2).toString
  let dir2 := (s.drop 2 |>.take 2).toString
  let dir3 := (s.drop 4 |>.take 2).toString
  let file := (s.drop 6).toString
  let path := store / dir1 / dir2 / dir3
  if !(<- path.pathExists) then
    IO.toEIO .ioError (IO.FS.createDirAll path)
  return path / file

def write (bytes: ByteArray) : StoreIO Address := do
  let addr  := Address.blake3 bytes
  let path <- storePath addr
  let _ <- IO.toEIO .ioError (IO.FS.writeBinFile path bytes)
  return addr

/-- Persist `bytes` keyed by an explicit caller-supplied address. Used
    for content whose canonical key isn't `blake3(bytes)` — e.g.
    `AssumptionTree` blobs that key by merkle root, not by their Ixon
    byte-serialization hash. -/
def writeAt (addr: Address) (bytes: ByteArray) : StoreIO Unit := do
  let path <- storePath addr
  IO.toEIO .ioError (IO.FS.writeBinFile path bytes)

/-- Raw read with NO integrity check. Only appropriate for `writeAt`-keyed
    content whose key is not `blake3(bytes)` (e.g. assumption-tree blobs
    keyed by merkle root) — callers of those must verify against their
    domain-specific key. For `Store.write`-keyed content use
    `readVerified`. -/
def read (a: Address) : StoreIO ByteArray := do
  let path <- storePath a
  IO.toEIO .ioError (IO.FS.readBinFile path)

/-- Read a blob written by `Store.write` (keyed by `blake3(bytes)`),
    re-verifying the content hash. `~/.ix/store` is a plain directory with
    no integrity protection of its own, so an unverified read lets on-disk
    tampering feed the caller arbitrary bytes under a trusted address. -/
def readVerified (a: Address) : StoreIO ByteArray := do
  let bytes ← read a
  let actual := Address.blake3 bytes
  if actual == a then return bytes
  else throw (.corrupt a actual)

end Store

end
