module

public import Ix.Address

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

/-- `~/.ix/cache/<namespace>` holds wipeable, keyed indexes into the
content-addressed store. Unlike `storeDir`, filenames here are caller-defined
lookup keys and their contents must always be treated as untrusted hints. -/
def cacheDir (namespace' : String) : StoreIO FilePath := do
  let home ← getHomeDir
  let path := home / ".ix" / "cache" / namespace'
  if !(<- path.pathExists) then
    IO.toEIO .ioError (IO.FS.createDirAll path)
  return path

/-- Resolve an object path without creating directories. Read-only consumers
can use this before bounded reads, including when the address is missing. -/
def existingPath (addr : Address) : StoreIO FilePath := do
  let store := (← getHomeDir) / ".ix" / "store"
  let hex := hexOfBytes addr.hash
  let s := hex.toSlice
  let dir1 := (s.take 2).toString
  let dir2 := (s.drop 2 |>.take 2).toString
  let dir3 := (s.drop 4 |>.take 2).toString
  let file := (s.drop 6).toString
  return store / dir1 / dir2 / dir3 / file

def storePath (addr: Address): StoreIO FilePath := do
  let path ← existingPath addr
  let parent := path.parent.getD path
  if !(← parent.pathExists) then
    IO.toEIO .ioError (IO.FS.createDirAll parent)
  return path

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

def read (a: Address) : StoreIO ByteArray := do
  let path <- storePath a
  IO.toEIO .ioError (IO.FS.readBinFile path)

end Store

end
