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

/-- Write `bytes` to `path` through a temporary name unique to this
    process and moment, then rename: a reader never sees a partial object,
    and concurrent writers of one object each move a complete copy into
    place. -/
private def publish (path : System.FilePath) (bytes : ByteArray) : IO Unit := do
  let pid ← IO.Process.getPID
  let stamp ← IO.monoNanosNow
  let tmp := System.FilePath.mk s!"{path}.tmp.{pid}.{stamp}"
  IO.FS.writeBinFile tmp bytes
  IO.FS.rename tmp path

def write (bytes: ByteArray) : StoreIO Address := do
  let addr  := Address.blake3 bytes
  let path <- storePath addr
  let _ <- IO.toEIO .ioError (publish path bytes)
  return addr

def read (a: Address) : StoreIO ByteArray := do
  let path <- storePath a
  IO.toEIO .ioError (IO.FS.readBinFile path)

/-- Write `bytes` under their BLAKE3 address, like every store object, and
    record `key → address` in the `~/.ix/cache/<namespace>` index. For
    objects referenced by another hash of their content, such as an
    assumption tree by its Merkle root. -/
def writeKeyed (namespace' : String) (key : Address) (bytes : ByteArray) :
    StoreIO Address := do
  let addr ← write bytes
  let index ← cacheDir namespace'
  IO.toEIO .ioError (publish (index / hexOfBytes key.hash) s!"{hexOfBytes addr.hash}\n".toUTF8)
  return addr

/-- Read an object recorded by `writeKeyed`. The index is only a hint:
    callers must check that the bytes have the requested `key`. -/
def readKeyed (namespace' : String) (key : Address) : StoreIO ByteArray := do
  let entry := (← cacheDir namespace') / hexOfBytes key.hash
  if !(← entry.pathExists) then throw (.unknownAddress key)
  let raw ← IO.toEIO .ioError (IO.FS.readFile entry)
  match Address.fromString raw.trimAscii.toString with
  | some addr => read addr
  | none => throw (.ixonError s!"malformed {namespace'} index entry for {hexOfBytes key.hash}")

end Store

end
