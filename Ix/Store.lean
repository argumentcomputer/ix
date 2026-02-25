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

def read (a: Address) : StoreIO ByteArray := do
  let path <- storePath a
  IO.toEIO .ioError (IO.FS.readBinFile path)

end Store

end
