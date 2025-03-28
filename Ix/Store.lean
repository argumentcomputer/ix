import Ix.Address
import Ix.Ixon
import Ix.Ixon.Serialize

import Init.System.FilePath
import Init.System.IO
import Init.System.IOError

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

def getHomeDir : StoreIO FilePath := do
  match ← IO.getEnv "HOME" with
  | .some path => return ⟨path⟩
  | .none => throw .noHome

def storeDir : StoreIO FilePath := do
  let home ← getHomeDir
  return home / ".ix" / "store"

def ensureStoreDir : StoreIO Unit := do
  let store ← storeDir
  IO.toEIO .ioError (IO.FS.createDirAll store)

def writeConst (x: Ixon.Const) : StoreIO Address := do
  let bytes := Ixon.Serialize.put x
  let addr  := Address.blake3 bytes
  let store ← storeDir
  let path := store / hexOfBytes addr.hash
  let _ <- IO.toEIO .ioError (IO.FS.writeBinFile path bytes)
  return addr

def readConst (a: Address) : StoreIO Ixon.Const := do
  let store ← storeDir
  let path := store / hexOfBytes a.hash
  let bytes ← IO.toEIO .ioError (IO.FS.readBinFile path)
  match Ixon.Serialize.get bytes with
  | .ok c => return c
  | .error e => throw (.ixonError e)


