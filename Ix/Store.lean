import Ix.Address
import Ix.Ixon
import Ix.Ixon.Serialize

import Init.System.FilePath
import Init.System.IO
import Init.System.IOError

open System
open Ixon

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

def writeConst (x: Ixon) : StoreIO Address := do
  let bytes := runPut (Serialize.put x)
  let addr  := Address.blake3 bytes
  let store ← storeDir
  let path := store / hexOfBytes addr.hash
  -- trust that the store is correct
  if !(<- path.pathExists) then
    let _ <- IO.toEIO .ioError (IO.FS.writeBinFile path bytes)
  return addr

-- unsafe, can corrupt store if called with bad address
def forceWriteConst (addr: Address) (x: Ixon) : StoreIO Address := do
  let bytes := runPut (Serialize.put x)
  let store ← storeDir
  let path := store / hexOfBytes addr.hash
  let _ <- IO.toEIO .ioError (IO.FS.writeBinFile path bytes)
  return addr

def readConst (a: Address) : StoreIO Ixon := do
  let store ← storeDir
  let path := store / hexOfBytes a.hash
  let bytes ← IO.toEIO .ioError (IO.FS.readBinFile path)
  match runGet Serialize.get bytes with
  | .ok c => return c
  | .error e => throw (.ixonError e)

end Store
