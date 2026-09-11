import Ix.Compiler.IxIR1.HPTCache
import Ix.Compiler.DurableSync

/-!
# Filesystem adapter for checked HPT caches

The analysis/cache scheduler remains pure. This module persists its `Store` as
one versioned, canonically ordered file. Reads reject symlinks and non-regular
files, gate the observed byte count before allocation, and stream the strict
outer grammar one bounded record at a time. A missing file is an empty cache
only through the explicitly named `loadFileOrEmptyWith` entry.

Writes validate the aggregate store policy and canonicalize its outer framing
before touching the filesystem; record blobs deliberately remain untrusted
until a query consumes them. The adapter refuses an existing non-regular
destination, streams and verifies a fresh sibling staging file, flushes its
runtime buffer, requests stable storage for the staged file and transaction
directory, and commits with the runtime's POSIX-style atomic `rename`. It then
syncs both directories affected by that cross-directory rename. An interruption
before rename leaves the old cache intact; an orphan staging directory is never
considered by ingress. On the ledger's supported filesystem baseline, a
successful return makes the complete replacement power-loss durable. The small
native sync boundary and the storage device's reported guarantees remain
explicit trust assumptions.
-/

namespace Ix.Compiler.IxIR1.HPT.CacheIO

open System (FilePath)
open Ix.Compiler.IxIR

/-- Sibling transaction directories are deliberately recognizable so callers
can inspect crash leftovers without treating them as cache inputs. The adapter
removes only the directory created by its own invocation. -/
def transactionDirectoryPrefix : String := ".compilatrix-hpt-"

def transactionDirectorySuffix : String := ".txn"

def isTransactionDirectoryName (name : String) : Bool :=
  name.startsWith transactionDirectoryPrefix &&
    name.endsWith transactionDirectorySuffix

inductive Error where
  | io (operation path message : String)
  | notRegularFile (path : String) (actual : IO.FS.FileType)
  | notDirectory (path : String) (actual : IO.FS.FileType)
  | fileBytes (actual limit : Nat)
  | cache (message : String)
  deriving Repr

private abbrev ReadM := StateT Nat (ExceptT Error IO)

private partial def readExactLoop (handle : IO.FS.Handle) (label : String)
    (remaining : Nat) (acc : ByteArray) : ReadM ByteArray := do
  if remaining == 0 then
    return acc
  let request := min remaining 65536
  let chunk ← liftM (handle.read request.toUSize)
  if chunk.isEmpty then
    throw (.cache s!"truncated HPT cache {label}")
  let consumed ← get
  set (consumed + chunk.size)
  readExactLoop handle label (remaining - chunk.size) (acc ++ chunk)

/-- Read exactly one bounded grammar component. The caller's state is the
number of file bytes consumed, so a file that changes after the metadata gate
still cannot make this adapter allocate beyond `maxStoreBytes`. -/
private def readExact (handle : IO.FS.Handle) (limit : Nat) (label : String)
    (size : Nat) : ReadM ByteArray := do
  let consumed ← get
  if consumed > limit || size > limit - consumed then
    throw (.fileBytes (consumed + size) limit)
  readExactLoop handle label size .empty

private def expectBytes (handle : IO.FS.Handle) (limit : Nat)
    (label : String) (expected : ByteArray) : ReadM Unit := do
  let actual ← readExact handle limit label expected.size
  if actual != expected then
    throw (.cache s!"unexpected HPT cache {label}")

/-- Incremental canonical unsigned-LEB reader. Its width comes from the
largest policy value, and every contribution is checked before multiplication
can construct a value above that policy. -/
private def readNatBounded (handle : IO.FS.Handle) (storeLimit : Nat)
    (label : String) (limit : Nat) : ReadM Nat := do
  let width := (Encoding.nat limit).size
  let mut value := 0
  let mut multiplier := 1
  let mut spelling := ByteArray.empty
  for _ in [:width] do
    let bytes ← readExact handle storeLimit label 1
    let byte := bytes[0]!
    spelling := spelling ++ bytes
    let low := byte.toNat % 128
    if low > (limit - value) / multiplier then
      throw (.cache s!"HPT cache {label} value exceeds {limit}")
    value := value + low * multiplier
    if byte.toNat < 128 then
      if spelling != Encoding.nat value then
        throw (.cache s!"noncanonical HPT cache {label}")
      return value
    multiplier := multiplier * 128
  throw (.cache s!"HPT cache {label} numeral exceeds its bounded width")

private def readAddress (handle : IO.FS.Handle) (limit : Nat)
    (label : String) : ReadM Ixon.Address := do
  let bytes ← readExact handle limit label 32
  match Ixon.Address.ofBytes? bytes with
  | some address => return address
  | none => throw (.cache "internal: streamed address did not contain 32 bytes")

private def finishRead (handle : IO.FS.Handle) (path : FilePath)
    (observed limit : Nat) : ReadM Unit := do
  let extra ← liftM (handle.read 1)
  if !extra.isEmpty then
    let consumed ← get
    let actual := consumed + extra.size
    set actual
    if actual > limit then
      throw (.fileBytes actual limit)
    throw (.cache "trailing bytes after canonical HPT cache store")
  let consumed ← get
  if consumed != observed then
    throw (.io "read" path.toString
      s!"file size changed during ingress: observed {observed}, consumed {consumed}")

private def readStore (limits : Cache.Limits) (path : FilePath)
    (observed : Nat) (handle : IO.FS.Handle) : ReadM Cache.Store := do
  expectBytes handle limits.maxStoreBytes "store domain" Cache.storeDomain
  let count ← readNatBounded handle limits.maxStoreBytes
    "store-entry count" limits.maxEntries
  let mut entries : Array (Ixon.Address × ByteArray) := #[]
  let mut previous : Option Ixon.Address := none
  let mut totalBytes := 0
  for _ in [:count] do
    let key ← readAddress handle limits.maxStoreBytes "lookup key"
    match previous with
    | some prior =>
        if Ixon.Merkle.compareAddress prior key != .lt then
          throw (.cache "noncanonical HPT cache lookup-key order")
    | none => pure ()
    let size ← readNatBounded handle limits.maxStoreBytes
      "record-byte count" limits.maxEntryBytes
    totalBytes := totalBytes + size
    if totalBytes > limits.maxBytes then
      throw (.cache s!"HPT cache input-byte count exceeds {limits.maxBytes}")
    let bytes ← readExact handle limits.maxStoreBytes "record payload" size
    entries := entries.push (key, bytes)
    previous := some key
  finishRead handle path observed limits.maxStoreBytes
  let store : Cache.Store := ⟨entries.toList⟩
  match store.preflight limits with
  | .ok _ => return store
  | .error message => throw (.cache message)

/-- Metadata retained by the chunk-directory index. Inspecting a singleton
store reads only its fixed framing and bounded length numeral; the record
payload remains on disk until the checked scheduler asks for that key. -/
structure SingletonHeader where
  key : Ixon.Address
  payloadBytes : Nat
  deriving BEq, Repr

private def readSingletonHeader (limits : Cache.Limits) (_path : FilePath)
    (observed : Nat) (handle : IO.FS.Handle) : ReadM SingletonHeader := do
  expectBytes handle limits.maxStoreBytes "store domain" Cache.storeDomain
  let count ← readNatBounded handle limits.maxStoreBytes
    "store-entry count" limits.maxEntries
  if count != 1 then
    throw (.cache s!"indexed HPT cache chunk contains {count} records; expected 1")
  let key ← readAddress handle limits.maxStoreBytes "lookup key"
  let size ← readNatBounded handle limits.maxStoreBytes
    "record-byte count" limits.maxEntryBytes
  let consumed ← get
  if consumed + size != observed then
    throw (.cache s!"indexed HPT cache chunk declares {size} payload bytes, but \
      its framed file has {observed} bytes")
  return ⟨key, size⟩

private def readKnownFileWith (limits : Cache.Limits) (path : FilePath)
    (metadata : IO.FS.Metadata) : IO (Except Error Cache.Store) := do
  if metadata.type != .file then
    return .error (.notRegularFile path.toString metadata.type)
  let observed := metadata.byteSize.toNat
  if observed > limits.maxStoreBytes then
    return .error (.fileBytes observed limits.maxStoreBytes)
  try
    let handle ← IO.FS.Handle.mk path .read
    let result ← ((readStore limits path observed handle).run 0).run
    return result.map Prod.fst
  catch error =>
    return .error (.io "read" path.toString error.toString)

/-- Read one existing cache file through metadata, byte, framing, aggregate,
and duplicate-key gates. Missing files are errors at this entry point. -/
def loadFileWith (limits : Cache.Limits) (path : FilePath) :
    IO (Except Error Cache.Store) := do
  try
    let metadata ← path.symlinkMetadata
    readKnownFileWith limits path metadata
  catch error =>
    return .error (.io "inspect" path.toString error.toString)

def loadFile (path : FilePath) : IO (Except Error Cache.Store) :=
  loadFileWith Cache.defaultLimits path

/-- Inspect a canonical one-record store without reading its record payload.
The full file is re-opened and validated if the lazy scheduler later selects
the key, so a concurrent change cannot make this header an acceptance proof. -/
def inspectSingletonFileWith (limits : Cache.Limits) (path : FilePath) :
    IO (Except Error SingletonHeader) := do
  try
    let metadata ← path.symlinkMetadata
    if metadata.type != .file then
      return .error (.notRegularFile path.toString metadata.type)
    let observed := metadata.byteSize.toNat
    if observed > limits.maxStoreBytes then
      return .error (.fileBytes observed limits.maxStoreBytes)
    let handle ← IO.FS.Handle.mk path .read
    let result ← ((readSingletonHeader limits path observed handle).run 0).run
    return result.map Prod.fst
  catch error =>
    return .error (.io "inspect indexed chunk" path.toString error.toString)

def inspectSingletonFile (path : FilePath) :
    IO (Except Error SingletonHeader) :=
  inspectSingletonFileWith Cache.defaultLimits path

/-- Cold-start entry: only an absent path denotes an empty store. Existing
malformed, oversized, duplicate-key, symlink, and non-file inputs still fail. -/
def loadFileOrEmptyWith (limits : Cache.Limits) (path : FilePath) :
    IO (Except Error Cache.Store) := do
  match ← path.symlinkMetadata.toBaseIO with
  | .ok metadata => readKnownFileWith limits path metadata
  | .error (.noFileOrDirectory ..) => return .ok ⟨[]⟩
  | .error error =>
      return .error (.io "inspect" path.toString error.toString)

def loadFileOrEmpty (path : FilePath) : IO (Except Error Cache.Store) :=
  loadFileOrEmptyWith Cache.defaultLimits path

private def validateWriteTarget (path : FilePath) : IO (Except Error Unit) := do
  match ← path.symlinkMetadata.toBaseIO with
  | .ok metadata =>
      if metadata.type == .file then
        return .ok ()
      return .error (.notRegularFile path.toString metadata.type)
  | .error (.noFileOrDirectory ..) => return .ok ()
  | .error error =>
      return .error (.io "inspect output" path.toString error.toString)

def Error.describe : Error → String
  | .io operation path message => s!"{operation} {path}: {message}"
  | .notRegularFile path actual =>
      s!"{path} is not a regular file ({repr actual})"
  | .notDirectory path actual =>
      s!"{path} is not a directory ({repr actual})"
  | .fileBytes actual limit =>
      s!"HPT cache store-byte budget exceeded: {actual} > {limit}"
  | .cache message => message

private def verifyExpectedStore (limits : Cache.Limits) (path : FilePath)
    (observed : Nat) (handle : IO.FS.Handle)
    (expected : Cache.Store) : ReadM Unit := do
  expectBytes handle limits.maxStoreBytes "store domain" Cache.storeDomain
  let count ← readNatBounded handle limits.maxStoreBytes
    "store-entry count" limits.maxEntries
  if count != expected.entries.length then
    throw (.cache s!"staged store has {count} entries; expected \
      {expected.entries.length}")
  for entry in expected.entries do
    let key ← readAddress handle limits.maxStoreBytes "lookup key"
    if key != entry.1 then
      throw (.cache "staged HPT cache lookup key differs from canonical store")
    let size ← readNatBounded handle limits.maxStoreBytes
      "record-byte count" limits.maxEntryBytes
    if size != entry.2.size then
      throw (.cache s!"staged HPT cache record has {size} bytes; expected \
        {entry.2.size}")
    let bytes ← readExact handle limits.maxStoreBytes "record payload" size
    if bytes != entry.2 then
      throw (.cache "staged HPT cache record differs from canonical store")
  finishRead handle path observed limits.maxStoreBytes

/-- Verify the staging file against the expected canonical store while
retaining at most one newly read record payload. -/
private def verifyStreamedFile (limits : Cache.Limits) (operation : String)
    (path : FilePath) (expectedSize : Nat) (expected : Cache.Store) :
    IO (Except Error Unit) := do
  try
    let metadata ← path.symlinkMetadata
    if metadata.type != .file then
      return .error (.notRegularFile path.toString metadata.type)
    let observed := metadata.byteSize.toNat
    if observed != expectedSize then
      return .error (.io operation path.toString
        s!"observed {observed} bytes, expected {expectedSize}")
    if observed > limits.maxStoreBytes then
      return .error (.fileBytes observed limits.maxStoreBytes)
    let handle ← IO.FS.Handle.mk path .read
    match ← ((verifyExpectedStore limits path observed handle expected).run 0).run with
    | .ok _ => return .ok ()
    | .error error =>
        return .error (.io operation path.toString error.describe)
  catch error =>
    return .error (.io operation path.toString error.toString)

private def writeChunk (handle : IO.FS.Handle) (limit : Nat)
    (emitted : IO.Ref Nat) (bytes : ByteArray) : IO Unit := do
  let count ← emitted.get
  if count > limit || bytes.size > limit - count then
    throw <| IO.userError
      s!"HPT cache store-byte budget exceeded while writing: \
        {count + bytes.size} > {limit}"
  handle.write bytes
  emitted.set (count + bytes.size)

/-- Write the canonical outer grammar without constructing its concatenated
byte array. Record payloads already belong to the in-memory `Store`; adapter
scratch space is limited to the small framing chunks. -/
private def writeStore (limits : Cache.Limits) (handle : IO.FS.Handle)
    (store : Cache.Store) : IO Nat := do
  let emitted ← IO.mkRef 0
  writeChunk handle limits.maxStoreBytes emitted Cache.storeDomain
  writeChunk handle limits.maxStoreBytes emitted
    (Encoding.nat store.entries.length)
  for entry in store.entries do
    writeChunk handle limits.maxStoreBytes emitted entry.1.hash
    writeChunk handle limits.maxStoreBytes emitted (Encoding.nat entry.2.size)
    writeChunk handle limits.maxStoreBytes emitted entry.2
  let actual ← emitted.get
  let expected := store.framedSize
  if actual != expected then
    throw <| IO.userError
      s!"internal HPT cache framed-size mismatch: wrote {actual}, expected {expected}"
  return actual

private def transactionParent (path : FilePath) : FilePath :=
  path.parent.getD ("." : FilePath)

private def createTransactionDirectory (path : FilePath) :
    IO (Except Error FilePath) := do
  let parent := transactionParent path
  let rec loop : Nat → IO (Except Error FilePath)
    | 0 =>
        pure (.error (.io "create transaction directory" parent.toString
          "exhausted 32 collision-resistant sibling names"))
    | attempts + 1 => do
        let nonce ← IO.rand 0 (2 ^ 64 - 1)
        let candidate := parent /
          s!"{transactionDirectoryPrefix}{nonce}{transactionDirectorySuffix}"
        match ← (IO.FS.createDir candidate).toBaseIO with
        | .ok () => return .ok candidate
        | .error (.alreadyExists ..) => loop attempts
        | .error error =>
            return .error (.io "create transaction directory"
              candidate.toString error.toString)
  loop 32

private def cleanupTransaction (directory staged : FilePath) : IO Unit := do
  try IO.FS.removeFile staged catch _ => pure ()
  try IO.FS.removeDir directory catch _ => pure ()

private def syncFile (path : FilePath) : IO (Except Error Unit) := do
  try
    Ix.Compiler.DurableSync.file path
    return .ok ()
  catch error =>
    return .error (.io "durably sync file" path.toString error.toString)

private def syncDirectory (path : FilePath) : IO (Except Error Unit) := do
  try
    Ix.Compiler.DurableSync.directory path
    return .ok ()
  catch error =>
    return .error (.io "durably sync directory" path.toString error.toString)

private def replaceFileAtomically (limits : Cache.Limits) (path : FilePath)
    (store : Cache.Store) (expectedSize : Nat) : IO (Except Error Unit) := do
  let directory ← match ← createTransactionDirectory path with
    | .ok directory => pure directory
    | .error error => return .error error
  let staged := directory / "store"
  let result ← try
    let handle ← IO.FS.Handle.mk staged .write
    let actualSize ← writeStore limits handle store
    handle.flush
    if actualSize != expectedSize then
      pure (.error (.io "stage canonical store" staged.toString
        s!"wrote {actualSize} bytes, expected {expectedSize}"))
    else
      match ← (verifyStreamedFile limits "verify staged write" staged
          expectedSize store) with
      | .error error => pure (.error error)
      | .ok () =>
          match ← syncFile staged with
          | .error error => pure (.error error)
          | .ok () =>
              match ← syncDirectory directory with
              | .error error => pure (.error error)
              | .ok () =>
                  match ← validateWriteTarget path with
                  | .error error => pure (.error error)
                  | .ok () =>
                      IO.FS.rename staged path
                      let parent := transactionParent path
                      match ← syncDirectory parent with
                      | .error error => pure (.error error)
                      | .ok () => syncDirectory directory
  catch error =>
    pure (.error (.io "atomic replace" path.toString error.toString))
  match result with
  | .error error =>
      cleanupTransaction directory staged
      return .error error
  | .ok () =>
      -- A successful return guarantees both cleanup and persistence of that
      -- final parent-directory change. Failed attempts still leave only a
      -- recognizable orphan that cache ingress ignores.
      try
        IO.FS.removeDir directory
      catch error =>
        return .error (.io "remove committed transaction directory"
          directory.toString error.toString)
      syncDirectory (transactionParent path)

/-- Canonicalize and persist a complete store after its individual and
aggregate resource checks. Artifact records are checked on lookup, not blessed
by this writer.
The destination's parent directory must already exist. The commit is an atomic
rename within one filesystem: before it the prior destination remains intact,
and after it the complete staged bytes occupy the destination. A successful
return also includes the staged-file and affected-directory stable-storage
barriers required by the ledger's power-loss durability contract. -/
def saveFileWith (limits : Cache.Limits) (path : FilePath)
    (store : Cache.Store) : IO (Except Error Unit) := do
  let canonical ← match Cache.prepareStoreWith limits store with
    | .ok canonical => pure canonical
    | .error message => return .error (.cache message)
  let expectedSize := canonical.framedSize
  match ← validateWriteTarget path with
  | .error error => return .error error
  | .ok () => pure ()
  replaceFileAtomically limits path canonical expectedSize

def saveFile (path : FilePath) (store : Cache.Store) :
    IO (Except Error Unit) :=
  saveFileWith Cache.defaultLimits path store

/-- Load (or cold-start), validate/rebuild against the current program, merge
only the emitted writes, and persist the resulting store. The returned
`Production` still carries the ordinary whole-program checker equality. -/
def refreshFileWith (limits : Cache.Limits)
    (program : List ReaddressAll.Artifact) (path : FilePath) :
    IO (Except Error (Cache.Production limits program)) := do
  let store ← match ← loadFileOrEmptyWith limits path with
    | .ok store => pure store
    | .error error => return .error error
  let production ← match Cache.runWith limits program store with
    | .ok production => pure production
    | .error message => return .error (.cache message)
  let updated := store.applyWrites production.writes
  match ← saveFileWith limits path updated with
  | .ok () => return .ok production
  | .error error => return .error error

def refreshFile (program : List ReaddressAll.Artifact) (path : FilePath) :
    IO (Except Error (Cache.Production Cache.defaultLimits program)) :=
  refreshFileWith Cache.defaultLimits program path

end Ix.Compiler.IxIR1.HPT.CacheIO
