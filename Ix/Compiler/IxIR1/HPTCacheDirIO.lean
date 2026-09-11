import Ix.Compiler.IxIR1.HPTCacheIO

/-!
# Indexed chunk-directory adapter for checked HPT caches

The single-file adapter streams framing but ultimately returns one in-memory
`Cache.Store`. This adapter uses the filesystem namespace as a content-key
index: each lookup key names one canonical singleton-store file. Directory
ingress retains only key, length, and rejection metadata, while the cache
scheduler opens at most the records selected by the current dependency chain.

Every selected payload remains untrusted and crosses `Cache.runLookupWithM`'s
ordinary record decoder, exact-query/content audits, local post-fixpoint check,
and final whole-program checker. Missing or malformed chunks are rebuilt and
published independently through `CacheIO.saveFileWith`, so a partial update is
safe and each successful replacement inherits the ledgered stable-storage
protocol. Recognizable orphan transaction directories are ignored.
-/

namespace Ix.Compiler.IxIR1.HPT.CacheDirIO

open System (FilePath)
open Ix.Compiler.IxIR
open Ix.Compiler.Ixon (Address)

/-- Independent controls for metadata-scale indexing and per-run lazy reads.
The embedded cache limits still bound every record, producer/checker work, and
new-record output. `maxIndexBytes` counts complete framed chunk files without
loading their payloads; `maxReadBytes` counts payloads selected in one run. -/
structure Limits where
  cache : Cache.Limits := {}
  maxIndexEntries : Nat := 1024 * 1024
  maxIndexBytes : Nat := 256 * 1024 * 1024 * 1024
  maxReadBytes : Nat := 64 * 1024 * 1024
  deriving BEq, Repr

def defaultLimits : Limits := {}

def recordFileSuffix : String := ".hpt"

def recordFileName (key : Address) : String :=
  key.toHex ++ recordFileSuffix

private def hexNibble? (byte : UInt8) : Option Nat :=
  let value := byte.toNat
  if 48 ≤ value && value ≤ 57 then some (value - 48)
  else if 97 ≤ value && value ≤ 102 then some (value - 87)
  else none

/-- Inverse of `recordFileName`; only the canonical lowercase 64-hex spelling
with the exact suffix is accepted. -/
def recordAddress? (name : String) : Option Address := do
  let input := name.toUTF8
  let suffix := recordFileSuffix.toUTF8
  if input.size != 64 + suffix.size then none
  else if input.extract 64 input.size != suffix then none
  else
    let mut output := ByteArray.empty
    for index in [:32] do
      let high ← hexNibble? input[2 * index]!
      let low ← hexNibble? input[2 * index + 1]!
      output := output.push (UInt8.ofNat (16 * high + low))
    Address.ofBytes? output

/-- An admitted header or a locally repairable malformed chunk. Complete file
bytes are retained for directory-budget accounting without retaining payloads. -/
inductive RecordMeta where
  | admitted (payloadBytes framedBytes : Nat)
  | rejected (reason : String) (framedBytes : Nat)
  deriving BEq, Repr

def RecordMeta.framedBytes : RecordMeta → Nat
  | .admitted _ bytes => bytes
  | .rejected _ bytes => bytes

/-- Metadata-only directory index. `ingress.bytes` is framed on-disk bytes for
this adapter (the in-memory adapter reports raw record payload bytes). -/
structure Index where
  directory : FilePath
  records : AddressEnv.Index RecordMeta
  ingress : Cache.IngressStats

private def enforce (label : String) (actual limit : Nat) :
    Except CacheIO.Error Unit :=
  if actual ≤ limit then .ok ()
  else .error (.cache s!"indexed HPT cache {label} budget exceeded: \
    {actual} > {limit}")

/-- Scan a cache directory into bounded metadata without retaining any record
payload. Malformed canonical-name chunks stay in the index as local
rejections; unknown names and non-regular record paths fail closed. -/
def indexDirectoryWith (limits : Limits) (directory : FilePath) :
    IO (Except CacheIO.Error Index) := do
  try
    let rootMetadata ← directory.symlinkMetadata
    if rootMetadata.type != .dir then
      return .error (.notDirectory directory.toString rootMetadata.type)
    let entries ← directory.readDir
    let mut records : Array (Address × RecordMeta) := #[]
    let mut count := 0
    let mut bytes := 0
    for entry in entries do
      let path := entry.path
      let metadata ← path.symlinkMetadata
      if CacheIO.isTransactionDirectoryName entry.fileName then
        if metadata.type != .dir then
          return .error (.notDirectory path.toString metadata.type)
      else
        let key ← match recordAddress? entry.fileName with
          | some key => pure key
          | none =>
              return .error (.cache s!"unexpected indexed HPT cache entry: \
                {path}")
        if metadata.type != .file then
          return .error (.notRegularFile path.toString metadata.type)
        count := count + 1
        match enforce "entry" count limits.maxIndexEntries with
        | .error error => return .error error
        | .ok () => pure ()
        let framedBytes := metadata.byteSize.toNat
        bytes := bytes + framedBytes
        match enforce "framed-byte" bytes limits.maxIndexBytes with
        | .error error => return .error error
        | .ok () => pure ()
        let recordMeta ← match ← CacheIO.inspectSingletonFileWith
            limits.cache path with
          | .error error => pure (.rejected error.describe framedBytes)
          | .ok header =>
              if header.key != key then
                pure (.rejected
                  "chunk header key does not match its canonical filename"
                  framedBytes)
              else
                pure (.admitted header.payloadBytes framedBytes)
        records := records.push (key, recordMeta)
    let index := AddressEnv.build records.toList
    if index.size != count then
      return .error (.cache "indexed HPT cache contains duplicate keys")
    return .ok ⟨directory, index, ⟨count, bytes⟩⟩
  catch error =>
    return .error (.io "index cache directory" directory.toString
      error.toString)

def indexDirectory (directory : FilePath) :
    IO (Except CacheIO.Error Index) :=
  indexDirectoryWith defaultLimits directory

private def transactionParent (path : FilePath) : FilePath :=
  path.parent.getD ("." : FilePath)

private def syncDirectory (path : FilePath) : IO (Except CacheIO.Error Unit) := do
  try
    Ix.Compiler.DurableSync.directory path
    return .ok ()
  catch error =>
    return .error (.io "durably sync directory" path.toString error.toString)

/-- Create exactly the requested cache directory under an existing parent and
persist its own metadata plus the new parent entry. -/
private def ensureDirectory (directory : FilePath) :
    IO (Except CacheIO.Error Unit) := do
  match ← directory.symlinkMetadata.toBaseIO with
  | .ok metadata =>
      if metadata.type == .dir then return .ok ()
      return .error (.notDirectory directory.toString metadata.type)
  | .error (.noFileOrDirectory ..) =>
      try
        IO.FS.createDir directory
      catch error =>
        return .error (.io "create cache directory" directory.toString
          error.toString)
      match ← syncDirectory directory with
      | .error error => return .error error
      | .ok () => syncDirectory (transactionParent directory)
  | .error error =>
      return .error (.io "inspect cache directory" directory.toString
        error.toString)

private def chargeRead (limits : Limits) (readBytes : IO.Ref Nat)
    (bytes : Nat) : ExceptT String IO Unit := do
  let prior ← readBytes.get
  if prior > limits.maxReadBytes || bytes > limits.maxReadBytes - prior then
    throw s!"indexed HPT cache read-byte budget exceeded: \
      {prior + bytes} > {limits.maxReadBytes}"
  readBytes.set (prior + bytes)

private def lookupRecord (limits : Limits) (index : Index)
    (readBytes : IO.Ref Nat) (key : Address) :
    ExceptT String IO Cache.LookupResult := do
  match index.records.get? key with
  | none => return .missing
  | some (.rejected reason _) => return .rejected reason
  | some (.admitted expectedBytes _) =>
      chargeRead limits readBytes expectedBytes
      let path := index.directory / recordFileName key
      match ← CacheIO.loadFileWith limits.cache path with
      | .error error => return .rejected error.describe
      | .ok store =>
          match store.entries with
          | [(storedKey, bytes)] =>
              if storedKey != key then
                return .rejected
                  "chunk payload key does not match its canonical filename"
              if bytes.size != expectedBytes then
                return .rejected
                  "chunk payload size changed after directory indexing"
              return .found bytes
          | entries =>
              return .rejected s!"indexed HPT cache chunk contains \
                {entries.length} records; expected 1"

private def projectedIndexWithinLimits (limits : Limits) (index : Index)
    (writes : List (Address × ByteArray)) : Except CacheIO.Error Unit := do
  let mut records := index.records
  let mut count := index.ingress.entries
  let mut bytes := index.ingress.bytes
  for write in writes do
    let framedBytes := (Cache.Store.mk [write]).framedSize
    match records.get? write.1 with
    | none => count := count + 1
    | some old => bytes := bytes - old.framedBytes
    bytes := bytes + framedBytes
    enforce "entry" count limits.maxIndexEntries
    enforce "framed-byte" bytes limits.maxIndexBytes
    records := records.insert write.1 (.admitted write.2.size framedBytes)

/-- Lazily schedule the current program against a metadata-only directory
index, then durably publish only rebuilt records. Independent per-key commits
make an interrupted multi-record refresh a safe mixture of old and new cache
entries; dependency-addressed queries and the final checker determine reuse. -/
def refreshDirectoryWith (limits : Limits)
    (program : List ReaddressAll.Artifact) (directory : FilePath) :
    IO (Except CacheIO.Error (Cache.Production limits.cache program)) := do
  match ← ensureDirectory directory with
  | .error error => return .error error
  | .ok () => pure ()
  let index ← match ← indexDirectoryWith limits directory with
    | .error error => return .error error
    | .ok index => pure index
  let readBytes ← IO.mkRef 0
  let scheduled ← (Cache.runLookupWithM limits.cache program index.ingress
    (lookupRecord limits index readBytes)).run
  let production ← match scheduled with
    | .error message => return .error (.cache message)
    | .ok production => pure production
  match projectedIndexWithinLimits limits index production.writes with
  | .error error => return .error error
  | .ok () => pure ()
  for write in production.writes do
    let path := directory / recordFileName write.1
    match ← CacheIO.saveFileWith limits.cache path ⟨[write]⟩ with
    | .error error => return .error error
    | .ok () => pure ()
  return .ok production

def refreshDirectory (program : List ReaddressAll.Artifact)
    (directory : FilePath) :
    IO (Except CacheIO.Error
      (Cache.Production defaultLimits.cache program)) :=
  refreshDirectoryWith defaultLimits program directory

end Ix.Compiler.IxIR1.HPT.CacheDirIO
