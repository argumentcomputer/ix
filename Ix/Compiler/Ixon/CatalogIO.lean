import Ix.Compiler.Ixon.Catalog

/-!
# Filesystem adapter for ix catalogs

`Catalog.loadWith` is deliberately a pure byte boundary.  This module adds the
small positional directory adapter needed by corpus tooling.  It parses the
manifest before resolving any member filenames, rejects non-regular files,
checks declared and observed sizes before each full-file read, and then hands
the exact bytes to the pure deep loader.

This remains an in-memory adapter.  A directory concurrently mutated between
metadata inspection and reading is still detected by the pure size/hash gate,
but avoiding the transient allocation in that race requires the future
streaming/mmap boundary.
-/

namespace Ix.Compiler.Ixon.CatalogIO

open System (FilePath)

inductive Error where
  | io (operation path message : String)
  | notRegularFile (path : String) (actual : IO.FS.FileType)
  | catalog (error : Catalog.Error)
  deriving Repr

structure PieceSpec where
  unit : Catalog.UnitRef
  filename : String
  expectedBytes : Nat
  deriving BEq, Repr

/-- Resolve the positional byte API into ix's exact on-disk filenames.  Member
labels have already passed `Catalog.decodeManifestWith`'s bare-name gate. -/
def pieceSpecs (manifest : Catalog.Manifest) : Array PieceSpec := Id.run do
  let mut specs := #[]
  match manifest.storage with
  | .fat rows =>
    for index in [:rows.size] do
      let row := rows[index]!
      let label := manifest.members[index]!.label
      specs := specs.push
        { unit := .fat index
          filename := s!"{label}.ixe"
          expectedBytes := row.fileBytes.toNat }
  | .chunked rows =>
    for index in [:rows.size] do
      let row := rows[index]!
      let label := manifest.members[row.owner.toNat]!.label
      specs := specs.push
        { unit := .chunk index row.owner.toNat
          filename := s!"{label}.chunk{index}.ixe"
          expectedBytes := row.fileBytes.toNat }
  return specs

private def resource (metric : Work.Metric) (actual limit : Nat) : Error :=
  .catalog (.resource ⟨metric, actual, limit⟩)

private def readManifest (limits : Catalog.Limits) (path : FilePath) :
    IO (Except Error ByteArray) := do
  try
    let metadata ← path.symlinkMetadata
    if metadata.type != .file then
      return .error (.notRegularFile path.toString metadata.type)
    let observed := metadata.byteSize.toNat
    if observed > limits.maxManifestBytes then
      return .error
        (resource .catalogManifestBytes observed limits.maxManifestBytes)
    let bytes ← IO.FS.readBinFile path
    if bytes.size > limits.maxManifestBytes then
      return .error
        (resource .catalogManifestBytes bytes.size limits.maxManifestBytes)
    return .ok bytes
  catch error =>
    return .error (.io "read manifest" path.toString error.toString)

private def readPiece (limits : Catalog.Limits) (directory : FilePath)
    (priorBytes : Nat) (spec : PieceSpec) :
    IO (Except Error ByteArray) := do
  let path := directory / spec.filename
  try
    let metadata ← path.symlinkMetadata
    if metadata.type != .file then
      return .error (.notRegularFile path.toString metadata.type)
    let observed := metadata.byteSize.toNat
    if observed != spec.expectedBytes then
      return .error
        (.catalog (.fileSize spec.unit observed spec.expectedBytes))
    let total := priorBytes + observed
    if total > limits.maxPieceBytes then
      return .error (resource .catalogPieceBytes total limits.maxPieceBytes)
    let bytes ← IO.FS.readBinFile path
    if bytes.size != spec.expectedBytes then
      return .error
        (.catalog (.fileSize spec.unit bytes.size spec.expectedBytes))
    let total := priorBytes + bytes.size
    if total > limits.maxPieceBytes then
      return .error (resource .catalogPieceBytes total limits.maxPieceBytes)
    return .ok bytes
  catch error =>
    return .error (.io "read storage unit" path.toString error.toString)

/-- Load and deeply validate one self-contained `.ixc` directory. -/
def loadDirWith (limits : Catalog.Limits) (directory : FilePath) :
    IO (Except Error Catalog.Loaded) := do
  let manifestPath := directory / "manifest"
  let manifestBytes ← match ← readManifest limits manifestPath with
    | .ok bytes => pure bytes
    | .error error => return .error error
  let manifest ← match Catalog.decodeManifestWith limits manifestBytes with
    | .ok manifest => pure manifest
    | .error error => return .error (.catalog error)
  let specs := pieceSpecs manifest
  let declaredBytes := specs.foldl
    (fun total spec => total + spec.expectedBytes) 0
  if declaredBytes > limits.maxPieceBytes then
    return .error
      (resource .catalogPieceBytes declaredBytes limits.maxPieceBytes)
  let mut bytes := #[]
  let mut priorBytes := 0
  for spec in specs do
    match ← readPiece limits directory priorBytes spec with
    | .error error => return .error error
    | .ok pieceBytes =>
      bytes := bytes.push pieceBytes
      priorBytes := priorBytes + pieceBytes.size
  return (Catalog.loadWith limits manifestBytes bytes).mapError Error.catalog

def loadDir (directory : FilePath) : IO (Except Error Catalog.Loaded) :=
  loadDirWith Catalog.defaultLimits directory

end Ix.Compiler.Ixon.CatalogIO
