import Ix.Compiler.Ixon.Merkle
import Ix.Compiler.Ixon.Sharing
import Ix.Compiler.AddressEnv

/-!
# Resource-bounded ix catalog ingress

An ix `.ixc` is a directory containing a binary `manifest` and either one
`<label>.ixe` per member (fat profile) or ordered
`<label>.chunkN.ixe` units (chunked profile).  Filesystem traversal is kept out
of this pure boundary: callers supply the manifest bytes and the piece bytes in
manifest order.

The loader mirrors ix's v1 manifest and the anonymous `.ixe` prefix.  It
performs deep verification unconditionally: fixed framing, file size/hash,
blob and constant hashes, checked v2 decoding, exact pinned-ix compressor
image and semantic addresses, piece/member/content Merkle roots,
profile-specific duplicate policy, and store-wide projection/member/
constructor coherence.  Metadata after `.ixe` section 3 is intentionally
opaque, exactly like ix's anonymous reader; it is not consulted by
Ix.Compiler's nameless pipeline.
-/

namespace Ix.Compiler.Ixon.Catalog

def magic : ByteArray :=
  String.toUTF8 "IXC" ++ ByteArray.mk #[0, 0, 0, 0, 0]

def version : UInt32 := 1
def flagChunked : UInt32 := 1
/-- Exact anonymous `.ixe` header carried by ix's `ixon-v2` environment. -/
def envFlag : UInt8 := 0xE
def envVersion : UInt64 := 2

structure Member where
  envRoot : Address
  constCount : UInt64
  label : String
  toolchain : String
  sourcePin : String
  deps : Array UInt32
  preimage : Option Address
  deriving BEq, Repr, Inhabited

structure FatPiece where
  fileHash : Address
  fileBytes : UInt64
  deriving BEq, Repr, Inhabited

structure Chunk where
  chunkRoot : Address
  fileHash : Address
  fileBytes : UInt64
  owner : UInt32
  deriving BEq, Repr, Inhabited

inductive Storage where
  | fat (pieces : Array FatPiece)
  | chunked (chunks : Array Chunk)
  deriving BEq, Repr

structure Manifest where
  membersRoot : Address
  contentRoot : Address
  members : Array Member
  storage : Storage
  /-- Future manifest sections are committed by the file bytes but opaque to
  this version, matching ix's forward-compatible manifest parser. -/
  trailing : ByteArray := .empty
  deriving BEq

/-- The identity of one piece in diagnostics and in the positional input API. -/
inductive UnitRef where
  | fat (member : Nat)
  | chunk (index owner : Nat)
  deriving BEq, DecidableEq, Repr

inductive ParseSource where
  | manifest
  | piece (unit : UnitRef)
  deriving BEq, DecidableEq, Repr

inductive MemberKind where
  | definition
  | inductive
  | recursor
  deriving BEq, DecidableEq, Repr

/-- Every failure at the catalog boundary is data-bearing.  Only low-level
canonical tag/EOF/UTF-8 diagnostics remain wrapped in `syntax`. -/
inductive Error where
  | syntax (source : ParseSource) (message : String)
  | resource (exceeded : Work.Exceeded)
  | badMagic
  | unsupportedVersion (actual expected : UInt32)
  | unknownFlags (flags : UInt32)
  | invalidLabel (member : Nat) (label : String)
  | dependencyOrder (member dependency : Nat)
  | invalidPreimageTag (member : Nat) (tag : UInt8)
  | membersRootMismatch (stored computed : Address)
  | pieceArity (expected actual : Nat)
  | fileSize (unit : UnitRef) (actual expected : Nat)
  | fileHash (unit : UnitRef) (actual expected : Address)
  | envHeader (unit : UnitRef) (flag : UInt8) (version : UInt64)
  | invalidMainTag (unit : UnitRef) (tag : UInt8)
  | unorderedAssumption (unit : UnitRef) (index : Nat)
  | blobHash (unit : UnitRef) (index : Nat)
      (stored computed : Address)
  | unorderedConstant (unit : UnitRef) (index : Nat)
  | constantHash (unit : UnitRef) (index : Nat)
      (stored computed : Address)
  | invalidConstant (unit : UnitRef) (address : Address)
      (error : DecodeCheck.Error)
  | unaddressableConstant (unit : UnitRef) (address : Address)
      (error : Constant.AddressError)
  | constantAddress (unit : UnitRef) (stored computed : Address)
  | mainMissing (unit : UnitRef) (main : Address)
  | hintCount (unit : UnitRef) (actual constants : Nat)
  | hintDelta (unit : UnitRef) (entry : Nat)
  | hintIndex (unit : UnitRef) (entry index constants : Nat)
  | hintValue (unit : UnitRef) (entry : Nat) (value : UInt64)
  | envRootMismatch (unit : UnitRef) (stored computed : Address)
  | fatMemberRoot (member : Nat) (stored computed : Address)
  | fatMemberCount (member : Nat) (stored : UInt64) (computed : Nat)
  | fatMemberAssumptions (member count : Nat)
  | chunkRoot (chunk : Nat) (stored computed : Address)
  | chunkMemberRoot (member : Nat) (stored computed : Address)
  | chunkMemberCount (member : Nat) (stored : UInt64) (computed : Nat)
  | duplicateChunkAddress (address : Address) (first second : Nat)
  | conflictingConstant (address : Address) (first second : Nat)
  | conflictingBlob (address : Address) (first second : Nat)
  | contentRootMismatch (stored computed : Address)
  | constructorOrdinal (block : Address) (member constructor : Nat)
      (actual : UInt64)
  | projectionBlockMissing (projection block : Address)
  | projectionBlockNotMutual (projection block : Address)
  | projectionMemberIndex (projection block : Address)
      (index bound : Nat)
  | projectionMemberKind (projection block : Address) (index : Nat)
      (expected actual : MemberKind)
  | projectionConstructorIndex (projection block : Address)
      (member constructor bound : Nat)
  deriving BEq, Repr

/-- Aggregate limits bound work over *all storage entries*, including repeated
fat-profile closure constants.  The final union has its own constant limit,
aligned by default with `Pipeline.Limits.maxConstants`. -/
structure Limits where
  ingress : DecodeCheck.Limits := {}
  sharing : Sharing.ResourceLimits := {}
  maxManifestBytes : Nat := 16 * 1024 * 1024
  maxMembers : Nat := 4096
  maxDependencyEdges : Nat := 64 * 1024
  maxStorageUnits : Nat := 16 * 1024
  maxPieceBytes : Nat := 1024 * 1024 * 1024
  maxConstantEntries : Nat := 32 * 1024
  maxConstantBytes : Nat := 1024 * 1024 * 1024
  maxBlobEntries : Nat := 32 * 1024
  maxBlobBytes : Nat := 1024 * 1024 * 1024
  maxAssumptions : Nat := 64 * 1024
  maxHints : Nat := 32 * 1024
  maxExpressionUnits : Nat := 2 * 1024 * 1024
  maxExpandedExpressionUnits : Nat := 2 * 1024 * 1024
  maxLayer1NodeVisits : Nat := 128 * 1024 * 1024
  maxUnionConstants : Nat := 16 * 1024
  deriving BEq, Repr

def defaultLimits : Limits := {}

structure Stats where
  manifestBytes : Nat := 0
  members : Nat := 0
  dependencyEdges : Nat := 0
  storageUnits : Nat := 0
  pieceBytes : Nat := 0
  constantEntries : Nat := 0
  constantBytes : Nat := 0
  blobEntries : Nat := 0
  blobBytes : Nat := 0
  assumptions : Nat := 0
  hints : Nat := 0
  expressionUnits : Nat := 0
  expandedExpressionUnits : Nat := 0
  layer1NodeVisits : Nat := 0
  unionConstants : Nat := 0
  deriving BEq, Repr

structure StoredConstant where
  address : Address
  bytes : ByteArray
  constant : Constant
  deriving BEq, Inhabited

structure StoredBlob where
  address : Address
  bytes : ByteArray
  deriving BEq, Inhabited

structure Piece where
  envRoot : Address
  main : Option Address
  assumptions : Array Address
  blobs : Array StoredBlob
  constants : Array StoredConstant
  /-- Sections 4-6, if present, are deliberately retained as opaque bytes. -/
  metadata : ByteArray
  deriving BEq, Inhabited

structure Loaded where
  manifest : Manifest
  pieces : Array Piece
  /-- Sorted, deduplicated semantic union used by the compiler pipeline. -/
  constants : List (Address × Constant)
  /-- Sorted raw blob union.  Literal interpretation remains a caller policy. -/
  blobs : List (Address × ByteArray)
  stats : Stats

private def enforce (metric : Work.Metric) (actual limit : Nat) :
    Except Error Unit :=
  match Work.ensure metric actual limit with
  | .ok _ => .ok ()
  | .error exceeded => .error (.resource exceeded)

/-! ## Exact manifest parser -/

private abbrev ParseM := StateT GetState (Except Error)

private def liftWire (source : ParseSource) (decoder : GetM α) : ParseM α :=
  fun state =>
    match decoder.run state with
    | .ok result => .ok result
    | .error message => .error (.syntax source message)

private def getBytesE (source : ParseSource) (count : Nat) : ParseM ByteArray :=
  liftWire source (getBytes count)

private def getU8E (source : ParseSource) : ParseM UInt8 :=
  liftWire source getU8

private def getTag0E (source : ParseSource) : ParseM UInt64 := do
  return (← liftWire source getTag0).size

private def getTag4E (source : ParseSource) : ParseM Tag4 :=
  liftWire source getTag4

private def getAddressE (source : ParseSource) : ParseM Address := do
  let bytes ← getBytesE source 32
  match Address.ofBytes? bytes with
  | some address => return address
  | none => throw (.syntax source "internal: address width")

private def getU16LE (source : ParseSource) : ParseM UInt16 := do
  let a ← getU8E source
  let b ← getU8E source
  return a.toUInt16 ||| (b.toUInt16 <<< 8)

private def getU32LE (source : ParseSource) : ParseM UInt32 := do
  let a ← getU8E source
  let b ← getU8E source
  let c ← getU8E source
  let d ← getU8E source
  return a.toUInt32 ||| (b.toUInt32 <<< 8) |||
    (c.toUInt32 <<< 16) ||| (d.toUInt32 <<< 24)

private def getU64LE (source : ParseSource) : ParseM UInt64 := do
  let lo ← getU32LE source
  let hi ← getU32LE source
  return lo.toUInt64 ||| (hi.toUInt64 <<< 32)

private def getString16 (source : ParseSource) : ParseM String := do
  let length ← getU16LE source
  let bytes ← getBytesE source length.toNat
  match String.fromUTF8? bytes with
  | some value => return value
  | none => throw (.syntax source "invalid UTF-8 string in .ixc")

def validLabel (label : String) : Bool :=
  !label.isEmpty && label != "." && label != ".." &&
    !label.any (fun character =>
      character == '/' || character == '\\' || character == '\x00')

def membersRootOf (members : Array Member) : Address :=
  Merkle.rootCanonical (members.map (·.envRoot))

private def parseMember (limits : Limits) (index : Nat)
    (dependencyTotal : Nat) : ParseM (Member × Nat) := do
  let source := ParseSource.manifest
  let envRoot ← getAddressE source
  let constCount ← getU64LE source
  let label ← getString16 source
  if !validLabel label then
    throw (.invalidLabel index label)
  let toolchain ← getString16 source
  let sourcePin ← getString16 source
  let dependencyCount := (← getU32LE source).toNat
  let nextDependencyTotal := dependencyTotal + dependencyCount
  match enforce .catalogDependencyEdges nextDependencyTotal
      limits.maxDependencyEdges with
  | .error error => throw error
  | .ok _ => pure ()
  let mut deps := #[]
  for _ in [:dependencyCount] do
    let dependency ← getU32LE source
    if dependency.toNat ≥ index then
      throw (.dependencyOrder index dependency.toNat)
    deps := deps.push dependency
  let preimageTag ← getU8E source
  let preimage ← match preimageTag with
    | 0 => pure none
    | 1 => some <$> getAddressE source
    | tag => throw (.invalidPreimageTag index tag)
  return (⟨envRoot, constCount, label, toolchain, sourcePin, deps,
    preimage⟩, nextDependencyTotal)

/-- Parse and structurally validate an ix v1 manifest, preserving future
trailing bytes. -/
def decodeManifestWith (limits : Limits) (bytes : ByteArray) :
    Except Error Manifest := do
  enforce .catalogManifestBytes bytes.size limits.maxManifestBytes
  let parser : ParseM (Manifest × Nat) := do
    let source := ParseSource.manifest
    let actualMagic ← getBytesE source 8
    if actualMagic != magic then throw .badMagic
    let actualVersion ← getU32LE source
    if actualVersion != version then
      throw (.unsupportedVersion actualVersion version)
    let flags ← getU32LE source
    if flags &&& (~~~flagChunked) != 0 then
      throw (.unknownFlags flags)
    let membersRoot ← getAddressE source
    let contentRoot ← getAddressE source
    let memberCount := (← getU32LE source).toNat
    match enforce .catalogMembers memberCount limits.maxMembers with
    | .error error => throw error
    | .ok _ => pure ()
    let mut members := #[]
    let mut dependencyTotal := 0
    for index in [:memberCount] do
      let (member, nextTotal) ← parseMember limits index dependencyTotal
      members := members.push member
      dependencyTotal := nextTotal
    let storage ←
      if flags &&& flagChunked == 0 then
        let mut pieces := #[]
        for _ in [:memberCount] do
          pieces := pieces.push
            { fileHash := (← getAddressE source)
              fileBytes := (← getU64LE source) }
        pure (.fat pieces)
      else
        let chunkCount := (← getU32LE source).toNat
        match enforce .catalogStorageUnits chunkCount
            limits.maxStorageUnits with
        | .error error => throw error
        | .ok _ => pure ()
        let mut chunks := #[]
        for chunkIndex in [:chunkCount] do
          let chunkRoot ← getAddressE source
          let fileHash ← getAddressE source
          let fileBytes ← getU64LE source
          let owner ← getU32LE source
          if owner.toNat ≥ memberCount then
            throw (.syntax source
              s!"chunk {chunkIndex} owner {owner} is out of range")
          chunks := chunks.push { chunkRoot, fileHash, fileBytes, owner }
        pure (.chunked chunks)
    let storageUnits := match storage with
      | .fat pieces => pieces.size
      | .chunked chunks => chunks.size
    match enforce .catalogStorageUnits storageUnits limits.maxStorageUnits with
    | .error error => throw error
    | .ok _ => pure ()
    let computedMembersRoot := membersRootOf members
    if computedMembersRoot != membersRoot then
      throw (.membersRootMismatch membersRoot computedMembersRoot)
    let consumed := (← get).idx
    return (⟨membersRoot, contentRoot, members, storage, .empty⟩, consumed)
  let (result, _) ← parser.run ⟨bytes, 0⟩
  let manifest := result.1
  let consumed := result.2
  return { manifest with trailing := bytes.extract consumed bytes.size }

def decodeManifest (bytes : ByteArray) : Except Error Manifest :=
  decodeManifestWith defaultLimits bytes

/-! ## Anonymous `.ixe` piece parser -/

private def cumulative (metric : Work.Metric) (prior delta limit : Nat) :
    Except Error Nat := do
  let actual := prior + delta
  enforce metric actual limit
  return actual

private def parsePieceWith (limits : Limits) (unit : UnitRef)
    (prior : Stats) (bytes : ByteArray) : Except Error (Piece × Stats) := do
  let source := ParseSource.piece unit
  let parser : ParseM (Piece × Stats) := do
    let tag ← getTag4E source
    if tag.flag != envFlag || tag.size != envVersion then
      throw (.envHeader unit tag.flag tag.size)
    let storedRoot ← getAddressE source
    let mainTag ← getU8E source
    let main ← match mainTag with
      | 0 => pure none
      | 1 => some <$> getAddressE source
      | tag => throw (.invalidMainTag unit tag)

    let assumptionCount := (← getTag0E source).toNat
    let totalAssumptions ← match cumulative .catalogAssumptions
        prior.assumptions assumptionCount limits.maxAssumptions with
      | .ok total => pure total
      | .error error => throw error
    let mut assumptions := #[]
    for index in [:assumptionCount] do
      let address ← getAddressE source
      if let some previous := assumptions.back? then
        if !Merkle.addressLT previous address then
          throw (.unorderedAssumption unit index)
      assumptions := assumptions.push address

    let blobCount := (← getTag0E source).toNat
    let totalBlobEntries ← match cumulative .catalogBlobEntries
        prior.blobEntries blobCount limits.maxBlobEntries with
      | .ok total => pure total
      | .error error => throw error
    let mut totalBlobBytes := prior.blobBytes
    let mut blobs := #[]
    for index in [:blobCount] do
      let address ← getAddressE source
      let length := (← getTag0E source).toNat
      totalBlobBytes ← match cumulative .catalogBlobBytes
          totalBlobBytes length limits.maxBlobBytes with
        | .ok total => pure total
        | .error error => throw error
      let payload ← getBytesE source length
      let computed := Address.blake3 payload
      if computed != address then
        throw (.blobHash unit index address computed)
      blobs := blobs.push ⟨address, payload⟩

    let constantCount := (← getTag0E source).toNat
    let totalConstantEntries ← match cumulative .catalogConstantEntries
        prior.constantEntries constantCount limits.maxConstantEntries with
      | .ok total => pure total
      | .error error => throw error
    let mut totalConstantBytes := prior.constantBytes
    let mut expressionUnits := prior.expressionUnits
    let mut expandedExpressionUnits := prior.expandedExpressionUnits
    let mut layer1NodeVisits := prior.layer1NodeVisits
    let mut constants := #[]
    for index in [:constantCount] do
      let address ← getAddressE source
      if let some previous := constants.back? then
        if !Merkle.addressLT previous.address address then
          throw (.unorderedConstant unit index)
      let length := (← getTag0E source).toNat
      totalConstantBytes ← match cumulative .catalogConstantBytes
          totalConstantBytes length limits.maxConstantBytes with
        | .ok total => pure total
        | .error error => throw error
      let payload ← getBytesE source length
      let computedRaw := Address.blake3 payload
      if computedRaw != address then
        throw (.constantHash unit index address computedRaw)
      let constant ← match DecodeCheck.decodeIxonV2CheckedWith limits.ingress payload with
        | .ok constant => pure constant
        | .error error => throw (.invalidConstant unit address error)
      let bodies := constant.info.exprs.toArray
      let objectExpressionUnits := Work.exprArrayUnits bodies +
        Work.exprArrayUnits constant.sharing
      let objectExpandedUnits :=
        (Work.expandedUnits? constant.sharing bodies).getD
          (Work.exprArrayUnits bodies)
      let objectLayer1 := Work.layer1NodeVisits constant.sharing bodies
      expressionUnits ← match cumulative .programExpressionUnits
          expressionUnits objectExpressionUnits limits.maxExpressionUnits with
        | .ok total => pure total
        | .error error => throw error
      expandedExpressionUnits ← match cumulative
          .programExpandedExpressionUnits expandedExpressionUnits
          objectExpandedUnits limits.maxExpandedExpressionUnits with
        | .ok total => pure total
        | .error error => throw error
      layer1NodeVisits ← match cumulative .layer1NodeVisits
          layer1NodeVisits objectLayer1 limits.maxLayer1NodeVisits with
        | .ok total => pure total
        | .error error => throw error
      let addressLimits : Constant.AddressLimits :=
        { ingress := limits.ingress, sharing := limits.sharing }
      let computedSemantic ← match constant.addressIxonV2CheckedWith
          addressLimits with
        | .ok computed => pure computed
        | .error error =>
          throw (.unaddressableConstant unit address error)
      if computedSemantic != address then
        throw (.constantAddress unit address computedSemantic)
      constants := constants.push ⟨address, payload, constant⟩

    if let some mainAddress := main then
      if !constants.any (fun stored => stored.address == mainAddress) then
        throw (.mainMissing unit mainAddress)

    let hintCount := (← getTag0E source).toNat
    if hintCount > constants.size then
      throw (.hintCount unit hintCount constants.size)
    let totalHints ← match cumulative .catalogHints prior.hints hintCount
        limits.maxHints with
      | .ok total => pure total
      | .error error => throw error
    let mut hintCursor := 0
    for entry in [:hintCount] do
      let delta := (← getTag0E source).toNat
      if delta == 0 then throw (.hintDelta unit entry)
      let index := hintCursor + delta - 1
      if index ≥ constants.size then
        throw (.hintIndex unit entry index constants.size)
      let value ← getTag0E source
      if value ≥ 2 && value - 2 > (4294967295 : UInt64) then
        throw (.hintValue unit entry value)
      hintCursor := index + 1

    let computedRoot := Merkle.rootCanonical
      (constants.map (·.address))
    if computedRoot != storedRoot then
      throw (.envRootMismatch unit storedRoot computedRoot)
    let consumed := (← get).idx
    let nextStats : Stats :=
      { prior with
        constantEntries := totalConstantEntries
        constantBytes := totalConstantBytes
        blobEntries := totalBlobEntries
        blobBytes := totalBlobBytes
        assumptions := totalAssumptions
        hints := totalHints
        expressionUnits
        expandedExpressionUnits
        layer1NodeVisits }
    return (⟨storedRoot, main, assumptions, blobs, constants,
      bytes.extract consumed bytes.size⟩, nextStats)
  let (result, _) ← parser.run ⟨bytes, 0⟩
  return result

/-! ## Store-wide coherence -/

private def kindOfMember : MutConst → MemberKind
  | .defn _ => .definition
  | .indc _ => .inductive
  | .recr _ => .recursor

private def checkMember (resolve : Address → Option Constant)
    (projection block : Address) (index : Nat) (expected : MemberKind) :
    Except Error MutConst := do
  let blockConstant ← match resolve block with
    | some constant => pure constant
    | none => throw (.projectionBlockMissing projection block)
  let members ← match blockConstant.info with
    | .muts members => pure members
    | _ => throw (.projectionBlockNotMutual projection block)
  let member ← match members[index]? with
    | some member => pure member
    | none => throw (.projectionMemberIndex projection block index members.size)
  let actual := kindOfMember member
  if actual != expected then
    throw (.projectionMemberKind projection block index expected actual)
  return member

/-- Validate invariants which cannot be checked while decoding one object:
constructor ordinals and projection targets in the complete store. -/
def validateStore (constants : List (Address × Constant)) : Except Error Unit := do
  let index := AddressEnv.build constants
  let resolve := AddressEnv.lookup index
  for (blockAddress, constant) in constants do
    match constant.info with
    | .muts members =>
      for memberIndex in [:members.size] do
        match members[memberIndex]! with
        | .indc ind =>
          for constructorIndex in [:ind.ctors.size] do
            let constructor := ind.ctors[constructorIndex]!
            if constructor.cidx.toNat != constructorIndex then
              throw (.constructorOrdinal blockAddress memberIndex
                constructorIndex constructor.cidx)
        | _ => pure ()
    | _ => pure ()
  for (projectionAddress, constant) in constants do
    match constant.info with
    | .iPrj projection =>
      let _ ← checkMember resolve projectionAddress projection.block
        projection.idx.toNat .inductive
      pure ()
    | .cPrj projection =>
      let member ← checkMember resolve projectionAddress projection.block
        projection.idx.toNat .inductive
      match member with
      | .indc ind =>
        if projection.cidx.toNat ≥ ind.ctors.size then
          throw (.projectionConstructorIndex projectionAddress
            projection.block projection.idx.toNat projection.cidx.toNat
            ind.ctors.size)
      | _ => pure ()
    | .rPrj projection =>
      let _ ← checkMember resolve projectionAddress projection.block
        projection.idx.toNat .recursor
      pure ()
    | .dPrj projection =>
      let _ ← checkMember resolve projectionAddress projection.block
        projection.idx.toNat .definition
      pure ()
    | _ => pure ()

private def sortedConstants (constants : Array StoredConstant) :
    Array StoredConstant :=
  constants.qsort fun left right =>
    Merkle.addressLT left.address right.address

private def sortedBlobs (blobs : Array StoredBlob) : Array StoredBlob :=
  blobs.qsort fun left right => Merkle.addressLT left.address right.address

private def storageUnits : Storage → Nat
  | .fat pieces => pieces.size
  | .chunked chunks => chunks.size

private def declaredPieceBytes : Storage → Nat
  | .fat pieces => pieces.foldl
      (fun total piece => total + piece.fileBytes.toNat) 0
  | .chunked chunks => chunks.foldl
      (fun total chunk => total + chunk.fileBytes.toNat) 0

/-- Deep-load a manifest and its positionally corresponding `.ixe` bytes.

For `.fat`, `pieceBytes[i]` is `<members[i].label>.ixe`.  For `.chunked`,
`pieceBytes[i]` is `<members[chunks[i].owner].label>.chunk<i>.ixe`.
-/
def loadWith (limits : Limits) (manifestBytes : ByteArray)
    (pieceBytes : Array ByteArray) : Except Error Loaded := do
  let manifest ← decodeManifestWith limits manifestBytes
  let expectedUnits := storageUnits manifest.storage
  if pieceBytes.size != expectedUnits then
    throw (.pieceArity expectedUnits pieceBytes.size)
  let declaredBytes := declaredPieceBytes manifest.storage
  enforce .catalogPieceBytes declaredBytes limits.maxPieceBytes
  let actualBytes := pieceBytes.foldl (fun total bytes => total + bytes.size) 0
  enforce .catalogPieceBytes actualBytes limits.maxPieceBytes
  let dependencyEdges := manifest.members.foldl
    (fun total member => total + member.deps.size) 0
  let mut stats : Stats :=
    { manifestBytes := manifestBytes.size
      members := manifest.members.size
      dependencyEdges
      storageUnits := expectedUnits
      pieceBytes := actualBytes }
  let mut parsedPieces : Array Piece := #[]
  match manifest.storage with
  | .fat rows =>
    for index in [:rows.size] do
      let unit := UnitRef.fat index
      let bytes := pieceBytes[index]!
      let row := rows[index]!
      if bytes.size != row.fileBytes.toNat then
        throw (.fileSize unit bytes.size row.fileBytes.toNat)
      let actualHash := Address.blake3 bytes
      if actualHash != row.fileHash then
        throw (.fileHash unit actualHash row.fileHash)
      let (piece, nextStats) ← parsePieceWith limits unit stats bytes
      let member := manifest.members[index]!
      if piece.envRoot != member.envRoot then
        throw (.fatMemberRoot index member.envRoot piece.envRoot)
      if piece.constants.size != member.constCount.toNat then
        throw (.fatMemberCount index member.constCount piece.constants.size)
      if !piece.assumptions.isEmpty then
        throw (.fatMemberAssumptions index piece.assumptions.size)
      parsedPieces := parsedPieces.push piece
      stats := nextStats
  | .chunked rows =>
    for index in [:rows.size] do
      let row := rows[index]!
      let unit := UnitRef.chunk index row.owner.toNat
      let bytes := pieceBytes[index]!
      if bytes.size != row.fileBytes.toNat then
        throw (.fileSize unit bytes.size row.fileBytes.toNat)
      let actualHash := Address.blake3 bytes
      if actualHash != row.fileHash then
        throw (.fileHash unit actualHash row.fileHash)
      let (piece, nextStats) ← parsePieceWith limits unit stats bytes
      if piece.envRoot != row.chunkRoot then
        throw (.chunkRoot index row.chunkRoot piece.envRoot)
      parsedPieces := parsedPieces.push piece
      stats := nextStats

  let chunked := match manifest.storage with
    | .fat _ => false
    | .chunked _ => true

  -- Disjointness is the first cross-piece invariant for the chunked profile.
  -- Check it before member coverage so a duplicate is always diagnosed as the
  -- profile violation, rather than incidentally as a member-count mismatch.
  if chunked then
    let mut seen : Std.HashMap Address Nat := {}
    for pieceIndex in [:parsedPieces.size] do
      for stored in parsedPieces[pieceIndex]!.constants do
        match seen.get? stored.address with
        | none => seen := seen.insert stored.address pieceIndex
        | some first =>
          throw (.duplicateChunkAddress stored.address first pieceIndex)

  -- Chunk rows are storage partitions; their owner-wise unions must recover
  -- each manifest member exactly, not merely the catalog-wide union.
  match manifest.storage with
  | .fat _ => pure ()
  | .chunked rows =>
    let mut ownerAddresses : Array (Array Address) :=
      Array.replicate manifest.members.size #[]
    for index in [:rows.size] do
      let owner := rows[index]!.owner.toNat
      let addresses := parsedPieces[index]!.constants.map (·.address)
      ownerAddresses := ownerAddresses.set! owner
        (ownerAddresses[owner]!.append addresses)
    for memberIndex in [:manifest.members.size] do
      let member := manifest.members[memberIndex]!
      let addresses := ownerAddresses[memberIndex]!
      let computedRoot := Merkle.rootCanonical addresses
      if computedRoot != member.envRoot then
        throw (.chunkMemberRoot memberIndex member.envRoot computedRoot)
      if addresses.size != member.constCount.toNat then
        throw (.chunkMemberCount memberIndex member.constCount addresses.size)

  let mut constantIndex : Std.HashMap Address (Nat × StoredConstant) := {}
  let mut unionConstants : Array StoredConstant := #[]
  let mut blobIndex : Std.HashMap Address (Nat × StoredBlob) := {}
  let mut unionBlobs : Array StoredBlob := #[]
  for pieceIndex in [:parsedPieces.size] do
    let piece := parsedPieces[pieceIndex]!
    for stored in piece.constants do
      match constantIndex.get? stored.address with
      | none =>
        constantIndex := constantIndex.insert stored.address
          (pieceIndex, stored)
        unionConstants := unionConstants.push stored
      | some (first, previous) =>
        if chunked then
          throw (.duplicateChunkAddress stored.address first pieceIndex)
        if previous.bytes != stored.bytes then
          throw (.conflictingConstant stored.address first pieceIndex)
    for stored in piece.blobs do
      match blobIndex.get? stored.address with
      | none =>
        blobIndex := blobIndex.insert stored.address (pieceIndex, stored)
        unionBlobs := unionBlobs.push stored
      | some (first, previous) =>
        if previous.bytes != stored.bytes then
          throw (.conflictingBlob stored.address first pieceIndex)

  enforce .programConstants unionConstants.size limits.maxUnionConstants
  let computedContentRoot := Merkle.rootCanonical
    (unionConstants.map (·.address))
  if computedContentRoot != manifest.contentRoot then
    throw (.contentRootMismatch manifest.contentRoot computedContentRoot)
  let constants := (sortedConstants unionConstants).toList.map
    (fun stored => (stored.address, stored.constant))
  validateStore constants
  let blobs := (sortedBlobs unionBlobs).toList.map
    (fun stored => (stored.address, stored.bytes))
  return Loaded.mk manifest parsedPieces constants blobs
    { stats with unionConstants := unionConstants.size }

def load (manifestBytes : ByteArray) (pieceBytes : Array ByteArray) :
    Except Error Loaded :=
  loadWith defaultLimits manifestBytes pieceBytes

end Ix.Compiler.Ixon.Catalog
