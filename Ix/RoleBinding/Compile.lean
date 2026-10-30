module

public import Ix.RoleBinding.Generate
public import Ix.CompileResource
public import Ix.EnvScope
public import Ix.Meta
public import IxC.Kernel.PinGen.Certs

/-! Artifact-specific support and evidence for the production compiler.

The original request is compiled separately and retains its accounting and
failure policy. Support and certificate inputs use the same raw backend;
they never recursively enter this finalizer. Emission supplies untrusted
binding/evidence bytes. Certified consumers must check the resulting artifact.
-/

@[expose] public section

namespace Ix.RoleBinding.Compile

open Ix.Kernel (Role)

/-- A raw backend must report any incomplete internal compilation as an error.
The finalizer also checks every requested support/certificate publication. -/
abbrev Backend := Lean.Environment → Ix.Compile.CompileInput → IO Ixon.Env

def leanBackend (workers : Nat) (opts : Ix.CompileM.DriverOptions) : Backend := fun _ input => do
  let out ← IO.ofExcept (← Ix.CompileM.compileLeanInputValidated input (numWorkers := workers) (opts := opts))
  unless out.cenv.ungrounded.isEmpty && out.ungroundedCount == 0 do
    throw (IO.userError "artifact support: incomplete Lean compilation")
  return out.env

def rustBackend : Backend := fun _ input => IO.FS.withTempDir fun dir => do
  let path := dir / "support.ixe"
  let constants ← IO.ofExcept input.prepare
  let status ← Ix.CompileM.rsCompileEnvBytesFFI constants path.toString false
  unless status.ungrounded.isEmpty do
    throw (IO.userError "artifact support: incomplete Rust compilation")
  IO.ofExcept (Ixon.deEnv (← IO.FS.readBinFile path))

def roleName (role : Role) : Lean.Name :=
  Ix.RoleEvidence.toLeanName (Ix.Kernel.roleKey (md := .source) role)

def publishedRoles (artifact : Ixon.Env) : List Role :=
  let matched := (Ix.Compile.Parallel.map 32
    (fun (name, _) => Role.ofLeanName? (Ix.LeanIngress.ingressName name))
    artifact.named.toArray).filterMap id
  let found : Std.HashSet Role := matched.foldl (fun roles role => roles.insert role) {}
  Role.all.filter found.contains

def closeRoles (roles : List Role) : List Role :=
  Role.all.filter (roles ++ roles.flatMap Role.block ++ roles.flatMap Role.deps).contains

/-- Explicitly check mandatory sources before the selected-closure collector,
which intentionally ignores unavailable seed names in other callers. -/
def supportInput (source : Lean.Environment) (artifact : Ixon.Env)
    (published? : Option (List Role) := none) :
    Except String (List Role × Ix.Compile.CompileInput) := do
  let published := published?.getD (publishedRoles artifact)
  let mut required := closeRoles (Ix.Kernel.preludeShape.flatten ++ published)
  for _ in [:Role.all.length + 1] do
    let roots := required.map roleName
    for name in roots do
      unless source.contains name do throw s!"artifact support: source has no {name}"
    let constants := Ix.EnvScope.collectSelectedDeps source roots
    let found := constants.filterMap fun (name, _) => Role.ofLeanName? (Ix.Kernel.Name.ofLeanName name)
    let next := closeRoles (required ++ found)
    if next == required then
      let input ← (Ix.Compile.compileInputFromEnv source constants).mapError toString
      return (required, input)
    unless required.length < next.length do
      throw "artifact support: role closure failed to grow"
    required := next
  throw "artifact support: role closure exceeded its finite domain"

/-- Merge authenticated support without replacing any original publication or
its metadata. The support is authenticated here; the original is authenticated
with the merged artifact (`finalize`). Structural names, rather than stored name
hashes, decide overlap.
A reducibility hint the support carries at an address the original already
hints is refused when merging it would change the original's hint (the reader
checks a definition at the hint stored at its address, so a changed hint would
change how the original's definitions are checked); otherwise the original's
hint is kept. -/
def mergeSupport (limits : Ix.Kernel.Admission.Limits) (original support : Ixon.Env) :
    Except String Ixon.Env := do
  let _ ← recordStore limits support
  unless support.main.isNone && support.assumptions.isEmpty do
    throw "artifact support: internal compilation produced a bundle"
  let originalNames ← sourceAddresses original
  let _ ← sourceAddresses support
  let mut out := original
  for (address, value) in support.consts.toList do
    if let some old := out.consts[address]? then
      unless old.rawBytes == value.rawBytes do throw s!"artifact support: conflicting record {address}"
    else out := { out with consts := out.consts.insert address value }
  for (address, bytes) in support.blobs.toList do
    if let some old := out.blobs[address]? then
      unless old == bytes do throw s!"artifact support: conflicting blob {address}"
    else out := { out with blobs := out.blobs.insert address bytes }
  for (name, named) in support.named.toList do
    if let some old := originalNames[Ix.LeanIngress.ingressName name]? then
      unless old == named.addr do throw s!"artifact support: published address changed for {name.pretty}"
    else if out.named.contains name then
      throw s!"artifact support: stored name hash collision at {name.pretty}"
    else
      out := { out with named := out.named.insert name named }
  for (address, name) in support.names.toList do
    if let some old := out.names[address]? then
      unless Ix.LeanIngress.ingressName old == Ix.LeanIngress.ingressName name do
        throw s!"artifact support: conflicting name bytes at {address}"
    else out := { out with names := out.names.insert address name }
  for (address, commitment) in support.comms.toList do
    if let some old := out.comms[address]? then
      unless Ixon.serComm old == Ixon.serComm commitment do
        throw s!"artifact support: conflicting commitment {address}"
    else out := { out with comms := out.comms.insert address commitment }
  for (address, name) in support.addrToName.toList do
    unless out.addrToName.contains address do
      out := { out with addrToName := out.addrToName.insert address name }
  for (address, hint) in support.anonHints.toList do
    match out.anonHints[address]? with
    | some old =>
      unless Ixon.mergeHints old hint == old do
        throw s!"artifact support: the support's reducibility hint at {address} would change \
          the artifact's hint there"
    | none => out := { out with anonHints := out.anonHints.insert address hint }
  return out

/-- Whether stored bytes open with the TagN header of a standalone constant
(`CONST_DEFN`, `CONST_RECR`, `CONST_AXIO`, or `CONST_QUOT`). -/
def standaloneHeader (bytes : ByteArray) : Bool :=
  bytes.size ≥ 8 &&
  match (Ixon.getTagN 4).run { idx := 0, bytes } with
  | .ok tag _ =>
    tag.flag == Ixon.Constant.FLAG && tag.value ≤ Ixon.ConstantInfo.CONST_QUOT
  | .error _ _ => false

/-- Whether stored bytes open with the TagN header of a standalone definition or
definition projection (`CONST_DEFN` or `CONST_DPRJ`). -/
def definitionHeader (bytes : ByteArray) : Bool :=
  match (Ixon.getTagN 4).run { idx := 0, bytes } with
  | .ok tag _ =>
    tag.flag == Ixon.Constant.FLAG &&
      (tag.value == Ixon.ConstantInfo.CONST_DEFN || tag.value == Ixon.ConstantInfo.CONST_DPRJ)
  | .error _ _ => false

/-- Whether stored bytes open with the TagN header of a standalone recursor or
recursor projection (`CONST_RECR` or `CONST_RPRJ`). -/
def recursorHeader (bytes : ByteArray) : Bool :=
  match (Ixon.getTagN 4).run { idx := 0, bytes } with
  | .ok tag _ =>
    tag.flag == Ixon.Constant.FLAG &&
      (tag.value == Ixon.ConstantInfo.CONST_RECR || tag.value == Ixon.ConstantInfo.CONST_RPRJ)
  | .error _ _ => false

/-- Whether a record's info is an inductive, constructor or recursor member or
projection (a constant that can belong to an inductive family). -/
def isFamilyRecordInfo : Ixon.ConstantInfo → Bool
  | .iPrj _ | .cPrj _ | .recr _ | .rPrj _ => true
  | _ => false

/-- The first published name whose address holds no stored record, or whose
record header disagrees with its entry kind (a block record for a non-`Muts`
entry, or a non-block record for a `Muts` entry), if any. -/
def unreadablePublished (ixe : Ixon.Env) : Option Ix.Name :=
  (Ix.Cert.parMap (fun (n, named) =>
    match ixe.consts.get? named.addr with
    | some lc =>
      match named.constMeta.info with
      | .muts .. => if Ix.Cert.blockHeader lc.rawBytes then none else some n
      | _ => if Ix.Cert.blockHeader lc.rawBytes then some n else none
    | none => some n) ixe.named.toArray).findSome? id

/-- The first non-`Muts` published name whose address does not resolve to a
constant or constructor reference in the artifact's record store, if any. -/
def unresolvedPublished (ixe : Ixon.Env) : Option Ix.Name :=
  (Ix.Cert.parMap (fun (n, named) =>
    match named.constMeta.info with
    | .muts .. => none
    | _ =>
      match ixe.consts.get? named.addr with
      | some lc =>
        if lc.cache.isNone && standaloneHeader lc.rawBytes then none
        else if (Ix.Kernel.Reader.resolve (Ix.Cert.storedRecord ixe) named.addr).isSome then none
        else some n
      | none => some n) ixe.named.toArray).findSome? id

/-- The first published definition, theorem or opaque whose address has no
reducibility hint in `ixe.anonHints`, if any. -/
def unhintedDefinition (ixe : Ixon.Env) : Option Ix.Name :=
  (Ix.Cert.parMap (fun (n, named) =>
    match named.constMeta.info with
    | .muts .. => none
    | info =>
      let isDef := (match info with | .defn .. => true | _ => false) ||
        named.hints.isSome ||
        match ixe.consts.get? named.addr with
        | some lc => definitionHeader lc.rawBytes
        | none => false
      if isDef && !ixe.anonHints.contains named.addr then some n else none) ixe.named.toArray).findSome? id

/-- Fast block owner lookup for `unownedRecursorWith`: a standalone constant is
its own block without scanning its expressions; projections and blocks use
`Ix.Cert.recordBlock`. -/
def fastRecordBlock (ixe : Ixon.Env) (a : Address) : Address :=
  match ixe.consts.get? a with
  | some lc =>
    if lc.cache.isNone && standaloneHeader lc.rawBytes then a
    else Ix.Cert.recordBlock ixe a
  | none => a

/-- `unownedRecursor` given the artifact's stored recursor records
(`Ix.Cert.storedRecursorRecords ixe`), so callers that also run
`recursorSlotErrorWith` compute the recursor record array once. -/
def unownedRecursorWith (ixe : Ixon.Env)
    (recRecords : Array (Address × Ixon.Constant)) :
    Option (Address × Ix.Name × Option (Ix.Kernel.ConstRef Address)) :=
  let idx := Ix.Kernel.Reader.buildIndex (Ix.Cert.storedRecord ixe) recRecords
  if idx.blocks.isEmpty then none
  else
    let publishedRecBlocks : Std.HashSet Address :=
      (Ix.Cert.parMap (fun (n, named) =>
        match ixe.consts.get? named.addr with
        | some lc =>
          if recursorHeader lc.rawBytes && (Ix.Cert.publishedRecursor? ixe n).isSome then
            Ix.Cert.publishedRecords ixe n
          else []
        | none => []) ixe.named.toArray).foldl
        (fun acc as => as.foldl (fun s a => s.insert a) acc) {}
    (Ix.Cert.parMap (fun (x, named) =>
      match named.constMeta.info with
      | .muts .. => none
      | _ =>
        let b := fastRecordBlock ixe named.addr
        match idx.blocks[b]? with
        | none => none
        | some shape =>
          match Ix.Cert.storedRecord ixe named.addr with
          | some c =>
            if isFamilyRecordInfo c.info then
              (shape.recs.find? fun r => !publishedRecBlocks.contains r.block).map fun r =>
                (b, x, some r)
            else some (b, x, none)
          | none => some (b, x, none)) ixe.named.toArray).findSome? id

/-- An inductive block the recursor index (`Ix.Kernel.Reader.buildIndex`)
attaches recursors to and a non-`Muts` name published in that block whose stored
record is not an inductive, constructor or recursor, or with an indexed recursor
attached there whose block is not published at a recursor in `ixe.named`, if any. -/
def unownedRecursor (ixe : Ixon.Env) :
    Option (Address × Ix.Name × Option (Ix.Kernel.ConstRef Address)) :=
  unownedRecursorWith ixe (Ix.Cert.storedRecursorRecords ixe)

/-- A literal-support role of the default role table (`Ix.Cert.roleTableBound`)
that a stored record's literal is checked against (`Ix.Cert.storedLiteralRoles`),
at whose address the artifact stores a record while the role's name
(`Ix.Cert.literalRoleIxName`) is not published at that address, if any. -/
def literalRoleUnnamed (ixe : Ixon.Env) : Option (Ix.Kernel.Role × Address) :=
  let unnamed := Ix.Cert.roleTableBound.toList.filter fun (s, b) =>
    Ix.Cert.literalSupportRoles.contains s && ixe.consts.contains b &&
      (ixe.named.get? (Ix.Cert.literalRoleIxName s)).map (·.addr) != some b
  if unnamed.isEmpty then none
  else
    let roles := Ix.Cert.storedLiteralRoles ixe
    unnamed.find? fun (s, _) => roles.contains s

/-- Check structural name uniqueness (`Ix.Cert.PublishedAgree`) and, when the
artifact carries a role binding, that the binding admits canonically, every
published role name is bound at its role's address (`Ix.Cert.PublishedRolesBound`),
every bound role's stored record has its role's kind (`Ix.Cert.RoleRecordKinds`),
and every stored literal-support role used by literals is published at its bound
address. -/
def roleBindingError (ixe : Ixon.Env) : Option String :=
  match sourceAddresses ixe with
  | .error e => some e
  | .ok _ =>
    match ixe.roleBinding with
    | none => none
    | some binding =>
      match Ix.Kernel.Admission.admitBinding Address.admissionHash ⟨binding.address, binding.bytes⟩ with
      | .error e => some (toString (Ix.Kernel.Admission.Error.binding e))
      | .ok table =>
        let roleMismatch := (Ix.Cert.parMap (fun (n, named) =>
          match Role.ofLeanName? (Ix.LeanIngress.ingressName n) with
          | some r =>
            if table.addressOf? r == some named.addr then none
            else some s!"the published role {n.pretty} ({repr r}) is at {named.addr}, not its bound address"
          | none => none) ixe.named.toArray).findSome? id
        if let some msg := roleMismatch then some msg
        else
          let kindMismatch := table.bound.toList.findSome? fun (r, p) =>
            match (ixe.consts.get? p).bind (·.get?) with
            | some c =>
              if Ix.Cert.roleRecordKindOk r c then none
              else some s!"the record at {p}, the bound address of {repr r}, is not of its role's kind"
            | none => some s!"the bound address {p} of {repr r} holds no readable record"
          if let some msg := kindMismatch then some msg
          else
            let unnamed := table.bound.toList.filter fun (s, b) =>
              Ix.Cert.literalSupportRoles.contains s && ixe.consts.contains b &&
                (ixe.named.get? (Ix.Cert.literalRoleIxName s)).map (·.addr) != some b
            if unnamed.isEmpty then none
            else
              let roles := Ix.Cert.storedLiteralRoles ixe
              match unnamed.find? fun (s, _) => roles.contains s with
              | some (s, b) =>
                some s!"the bound address {b} of the literal-support role {repr s} is not published under {(Ix.Cert.literalRoleIxName s).pretty}"
              | none => none

/-- **The finalized artifact keeps the original's artifact-level checks.**
`finalize` adds support records, certificate records, evidence records and a
binding after the compile's checks (`Ix.Cert.checkReport`) ran on `original`.
This runs again, on the finalized artifact `final`, every check of
`checkReport` that reads the artifact, checks that the original's publications
and hints are unchanged, and checks the emitted role binding against `final`:

* every name `original` publishes is published at the same address, and every
  reducibility hint `original` stores is stored unchanged;
* every record and blob is stored at the admission hash of its bytes
  (`Ix.Cert.unauthentic`);
* no record is on a reference cycle (`Ix.Cert.referenceCycle`);
* no two published names share a stored hash (`Ix.Cert.nameHashCollision`);
* every `Muts` entry agrees with its block's projections (`Ix.Cert.mutsMismatch`);
* every non-`Muts` published name resolves in the record store
  (`unresolvedPublished`);
* no member has two stored definition projection records
  (`Ix.Cert.projectionCollision`);
* every published name points to a readable record of its entry's kind
  (`unreadablePublished`);
* no address holds both a blob and a record (`Ix.Cert.blobRecordCollision`);
* every inductive block with indexed recursors has only family records published
  in it and has its indexed recursors published (`unownedRecursor`);
* the record at an address the default role table binds has its role's kind
  (`Ix.Cert.roleRecordKind`), and any stored literal-support role used by
  literals is published under its name (`literalRoleUnnamed`);
* every stored recursor member is filed at a slot of its own
  (`Ix.Cert.recursorSlotError`);
* every published definition, theorem or opaque has a reducibility hint at its
  address (`unhintedDefinition`);
* no two published names share a structural spelling, and the emitted role
  binding admits and agrees with `final`'s published roles and records
  (`roleBindingError`). -/
structure FinalizedCheckTasks where
  unauthentic : Task (List Address)
  referenceCycle : Task (Option (List Address))
  nameHashCollision : Task (Option (Ix.Name × Ix.Name))
  mutsMismatch : Task (Option (Ix.Name × Nat × Address))
  unresolvedPublished : Task (Option Ix.Name)
  projectionCollision : Task (Option (Address × Nat))
  unreadablePublished : Task (Option Ix.Name)
  blobRecordCollision : Task (Option Address)
  unownedRecursor : Task (Option (Address × Ix.Name × Option (Ix.Kernel.ConstRef Address)))
  roleRecordKind : Task (Option (Ix.Kernel.Role × Address))
  literalRoleUnnamed : Task (Option (Ix.Kernel.Role × Address))
  recursorSlotError : Task (Option Ix.Cert.RecursorShapeError)
  unhintedDefinition : Task (Option Ix.Name)
  roleBindingError : Task (Option String)

def FinalizedCheckTasks.spawn (final : Ixon.Env) : FinalizedCheckTasks :=
  let recRecords := Task.spawn fun _ => Ix.Cert.storedRecursorRecords final
  { unauthentic := Task.spawn fun _ => Ix.Cert.unauthenticPar final
    referenceCycle := Task.spawn fun _ => Ix.Cert.referenceCycle final
    nameHashCollision := Task.spawn fun _ => Ix.Cert.nameHashCollision { consts := {} } final
    mutsMismatch := Task.spawn fun _ => Ix.Cert.mutsMismatch final
    unresolvedPublished := Task.spawn fun _ => Ix.RoleBinding.Compile.unresolvedPublished final
    projectionCollision := Task.spawn fun _ => Ix.Cert.projectionCollision final
    unreadablePublished := Task.spawn fun _ => Ix.RoleBinding.Compile.unreadablePublished final
    blobRecordCollision := Task.spawn fun _ => Ix.Cert.blobRecordCollision final
    unownedRecursor := Task.spawn fun _ =>
      Ix.RoleBinding.Compile.unownedRecursorWith final recRecords.get
    roleRecordKind := Task.spawn fun _ => Ix.Cert.roleRecordKind final
    literalRoleUnnamed := Task.spawn fun _ => Ix.RoleBinding.Compile.literalRoleUnnamed final
    recursorSlotError := Task.spawn fun _ =>
      Ix.Cert.recursorSlotErrorWith final recRecords.get
    unhintedDefinition := Task.spawn fun _ => Ix.RoleBinding.Compile.unhintedDefinition final
    roleBindingError := Task.spawn fun _ => Ix.RoleBinding.Compile.roleBindingError final }

@[noinline] def checkFinalizedOf (ts : FinalizedCheckTasks) : Except String Unit := do
  if let some a := ts.unauthentic.get.head? then
    throw s!"artifact finalization: the record or blob at {a} is not stored at the hash of its bytes"
  if let some cycle := ts.referenceCycle.get then
    throw s!"artifact finalization: the records {cycle.take 4} are on a reference cycle"
  if let some (n, m) := ts.nameHashCollision.get then
    throw s!"artifact finalization: the published names {n.pretty} and {m.pretty} share a stored hash"
  if let some (entry, i, _) := ts.mutsMismatch.get then
    throw s!"artifact finalization: class {i} of the Muts entry {entry.pretty} lists a name not \
      published at its member's projection"
  if let some n := ts.unresolvedPublished.get then
    throw s!"artifact finalization: the published name {n.pretty} does not resolve in the record store"
  if let some (block, i) := ts.projectionCollision.get then
    throw s!"artifact finalization: member {i} of the block at {block} has more than one stored \
      definition projection record"
  if let some n := ts.unreadablePublished.get then
    throw s!"artifact finalization: the published name {n.pretty} is at an address with no readable \
      record of its entry's kind"
  if let some a := ts.blobRecordCollision.get then
    throw s!"artifact finalization: the address {a} holds both a stored blob and a stored record"
  if let some (b, x, r?) := ts.unownedRecursor.get then
    match r? with
    | none =>
      throw s!"artifact finalization: the published name {x.pretty} in the inductive block at {b} \
        is not an inductive, constructor or recursor"
    | some r =>
      throw s!"artifact finalization: the recursor at {r.block}, indexed under the inductive block \
        at {b} for {x.pretty}, is not published"
  if let some (role, address) := ts.roleRecordKind.get then
    throw s!"artifact finalization: the record at {address}, the default role table's address of \
      {repr role}, is not of its role's kind"
  if let some (role, address) := ts.literalRoleUnnamed.get then
    throw s!"artifact finalization: the record at {address}, the default role table's address of \
      the literal-support role {repr role}, is not published under {(Ix.Cert.literalRoleIxName role).pretty}"
  if let some e := ts.recursorSlotError.get then
    throw s!"artifact finalization: {e.message}"
  if let some n := ts.unhintedDefinition.get then
    throw s!"artifact finalization: the published definition {n.pretty} has no reducibility hint \
      at its address"
  if let some msg := ts.roleBindingError.get then
    throw s!"artifact finalization: {msg}"

def checkFinalized (original final : Ixon.Env) : Except String Unit := do
  let tasks := FinalizedCheckTasks.spawn final
  if let some name := (Ix.Cert.parMap (fun (name, named) =>
      if (final.named.get? name).map (·.addr) == some named.addr then none else some name)
      original.named.toArray).findSome? id then
    throw s!"artifact finalization: the published address of {name.pretty} changed"
  if let some address := (Ix.Cert.parMap (fun (address, hint) =>
      if final.anonHints[address]? == some hint then none else some address)
      original.anonHints.toArray).findSome? id then
    throw s!"artifact finalization: the reducibility hint at {address} changed"
  checkFinalizedOf tasks

/-- Adding internal support cannot hide a failed original request, change an
original address, or replace its source contract input. -/
def preserveRequestedWith (input : Ix.Compile.CompileInput)
    (old current : Std.HashMap Ix.Kernel.Name Address) : Except String Unit := do
  for (name, _) in input.constants do
    let key := Ix.Kernel.Name.ofLeanName name
    unless old[key]? == current[key]? do
      throw s!"artifact support: changed original publication/failure for {name}"

def preserveRequested (input : Ix.Compile.CompileInput) (before after : Ixon.Env) :
    Except String Unit := do
  let old ← sourceAddresses before
  let current ← sourceAddresses after
  preserveRequestedWith input old current

def compileRequired (backend : Backend) (source : Lean.Environment)
    (input : Ix.Compile.CompileInput) : IO Ixon.Env := do
  let out ← backend source input
  let published ← IO.ofExcept (sourceAddresses out)
  for (name, _) in input.constants do
    unless published.contains (Ix.Kernel.Name.ofLeanName name) do
      throw (IO.userError s!"artifact support: internal compilation did not publish {name}")
  return out

initialize cachedNativeCertSource : IO.Ref (Option Lean.Environment) ← IO.mkRef none

/-- The certificate theorems of the toolchain ix runs on: its own
`IxC.Kernel.PinGen.Certs`, elaborated against its own `Init`. -/
def nativeCertSource : IO Lean.Environment := do
  if let some env ← cachedNativeCertSource.get then
    return env
  ensureModuleSearchPath `IxC.Kernel.PinGen.Certs
  let env ← Lean.importModules #[{ module := `IxC.Kernel.PinGen.Certs }] default (loadExts := false)
  cachedNativeCertSource.set (some env)
  return env

/-- Release a `CheckedStore`'s decoded record map on a background task after
emission has finished reading it. -/
@[noinline] def dropCheckedStore {limits : Ix.Kernel.Admission.Limits} {env : Ixon.Env}
    (store : CheckedStore limits env) : IO Nat :=
  IO.lazyPure fun _ => store.records.size

/-- If `lc` is a projection record (`cPrj`, `rPrj`, `iPrj`, or `dPrj`), its
owning block address, read from the projection header without decoding any
constant body. -/
def projectionBlock? (lc : Ixon.LazyConstant) : Option Address :=
  match lc.cache with
  | some c =>
    match c.info with
    | .dPrj p | .iPrj p | .rPrj p | .cPrj p => some p.block
    | _ => none
  | none =>
    let getProjBlock : Ixon.GetM (Option Address) := do
      let tag ← Ixon.getTagN 4
      if tag.flag != Ixon.Constant.FLAG then return none
      match tag.value with
      | 4 => (·.block) <$> Ixon.getConstructorProj
      | 5 => (·.block) <$> Ixon.getRecursorProj
      | 6 => (·.block) <$> Ixon.getInductiveProj
      | 7 => (·.block) <$> Ixon.getDefinitionProj
      | _ => return none
    match getProjBlock.run { idx := lc.off, bytes := lc.buf } with
    | .ok block? _ => block?
    | .error _ _ => none

/-- Extract the compiled support closure of `selected` from `artifact` when
every constant in `selected.constants` is already published in `artifact`. -/
def sliceSupport? (artifact : Ixon.Env)
    (existing : Std.HashMap Ix.Kernel.Name Address)
    (selected : Ix.Compile.CompileInput) : Option Ixon.Env := do
  let mut todo : Array Address := #[]
  let mut queued : Std.HashSet Address := {}
  let mut selectedNames : Std.HashSet Ix.Kernel.Name := {}
  for (name, _) in selected.constants do
    let key := Ix.Kernel.Name.ofLeanName name
    let addr ← existing[key]?
    guard (artifact.consts.contains addr)
    selectedNames := selectedNames.insert key
    unless queued.contains addr do
      queued := queued.insert addr
      todo := todo.push addr
  let mut visited : Std.HashSet Address := {}
  let mut consts : Std.HashMap Address Ixon.LazyConstant := {}
  let mut blobs : Std.HashMap Address ByteArray := {}
  let mut anonHints : Std.HashMap Address Lean.ReducibilityHints := {}
  for _ in [:artifact.consts.size + 1] do
    if h : todo.size > 0 then
      let addr := todo[todo.size - 1]
      todo := todo.pop
      unless visited.contains addr do
        let lc ← artifact.consts[addr]?
        let (refs, own) ← Ix.Cert.RecordRefs.lazyRefs addr lc
        visited := visited.insert addr
        consts := consts.insert addr lc
        if let some hint := artifact.anonHints[addr]? then
          anonHints := anonHints.insert addr hint
        let deps := if own == addr then refs else refs.push own
        for dep in deps do
          if artifact.consts.contains dep then
            unless queued.contains dep do
              queued := queued.insert dep
              todo := todo.push dep
          else if let some bytes := artifact.blobs[dep]? then
            blobs := blobs.insert dep bytes
    else
      break
  guard todo.isEmpty
  let kept := (Ix.Cert.parMap (fun (name, entry) =>
    match artifact.consts[entry.addr]? with
    | some lc =>
      let keep := visited.contains entry.addr ||
        match projectionBlock? lc with
        | some b => visited.contains b
        | none => false
      if keep then
        some (name, entry, lc, selectedNames.contains (Ix.LeanIngress.ingressName name))
      else none
    | none => none) artifact.named.toArray).filterMap id
  let mut named : Std.HashMap Ix.Name Ixon.Named := {}
  for (name, entry, lc, isSelected) in kept do
    consts := consts.insert entry.addr lc
    if let some hint := artifact.anonHints[entry.addr]? then
      anonHints := anonHints.insert entry.addr hint
    if isSelected then
      named := named.insert name entry
  some { consts, blobs, named, anonHints }

/-- Generate from real certificate source, compiled by the same raw backend.
No committed/default role table or certificate store supplies missing inputs.

The certificate theorems are read from `certSource`, which must be the same
toolchain's environment as `source`: `nativeCertSource` for a compile of ix's own
toolchain, and the imported environment itself for a compile of another
toolchain's export (`Ix.LeanExport`). It is only run when a role with
certificate evidence (a well-founded operation, or a definition specified by
equations that hold by a certificate) is published. -/
def finalize (backend : Backend) (source : Lean.Environment)
    (certSource : IO Lean.Environment)
    (input : Ix.Compile.CompileInput) (artifact : Ixon.Env)
    (limits : Ix.Kernel.Admission.Limits) : IO Ixon.Env := do
  let initialRoles := publishedRoles artifact
  let (required, selected) ← IO.ofExcept (supportInput source artifact (some initialRoles))
  let theorems := (Ix.RoleEvidence.allCertTheorems.filter (fun (role, _) => required.contains role)).flatMap (·.2)
  let certificatesTask ← IO.asTask do
    if theorems.isEmpty then pure ({} : Ixon.Env) else do
      let certSource ← certSource
      for name in theorems do
        match certSource.find? name with
        | some (.thmInfo _) => pure ()
        | _ => throw (IO.userError s!"artifact evidence: source theorem unavailable: {name}")
      let constants := Ix.EnvScope.collectSelectedDeps certSource theorems
      let selected ← IO.ofExcept ((Ix.Compile.compileInputFromEnv certSource constants).mapError toString)
      compileRequired backend certSource selected
  let existing ← IO.ofExcept (sourceAddresses artifact)
  let covered := selected.constants.all fun (name, _) =>
    existing.contains (Ix.Kernel.Name.ofLeanName name)
  let (merged, compiledSupport?) ← if covered then
      pure (artifact, none)
    else do
      let support ← compileRequired backend source selected
      let merged ← IO.ofExcept (mergeSupport limits artifact support)
      let mergedNames ← IO.ofExcept (sourceAddresses merged)
      IO.ofExcept (preserveRequestedWith input existing mergedNames)
      pure (merged, some support)
  let support ← match compiledSupport? with
    | some support => pure support
    | none =>
      match sliceSupport? merged existing selected with
      | some support => pure support
      | none => compileRequired backend source selected
  let supportStore ← IO.ofExcept (checkedStore limits support)
  let actual := if covered then initialRoles else publishedRoles merged
  unless actual == required do
    throw (IO.userError "artifact support: compiled role publications differ from the selected closure")
  let certificates ← IO.ofExcept certificatesTask.get
  IO.ofExcept (checkCertificateContent merged certificates)
  -- The support already contains every selected role and its source closure.
  -- Evidence generation needs only that closure and the certificate closure;
  -- emission below checks its binding against the complete merged artifact.
  let generated ← IO.ofExcept (generate limits support certificates required Ix.Kernel.preludeShape
    (store? := some supportStore))
  let emitted ← IO.ofExcept (generated.emit limits merged
    (roleStore? := some (supportStore.records[·]?)))
  let _ ← IO.asTask (prio := .dedicated) (dropCheckedStore supportStore)
  unless emitted.roleBinding.isSome do
    throw (IO.userError "artifact finalization: missing emitted role binding")
  let emittedNames ← IO.ofExcept (sourceAddresses emitted)
  IO.ofExcept (preserveRequestedWith input existing emittedNames)
  IO.ofExcept (checkFinalized artifact emitted)
  return emitted

/-- Publish only after finalization and serialization succeed. The temporary
file is beside the destination so rename is atomic on that filesystem. -/
def writeAtomic (path : System.FilePath) (bytes : ByteArray) : IO Unit := do
  let nonce ← IO.rand 0 18446744073709551615
  let temporary := System.FilePath.mk (path.toString ++ s!".binding-{nonce}")
  let handle ← IO.FS.Handle.mk temporary .writeNew
  try
    handle.write bytes
    handle.flush
    IO.FS.rename temporary path
  finally
    if ← temporary.pathExists then IO.FS.removeFile temporary

end Ix.RoleBinding.Compile
