module

public import IxCK.Kernel.Admission.Bytes
public import IxCK.Kernel.Ixon.Prelude
public import IxCK.Kernel.Cached.Policy
public import IxCK.Kernel.Egress.Projection

/-! # Admission from ordered Ixon record bytes

The certified Ixon entry (`docs/kernel.md`): `checkBytes hash binding` checks
exactly the declarations described by the supplied canonical record bytes
with the verified checker `Ix.Kernel` (derived from con-leche,
`IxCK/Kernel/NOTICE`), under the supplied role table:

    preflight → uniqueKeys → authenticate hash → admitBinding hash
              → decodeRecords → Ixon reader → evidenceOf
              → preparePrelude → Ix.Kernel.Cached.checkDecls .verified ev

* `preflight`, `uniqueKeys`, `authenticate` and `decodeRecords` are the byte
  stage (`Ix.Kernel.Admission.Bytes`): the batch limits, key uniqueness (no
  two records and no two blobs under one address), authentication (every
  record and blob under `hash` of its supplied bytes) and canonical
  per-record decoding, with their error positions.
* `admitBinding` admits the role table (`Ix.Kernel.RoleTable`): its binding
  section is authenticated (the section's address is `hash` of its bytes, the
  binding hash a claim commits to), decoded canonically
  (`RoleTable.ofBytes`) and checked for well-formedness
  (`RoleTable.check`). Each failure is a reject.
* The reader is `Ix.Kernel.Reader` (address keys as reserved names, the
  table's bound addresses renamed to their role keys, regrouping of `muts`
  blocks and projection records, the in-process modeller and the projection
  rewrite), against the supplied records with the prelude's and the default
  evidence's records as a fallback store. `evidenceOf` resolves the table's
  evidence to the theorems' values.
* `preparePrelude` is `Ix.Kernel.Frontend.preparePrelude`
  (`IxCK/Kernel/Frontend/Prepare.lean`), with the Ixon prelude read under the
  same table (`Ix.Kernel.Reader.preludeFor`).
* The fold is `Ix.Kernel.Cached.checkDecls` at `.verified`, at the table's
  evidence: the theorem holds at every evidence, so the table is untrusted.

The content hash is the parameter `hash : ByteArray → Address`: the kernel
admits no hasher, and every theorem holds at every `hash`. The root library
instantiates the entry at BLAKE3 (`Ixon.Authenticated`).

This module holds definitions only, so that running the entry does not
build the proof tree; its theorems are in `Ix.Kernel.Admission.Theorems`.
There `checkBytes_has_model` is `Ix.Kernel.model_exists` at the prepared
declarations: the reader owes nothing, because the main theorem holds for
every declaration array and every evidence. The host supplies record order,
address keys, literal blobs and the role table; each key is authenticated as
`hash` of its supplied bytes, and blobs retain those exact bytes. No host
decoder or verdict participates in this path. The entry does not reorder
beyond `preparePrelude`: a host order is a dependency order in which each
record follows its references, a certified `Nat` operation's certificate
ground, and the constants its literals reference (`Reader.literalEdges`; the
checker declines a string literal before the string-support declarations), as
the environment-check driver's order is.
-/

@[expose] public section

namespace Ix.Kernel.Admission

open Ix.Kernel (ConstRef)
open Ix.Kernel.Reader

/-- The fold's settings from the entry's limits: phase B's task bound and
the cached core's configurable bounds (`levelBudget`). -/
def Limits.fold (l : Limits) : Ix.Kernel.Cached.FoldConfig :=
  { workers := l.workers, core := { levelBudget := l.levelBudget } }

/-- **The role table as the entry receives it**: the binding section's
bytes, under the address a claim commits to. -/
structure Binding where
  address : Address
  bytes : ByteArray

/-- Failures of the role table's admission; each is a reject. -/
inductive BindingError where
  /-- the section's address is not `hash` of its bytes -/
  | mismatch (address : Address)
  /-- the bytes are not a canonical binding section (`RoleTable.ofBytes`) -/
  | decode
  /-- the table is not well formed (`RoleTable.check`) -/
  | malformed (reason : String)

/-- **The role table's admission**: authentication of its section under
`hash`, canonical decoding, and well-formedness. -/
def admitBinding (hash : ByteArray → Address) (b : Binding) :
    Except BindingError Ix.Kernel.RoleTable := do
  unless decide (hash b.bytes = b.address) do throw (.mismatch b.address)
  let some t := Ix.Kernel.RoleTable.ofBytes b.bytes | throw .decode
  t.check.mapError .malformed
  pure t

/-- **The bound on a record's universe-parameter count** under the strict
admission (`admitLevels`): Lean declarations have a handful; the format
admits up to `2^32` (`Ixon.maxLevelCount`). -/
def maxRecordLevelParams : Nat := 1024

/-- Byte, binding, reader and checker failures, kept apart. Positions are the
supplied records' (authentication, decoding, reading) or the fold's
(checking). -/
inductive Error where
  | limit (resource : Resource)
  | duplicate (table : Table) (position : Nat) (address : Address)
  | mismatch (table : Table) (position : Nat) (address : Address)
  | decode (position : Nat) (address : Address) (reason : String)
  /-- the role table's section does not admit -/
  | binding (error : BindingError)
  /-- the committed prelude does not load (a corrupted file) -/
  | prelude (reason : String)
  | read (position : Nat) (error : ReadError)
  /-- the reader's state after the stream holds, at a key the prelude's state holds,
  another entry than the prelude's (`State.keepsPrelude`): a stream's copy of a
  prelude record does not read to what the prelude read -/
  | preludeCopy
  | kernel (error : Ix.Kernel.CheckError .anon) (position : Nat)
  /-- the check admits user axioms (`AxiomPolicy.allowUser`), and the role table
  leaves one of `userAxiomRoles` unbound: that role's own axiom would read under
  an input key and be admitted as a user axiom (`admitAxiomPolicy`) -/
  | axiomRoleUnbound (role : Ix.Kernel.Role)
  /-- the strict admission pins the role table to the committed default table
  (`admitPinnedRoles`), and the table binds the pinned role `role`
  (`Role.pinnedToReference`) at `address`, where the committed table binds
  `committed` -/
  | unpinned (role : Ix.Kernel.Role) (address : Option Address) (committed : Option Address)
  /-- the strict admission's universe-parameter bound (`admitLevels`): the
  decoded record at `position` (address `address`) has a member with `count`
  universe parameters, more than `maxRecordLevelParams` -/
  | levels (position : Nat) (address : Address) (count : Nat)

instance : ToString Error where
  toString
    | .limit r => s!"limit: {repr r}"
    | .duplicate t p a => s!"duplicate {repr t} address at {p} ({a})"
    | .mismatch t p a => s!"{repr t} address at {p} is not the hash of its bytes ({a})"
    | .decode p a r => s!"decode at {p} ({a}): {r}"
    | .binding (.mismatch a) => s!"binding: the role table's address is not the hash of its bytes ({a})"
    | .binding .decode => "binding: the role table is not a canonical binding section"
    | .binding (.malformed r) => s!"binding: {r}"
    | .prelude r => s!"prelude: {r}"
    | .read p e => s!"read at {p}: {e}"
    | .preludeCopy => "prelude copy: the stream's reading leaves other entries than the prelude's at a prelude key"
    | .kernel e p => s!"kernel at {p}: {e}"
    | .axiomRoleUnbound r => s!"user axioms: the role table leaves {repr r} unbound; a check that \
        admits user axioms requires all axiom roles bound"
    | .unpinned r a c =>
      let addr? : Option Address → String := fun | some a => toString a | none => "nothing"
      s!"pinned role: the role table binds {r.leanName} at {addr? a}, the committed default \
        table at {addr? c}; the strict admission requires the committed binding of the literal \
        support and of True (a caller may opt out)"
    | .levels p a n => s!"limit: the record at {p} ({a}) has a member with {n} universe \
        parameters; the strict admission reads at most {maxRecordLevelParams}"

/-- The byte stage's failures, unchanged. -/
def Error.ofBytes : ByteError → Error
  | .limit r => .limit r
  | .duplicate t p a => .duplicate t p a
  | .mismatch t p a => .mismatch t p a
  | .decode p a r => .decode p a r

/-- **The address of a member's projection record** under `hash`: the record
projection reconstruction writes for it (`Egress.writeProjection`, with the
layout of the member's kind in its block), serialized and hashed. The reader
keys a block member whose projection record the input omits by it. -/
def projectionAddress (hash : ByteArray → Address) (store : Store) (r : ConstRef Address) :
    Option Address := do
  let layout : Ix.Kernel.Egress.ProjectionLayout ← match r with
    | .ctor .. => some .constructor
    | .member b i => do
      let .muts ms := (← store b).info | none
      match ← ms[i]? with
      | .indc _ => some .inductive
      | .defn _ => some .definition
      | .recr _ => some .recursor
  let record ← (Ix.Kernel.Egress.writeProjection layout r).toOption
  pure (hash (Ixon.serConstant record))

/-- The reader's context for decoded records under a role table and a
prelude, as `readStream` builds it: the records' store backed by the
prelude's records and its evidence records, the recursor index of all, and
the projection addresses under `hash` for the members the input omits a
projection record of. -/
def streamContext (hash : ByteArray → Address) (t : Ix.Kernel.RoleTable) (pre : Prelude .anon)
    (constants : List (Address × Ixon.Constant)) (blobs : Ix.Kernel.Ingress.Blobs)
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint) : Ctx .anon :=
  contextOf t constants.toArray blobs (pre.records ++ pre.evidence) pre.blobs hint
    (projectionAddress hash)

/-- The reading of decoded records under a role table: the prelude's state
continues into the stream, and the prelude's records back the store. The
result is the table's evidence resolved against the reading
(`evidenceOf`), and the declarations. A reading whose final state holds other entries
than the prelude's at a prelude key (`State.keepsPrelude`: the stream's copy of a prelude
record read differently) is refused. -/
def readStream (hash : ByteArray → Address) (t : Ix.Kernel.RoleTable) (pre : Prelude .anon)
    (constants : List (Address × Ixon.Constant)) (blobs : Ix.Kernel.Ingress.Blobs)
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint := fun _ => none) :
    Except Error (Ix.Kernel.Evidences .anon × Array (Ix.Kernel.Declaration .anon)) := do
  let cx := streamContext hash t pre constants blobs hint
  match readRecords cx pre.state constants.toArray with
  | .ok (st, decls) =>
    -- the stream's own copies of the prelude's records read to what the prelude read
    if State.keepsPrelude pre.state st then pure (evidenceOf cx st t, decls) else throw .preludeCopy
  | .error (e, i) => throw (.read i e)

/-- The evidence and the declarations the fold runs over, from the bytes. -/
def prepareWith (hash : ByteArray → Address) (binding : Binding) (pre : Prelude .anon)
    (limits : Limits) (records : Records) (blobs : Ix.Kernel.Ingress.Blobs)
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint := fun _ => none) :
    Except Error (Ix.Kernel.Evidences .anon × Array (Ix.Kernel.Declaration .anon)) := do
  (preflight limits records blobs).mapError Error.ofBytes
  (uniqueKeys records blobs).mapError Error.ofBytes
  (authenticate hash records blobs).mapError Error.ofBytes
  let t ← (admitBinding hash binding).mapError .binding
  let constants ← (decodeWithin limits records).mapError Error.ofBytes
  let (ev, decls) ← readStream hash t pre constants blobs hint
  pure (ev, Ix.Kernel.Frontend.preparePrelude pre.ix decls)

/-- `readStream` without generating in-process inductive models (`readRecordsBare`). -/
def readStreamBare (hash : ByteArray → Address) (t : Ix.Kernel.RoleTable) (pre : Prelude .anon)
    (constants : List (Address × Ixon.Constant)) (blobs : Ix.Kernel.Ingress.Blobs)
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint := fun _ => none) :
    Except Error (Ix.Kernel.Evidences .anon × Array (Ix.Kernel.Declaration .anon)) := do
  let cx := streamContext hash t pre constants blobs hint
  match readRecordsBare cx pre.state constants.toArray with
  | .ok (st, decls) =>
    if State.keepsPrelude pre.state st then pure (evidenceOf cx st t, decls) else throw .preludeCopy
  | .error (e, i) => throw (.read i e)

/-- Tail-recursive bounded exact decoding for `prepareBare`, retaining all
records, keys, and their order under per-record byte and universe-node limits. -/
def decodeLoopBare (limits : Limits) : Nat → Records → Ingress.Constants →
    Except ByteError Ingress.Constants
  | _, [], reversed => .ok reversed.reverse
  | position, (address, bytes) :: rest, reversed => do
    let constant ← (Ixon.Bounded.deConstant limits.maxRecordBytes
      limits.maxRecordUnivNodes bytes).mapError (.decode position address)
    decodeLoopBare limits (position + 1) rest ((address, constant) :: reversed)

/-- Decode records with bounded exact per-record decoding (`Ixon.Bounded.deConstant`)
for `prepareBare`. -/
def decodeRecordsBare (limits : Limits) (records : Records) : Except ByteError Ingress.Constants :=
  decodeLoopBare limits 0 records []

/-- `prepareWith` without generating in-process inductive models (`readStreamBare`),
using bounded exact per-record decoding (`decodeRecordsBare` / `Ixon.Bounded.deConstant`,
retaining exact record layouts under `limits` rather than `prepareWith`'s canonical-only
`decodeRecords`): each inductive block lowers directly to its own declaration, so an
external check that brings its own model advice supplies the model declarations separately. -/
def prepareBare (hash : ByteArray → Address) (binding : Binding) (pre : Prelude .anon)
    (limits : Limits) (records : Records) (blobs : Ix.Kernel.Ingress.Blobs)
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint := fun _ => none) :
    Except Error (Ix.Kernel.Evidences .anon × Array (Ix.Kernel.Declaration .anon)) := do
  (preflight limits records blobs).mapError Error.ofBytes
  (uniqueKeys records blobs).mapError Error.ofBytes
  (authenticate hash records blobs).mapError Error.ofBytes
  let t ← (admitBinding hash binding).mapError .binding
  let constants ← (decodeRecordsBare limits records).mapError Error.ofBytes
  let (ev, decls) ← readStreamBare hash t pre constants blobs hint
  pure (ev, Ix.Kernel.Frontend.preparePrelude pre.ix decls)

/-- The entry over an explicit prelude (tests inject one). -/
def checkBytesWith (hash : ByteArray → Address) (binding : Binding) (pre : Prelude .anon)
    (limits : Limits) (records : Records) (blobs : Ix.Kernel.Ingress.Blobs)
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint := fun _ => none) :
    Except Error (Ix.Kernel.Env .anon) := do
  let (ev, decls) ← prepareWith hash binding pre limits records blobs hint
  (Ix.Kernel.Cached.checkDecls .verified ev decls limits.fold).mapError
    fun (e, i) => .kernel e i

/-- `checkBytes` over a source of preludes: the prelude for the admitted
table is `prelude t` (`preludeFor`, the committed prelude, in `checkBytes`).
The theorems are stated over it, so that no proof unfolds the committed
prelude's data. -/
def checkBytesUsing (prelude : Ix.Kernel.RoleTable → Except String (Prelude .anon))
    (hash : ByteArray → Address) (binding : Binding) (limits : Limits)
    (records : Records) (blobs : Ix.Kernel.Ingress.Blobs)
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint := fun _ => none) :
    Except Error (Ix.Kernel.Env .anon) := do
  let t ← (admitBinding hash binding).mapError .binding
  let pre ← (prelude t).mapError Error.prelude
  checkBytesWith hash binding pre limits records blobs hint

/-- **The certified Ixon entry**: check exactly the declarations described by
the supplied canonical record bytes with the verified checker, after the
batch limits, key uniqueness, authentication of every record and blob
address as `hash` of its bytes, the role table's admission (its section
authenticated under `hash`, decoded canonically, well formed) and canonical
per-record decoding, behind the committed Ixon prelude read under that table.
`hint` is the host's optional (untrusted) reducibility hint per constant. -/
def checkBytes (hash : ByteArray → Address) (binding : Binding) (limits : Limits)
    (records : Records) (blobs : Ix.Kernel.Ingress.Blobs)
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint := fun _ => none) :
    Except Error (Ix.Kernel.Env .anon) :=
  checkBytesUsing preludeFor hash binding limits records blobs hint

/-- The verified fold over decoded records under an admitted role table: the
reader, the prelude, the fold. `checkBytesWith` is byte admission followed by
this (`checkBytesWith_eq`). Decoded records carry no bytes to authenticate: a
caller that starts here vouches for its keys and its table; `hash` keys the
block members whose projection records the input omits. -/
def checkConstantsWith (hash : ByteArray → Address) (t : Ix.Kernel.RoleTable) (pre : Prelude .anon)
    (constants : List (Address × Ixon.Constant)) (blobs : Ix.Kernel.Ingress.Blobs)
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint := fun _ => none)
    (cfg : Ix.Kernel.Cached.FoldConfig := {}) :
    Except Error (Ix.Kernel.Env .anon) := do
  let (ev, decls) ← readStream hash t pre constants blobs hint
  (Ix.Kernel.Cached.checkDecls .verified ev (Ix.Kernel.Frontend.preparePrelude pre.ix decls) cfg).mapError
    fun (e, i) => .kernel e i

/-- The fold's worker count changes no verdict of `checkConstantsWith` (`Cached.checkDecls_cfg`). -/
theorem checkConstantsWith_cfg (hash : ByteArray → Address) (t : Ix.Kernel.RoleTable)
    (pre : Prelude .anon) (constants : List (Address × Ixon.Constant)) (blobs : Ix.Kernel.Ingress.Blobs)
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint) (cfg : Ix.Kernel.Cached.FoldConfig) :
    checkConstantsWith hash t pre constants blobs hint cfg =
      checkConstantsWith hash t pre constants blobs hint { core := cfg.core } := by
  unfold checkConstantsWith
  cases readStream hash t pre constants blobs hint with
  | error e => rfl
  | ok p =>
    simp only [bind, Except.bind]
    rw [Ix.Kernel.Cached.checkDecls_cfg _ _ _ cfg]

/-- `checkConstantsWith` under a role table, behind the prelude `prelude t`. -/
def checkConstantsUsing (prelude : Ix.Kernel.RoleTable → Except String (Prelude .anon))
    (hash : ByteArray → Address) (t : Ix.Kernel.RoleTable) (constants : List (Address × Ixon.Constant))
    (blobs : Ix.Kernel.Ingress.Blobs)
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint := fun _ => none)
    (cfg : Ix.Kernel.Cached.FoldConfig := {}) :
    Except Error (Ix.Kernel.Env .anon) := do
  let pre ← (prelude t).mapError Error.prelude
  checkConstantsWith hash t pre constants blobs hint cfg

/-- `checkConstantsWith` under a role table, behind the committed prelude read
under it. -/
def checkConstants (hash : ByteArray → Address) (t : Ix.Kernel.RoleTable) (constants : List (Address × Ixon.Constant))
    (blobs : Ix.Kernel.Ingress.Blobs)
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint := fun _ => none)
    (cfg : Ix.Kernel.Cached.FoldConfig := {}) :
    Except Error (Ix.Kernel.Env .anon) :=
  checkConstantsUsing preludeFor hash t constants blobs hint cfg

/-- `checkConstants` under a role table's section: the table admitted
(`admitBinding`: authentic under `hash`, canonical, well formed), then
`checkConstants`. The root library's projection variant
(`Ixon.Projection`) ends in it. -/
def checkConstantsAt (hash : ByteArray → Address) (binding : Binding)
    (constants : List (Address × Ixon.Constant)) (blobs : Ix.Kernel.Ingress.Blobs)
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint := fun _ => none)
    (cfg : Ix.Kernel.Cached.FoldConfig := {}) :
    Except Error (Ix.Kernel.Env .anon) := do
  let t ← (admitBinding hash binding).mapError .binding
  checkConstants hash t constants blobs hint cfg

/-- The default role table's section, under the address the generator
committed it at (`RoleData.tableAddress`, BLAKE3 of its bytes). For tests and
the command line: the entry's theorems hold for every table. -/
def defaultBinding : Except String Binding := do
  pure ⟨← defaultTableAddress, ← defaultTableBytes⟩

/-! ## The strict admission

Two checks a strict admission makes before the entry, none of which any
theorem of the entry depends on (every theorem holds for every table and
every batch), and which only refuse:

* **pinned roles** (`admitPinnedRoles`): the
  string-literal support (`Role.literalSupportPinned`) and `True`, `True.intro`
  (`Role.trustAnchorsPinned`, together `Role.pinnedToReference`) are bound where
  the committed default table binds them, or not at all, as `checkBytes` binds
  the prelude roles to the committed prelude records (`preludeFor`). A literal's
  meaning, and the statement of the tolerated `Lean.trustCompiler`, follow these
  roles' bound records, which the fold validates by type only. A caller that
  wants custom literal-support bindings while keeping `True`/`True.intro` pinned
  passes `RolePins.trustAnchors` (used by `--allow-custom-literal-support`); a
  caller that wants to release every pinned role passes `RolePins.asBound`;
* **universe-parameter counts** (`admitLevels`): no record has more
  than `maxRecordLevelParams` universe parameters in any member. The reader
  builds a list of that length per member and the header check compares its
  entries pairwise, so a count near the format's bound (`2^32`) costs a record
  of a dozen bytes gigabytes of memory or hours before any verdict.

`checkBytesStrict` is `checkBytes` behind both; the host's artifact admission
(`Ix.RoleBinding.Artifact`) runs them on its own preparation. -/

/-- **How a strict admission treats the pinned roles**
(`Ix.Kernel.Role.pinnedToReference`). -/
inductive RolePins where
  /-- each pinned role (`Role.pinnedToReference`: the string-literal support
  and `True`, `True.intro`) the table binds is bound where the committed
  default table binds it (`RoleTable.PinnedTo`) -/
  | committed
  /-- `True` and `True.intro` (`Role.trustAnchorsPinned`) remain bound where
  the committed default table binds them (`RoleTable.PinnedRoles
  Role.trustAnchorsPinned`), while the string-literal support uses the table's
  own bindings (checked by type only): for `--allow-custom-literal-support`
  without releasing the tolerated `Lean.trustCompiler`'s statement -/
  | trustAnchors
  /-- the table's own bindings, which the fold validates by type only: a
  caller that pins the binding itself, or reads literals and `True` as the
  table defines them -/
  | asBound
  deriving Repr, DecidableEq, Inhabited

/-- **The pinned roles' admission**: under `committed`, the first pinned role
(`Role.pinnedToReference`) the table binds elsewhere than the committed default
table is refused (`Error.unpinned`); under `trustAnchors`, only `True` and
`True.intro` (`Role.trustAnchorsPinned`) are checked; under `asBound`, none.
A corrupted committed table is a `prelude` failure. -/
def admitPinnedRoles (pins : RolePins) (t : Ix.Kernel.RoleTable) : Except Error Unit :=
  match pins with
  | .asBound => pure ()
  | .committed => do
    let d ← defaultTable.mapError Error.prelude
    match t.unpinned? d with
    | some r => throw (.unpinned r (t.addressOf? r) (d.addressOf? r))
    | none => pure ()
  | .trustAnchors => do
    let d ← defaultTable.mapError Error.prelude
    match t.unpinnedIn? Ix.Kernel.Role.trustAnchorsPinned d with
    | some r => throw (.unpinned r (t.addressOf? r) (d.addressOf? r))
    | none => pure ()

/-- **The largest universe-parameter count among a record's members**,
constructors included: the length of each level-parameter list the reader
builds (`Reader.readRecord`). -/
def levelCount : Ixon.ConstantInfo → Nat
  | .defn d => d.lvls.toNat
  | .recr r => r.lvls.toNat
  | .axio a => a.lvls.toNat
  | .quot q => q.lvls.toNat
  | .cPrj _ | .rPrj _ | .iPrj _ | .dPrj _ => 0
  | .muts ms => ms.foldl (init := 0) fun acc m => max acc <| match m with
    | .defn d => d.lvls.toNat
    | .indc i => i.ctors.foldl (init := i.lvls.toNat) fun acc c => max acc c.lvls.toNat
    | .recr r => r.lvls.toNat

/-- Whether a decoded record's universe-parameter counts are within the
strict admission's bound. -/
def levelsWithin (entry : Address × Ixon.Constant) : Bool :=
  decide (levelCount entry.2.info ≤ maxRecordLevelParams)

/-- **The universe-parameter bound's admission**: the first decoded record
over `maxRecordLevelParams` is refused (`Error.levels`, a decline), before the
reader builds anything from it. -/
def admitLevels (constants : List (Address × Ixon.Constant)) : Except Error Unit :=
  if constants.all levelsWithin then pure ()
  else
    let i := constants.findIdx (fun e => !levelsWithin e)
    match constants[i]? with
    | some (a, c) => throw (.levels i a (levelCount c.info))
    | none => throw (.levels i ⟨ByteArray.empty⟩ 0)

/-- **The strict admission's checks**, on the admitted table and the decoded
records: the universe-parameter bound, then the pinned roles. -/
def admitStrict (pins : RolePins) (t : Ix.Kernel.RoleTable)
    (constants : List (Address × Ixon.Constant)) : Except Error Unit := do
  admitLevels constants
  admitPinnedRoles pins t

/-- **The certified entry behind the strict admission**: the batch limits,
the role table's admission and canonical decoding within the depth limit (as
in `checkBytes`), the strict admission's checks (`admitStrict`), then
`checkBytes`. An accept is an accept of `checkBytes`
(`checkBytesStrict_checkBytes`), so every theorem of `checkBytes` holds of it.

`checkBytesStrict` delegates directly to `checkBytes` (repeating preflight and
record decoding) so that `checkBytes` and all of its theorems stay unchanged;
hot host paths (`Ix.RoleBinding.Artifact.check`, `Ix.HostAdmission.certify`)
run `admitLevels` and `admitPinnedRoles` on their single preparation pass to
avoid double-decoding. -/
def checkBytesStrict (pins : RolePins) (hash : ByteArray → Address) (binding : Binding)
    (limits : Limits) (records : Records) (blobs : Ix.Kernel.Ingress.Blobs)
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint := fun _ => none) :
    Except Error (Ix.Kernel.Env .anon) := do
  (preflight limits records blobs).mapError Error.ofBytes
  let t ← (admitBinding hash binding).mapError .binding
  let constants ← (decodeWithin limits records).mapError Error.ofBytes
  admitStrict pins t constants
  checkBytes hash binding limits records blobs hint

/-- How an Ix caller classifies a failure of the certified entry
(`docs/kernel.md`, "Outcomes"):
`reject` only where an independent check establishes that the
input is wrong (the batch limits are a coverage bound and decline; a key
used twice in one table, a key that is not the hash of its bytes, a role
table that does not admit, a non-canonical record and a record the reader
finds malformed reject); every checker verdict declines, because the checker
reports fuel exhaustion as `internal` and a failed conversion search as
`invalid`, and neither is evidence that the input is wrong. -/
inductive Outcome where
  | rejected
  | declined
  deriving Repr, DecidableEq

/-- The classification of a failure of `checkBytes` (call it as
`e.outcome`). -/
def Error.outcome : Error → Outcome
  | .limit _ => .declined
  | .duplicate .. => .rejected
  | .mismatch .. => .rejected
  | .decode .. => .rejected
  | .binding _ => .rejected
  | .prelude _ => .declined
  | .read _ (.malformed _) => .rejected
  | .read _ (.declined _) => .declined
  | .preludeCopy => .declined
  | .kernel _ _ => .declined
  | .axiomRoleUnbound _ => .declined
  | .unpinned .. => .declined
  | .levels .. => .declined

/-- The classification of a byte-stage failure, as `Error.outcome` makes it:
a batch limit declines; a key used twice in one table, a key that is not the
hash of its bytes and a record that does not decode canonically reject. The
projection variant (`Ixon.Projection`) classifies its byte stage with it. -/
def ByteError.outcome : ByteError → Outcome
  | .limit _ => .declined
  | .duplicate .. => .rejected
  | .mismatch .. => .rejected
  | .decode .. => .rejected

/-! ## Checks that admit user axioms

The fold runs under an axiom policy (`Ix.Kernel.Cached.AxiomPolicy`,
`IxCK/Kernel/Cached/Policy.lean`). `strict` is the certified entry's: at it,
`checkConstantsUnder` and `checkBytesUnder` are `checkConstantsWith` and
`checkBytesWith` (`checkConstantsUnder_strict`, `checkBytesUnder_strict`,
`Ix.Kernel.Admission.UserAxioms`). `allowUser` also admits user axioms, and an
accept is then conditional on them: the entries return the environment
together with the user axioms of the declarations the fold ran over
(`preparedUserAxioms`; the environment cannot list them, since an opaque is
installed as `.axiomInfo` too). With none, the accept is the strict entry's
(`checkBytesUnder_strict_of_nil`). Under `allowUser` the role table must bind
the axiom roles (`admitAxiomPolicy`), and the fold declines a user axiom that
restates an axiom role's specification (`Cached.checkUserAxiomDeclC`). -/

/-- The user axioms of a prepared declaration array (`userAxiomsOfDecls`): its
`.axiomDecl`s under eligible keys, in order. -/
def preparedUserAxioms (decls : Array (Ix.Kernel.Declaration .anon)) :
    List (Ix.Kernel.ConstantVal .anon) :=
  Ix.Kernel.userAxiomsOfDecls decls.toList

/-- **The roles a check that admits user axioms requires bound**: every role in
`Role.all` whose specification is an axiom (`Role.spec` is `.axiom`: `propext`,
`Classical.choice`, `sorryAx`, `Lean.trustCompiler`, and the native-reduction
axioms, plus any future axiom role). Auto-derived from `Role.all` so no axiom
role can be omitted. Left unbound, the role's own axiom reads under an input
key, which is eligible, and would be admitted as a user axiom. -/
def userAxiomRoles : List Ix.Kernel.Role :=
  Ix.Kernel.Role.all.filter fun r =>
    match (Ix.Kernel.Role.spec (md := .anon)) r with
    | .axiom .. => true
    | _ => false

/-- **The role table's admission under an axiom policy**: nothing more under
`strict`; under `allowUser`, every role of `userAxiomRoles` bound, else the
first unbound one is refused (`Error.axiomRoleUnbound`). -/
def admitAxiomPolicy (policy : Ix.Kernel.Cached.AxiomPolicy) (t : Ix.Kernel.RoleTable) :
    Except Error Unit :=
  match policy with
  | .strict => pure ()
  | .allowUser =>
    match userAxiomRoles.find? (fun r => (t.addressOf? r).isNone) with
    | some r => throw (.axiomRoleUnbound r)
    | none => pure ()

/-- **The fold over decoded records under an axiom policy**: the policy's
admission of the table (`admitAxiomPolicy`), the reader, the prelude, and the
fold under the policy (`Cached.checkDeclsUnder`). The result is the environment
and the user axioms it is conditional on (`preparedUserAxioms`, empty under
`strict`). -/
def checkConstantsUnder (policy : Ix.Kernel.Cached.AxiomPolicy) (hash : ByteArray → Address)
    (t : Ix.Kernel.RoleTable) (pre : Prelude .anon)
    (constants : List (Address × Ixon.Constant)) (blobs : Ix.Kernel.Ingress.Blobs)
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint := fun _ => none)
    (cfg : Ix.Kernel.Cached.FoldConfig := {}) :
    Except Error (Ix.Kernel.Env .anon × List (Ix.Kernel.ConstantVal .anon)) := do
  admitAxiomPolicy policy t
  let (ev, decls) ← readStream hash t pre constants blobs hint
  let ds := Ix.Kernel.Frontend.preparePrelude pre.ix decls
  let env ← (Ix.Kernel.Cached.checkDeclsUnder .verified policy ev ds cfg).mapError
    fun (e, i) => .kernel e i
  pure (env, preparedUserAxioms ds)

/-- The fold's worker count changes no verdict of `checkConstantsUnder` (`Cached.checkDeclsUnder_cfg`). -/
theorem checkConstantsUnder_cfg (policy : Ix.Kernel.Cached.AxiomPolicy) (hash : ByteArray → Address)
    (t : Ix.Kernel.RoleTable) (pre : Prelude .anon) (constants : List (Address × Ixon.Constant))
    (blobs : Ix.Kernel.Ingress.Blobs) (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint)
    (cfg : Ix.Kernel.Cached.FoldConfig) :
    checkConstantsUnder policy hash t pre constants blobs hint cfg =
      checkConstantsUnder policy hash t pre constants blobs hint { core := cfg.core } := by
  unfold checkConstantsUnder
  cases admitAxiomPolicy policy t with
  | error e => rfl
  | ok _ =>
    simp only [bind, Except.bind]
    cases readStream hash t pre constants blobs hint with
    | error e => rfl
    | ok p =>
      dsimp only
      rw [Ix.Kernel.Cached.checkDeclsUnder_cfg _ _ _ _ cfg]

/-- **The bytes entry under an axiom policy**: `checkBytesWith`'s byte
admission (`checkBytesWith_eq`: the batch limits, key uniqueness,
authentication, the role table's admission, canonical decoding within
the depth limit), then `checkConstantsUnder`. -/
def checkBytesUnder (policy : Ix.Kernel.Cached.AxiomPolicy) (hash : ByteArray → Address)
    (binding : Binding) (pre : Prelude .anon)
    (limits : Limits) (records : Records) (blobs : Ix.Kernel.Ingress.Blobs)
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint := fun _ => none) :
    Except Error (Ix.Kernel.Env .anon × List (Ix.Kernel.ConstantVal .anon)) := do
  (preflight limits records blobs).mapError Error.ofBytes
  (uniqueKeys records blobs).mapError Error.ofBytes
  (authenticate hash records blobs).mapError Error.ofBytes
  let t ← (admitBinding hash binding).mapError .binding
  let constants ← (decodeWithin limits records).mapError Error.ofBytes
  checkConstantsUnder policy hash t pre constants blobs hint limits.fold

/-- **Deprecated**: `checkBytesWith` with user axioms
admitted, returning only `Prod.fst` of `checkBytesUnder .allowUser` and
discarding the list of user axioms the accepted environment depends on. A
caller cannot observe which axioms were admitted; prefer `checkBytesUnder
.allowUser` directly so the returned axiom list is inspected and reported. -/
def checkBytesWithUserAxioms (hash : ByteArray → Address) (binding : Binding) (pre : Prelude .anon)
    (limits : Limits) (records : Records) (blobs : Ix.Kernel.Ingress.Blobs)
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint := fun _ => none) :
    Except Error (Ix.Kernel.Env .anon) :=
  Prod.fst <$> checkBytesUnder .allowUser hash binding pre limits records blobs hint

/-- **Deprecated**: `checkConstantsWith` with user
axioms admitted, returning only `Prod.fst` of `checkConstantsUnder .allowUser`
and discarding the list of user axioms the accepted environment depends on.
Prefer `checkConstantsUnder .allowUser` directly so the returned axiom list
is inspected and reported. -/
def checkConstantsWithUserAxioms (hash : ByteArray → Address) (t : Ix.Kernel.RoleTable) (pre : Prelude .anon)
    (constants : List (Address × Ixon.Constant)) (blobs : Ix.Kernel.Ingress.Blobs)
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint := fun _ => none) :
    Except Error (Ix.Kernel.Env .anon) :=
  Prod.fst <$> checkConstantsUnder .allowUser hash t pre constants blobs hint

end Ix.Kernel.Admission

end
