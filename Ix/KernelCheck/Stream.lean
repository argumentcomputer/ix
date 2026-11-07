module

public import Ix.KernelCheck.Step
import all IxCK.Ixon.Types.Kinds

@[expose] public section

/-! # The environment check's streaming load (untrusted harness)

`kernel-check-ixe` loads an `.ixe` this way unless `--load eager` is given.
The `.ixe` is parsed metadata-light (`Ixon.deEnvAnon`: names map to
addresses, records stay undecoded until `loadEnv`). Every record is
decoded once for its **skeleton** (`skeleton`): what the order, the record
views and the reader read of a record other than the one being read. The
setup (`CheckIxeStep.setup`) is built over the skeletons, with the literal
edges computed from stand-ins that keep each record's literal kinds
(`literalStandIn`), so the order, the recursor index and the views are those
of the eager load.

In `loadEnv`, parallel worker chunks decode each record once to build its
skeleton and literal flags (keeping full records in the skeleton store only
for proof-evidence records and their owners), build `CheckIxeStep.setup` over
the skeleton store, and then pre-read context-free records in parallel into
`PreRead` (`Read .anon`) entries while retaining full decoded `Ixon.Constant`s
only for context-dependent or tier records. During the check loop
(`CheckIxeStep.checkLoopWith`), each record's pre-read `Read .anon` (or
fallback decoded `Ixon.Constant`) is taken and dropped from `StreamState`
once read.

The rows are the eager load's: the same records in the same order, read by
the same reader from the same decoded records. -/

namespace Ix.Kernel.Reader

/-- Whether a value's body is a projection of the bound variable: the only
shape the projection-function rewrite (`projRewrite`) reads the state for. -/
def projBody (value : CExpr md) : Bool :=
  match Ix.Kernel.Frontend.lamBody value with
  | .proj _ _ (.bvar 0) => true
  | _ => false

/-- Whether `lowerDefinition` reads its reading state `st`: through the
projection rewrite, on a definition's or theorem's projection body (an
opaque's value is kept as read). -/
def readsState (value : CExpr md) : Ix.DefKind → Bool
  | .opaq => false
  | _ => projBody value

/-- Whether `lowerDefinition` reads its `heights`: through the height rule, on
a definition without a host hint. -/
def readsHeights (hint : Option Ix.Kernel.ReducibilityHint) : Ix.DefKind → Bool
  | .defn => hint.isNone
  | _ => false

/-- Whether `lowerDefinition hint st heights cv value kind safety` reads its
reading state or its heights. When it does not, its result is the same at
every state (`lowerDefinition_stateless`), so a reading at the empty state
stands. -/
def needsState (hint : Option Ix.Kernel.ReducibilityHint) (value : CExpr md)
    (kind : Ix.DefKind) : Bool :=
  readsState value kind || readsHeights hint kind

theorem projRewrite_eq_none (st : State md) (cv : CVal md) (value : CExpr md)
    (h : projBody value = false) : projRewrite st cv value = none := by
  unfold projBody at h
  unfold projRewrite
  split
  · rename_i heq
    rw [heq] at h
    simp at h
  · rfl

/-- `needsState` is exact about `lowerDefinition`'s reads: if it says no
state is read, any two states lower the same. -/
theorem lowerDefinition_stateless (hint : Option Ix.Kernel.ReducibilityHint)
    (st st' : State md) (heights heights' : CName md → Nat) (cv : CVal md)
    (value : CExpr md) (kind : Ix.DefKind) (safety : Ix.DefinitionSafety)
    (h : needsState hint value kind = false) :
    lowerDefinition hint st heights cv value kind safety =
      lowerDefinition hint st' heights' cv value kind safety := by
  cases kind with
  | defn =>
    cases hint with
    | none => simp [needsState, readsHeights] at h
    | some k =>
      simp only [needsState, readsState, readsHeights, Option.isNone_some, Bool.or_false] at h
      simp [lowerDefinition, projRewrite_eq_none _ _ _ h]
  | thm =>
    simp only [needsState, readsState, readsHeights, Bool.or_false] at h
    simp [lowerDefinition, projRewrite_eq_none _ _ _ h]
  | opaq =>
    -- the derived `BEq` is unfolded here (`import all` of its module)
    have hk : (Ix.DefKind.opaq != Ix.DefKind.opaq) = false := rfl
    simp [lowerDefinition, hk]

end Ix.Kernel.Reader

namespace Benchmarks.Kernel.CheckIxeStream

open Ix.Kernel.Reader
open Benchmarks.Kernel.CheckIxeStep

/-! ## Skeletons -/

def stubExpr : Ixon.Expr := .sort 0

def stubDefn (d : Ixon.Definition) : Ixon.Definition := { d with typ := stubExpr, value := stubExpr }

def stubInd (i : Ixon.Inductive) : Ixon.Inductive :=
  { i with typ := stubExpr, ctors := i.ctors.map fun c => { c with typ := stubExpr } }

/-- What the order, the record views and the reader read of a record other
than the one being read: its info tag and kind (`owner`, `kindOf`,
`resolveSource`), its references (`order`, `dependencies`), an inductive's
constructor count and universe count (`inductiveAt`, `buildIndex`), and
recursor records in full (`buildIndex` reads their types; an inductive block
is read with its recursor records). Expressions, sharing and universe tables
are dropped from everything else. -/
def skeleton (c : Ixon.Constant) : Ixon.Constant :=
  match c.info with
  | .defn d => { c with info := .defn (stubDefn d), sharing := #[], univs := #[] }
  | .axio a => { c with info := .axio { a with typ := stubExpr }, sharing := #[], univs := #[] }
  | .quot q => { c with info := .quot { q with typ := stubExpr }, sharing := #[], univs := #[] }
  | .muts ms =>
    if ms.any (fun | .recr _ => true | _ => false) then c
    else
      { c with
        info := .muts (ms.map fun
          | .defn d => .defn (stubDefn d)
          | .indc i => .indc (stubInd i)
          | .recr r => .recr r)
        sharing := #[], univs := #[] }
  | _ => c

/-- A stand-in that `literalKinds` reads as a record with literals of the
given kinds. -/
def literalStandIn (nat str : Bool) : Ixon.Constant :=
  { info := .axio { isUnsafe := false, lvls := 0, typ := stubExpr }
    sharing := (if nat then #[Ixon.Expr.nat 0] else #[]) ++ (if str then #[Ixon.Expr.str 0] else #[])
    refs := #[], univs := #[] }

/-! ## The load -/

/-- A pre-computed record reading when the expression DAG does not depend on
prior records' `State .anon`, or a pre-built `.defn` header (`cv`, `value`)
that only needs `lowerDefinition` against `st.projOwners` / `st.heights` during
the sequential pass. -/
inductive PreRead where
  | ready (r : Except ReadError (Read .anon))
  | defn (cv : CVal .anon) (value : CExpr .anon)
      (kind : Ix.DefKind) (safety : Ix.DefinitionSafety)

/-- Pre-read a record against an empty `State .anon` when its `Expr .anon`
construction is independent of prior records' state. A single definition
whose lowering reads the state (`needsState`) is pre-read up to its header and
value, lowered at its turn. Returns `none` only for records whose expression
construction depends on `st` otherwise (inductive blocks needing the
in-process model, or mutual definition blocks with a member whose lowering
reads the state). -/
def preReadRecord (cx : Ctx .anon) (address : Address) (c : Ixon.Constant) : Option PreRead :=
  match c.info with
  | .defn d =>
    match readRecord cx {} address c with
    | .error e => some (.ready (.error e))
    | .ok rd =>
      match rd.decls[0]? with
      | some (Ix.Kernel.Declaration.defnDecl cv value _)
      | some (Ix.Kernel.Declaration.thmDecl cv value) =>
        if needsState (cx.hint (.member address 0)) value d.kind then
          some (.defn cv value d.kind d.safety)
        else
          some (.ready (.ok rd))
      | _ => some (.ready (.ok rd))
  | .muts ms =>
    if ms.any (fun | .indc _ => true | _ => false) then
      match readRecord cx {} address c with
      | .ok rd =>
        if rd.blocks.all fun (_, b) => !Ix.Kernel.Frontend.InModel.wants b then
          some (.ready (.ok rd))
        else
          none
      | .error _ => none
    else if ms.all (fun | .defn _ => true | _ => false) then
      match readRecord cx {} address c with
      | .error e => some (.ready (.error e))
      | .ok rd =>
        -- `needsState` member by member: the heights by the member's index
        -- in the block (its hint's), the state by its declaration (the
        -- declarations follow `defOrder`, not the block's order)
        let needsSt := (List.range ms.size).any (fun i =>
          match ms[i]? with
          | some (.defn d) => readsHeights (cx.hint (.member address i)) d.kind
          | _ => false) ||
          rd.decls.any fun (d : Ix.Kernel.Declaration .anon) =>
            match d with
            | .defnDecl _ value _ => readsState value .defn
            | .thmDecl _ value => readsState value .thm
            | _ => false
        if needsSt then none else some (.ready (.ok rd))
    else
      some (.ready (readRecord cx {} address c))
  | _ =>
    some (.ready (readRecord cx {} address c))

/-- Pre-read a chunk of decoded records in a worker task, keeping a decoded
record only where the check loop still reads it: when its pre-read gave up,
and for a tier record (the tier reader reads it). Every other decoded record
is freed with its chunk. -/
def preReadChunk (cx : Ctx .anon)
    (chunk : Array (Address × Ixon.Constant × Ixon.Constant × (Bool × Bool))) :
    Array (Address × Option PreRead × Option Ixon.Constant) :=
  chunk.map fun (address, c, _, _) =>
    let pr := preReadRecord cx address c
    (address, pr, if pr.isNone || Ix.Kernel.Admission.isTierInfo c.info then some c else none)

/-- A streaming load: the environment without its records, the setup over
the skeletons, the decoded records the pre-read could not read ahead (the
context-dependent ones and the tier records), the parallel pre-readings (both
handed to the check loop's thread in a reference, so that the loop takes the
only reference to the containers), and the prelude's records that the `.ixe`
does not hold (read in full from the setup's store). -/
structure Loaded where
  env : Ixon.Env
  setup : Setup
  decoded : IO.Ref (Std.HashMap Address Ixon.Constant)
  preReads : IO.Ref (Std.HashMap Address PreRead)
  preludeOnly : Std.HashSet Address
  tierAddresses : Std.HashSet Address := {}

/-- A lazy constant decoded, as `LazyConstant.get` decodes it, from its own
copy of its bytes. Every record of a loaded `.ixe` is a window into the one
file buffer, and the decoder's state holds the buffer it reads: decoded in
place by the parallel workers, every step of every worker updates that one
buffer's thread-shared reference count, and the chunks spend about 50 times
the work of decoding the same records one at a time from copies. -/
def decodeOwn (lazy : Ixon.LazyConstant) : Except String Ixon.Constant :=
  match lazy.cache with
  | some c => .ok c
  | none => Ixon.deConstantAt lazy.rawBytes 0 lazy.len

/-- Decode a slice `[lo, hi)` of lazy constants together with their skeletons
and literal-kind flags. -/
def decodeChunk (entries : Array (Address × Ixon.LazyConstant))
    (lo hi : Nat) : Except String (Array (Address × Ixon.Constant × Ixon.Constant × (Bool × Bool))) := Id.run do
  let mut out := Array.mkEmpty (hi - lo)
  for idx in [lo:hi] do
    if h : idx < entries.size then
      let (address, lazy) := entries[idx]
      match decodeOwn lazy with
      | .ok c => out := out.push (address, c, skeleton c, literalKinds c)
      | .error e => return .error e
  return .ok out

/-- Load an already-parsed anonymous `.ixe` environment for streaming: decode
every record once in parallel chunks for its skeleton, literal kinds, and
streaming read state, build the setup over the skeletons, and pre-read
state-independent expression DAGs in parallel.

With `persistent`, the setup is marked persistent before the pre-read: the
pre-read workers then read its reader context without thread-shared reference
counting, and the setup is never freed. A caller that keeps the setup to the
end of its process sets it (`kernel-check-ixe`); without it, the setup is
freed as usual once its last reference is dropped. -/
def loadEnv (env : Ixon.Env) (table : Ix.Kernel.RoleTable) (pre : Prelude .anon)
    (persistent : Bool := false) : IO Loaded := do
  -- Input theorem records shadow fallback evidence at the same address.
  -- Preserve their real values, including a projected theorem's owner.
  let mut proofRecords : Std.HashSet Address := {}
  for (_, evEntries) in table.evidence do
    for entry in evEntries do
      if let .proof address := entry then
        proofRecords := proofRecords.insert address
        if let some lazy := env.consts[address]? then
          let record ← IO.ofExcept lazy.get
          proofRecords := proofRecords.insert (Ixon.CheckOrder.owner address record)
  let entries := env.consts.toArray
  let env := { env with consts := {} }
  let chunkSize := Nat.max 256 ((entries.size + 63) / 64)
  let numChunks := (entries.size + chunkSize - 1) / chunkSize
  let tasks := (Array.range numChunks).map fun i =>
    let lo := i * chunkSize
    let hi := Nat.min entries.size (lo + chunkSize)
    Task.spawn fun () => decodeChunk entries lo hi
  let mut chunks : Array (Array (Address × Ixon.Constant × Ixon.Constant × (Bool × Bool))) :=
    Array.mkEmpty numChunks
  let mut store : RecordStore := Std.HashMap.emptyWithCapacity entries.size
  let mut litFlags : Array (Address × Bool × Bool) := #[]
  let mut tierAddresses : Std.HashSet Address := {}
  for t in tasks do
    let chunk ← IO.ofExcept t.get
    chunks := chunks.push chunk
    for (address, c, sk, (nat, str)) in chunk do
      if nat || str then litFlags := litFlags.push (address, nat, str)
      if Ix.Kernel.Admission.isTierInfo sk.info then
        tierAddresses := tierAddresses.insert address
      store := store.insert address (if proofRecords.contains address then c else sk)
  let preludeOnly := pre.records.foldl (init := {}) fun (acc : Std.HashSet Address) (a, _) =>
    if store.contains a then acc else acc.insert a
  let hints := Hints.ofStore store env.anonHints
  let s := setup store (env.blobs[·]?) table pre hints.lookup (literalFlags := some litFlags)
  -- `markPersistent` is `unsafe`: a persistent object is never freed.
  let s ← if persistent then unsafe Runtime.markPersistent s else pure s
  let preTasks := chunks.map fun chunk => Task.spawn fun () => preReadChunk s.cx chunk
  let mut preReads : Std.HashMap Address PreRead := Std.HashMap.emptyWithCapacity entries.size
  let mut decoded : Std.HashMap Address Ixon.Constant := {}
  for pt in preTasks do
    let preChunk := pt.get
    for (address, pr?, c?) in preChunk do
      if let some pr := pr? then preReads := preReads.insert address pr
      if let some c := c? then decoded := decoded.insert address c
  return {
    env
    setup := s
    decoded := ← IO.mkRef decoded
    preReads := ← IO.mkRef preReads
    preludeOnly
    tierAddresses
  }

/-- Load an `.ixe` for streaming: decode every record once in parallel chunks
for its skeleton, literal kinds, and streaming read state, and build the setup
over the skeletons (`loadEnv`, with `persistent`). -/
def load (bytes : ByteArray) (table : Ix.Kernel.RoleTable) (pre : Prelude .anon)
    (persistent : Bool := false) : IO Loaded := do
  let env ← IO.ofExcept (Ixon.deEnvAnon bytes)
  loadEnv env table pre persistent

/-! ## Reading -/

/-- The reading state of a streaming run: the reader's state, the pre-built
readings, and the decoded records of the `.ixe` not yet read. -/
structure StreamState where
  st : State .anon := {}
  records : Std.HashMap Address Ixon.Constant := {}
  preReads : Std.HashMap Address PreRead := {}

/-- Take both the pre-read map and fallback decoded records out of `Loaded`
so the check loop's thread holds the sole reference to the containers. -/
def Loaded.init (l : Loaded) : IO StreamState := do
  let records ← l.decoded.modifyGet fun m => (m, {})
  let preReads ← l.preReads.modifyGet fun m => (m, {})
  return { records, preReads }

/-- A record read in full: from the pre-read map or fallback decoded record map,
or, for a prelude record the `.ixe` does not hold, the setup's. -/
def StreamState.read (l : Loaded) (ss : StreamState) (address : Address) : Except ReadError (Read .anon) :=
  match ss.preReads[address]? with
  | some (.ready r) => r
  | some (.defn cv value kind safety) =>
    match lowerDefinition (l.setup.cx.hint (.member address 0)) ss.st (ss.st.heights.getD · 0)
        cv value kind safety with
    | .ok (decl, rw) => .ok { decls := #[decl], projRewrites := if rw then 1 else 0 }
    | .error e => .error e
  | none =>
    match ss.records[address]? with
    | some source => readRecord l.setup.cx ss.st address source
    | none =>
      if l.preludeOnly.contains address then l.setup.read ss.st address
      else .error (.malformed "record is missing or was read already")

/-- The state after a record: the reader's state learns from it, and its
pre-read entry or decoded record is dropped. -/
def StreamState.commit (ss : StreamState) (address : Address) (rd : Read .anon) : StreamState :=
  { st := ss.st.commit rd
    records := if ss.records.isEmpty then ss.records else ss.records.erase address
    preReads := ss.preReads.erase address }

/-- A tier record read in full by the tier reader (`none`: not a tier record).
Its skeleton keeps its safety, so the test needs no decoding. -/
def StreamState.tierRead (l : Loaded) (ss : StreamState) (address : Address) :
    Option (Except ReadError (Ix.Kernel.Tier.TierDecl .anon)) := do
  let sk ← l.setup.store[address]?
  guard (Ix.Kernel.Admission.isTierInfo sk.info)
  match ss.records[address]? with
  | some source => readTierAt l.setup.cx address source
  | none => some (.error (.malformed "record is missing or was read already"))

/-- A streaming load as a loop source. -/
def Loaded.source (l : Loaded) : LoopSource StreamState :=
  { view := l.setup.view, read := StreamState.read l,
    commit := StreamState.commit, init := l.init,
    tier := some (StreamState.tierRead l),
    tierAddresses := some l.tierAddresses }

end Benchmarks.Kernel.CheckIxeStream
