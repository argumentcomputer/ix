module

public import Ix.Address.Admission
public import Ix.Ixon.CheckOrder
public import Ix.RoleBinding.Artifact
public import IxC.Kernel.Admission.Tier
public import IxC.Kernel.Tier.Ind
public import IxC.Kernel.Tier.Answer

/-! # resource-v1's typing half

`typeCheck` types every record of an Ixon environment as committed: its
exact bytes (never a materialized cache), in an executable whole-environment
check order (`Ixon.CheckOrder.wholeEnv`), with every blob, the compiler's
reducibility hints and the artifact's admitted role table and actual prelude.
Legacy unbound inputs retain the default table/prelude. It splits the records in two.

**The certified part** is checked by IxC's tiered Ixon entry at BLAKE3,
`Ix.Kernel.Admission.checkBytesTieredUsing`, with the same prepared binding and
guarded prelude. Its accept is what the entry's theorem states: every record
and blob of the part authenticated, the logical environment model-backed, and
the tier's `partial` and `unsafe` definitions, unsafe opaques and unsafe axioms
typed with every tier constant opaque.

**The uncertified part** is what that entry declines by design, and the
records that depend on it: every **unsafe inductive** (the reader declines
it, divergence Q2) and every **assumption axiom** (a safe axiom no role
binds: the certified theory is Lean's with its three standard axioms, which
the role table binds), with the recursor and projection records of such a
block and every record that names one of them, transitively. No record of
the certified part names an uncertified one. It is typed by IxC's checking
functions outside any theorem, as Lean's kernel would type it, from the
certified part's environment:
* first its safe records in check order: an assumption axiom by its header
  (`Tier.axiomC`: annotated, its type a sort, then pushed as an axiom), every
  other declaration by the fold's own phase A and phase B steps
  (`Cached.annotDeclStep`, `Cached.checkPendingList`);
* then, staged as Lean's lattice (`Tier.TierDecl.stage`), every tier record
  and its unsafe inductive blocks, **transparently, as Lean and `Ix.Tc`
  check them**: with δ on tier definitions and ι on unsafe recursors, over
  the typing tier's **answer view** (`IxC.Kernel.Tier.Answer`; this module is
  the answers fence's one allowed importer, `Tests/Ix/Kernel/Layering.lean`).
  A definition block is checked by the batch tier's step (`Tier.checkDeclC`,
  tier constants opaque) and, if that refuses, over the answer view with its
  own δ forms installed (`defsOverAnswers`: Lean's kernel unfolds
  `U.below` to type `U.brecOn`); its δ forms then join the view. An unsafe
  opaque or axiom is checked opaque only (Lean unfolds neither). An unsafe
  block is installed by T1's typing-only `Tier.indC` (formers, constructors
  with Lean's field-universe rule, the given recursor records' headers and
  rules; no positivity, as Lean skips it for unsafe) and joins the view with
  its recursors' typed rules (`AnswerView.pushInd`). The certified part's tier
  records are read and re-checked here too, for their δ forms.

**The certified part never reads the answer view.** `checkCertified` runs
the tiered byte entry exactly as its theorem takes it, and returns
only the installed environment; `typeUncertified` takes that environment as
its only input from the certified run and builds the answer view for the
uncertified records' checks alone.

An environment without unsafe inductives and assumption axioms starts with
an empty uncertified part. Its verdict is the certified entry's alone when
the batch tier succeeds. If the batch tier refuses a tier record, `typeCheck`
moves every tier record to the uncertified part and retries certified
admission on the remaining logical records. The separate checker then types
the tier transparently. A successful result with a nonempty uncertified part
combines the certified part's theorem with IxC's uncertified typing of the
rest. The claim string stays `resource-v1`, uncertified as a resource claim
(`Ix.Resource.Claim`).

The reading of an unsafe block (`readTierBlock`) is a separate entry: the
certified reader, the batch tier and its theorem are unchanged, and the
certified entry still declines unsafe inductives. Nothing here is trusted by
a theorem: a wrong order, split or hint is a decline, never a certified
accept. -/

@[expose] public section

namespace Ix.Resource

open Ix.Kernel (ConstRef)
open Ix.Kernel.Reader

variable {md : Ix.Kernel.Mode}

/-- Bounds wide enough for a whole compiled library (as `kernel-check-ixe
--entry` sets them). They are coverage bounds: an input past one declines. -/
def typingLimits : Ix.Kernel.Admission.Limits := ⟨1 <<< 22, 1 <<< 22, 1 <<< 34, 1 <<< 28, 1 <<< 26⟩

/-- A shipped reducibility hint as the kernel's (`Ix.Cert.hintOf`, copied). -/
def hintOf : Lean.ReducibilityHints → Ix.Kernel.ReducibilityHint
  | .opaque => .opaque
  | .abbrev => .abbrev
  | .regular h => .regular h.toNat

/-- What the typing half reads: every record in check order with its
committed bytes, every blob, the hints with the projection map they are read
through, and the role table and prelude. -/
structure TypingInput where
  binding : Ix.Kernel.Admission.Binding
  /-- A supplied artifact binding requires complete role/evidence coverage,
  including operations unused by the requested resource program. -/
  bound : Bool := false
  table : Ix.Kernel.RoleTable
  pre : Prelude .anon
  /-- every record, in check order: address, decoded record, committed bytes -/
  ordered : Array (Address × Ixon.Constant × ByteArray)
  blobs : Ix.Kernel.Ingress.Blobs
  /-- each definition block member's projection record -/
  projections : Std.HashMap (ConstRef Address) Address
  hints : Std.HashMap Address Lean.ReducibilityHints

/-- **The compiler's reducibility hints**, read as `Ix.Cert.hintsOf` reads
them (copied, so that `Ix.Resource` does not import `Ix.Cert`; the test
`resource-hints` checks that the two agree): the hint the artifact ships at
a definition block member's projection record, otherwise at the record. The
projection map is built once, with the input: a lookup returned as a closure
from a function of the environment would be compiled at its full arity and
rebuild the map at every call. -/
def TypingInput.hint (input : TypingInput) (r : ConstRef Address) : Option Ix.Kernel.ReducibilityHint :=
  hintOf <$> input.hints.get? ((input.projections.get? r).getD r.block)

/-- The entry uses the same admitted table and guarded prelude as preparation.
The resource answer view remains confined to the separately typed part. -/
def TypingInput.preludeFor (input : TypingInput) (table : Ix.Kernel.RoleTable) :
    Except String (Prelude .anon) := do
  unless table.toBytes == input.binding.bytes do
    throw "resource validator: admitted table differs from prepared binding"
  return input.pre

/-- The typing half's input. Every record is decoded from its committed
bytes (`lazy.rawBytes`: Lean's public `LazyConstant` record permits a
conflicting materialized cache, which neither validator may trust in place of
the committed bytes) by the entry's own canonical decoder; the entry decodes
the same bytes again itself. -/
def typingInput (env : Ixon.Env) : Except String TypingInput := do
  if env.roleBinding.isSome then
    let input ← (Ix.RoleBinding.Artifact.prepareRecords env typingLimits).mapError toString
    let p := input.prepared
    let bytes : Std.HashMap Address ByteArray := p.records.foldl (fun m (a, b) => m.insert a b) {}
    let ordered ← input.constants.toArray.mapM fun (a, c) => do
      let some raw := bytes[a]? | throw s!"resource validator: missing prepared bytes at {a}"
      pure (a, c, raw)
    let projections : Std.HashMap (ConstRef Address) Address := input.constants.foldl (init := {}) fun m (a, c) =>
      match c.info with
      | .dPrj p => m.insert (.member p.block p.idx.toNat) a
      | _ => m
    return { binding := p.binding, bound := true, table := p.table, pre := p.pre, ordered, projections
             hints := env.anonHints, blobs := p.blobs }
  let binding ← Ix.Kernel.Admission.defaultBinding
  let table ← defaultTable
  let pre : Prelude .anon ← preludeFor table
  let committed : Array (Address × ByteArray) :=
    (env.consts.toArray.map fun (a, lazy) => (a, lazy.rawBytes)).qsort fun x y => x.1.cmpBytes y.1 == .lt
  let constants ← (Ix.Kernel.Admission.decodeRecords typingLimits committed.toList).mapError
    (toString ∘ Ix.Kernel.Admission.Error.ofBytes)
  let bytes : Std.HashMap Address ByteArray := committed.foldl (fun m (a, b) => m.insert a b) {}
  let decoded : Std.HashMap Address Ixon.Constant := constants.foldl (fun m (a, c) => m.insert a c) {}
  let ordered := (Ixon.CheckOrder.wholeEnv table pre constants.toArray).filterMap fun a => do
    pure (a, ← decoded[a]?, ← bytes[a]?)
  let projections : Std.HashMap (ConstRef Address) Address := constants.foldl (init := {}) fun m (a, c) =>
    match c.info with
    | .dPrj p => m.insert (.member p.block p.idx.toNat) a
    | _ => m
  return { binding, table, pre, ordered, projections, hints := env.anonHints
           blobs := (env.blobs.toArray.qsort fun x y => x.1.cmpBytes y.1 == .lt).toList }

/-! ## The split -/

/-- Whether a record is an unsafe inductive piece: a block with an unsafe
type, constructor or recursor, or a recursor record of an unsafe recursor. -/
def isUnsafeInductive (c : Ixon.Constant) : Bool :=
  match c.info with
  | .muts ms => ms.any fun
    | .indc ind => ind.isUnsafe || ind.ctors.any (·.isUnsafe)
    | .recr r => r.isUnsafe
    | .defn _ => false
  | .recr r => r.isUnsafe
  | _ => false

/-- Whether a record is an assumption axiom: a safe axiom that no role of the
table binds. -/
def isAssumption (roles : Bindings .anon) (a : Address) (c : Ixon.Constant) : Bool :=
  match c.info with
  | .axio ax => !ax.isUnsafe && !roles.names.contains (.member a 0)
  | _ => false

/-- **The uncertified part**, by record owner: the owners of unsafe
inductive pieces and assumption axioms, and every owner whose records name
one of them, transitively (a projection record goes with its owner). -/
def uncertifiedOwners (roles : Bindings .anon) (ordered : Array (Address × Ixon.Constant × ByteArray)) :
    Std.HashSet Address := Id.run do
  let store : Ixon.CheckOrder.RecordStore := ordered.foldl (fun m (a, c, _) => m.insert a c) {}
  let ownerOf (a : Address) : Address := match store[a]? with
    | some c => Ixon.CheckOrder.owner a c
    | none => a
  let mut users : Std.HashMap Address (Array Address) := {}
  let mut todo : Array Address := #[]
  for (a, c, _) in ordered do
    let o := Ixon.CheckOrder.owner a c
    if isUnsafeInductive c || isAssumption roles a c then todo := todo.push o
    for r in c.refs do
      if store.contains r then
        let t := ownerOf r
        unless t == o do users := users.insert t ((users.getD t #[]).push o)
  let mut out : Std.HashSet Address := {}
  while h : todo.size > 0 do
    let o := todo[todo.size - 1]
    todo := todo.pop
    if out.contains o then continue
    out := out.insert o
    todo := todo ++ users.getD o #[]
  return out

/-! ## Reading the uncertified part -/

/-- **An unsafe inductive block read for the tier** (the separate tier entry
for Ixon): `Reader.readInductive`'s reading of the block, its constructors
and its recursor records, without its safety declines and without lowering
(no modeller, no `indDecl`), as T1's Source conversion
(`Ix.LeanIngress.convertTierInductive`) reads a block for the tier. -/
def readTierBlock (cx : Ctx .anon) (owner : Address) (c : Ixon.Constant) (ms : Array Ixon.MutConst) :
    ReadM (BlockRead .anon) := do
  let some shape := cx.index.blocks[owner]?
    | declined "inductive block without a recursor in the input"
  let self : Nat → Option (ReadM (CName .anon)) := fun i =>
    if i < ms.size then some (cx.memberKey (.member owner i)) else none
  let indcs : Array (Nat × Ixon.Inductive) :=
    shape.order.filterMap fun i => match (ms[i]? : Option Ixon.MutConst) with
      | some (.indc ind) => some (i, ind)
      | _ => none
  unless indcs.size == shape.order.size do malformed "recursor motive is not a member of its block"
  let some (_, first) := indcs[0]? | malformed "empty inductive block"
  let nPd := first.params.toNat
  unless indcs.all (·.2.params.toNat == nPd) do
    declined "inductive block whose type records disagree on numParams"
  let blockLps := List.range first.lvls.toNat
  let mrInd := MemberReader.mk' cx c id self
  let mut types : Array (CVal .anon × Nat × Nat) := #[]
  for (i, ind) in indcs do
    types := types.push (⟨← cx.memberKey (.member owner i), List.range ind.lvls.toNat,
      ← mrInd.read ind.typ⟩, ind.params.toNat, ind.indices.toNat)
  let mut ctors : Array (CVal .anon × Nat × Nat) := #[]
  let mut ctorNames : Array (List (CName .anon)) := #[]
  for (i, ind) in indcs do
    let mut names : List (CName .anon) := []
    for (ctor, j) in ind.ctors.zipIdx do
      unless ctor.cidx.toNat == j do malformed "constructor index differs from its position"
      let cv : CVal .anon :=
        ⟨← cx.memberKey (.ctor owner i j), List.range ctor.lvls.toNat, ← mrInd.read ctor.typ⟩
      unless nPd + ctor.fields.toNat == piTeleLen cv.type do
        malformed s!"constructor {cv.name} declares {ctor.fields} fields at {nPd} parameters; \
          its type has {piTeleLen cv.type} binders"
      ctors := ctors.push (cv, ctor.params.toNat, ctor.fields.toNat)
      names := names ++ [cv.name]
    ctorNames := ctorNames.push names
  let mut recs : Array (CVal .anon × RecCounts × List (Ix.Kernel.RecRule .anon)) := #[]
  for ref in shape.recs do
    let some entry := cx.index.recs[ref]? | malformed "unindexed recursor"
    let .member rOwner j := ref | malformed "recursor reference is a constructor"
    let some rc := cx.store rOwner | malformed "recursor record is missing"
    let some (_, r) := (recursorMembers rc).find? (·.1 == j) | malformed "recursor member is missing"
    let key ← cx.memberKey ref
    let rself : Nat → Option (ReadM (CName .anon)) := fun i => match rc.info with
      | .muts rms => if i < rms.size then some (cx.memberKey (.member rOwner i)) else none
      | _ => if i == 0 then some (pure key) else none
    let lps := recLps entry.large blockLps
    let mr := MemberReader.mk' cx rc (recParam lps) rself
    let cv : CVal .anon := ⟨key, lps, ← mr.read r.typ⟩
    let some major := inductiveAt cx.store entry.major
      | declined s!"recursor {key}: its major premise is not an inductive"
    unless major.ctors.size == r.rules.size do
      malformed s!"recursor {key} has {r.rules.size} rules for {major.ctors.size} constructors"
    let .member mb mi := entry.major | malformed "recursor major is a constructor"
    let mut rules : List (Ix.Kernel.RecRule .anon) := []
    for (rule, k) in r.rules.zipIdx do
      rules := rules ++ [Ix.Kernel.RecRule.mk (← cx.memberKey (.ctor mb mi k)) rule.fields.toNat 0 .inert
        (← mr.read rule.rhs) false false false]
    recs := recs.push (cv, ⟨r.params.toNat, r.motives.toNat, r.minors.toNat, r.indices.toNat, r.k,
      some entry.motive⟩, rules)
  return ⟨nPd, types, ctors, ctorNames, recs⟩

/-- A block as the tier takes it (`Ix.LeanIngress.tierIndOf`'s, at any mode). -/
def tierIndOf (rb : BlockRead md) : Ix.Kernel.Tier.TierInd md :=
  { numParams := rb.numParams
    types := rb.types.toList.map fun (cv, _, nIdx) => (cv, nIdx)
    ctors := rb.ctors.toList.map fun (cv, _, nF) =>
      (cv, (rb.ctorNames.findIdx? (·.contains cv.name)).getD rb.types.size, nF)
    recs := rb.recs.toList.map fun (cv, c, rules) =>
      (cv, ⟨c.params, c.motives, c.minors, c.indices⟩, rules) }

/-- An uncertified tier item: a tier declaration (`Tier.checkDeclC`) or an
unsafe inductive block (`Tier.indC`). -/
inductive TierItem where
  | decl (record : Address) (d : Ix.Kernel.Tier.TierDecl .anon)
  | block (b : Ix.Kernel.Tier.TierInd .anon)
  deriving Inhabited

/-- Lean's lattice: a partial block (0), an unsafe opaque (1), an unsafe
block, axiom or inductive (2). -/
def TierItem.stage : TierItem → Nat
  | .decl _ d => d.stage
  | .block _ => 2

/-- The uncertified part, read: its safe records' declarations and its tier
items, each with its record's position in check order. -/
structure Uncertified where
  safe : Array (Nat × Array (Ix.Kernel.Declaration .anon)) := #[]
  tier : Array (Nat × TierItem) := #[]
  /-- the reading's final state, for the table's evidence -/
  state : State .anon := {}

/-- **The reading of the uncertified part**, in check order over every
record, one reader state throughout (the certified part's logical records are
read for the state only, as the certified entry reads them): an unsafe
inductive block by `readTierBlock` (its recursor and projection records with
it), every tier record, the certified part's included (its δ form joins the
answer view), by the tiered entry's own tier reader
(`Admission.readTierRecord`), every other record by the reader
(`Reader.readRecord`). -/
def readUncertified (cx : Ctx .anon) (pre : Prelude .anon)
    (ordered : Array (Address × Ixon.Constant × ByteArray)) (unc : Std.HashSet Address) :
    Except (Nat × ReadError) Uncertified := do
  let tierOwners : Std.HashSet Address := ordered.foldl
    (fun s (a, c, _) => if Ix.Kernel.Admission.isTierInfo c.info then s.insert a else s) {}
  let unsafeOwners : Std.HashSet Address := ordered.foldl
    (fun s (a, c, _) => if isUnsafeInductive c then s.insert a else s) {}
  let isTier (c : Ixon.Constant) : Bool := Ix.Kernel.Admission.isTierInfo c.info || match c.info with
    | .dPrj p => tierOwners.contains p.block
    | _ => false
  let mut out : Uncertified := { state := pre.state }
  for ((a, c, _), i) in ordered.zipIdx do
    let o := Ixon.CheckOrder.owner a c
    if unsafeOwners.contains o then
      -- an unsafe block, read with its recursors; its recursor and projection records go with it
      if let .muts ms := c.info then
        if ms.any (fun | .indc _ => true | _ => false) then
          match readTierBlock cx a c ms with
          | .ok rb => out := { out with tier := out.tier.push (i, .block (tierIndOf rb)) }
          | .error e => throw (i, e)
    else if isTier c then
      -- every tier record, the certified part's too: its δ form joins the answer view
      match Ix.Kernel.Admission.readTierRecord cx a c with
      | .ok (some d) => out := { out with tier := out.tier.push (i, .decl a d) }
      | .ok none => pure ()
      | .error e => throw (i, e)
    else
      match readRecord cx out.state a c with
      | .ok r =>
        out := { out with state := out.state.commit r }
        if unc.contains o && !r.decls.isEmpty then out := { out with safe := out.safe.push (i, r.decls) }
      | .error e => throw (i, e)
  return out

/-! ## Typing the uncertified part -/

/-- **A definition block over the answer view**, for a block the opaque
check (`Tier.checkDeclC`) refuses: Lean adds a block's members before it
checks their bodies, and unfolds tier definitions and fires unsafe
recursors while it does. With the block's δ forms `infos` in the view, each
value's type, inferred there, must be convertible to its header there. -/
def defsOverAnswers (av : Ix.Kernel.Tier.AnswerView .anon) (infos : List (Ix.Kernel.ConstantInfo .anon)) :
    Except (Ix.Kernel.CheckError .anon) Unit := do
  let knot := (av.pushInfos infos).knot
  for info in infos do
    if let .defnInfo cvA jv _ := info then
      let ok ← Ix.Kernel.Tier.runC (do
        let ty ← knot.infer 0 jv
        knot.defeq 0 ty cvA.type)
      unless ok do
        throw (.invalid msg!"the value of {cvA.name} does not have its declared type, \
          with tier definitions and unsafe recursors reducing")

/-- The headers a block's δ forms install, as tier constants (opaque). -/
def headerInfos (infos : List (Ix.Kernel.ConstantInfo .anon)) : List (Ix.Kernel.ConstantInfo .anon) :=
  infos.filterMap fun
    | .defnInfo cvA _ _ => some (.axiomInfo cvA)
    | _ => none

/-- **The uncertified fold** from the certified part's environment `env`
(the certified run's result, and nothing else of it), as `Uncertified` lists
it; a failure carries its record's position.

* The safe records: an assumption axiom by its header (`Tier.axiomC`), every
  other declaration by the fold's own phase A and B steps.
* The tier items, staged as Lean's lattice, against two indexes: the check
  index (tier constants opaque, as the batch tier checks) and the **answer
  view** (`Tier.AnswerView`: tier definitions with their δ forms, unsafe
  blocks with their recursors' typed rules). A definition block is checked
  first at the check index (`Tier.checkDeclC`); if that refuses, over the
  answer view (`defsOverAnswers`). Its δ forms (`Tier.defsAnswerC`, with the
  shipped hints) then join the view; the certified part's tier records come
  through here too, for their δ forms, re-checked. An unsafe opaque or axiom
  is checked at the check index only (Lean unfolds neither). An unsafe block
  is installed by `Tier.indC` in the check index and by
  `Tier.AnswerView.pushInd` (ι) in the view. -/
def checkUncertified (ev : Ix.Kernel.Evidences .anon) (env : Ix.Kernel.Env .anon)
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint) (u : Uncertified) :
    Except (Nat × Ix.Kernel.CheckError .anon) Unit := do
  -- the safe records: assumption axioms by their headers, the rest by the fold's steps
  let mut fe := Ix.Kernel.mkFEnv env
  let mut cs : Ix.Kernel.Cached.CState .anon := {}
  let mut pos := 0
  for (i, ds) in u.safe do
    for d in ds do
      match d with
      | .axiomDecl cv =>
        match Ix.Kernel.Tier.axiomC fe cv with
        | .ok (fe', _) => fe := fe'
        | .error e => throw (i, e)
      | _ =>
        match Ix.Kernel.Cached.annotDeclStep .verified ev (pos, fe, #[]) d cs with
        | .error (e, _) => throw (i, e)
        | .ok ((pos', fe', pend), cs') =>
          match Ix.Kernel.Cached.checkPendingList .verified fe' pend.toList with
          | .ok () =>
            fe := fe'
            cs := cs'
            pos := pos'
          | .error (e, _) => throw (i, e)
  -- the tier items, staged as Lean's lattice, from the safe view `fe`
  let fe₀ := fe
  let mut feT := fe
  let mut av := Ix.Kernel.Tier.AnswerView.ofLogical fe
  let staged := u.tier.filter (·.2.stage == 0) ++ u.tier.filter (·.2.stage == 1) ++
    u.tier.filter (·.2.stage == 2)
  for (i, item) in staged do
    match item with
    | .decl record d@(.defs _ ms) =>
      let withHints := ms.zipIdx.map fun ((cv, v), j) =>
        (cv, v, (hint (.member record j)).getD (.regular 0))
      match Ix.Kernel.Tier.checkDeclC fe₀ feT d with
      | .ok (fe', _) =>
        match Ix.Kernel.Tier.defsAnswerC feT withHints with
        | .ok infos =>
          feT := fe'
          av := av.pushInfos infos
        | .error e => throw (i, e)
      | .error _ =>
        match Ix.Kernel.Tier.defsAnswerC feT withHints with
        | .error e => throw (i, e)
        | .ok infos =>
          match defsOverAnswers av infos with
          | .error e => throw (i, e)
          | .ok () =>
            feT := Ix.Kernel.Tier.pushAll feT (headerInfos infos)
            av := av.pushInfos infos
    | .decl _ d =>
      match Ix.Kernel.Tier.checkDeclC fe₀ feT d with
      | .ok (fe', ts) =>
        feT := fe'
        av := av.pushInfos (Ix.Kernel.Tier.TierConst.infos ts)
      | .error e => throw (i, e)
    | .block b =>
      match Ix.Kernel.Tier.indC feT b with
      | .ok o =>
        feT := Ix.Kernel.Tier.pushAll feT o.checkInfos
        av := av.pushInd o
      | .error e => throw (i, e)

/-! ## The typing half -/

/-- The record a failure of the tiered entry is reported at, by its position
in `records`, when the failure has one. -/
def failureRecord (records : Ix.Kernel.Admission.Records) :
    Ix.Kernel.Admission.TierError → Option Address
  | .entry (.read p _) | .read p _ | .tier _ p => (records[p]?).map (·.1)
  | .entry (.decode _ a _) | .fence a _ => some a
  | _ => none

/-- The uncertified part's owners (`uncertifiedOwners`) under the input's
role table. -/
def splitOf (input : TypingInput) : Std.HashSet Address :=
  let store : Ixon.CheckOrder.RecordStore := input.ordered.foldl (fun m (a, c, _) => m.insert a c) {}
  let evidence : Std.HashMap Address Ixon.Constant := input.pre.evidence.foldl
    (fun m (a, c) => m.insert a c) {}
  let look : Store := fun a => store[a]? <|> (input.pre.records.find? (·.1 == a)).map (·.2) <|> evidence[a]?
  uncertifiedOwners (bindingsOf look input.table) input.ordered

/-- **The certified part**: IxC's tiered entry at BLAKE3 under the input's
actual binding and prelude, over every record outside `unc`, exactly as the
entry and its theorem (`Ix.Kernel.Admission.checkBytesTieredUsing_ok`) take it. Its result is
the installed logical environment; nothing here reads the answer view. A
failure says whether it is the batch tier's (`TierError.tier`). -/
def checkCertified (input : TypingInput) (unc : Std.HashSet Address) :
    Except (String × Bool) (Ix.Kernel.Env .anon) := do
  let records : Ix.Kernel.Admission.Records := input.ordered.toList.filterMap fun (a, c, b) =>
    if unc.contains (Ixon.CheckOrder.owner a c) then none else some (a, b)
  if input.bound then
    let constants := input.ordered.toList.filterMap fun (a, c, _) =>
      if unc.contains (Ixon.CheckOrder.owner a c) then none else some (a, c)
    let (logical, _) := Ix.Kernel.Admission.partitionTier constants
    let (evidence, declarations) ← (Ix.Kernel.Admission.readStream Address.admissionHash
      input.table input.pre logical input.blobs input.hint).mapError
        fun e => (s!"resource validator: bound evidence reading failed: {e}", false)
    (Ix.RoleBinding.Artifact.checkEvidence input.table evidence
      (Ix.Kernel.Frontend.preparePrelude input.pre.ix declarations)).mapError
        fun e => (s!"resource validator: {e}", false)
  match Ix.Kernel.Admission.checkBytesTieredUsing input.preludeFor Address.admissionHash input.binding typingLimits records
      input.blobs input.hint with
  | .ok (env, _) => pure env
  | .error e =>
    let site := match failureRecord records e with
      | some a => s!" at {a}"
      | none => ""
    let isTier := match e with | .tier .. => true | _ => false
    throw (s!"resource validator: erased typing failed{site}: {e}", isTier)

/-- **The uncertified part**, typed from the certified run's environment
`env` (its only input from that run): read (`readUncertified`), then checked
over the check index and the answer view (`checkUncertified`). -/
def typeUncertified (input : TypingInput) (unc : Std.HashSet Address) (env : Ix.Kernel.Env .anon) :
    Except String Unit := do
  let constants := input.ordered.toList.map fun (a, c, _) => (a, c)
  let cx := Ix.Kernel.Admission.streamContext Address.admissionHash input.table input.pre constants
    input.blobs input.hint
  let site (i : Nat) : String := ((input.ordered[i]?).map fun (a, _, _) => s!" at {a}").getD ""
  let u ← (readUncertified cx input.pre input.ordered unc).mapError fun (i, e) =>
    s!"resource validator: erased typing failed{site i} (uncertified part): read: {e}"
  let ev := evidenceOf cx u.state input.table
  (checkUncertified ev env input.hint u).mapError fun (i, e) =>
    s!"resource validator: erased typing failed{site i} (uncertified part): {e}"

/-- The owners of the tier records (`Admission.isTierInfo`) and of their
definition projections. -/
def tierOwnersOf (input : TypingInput) : Std.HashSet Address :=
  input.ordered.foldl (fun s (a, c, _) => if Ix.Kernel.Admission.isTierInfo c.info then s.insert a else s) {}

/-- **The typing half** of the resource validator: the certified part
(`checkCertified`), then, when there is one, the uncertified part from its
result (`typeUncertified`). When the batch tier refuses a tier record (it
keeps tier constants opaque, where Lean unfolds tier definitions), the
certified part is the logical records alone, and every tier record joins the
uncertified part, typed transparently. A failure is `resource validator:
erased typing failed`, with IxC's error and, where it has one, the failing
record; an uncertified part's failure says so. -/
def typeCheck (env : Ixon.Env) : Except String Unit := do
  let input ← (typingInput env).mapError (s!"resource validator: erased typing failed: {·}")
  let unc := splitOf input
  match checkCertified input unc with
  | .ok env₀ => unless unc.isEmpty do typeUncertified input unc env₀
  | .error (e, isTier) =>
    unless isTier do throw e
    let unc := (tierOwnersOf input).fold (·.insert ·) unc
    let env₀ ← (checkCertified input unc).mapError (·.1)
    typeUncertified input unc env₀

end Ix.Resource

end
