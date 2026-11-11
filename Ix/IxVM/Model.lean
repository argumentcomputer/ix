module

public import Ix.Ixon
public import Ix.Common
public import Ix.Ixon.CheckOrder
public import IxC.Kernel.Admission
public import IxC.Kernel.Ixon.Prelude
public import Aiur.Ixon

/-!
# Model advice for IxVM's modeled route

IxVM checks a mutual or nested inductive block the way the certified kernel's
modeled install does (`IxC/Kernel/Inductives/Modeled.lean`): against a *model*
of the block, made of ordinary declarations that IxVM type-checks (a tag
enumeration and an auxiliary indexed family, both plain inductives on the
native route; a `_model` definition per type, constructor and recursor; an
`iota_j` theorem per recursor rule; for nested blocks the pack/unpack
isomorphisms). The circuit side is `IxVM/IxVM/Source/KernelModeled.lean`.

The model is **untrusted prover-side advice**. It is generated here by the
certified kernel's own in-process modeller (`IxC/Kernel/Frontend/InModel`),
reached through the kernel's Ixon reader (`Ix.Kernel.Reader.readRecord`, which
calls the modeller for every mutual or nested block it reads), and encoded back
into Ixon records. Nothing binds the model to the block by hashing: IxVM checks
whatever model the prover supplies (`KernelModeled::check_family`).

**The model is witness, never input.** The claim, its digest, the claimed
environment and the `.ixe` file are the same with or without it. `attach` fills
prover-side fields of `Ixon.Env` that are never serialized and that no claim
builder reads (`consts` and `blobs` are untouched):

* `Env.modelRecords` (with `Env.modelHints`, `Env.modelBlobs`): the generated
  records, served on the IO store like any record (channel 2, hash-checked by
  IxVM when loaded; definitions' hints on channel 3; literal blobs on 4);
* `Env.models`: per modeled block (keyed by its `muts` address), the payload IxVM
  reads on channel 7, in `KernelModeled`'s layout: the recursor family record,
  the advice records, the witnessed outside references, then the models of the
  types, constructors and recursors and the `iota_j` theorems;
* `Env.modelDeps`: per modeled block, the advice records and the container
  recursors the payload names, for the witness byte scope of a run.
-/

public section

namespace IxVM.Model

open Ix.Kernel (Key Expr Level ConstantInfo ConstantVal Declaration ConstRef auxKey)

/-! ## Encoding kernel declarations as Ixon records -/

/-- The tables of the record being encoded. -/
structure Enc where
  refs : Array Address := #[]
  refIdx : Std.HashMap Address Nat := {}
  univs : Array Ixon.Univ := #[]
  univIdx : Std.HashMap Ixon.Univ Nat := {}
  blobs : Array (Address × ByteArray) := #[]

abbrev EncM := StateT Enc (Except String)

def refOf (a : Address) : EncM UInt64 := do
  let s ← get
  match s.refIdx[a]? with
  | some i => pure i.toUInt64
  | none =>
    set { s with refs := s.refs.push a, refIdx := s.refIdx.insert a s.refs.size }
    pure s.refs.size.toUInt64

def univOf (u : Ixon.Univ) : EncM UInt64 := do
  let s ← get
  match s.univIdx[u]? with
  | some i => pure i.toUInt64
  | none =>
    set { s with univs := s.univs.push u, univIdx := s.univIdx.insert u s.univs.size }
    pure s.univs.size.toUInt64

def blobOf (bytes : ByteArray) : EncM UInt64 := do
  let a := Address.blake3 bytes
  modify fun s => { s with blobs := s.blobs.push (a, bytes) }
  refOf a

/-- A level over the declaration's parameters `lps` (kernel positions), as an
Ixon universe: a parameter is its index in `lps` (Ixon's level variables are
the declaration's parameters in declaration order; a large eliminator's
elimination level comes first, as the reader numbers it). -/
def encLevel (lps : List Nat) : Level → Except String Ixon.Univ
  | .zero => .ok .zero
  | .succ u => .succ <$> encLevel lps u
  | .max u v => return .max (← encLevel lps u) (← encLevel lps v)
  | .imax u v => return .imax (← encLevel lps u) (← encLevel lps v)
  | .param p => match lps.findIdx? (· == p) with
    | some i => .ok (.var i.toUInt64)
    | none => .error s!"level parameter {p} is not declared"

/-- How keys resolve to addresses: generated keys to the records encoded so
far, role keys to the role table's addresses, input keys to themselves. -/
structure Names where
  roles : Std.HashMap Ix.Kernel.Role Address := {}
  gen : Std.HashMap (Key .anon) Address := {}

def Names.addr (nm : Names) (k : Key .anon) : Except String Address :=
  match nm.gen[k]? with
  | some a => .ok a
  | none => match k with
    | .id a => .ok a
    | .role r => (match nm.roles[r]? with
      | some a => .ok a
      | none => .error s!"role {repr r} is not bound")
    | .aux .. => .error s!"generated key {k} is referenced before it is encoded"

def liftExcept {α} (x : Except String α) : EncM α := match x with
  | .ok a => pure a
  | .error e => throw e

partial def encExpr (nm : Names) (lps : List Nat) (self : Key .anon → Option Nat) :
    Expr .anon → EncM Ixon.Expr
  | .bvar i => pure (.var i.toUInt64)
  | .fvar .. => throw "free variable in a generated record"
  | .sort u => do pure (.sort (← univOf (← liftExcept (encLevel lps u))))
  | .const k us => do
    let uis ← us.toArray.mapM fun u => do univOf (← liftExcept (encLevel lps u))
    match self k with
    | some i => pure (.recur i.toUInt64 uis)
    | none => pure (.ref (← refOf (← liftExcept (nm.addr k))) uis)
  | .app f a => return .app (← encExpr nm lps self f) (← encExpr nm lps self a)
  | .lam t b _ => return .leanLam (← encExpr nm lps self t) (← encExpr nm lps self b)
  | .forallE t b _ => return .leanAll (← encExpr nm lps self t) (← encExpr nm lps self b)
  | .letE t v b _ =>
    return .leanLet false (← encExpr nm lps self t) (← encExpr nm lps self v) (← encExpr nm lps self b)
  | .lit (.natVal n) => return .nat (← blobOf (ByteArray.mk (Nat.toBytesLE n)))
  | .lit (.strVal s) => return .str (← blobOf s.toUTF8)
  | .proj s i e => do
    let si ← refOf (← liftExcept (nm.addr s))
    return .prj si i.toUInt64 (← encExpr nm lps self e)

def addressOf (c : Ixon.Constant) : Address := Address.blake3 (Ixon.ser c)

def projRecord (info : Ixon.ConstantInfo) : Ixon.Constant := ⟨info, #[], #[], #[]⟩

def hintOf : Ix.Kernel.ReducibilityHint → Lean.ReducibilityHints
  | .opaque => .opaque
  | .abbrev => .abbrev
  | .regular h => .regular h.toUInt32

/-- The number of leading `∀` binders of a type. -/
def piCount : Expr .anon → Nat
  | .forallE _ b _ => piCount b + 1
  | _ => 0

/-- The body after `n` leading `∀` binders. -/
def piBody : Nat → Expr .anon → Option (Expr .anon)
  | 0, e => some e
  | n + 1, .forallE _ b _ => piBody n b
  | _, _ => none

/-- Records produced by encoding one generated declaration: each record with
its address, the keys it declares, the hint of a definition, literal blobs. -/
structure Encoded where
  records : Array (Address × Ixon.Constant) := #[]
  keys : Array (Key .anon × Address) := #[]
  hints : Array (Address × Lean.ReducibilityHints) := #[]
  blobs : Array (Address × ByteArray) := #[]

def encDefinition (nm : Names) (cv : ConstantVal .anon) (value : Expr .anon) (kind : Ix.DefKind)
    (hint : Option Ix.Kernel.ReducibilityHint) : Except String Encoded := do
  let lps := cv.levelParams
  let ((typ, v), s) ← (do
      let t ← encExpr nm lps (fun _ => none) cv.type
      let v ← encExpr nm lps (fun _ => none) value
      pure (t, v) : EncM _).run {}
  let c : Ixon.Constant := ⟨.defn { kind := kind, safety := .safe, lvls := lps.length.toUInt64, typ, value := v },
    #[], s.refs, s.univs⟩
  let a := addressOf c
  return { records := #[(a, c)], keys := #[(cv.name, a)], blobs := s.blobs,
           hints := match hint with | some h => #[(a, hintOf h)] | none => #[] }

/-- A generated one-type inductive block (the tag or the auxiliary family):
the `muts` record, its type and constructor projection records, and its
recursor as a top-level record. -/
def encInductive (nm : Names) (block : List (ConstantInfo .anon)) (nP : Nat) : Except String Encoded := do
  let tys := block.filterMap fun ci => match ci with | .indInfo cv _ => some cv | _ => none
  let ctors := block.filterMap fun ci => match ci with | .ctorInfo cv cP cF => some (cv, cP, cF) | _ => none
  let recs := block.filterMap fun ci => match ci with
    | .recInfo cv mI rP rules => some (cv, mI, rP, rules) | _ => none
  let [cvT] := tys | throw s!"generated inductive block with {tys.length} types"
  let nIdx := piCount cvT.type - nP
  let lps := cvT.levelParams
  let self : Key .anon → Option Nat := fun k => if k == cvT.name then some 0 else none
  let ((typ, ctorRecs), s) ← (do
      let t ← encExpr nm lps self cvT.type
      let mut cs : Array Ixon.Constructor := #[]
      let mut j : Nat := 0
      for (cv, cP, cF) in ctors do
        unless cv.levelParams == lps do throw s!"constructor {cv.name}: level parameters differ"
        let ct ← encExpr nm lps self cv.type
        cs := cs.push { isUnsafe := false, lvls := lps.length.toUInt64, cidx := j.toUInt64,
                        params := cP.toUInt64, fields := cF.toUInt64, typ := ct }
        j := j + 1
      pure (t, cs) : EncM _).run {}
  let ind : Ixon.Inductive := { isUnsafe := false, lvls := lps.length.toUInt64, params := nP.toUInt64,
                                indices := nIdx.toUInt64, typ, ctors := ctorRecs }
  let blockC : Ixon.Constant := ⟨.muts #[.indc ind], #[], s.refs, s.univs⟩
  let blockA := addressOf blockC
  let iprj := projRecord (.iPrj ⟨0, blockA⟩)
  let iprjA := addressOf iprj
  let mut out : Encoded := { records := #[(blockA, blockC), (iprjA, iprj)], keys := #[(cvT.name, iprjA)],
                             blobs := s.blobs }
  let mut j : Nat := 0
  for (cv, _, _) in ctors do
    let cprj := projRecord (.cPrj ⟨0, j.toUInt64, blockA⟩)
    let cprjA := addressOf cprj
    out := { out with records := out.records.push (cprjA, cprj), keys := out.keys.push (cv.name, cprjA) }
    j := j + 1
  -- the recursor, against the names declared so far (the type and constructors)
  let nm' : Names := { nm with gen := out.keys.foldl (fun m (k, a) => m.insert k a) nm.gen }
  for (cvR, mI, rP, rules) in recs do
    let rlps := cvR.levelParams
    let rself : Key .anon → Option Nat := fun k => if k == cvR.name then some 0 else none
    let ((rtyp, rrules), rs) ← (do
        let t ← encExpr nm' rlps rself cvR.type
        let rr ← rules.toArray.mapM fun (r : Ix.Kernel.RecRule .anon) => do
          pure ({ fields := r.nfields.toUInt64, rhs := ← encExpr nm' rlps rself r.rhs } : Ixon.RecursorRule)
        pure (t, rr) : EncM _).run {}
    -- K-like: a `Prop` family with one constructor and no fields (Lean's `is_K_target`)
    let isProp := match piBody (nP + nIdx) cvT.type with
      | some (.sort .zero) => true
      | _ => false
    let k := isProp && ctors.length == 1 && ctors.all (fun (_, _, cF) => cF == 0)
    let recR : Ixon.Recursor :=
      { k := k, isUnsafe := false, lvls := rlps.length.toUInt64,
        params := nP.toUInt64, indices := (mI - rP).toUInt64, motives := 1,
        minors := ctors.length.toUInt64, typ := rtyp, rules := rrules }
    let recC : Ixon.Constant := ⟨.recr recR, #[], rs.refs, rs.univs⟩
    let recA := addressOf recC
    out := { out with records := out.records.push (recA, recC), keys := out.keys.push (cvR.name, recA),
                      blobs := out.blobs ++ rs.blobs }
  return out

def encDecl (nm : Names) : Declaration .anon → Except String Encoded
  | .defnDecl cv v h => encDefinition nm cv v .defn (some h)
  | .thmDecl cv v => encDefinition nm cv v .thm none
  | .indDecl block nP => encInductive nm block nP
  | _ => .error "unexpected generated record kind"

/-! ## Outside references and their witnesses -/

/-- The basis roles a payload may name (`KernelModeled::basis_role_allowed`):
`Nat` and its constructors and recursor, `Eq`, `Eq.refl`, `Eq.rec`, `PUnit`,
`PUnit.unit`, `PUnit.rec`, the quotient (`Quot`, `Quot.mk`, `Quot.lift`,
`Quot.ind`, `Quot.sound`, from which function extensionality is a theorem),
`String`, `Char`. -/
def basisRoleAllowed (r : Nat) : Bool :=
  [0, 1, 2, 3, 8, 9, 10, 11, 12, 13, 32, 33, 34, 35, 36, 37, 39].contains r

/-- The `refs` indices a record uses as constants (`KernelClaim::const_idxs_of`). -/
partial def usedIdxsExpr : Ixon.Expr → Std.HashSet Nat
  | .ref i _ => ({} : Std.HashSet Nat).insert i.toNat
  | .prj i _ inner => (usedIdxsExpr inner).insert i.toNat
  | .app a b | .lam _ a b | .all _ _ a b => (usedIdxsExpr a).union (usedIdxsExpr b)
  | .letE _ t v b => ((usedIdxsExpr t).union (usedIdxsExpr v)).union (usedIdxsExpr b)
  | _ => {}

def usedIdxs (c : Ixon.Constant) : Std.HashSet Nat := Id.run do
  let mut out : Std.HashSet Nat := {}
  for e in c.sharing do out := out.union (usedIdxsExpr e)
  let ofDefn (d : Ixon.Definition) := (usedIdxsExpr d.typ).union (usedIdxsExpr d.value)
  let ofRecr (r : Ixon.Recursor) := r.rules.foldl
    (fun acc rule => acc.union (usedIdxsExpr rule.rhs)) (usedIdxsExpr r.typ)
  let ofIndc (i : Ixon.Inductive) := i.ctors.foldl
    (fun acc ctor => acc.union (usedIdxsExpr ctor.typ)) (usedIdxsExpr i.typ)
  match c.info with
  | .defn d => out := out.union (ofDefn d)
  | .recr r => out := out.union (ofRecr r)
  | .axio a => out := out.union (usedIdxsExpr a.typ)
  | .quot q => out := out.union (usedIdxsExpr q.typ)
  | .muts members =>
    for m in members do
      out := out.union <| match m with
        | .defn d => ofDefn d
        | .indc i => ofIndc i
        | .recr r => ofRecr r
  | _ => pure ()
  return out

def projectionBlock? (c : Ixon.Constant) : Option Address :=
  match c.info with
  | .iPrj p => some p.block
  | .cPrj p => some p.block
  | .rPrj p => some p.block
  | .dPrj p => some p.block
  | _ => none

/-- Breadth-first search of the dependency closure the claim walk visits from
`root` (used references, projection to block), recording each record's
predecessor and step (`0` projection to block, `j + 1` the `j`-th reference). -/
def depsSearch (look : Address → Option Ixon.Constant) (root : Address) (limit : Nat := 400000) :
    Std.HashMap Address (Address × Nat) := Id.run do
  let mut parent : Std.HashMap Address (Address × Nat) := {}
  let mut seen : Std.HashSet Address := ({} : Std.HashSet Address).insert root
  let mut queue : Array Address := #[root]
  let mut head := 0
  while head < queue.size && head < limit do
    let a := queue[head]!
    head := head + 1
    let some c := look a | continue
    let mut nexts : Array (Address × Nat) := #[]
    if let some b := projectionBlock? c then nexts := nexts.push (b, 0)
    let used := usedIdxs c
    for (r, j) in c.refs.zipIdx do
      if used.contains j then nexts := nexts.push (r, j + 1)
    for (n, st) in nexts do
      unless seen.contains n do
        seen := seen.insert n
        parent := parent.insert n (a, st)
        queue := queue.push n
  return parent

/-- The steps from the search root to `x`, if the search reached it. -/
partial def pathTo (parent : Std.HashMap Address (Address × Nat)) (root x : Address) :
    Option (List Nat) :=
  if x == root then some []
  else match parent[x]? with
    | some (p, st) => (pathTo parent root p).map (· ++ [st])
    | none => none

/-! ## Payloads -/

def putAddr (b : ByteArray) (a : Address) : ByteArray := b ++ a.hash
def putN (b : ByteArray) (n : Nat) : ByteArray := Aiur.Ixon.tagN0 b n.toUInt64

/-- A payload, structured (`KernelModeled`'s layout): the recursor family
record, the advice records, the witnessed outside references (address, kind,
dependency path), the models of the types, constructors and recursors, and the
`iota_j` theorems. `adviceCount` overrides the advice count written (tests). -/
structure Payload where
  recBlock : Address
  advice : Array Address
  witnesses : Array (Address × Nat × List Nat × List Nat)
  typeModels : Array Address
  ctorModels : Array Address
  recModels : Array Address
  iotas : Array Address
  adviceCount : Option Nat := none
  deriving Inhabited

def Payload.ser (p : Payload) : ByteArray := Id.run do
  let mut b := putAddr ByteArray.empty p.recBlock
  b := putN b (p.adviceCount.getD p.advice.size)
  for a in p.advice do b := putAddr b a
  b := putN b p.witnesses.size
  for (x, kind, steps, extra) in p.witnesses do
    b := (putAddr b x).push kind.toUInt8
    unless kind == 0 do b := steps.foldl putN (putN b steps.length)
    b := extra.foldl putN b
  for a in p.typeModels ++ p.ctorModels ++ p.recModels ++ p.iotas do b := putAddr b a
  return b

/-- One block's advice, ready to attach. -/
structure BlockAdvice where
  layout : Payload
  records : Array (Address × Ixon.Constant)
  hints : Array (Address × Lean.ReducibilityHints)
  blobs : Array (Address × ByteArray)
  deps : Array Address

def BlockAdvice.payload (a : BlockAdvice) : ByteArray := a.layout.ser

/-- The reader's keys for the public members of block `b` and of its recursor
family, with the family record and each recursor's rule count. -/
structure FamilyKeys where
  recBlock : Address
  types : Array (Key .anon)
  ctors : Array (Key .anon)
  recs : Array (Key .anon × Nat)

def readKey (x : Ix.Kernel.Reader.ReadM (Key .anon)) : Except String (Key .anon) :=
  match x with
  | .ok k => .ok k
  | .error _ => .error "the reader has no key for a member"

def familyKeys (cx : Ix.Kernel.Reader.Ctx .anon) (b : Address) (bc : Ixon.Constant)
    (shape : Ix.Kernel.Reader.BlockShape) : Except String FamilyKeys := do
  let .muts ms := bc.info | throw "the block is not a muts record"
  let mut types := #[]
  let mut ctors := #[]
  for (m, p) in ms.zipIdx do
    let .indc ind := m | throw "a block member is not an inductive"
    types := types.push (← readKey (cx.memberKey (.member b p)))
    for j in [0:ind.ctors.size] do
      ctors := ctors.push (← readKey (cx.memberKey (.ctor b p j)))
  let owners := shape.recs.foldl (fun acc (r : ConstRef Address) => match r with
    | .member o _ => if acc.contains o then acc else acc.push o
    | _ => acc) #[]
  let #[rb] := owners | throw s!"the recursor family spans {owners.size} records"
  let some rbc := cx.store rb | throw "the recursor family record is missing"
  let recRefs : Array (Nat × Nat) := match rbc.info with
    | .muts rms => (rms.zipIdx).map fun (m, j) => (match m with
      | .recr rr => (j, rr.rules.size)
      | _ => (j, 0))
    | .recr rr => #[(0, rr.rules.size)]
    | _ => #[]
  let mut recs := #[]
  for (j, n) in recRefs do
    recs := recs.push (← readKey (cx.memberKey (.member rb j)), n)
  return { recBlock := rb, types, ctors, recs }

/-- The advice of one block, from the declarations the reader generated for it. -/
def blockAdvice (table : Ix.Kernel.RoleTable) (look : Address → Option Ixon.Constant)
    (cx : Ix.Kernel.Reader.Ctx .anon) (b : Address) (bc : Ixon.Constant)
    (shape : Ix.Kernel.Reader.BlockShape) (gen : List (Declaration .anon))
    (tweak : Declaration .anon → Declaration .anon := id) :
    Except String BlockAdvice := do
  let fk ← familyKeys cx b bc shape
  let roles : Std.HashMap Ix.Kernel.Role Address := table.bound.foldl (fun m (r, a) => m.insert r a) {}
  let mut nm : Names := { roles := roles }
  let mut records : Array (Address × Ixon.Constant) := #[]
  let mut hints : Array (Address × Lean.ReducibilityHints) := #[]
  let mut blobs : Array (Address × ByteArray) := #[]
  for d in gen.map tweak do
    let e ← encDecl nm d
    for rc in e.records do
      unless records.any (·.1 == rc.1) do records := records.push rc
    hints := hints ++ e.hints
    blobs := blobs ++ e.blobs
    nm := { nm with gen := e.keys.foldl (fun m (k, x) => m.insert k x) nm.gen }
  let aset : Std.HashSet Address := records.foldl (fun s (a, _) => s.insert a) {}
  -- outside references: used references that are not advice
  let mut outside : Array Address := #[]
  for (_, c) in records do
    let used := usedIdxs c
    for (r, j) in c.refs.zipIdx do
      unless used.contains j do continue
      if aset.contains r || outside.contains r then continue
      outside := outside.push r
  let parent := depsSearch look b
  -- a path of one step or more: the block itself is not in its closure
  let pathFrom (x : Address) : Option (List Nat) := (pathTo parent b x).filter (!·.isEmpty)
  let roleOf (x : Address) : Option Nat := do
    let (r, _) ← table.bound.find? (·.2 == x)
    Ix.Kernel.Role.all.idxOf? r
  -- the witness of one outside reference: (address, kind, path, extra)
  let classify (x : Address) : Except String (Address × Nat × List Nat × List Nat) := do
    if let some steps := pathFrom x then
      return (x, 1, steps, [])
    else if (roleOf x).any basisRoleAllowed then
      return (x, 0, [], [])
    else if let some (pb, idx, c1) := (look x).bind (fun c => match c.info with
        | .iPrj p => some (p.block, p.idx.toNat, 0)
        | .cPrj p => some (p.block, p.idx.toNat, p.cidx.toNat + 1)
        | _ => none) then
      -- a type or constructor of a block in the closure (its block's walk checks it)
      let some steps := pathFrom pb
        | throw s!"outside projection {x} is of a block outside the closure"
      return (x, 3, steps, [idx, c1])
    else
      -- a container's recursor: a recursor of a block in the closure
      let ref? : Option (ConstRef Address) := (look x).bind fun c => match c.info with
        | .recr _ => some (.member x 0)
        | .rPrj p => some (.member p.block p.idx.toNat)
        | _ => none
      let some ref := ref? | throw s!"outside reference {x} is neither in the closure nor a basis role"
      let some entry := cx.index.recs[ref]? | throw s!"outside recursor {x} is not indexed"
      let some steps := pathFrom entry.block
        | throw s!"outside recursor {x} eliminates a block outside the closure"
      return (x, 2, steps, [])
  let mut deps : Array Address := (records.map (·.1)).push fk.recBlock
  let mut witnesses : Array (Address × Nat × List Nat × List Nat) := #[]
  for x in outside do
    let w ← classify x
    witnesses := witnesses.push w
    if w.2.1 == 2 then deps := deps.push x
  -- the references of a container's recursor family that the circuit cannot place by
  -- the container's block alone (`KernelModeled::container_refs_ok`: the block's
  -- references, its members, members of the blocks its used references project
  -- from) are witnessed too (Array.mk's List under a nested container)
  let mut extra : Array Address := #[]
  for (x, k, _, _) in witnesses do
    unless k == 2 do continue
    let some xc := look x | continue
    let pr : Option Ixon.Constant × Option (ConstRef Address) := match xc.info with
      | .rPrj p => (look p.block, some (.member p.block p.idx.toNat))
      | _ => (some xc, some (.member x 0))
    let (fam?, ref?) := pr
    let some fam := fam? | continue
    let some ref := ref? | continue
    let some entry := cx.index.recs[ref]? | continue
    let some ibc := look entry.block | continue
    let iused := usedIdxs ibc
    let irefBlocks : Array Address := ibc.refs.zipIdx.filterMap fun (q, j) =>
      if iused.contains j then (look q).bind projectionBlock? else none
    let used := usedIdxs fam
    for (r, j) in fam.refs.zipIdx do
      unless used.contains j do continue
      if ibc.refs.contains r || outside.contains r || extra.contains r then continue
      let rc? := look r
      if (rc?.bind projectionBlock?) == some entry.block then continue
      let icBlock : Option Address := rc?.bind fun c => match c.info with
        | .iPrj p => some p.block
        | .cPrj p => some p.block
        | _ => none
      if icBlock.any irefBlocks.contains then continue
      extra := extra.push r
  for x in extra do
    let w ← classify x
    witnesses := witnesses.push w
    if w.2.1 == 2 then deps := deps.push x
  -- the member models and the iota theorems, in the circuit's order
  let modelOf (k : Key .anon) : Except String Address :=
    match nm.gen[auxKey k .model]? with
    | some a => pure a
    | none => throw s!"no model for {k}"
  let typeModels ← fk.types.mapM modelOf
  let ctorModels ← fk.ctors.mapM modelOf
  let recModels ← fk.recs.mapM (modelOf ·.1)
  let mut iotas : Array Address := #[]
  for (k, n) in fk.recs do
    for j in [0:n] do
      let some t := nm.gen[auxKey (auxKey k .model) (.iota j)]? | throw s!"no iota_{j} for {k}"
      iotas := iotas.push t
  let layout : Payload := { recBlock := fk.recBlock, advice := records.map (·.1), witnesses,
                            typeModels, ctorModels, recModels, iotas }
  return { layout, records, hints, blobs, deps }

/-! ## Attaching the models -/

/-- `env` with an empty payload for every inductive block that has none: a
mutual or nested block the modeller could not model (or one without its
recursor family) is then refused by the circuit (`KernelModeled`, "no model
advice") rather than by a witness that lacks data. A native block's payload is
never read. -/
def withEmptyPayloads (env : Ixon.Env) : Ixon.Env := Id.run do
  let mut env := env
  for (a, lc) in env.consts do
    if env.models.contains a then continue
    if let some c := lc.get? then
      if let .muts ms := c.info then
        if ms.any (fun m => match m with | .indc _ => true | _ => false) then
          env := { env with models := env.models.insert a ByteArray.empty }
  return env

/-- What the attach step did, per block: the advice's record count and outside
references by witness kind, or why the block has no model. -/
structure Report where
  blocks : Array (Address × Except String (Nat × Array (Address × Nat))) := #[]
  /-- the advice attached, per block (tests corrupt it) -/
  advice : Array (Address × BlockAdvice) := #[]

/-- The models of every mutual or nested inductive block of `env` the kernel's
reader models, attached as records and prover-side indexes, with a report.
Blocks whose reading or encoding fails (a decline or a rejection of the reader,
an unsafe block) get no model, and IxVM rejects them. -/
def generateReport (env : Ixon.Env) (tweak : Declaration .anon → Declaration .anon := id) :
    Except String (Ixon.Env × Report) := do
  -- an environment whose binding or prelude does not read gets no model (its claims
  -- are decided without one: a modeled block in them is refused)
  let fallback := ({ withEmptyPayloads env with modelsAttached := true }, ({} : Report))
  let table? : Option Ix.Kernel.RoleTable := match env.roleBinding with
    | some b => Ix.Kernel.RoleTable.ofBytes b.bytes
    | none => Ix.Kernel.Reader.defaultTable.toOption
  let some table := table? | return fallback
  let .ok (pre : Ix.Kernel.Reader.Prelude .anon) := Ix.Kernel.Reader.preludeFor table | return fallback
  let mut records : Array (Address × Ixon.Constant) := #[]
  for (a, lc) in env.consts do
    if let some c := lc.get? then records := records.push (a, c)
  let cx : Ix.Kernel.Reader.Ctx .anon :=
    Ix.Kernel.Reader.contextOf table records env.blobs.toList (pre.records ++ pre.evidence) pre.blobs
      (fun _ => none) (Ix.Kernel.Admission.projectionAddress Address.blake3)
  -- the modeled blocks: several types, or more recursors than types (nested)
  let mut roots : Array Address := #[]
  let mut extra : Std.HashMap Address (Array Address) := {}
  for (b, shape) in cx.index.blocks do
    let recBlocks := shape.recs.foldl (fun acc (r : ConstRef Address) => match r with
      | .member o _ => if acc.contains o then acc else acc.push o
      | _ => acc) #[]
    extra := extra.insert b recBlocks
    if shape.order.size > 1 || shape.recs.size > shape.order.size then roots := roots.push b
  if roots.isEmpty then return ({ withEmptyPayloads env with modelsAttached := true }, {})
  let store : Ixon.CheckOrder.RecordStore := records.foldl (fun m (a, c) => m.insert a c) {}
  let look (a : Address) : Option Ixon.Constant := store[a]? <|> cx.store a
  let owners : Std.HashSet Address :=
    (Ixon.CheckOrder.closure store extra roots).foldl (·.insert ·) {}
  let sub := records.filter fun (a, c) => owners.contains (Ixon.CheckOrder.owner a c)
  let ordered := Ixon.CheckOrder.wholeEnv table pre sub
  let rootSet : Std.HashSet Address := roots.foldl (·.insert ·) {}
  let mut st := pre.state
  let mut env := env
  let mut report : Report := {}
  for a in ordered do
    let some c := store[a]? | continue
    match Ix.Kernel.Reader.readRecord cx st a c with
    | .error why =>
      if rootSet.contains a then report := { report with blocks := report.blocks.push (a, .error s!"the reader: {why}") }
    | .ok r =>
      st := st.commit r
      unless rootSet.contains a do continue
      if r.generated == 0 then
        report := { report with blocks := report.blocks.push (a, .error "the reader generated no model")}
        continue
      let some shape := cx.index.blocks[a]? | continue
      match blockAdvice table look cx a c shape (r.decls.toList.take r.generated) tweak with
      | .error e => report := { report with blocks := report.blocks.push (a, .error e) }
      | .ok adv =>
        for (ra, rc) in adv.records do
          env := { env with modelRecords := env.modelRecords.insert ra rc }
        for (ha, h) in adv.hints do
          env := { env with modelHints := env.modelHints.insert ha h }
        for (ba, bytes) in adv.blobs do
          unless env.blobs.contains ba do env := { env with modelBlobs := env.modelBlobs.insert ba bytes }
        env := { env with models := env.models.insert a adv.payload,
                          modelDeps := env.modelDeps.insert a adv.deps }
        report := { report with
          blocks := report.blocks.push (a, .ok (adv.records.size, adv.layout.witnesses.map fun (x, k, _, _) => (x, k))),
          advice := report.advice.push (a, adv) }
  return ({ withEmptyPayloads env with modelsAttached := true }, report)

def generate (env : Ixon.Env) : Except String Ixon.Env := (·.1) <$> generateReport env

/-- `generate`, once per environment. -/
def attach (env : Ixon.Env) : Except String Ixon.Env :=
  if env.modelsAttached then .ok env else generate env

end IxVM.Model

end
