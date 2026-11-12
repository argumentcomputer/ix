module

public import Ix.Ixon
public import Ix.Common
public import Ix.Ixon.CheckOrder
public import IxC.Kernel.Admission
public import IxC.Kernel.Ixon.Prelude
public import Aiur.Ixon
public import Ix.CompileM
public import Ix.IxVM.RecordSections

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

def projRecord (info : Ixon.ConstantInfo) : Ixon.Constant := ⟨info, #[], #[], #[], #[]⟩

/-- `e` with every index into the record's refs table moved by `f`: a reference, a
projection's structure, a literal's blob. -/
def remapRefs (f : UInt64 → UInt64) : Ixon.Expr → Ixon.Expr
  | .ref i us => .ref (f i) us
  | .prj t i v => .prj (f t) i (remapRefs f v)
  | .str i => .str (f i)
  | .nat i => .nat (f i)
  | .app a b => .app (remapRefs f a) (remapRefs f b)
  | .lam bc t b => .lam bc (remapRefs f t) (remapRefs f b)
  | .all bc vc t b => .all bc vc (remapRefs f t) (remapRefs f b)
  | .letE lc t v b => .letE lc (remapRefs f t) (remapRefs f v) (remapRefs f b)
  | e => e

/-- `e` with every index into the record's univs table moved by `f`: a sort's level
and the universe arguments of a reference or of a recursive reference. -/
def remapUnivs (f : UInt64 → UInt64) : Ixon.Expr → Ixon.Expr
  | .sort i => .sort (f i)
  | .ref i us => .ref i (us.map f)
  | .recur i us => .recur i (us.map f)
  | .prj t i v => .prj t i (remapUnivs f v)
  | .app a b => .app (remapUnivs f a) (remapUnivs f b)
  | .lam bc t b => .lam bc (remapUnivs f t) (remapUnivs f b)
  | .all bc vc t b => .all bc vc (remapUnivs f t) (remapUnivs f b)
  | .letE lc t v b => .letE lc (remapUnivs f t) (remapUnivs f v) (remapUnivs f b)
  | e => e

/-- The compiler's univs table for the levels `univs` (`Ix.CompileM.preseedExprTables`):
each in its canonical form (`Ixon.canonUniv`), sorted by encoding
(`Ix.CompileM.univSortKey`), each once; with the new index of each old one. -/
def canonicalUnivs (univs : Array Ixon.Univ) : Array Ixon.Univ × (UInt64 → UInt64) :=
  let canon := univs.map Ixon.canonUniv
  let keyed := (canon.map fun u => (Ix.CompileM.univSortKey u, u)).qsort
    fun (ka, _) (kb, _) => Ix.CompileM.byteArrayCmp ka kb == .lt
  let table : Array Ixon.Univ :=
    keyed.foldl (fun acc (_, u) => if acc.back? == some u then acc else acc.push u) #[]
  let pos : Std.HashMap Ixon.Univ UInt64 :=
    table.zipIdx.foldl (fun m (u, i) => m.insert u i.toUInt64) {}
  (table, fun i => ((canon[i.toNat]?).bind (pos[·]?)).getD i)

/-- A generated record with the compiler's tables and canonical sharing: the refs
sorted by address bytes and the levels canonical and sorted by encoding, as the
compiler preseeds them, every index into either table moved with it, then
`Ix.CompileM.buildConstantWithSharing`. A generated record that is alpha-equivalent
to a compiled one (a block's tag enumeration and a Lean enumeration of its size) is then the same record whatever order
the encoder met its references and levels in. Its binder data come later, per block
(`BlockAdvice.withSections`). -/
def sharedRecord (info : Ixon.ConstantInfo) (refs : Array Address) (univs : Array Ixon.Univ) :
    Except String Ixon.Constant := do
  let sorted := refs.qsort fun a b => a.cmpBytes b == .lt
  let pos : Std.HashMap Address UInt64 :=
    sorted.zipIdx.foldl (fun m (a, i) => m.insert a i.toUInt64) {}
  let move (i : UInt64) : UInt64 := ((refs[i.toNat]?).bind (pos[·]?)).getD i
  let (table, umove) := canonicalUnivs univs
  let roots := (Ix.CompileM.constantInfoRootExprs info).map (remapUnivs umove ∘ remapRefs move)
  let info ← (Ix.CompileM.withRootExprs info roots).mapError (s!"model record refs: {·}")
  (Ix.CompileM.buildConstantWithSharing Ix.CompileM.compilerSharingLimits info sorted table).mapError
    (s!"model record sharing: {·}")

/-- `e` with every `share` node replaced by its entry of `sharing`, recursively (a
canonical table is acyclic). -/
partial def unshareAll (sharing : Array Ixon.Expr) : Ixon.Expr → Ixon.Expr
  | .share i => match sharing[i.toNat]? with
    | some e => unshareAll sharing e
    | none => .share i
  | .prj t i v => .prj t i (unshareAll sharing v)
  | .app a b => .app (unshareAll sharing a) (unshareAll sharing b)
  | .lam bc t b => .lam bc (unshareAll sharing t) (unshareAll sharing b)
  | .all bc vc t b => .all bc vc (unshareAll sharing t) (unshareAll sharing b)
  | .letE lc t v b => .letE lc (unshareAll sharing t) (unshareAll sharing v) (unshareAll sharing b)
  | e => e

/-- Record `c` with its references renamed by `rename`, in the compiler's form again
(`sharedRecord` over its expressions with the sharing expanded: refs sorted, levels
canonical and sorted, sharing rebuilt), without a section. A projection, whose tables
are empty, has its block renamed. -/
def renormalize (rename : Address → Address) (c : Ixon.Constant) : Except String Ixon.Constant := do
  match c.info with
  | .iPrj _ | .cPrj _ | .rPrj _ | .dPrj _ => return Ix.Compile.BinderData.rewriteRecord rename c #[]
  | _ =>
    let roots := (Ix.CompileM.constantInfoRootExprs c.info).map (unshareAll c.sharing)
    let info ← (Ix.CompileM.withRootExprs c.info roots).mapError (s!"model record refs: {·}")
    sharedRecord info (c.refs.map rename) c.univs

/-- An expression with its table indices erased: the places of its binders and share
nodes, which are all a record's section depends on, and not which reference, level
or blob a leaf names. -/
def shapeOf : Ixon.Expr → Ixon.Expr
  | .sort _ => .sort 0
  | .ref _ _ => .ref 0 #[]
  | .recur i _ => .recur i #[]
  | .prj _ i v => .prj 0 i (shapeOf v)
  | .str _ => .str 0
  | .nat _ => .nat 0
  | .app a b => .app (shapeOf a) (shapeOf b)
  | .lam bc t b => .lam bc (shapeOf t) (shapeOf b)
  | .all bc vc t b => .all bc vc (shapeOf t) (shapeOf b)
  | .letE lc t v b => .letE lc (shapeOf t) (shapeOf v) (shapeOf b)
  | e => e

/-- The shapes of a record's roots and sharing entries. -/
def recordShape (c : Ixon.Constant) : Array Ixon.Expr × Array Ixon.Expr :=
  ((Ix.CompileM.constantInfoRootExprs c.info).map shapeOf, c.sharing.map shapeOf)

/-- Each element of `xs` before the next by `lt`. -/
def ascendingBy {α : Type} (xs : Array α) (lt : α → α → Bool) : Bool :=
  (xs.zip (xs.extract 1 xs.size)).all fun (a, b) => lt a b

/-- **The compiler's table invariant** (`Ix.CompileM.preseedExprTables`): the refs
strictly ascending by address bytes; the levels each in canonical form
(`Ixon.canonUniv`) and strictly ascending by encoding. No decoder checks it: Lean's
`Ixon.Canonical.deConstant`, the reader's wire check, Rust's codec and IxVM's parser
read the tables in any order. Like the complete binder-data form, it is a property of
how records are built, which makes a constant's address unique; every model record
holds it (`ixvm-model-advice`). Finalize's evidence theorems keep their references in
first-use order. -/
def tablesCanonical (c : Ixon.Constant) : Bool :=
  ascendingBy c.refs (fun a b => a.cmpBytes b == .lt) &&
    c.univs.all (fun u => Ixon.canonUniv u == u) &&
    ascendingBy (c.univs.map Ix.CompileM.univSortKey) (fun a b => Ix.CompileM.byteArrayCmp a b == .lt)

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
  let c ← sharedRecord (.defn { kind := kind, safety := .safe, lvls := lps.length.toUInt64, typ, value := v })
    s.refs s.univs
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
  let blockC ← sharedRecord (.muts #[.indc ind]) s.refs s.univs
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
    let recC ← sharedRecord (.recr recR) rs.refs rs.univs
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
`PUnit.unit`, `PUnit.rec`, `String`, `Char`. -/
def basisRoleAllowed (r : Nat) : Bool := [0, 1, 2, 3, 8, 9, 10, 11, 12, 13, 37, 39].contains r

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

/-! ## The advice's binder data

A generated record carries its binder-data section like any record, so its
address covers the data IxVM reads from it. The records are encoded first (each
naming the ones before it by address), then annotated as a whole by IxC's pass,
typed against the environment's records (`IxVM.RecordSections.sectionsOf`; the
data do not depend on addresses), and then re-addressed bottom-up: each record's
references to the advice follow their new addresses, the record is put in the
compiler's form again (`renormalize`: its refs sorted by the new addresses, its
sharing rebuilt), its section is set, and it is hashed. The section computed before
fits the rebuilt record when the two have the same shape (`recordShape`); otherwise
it is computed again for the record as it stands. So every advice record is the
record the compiler would write for its declaration. The payload, hints and
dependencies name the new addresses. -/

/-- `adv` with every record's binder-data section, re-addressed. `support` are the
environment's records, `chosen` its role table and prelude. -/
def BlockAdvice.withSections (adv : BlockAdvice) (support : Array (Address × Ixon.Constant))
    (blobs : Std.HashMap Address ByteArray) (hints : Std.HashMap Address Lean.ReducibilityHints)
    (chosen : Ix.Kernel.RoleTable × Ix.Kernel.Reader.Prelude .anon) : Except String BlockAdvice := do
  let blobs := adv.blobs.foldl (fun m (a, b) => m.insert a b) blobs
  let hints := adv.hints.foldl (fun m (a, h) => m.insert a h) hints
  -- the advice records are the view's models: indexed after the environment's, so a generated
  -- recursor cannot displace the environment's recursor of an alpha-equivalent block
  let models : Std.HashSet Address := adv.records.foldl (fun s (a, _) => s.insert a) {}
  let sections ← IxVM.RecordSections.sectionsOf adv.records support blobs hints chosen (models := models)
  let store : Std.HashMap Address Ixon.Constant :=
    adv.records.foldl (fun m (a, c) => m.insert a c) {}
  let order ← Ix.Compile.BinderData.bottomUp store adv.records
  let mut renamed : Std.HashMap Address Address := {}
  let mut rewritten : Std.HashMap Address Ixon.Constant := {}
  for a in order do
    let some c := store[a]? | continue
    let rename (x : Address) : Address := renamed.getD x x
    let c1 ← renormalize rename c
    let c' ← if recordShape c1 == recordShape c then
        pure { c1 with binders := sections.getD a #[] }
      else do
        -- the rebuilt sharing moved a binder or a share: the section of the record as it stands,
        -- typed against the environment and the advice re-addressed so far
        let a1 := addressOf c1
        let done := rewritten.toArray
        let fresh ← IxVM.RecordSections.sectionsOf #[(a1, c1)] (support ++ done) blobs hints chosen
          (models := done.foldl (fun s (x, _) => s.insert x) ({} : Std.HashSet Address))
        pure { c1 with binders := fresh.getD a1 #[] }
    let a' := addressOf c'
    renamed := renamed.insert a a'
    rewritten := rewritten.insert a' c'
  let rename (x : Address) : Address := renamed.getD x x
  -- the records in their original order, each once
  let mut records : Array (Address × Ixon.Constant) := #[]
  for (a, _) in adv.records do
    let a' := rename a
    if records.any (·.1 == a') then continue
    let some c' := rewritten[a']? | throw s!"model advice: record {a} was not re-addressed"
    records := records.push (a', c')
  let l := adv.layout
  let layout : Payload := { l with
    recBlock := rename l.recBlock
    advice := records.map (·.1)
    witnesses := l.witnesses.map (fun (x, k, steps, extra) => (rename x, k, steps, extra))
    typeModels := l.typeModels.map rename
    ctorModels := l.ctorModels.map rename
    recModels := l.recModels.map rename
    iotas := l.iotas.map rename }
  return { adv with layout, records,
                    hints := adv.hints.map (fun (a, h) => (rename a, h)),
                    deps := adv.deps.map rename }

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
      let advice := blockAdvice table look cx a c shape (r.decls.toList.take r.generated) tweak
        >>= (·.withSections records env.blobs env.anonHints (table, pre))
      match advice with
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
