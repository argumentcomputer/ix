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
  exprCache : Std.HashMap (Expr .anon) Ixon.Expr := {}

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
  let s ← get
  unless s.refIdx.contains a do
    set { s with blobs := s.blobs.push (a, bytes) }
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

/-- `e` as a record's expression. Kernel terms carry no modes, so a binder and a let
encode at the default ones; a let keeps its `nonDep` flag, which is committed content
of the record the kernel read it from, so a
declaration read from a record encodes to that record's expressions; the modeller's
own binders and lets carry the Lean fragment's. -/
partial def encExpr (nm : Names) (lps : List Nat) (self : Key .anon → Option Nat)
    (e : Expr .anon) : EncM Ixon.Expr :=
  match e with
  | .bvar i => pure (.var i.toUInt64)
  | .fvar .. => throw "free variable in a generated record"
  | .sort u => do pure (.sort (← univOf (← liftExcept (encLevel lps u))))
  | .lit (.natVal n) => return .nat (← blobOf (ByteArray.mk (Nat.toBytesLE n)))
  | .lit (.strVal s) => return .str (← blobOf s.toUTF8)
  | _ => do
    if let some cached := (← get).exprCache[e]? then
      return cached
    let res ← match e with
      | .const k us => do
        let uis ← us.toArray.mapM fun u => do univOf (← liftExcept (encLevel lps u))
        match self k with
        | some i => pure (.recur i.toUInt64 uis)
        | none => pure (.ref (← refOf (← liftExcept (nm.addr k))) uis)
      | .app f a => pure (.app (← encExpr nm lps self f) (← encExpr nm lps self a))
      | .lam t b _ => pure (.lam (← encExpr nm lps self t) (← encExpr nm lps self b))
      | .forallE t b _ => pure (.all (← encExpr nm lps self t) (← encExpr nm lps self b))
      | .letE t v b l =>
        pure (.letE l.nonDep (.value .many) (← encExpr nm lps self t) (← encExpr nm lps self v)
          (← encExpr nm lps self b))
      | .proj s i x => do
        let si ← refOf (← liftExcept (nm.addr s))
        pure (.prj si i.toUInt64 (← encExpr nm lps self x))
      | _ => throw "unreachable"
    modify fun s => { s with exprCache := s.exprCache.insert e res }
    return res

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
  | .lam t b => .lam (remapRefs f t) (remapRefs f b)
  | .all t b => .all (remapRefs f t) (remapRefs f b)
  | .letE nd lm t v b => .letE nd lm (remapRefs f t) (remapRefs f v) (remapRefs f b)
  | e => e

/-- `e` with every index into the record's univs table moved by `f`: a sort's level
and the universe arguments of a reference or of a recursive reference. -/
def remapUnivs (f : UInt64 → UInt64) : Ixon.Expr → Ixon.Expr
  | .sort i => .sort (f i)
  | .ref i us => .ref i (us.map f)
  | .recur i us => .recur i (us.map f)
  | .prj t i v => .prj t i (remapUnivs f v)
  | .app a b => .app (remapUnivs f a) (remapUnivs f b)
  | .lam t b => .lam (remapUnivs f t) (remapUnivs f b)
  | .all t b => .all (remapUnivs f t) (remapUnivs f b)
  | .letE nd lm t v b => .letE nd lm (remapUnivs f t) (remapUnivs f v) (remapUnivs f b)
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
  let sorted := (refs.qsort fun a b => a.cmpBytes b == .lt).foldl
    (fun acc a => if acc.back? == some a then acc else acc.push a) #[]
  let pos : Std.HashMap Address UInt64 :=
    sorted.zipIdx.foldl (fun m (a, i) => m.insert a i.toUInt64) {}
  let move (i : UInt64) : UInt64 := ((refs[i.toNat]?).bind (pos[·]?)).getD i
  let (table, umove) := canonicalUnivs univs
  let roots := (Ix.CompileM.constantInfoRootExprs info).map (remapUnivs umove ∘ remapRefs move)
  let info ← (Ix.CompileM.withRootExprs info roots).mapError (s!"model record refs: {·}")
  (Ix.CompileM.buildConstantWithSharing Ix.CompileM.compilerSharingLimits info sorted table).mapError
    (s!"model record sharing: {·}")

/-- Replace each `.share i` in `e` with `tbl[i]?` in a single pass. -/
def substShares (tbl : Array Ixon.Expr) : Ixon.Expr → Ixon.Expr
  | .share i => tbl[i.toNat]?.getD (.share i)
  | .prj t i v => .prj t i (substShares tbl v)
  | .app a b => .app (substShares tbl a) (substShares tbl b)
  | .lam t b => .lam (substShares tbl t) (substShares tbl b)
  | .all t b => .all (substShares tbl t) (substShares tbl b)
  | .letE nd lm t v b =>
      .letE nd lm (substShares tbl t) (substShares tbl v) (substShares tbl b)
  | e => e

/-- Whether `e` only references `.share` indices strictly less than `bound`. -/
def sharesBelow (bound : Nat) : Ixon.Expr → Bool
  | .share i => i.toNat < bound
  | .prj _ _ v => sharesBelow bound v
  | .app a b | .lam a b | .all a b => sharesBelow bound a && sharesBelow bound b
  | .letE _ _ t v b => sharesBelow bound t && sharesBelow bound v && sharesBelow bound b
  | _ => true

/-- Expand a backward-referenced `sharing` table bottom-up in `O(|sharing|)` time; returns
`none` if any entry has a forward share reference. -/
def expandSharingTable? (sharing : Array Ixon.Expr) : Option (Array Ixon.Expr) := Id.run do
  let mut out : Array Ixon.Expr := Array.mkEmpty sharing.size
  for e in sharing do
    unless sharesBelow out.size e do return none
    out := out.push (substShares out e)
  return some out

/-- Recursive fallback expansion for non-backward sharing tables. -/
partial def unshareAllRec (sharing : Array Ixon.Expr) : Ixon.Expr → Ixon.Expr
  | .share i => match sharing[i.toNat]? with
    | some e => unshareAllRec sharing e
    | none => .share i
  | .prj t i v => .prj t i (unshareAllRec sharing v)
  | .app a b => .app (unshareAllRec sharing a) (unshareAllRec sharing b)
  | .lam t b => .lam (unshareAllRec sharing t) (unshareAllRec sharing b)
  | .all t b => .all (unshareAllRec sharing t) (unshareAllRec sharing b)
  | .letE nd lm t v b =>
      .letE nd lm (unshareAllRec sharing t) (unshareAllRec sharing v) (unshareAllRec sharing b)
  | e => e

/-- `e` with every `share` node replaced by its entry of `sharing`, recursively (a
canonical table is acyclic and backward-referenced, expanded once in `O(|sharing|)`). -/
def unshareAll (sharing : Array Ixon.Expr) (e : Ixon.Expr) : Ixon.Expr :=
  if sharing.isEmpty then e
  else match expandSharingTable? sharing with
    | some tbl => substShares tbl e
    | none => unshareAllRec sharing e

/-- Record `c` with its references renamed by `rename`, in the compiler's form again
(`sharedRecord` over its expressions with the sharing expanded: refs sorted, levels
canonical and sorted, sharing rebuilt), without a section. A projection, whose tables
are empty, has its block renamed. -/
def renormalize (rename : Address → Address) (c : Ixon.Constant) : Except String Ixon.Constant := do
  match c.info with
  | .iPrj _ | .cPrj _ | .rPrj _ | .dPrj _ => return Ix.Compile.BinderData.rewriteRecord rename c #[]
  | _ =>
    let expand : Ixon.Expr → Ixon.Expr :=
      if c.sharing.isEmpty then id
      else match expandSharingTable? c.sharing with
        | some tbl => substShares tbl
        | none => unshareAllRec c.sharing
    let roots := (Ix.CompileM.constantInfoRootExprs c.info).map expand
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
  | .lam t b => .lam (shapeOf t) (shapeOf b)
  | .all t b => .all (shapeOf t) (shapeOf b)
  | .letE nd lm t v b => .letE nd lm (shapeOf t) (shapeOf v) (shapeOf b)
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
`PUnit.unit`, `PUnit.rec`, the quotient (`Quot`, `Quot.mk`, `Quot.lift`,
`Quot.ind`, `Quot.sound`, from which function extensionality is a theorem).
An anchor such as `String` or `Char` is witnessed by a dependency path. -/
def basisRoleAllowed (r : Nat) : Bool :=
  [0, 1, 2, 3, 8, 9, 10, 11, 12, 13, 32, 33, 34, 35, 36].contains r

/-- The `refs` indices a record uses as constants (`KernelClaim::const_idxs_of`). -/
partial def usedIdxsExpr : Ixon.Expr → Std.HashSet Nat
  | .ref i _ => ({} : Std.HashSet Nat).insert i.toNat
  | .prj i _ inner => (usedIdxsExpr inner).insert i.toNat
  | .app a b | .lam a b | .all a b => (usedIdxsExpr a).union (usedIdxsExpr b)
  | .letE _ _ t v b => ((usedIdxsExpr t).union (usedIdxsExpr v)).union (usedIdxsExpr b)
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

/-- A role whose record a validation walks (`KernelRoles::role_admission_checks`, read by
`KernelModeled::addr_covered`): a block member outside the quotient package, an operation,
a definition specified by equations, or one of the eleven non-container binding-validated
anchors (`Bool`, `And`, `String`, `Char`, and their bound constructors/recursors/helpers).
The top-level walk does not enter a record bound to one, so a witness reached past one, or
at one, must be bound to such a role itself (`KernelModeled::assert_covered_past`). -/
def coveredRole (r : Ix.Kernel.Role) : Bool :=
  match r with
  | .bool | .boolFalse | .boolTrue | .boolRec
  | .and | .andIntro | .andRec
  | .string | .stringOfList | .char | .charOfNat => true
  | _ =>
    let quotPackage : Bool := match r with
      | .quot | .quotMk | .quotLift | .quotInd | .quotSound => true
      | _ => false
    match r.spec (md := .anon) with
    | .block .. => !quotPackage
    | .ops .. | .eqns .. => true
    | _ => false

/-- Breadth-first search of the dependency closure the claim walk visits from
`root` (used references, projection to block), recording each record's
predecessor and step (`0` projection to block, `j + 1` the `j`-th reference).
The search does not enter a record `avoid` answers `true` for. -/
def depsSearch (look : Address → Option Ixon.Constant) (root : Address) (limit : Nat := 400000)
    (avoid : Address → Bool := fun _ => false) :
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
      unless seen.contains n || avoid n do
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
dependency path), the models of the types, constructors and recursors, the
`iota_j` theorems, and per projection-eligible member and field the pair
`(proj_i, proj_i.iota)`. `adviceCount` overrides the advice count written (tests). -/
structure Payload where
  recBlock : Address
  advice : Array Address
  witnesses : Array (Address × Nat × List Nat × List Nat)
  typeModels : Array Address
  ctorModels : Array Address
  recModels : Array Address
  iotas : Array Address
  projModels : Array (Address × Address) := #[]
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
  for (pm, pi) in p.projModels do b := putAddr (putAddr b pm) pi
  return b

/-- Mirror of `KernelLevels::level_is_not_zero` on `Ixon.Univ`. -/
def ixonUnivIsNotZero : Ixon.Univ → Bool
  | .zero => false
  | .var _ => false
  | .succ _ => true
  | .max a b => ixonUnivIsNotZero a || ixonUnivIsNotZero b
  | .imax _ b => ixonUnivIsNotZero b

/-- Lift loose bound variables `≥ cutoff` by `shift` in an unshared `Ixon.Expr`. -/
def ixonLift (shift cutoff : Nat) : Ixon.Expr → Ixon.Expr
  | .var i => if i.toNat < cutoff then .var i else .var (i.toNat + shift).toUInt64
  | .app a b => .app (ixonLift shift cutoff a) (ixonLift shift cutoff b)
  | .lam t b => .lam (ixonLift shift cutoff t) (ixonLift shift (cutoff + 1) b)
  | .all t b => .all (ixonLift shift cutoff t) (ixonLift shift (cutoff + 1) b)
  | .letE nd lm t v b =>
      .letE nd lm (ixonLift shift cutoff t) (ixonLift shift cutoff v) (ixonLift shift (cutoff + 1) b)
  | .prj t i v => .prj t i (ixonLift shift cutoff v)
  | e => e

/-- Mirror of `KernelSubst::expr_inst1` on an unshared `Ixon.Expr`. -/
def ixonInst1 (arg : Ixon.Expr) (depth : Nat) : Ixon.Expr → Ixon.Expr
  | .var i =>
      if i.toNat < depth then .var i
      else if i.toNat == depth then ixonLift depth 0 arg
      else .var (i.toNat - 1).toUInt64
  | .app a b => .app (ixonInst1 arg depth a) (ixonInst1 arg depth b)
  | .lam t b => .lam (ixonInst1 arg depth t) (ixonInst1 arg (depth + 1) b)
  | .all t b => .all (ixonInst1 arg depth t) (ixonInst1 arg (depth + 1) b)
  | .letE nd lm t v b =>
      .letE nd lm (ixonInst1 arg depth t) (ixonInst1 arg depth v) (ixonInst1 arg (depth + 1) b)
  | .prj t i v => .prj t i (ixonInst1 arg depth v)
  | e => e

/-- Mirror of `KernelWhnf::type_sort_never` at declaration level parameters on an
unshared `Ixon.Expr`. -/
def ixonTypeSortNever (univs : Array Ixon.Univ) : Ixon.Expr → Nat → Bool
  | .all _ b, n + 1 => ixonTypeSortNever univs b n
  | .sort uIdx, 0 => (univs[uIdx.toNat]?).any ixonUnivIsNotZero
  | _, _ => false

/-- Mirror of `KernelCheck::peel_n_foralls_zeta` on an unshared `Ixon.Expr`. -/
partial def ixonPeelForallsZeta : Ixon.Expr → Nat → Option Ixon.Expr
  | e, 0 => some e
  | .all _ b, n + 1 => ixonPeelForallsZeta b n
  | .letE _ _ _ v b, n => ixonPeelForallsZeta (ixonInst1 v 0 b) n
  | _, _ => none

/-- Mirror of `KernelWhnf::se_mentions` on an unshared `Ixon.Expr` of a block. -/
def ixonMentionsBlock (refs : Array Address) (mems : Std.HashSet Address) (nMems : Nat) :
    Ixon.Expr → Bool
  | .recur j _ => j.toNat < nMems
  | .ref r _ => (refs[r.toNat]?).any mems.contains
  | .app a b | .lam a b | .all a b =>
      ixonMentionsBlock refs mems nMems a || ixonMentionsBlock refs mems nMems b
  | .letE _ _ t v b =>
      ixonMentionsBlock refs mems nMems t || ixonMentionsBlock refs mems nMems v ||
        ixonMentionsBlock refs mems nMems b
  | .prj _ _ inner => ixonMentionsBlock refs mems nMems inner
  | _ => false

/-- Mirror of `KernelModeled::field_has_neg` on an unshared `Ixon.Expr`. -/
partial def ixonFieldHasNeg (refs : Array Address) (mems : Std.HashSet Address) (nMems : Nat) :
    Ixon.Expr → Bool
  | .all dom body =>
      ixonMentionsBlock refs mems nMems dom || ixonFieldHasNeg refs mems nMems body
  | .letE _ _ _ v b => ixonFieldHasNeg refs mems nMems (ixonInst1 v 0 b)
  | _ => false

/-- Mirror of `KernelModeled::fields_have_neg` on an unshared `Ixon.Expr`. -/
partial def ixonFieldsHaveNeg (refs : Array Address) (mems : Std.HashSet Address) (nMems : Nat) :
    Ixon.Expr → Nat → Bool
  | _, 0 => false
  | .all dom body, n + 1 =>
      ixonFieldHasNeg refs mems nMems dom || ixonFieldsHaveNeg refs mems nMems body n
  | .letE _ _ _ v b, n => ixonFieldsHaveNeg refs mems nMems (ixonInst1 v 0 b) n
  | _, _ => false

/-- Mirror of `KernelModeled::block_has_neg_occ` on a `muts` block record. -/
def ixonBlockHasNegOcc (b : Address) (bc : Ixon.Constant) (ms : Array Ixon.MutConst) : Bool := Id.run do
  let expand : Ixon.Expr → Ixon.Expr :=
    if bc.sharing.isEmpty then id
    else match expandSharingTable? bc.sharing with
      | some tbl => substShares tbl
      | none => unshareAllRec bc.sharing
  let mut mems : Std.HashSet Address := {}
  for (m, pos) in ms.zipIdx do
    match m with
    | .indc _ => mems := mems.insert (addressOf (projRecord (.iPrj ⟨pos.toUInt64, b⟩)))
    | .defn _ => mems := mems.insert (addressOf (projRecord (.dPrj ⟨pos.toUInt64, b⟩)))
    | .recr _ => mems := mems.insert (addressOf (projRecord (.rPrj ⟨pos.toUInt64, b⟩)))
  for m in ms do
    let .indc ind := m | continue
    for ct in ind.ctors do
      let cty := expand ct.typ
      let some body := ixonPeelForallsZeta cty ct.params.toNat | continue
      if ixonMentionsBlock bc.refs mems ms.size body &&
          ixonFieldsHaveNeg bc.refs mems ms.size body ct.fields.toNat then
        return true
  return false

/-- Mirror of `KernelModeled::modeled_proj_eligible` for member `pos` of `ms`. -/
def ixonMemberProjEligible (bc : Ixon.Constant) (ms : Array Ixon.MutConst) (hasNeg : Bool)
    (pos : Nat) : Bool :=
  if hasNeg then false
  else match ms[pos]? with
  | some (.indc ind) =>
    if ind.indices == 0 && ind.ctors.size == 1 then
      let ity := unshareAll bc.sharing ind.typ
      if ixonTypeSortNever bc.univs ity ind.params.toNat then
        match ind.ctors[0]? with
        | some ct => ct.lvls == ind.lvls && ct.params == ind.params && ct.fields > 0
        | none => false
      else false
    else false
  | _ => false

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

/-! ## Compaction and dead-declaration pruning of generated model advice -/

/-- The tag enumeration's recursor metadata, used to ι-reduce closed `tag.rec ... (tag.m ...)`
dispatch redexes generated by the modeller (`Nested.lean`'s `ihBinder` and `dispatchMotive`). -/
structure TagRecInfo where
  recKey : Key .anon
  nP : Nat
  numCtors : Nat
  ctors : Std.HashMap (Key .anon) (Nat × Nat)

/-- Extract `TagRecInfo` from a non-recursive, index-free 1-type tag `.indDecl`. -/
def extractTagRecInfo (gen : List (Declaration .anon)) : Option TagRecInfo :=
  gen.findSome? fun d => match d with
    | .indDecl block nP =>
      let tys := block.filterMap fun ci => match ci with | .indInfo cv _ => some cv | _ => none
      let ctors := block.filterMap fun ci => match ci with | .ctorInfo cv cP cF => some (cv, cP, cF) | _ => none
      let recs := block.filterMap fun ci => match ci with | .recInfo cv mI rP rules => some (cv, mI, rP, rules) | _ => none
      match tys, recs with
      | [cvT], [(cvR, mI, rP, rules)] =>
        let k := ctors.length
        if piCount cvT.type == nP && mI == nP + 1 + k && rP == nP + 1 + k && rules.length == k &&
            ctors.all (fun (_, cP, _) => cP == nP) &&
            (ctors.zip rules).all (fun ((cvC, _, cF), r) =>
              r.ctor == cvC.name && r.nfields == cF &&
                match cvC.type.stripPis (nP + cF) with
                | some (bs, _) => bs.all (fun (dom, _) => !dom.mentionsConst cvT.name)
                | none => false) then
          let cmap := (ctors.zipIdx).foldl (init := ({} : Std.HashMap (Key .anon) (Nat × Nat)))
            fun m ((cvC, _, cF), idx) => m.insert cvC.name (idx, cF)
          some { recKey := cvR.name, nP, numCtors := k, ctors := cmap }
        else none
      | _, _ => none
    | _ => none

/-- Count occurrences of bound variable `d` in `e`, stopping once `acc > limit`. -/
def bvarOccsBounded (limit : Nat) : Nat → Expr .anon → Nat → Nat
  | d, e, acc =>
    if acc > limit then acc
    else match e with
      | .bvar i => if i == d then acc + 1 else acc
      | .app f a =>
        let acc := bvarOccsBounded limit d f acc
        bvarOccsBounded limit d a acc
      | .lam t b _ | .forallE t b _ =>
        let acc := bvarOccsBounded limit d t acc
        bvarOccsBounded limit (d + 1) b acc
      | .letE t v b _ =>
        let acc := bvarOccsBounded limit d t acc
        let acc := bvarOccsBounded limit d v acc
        bvarOccsBounded limit (d + 1) b acc
      | .proj _ _ x => bvarOccsBounded limit d x acc
      | _ => acc

/-- Count AST nodes in `e`, stopping once `acc > limit`. -/
def exprNodesBounded (limit : Nat) : Expr .anon → Nat → Nat
  | e, acc =>
    if acc > limit then acc
    else match e with
      | .app f a =>
        let acc := exprNodesBounded limit f (acc + 1)
        exprNodesBounded limit a acc
      | .lam t b _ | .forallE t b _ =>
        let acc := exprNodesBounded limit t (acc + 1)
        exprNodesBounded limit b acc
      | .letE t v b _ =>
        let acc := exprNodesBounded limit t (acc + 1)
        let acc := exprNodesBounded limit v acc
        exprNodesBounded limit b acc
      | .proj _ _ x => exprNodesBounded limit x (acc + 1)
      | _ => acc + 1

/-- Collect an application spine `(head, args)` without quadratic re-traversal. -/
def splitAppSpine (e : Expr .anon) : Expr .anon × List (Expr .anon) :=
  let rec go : Expr .anon → List (Expr .anon) → Expr .anon × List (Expr .anon)
    | .app f a, acc => go f (a :: acc)
    | fn, acc => (fn, acc)
  go e []

/-- Whether `e` is a constructor application of the tag enumeration `tag?`. -/
def isTagCtorApp (tag? : Option TagRecInfo) (e : Expr .anon) : Bool :=
  match tag? with
  | none => false
  | some ti =>
    match e.getAppFn with
    | .const ck _ => ti.ctors.contains ck
    | _ => false

/-- Peel leading lambdas, returning `(arity, body)`. -/
def peelLamArity : Expr .anon → Nat → Nat × Expr .anon
  | .lam _ b _, n => peelLamArity b (n + 1)
  | e, n => (n, e)

/-- Capture-avoiding multi-argument substitution for a term `body` originally under `args.length`
lambdas (`args[0]` substitutes the outermost binder, `args.getLast` the innermost). -/
def applyLamArgs (body : Expr .anon) (args : List (Expr .anon)) : Expr .anon :=
  let rec go (e : Expr .anon) (rem : Nat) : List (Expr .anon) → Expr .anon
    | [] => e
    | a :: rest => go (e.instantiate1Lift a (rem - 1)) (rem - 1) rest
  go body args.length args

/-- An `Eq.rec`-at-`Eq.refl` helper (`congrPack_j`, `Eq.ndrec`, `Eq.recOn`,
`Eq.ndrecOn`, `Eq.subst`, `congrArg`, `congrFun`): when applied to `arity`
arguments whose `prfArgIdx`-th argument is `Eq.refl _ _`, reduces definitionally
to `base` instantiated at those levels and arguments. When `guardSize` is true
(external helpers), arguments referenced more than once in `base` are guarded
against term-size blowup. -/
structure EqReflHelper where
  levelParams : List Nat
  arity : Nat
  prfArgIdx : Nat
  base : Expr .anon
  guardSize : Bool := false

/-- True when `e` references no constant (or projection struct) other than `.role .eqRefl`. -/
def exprOnlyEqReflConsts : Expr .anon → Bool
  | .const (.role .eqRefl) _ => true
  | .const _ _ => false
  | .proj _ _ _ => false
  | .app f a => exprOnlyEqReflConsts f && exprOnlyEqReflConsts a
  | .lam t b _ | .forallE t b _ => exprOnlyEqReflConsts t && exprOnlyEqReflConsts b
  | .letE t v b _ => exprOnlyEqReflConsts t && exprOnlyEqReflConsts v && exprOnlyEqReflConsts b
  | _ => true

/-- Recognize a helper `λ x_0 ... x_{k-1}, Head ... (.bvar prfBVar)` whose head is either
`Eq.rec` or an already-recognized `EqReflHelper` (allowing `Eq.ndrec` / `Eq.subst` →
`congrArg` / `congrFun` / `Eq.ndrecOn` chaining). For internal helpers (`external = false`),
`base` may be an `Eq.refl` application or `.bvar j` (`j < arity`). For external helpers
(`external = true`), `base` must also introduce no constants other than `.role .eqRefl` and
stay within 64 AST nodes so reduction never introduces un-witnessed outside references. -/
def recognizeEqReflHelper (known : Std.HashMap (Key .anon) EqReflHelper)
    (external : Bool) (cv : ConstantVal .anon) (v : Expr .anon) : Option EqReflHelper :=
  let (arity, body) := peelLamArity v 0
  if arity == 0 then none
  else
    let (fn, args) := splitAppSpine body
    let matched : Option (Nat × Expr .anon) := match fn, args with
      | .const (.role .eqRec) _, [_α, _a, _mot, base, _b, .bvar prfBVar] =>
        if prfBVar < arity then some (arity - 1 - prfBVar, base) else none
      | .const k us, _ =>
        match known[k]? with
        | some eh =>
          if args.length == eh.arity && us.length == eh.levelParams.length then
            match args[eh.prfArgIdx]? with
            | some (.bvar prfBVar) =>
              if prfBVar < arity then
                let base := applyLamArgs (eh.base.instantiateLevelParams eh.levelParams us) args
                some (arity - 1 - prfBVar, base)
              else none
            | _ => none
          else none
        | none => none
      | _, _ => none
    match matched with
    | none => none
    | some (prfArgIdx, base) =>
      let baseOk : Bool := match base with
        | .bvar j => j < arity
        | _ =>
          let (bh, bargs) := splitAppSpine base
          match bh with
          | .const (.role .eqRefl) _ =>
            bargs.length == 2 &&
              (!external || (exprOnlyEqReflConsts base && exprNodesBounded 64 base 0 ≤ 64))
          | _ => false
      if baseOk then
        some { levelParams := cv.levelParams, arity, prfArgIdx, base, guardSize := external }
      else none

/-- Extract internal `Eq.rec`-at-`Eq.refl` helpers from `gen`, seeded with any external helpers
recognized from the environment (`Eq.ndrec`, `Eq.subst`, `congrArg`, `congrFun`, etc.). -/
def extractEqReflHelpers (gen : Array (Declaration .anon)) (req : Std.HashSet (Key .anon))
    (external : Std.HashMap (Key .anon) EqReflHelper := {}) :
    Std.HashMap (Key .anon) EqReflHelper := Id.run do
  let mut out : Std.HashMap (Key .anon) EqReflHelper := external
  for d in gen do
    let .defnDecl cv v _ := d | continue
    if req.contains cv.name then continue
    if let some eh := recognizeEqReflHelper out false cv v then
      out := out.insert cv.name eh
  return out

/-- Safe bottom-up β + dead-`let` + `tag.rec`-ι + `Eq.rec`-ι + `Eq`-at-`Eq.refl` helper
(`congrPack_j`, `Eq.ndrec`, `congrArg`, `congrFun`) compaction on generated model expressions.
Structural descent is unbounded; `stepFuel` bounds only actual reduction steps. Preserves
definitional equality and well-typedness, never ζ-reduces live `letE` (only eliminates unused
`letE` bindings), and guards β-reduction and external helper substitutions against term blowup
(`occs ≤ 1`, tag constructor argument, or `occs * size ≤ 64`). -/
partial def compactExpr (tag? : Option TagRecInfo)
    (eqHelpers : Std.HashMap (Key .anon) EqReflHelper) (e : Expr .anon) : Expr .anon :=
  go 256 e
where
  go (stepFuel : Nat) (e : Expr .anon) : Expr .anon :=
    match e with
    | .lam t b bm => .lam (go stepFuel t) (go stepFuel b) bm
    | .forallE t b bm => .forallE (go stepFuel t) (go stepFuel b) bm
    | .letE t v b lm =>
      let b' := go stepFuel b
      if bvarOccsBounded 1 0 b' 0 == 0 then
        b'.instantiate1Lift (.sort .zero) 0
      else
        .letE (go stepFuel t) (go stepFuel v) b' lm
    | .proj s i x => .proj s i (go stepFuel x)
    | .app .. =>
      let (fn0, args0) := splitAppSpine e
      let fn := go stepFuel fn0
      let args := args0.map (go stepFuel)
      reduceSpine stepFuel fn args
    | e => e
  isEqReflApp (e : Expr .anon) : Bool :=
    let (ph, pargs) := splitAppSpine e
    match ph with
    | .const (.role .eqRefl) _ => pargs.length == 2
    | _ => false
  reduceSpine (stepFuel : Nat) (fn : Expr .anon) (args : List (Expr .anon)) : Expr .anon :=
    match stepFuel with
    | 0 => Expr.mkAppN fn args
    | stepFuel + 1 =>
      match fn, args with
      -- Safe β-reduction
      | .lam _ body _, a :: rest =>
        let occs := bvarOccsBounded 64 0 body 0
        let canBeta :=
          if occs ≤ 1 || isTagCtorApp tag? a then true
          else if occs ≤ 64 then
            let sz := exprNodesBounded (64 / occs) a 0
            occs * sz ≤ 64
          else false
        if canBeta then
          let body' := go stepFuel (body.instantiate1Lift a 0)
          let (fn', extra) := splitAppSpine body'
          reduceSpine stepFuel fn' (extra ++ rest)
        else Expr.mkAppN fn args
      -- `Eq.rec α a mot h b (Eq.refl α' a') rest ↦ h rest`
      | .const (.role .eqRec) _, _ :: _ :: _ :: h :: _ :: prf :: rest =>
        if isEqReflApp prf then
          let (fn', extra) := splitAppSpine h
          reduceSpine stepFuel fn' (extra ++ rest)
        else Expr.mkAppN fn args
      -- `tag.rec p⃗ mot m_0 ... m_{k-1} (tag.j p⃗ f⃗) rest ↦ m_j f⃗ rest`
      -- and `Eq`-at-`Eq.refl` helpers (`congrPack_j`, `Eq.ndrec`, `congrArg`, `congrFun`)
      | .const k us, _ =>
        match eqHelpers[k]? with
        | some eh =>
          if args.length ≥ eh.arity && us.length == eh.levelParams.length then
            match args[eh.prfArgIdx]? with
            | some prf =>
              if isEqReflApp prf then
                let taken := args.take eh.arity
                let sizeOk := !eh.guardSize || (taken.zipIdx).all fun (arg, idx) =>
                  let occs := bvarOccsBounded 64 (eh.arity - 1 - idx) eh.base 0
                  if occs ≤ 1 then true
                  else if occs ≤ 64 then occs * exprNodesBounded (64 / occs) arg 0 ≤ 64
                  else false
                if sizeOk then
                  let inst := applyLamArgs (eh.base.instantiateLevelParams eh.levelParams us) taken
                  let (fn', extra) := splitAppSpine (go stepFuel inst)
                  reduceSpine stepFuel fn' (extra ++ args.drop eh.arity)
                else Expr.mkAppN fn args
              else Expr.mkAppN fn args
            | none => Expr.mkAppN fn args
          else Expr.mkAppN fn args
        | none =>
          match tag? with
          | some ti =>
            if k == ti.recKey && args.length ≥ ti.nP + 1 + ti.numCtors + 1 then
              let majorIdx := ti.nP + 1 + ti.numCtors
              match args[majorIdx]? with
              | some major =>
                let (mh, margs) := splitAppSpine major
                match mh with
                | .const ck _ =>
                  match ti.ctors[ck]? with
                  | some (cidx, cF) =>
                    if margs.length == ti.nP + cF then
                      match args[ti.nP + 1 + cidx]? with
                      | some minor =>
                        let (fn', extra) := splitAppSpine minor
                        reduceSpine stepFuel fn' (extra ++ margs.drop ti.nP ++ args.drop (majorIdx + 1))
                      | none => Expr.mkAppN fn args
                    else Expr.mkAppN fn args
                  | none => Expr.mkAppN fn args
                | _ => Expr.mkAppN fn args
              | none => Expr.mkAppN fn args
            else Expr.mkAppN fn args
          | none => Expr.mkAppN fn args
      | _, _ => Expr.mkAppN fn args

/-- Collect all constant keys referenced by `e` (constants and `.proj` structure heads). -/
def exprConstKeys (e : Expr .anon) (acc : Std.HashSet (Key .anon)) : Std.HashSet (Key .anon) :=
  match e with
  | .const k _ => acc.insert k
  | .proj k _ x => exprConstKeys x (acc.insert k)
  | .app f a => exprConstKeys a (exprConstKeys f acc)
  | .lam t b _ | .forallE t b _ => exprConstKeys b (exprConstKeys t acc)
  | .letE t v b _ => exprConstKeys b (exprConstKeys v (exprConstKeys t acc))
  | _ => acc

/-- All keys declared by a generated kernel declaration. -/
def declDeclaredKeys : Declaration .anon → List (Key .anon)
  | .defnDecl cv _ _ => [cv.name]
  | .thmDecl cv _ => [cv.name]
  | .indDecl block _ => block.map ConstantInfo.name
  | _ => []

/-- All constant keys referenced by a generated kernel declaration. -/
def declReferencedKeys : Declaration .anon → Std.HashSet (Key .anon)
  | .defnDecl cv v _ => exprConstKeys v (exprConstKeys cv.type {})
  | .thmDecl cv v => exprConstKeys v (exprConstKeys cv.type {})
  | .indDecl block _ => block.foldl (init := {}) fun s ci => match ci with
    | .indInfo cv _ => exprConstKeys cv.type s
    | .ctorInfo cv _ _ => exprConstKeys cv.type s
    | .recInfo cv _ _ rules => rules.foldl (fun s r => exprConstKeys r.rhs s) (exprConstKeys cv.type s)
    | _ => s
  | _ => {}

/-- Keep only declarations reachable from `req`, preserving topological order. -/
def pruneGenReachable (decls : Array (Declaration .anon)) (req : Std.HashSet (Key .anon)) :
    Array (Declaration .anon) := Id.run do
  let mut declByKey : Std.HashMap (Key .anon) Nat := {}
  for (d, i) in decls.zipIdx do
    for k in declDeclaredKeys d do
      declByKey := declByKey.insert k i
  let mut reach : Std.HashSet Nat := {}
  let mut queue : Array Nat := #[]
  for k in req do
    if let some i := declByKey[k]? then
      unless reach.contains i do
        reach := reach.insert i
        queue := queue.push i
  let mut head := 0
  while head < queue.size do
    let idx := queue[head]!
    head := head + 1
    for dep in declReferencedKeys decls[idx]! do
      if let some j := declByKey[dep]? then
        unless reach.contains j do
          reach := reach.insert j
          queue := queue.push j
  let mut out : Array (Declaration .anon) := #[]
  for (d, i) in decls.zipIdx do
    if reach.contains i then out := out.push d
  return out

/-- Compact expressions in generated model declarations (leaving public root types and
inductive blocks intact) and prune declarations unreachable from the required public roots. -/
def compactAndPruneGen (gen : List (Declaration .anon)) (req : Std.HashSet (Key .anon))
    (extEqHelpers : Std.HashMap (Key .anon) EqReflHelper := {}) :
    List (Declaration .anon) := Id.run do
  let genArr := gen.toArray
  let tag? := extractTagRecInfo gen
  let eqHelpers := extractEqReflHelpers genArr req extEqHelpers
  let compacted : Array (Declaration .anon) := genArr.map fun d => match d with
    | .defnDecl cv v h =>
      let ty := if req.contains cv.name then cv.type else compactExpr tag? eqHelpers cv.type
      .defnDecl { cv with type := ty } (compactExpr tag? eqHelpers v) h
    | .thmDecl cv v =>
      let ty := if req.contains cv.name then cv.type else compactExpr tag? eqHelpers cv.type
      .thmDecl { cv with type := ty } (compactExpr tag? eqHelpers v)
    | other => other
  return (pruneGenReachable compacted req).toList

/-- The advice of one block, from the declarations the reader generated for it. -/
def blockAdvice (table : Ix.Kernel.RoleTable) (look : Address → Option Ixon.Constant)
    (cx : Ix.Kernel.Reader.Ctx .anon) (b : Address) (bc : Ixon.Constant)
    (shape : Ix.Kernel.Reader.BlockShape) (gen : List (Declaration .anon))
    (tweak : Declaration .anon → Declaration .anon := id)
    (extEqHelpers : Std.HashMap (Key .anon) EqReflHelper := {}) :
    Except String BlockAdvice := do
  let fk ← familyKeys cx b bc shape
  -- Determine eligible modeled-projection keys once (reused for pruning and payload assembly)
  let mut projKeys : Array (Key .anon × Key .anon) := #[]
  if let .muts ms := bc.info then
    let hasNeg := ixonBlockHasNegOcc b bc ms
    for (m, pos) in ms.zipIdx do
      if ixonMemberProjEligible bc ms hasNeg pos then
        if let .indc ind := m then
          if let some ct := ind.ctors[0]? then
            let some tk := fk.types[pos]? | throw s!"no type key at member {pos}"
            for fidx in [0:ct.fields.toNat] do
              let pmKey := Ix.Kernel.projModelName tk fidx
              projKeys := projKeys.push (pmKey, auxKey pmKey .projIota)
  -- Required public root keys checked by `KernelModeled::check_family`
  let mut req : Std.HashSet (Key .anon) := {}
  for k in fk.types ++ fk.ctors do req := req.insert (auxKey k .model)
  for (k, n) in fk.recs do
    req := req.insert (auxKey k .model)
    for j in [0:n] do req := req.insert (auxKey (auxKey k .model) (.iota j))
  for (pmKey, piKey) in projKeys do
    req := (req.insert pmKey).insert piKey
  let liveGen := (compactAndPruneGen gen req extEqHelpers).map tweak
  let roles : Std.HashMap Ix.Kernel.Role Address := table.bound.foldl (fun m (r, a) => m.insert r a) {}
  let mut nm : Names := { roles := roles }
  let mut records : Array (Address × Ixon.Constant) := #[]
  let mut recSeen : Std.HashSet Address := {}
  let mut hints : Array (Address × Lean.ReducibilityHints) := #[]
  let mut hintSeen : Std.HashSet Address := {}
  let mut blobs : Array (Address × ByteArray) := #[]
  let mut blobSeen : Std.HashSet Address := {}
  for d in liveGen do
    let e ← encDecl nm d
    for rc in e.records do
      unless recSeen.contains rc.1 do
        recSeen := recSeen.insert rc.1
        records := records.push rc
    for h in e.hints do
      unless hintSeen.contains h.1 do
        hintSeen := hintSeen.insert h.1
        hints := hints.push h
    for bl in e.blobs do
      unless blobSeen.contains bl.1 do
        blobSeen := blobSeen.insert bl.1
        blobs := blobs.push bl
    nm := { nm with gen := e.keys.foldl (fun m (k, x) => m.insert k x) nm.gen }
  let aset : Std.HashSet Address := recSeen
  -- outside references: used references that are not advice
  let mut outside : Array Address := #[]
  for (_, c) in records do
    let used := usedIdxs c
    for (r, j) in c.refs.zipIdx do
      unless used.contains j do continue
      if aset.contains r || outside.contains r then continue
      outside := outside.push r
  -- the records bound to a covered role (`coveredRole`)
  let coveredAt : Std.HashSet Address := table.bound.foldl
    (fun s (r, a) => if coveredRole r then s.insert a else s) {}
  let covered (a : Address) : Bool := coveredAt.contains a
  let parent := depsSearch look b
  -- the same search through uncovered records only
  let parentU := depsSearch look b (avoid := covered)
  -- a path of one step or more: the block itself is not in its closure
  let pathFrom (x : Address) : Option (List Nat) := (pathTo parent b x).filter (!·.isEmpty)
  -- a path the circuit accepts for a witness `x` stopping at `stop`
  -- (`KernelModeled::assert_covered_past`): no record on it covered, the stop included, or any
  -- path for a covered `x`
  let pathOk (x stop : Address) : Option (List Nat) :=
    (pathTo parentU b stop).filter (!·.isEmpty) <|> (if covered x then pathFrom stop else none)
  let roleOf (x : Address) : Option Nat := do
    let (r, _) ← table.bound.find? (·.2 == x)
    Ix.Kernel.Role.all.idxOf? r
  -- the witness of one outside reference: (address, kind, path, extra), with the paths `path`
  -- gives
  let classifyBy (path : Address → Address → Option (List Nat)) (x : Address) :
      Except String (Address × Nat × List Nat × List Nat) := do
    if let some steps := path x x then
      return (x, 1, steps, [])
    else if (roleOf x).any basisRoleAllowed then
      return (x, 0, [], [])
    else if let some (pb, idx, c1) := (look x).bind (fun c => match c.info with
        | .iPrj p => some (p.block, p.idx.toNat, 0)
        | .cPrj p => some (p.block, p.idx.toNat, p.cidx.toNat + 1)
        | _ => none) then
      -- a type or constructor of a block in the closure (its block's walk checks it)
      let some steps := path x pb
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
      let some steps := path x entry.block
        | throw s!"outside recursor {x} eliminates a block outside the closure"
      return (x, 2, steps, [])
  -- a witness by a path the circuit accepts; failing that, by the search's shortest path (the
  -- circuit refuses it: no witness of `x` passes `assert_covered_past`)
  let classify (x : Address) : Except String (Address × Nat × List Nat × List Nat) :=
    match classifyBy pathOk x with
    | .ok w => .ok w
    | .error _ => classifyBy (fun _ stop => pathFrom stop) x
  let mut deps : Array Address := (records.map (·.1)).push fk.recBlock
  let mut witnesses : Array (Address × Nat × List Nat × List Nat) := #[]
  for x in outside do
    let w ← classify x
    witnesses := witnesses.push w
    if w.2.1 == 2 then deps := deps.push x
  -- the references of a container's recursor family that the circuit cannot place by
  -- the container's block alone (`KernelModeled::container_refs_ok`: the block's
  -- used references, its members, members of the blocks its used references project
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
    -- the blocks the used references project from, and those an uncovered one projects from
    -- (`KernelModeled::ref_projects_from`: a hit through a covered used reference counts only
    -- for a covered reference)
    let (iusedRefs, irefBlocks, irefBlocksU) :
        Std.HashSet Address × Std.HashSet Address × Std.HashSet Address :=
      ibc.refs.zipIdx.foldl (fun (ur, ib, ibu) (q, j) =>
        if iused.contains j then
          (match (look q).bind projectionBlock? with
           | some pb => (ur.insert q, ib.insert pb, if covered q then ibu else ibu.insert pb)
           | none => (ur.insert q, ib, ibu))
        else (ur, ib, ibu)) ({}, {}, {})
    let used := usedIdxs fam
    for (r, j) in fam.refs.zipIdx do
      unless used.contains j do continue
      if iusedRefs.contains r then continue
      if outside.contains r || extra.contains r then continue
      let rc? := look r
      if (rc?.bind projectionBlock?) == some entry.block then continue
      let icBlock : Option Address := rc?.bind fun c => match c.info with
        | .iPrj p => some p.block
        | .cPrj p => some p.block
        | _ => none
      if icBlock.any (fun pb => irefBlocksU.contains pb || (covered r && irefBlocks.contains pb)) then
        continue
      extra := extra.push r
  -- likewise the block's own recursor family: its used references that the circuit cannot
  -- place by the block (`KernelModeled::family_refs_ok`: a used reference of the block, a
  -- type, constructor or recursor of the block, or a type or constructor of a block that one
  -- of the block's used references is a type, constructor or recursor of)
  if let some fam := look fk.recBlock then
    let bused := usedIdxs bc
    let typeCtorRecBlock (c : Ixon.Constant) : Option Address := match c.info with
      | .iPrj p => some p.block
      | .cPrj p => some p.block
      | .rPrj p => some p.block
      | _ => none
    let (busedRefs, brefBlocks, brefBlocksU) :
        Std.HashSet Address × Std.HashSet Address × Std.HashSet Address :=
      bc.refs.zipIdx.foldl (fun (br, bb, bbu) (q, j) =>
        if bused.contains j then
          (match (look q).bind typeCtorRecBlock with
           | some pb => (br.insert q, bb.insert pb, if covered q then bbu else bbu.insert pb)
           | none => (br.insert q, bb, bbu))
        else (br, bb, bbu)) ({}, {}, {})
    let used := usedIdxs fam
    for (r, j) in fam.refs.zipIdx do
      unless used.contains j do continue
      if busedRefs.contains r then continue
      if outside.contains r || extra.contains r then continue
      let rc? := look r
      if (rc?.bind typeCtorRecBlock) == some b then continue
      let icBlock : Option Address := rc?.bind fun c => match c.info with
        | .iPrj p => some p.block
        | .cPrj p => some p.block
        | _ => none
      if icBlock.any (fun pb => brefBlocksU.contains pb || (covered r && brefBlocks.contains pb)) then
        continue
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
  let mut projModels : Array (Address × Address) := #[]
  for (pmKey, piKey) in projKeys do
    let some pm := nm.gen[pmKey]? | throw s!"no projection model for {pmKey}"
    let some pi := nm.gen[piKey]? | throw s!"no projection iota for {piKey}"
    projModels := projModels.push (pm, pi)
  -- Deduplicate `deps` preserving order
  let mut depSeen : Std.HashSet Address := {}
  let mut dedupDeps : Array Address := #[]
  for d in deps do
    unless depSeen.contains d do
      depSeen := depSeen.insert d
      dedupDeps := dedupDeps.push d
  let isCPrj : Ixon.Constant → Bool
    | ⟨.cPrj _, _, _, _, _⟩ => true
    | _ => false
  let adviceAddrs := (records.filter fun (_, c) => !isCPrj c).map (·.1)
  let layout : Payload := { recBlock := fk.recBlock, advice := adviceAddrs, witnesses,
                            typeModels, ctorModels, recModels, iotas, projModels }
  return { layout, records, hints, blobs, deps := dedupDeps }

/-! ## The advice's binder data

A generated record carries its binder-data section like any record, so its
address covers the data IxVM reads from it. The records are encoded first (each
naming the ones before it by address), then installed once into IxC's kernel
environment (`IxVM.PwHints.KernelEnv.ofView`, typed against the environment's
records), and then re-addressed bottom-up: each record's references to the
advice follow their new addresses, the record is put in the compiler's form
again (reusing the existing sharing directly when `refs` remain strictly
ascending, otherwise calling `renormalize`), its section is computed directly
against the already-built `KernelEnv` by mapping its refs back to their
unsectioned addresses (`localInv`, falling back to `sectionsOf` only on an
address collision), and it is hashed. So every advice record is the record the
compiler would write for its declaration, without rebuilding the kernel
environment per record. The payload, hints and dependencies name the new
addresses. -/

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
  let view : IxVM.PwHints.View :=
    { records := adv.records, support, blobs, hints, table := some chosen.1.toBytes, models }
  let kEnv ← IxVM.PwHints.KernelEnv.ofView view (prelude? := some chosen)
  let core := Ix.Kernel.Cached.coreKnotI .verified kEnv.fe Ix.Kernel.checkFuel
  let store : Std.HashMap Address Ixon.Constant :=
    adv.records.foldl (fun m (a, c) => m.insert a c) {}
  let order ← Ix.Compile.BinderData.bottomUp store adv.records
  let mut renamed : Std.HashMap Address Address := {}
  let mut rewritten : Std.HashMap Address Ixon.Constant := {}
  for a in order do
    let some c := store[a]? | continue
    let rename (x : Address) : Address := renamed.getD x x
    let c1 ← match c.info with
      | .iPrj _ | .cPrj _ | .rPrj _ | .dPrj _ =>
        pure (Ix.Compile.BinderData.rewriteRecord rename c #[])
      | _ =>
        let refs' := c.refs.map rename
        if tablesCanonical c && ascendingBy refs' (fun x y => x.cmpBytes y == .lt) then
          pure { c with refs := refs', binders := #[] }
        else
          renormalize rename c
    let binders ←
      if (IxVM.PwHints.roots c1).isEmpty then pure #[]
      else if IxVM.RecordSections.unsafeOrPartial c1 then
        Ix.Compile.BinderData.stripSection c1
      else do
        -- Map `c1.refs` back to their unsectioned addresses in `kEnv` (local to `c.refs` so
        -- unchanged `support` refs never collide with renamed advice addresses).
        let mut localInv : Std.HashMap Address Address := {}
        let mut collision := false
        for r in c.refs do
          let r' := rename r
          match localInv[r']? with
          | some prev => if prev != r then collision := true
          | none => localInv := localInv.insert r' r
        if !collision then
          let c1Old := { c1 with refs := c1.refs.map (fun x => localInv.getD x x) }
          let (blocks, _, _) := IxVM.PwHints.annotateRecord kEnv core a c1Old (taint := true)
          Ix.Compile.BinderData.sectionOf c1 blocks
        else
          let a1 := addressOf c1
          let done := rewritten.toArray
          let fresh ← IxVM.RecordSections.sectionsOf #[(a1, c1)] (support ++ done) blobs hints chosen
            (models := done.foldl (fun s (x, _) => s.insert x) ({} : Std.HashSet Address))
          pure (fresh.getD a1 #[])
    let c' := { c1 with binders }
    let a' := addressOf c'
    renamed := renamed.insert a a'
    rewritten := rewritten.insert a' c'
  let rename (x : Address) : Address := renamed.getD x x
  -- the records in their original order, each once
  let mut records : Array (Address × Ixon.Constant) := #[]
  let mut seen : Std.HashSet Address := {}
  for (a, _) in adv.records do
    let a' := rename a
    if seen.contains a' then continue
    let some c' := rewritten[a']? | throw s!"model advice: record {a} was not re-addressed"
    seen := seen.insert a'
    records := records.push (a', c')
  let mut hints' : Array (Address × Lean.ReducibilityHints) := #[]
  let mut hintSeen : Std.HashSet Address := {}
  for (a, h) in adv.hints do
    let a' := rename a
    unless hintSeen.contains a' do
      hintSeen := hintSeen.insert a'
      hints' := hints'.push (a', h)
  let mut deps' : Array Address := #[]
  let mut depSeen : Std.HashSet Address := {}
  for d in adv.deps do
    let d' := rename d
    unless depSeen.contains d' do
      depSeen := depSeen.insert d'
      deps' := deps'.push d'
  let l := adv.layout
  let mut advice' : Array Address := #[]
  let mut adviceSeen : Std.HashSet Address := {}
  for a in l.advice do
    let a' := rename a
    unless adviceSeen.contains a' do
      adviceSeen := adviceSeen.insert a'
      advice' := advice'.push a'
  let layout : Payload := { l with
    recBlock := rename l.recBlock
    advice := advice'
    witnesses := l.witnesses.map (fun (x, k, steps, extra) => (rename x, k, steps, extra))
    typeModels := l.typeModels.map rename
    ctorModels := l.ctorModels.map rename
    recModels := l.recModels.map rename
    iotas := l.iotas.map rename
    projModels := l.projModels.map (fun (pm, pi) => (rename pm, rename pi)) }
  return { adv with layout, records, hints := hints', deps := deps' }

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
    if lc.peekTag.toOption != some .muts then continue
    if let some c := lc.get? then
      if let .muts ms := c.info then
        if ms.any (fun m => match m with | .indc _ => true | _ => false) then
          env := { env with models := env.models.insert a ByteArray.empty }
  return env

/-- Whether a generated one-type inductive block has a constructor field domain that
mentions the family other than as the head of a direct or reflexive recursive field:
`fieldErase` (`IxC/Kernel/Frontend/InModel/Nested.lean`) leaves such an occurrence under
a redex that positivity's WHNF (`normPosDom`) reduces away when generating the recursor,
so the generated recursor record must carry the normalized domain too. -/
def indNeedsRecNorm (block : List (ConstantInfo .anon)) (nP : Nat) : Bool :=
  let tys := block.filterMap fun ci => match ci with | .indInfo cv _ => some cv | _ => none
  match tys with
  | [cvT] =>
    let T := cvT.name
    let tHead : Expr .anon := .const T (cvT.levelParams.map .param)
    let rec piDomMentions : Expr .anon → Bool
      | .forallE ty b _ => ty.mentionsConst T || piDomMentions b
      | _ => false
    block.any fun ci => match ci with
      | .ctorInfo cv _ cF =>
        match cv.type.stripPis (nP + cF) with
        | some (bs, _) =>
          (bs.drop nP).any fun (d, _) =>
            d.mentionsConst T &&
              (d.piResult.getAppFn != tHead || piDomMentions d ||
                (d.piResult.getAppArgs.drop nP).any (·.mentionsConst T))
        | none => false
      | _ => false
  | _ => false

/-- Replace the constructors and recursor of any generated `.indDecl` that
`indNeedsRecNorm` flags with those IxC's native install computes over the
normalized constructor domains (`ctorsA`, `cvRa`, and `sumRules`), installing
`d` first if `k.fe` does not already hold it, so the advice records pass
`KernelCheck`'s syntactic positivity and native recursor checks. -/
def normGeneratedRecs (gen : List (Declaration .anon)) (k : IxVM.PwHints.KernelEnv) :
    List (Declaration .anon) := Id.run do
  let mut fe := k.fe
  let mut pos := 0
  let mut out : Array (Declaration .anon) := #[]
  for d in gen do
    match d with
    | .indDecl block nP =>
      if indNeedsRecNorm block nP then
        if block.any (fun ci => (fe.find? ci.name).isNone) then
          let (fe', pos', _) := IxVM.PwHints.installDecl k.setup.evidence fe pos d
          fe := fe'
          pos := pos'
        let block' := block.map fun ci => match ci with
          | .ctorInfo cvC _ _ =>
            match fe.find? cvC.name with
            | some ci'@(.ctorInfo ..) => ci'
            | _ => ci
          | .recInfo cvR _ _ _ =>
            match fe.find? cvR.name with
            | some (.recInfo cvRa mI rP rules) => .recInfo cvRa mI rP rules
            | _ => ci
          | _ => ci
        out := out.push (.indDecl block' nP)
      else
        if block.any (fun ci => (fe.find? ci.name).isNone) then
          let (fe', pos', _) := IxVM.PwHints.installDecl k.setup.evidence fe pos d
          fe := fe'
          pos := pos'
        out := out.push d
    | .defnDecl cv _ _ | .thmDecl cv _ | .axiomDecl cv | .opaqueDecl cv _ | .quotDecl _ cv =>
      if (fe.find? cv.name).isNone then
        let (fe', pos', _) := IxVM.PwHints.installDecl k.setup.evidence fe pos d
        fe := fe'
        pos := pos'
      out := out.push d
    | .basisDecl _ => out := out.push d
  return out.toList

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
  -- rebuild all five derived maps from empty maps so stale advice cannot outlive an edit
  let env := env.clearModels
  -- an environment whose binding or prelude does not read gets no model (its claims
  -- are decided without one: a modeled block in them is refused)
  let fallback := ({ withEmptyPayloads env with modelsAttached := true }, ({} : Report))
  let table? : Option Ix.Kernel.RoleTable := match env.roleBinding with
    | some b => Ix.Kernel.RoleTable.ofBytes b.bytes
    | none => Ix.Kernel.Reader.defaultTable.toOption
  let some table := table? | return fallback
  let .ok (pre : Ix.Kernel.Reader.Prelude .anon) := Ix.Kernel.Reader.preludeFor table | return fallback
  let fallbackRecs := pre.records ++ pre.evidence
  let fallbackMap : Std.HashMap Address Ixon.Constant :=
    fallbackRecs.foldl (fun m (a, c) => m.insert a c) {}
  let fallbackBlobMap : Std.HashMap Address ByteArray :=
    pre.blobs.foldl (fun m (a, b) => if m.contains a then m else m.insert a b) {}
  -- Only `.recr` and `.muts` records have `recursorMembers` non-empty; decode just those
  -- (in parallel for large environments) to build the recursor index and locate modeled blocks.
  let recOrMutsRaw : Array (Address × Ixon.LazyConstant) := Id.run do
    let mut out : Array (Address × Ixon.LazyConstant) := #[]
    for (a, lc) in env.consts do
      match lc.peekTag with
      | .ok .recr | .ok .muts => out := out.push (a, lc)
      | _ => pure ()
    return out
  let recOrMuts : Array (Address × Ixon.Constant) := Id.run do
    if recOrMutsRaw.size < 256 then
      return recOrMutsRaw.filterMap fun (a, lc) => lc.get?.map (a, ·)
    let numTasks := min 32 ((recOrMutsRaw.size + 63) / 64)
    let chunk := (recOrMutsRaw.size + numTasks - 1) / numTasks
    let tasks := (Array.range numTasks).filterMap fun t =>
      let lo := t * chunk
      if lo ≥ recOrMutsRaw.size then none
      else
        let hi := min recOrMutsRaw.size (lo + chunk)
        some <| Task.spawn fun _ => Id.run do
          let mut part : Array (Address × Ixon.Constant) := Array.mkEmpty (hi - lo)
          for i in [lo:hi] do
            let (a, lc) := recOrMutsRaw[i]!
            if let some c := lc.get? then part := part.push (a, c)
          return part
    return tasks.foldl (init := Array.mkEmpty recOrMutsRaw.size) fun acc t => acc ++ t.get
  let recOrMutsMap : Std.HashMap Address Ixon.Constant :=
    recOrMuts.foldl (init := Std.HashMap.emptyWithCapacity recOrMuts.size) fun m (a, c) => m.insert a c
  let lazyLook : Ix.Kernel.Reader.Store := fun a =>
    recOrMutsMap[a]? <|> (env.consts[a]?.bind (·.get?)) <|> fallbackMap[a]?
  let isInputIndexed (a : Address) (c : Ixon.Constant) : Bool :=
    let members := Ix.Kernel.Reader.recursorMembers c
    if members.isEmpty then true else
    let tbl := Ix.Kernel.Reader.Shape.sharing c.sharing
    members.all (fun (_, r) =>
      match Ix.Kernel.Reader.analyseRecursorPrepared lazyLook a c tbl r with
      | some (_, carriers, _) =>
        match carriers[0]? with
        | some (ConstRef.member b _) => env.consts.contains b
        | _ => true
      | none => true) || fallbackMap[a]? == some c
  let isFallbackIndexed (a : Address) (c : Ixon.Constant) : Bool :=
    let members := Ix.Kernel.Reader.recursorMembers c
    if members.isEmpty then true else
    let tbl := Ix.Kernel.Reader.Shape.sharing c.sharing
    members.all fun (_, r) =>
      match Ix.Kernel.Reader.analyseRecursorPrepared lazyLook a c tbl r with
      | some (_, carriers, _) =>
        match carriers[0]? with
        | some (ConstRef.member b _) => !env.consts.contains b
        | _ => true
      | none => true
  let indexed :=
    recOrMuts.filter (fun (a, c) => isInputIndexed a c) ++
    fallbackRecs.filter (fun (a, c) => !env.consts.contains a && isFallbackIndexed a c)
  let initIndex := Ix.Kernel.Reader.buildIndex lazyLook indexed
  -- the modeled blocks: several types, or more recursors than types (nested)
  let mut roots : Array Address := #[]
  let mut extra : Std.HashMap Address (Array Address) := {}
  for (b, shape) in initIndex.blocks do
    let recBlocks := shape.recs.foldl (fun acc (r : ConstRef Address) => match r with
      | .member o _ => if acc.contains o then acc else acc.push o
      | _ => acc) #[]
    extra := extra.insert b recBlocks
    if shape.order.size > 1 || shape.recs.size > shape.order.size then roots := roots.push b
  if roots.isEmpty then return ({ withEmptyPayloads env with modelsAttached := true }, {})
  let roleSeeds : Array Address :=
    table.bound.filterMap fun (_, ra) => if env.consts.contains ra then some ra else none
  -- Decode ONLY the transitive closure of `roots ++ roleSeeds` (plus their projection wrappers),
  -- avoiding deserializing hundreds of thousands of unrelated definitions.
  let store : Ixon.CheckOrder.RecordStore := Id.run do
    let mut st : Ixon.CheckOrder.RecordStore := {}
    let mut visited : Std.HashSet Address := {}
    let mut todo : Array Address := roots ++ roleSeeds
    while h : todo.size > 0 do
      let a := todo[todo.size - 1]
      todo := todo.pop
      if visited.contains a then continue
      visited := visited.insert a
      let some c := recOrMutsMap[a]? <|> (env.consts[a]?.bind (·.get?)) | continue
      st := st.insert a c
      let o := Ixon.CheckOrder.owner a c
      if o != a then
        if !visited.contains o then todo := todo.push o
      else
        for r in c.refs do
          if !visited.contains r && env.consts.contains r then todo := todo.push r
        if let some ex := extra[o]? then
          for r in ex do
            if !visited.contains r && env.consts.contains r then todo := todo.push r
        if let .muts members := c.info then
          let mut i : UInt64 := 0
          for m in members do
            let info : Ixon.ConstantInfo := match m with
              | .defn _ => .dPrj ⟨i, o⟩
              | .indc _ => .iPrj ⟨i, o⟩
              | .recr _ => .rPrj ⟨i, o⟩
            let pc := projRecord info
            let pa := addressOf pc
            if env.consts.contains pa && !st.contains pa then
              st := st.insert pa pc
            if let .indc ind := m then
              let mut cidx : UInt64 := 0
              for _ in ind.ctors do
                let cpc := projRecord (.cPrj ⟨i, cidx, o⟩)
                let cpa := addressOf cpc
                if env.consts.contains cpa && !st.contains cpa then
                  st := st.insert cpa cpc
                cidx := cidx + 1
            i := i + 1
    return st
  let subRecords : Array (Address × Ixon.Constant) := store.toArray
  let byOwner : Std.HashMap Address (Array (Address × Ixon.Constant)) :=
    subRecords.foldl (init := Std.HashMap.emptyWithCapacity (subRecords.size / 2)) fun m (ra, rc) =>
      let o := Ixon.CheckOrder.owner ra rc
      m.alter o fun xs => some ((xs.getD #[]).push (ra, rc))
  let look : Ix.Kernel.Reader.Store := fun a => store[a]? <|> fallbackMap[a]?
  let blobLook : Address → Option ByteArray := fun a => env.blobs[a]? <|> fallbackBlobMap[a]?
  let allSub := subRecords ++ fallbackRecs.filter (fun (a, _) => !store.contains a)
  let subIndexed := indexed.filter fun (a, _) => store.contains a || !env.consts.contains a
  let cx : Ix.Kernel.Reader.Ctx .anon :=
    Ix.Kernel.Reader.contextWith look blobLook table allSub
      (fun _ => none) (Ix.Kernel.Admission.projectionAddress Address.blake3 look) subIndexed
  let supportFor (seeds : Array Address) : Array (Address × Ixon.Constant) := Id.run do
    let closureOwners := Ixon.CheckOrder.closure store extra (roleSeeds ++ seeds)
    let mut out : Array (Address × Ixon.Constant) := #[]
    for o in closureOwners do
      for entry in byOwner.getD o #[] do
        out := out.push entry
    return out
  let owners : Std.HashSet Address :=
    (Ixon.CheckOrder.closure store extra (roots ++ roleSeeds)).foldl (·.insert ·) {}
  let sub := subRecords.filter fun (a, c) => owners.contains (Ixon.CheckOrder.owner a c)
  let ordered := Ixon.CheckOrder.wholeEnv table pre sub
  let rootSet : Std.HashSet Address := roots.foldl (·.insert ·) {}
  let mut st := pre.state
  let mut extEqHelpers : Std.HashMap (Key .anon) EqReflHelper := {}
  let mut env := env
  let mut report : Report := {}
  let mut work : Array (Address × Ixon.Constant × Ix.Kernel.Reader.BlockShape × List (Declaration .anon) × Bool) := #[]
  for a in ordered do
    let some c := store[a]? | continue
    match Ix.Kernel.Reader.readRecord cx st a c with
    | .error why =>
      if rootSet.contains a then report := { report with blocks := report.blocks.push (a, .error s!"the reader: {why}") }
    | .ok r =>
      st := st.commit r
      for d in r.decls do
        match d with
        | .defnDecl cv v _ | .thmDecl cv v =>
          if let some eh := recognizeEqReflHelper extEqHelpers true cv v then
            extEqHelpers := extEqHelpers.insert cv.name eh
        | _ => pure ()
      unless rootSet.contains a do continue
      if r.generated == 0 then
        report := { report with blocks := report.blocks.push (a, .error "the reader generated no model")}
        continue
      let some shape := cx.index.blocks[a]? | continue
      let gen0 := r.decls.toList.take r.generated
      let needNorm := gen0.any fun | .indDecl b nP => indNeedsRecNorm b nP | _ => false
      work := work.push (a, c, shape, gen0, needNorm)
  let anyNorm := work.any fun (_, _, _, _, n) => n
  let kEnv? : Option IxVM.PwHints.KernelEnv :=
    if anyNorm then
      let view : IxVM.PwHints.View :=
        { records := sub, support := supportFor #[], blobs := env.blobs,
          hints := env.anonHints, table := some table.toBytes }
      (IxVM.PwHints.KernelEnv.ofView view (prelude? := some (table, pre))).toOption
    else none
  let runOne (item : Address × Ixon.Constant × Ix.Kernel.Reader.BlockShape × List (Declaration .anon) × Bool) :
      Address × Except String BlockAdvice :=
    let (a, c, shape, gen0, needNorm) := item
    let gen := if needNorm then
        match kEnv? with | some k => normGeneratedRecs gen0 k | none => gen0
      else gen0
    let advice := blockAdvice table look cx a c shape gen tweak extEqHelpers >>= fun adv =>
      let advSet : Std.HashSet Address := adv.records.foldl (fun s (x, _) => s.insert x) {}
      let seeds : Array Address := Id.run do
        let mut s : Array Address := #[a]
        for (_, rc) in adv.records do
          for r in rc.refs do
            if !advSet.contains r && store.contains r then s := s.push r
        for d in adv.deps do
          if !advSet.contains d && store.contains d then s := s.push d
        return s
      adv.withSections (supportFor seeds) env.blobs env.anonHints (table, pre)
    (a, advice)
  let results : Array (Address × Except String BlockAdvice) :=
    if work.size ≤ 1 then work.map runOne
    else
      let tasks := work.map fun item => Task.spawn fun _ => runOne item
      tasks.map (·.get)
  for (a, advice) in results do
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
