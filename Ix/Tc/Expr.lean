module

public import Ix.Tc.Mode
public import Ix.Tc.Id
public import Ix.Tc.Level
public import Ix.Address
public import Ix.Unsigned

/-!
Mirror: crates/kernel/src/expr.rs

Expressions with optional metadata. Each variant carries an `ExprInfo m` with
its Blake3 address, substitution annotations (`lbr`, `count0`), an fvar
reachability flag, and (meta mode) mdata.

Hash contract (byte-exact vs Rust; metadata excluded in BOTH modes):

| node                  | preimage                                            |
|-----------------------|-----------------------------------------------------|
| `var i`               | `[EVAR] ++ i.toLEBytes` (8-byte LE)                 |
| `fvar id`             | `[EFVAR] ++ id.toLEBytes`                           |
| `sort u`              | `[ESORT] ++ u.addr`                                 |
| `const id us`         | `[EREF] ++ id.addr ++ us[0].addr ++ …`              |
| `app f a`             | `[EAPP] ++ f.addr ++ a.addr`                        |
| `lam ty body`         | `[ELAM] ++ ty.addr ++ body.addr`                    |
| `all ty body`         | `[EALL] ++ ty.addr ++ body.addr`                    |
| `letE ty val body nd` | `[ELET] ++ ty.addr ++ val.addr ++ body.addr ++ [nd]`|
| `prj id f val`        | `[EPRJ] ++ id.addr ++ f.toLEBytes ++ val.addr`      |
| `nat _ blob`          | `[ENAT] ++ blob` (value itself NOT hashed)          |
| `str _ blob`          | `[ESTR] ++ blob` (value itself NOT hashed)          |

`letE`'s `nonDep` IS hashed (dropping it would conflate letEs differing only
in `nonDep` and break Ixon roundtrip fidelity). Binder names, binder info,
and mdata are never hashed — hash equality is alpha-invariant in meta mode.
-/

public section
@[expose] section

namespace Ix.Tc

open Blake3.Rust (Hasher)

/-- A single mdata layer: key-value pairs from Lean's `Expr.mdata`. -/
abbrev MData := Array (Name × Ix.DataValue)

/-- Per-expression info: Blake3 address, substitution annotations, mdata. -/
structure ExprInfo (m : Mode) where
  /-- Blake3 hash of semantic expression content. Metadata fields are stored
      for diagnostics/egress but do not contribute to the hash. -/
  addr : Address
  /-- Loose bound variable range: upper bound on free de Bruijn indices. -/
  lbr : UInt64
  /-- Count of free `var 0` occurrences. -/
  count0 : UInt64
  /-- Whether any `fvar` occurrence is reachable in this expression. Computed
      at construction and propagated via OR, so the check is O(1). -/
  hasFVars : Bool
  /-- Lean mdata annotations. Semantically transparent, erased in anon mode. -/
  mdata : m.F (Array MData)
  /-- Metadata-AWARE content address (meta mode only): Blake3 over the
      semantic `addr` plus this node's metadata (binder/const/prj names,
      binder infos, mdata layers) plus the children's `metaAddr`s. The
      semantic `addr` stays metadata-blind (anon/meta address parity is
      load-bearing); `metaAddr` exists so meta-mode interning and egress
      memoization key on FULL fidelity — a metadata-blind key would
      collapse alpha-identical subtrees first-wins and lose per-occurrence
      names/infos/mdata (the exact drift that forced Rust's roundtrip off
      the direct `lean_egress` path). Checking never reads it: every
      semantic cache keys by `addr`. Universe display names are excluded —
      level egress resolves parameter names positionally. -/
  metaAddr : m.F Address

/-- Expression. Each variant carries its `ExprInfo m`. -/
inductive KExpr (m : Mode) where
  | var (idx : UInt64) (name : m.F Name) (info : ExprInfo m)
  /-- Free variable: opaque identity from the active local context. `FVarId`
      participates in the content hash; the name is display-only. The type
      lives in the active `LocalContext`, not on the node. -/
  | fvar (id : FVarId) (name : m.F Name) (info : ExprInfo m)
  | sort (u : KUniv m) (info : ExprInfo m)
  | const (id : KId m) (us : Array (KUniv m)) (info : ExprInfo m)
  | app (f a : KExpr m) (info : ExprInfo m)
  | lam (name : m.F Name) (bi : m.F Lean.BinderInfo) (ty body : KExpr m)
      (info : ExprInfo m)
  | all (name : m.F Name) (bi : m.F Lean.BinderInfo) (ty body : KExpr m)
      (info : ExprInfo m)
  | letE (name : m.F Name) (ty val body : KExpr m) (nonDep : Bool)
      (info : ExprInfo m)
  /-- Projection: struct type id, field index, struct value. -/
  | prj (id : KId m) (field : UInt64) (val : KExpr m) (info : ExprInfo m)
  | nat (val : Nat) (blob : Address) (info : ExprInfo m)
  | str (val : String) (blob : Address) (info : ExprInfo m)

namespace KExpr

def info : KExpr m → ExprInfo m
  | .var _ _ i
  | .fvar _ _ i
  | .sort _ i
  | .const _ _ i
  | .app _ _ i
  | .lam _ _ _ _ i
  | .all _ _ _ _ i
  | .letE _ _ _ _ _ i
  | .prj _ _ _ i
  | .nat _ _ i
  | .str _ _ i => i

@[inline] def addr (e : KExpr m) : Address := e.info.addr
@[inline] def lbr (e : KExpr m) : UInt64 := e.info.lbr
@[inline] def count0 (e : KExpr m) : UInt64 := e.info.count0
@[inline] def hasFVars (e : KExpr m) : Bool := e.info.hasFVars
@[inline] def mdata (e : KExpr m) : m.F (Array MData) := e.info.mdata

/-- The metadata-aware address as a plain `Address` (meta mode; `default`
    is unreachable — every meta node carries one). -/
@[inline] def metaAddrD (e : KExpr m) : Address :=
  (Mode.get? e.info.metaAddr).getD default

/-- Intern/memo key: metadata-blind in anon mode, metadata-aware in meta
    mode (see `ExprInfo.metaAddr`). -/
def internKey : {m : Mode} → KExpr m → Address
  | .anon, e => e.addr
  | .«meta», e => e.info.metaAddr

/-- Content-addressed equality (Rust `hash_eq`). -/
instance : BEq (KExpr m) where
  beq a b := a.addr == b.addr

instance : Hashable (KExpr m) where
  hash e := hash e.addr

@[inline] def noMData {m : Mode} : m.F (Array MData) := Mode.field #[]

/-! ### Smart constructors

Each computes the Blake3 address per the module-doc contract and the derived
`ExprInfo` invariants. Rust's hash-first/`*_with_addr` split (alloc avoidance
for intern-table pre-checks) is intentionally not ported: construct, then
intern.

The `metaAddr` thunks below only ever run in meta mode (`Mode.fieldWith`
discards them unevaluated in anon mode), so the anon hot path pays
nothing. -/

/-- Fold a metadata name field into a hasher (meta-mode thunks only). -/
@[inline] def hashFName {m : Mode} (h : Hasher) (n : m.F Name) : Hasher :=
  h.update ((Mode.get? n).getD Ix.Name.mkAnon).getHash.hash

/-- Fold a metadata binder-info field into a hasher. -/
@[inline] def hashFBi {m : Mode} (h : Hasher) (bi : m.F Lean.BinderInfo) :
    Hasher :=
  h.update ⟨#[match (Mode.get? bi).getD .default with
    | .default => 0 | .implicit => 1
    | .strictImplicit => 2 | .instImplicit => 3]⟩

/-- Fold mdata layers into a hasher. -/
def hashFMData {m : Mode} (h : Hasher) (md : m.F (Array MData)) : Hasher :=
  Id.run do
    let layers := (Mode.get? md).getD #[]
    let mut h := h.update layers.size.toUInt64.toLEBytes
    for layer in layers do
      h := h.update layer.size.toUInt64.toLEBytes
      for (n, dv) in layer do
        h := h.update n.getHash.hash
        h := Ix.Expr.hashDataValue h dv
    return h

def mkVar (idx : UInt64) (name : m.F Name)
    (mdata : m.F (Array MData) := noMData) : KExpr m := Id.run do
  let mut h := Hasher.init ()
  h := h.update ⟨#[Ix.TAG_EVAR]⟩
  h := h.update idx.toLEBytes
  let addr := Address.mk (h.finalizeWithLength 32).val
  let metaAddr : m.F Address := Mode.fieldWith fun () => Id.run do
    let mut mh := Hasher.init ()
    mh := mh.update addr.hash
    mh := hashFName mh name
    mh := hashFMData mh mdata
    return Address.mk (mh.finalizeWithLength 32).val
  return .var idx name
    { addr, lbr := idx + 1, count0 := if idx == 0 then 1 else 0,
      hasFVars := false, mdata, metaAddr }

def mkFVar (id : FVarId) (name : m.F Name)
    (mdata : m.F (Array MData) := noMData) : KExpr m := Id.run do
  let mut h := Hasher.init ()
  h := h.update ⟨#[Ix.TAG_EFVAR]⟩
  h := h.update id.id.toLEBytes
  let addr := Address.mk (h.finalizeWithLength 32).val
  -- FVars are leaves: no loose bvars, no var-0 occurrences; hasFVars is true
  -- since this node *is* an fvar.
  let metaAddr : m.F Address := Mode.fieldWith fun () => Id.run do
    let mut mh := Hasher.init ()
    mh := mh.update addr.hash
    mh := hashFName mh name
    mh := hashFMData mh mdata
    return Address.mk (mh.finalizeWithLength 32).val
  return .fvar id name
    { addr, lbr := 0, count0 := 0, hasFVars := true, mdata, metaAddr }

def mkSort (u : KUniv m) (mdata : m.F (Array MData) := noMData) : KExpr m :=
  Id.run do
    let mut h := Hasher.init ()
    h := h.update ⟨#[Ix.TAG_ESORT]⟩
    h := h.update u.addr.hash
    let addr := Address.mk (h.finalizeWithLength 32).val
    let metaAddr : m.F Address := Mode.fieldWith fun () => Id.run do
      let mut mh := Hasher.init ()
      mh := mh.update addr.hash
      mh := hashFMData mh mdata
      return Address.mk (mh.finalizeWithLength 32).val
    return .sort u
      { addr, lbr := 0, count0 := 0, hasFVars := false, mdata, metaAddr }

/-- `id.addr` is the constant's content address — its identity. `id.name` is
    display-only and NOT hashed. -/
def mkConst (id : KId m) (us : Array (KUniv m))
    (mdata : m.F (Array MData) := noMData) : KExpr m := Id.run do
  let mut h := Hasher.init ()
  h := h.update ⟨#[Ix.TAG_EREF]⟩
  h := h.update id.addr.hash
  for u in us do
    h := h.update u.addr.hash
  let addr := Address.mk (h.finalizeWithLength 32).val
  let metaAddr : m.F Address := Mode.fieldWith fun () => Id.run do
    let mut mh := Hasher.init ()
    mh := mh.update addr.hash
    mh := hashFName mh id.name
    mh := hashFMData mh mdata
    return Address.mk (mh.finalizeWithLength 32).val
  return .const id us
    { addr, lbr := 0, count0 := 0, hasFVars := false, mdata, metaAddr }

def mkApp (f a : KExpr m) (mdata : m.F (Array MData) := noMData) : KExpr m :=
  Id.run do
    let mut h := Hasher.init ()
    h := h.update ⟨#[Ix.TAG_EAPP]⟩
    h := h.update f.addr.hash
    h := h.update a.addr.hash
    let addr := Address.mk (h.finalizeWithLength 32).val
    let metaAddr : m.F Address := Mode.fieldWith fun () => Id.run do
      let mut mh := Hasher.init ()
      mh := mh.update addr.hash
      mh := mh.update f.metaAddrD.hash
      mh := mh.update a.metaAddrD.hash
      mh := hashFMData mh mdata
      return Address.mk (mh.finalizeWithLength 32).val
    return .app f a
      { addr, lbr := max f.lbr a.lbr, count0 := f.count0 + a.count0,
        hasFVars := f.hasFVars || a.hasFVars, mdata, metaAddr }

/-- Binder `name`/`bi` are display/elaboration metadata only: NOT hashed. -/
def mkLam (name : m.F Name) (bi : m.F Lean.BinderInfo) (ty body : KExpr m)
    (mdata : m.F (Array MData) := noMData) : KExpr m := Id.run do
  let mut h := Hasher.init ()
  h := h.update ⟨#[Ix.TAG_ELAM]⟩
  h := h.update ty.addr.hash
  h := h.update body.addr.hash
  let addr := Address.mk (h.finalizeWithLength 32).val
  let metaAddr : m.F Address := Mode.fieldWith fun () => Id.run do
    let mut mh := Hasher.init ()
    mh := mh.update addr.hash
    mh := hashFName mh name
    mh := hashFBi mh bi
    mh := mh.update ty.metaAddrD.hash
    mh := mh.update body.metaAddrD.hash
    mh := hashFMData mh mdata
    return Address.mk (mh.finalizeWithLength 32).val
  return .lam name bi ty body
    { addr, lbr := max ty.lbr body.lbr.sat1, count0 := ty.count0,
      hasFVars := ty.hasFVars || body.hasFVars, mdata, metaAddr }

/-- See `mkLam` — binder `name`/`bi` intentionally not hashed. -/
def mkAll (name : m.F Name) (bi : m.F Lean.BinderInfo) (ty body : KExpr m)
    (mdata : m.F (Array MData) := noMData) : KExpr m := Id.run do
  let mut h := Hasher.init ()
  h := h.update ⟨#[Ix.TAG_EALL]⟩
  h := h.update ty.addr.hash
  h := h.update body.addr.hash
  let addr := Address.mk (h.finalizeWithLength 32).val
  let metaAddr : m.F Address := Mode.fieldWith fun () => Id.run do
    let mut mh := Hasher.init ()
    mh := mh.update addr.hash
    mh := hashFName mh name
    mh := hashFBi mh bi
    mh := mh.update ty.metaAddrD.hash
    mh := mh.update body.metaAddrD.hash
    mh := hashFMData mh mdata
    return Address.mk (mh.finalizeWithLength 32).val
  return .all name bi ty body
    { addr, lbr := max ty.lbr body.lbr.sat1, count0 := ty.count0,
      hasFVars := ty.hasFVars || body.hasFVars, mdata, metaAddr }

/-- Binder `name` not hashed; `nonDep` IS hashed (see module doc). -/
def mkLet (name : m.F Name) (ty val body : KExpr m) (nonDep : Bool)
    (mdata : m.F (Array MData) := noMData) : KExpr m := Id.run do
  let mut h := Hasher.init ()
  h := h.update ⟨#[Ix.TAG_ELET]⟩
  h := h.update ty.addr.hash
  h := h.update val.addr.hash
  h := h.update body.addr.hash
  h := h.update ⟨#[if nonDep then 1 else 0]⟩
  let addr := Address.mk (h.finalizeWithLength 32).val
  let metaAddr : m.F Address := Mode.fieldWith fun () => Id.run do
    let mut mh := Hasher.init ()
    mh := mh.update addr.hash
    mh := hashFName mh name
    mh := mh.update ty.metaAddrD.hash
    mh := mh.update val.metaAddrD.hash
    mh := mh.update body.metaAddrD.hash
    mh := hashFMData mh mdata
    return Address.mk (mh.finalizeWithLength 32).val
  return .letE name ty val body nonDep
    { addr, lbr := max (max ty.lbr val.lbr) body.lbr.sat1,
      count0 := ty.count0 + val.count0,
      hasFVars := ty.hasFVars || val.hasFVars || body.hasFVars, mdata,
      metaAddr }

/-- `id.name` is display-only and NOT hashed. -/
def mkPrj (id : KId m) (field : UInt64) (val : KExpr m)
    (mdata : m.F (Array MData) := noMData) : KExpr m := Id.run do
  let mut h := Hasher.init ()
  h := h.update ⟨#[Ix.TAG_EPRJ]⟩
  h := h.update id.addr.hash
  h := h.update field.toLEBytes
  h := h.update val.addr.hash
  let addr := Address.mk (h.finalizeWithLength 32).val
  let metaAddr : m.F Address := Mode.fieldWith fun () => Id.run do
    let mut mh := Hasher.init ()
    mh := mh.update addr.hash
    mh := hashFName mh id.name
    mh := mh.update val.metaAddrD.hash
    mh := hashFMData mh mdata
    return Address.mk (mh.finalizeWithLength 32).val
  return .prj id field val
    { addr, lbr := val.lbr, count0 := val.count0, hasFVars := val.hasFVars,
      mdata, metaAddr }

/-- The literal value is NOT hashed — only the blob address is. -/
def mkNat (val : Nat) (blob : Address)
    (mdata : m.F (Array MData) := noMData) : KExpr m := Id.run do
  let mut h := Hasher.init ()
  h := h.update ⟨#[Ix.TAG_ENAT]⟩
  h := h.update blob.hash
  let addr := Address.mk (h.finalizeWithLength 32).val
  let metaAddr : m.F Address := Mode.fieldWith fun () => Id.run do
    let mut mh := Hasher.init ()
    mh := mh.update addr.hash
    mh := hashFMData mh mdata
    return Address.mk (mh.finalizeWithLength 32).val
  return .nat val blob
    { addr, lbr := 0, count0 := 0, hasFVars := false, mdata, metaAddr }

/-- The literal value is NOT hashed — only the blob address is. -/
def mkStr (val : String) (blob : Address)
    (mdata : m.F (Array MData) := noMData) : KExpr m := Id.run do
  let mut h := Hasher.init ()
  h := h.update ⟨#[Ix.TAG_ESTR]⟩
  h := h.update blob.hash
  let addr := Address.mk (h.finalizeWithLength 32).val
  let metaAddr : m.F Address := Mode.fieldWith fun () => Id.run do
    let mut mh := Hasher.init ()
    mh := mh.update addr.hash
    mh := hashFMData mh mdata
    return Address.mk (mh.finalizeWithLength 32).val
  return .str val blob
    { addr, lbr := 0, count0 := 0, hasFVars := false, mdata, metaAddr }

instance : Inhabited (KExpr m) := ⟨mkSort .mkZero⟩

/-- Blob address for a `nat` literal: Blake3 of the minimal little-endian
    encoding (`0 ↦ #[0]`). Used when whnf materializes literals. -/
def natBlob (n : Nat) : Address := Address.blake3 ⟨n.toBytesLE⟩

/-- Blob address for a `str` literal: Blake3 of the UTF-8 bytes. -/
def strBlob (s : String) : Address := Address.blake3 s.toUTF8

/-- `nat` literal with its canonical blob address. -/
def mkNatLit (n : Nat) : KExpr m := mkNat n (natBlob n)

/-- `str` literal with its canonical blob address. -/
def mkStrLit (s : String) : KExpr m := mkStr s (strBlob s)

/-! ### Spine helpers -/

/-- Collect the application spine: `f a b c ↦ (f, #[a, b, c])`. -/
def collectSpine (e : KExpr m) : KExpr m × Array (KExpr m) :=
  go e #[]
where
  go : KExpr m → Array (KExpr m) → KExpr m × Array (KExpr m)
    | .app f a _, args => go f (args.push a)
    | e, args => (e, args.reverse)

/-- Apply `f` to `args` left-to-right. -/
def mkAppN (f : KExpr m) (args : Array (KExpr m)) : KExpr m :=
  args.foldl mkApp f

/-- Spine head without collecting arguments. -/
def spineHead (e : KExpr m) : KExpr m :=
  match e with
  | .app f _ _ => spineHead f
  | e => e

/-- Number of applications in the spine. -/
def spineLen (e : KExpr m) : Nat :=
  go e 0
where
  go : KExpr m → Nat → Nat
    | .app f _ _, n => go f (n + 1)
    | _, n => n

/-! ### Display (diagnostics only) -/

/-- Meta mode shows names when available; anon mode shows positional/hash
    fallbacks. Depth-capped. Mirrors Rust `fmt_expr`. -/
partial def render (e : KExpr m) (depth : Nat := 0) : String :=
  if depth > 20 then "..."
  else match e with
    | .var idx name _ =>
      if MetaDisplay.hasMeta name then MetaDisplay.metaFmt name
      else s!"#{idx.toNat}"
    | .fvar id name _ =>
      if MetaDisplay.hasMeta name then s!"{MetaDisplay.metaFmt name}@{id}"
      else toString id
    | .sort u _ => s!"Sort {u}"
    | .const id us _ =>
      let base := toString id
      if us.isEmpty then base
      else
        let lvls := us.toList.map toString |> String.intercalate ", "
        s!"{base}.\{{lvls}}"
    | .app .. =>
      let (head, args) := collectSpine e
      let parts := (head :: args.toList).map (render · (depth + 1))
      s!"({String.intercalate " " parts})"
    | .lam name _ ty body _ =>
      let n := if MetaDisplay.hasMeta name then MetaDisplay.metaFmt name else "_"
      s!"(fun ({n} : {render ty (depth + 1)}) => {render body (depth + 1)})"
    | .all name _ ty body _ =>
      let n := if MetaDisplay.hasMeta name then MetaDisplay.metaFmt name else "_"
      s!"(({n} : {render ty (depth + 1)}) -> {render body (depth + 1)})"
    | .letE name ty val body _ _ =>
      let n := if MetaDisplay.hasMeta name then MetaDisplay.metaFmt name else "_"
      s!"(let {n} : {render ty (depth + 1)} := {render val (depth + 1)} in {render body (depth + 1)})"
    | .prj id field val _ => s!"{render val (depth + 1)}.{field.toNat}@{id}"
    | .nat val _ _ => toString val
    | .str val _ _ => reprStr val

instance : ToString (KExpr m) := ⟨(render ·)⟩

instance : Repr (KExpr m) := ⟨fun e _ => .text e.render⟩

end KExpr

end Ix.Tc

end
end
