module
public import Lean
public meta import ConLeche.Kernel.Expr

/-!
# The pin-dump interchange format (task #176)

The pinned `Nat`-operation declarations and their certificate proof
blobs used to be *computed* while `ConLeche/Kernel/NatOpPins.lean`
elaborated, by loading `ConLeche/PinGen/Certs.olean` into a full-view
environment (`importModules` at `OLeanLevel.private`).  That is not an
import edge, so Lake never ordered the two — on a cold tree
`lake build con-leche` failed with

    object file '…/ConLeche/PinGen/Certs.olean' of module
    ConLeche.PinGen.Certs does not exist

(the `extraDepTargets` in `lakefile.toml` did not reach the module when
it was built through the executable's import graph).  The user's
ruling: *commit the pin as a file* — which is what multi-toolchain
support needs anyway.

This module is the format both ends share:

* the **generator** (`PinDump.lean`, the `natop-pins-export`
  executable — it lives in the certificate library's world, where the
  proof bodies are visible) computes the pins exactly as before and
  serialises them here;
* the **loader** (`ConLeche/Kernel/NatOpPins.lean`) `include_str`s the
  committed dump and splices it at elaboration time.

Nothing here reads an olean by name, so both ends are ordinary Lake
targets with ordinary import edges.

## What is dumped

Not the `ConLeche.Expr` tree, but the **share table** the emitter builds
from it (`ConLeche.PinGen.ShareSt`): pins share subterms heavily, and
emitting them unshared would explode.  A dumped blob is therefore an
array of `PinEntry`s — each one constructor application whose
arguments are *absolute* indices of earlier entries — plus the root
reference.  `PinBlob.value` turns that back into the `let`-chain
`Lean.Expr` the splice `addDecl`s, and `buildExprValue` (the emitter
the `#gen_trust_pins` pins still go through) is literally
`(blobOf ·).value`, so there is one emitter, not two: the committed
dump reproduces the pre-#176 declaration values by construction.
Receipt, taken once at #176: the eight pins and their nineteen
certificate blobs, re-serialised out of the SPLICED constants, are
byte-identical before (`#gen_natop_pins`) and after
(`#load_natop_pins`) — 40 908 lines, `diff -q` clean.

## Encoding

JSON, via `Lean.Json` — the toolchain's own parser, already the
generator's input format (`scripts/natop_prefix.json`).  The
alternative, our ndjson export dialect, would have wanted the
frontend's `Expr` parser, and that is unreachable from here:
`ConLeche.Frontend.*` imports `ConLeche.Kernel.*`, which imports
`ConLeche.Kernel.NatOpPins` — a cycle.  A bespoke line format would have
had to re-solve string escaping (name components and `strVal`
literals) that JSON already solves.

Entries are compact tag-led arrays (`["a",123,124]` for an
application), one per line in the emitted file, so the committed dump
diffs readably.
-/

public meta section

namespace ConLeche.PinGen

open Lean

/-! ## References

The share table's entries reference each other by absolute index.  Two
subobjects are never given entries of their own — `Name.anonymous` and
`Level.zero` are emitted inline, exactly as the pre-#176 builder did —
so a reference is one of three things. -/

/-- A reference to a shared subobject. -/
inductive PinRef where
  /-- Entry `i` of the table. -/
  | idx (i : Nat)
  /-- The inline `ConLeche.Name.anonymous`. -/
  | anon
  /-- The inline `ConLeche.Level.zero`. -/
  | lzero
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- The three entry *sorts*; they fix the `let` binder's name prefix and
type, and they are what makes the emitted chain readable. -/
inductive PinSort where
  | nameS | levelS | exprS
  deriving DecidableEq, Repr, Inhabited

/-- One share-table entry: a constructor application over references. -/
inductive PinEntry where
  | nameStr (p : PinRef) (s : String)
  | nameNum (p : PinRef) (i : Nat)
  | levSucc (u : PinRef)
  | levMax (u v : PinRef)
  | levImax (u v : PinRef)
  | levParam (n : PinRef)
  | exBVar (i : Nat)
  | exFVar (idx : Nat) (ty : PinRef)
  | exSort (u : PinRef)
  | exConst (n : PinRef) (us : List PinRef)
  | exApp (f a : PinRef)
  | exLam (ty b : PinRef) (pw : Option (List ConLeche.Name))
  | exForall (ty b : PinRef) (pw : Option (List ConLeche.Name))
  | exLet (ty v b : PinRef)
  | exLitNat (v : Nat)
  | exLitStr (s : String)
  | exProj (s : PinRef) (i : Nat) (e : PinRef)
  deriving Inhabited

/-- One dumped blob: the share table and the root reference. -/
structure PinBlob where
  root : PinRef
  entries : Array PinEntry
  deriving Inhabited

/-- One operation's dumped data. -/
structure PinOpDump where
  /-- The pinned toolchain operation (for diagnostics). -/
  op : String
  /-- The spliced definition names. -/
  pinName : String
  proofsName : String
  pin : PinBlob
  proofs : Array PinBlob
  deriving Inhabited

/-- A whole dump file. -/
structure PinDumpFile where
  toolchain : String
  leanVersion : String
  ops : Array PinOpDump
  /-- The built-in prelude (task #191): the basename of the sidecar
  lean4export-format file beside this dump, the record owners it
  carries beyond the pinned basis blocks, the names it declares in
  order, and per operation the order-sensitive ground that could NOT
  be preluded (stream-certified `Nat` operations the statements are
  spelled over) — see `ConLeche/PinGen/Prelude.lean`. -/
  preludeFile : String := ""
  preludeMembers : Array String := #[]
  preludeNames : Array String := #[]
  orderResidual : Array (String × Array String) := #[]
  deriving Inhabited

/-- The format tag written into, and required of, a dump file.
`/2` since task #191: the prelude fields. -/
def dumpFormatTag : String := "con-leche-natop-pins/3"

/-- The dump file's basename for a toolchain: the `lean-toolchain`
string with everything outside `[A-Za-z0-9._-]` turned into `-`
(`leanprover/lean4:v4.33.0` ↦ `leanprover-lean4-v4.33.0.json`), so a
second toolchain's dump sits beside the first. -/
def toolchainFileName (tc : String) : String :=
  (tc.map fun c =>
    if c.isAlphanum || c == '.' || c == '-' || c == '_' then c else '-')
  ++ ".json"

/-! ## Rebuilding the `Lean.Expr`

`refExpr`, `PinEntry.sort`, `PinEntry.decl` and `assemble` together are
the pre-#176 `ShareSt` emitter, factored so that the generator and the
loader run the *same* code. -/

def nameT : Lean.Expr := .const ``ConLeche.Name []
def levelT : Lean.Expr := .const ``ConLeche.Level []
def exprT : Lean.Expr := .const ``ConLeche.Expr []

/-- Quote a `ConLeche.Name` structurally (used for the `pw` parameter
lists, which the share table does not cover — they are tiny). -/
def quoteName : ConLeche.Name → Lean.Expr
  | .anonymous => .const ``ConLeche.Name.anonymous []
  | .str p s => mkApp2 (.const ``ConLeche.Name.str []) (quoteName p) (mkStrLit s)
  | .num p n => mkApp2 (.const ``ConLeche.Name.num []) (quoteName p) (mkRawNatLit n)

def quoteNameList (ns : List ConLeche.Name) : Lean.Expr :=
  ns.foldr
    (fun n acc => mkApp3 (.const ``List.cons [.zero]) nameT (quoteName n) acc)
    (.app (.const ``List.nil [.zero]) nameT)

/-- Quote a `PropWhen` through its public interface (`never` /
`ifAllZero`) — the representation is private. -/
def quotePropWhen : Option (List ConLeche.Name) → Lean.Expr
  | none => .const ``ConLeche.PropWhen.never []
  | some ps => .app (.const ``ConLeche.PropWhen.ifAllZero []) (quoteNameList ps)

def quoteBinderMeta (pw : Option (List ConLeche.Name)) : Lean.Expr :=
  .app (.const ``ConLeche.BinderMeta.mk []) (quotePropWhen pw)

/-- A reference as an *absolute* `.bvar` (entry references) or an
inline constant.  `assemble` rewrites the `.bvar`s into de Bruijn
indices; the emitted values contain no real bound variables, so the
disguise is unambiguous. -/
def refExpr : PinRef → Lean.Expr
  | .idx i => .bvar i
  | .anon => .const ``ConLeche.Name.anonymous []
  | .lzero => .const ``ConLeche.Level.zero []

def PinEntry.sort : PinEntry → PinSort
  | .nameStr .. | .nameNum .. => .nameS
  | .levSucc .. | .levMax .. | .levImax .. | .levParam .. => .levelS
  | _ => .exprS

def PinSort.prefix' : PinSort → String
  | .nameS => "n" | .levelS => "l" | .exprS => "e"

def PinSort.type : PinSort → Lean.Expr
  | .nameS => nameT | .levelS => levelT | .exprS => exprT

def levelListE (us : List Lean.Expr) : Lean.Expr :=
  us.foldr (fun u acc => mkApp3 (.const ``List.cons [.zero]) levelT u acc)
    (.app (.const ``List.nil [.zero]) levelT)

/-- The value of one entry, with absolute references. -/
def PinEntry.value : PinEntry → Lean.Expr
  | .nameStr p s =>
    mkApp2 (.const ``ConLeche.Name.str []) (refExpr p) (mkStrLit s)
  | .nameNum p i =>
    mkApp2 (.const ``ConLeche.Name.num []) (refExpr p) (mkRawNatLit i)
  | .levSucc u => .app (.const ``ConLeche.Level.succ []) (refExpr u)
  | .levMax u v =>
    mkApp2 (.const ``ConLeche.Level.max []) (refExpr u) (refExpr v)
  | .levImax u v =>
    mkApp2 (.const ``ConLeche.Level.imax []) (refExpr u) (refExpr v)
  | .levParam n => .app (.const ``ConLeche.Level.param []) (refExpr n)
  | .exBVar i => .app (.const ``ConLeche.Expr.bvar []) (mkRawNatLit i)
  | .exFVar idx ty =>
    mkApp2 (.const ``ConLeche.Expr.fvar []) (mkRawNatLit idx) (refExpr ty)
  | .exSort u => .app (.const ``ConLeche.Expr.sort []) (refExpr u)
  | .exConst n us =>
    mkApp2 (.const ``ConLeche.Expr.const []) (refExpr n)
      (levelListE (us.map refExpr))
  | .exApp f a =>
    mkApp2 (.const ``ConLeche.Expr.app []) (refExpr f) (refExpr a)
  | .exLam ty b pw =>
    mkApp3 (.const ``ConLeche.Expr.lam []) (refExpr ty) (refExpr b)
      (quoteBinderMeta pw)
  | .exForall ty b pw =>
    mkApp3 (.const ``ConLeche.Expr.forallE []) (refExpr ty) (refExpr b)
      (quoteBinderMeta pw)
  | .exLet ty v b =>
    mkApp3 (.const ``ConLeche.Expr.letE []) (refExpr ty) (refExpr v) (refExpr b)
  | .exLitNat v =>
    .app (.const ``ConLeche.Expr.lit [])
      (.app (.const ``ConLeche.Literal.natVal []) (mkRawNatLit v))
  | .exLitStr s =>
    .app (.const ``ConLeche.Expr.lit [])
      (.app (.const ``ConLeche.Literal.strVal []) (mkStrLit s))
  | .exProj s i e =>
    mkApp3 (.const ``ConLeche.Expr.proj []) (refExpr s) (mkRawNatLit i)
      (refExpr e)

/-- The `let` binder for entry `i`. -/
def PinEntry.decl (i : Nat) (en : PinEntry) :
    Lean.Name × Lean.Expr × Lean.Expr :=
  let s := en.sort
  (.mkSimple s!"{s.prefix'}{i}", s.type, en.value)

/-- Convert absolute entry references (`.bvar j`) into de Bruijn indices
for a position under `k` enclosing `let` binders.  The emitted values
are pure application trees, so only `app` recurses. -/
partial def relat (k : Nat) : Lean.Expr → Lean.Expr
  | .bvar j => .bvar (k - 1 - j)
  | .app f a => .app (relat k f) (relat k a)
  | e => e

/-- Wrap `root` (with absolute references) in the collected `let`-chain. -/
def assemble (entries : Array (Lean.Name × Lean.Expr × Lean.Expr))
    (root : Lean.Expr) : Lean.Expr := Id.run do
  let n := entries.size
  let mut body := relat n root
  for i in [0:n] do
    let k := n - 1 - i
    let (nm, ty, v) := entries[k]!
    body := .letE nm ty (relat k v) body false
  return body

/-- The definition value of a dumped blob: the shared `let`-chain. -/
def PinBlob.value (b : PinBlob) : Lean.Expr :=
  assemble (b.entries.mapIdx fun i en => PinEntry.decl i en) (refExpr b.root)

/-! ## The sharing builder

The pins share subterms heavily (every distinct name, level and
expression node occurs many times).  Emitting them through the plain
`ToExpr` instance would lose all sharing, so each distinct subobject
becomes one `PinEntry` (`ConLeche/PinGen/Dump.lean`), bound once in the
`let`-chain `PinBlob.value` assembles; references are absolute entry
indices.  The share table is also exactly what the committed dump
carries (task #176), so the generator and the loader emit the same
declaration value by construction. -/

structure ShareSt where
  /-- Emitted entries, in dependency order. -/
  entries : Array PinEntry := #[]
  nameMap : Std.HashMap ConLeche.Name PinRef := {}
  levelMap : Std.HashMap ConLeche.Level PinRef := {}
  exprMap : Std.HashMap ConLeche.Expr PinRef := {}

abbrev ShareM := StateM ShareSt

def pushEntry (en : PinEntry) : ShareM PinRef := do
  let n := (← get).entries.size
  modify fun st => { st with entries := st.entries.push en }
  return .idx n

partial def shareName (n : ConLeche.Name) : ShareM PinRef := do
  if let some r := (← get).nameMap[n]? then return r
  let r ← match n with
    | .anonymous => pure PinRef.anon
    | .str p s => do pushEntry (.nameStr (← shareName p) s)
    | .num p i => do pushEntry (.nameNum (← shareName p) i)
  modify fun st => { st with nameMap := st.nameMap.insert n r }
  return r

partial def shareLevel (l : ConLeche.Level) : ShareM PinRef := do
  if let some r := (← get).levelMap[l]? then return r
  let r ← match l with
    | .zero => pure PinRef.lzero
    | .succ u => do pushEntry (.levSucc (← shareLevel u))
    | .max u w => do
      let uv ← shareLevel u; let wv ← shareLevel w
      pushEntry (.levMax uv wv)
    | .imax u w => do
      let uv ← shareLevel u; let wv ← shareLevel w
      pushEntry (.levImax uv wv)
    | .param n => do pushEntry (.levParam (← shareName n))
  modify fun st => { st with levelMap := st.levelMap.insert l r }
  return r

partial def shareExpr (e : ConLeche.Expr) : ShareM PinRef := do
  if let some r := (← get).exprMap[e]? then return r
  let r ← match e with
    | .bvar i => pushEntry (.exBVar i)
    | .fvar idx ty => do
      let tv ← shareExpr ty
      pushEntry (.exFVar idx tv)
    | .sort u => do pushEntry (.exSort (← shareLevel u))
    | .const n us => do
      let nv ← shareName n
      let uvs ← us.mapM shareLevel
      pushEntry (.exConst nv uvs)
    | .app f a => do
      let fv ← shareExpr f
      let av ← shareExpr a
      pushEntry (.exApp fv av)
    | .lam ty b m => do
      let tv ← shareExpr ty
      let bv ← shareExpr b
      pushEntry (.exLam tv bv m.pw.toList?)
    | .forallE ty b m => do
      let tv ← shareExpr ty
      let bv ← shareExpr b
      pushEntry (.exForall tv bv m.pw.toList?)
    | .letE ty v b => do
      let tv ← shareExpr ty
      let vv ← shareExpr v
      let bv ← shareExpr b
      pushEntry (.exLet tv vv bv)
    | .lit (.natVal v) => pushEntry (.exLitNat v)
    | .lit (.strVal s) => pushEntry (.exLitStr s)
    | .proj s i x => do
      let sv ← shareName s
      let xv ← shareExpr x
      pushEntry (.exProj sv i xv)
  modify fun st => { st with exprMap := st.exprMap.insert e r }
  return r

/-- The share table of one expression: what the dump carries and what
`PinBlob.value` turns back into the emitted `let`-chain. -/
def blobOf (e : ConLeche.Expr) : PinBlob :=
  let (root, st) := Id.run (StateT.run (s := ({} : ShareSt)) (shareExpr e))
  { root, entries := st.entries }

/-- Build the value of a single-expression definition (`… : Expr`) as a
shared `let`-chain. -/
def buildExprValue (e : ConLeche.Expr) : Lean.Expr := (blobOf e).value

/-! ## JSON codec -/

def natJ (n : Nat) : Json := Json.num (JsonNumber.fromNat n)

def refToJson : PinRef → Json
  | .idx i => natJ i
  | .anon => Json.str "anon"
  | .lzero => Json.str "lzero"

def refOfJson (j : Json) : Except String PinRef :=
  match j with
  | Json.num _ => return .idx (← j.getNat?)
  | Json.str "anon" => return .anon
  | Json.str "lzero" => return .lzero
  | _ => .error s!"bad pin reference: {j.compress}"

/-- A `ConLeche.Name` as the array of its components, outermost last. -/
def snameComps : ConLeche.Name → Array Json → Array Json
  | .anonymous, acc => acc
  | .str p s, acc => (snameComps p acc).push (Json.str s)
  | .num p i, acc => (snameComps p acc).push (natJ i)

def snameToJson (n : ConLeche.Name) : Json := Json.arr (snameComps n #[])

def snameOfJson (j : Json) : Except String ConLeche.Name := do
  let arr ← j.getArr?
  let mut n : ConLeche.Name := .anonymous
  for c in arr do
    match c with
    | Json.str s => n := .str n s
    | Json.num _ => n := .num n (← c.getNat?)
    | _ => throw s!"bad name component: {c.compress}"
  return n

def pwToJson : Option (List ConLeche.Name) → Json
  | none => Json.null
  | some ps => Json.arr (ps.map snameToJson).toArray

def pwOfJson : Json → Except String (Option (List ConLeche.Name))
  | Json.null => return none
  | j => do
    let arr ← j.getArr?
    return some (← arr.toList.mapM snameOfJson)

def PinEntry.toJson : PinEntry → Json
  | .nameStr p s => Json.arr #[Json.str "ns", refToJson p, Json.str s]
  | .nameNum p i => Json.arr #[Json.str "nn", refToJson p, natJ i]
  | .levSucc u => Json.arr #[Json.str "ls", refToJson u]
  | .levMax u v => Json.arr #[Json.str "lM", refToJson u, refToJson v]
  | .levImax u v => Json.arr #[Json.str "lI", refToJson u, refToJson v]
  | .levParam n => Json.arr #[Json.str "lp", refToJson n]
  | .exBVar i => Json.arr #[Json.str "b", natJ i]
  | .exFVar idx ty => Json.arr #[Json.str "f", natJ idx, refToJson ty]
  | .exSort u => Json.arr #[Json.str "s", refToJson u]
  | .exConst n us =>
    Json.arr #[Json.str "c", refToJson n,
      Json.arr (us.map refToJson).toArray]
  | .exApp f a => Json.arr #[Json.str "a", refToJson f, refToJson a]
  | .exLam ty b pw =>
    Json.arr #[Json.str "lam", refToJson ty, refToJson b, pwToJson pw]
  | .exForall ty b pw =>
    Json.arr #[Json.str "fa", refToJson ty, refToJson b, pwToJson pw]
  | .exLet ty v b =>
    Json.arr #[Json.str "le", refToJson ty, refToJson v, refToJson b]
  | .exLitNat v => Json.arr #[Json.str "ln", natJ v]
  | .exLitStr s => Json.arr #[Json.str "lstr", Json.str s]
  | .exProj s i e =>
    Json.arr #[Json.str "p", refToJson s, natJ i, refToJson e]

def pinEntryOfJson (j : Json) : Except String PinEntry := do
  let a ← j.getArr?
  let at? (i : Nat) : Except String Json :=
    match a[i]? with
    | some v => return v
    | none => .error s!"pin entry field {i} missing: {j.compress}"
  let tag ← (← at? 0).getStr?
  let ref (i : Nat) : Except String PinRef := do refOfJson (← at? i)
  let nat (i : Nat) : Except String Nat := do (← at? i).getNat?
  let str (i : Nat) : Except String String := do (← at? i).getStr?
  match tag with
  | "ns" => return .nameStr (← ref 1) (← str 2)
  | "nn" => return .nameNum (← ref 1) (← nat 2)
  | "ls" => return .levSucc (← ref 1)
  | "lM" => return .levMax (← ref 1) (← ref 2)
  | "lI" => return .levImax (← ref 1) (← ref 2)
  | "lp" => return .levParam (← ref 1)
  | "b" => return .exBVar (← nat 1)
  | "f" => return .exFVar (← nat 1) (← ref 2)
  | "s" => return .exSort (← ref 1)
  | "c" => do
    let us ← (← at? 2).getArr?
    return .exConst (← ref 1) (← us.toList.mapM refOfJson)
  | "a" => return .exApp (← ref 1) (← ref 2)
  | "lam" => return .exLam (← ref 1) (← ref 2) (← pwOfJson (← at? 3))
  | "fa" => return .exForall (← ref 1) (← ref 2) (← pwOfJson (← at? 3))
  | "le" => return .exLet (← ref 1) (← ref 2) (← ref 3)
  | "ln" => return .exLitNat (← nat 1)
  | "lstr" => return .exLitStr (← str 1)
  | "p" => return .exProj (← ref 1) (← nat 2) (← ref 3)
  | t => .error s!"unknown pin entry tag {t}"

def blobOfJson (j : Json) : Except String PinBlob := do
  let root ← refOfJson (← j.getObjVal? "root")
  let es ← (← j.getObjVal? "entries").getArr?
  return { root, entries := ← es.mapM pinEntryOfJson }

def opDumpOfJson (j : Json) : Except String PinOpDump := do
  return {
    op := ← (← j.getObjVal? "op").getStr?
    pinName := ← (← j.getObjVal? "pinName").getStr?
    proofsName := ← (← j.getObjVal? "proofsName").getStr?
    pin := ← blobOfJson (← j.getObjVal? "pin")
    proofs := ← (← (← j.getObjVal? "proofs").getArr?).mapM blobOfJson }

/-- Parse a dump file, checking the format tag. -/
def dumpFileOfJson (j : Json) : Except String PinDumpFile := do
  let fmt ← (← j.getObjVal? "format").getStr?
  unless fmt == dumpFormatTag do
    throw s!"pin dump format {fmt}, expected {dumpFormatTag}"
  let strs (key : String) : Except String (Array String) := do
    (← (← j.getObjVal? key).getArr?).mapM (·.getStr?)
  let residual ← (← (← j.getObjVal? "orderResidual").getArr?).mapM fun r => do
    let op ← (← r.getObjVal? "op").getStr?
    let names ← (← (← r.getObjVal? "residual").getArr?).mapM (·.getStr?)
    pure (op, names)
  return {
    toolchain := ← (← j.getObjVal? "toolchain").getStr?
    leanVersion := ← (← j.getObjVal? "leanVersion").getStr?
    ops := ← (← (← j.getObjVal? "ops").getArr?).mapM opDumpOfJson
    preludeFile := ← (← j.getObjVal? "preludeFile").getStr?
    preludeMembers := ← strs "preludeMembers"
    preludeNames := ← strs "preludeNames"
    orderResidual := residual }

def parseDumpFile (s : String) : Except String PinDumpFile := do
  dumpFileOfJson (← Json.parse s)

/-! ## Rendering

Written by hand rather than through `Json.compress` on one giant
object: the dump is a few MB and putting each share-table entry on its
own line keeps the committed file diffable. -/

def blobLines (b : PinBlob) (indent : String) : Array String := Id.run do
  let mut out := #[indent ++ "{\"root\":" ++ (refToJson b.root).compress ++
    ",\"entries\":["]
  for i in [0:b.entries.size] do
    let sep := if i + 1 == b.entries.size then "" else ","
    out := out.push ((b.entries[i]!).toJson.compress ++ sep)
  out := out.push (indent ++ "]}")
  return out

/-! ## The loader

`ConLeche/Kernel/NatOpPins.lean` `include_str`s EVERY committed dump and
invokes `#load_natop_pins` on them, in the order it lists them.
Everything the splice needs is in the dumps (the definition names
included), so the loader consults neither `opSpecs` nor any olean.

**Pin variants (task #273).**  Each dump becomes one `NatOpPinSet`
(`ConLeche/Kernel/NatOpPinSet.lean`), `natOpPinSet_v<i>` for the `i`-th
argument, its pins and proof blobs spliced as `<pinName>_v<i>` /
`<proofsName>_v<i>` (`_<j>` per blob); `natOpPinSets : List NatOpPinSet`
lists them in argument order, which is the order the install gate
tries them in (`checkDivModPinLoop`, `ConLeche/Kernel/Checker.lean`).
The loader no longer insists that a dump was generated by the running
toolchain — the point of variants is that a binary built on one
toolchain carries the pins of several; `tests/pindump.sh` is what
insists that the CURRENT toolchain's dump exists and is fresh. -/

/-- Splice one operation's pin and certificate proofs into the ambient
environment (kernel-checked, then compiled), under the variant's
suffix; returns the pin constant and the proof-list constant.

Each certificate proof becomes its **own** definition
(`…CertProofs_v<i>_<j>`), and `…CertProofs_v<i>` is the shallow list of
those constants: consumers that reduce the *list* structure (the model
bridge's `CertRuns` destructuring) then never zeta through the blobs'
`let`-chains — the self-contained blobs of task #113 are deep enough
that doing so exceeds the kernel's recursion depth, and the blobs are
meant to stay opaque to the model anyway. -/
/- MODULE SYSTEM (task #231).  Every constant spliced here must land in the
*public* scope with its body exposed, exactly as the `def` it stands for
would: `addDecl` otherwise gives the public view an opaque `axiom`
presentation (`Lean/AddDecl.lean`), and the pins' `rfl`/`decide`/`simp`
consumers — `ConLeche/Kernel/Checker.lean`, `ConLeche/Model/DivModCert.lean` —
read the *value*. -/
private def addExposed (decl : Declaration) : Elab.TermElabM Unit := do
  withExporting (isExporting := true) do
    addDecl decl (forceExpose := true)
  compileDecl decl

def spliceOpDump (suffix : String) (o : PinOpDump) :
    Elab.TermElabM (Lean.Name × Lean.Name) := do
  let pinName := o.pinName.toName.appendAfter suffix
  let pinDecl := Declaration.defnDecl {
    name := pinName, levelParams := [], type := exprT,
    value := o.pin.value, hints := .abbrev, safety := .safe }
  addExposed pinDecl
  let proofsName := o.proofsName.toName.appendAfter suffix
  let mut proofConsts : List Lean.Expr := []
  for i in [0:o.proofs.size] do
    let elemName := proofsName.appendAfter s!"_{i}"
    let elemDecl := Declaration.defnDecl {
      name := elemName, levelParams := [], type := exprT,
      value := o.proofs[i]!.value, hints := .abbrev, safety := .safe }
    addExposed elemDecl
    proofConsts := proofConsts ++ [.const elemName []]
  let proofsDecl := Declaration.defnDecl {
    name := proofsName, levelParams := [],
    type := Lean.Expr.app (.const ``List [.zero]) exprT,
    value := proofConsts.foldr
      (fun p acc => mkApp3 (.const ``List.cons [.zero]) exprT p acc)
      (.app (.const ``List.nil [.zero]) exprT),
    hints := .abbrev, safety := .safe }
  addExposed proofsDecl
  return (pinName, proofsName)

/-- The operations in the field order of `ConLeche.NatOpPinSet`. -/
def pinSetOpOrder : List String :=
  ["Nat.div", "Nat.mod", "Nat.gcd", "Nat.land", "Nat.lor", "Nat.xor",
   "Nat.shiftLeft", "Nat.shiftRight"]

/-- Splice one dump as the variant `natOpPinSet_v<i>`; returns its
name. -/
def spliceDump (i : Nat) (d : PinDumpFile) : Elab.TermElabM Lean.Name := do
  let suffix := s!"_v{i}"
  let mut pins : Array Lean.Expr := #[]
  let mut proofs : Array Lean.Expr := #[]
  for op in pinSetOpOrder do
    let some o := d.ops.find? (·.op == op) |
      throwError "pin dump {d.toolchain} carries no pin for {op}"
    let (pn, prn) ← spliceOpDump suffix o
    pins := pins.push (.const pn [])
    proofs := proofs.push (.const prn [])
  let setName := (`ConLeche.natOpPinSet).appendAfter suffix
  let setDecl := Declaration.defnDecl {
    name := setName, levelParams := [],
    -- single-backtick names: the structure lives in
    -- `ConLeche/Kernel/NatOpPinSet.lean`, which the SPLICING module
    -- imports (`ConLeche/Kernel/NatOpPins.lean`), not this format module
    type := .const `ConLeche.NatOpPinSet [],
    value := mkAppN (.const `ConLeche.NatOpPinSet.mk [])
      (#[mkStrLit d.toolchain] ++ pins ++ proofs),
    hints := .abbrev, safety := .safe }
  addExposed setDecl
  return setName

/-- Parse the committed dumps and splice every one of them as a
variant, then `natOpPinSets` in argument order. -/
def loadPinsFromTexts (texts : Array String) : Elab.Command.CommandElabM Unit := do
  if texts.isEmpty then
    throwError "#load_natop_pins: no dump given"
  let mut dumps : Array PinDumpFile := #[]
  for text in texts do
    match parseDumpFile text with
    | .ok d => dumps := dumps.push d
    | .error e => throwError "bad pin dump: {e}"
  Elab.Command.liftTermElabM do
    let mut sets : List Lean.Expr := []
    for i in [0:dumps.size] do
      let n ← spliceDump i dumps[i]!
      sets := sets ++ [.const n []]
    let setT : Lean.Expr := .const `ConLeche.NatOpPinSet []
    let listDecl := Declaration.defnDecl {
      name := `ConLeche.natOpPinSets, levelParams := [],
      type := Lean.Expr.app (.const ``List [.zero]) setT,
      value := sets.foldr
        (fun p acc => mkApp3 (.const ``List.cons [.zero]) setT p acc)
        (.app (.const ``List.nil [.zero]) setT),
      hints := .abbrev, safety := .safe }
    addExposed listDecl

/-- `#load_natop_pins <string literal>, …` — splice the committed pin
dumps as variants, in this order.  The arguments are meant to be
`include_str`s, which elaborate to string literals, so the texts are
read off the syntax tree with no evaluation. -/
elab "#load_natop_pins" ss:term,+ : command => do
  let texts ← Elab.Command.liftTermElabM do
    ss.getElems.mapM fun s => do
      let e ← instantiateMVars (← Elab.Term.elabTerm s (some (.const ``String [])))
      match e with
      | .lit (.strVal t) => pure t
      | _ =>
        throwError "#load_natop_pins expects string literals \
          (`include_str`s of the committed dumps)"
  loadPinsFromTexts texts

def dumpLines (d : PinDumpFile) : Array String := Id.run do
  let mut out := #["{"]
  out := out.push ("\"format\":" ++ (Json.str dumpFormatTag).compress ++ ",")
  -- JSON has no comments, so the file's header is a pair of ignored
  -- fields (the reader only looks at the ones it knows).
  out := out.push ("\"_README\":" ++ (Json.str
    ("GENERATED FILE — do not edit.  The pinned Nat-operation defining \
     expressions and their certificate proof blobs, as share tables \
     (see ConLeche/PinGen/Dump.lean for the encoding).  Spliced into \
     ConLeche/Kernel/NatOpPins.lean by #load_natop_pins.  The built-in \
     prelude the pins' order-sensitive ground needs (task #191) is the \
     sidecar file named by preludeFile, embedded by \
     ConLeche/Frontend/Prelude.lean; orderResidual lists, per operation, \
     the order-sensitive ground that stays the stream's (see \
     ConLeche/PinGen/Prelude.lean).")).compress ++ ",")
  out := out.push ("\"_regenerate\":" ++ (Json.str
    ("lake exe natop-pins-export   — then commit the result; \
     tests/pindump.sh (run from tests/arena.sh) diffs this file \
     against a fresh regeneration and fails if it is stale.")).compress
    ++ ",")
  out := out.push ("\"toolchain\":" ++ (Json.str d.toolchain).compress ++ ",")
  out := out.push
    ("\"leanVersion\":" ++ (Json.str d.leanVersion).compress ++ ",")
  -- the built-in prelude's index (task #191; the records themselves are
  -- the sidecar file)
  out := out.push ("\"preludeFile\":" ++ (Json.str d.preludeFile).compress ++ ",")
  let strArr (a : Array String) : String := (Json.arr (a.map Json.str)).compress
  out := out.push ("\"preludeMembers\":" ++ strArr d.preludeMembers ++ ",")
  out := out.push ("\"preludeNames\":" ++ strArr d.preludeNames ++ ",")
  out := out.push "\"orderResidual\":["
  for i in [0:d.orderResidual.size] do
    let (op, names) := d.orderResidual[i]!
    let sep := if i + 1 == d.orderResidual.size then "" else ","
    out := out.push ("{\"op\":" ++ (Json.str op).compress ++ ",\"residual\":" ++
      strArr names ++ "}" ++ sep)
  out := out.push "],"
  out := out.push "\"ops\":["
  for oi in [0:d.ops.size] do
    let o := d.ops[oi]!
    out := out.push "{"
    out := out.push ("\"op\":" ++ (Json.str o.op).compress ++ ",")
    out := out.push ("\"pinName\":" ++ (Json.str o.pinName).compress ++ ",")
    out := out.push
      ("\"proofsName\":" ++ (Json.str o.proofsName).compress ++ ",")
    out := out.push "\"pin\":"
    out := out ++ blobLines o.pin ""
    out := out.push ",\"proofs\":["
    for pi in [0:o.proofs.size] do
      out := out ++ blobLines o.proofs[pi]! ""
      if pi + 1 != o.proofs.size then out := out.push ","
    out := out.push "]"
    out := out.push (if oi + 1 == d.ops.size then "}" else "},")
  out := out.push "]"
  out := out.push "}"
  return out

end ConLeche.PinGen
