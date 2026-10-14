import IxC.Kernel.Frontend.InModel
import IxC.Kernel.Frontend.Prepare
import IxC.Address.Core
import IxC.Ixon.Types
import IxC.Kernel.Ref

/-! # Ixon records as kernel declarations

This reader turns decoded Ixon records into the `Array Ix.Kernel.Declaration`
that the verified fold `Ix.Kernel.Cached.checkDecls` consumes. It is the
Ixon counterpart of upstream con-leche's NDJSON decoder
(`Frontend/ExportC.lean`, not carried here): the same record shapes, the same
projection rewrite (`Ix.Kernel.Frontend.ProjRec`) and the same in-process
modeller for nested and mutual blocks (`Ix.Kernel.Frontend.InModel`), both
derived from upstream's. Its output then goes through `Frontend.preparePrelude` and the
fold.

## Soundness: nothing here is trusted

`Ix.Kernel.model_exists` holds for every `ds : Array Declaration` that
`checkDecls .verified pins ds` accepts, at every pin list. So no property of
this reader is needed for the consistency of what the fold accepts: a wrong
name, a wrong grouping, a wrong rule order or a wrong level parameter can
only make the fold reject or decline, or make it accept a different
environment than the records describe, which is still a modelled one. What
the reader does decide is coverage, and the faithfulness of the accepted
environment to the Ixon records; the latter is the fidelity theorem
(`Ix.Kernel.Ixon.ReaderSpec`, `Ix.Kernel.Admission.Theorems`).

## Keys

The kernel key is `Ix.Kernel.Key`. A constant reference `ConstRef Address`
is encoded injectively under the reserved root `ix`:

* `.member b i` ↦ `ix.<hex b>.i` (a `.num` component);
* `.ctor b i c` ↦ `ix.<hex b>.i.c`;
* a level parameter is positional: parameter `i` is `.num .anonymous i`.

Hex spelling of the address bytes is injective, and the two shapes differ in
their number of `.num` components, so distinct references get distinct
names (`keyName_injective`). None of these names has a shape the checker
reserves (`_model`, `T.proj.i`, `T.projTable.0`) or that the frontend derives
(`T.rec`, `T.rec_k`).

Three kinds of names are not of this form:

* **Recursors** are named after what they eliminate, because the direct
  install, the structure route and the in-process modeller find a block's
  recursor by name: the recursor whose motive is the block's member `m`
  (in motive order) is `T_m.rec`, and the one whose motive is the `j`-th
  auxiliary (nested) motive is `T_0.rec_j` (1-based), exactly Lean's own
  convention. The motive is read off the recursor's type (the head of its
  result), the member off that motive's major carrier.
* **Pinned names** (`Pins.names`): the checker's own pinned names and no
  others: the basis (`Eq`, `Nat`, `PUnit`, `Empty`, `False`, the `Quot`
  package), the prelude's `And` and `Bool`, the literal support (`String`,
  `String.ofList`, `List`, `Char`, `Char.ofNat`), the structural and
  pin-certified Nat operations, the standard axioms with `Iff` and
  `Nonempty`, the compiler-trust family with `True`, and `sorryAx`. The table
  maps a `ConstRef Address` to its pinned name; it is generated from the
  compiled Init records (`Benchmarks/Kernel/PinGen.lean`, which
  checks every entry through the verified fold) and committed
  (`IxC/Kernel/Ixon/PinData.lean`); the reader never reads Ixon metadata.
  `pinMap` refuses a table that is not a partial injection or that uses the
  reserved root or a derived shape. The checker itself compares every pinned
  name's declaration with its pinned shape, binder contracts included (basis
  blocks up to `canon`, with a reserved-name reject otherwise; literal support and Nat operations by
  exact type shapes and certified recurrences; the standard and trust axioms
  by `matchesPin`), so a table entry on a constant of another shape is
  rejected or declined, never accepted under the pinned name.
* **Level parameters** are positional: a record's universe variable `i` is
  the level parameter `i`, and a constant with `n` of them has the level
  parameters `[0, …, n-1]`. The one exception is a recursor with one level
  more than its block (a large eliminator), which the checker recognises by
  the shape `elim :: lps` of its level parameters with `elim` not among the
  block's `lps`: its variable `0` is the fresh parameter `n` (the block has
  `n`) and its variable `k + 1` is the block's `k`. References instantiate
  by position.

## Regrouping

* An inductive `muts` block becomes one `indDecl`: its members in motive
  order, their constructors in `cidx` order, then every recursor that
  eliminates the block (from separate `recr` or recursor-`muts` records, or
  from the block itself), in motive order. Rule constructors are the major
  carrier's constructors in `cidx` order (a nested auxiliary recursor's
  rules are its container's constructors). The block's records emit at the
  block's position; recursor records emit nothing.
* A definition `muts` block becomes one declaration per member (a
  `defnDecl`, `thmDecl` or `opaqueDecl` each, checked like a singleton),
  ordered so that every member follows the members it names by `recur`.
  The safety policy is applied to every member before the order is sought,
  with a singleton's reasons: a block with a member that is not safe
  declines with that member's safety. Those are the only blocks with a cycle
  in practice: Lean's kernel takes a mutual definition block only when its
  members are `partial` or `unsafe` (`add_mutual`), and that is how the
  compiler's `_unsafe_rec` companions of structural and well-founded
  definitions are stored (`addAndCompilePartialRec`: one `partial` block per
  mutual group, the members calling each other). Safe mutual recursion
  reaches Lean's kernel as definitions added one at a time (through
  `brecOn` or a `_mutual` fixpoint), so a safe block orders; one that does
  not is declined as a mutually recursive definition block (the checker,
  like Lean's kernel, has no safe mutual definitions).
* `defn`/`axio`/`quot` singletons become one declaration each; projection
  records emit nothing (they are only checked to resolve).
* Every binder carries `pw := .never` (the checker's annotation pass computes
  the datum) and keeps its Ixon contracts in `BinderMeta`: a `lam`'s
  binder contract as `contract` (its `result` is `shared`), an `all`'s input
  contract as `contract` and its result contract as `result`. A `letE`'s
  contract (`Ixon.LetContract`) is erased: the checker's `letE` has no field
  for it yet (it is to arrive with a `LetMeta` field).
* Definitions get the kernel's height rule `regular (1 + max height)` unless
  the host supplies a hint (the environment check supplies the compiler's own).
-/

namespace Ix.Kernel.Reader

open Ix.Kernel (ConstRef)

/-! The checker's syntax (`Ix.Kernel`), abbreviated so that the reader's
signatures tell it apart from Ixon's and Lean's. -/

abbrev CName := Ix.Kernel.Key
abbrev CExpr := Ix.Kernel.Expr
abbrev CLevel := Ix.Kernel.Level
abbrev CDecl := Ix.Kernel.Declaration
abbrev CInfo := Ix.Kernel.ConstantInfo
abbrev CVal := Ix.Kernel.ConstantVal

/-! ## Keys -/

/-- The reserved root of address-encoded names. -/
def ixRoot : CName := .str .anonymous "ix"

def addressHex (a : Address) : String := hexOfBytes a.hash

/-- `ix.<hex b>`. -/
def blockName (b : Address) : CName := .str ixRoot (addressHex b)

/-- The address encoding of a constant reference. -/
def keyName : ConstRef Address → CName
  | .member b i => .num (blockName b) i
  | .ctor b i c => .num (.num (blockName b) i) c

/-! ### `keyName` is injective

Distinct references get distinct names: the hexadecimal spelling of the
address bytes is injective (each byte is two digits that `byteOfHex` reads
back, checked for all 256 bytes by kernel evaluation), and a member's name
and a constructor's name differ in their number of trailing `.num`
components. Nothing in the checker's soundness needs this (`model_exists`
holds for every declaration array); it is what makes the encoding a key. -/

/-- `ByteArray.toList`'s loop, in closed form. -/
theorem byteArray_toList_loop (bs : ByteArray) (i : Nat) (r : List UInt8) :
    ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
  fun_induction ByteArray.toList.loop bs i r with
  | case1 i r h ih =>
    rw [ih]
    have h' : i < bs.data.size := h
    have hl : i < bs.data.toList.length := by rw [Array.length_toList]; exact h'
    rw [List.drop_eq_getElem_cons hl]
    simp only [ByteArray.get!, getElem!_pos bs.data i h', List.reverse_cons, List.append_assoc,
      List.singleton_append, Array.getElem_toList]
  | case2 i r h =>
    have : bs.data.toList.length ≤ i := by rw [Array.length_toList]; exact Nat.le_of_not_lt h
    rw [List.drop_eq_nil_of_le this, List.append_nil]

theorem byteArray_toList (bs : ByteArray) : bs.toList = bs.data.toList := by
  rw [ByteArray.toList, byteArray_toList_loop]; rfl

/-- The two hexadecimal digits `hexOfByte` writes for a byte. -/
def hexDigits (b : UInt8) : List Char :=
  [(hexOfNat (UInt8.toNat (b >>> 4))).get!, (hexOfNat (UInt8.toNat (b &&& 0xF))).get!]

theorem hexOfByte_toList (b : UInt8) : (hexOfByte b).toList = hexDigits b := by
  simp [hexOfByte, hexDigits]

/-- Every byte's digits read back as the byte (all 256, by kernel evaluation). -/
theorem byteOfHex_hexDigits_lt : ∀ n, n < 256 →
    byteOfHex (hexDigits (UInt8.ofNat n))[0]! (hexDigits (UInt8.ofNat n))[1]! =
      some (UInt8.ofNat n) := by
  decide +kernel

theorem byteOfHex_hexDigits (b : UInt8) :
    byteOfHex (hexDigits b)[0]! (hexDigits b)[1]! = some b := by
  have := byteOfHex_hexDigits_lt b.toNat b.toNat_lt
  rwa [UInt8.ofNat_toNat] at this

theorem hexOfBytes_toList_foldl (acc : String) (l : List UInt8) :
    ((l.map hexOfByte).foldl (· ++ ·) acc).toList = acc.toList ++ l.flatMap hexDigits := by
  induction l generalizing acc with
  | nil => simp
  | cons b l ih => simp [ih, String.toList_append, hexOfByte_toList, List.append_assoc]

theorem hexOfBytes_toList (bs : ByteArray) :
    (hexOfBytes bs).toList = bs.data.toList.flatMap hexDigits := by
  rw [hexOfBytes, hexOfBytes_toList_foldl, byteArray_toList]; simp

theorem hexDigits_injective {a b : UInt8} (h : hexDigits a = hexDigits b) : a = b := by
  have ha := byteOfHex_hexDigits a
  rw [h, byteOfHex_hexDigits b] at ha
  exact (Option.some.inj ha).symm

theorem hexDigits_length (b : UInt8) : (hexDigits b).length = 2 := rfl

theorem flatMap_hexDigits_injective :
    ∀ {l m : List UInt8}, l.flatMap hexDigits = m.flatMap hexDigits → l = m
  | [], [], _ => rfl
  | [], b :: m, h => by simp [List.flatMap_cons, hexDigits] at h
  | a :: l, [], h => by simp [List.flatMap_cons, hexDigits] at h
  | a :: l, b :: m, h => by
    rw [List.flatMap_cons, List.flatMap_cons] at h
    obtain ⟨hd, tl⟩ := List.append_inj h (by rw [hexDigits_length, hexDigits_length])
    rw [hexDigits_injective hd, flatMap_hexDigits_injective tl]

/-- The hexadecimal spelling of a byte array is injective. -/
theorem hexOfBytes_injective {a b : ByteArray} (h : hexOfBytes a = hexOfBytes b) : a = b := by
  have hl := congrArg String.toList h
  rw [hexOfBytes_toList, hexOfBytes_toList] at hl
  have hd := flatMap_hexDigits_injective hl
  cases a; cases b
  simp only [Array.toList_inj] at hd
  rw [hd]

theorem addressHex_injective {a b : Address} (h : addressHex a = addressHex b) : a = b := by
  cases a; cases b
  simp only [addressHex] at h
  rw [hexOfBytes_injective h]

/-- **`keyName` is injective**: distinct constant references get distinct
names. -/
theorem keyName_injective {r s : ConstRef Address} (h : keyName r = keyName s) : r = s := by
  cases r with
  | member b i =>
    cases s with
    | member b' i' =>
      simp only [keyName, blockName, Ix.Kernel.Name.num.injEq, Ix.Kernel.Name.str.injEq,
        true_and] at h
      obtain ⟨hb, hi⟩ := h
      rw [addressHex_injective hb, hi]
    | ctor b' i' c' => simp [keyName, blockName] at h
  | ctor b i c =>
    cases s with
    | member b' i' => simp [keyName, blockName] at h
    | ctor b' i' c' =>
      simp only [keyName, blockName, Ix.Kernel.Name.num.injEq, Ix.Kernel.Name.str.injEq,
        true_and] at h
      obtain ⟨⟨hb, hi⟩, hc⟩ := h
      rw [addressHex_injective hb, hi, hc]

/-! ## Errors -/

/-- A record the reader cannot turn into declarations: `malformed` is a
reject (the bytes describe no declaration), `declined` an unsupported
feature (an unsafe declaration, a block without its recursor, a block the
modeller declines). -/
inductive ReadError where
  | malformed (reason : String)
  | declined (reason : String)
  deriving Repr, Inhabited, BEq

instance : ToString ReadError where
  toString
    | .malformed r => s!"malformed: {r}"
    | .declined r => s!"declined: {r}"

abbrev ReadM := Except ReadError

def malformed (reason : String) : ReadM α := throw (.malformed reason)
def declined (reason : String) : ReadM α := throw (.declined reason)

/-! ## The pin table -/

/-- One pinned name: the reference it is assigned to. -/
structure Pin where
  ref : ConstRef Address
  name : CName

/-- The first component of a name. -/
def rootComponent : CName → Option String
  | .anonymous => none
  | .str .anonymous s => some s
  | .num .anonymous _ => none
  | .str p _ | .num p _ => rootComponent p

/-- Names the frontend derives from others (a recursor's spelling, a model
companion, a projection function or table); a pin may not take one. -/
def derivedShape (n : CName) : Bool :=
  n.isRecSpelling || n.isModelSuffix || n.isProjFnShape

/-- The table as a lookup, after checking that it is a partial injection
from references to names outside the reserved `ix` root and the derived
shapes. A table that fails the check is not used at all. -/
def pinMap (pins : Array Pin) : Except String (Std.HashMap (ConstRef Address) CName) := do
  let mut byRef : Std.HashMap (ConstRef Address) CName := {}
  let mut names : Std.HashSet CName := {}
  for p in pins do
    if rootComponent p.name == some "ix" then throw s!"pin {p.name} is under the reserved root"
    if derivedShape p.name then throw s!"pin {p.name} has a derived shape"
    if names.contains p.name then throw s!"pin {p.name} is assigned twice"
    if byRef.contains p.ref then throw s!"pin {p.name}: its reference is pinned twice"
    names := names.insert p.name
    byRef := byRef.insert p.ref p.name
  return byRef

/-- The pinned names a reading uses. -/
structure Pins where
  names : Std.HashMap (ConstRef Address) CName := {}

/-! ## Stores and references -/

abbrev Store := Address → Option Ixon.Constant

def emptyTables (c : Ixon.Constant) : Bool :=
  c.sharing.isEmpty && c.refs.isEmpty && c.univs.isEmpty

/-- The reference a record address denotes: a singleton is member 0 of
itself, a projection the member (or constructor) of its owning block, a
`muts` block nothing. -/
def resolveSource (store : Store) (address : Address) (c : Ixon.Constant) :
    Option (ConstRef Address) :=
  match c.info with
  | .defn _ | .recr _ | .axio _ | .quot _ => some (.member address 0)
  | .muts _ => none
  | .dPrj p => do
    guard (emptyTables c)
    let .muts ms := (← store p.block).info | none
    let .defn _ ← ms[p.idx.toNat]? | none
    pure (.member p.block p.idx.toNat)
  | .iPrj p => do
    guard (emptyTables c)
    let .muts ms := (← store p.block).info | none
    let .indc _ ← ms[p.idx.toNat]? | none
    pure (.member p.block p.idx.toNat)
  | .rPrj p => do
    guard (emptyTables c)
    let .muts ms := (← store p.block).info | none
    let .recr _ ← ms[p.idx.toNat]? | none
    pure (.member p.block p.idx.toNat)
  | .cPrj p => do
    guard (emptyTables c)
    let .muts ms := (← store p.block).info | none
    let .indc ind ← ms[p.idx.toNat]? | none
    let ctor ← ind.ctors[p.cidx.toNat]?
    guard (ctor.cidx == p.cidx)
    pure (.ctor p.block p.idx.toNat p.cidx.toNat)

def resolve (store : Store) (address : Address) : Option (ConstRef Address) := do
  resolveSource store address (← store address)

/-- The inductive at a member reference, if the store has one there. -/
def inductiveAt (store : Store) : ConstRef Address → Option Ixon.Inductive
  | .member b i => do
    let .muts ms := (← store b).info | none
    let .indc ind ← ms[i]? | none
    pure ind
  | .ctor .. => none

/-- The recursor members of a record, with their positions. -/
def recursorMembers (c : Ixon.Constant) : Array (Nat × Ixon.Recursor) :=
  match c.info with
  | .recr r => #[(0, r)]
  | .muts ms => (ms.zipIdx.filterMap fun | (.recr r, j) => some (j, r) | _ => none)
  | _ => #[]

/-! ## Spines of Ixon expressions

The recursor analysis reads a few syntactic positions of a recursor's type
before any conversion: through `share` indirections, a bounded number of
binders, an application head. -/

/-- Follow top-level `share` indirections (at most the table's size). -/
def unshare (c : Ixon.Constant) (e : Ixon.Expr) : Ixon.Expr :=
  go (c.sharing.size + 1) e
where
  go : Nat → Ixon.Expr → Ixon.Expr
    | 0, e => e
    | n + 1, .share i =>
      match c.sharing[i.toNat]? with
      | some e => go n e
      | none => .share i
    | _, e => e

/-- Strip `n` leading `∀` binders: their domains and the body. -/
def stripAll (c : Ixon.Constant) : Nat → Ixon.Expr → Option (List Ixon.Expr × Ixon.Expr)
  | 0, e => some ([], e)
  | n + 1, e =>
    match unshare c e with
    | .all _ _ t b => do
      let (ts, r) ← stripAll c n b
      pure (t :: ts, r)
    | _ => none

/-- Strip every leading `∀` binder (bounded by `fuel`). -/
def stripAllFull (c : Ixon.Constant) : Nat → Ixon.Expr → List Ixon.Expr × Ixon.Expr
  | 0, e => ([], e)
  | n + 1, e =>
    match unshare c e with
    | .all _ _ t b =>
      let (ts, r) := stripAllFull c n b
      (t :: ts, r)
    | e => ([], e)

/-- The head of an application spine (bounded by `fuel`). -/
def appHead (c : Ixon.Constant) : Nat → Ixon.Expr → Ixon.Expr
  | 0, e => e
  | n + 1, e =>
    match unshare c e with
    | .app f _ => appHead c n f
    | e => e

/-- The spine bound of the syntactic walks: a binder or argument count of a
real declaration is far below it. -/
def spineFuel : Nat := 1 <<< 20

/-- The constant at the head of `e`, as a reference: through `refs`, or a
`recur` into the record's own block. -/
def headRef (store : Store) (owner : Address) (c : Ixon.Constant) (e : Ixon.Expr) :
    Option (ConstRef Address) :=
  match appHead c spineFuel e with
  | .ref i _ => do resolve store (← c.refs[i.toNat]?)
  | .recur i _ =>
    match c.info with
    | .muts ms => if i.toNat < ms.size then some (.member owner i.toNat) else none
    | _ => if i == 0 then some (.member owner 0) else none
  | _ => none

/-! ## The recursor index -/

/-- What the reader knows about a recursor before reading its block. -/
structure RecEntry where
  /-- the inductive block it eliminates -/
  block : Address
  /-- the motive it eliminates (its result's head), in motive order -/
  motive : Nat
  /-- the reference of its major premise's carrier: a member of `block` for
  a real motive, the container for a nested auxiliary one -/
  major : ConstRef Address
  /-- whether its level parameters carry an elimination level in front of
  the block's (its parameter `0` is then named after the block's) -/
  large : Bool
  /-- its name -/
  name : CName

/-- What the reader knows about an inductive block before reading it. -/
structure BlockShape where
  /-- the block's member positions, in motive order -/
  order : Array Nat
  /-- its recursors, in motive order -/
  recs : Array (ConstRef Address)
  deriving Inhabited

structure RecIndex where
  recs : Std.HashMap (ConstRef Address) RecEntry := {}
  blocks : Std.HashMap Address BlockShape := {}
  deriving Inhabited

/-- One recursor's analysis: its motive (from its type's result head), the
carrier of every motive, and its major premise's carrier. -/
def analyseRecursor (store : Store) (owner : Address) (c : Ixon.Constant)
    (r : Ixon.Recursor) : Option (Nat × Array (ConstRef Address) × ConstRef Address) := do
  let nP := r.params.toNat
  let nM := r.motives.toNat
  let nm := r.minors.toNat
  let nI := r.indices.toNat
  let depth := nP + nM + nm + nI + 1
  let (doms, body) ← stripAll c depth r.typ
  let .var k := appHead c spineFuel body | none
  let pos := depth - 1 - k.toNat
  guard (k.toNat < depth && nP ≤ pos && pos < nP + nM)
  let carriers ← (doms.drop nP |>.take nM).toArray.mapM fun dom => do
    let (bs, _) := stripAllFull c spineFuel dom
    headRef store owner c (← bs.getLast?)
  let major ← headRef store owner c (← doms.getLast?)
  pure (pos - nP, carriers, major)

/-- Index every recursor of `records` by the block it eliminates, and name
it (`T_m.rec`, or `T_0.rec_j` at the `j`-th auxiliary motive). A recursor
whose type does not have the recursor shape is not indexed; its record and
its block then decline. -/
def buildIndex (store : Store) (pins : Std.HashMap (ConstRef Address) CName)
    (records : Array (Address × Ixon.Constant)) : RecIndex := Id.run do
  let memberName (r : ConstRef Address) : CName := pins.getD r (keyName r)
  let mut idx : RecIndex := {}
  let mut found : Std.HashMap Address (Array (Nat × ConstRef Address)) := {}
  for (owner, c) in records do
    for (j, r) in recursorMembers c do
      let ref : ConstRef Address := .member owner j
      if idx.recs.contains ref then continue
      let some ((m, carriers, major) : Nat × Array (ConstRef Address) × ConstRef Address) :=
        analyseRecursor store owner c r | continue
      let some (ConstRef.member b i0) := carriers[0]? | continue
      let some blockRecord := store b | continue
      let .muts ms := blockRecord.info | continue
      let indc := (ms.zipIdx.filterMap fun | (.indc ind, i) => some (i, ind) | _ => none)
      let some (_, first) := indc[0]? | continue
      let size := indc.size
      let order := (carriers.extract 0 size).filterMap fun
        | .member b' i => if b' == b then some i else none
        | .ctor .. => none
      unless order.size == size && order[0]? == some i0 &&
          order.all (fun i => indc.any (·.1 == i)) &&
          (order.toList.eraseDups.length == size) do continue
      let base : ConstRef Address := .member b (order[0]!)
      let name :=
        if m < size then (memberName (.member b (order[m]!))).str "rec"
        else (memberName base).str s!"rec_{m - size + 1}"
      -- one recursor per motive of a block: the first record's (the supplied
      -- records come before the prelude's fallback); a second one is not
      -- grouped with the block and declines as a recursor without its block
      if (found.getD b #[]).any (·.1 == m) then continue
      let large := r.lvls.toNat == first.lvls.toNat + 1
      idx := { idx with recs := idx.recs.insert ref ⟨b, m, major, large, name⟩ }
      found := found.insert b ((found.getD b #[]).push (m, ref))
      unless idx.blocks.contains b do
        idx := { idx with blocks := idx.blocks.insert b ⟨order, #[]⟩ }
  for (b, rs) in found.toList do
    let sorted := rs.qsort (fun x y => x.1 < y.1)
    let shape := idx.blocks.getD b default
    idx := { idx with blocks := idx.blocks.insert b { shape with recs := sorted.map (·.2) } }
  return idx

/-! ## The reader's context -/

/-- Address encodings computed ahead of reading: every entry is `keyName` of
its key. The reader names a reference at every occurrence (3.7 million
`ref`/`prj` nodes in Init+Std); calling `keyName` there would spell the
address in hexadecimal each time, which dominates the reading time, and give
every occurrence its own name object. Looked up here, each reference is spelled once and every
occurrence reads the same object, as a lean4export stream's name table
gives upstream con-leche's parser one name per index. -/
structure KeyNames where
  map : Std.HashMap (ConstRef Address) CName := {}
  sound : ∀ r n, map[r]? = some n → n = keyName r := by simp

/-- `keyName r`, from the table where it has an entry. -/
def KeyNames.get (k : KeyNames) (r : ConstRef Address) : CName :=
  match k.map[r]? with
  | some n => n
  | none => keyName r

theorem KeyNames.get_eq (k : KeyNames) (r : ConstRef Address) : k.get r = keyName r := by
  unfold KeyNames.get
  cases h : k.map[r]? with
  | none => rfl
  | some n => exact k.sound r n h

/-- The table with `r`'s encoding added. -/
def KeyNames.insert (k : KeyNames) (r : ConstRef Address) : KeyNames :=
  ⟨k.map.insert r (keyName r), fun r' n h => by
    rw [Std.HashMap.getElem?_insert] at h
    split at h
    · next hr =>
      cases h
      rw [beq_iff_eq.mp hr]
    · exact k.sound r' n h⟩

/-- The address encodings of the unpinned references `records` denote (each
record's `resolveSource`), for `Ctx.keys`. -/
def keyNamesOf (store : Store) (pins : Std.HashMap (ConstRef Address) CName)
    (records : Array (Address × Ixon.Constant)) : KeyNames :=
  records.foldl (init := {}) fun k (a, c) =>
    match resolveSource store a c with
    | some r => if pins.contains r || k.map.contains r then k else k.insert r
    | none => k

/-- Everything a record is read against: the stores, the pins, the
recursor index, the host's (optional, untrusted) reducibility hints, and the
address encodings computed ahead (`keyNamesOf`; an empty table only costs
time). -/
structure Ctx where
  store : Store
  blob : Address → Option ByteArray
  pins : Pins
  index : RecIndex
  hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint := fun _ => none
  keys : KeyNames := {}

def Ctx.nameOf (cx : Ctx) (r : ConstRef Address) : CName :=
  match cx.index.recs[r]? with
  | some e => e.name
  | none => match cx.pins.names[r]? with
    | some n => n
    | none => cx.keys.get r

/-- A recursor's level parameters: its block's `blockLps`, behind the
fresh elimination parameter `blockLps.length` for a large eliminator (the
shape `elim :: lps`, `elim` not among `lps`, by which the checker
recognises one). -/
def recLps (large : Bool) (blockLps : List LevelParam) : List LevelParam :=
  if large then blockLps.length :: blockLps else blockLps

/-! ## Expressions -/

/-- Little-endian natural-number payload (Ix's `Ingress.natural`). -/
def natural (bytes : ByteArray) : Nat :=
  bytes.data.foldr (fun byte rest => byte.toNat + 256 * rest) 0

def convUniv (param : Nat → LevelParam) : Ixon.Univ → CLevel
  | .zero => .zero
  | .succ u => .succ (convUniv param u)
  | .max a b => .max (convUniv param a) (convUniv param b)
  | .imax a b => .imax (convUniv param a) (convUniv param b)
  | .var i => .param (param i.toNat)

/-- A recursor's universe variable `i` is its `i`-th level parameter
(`recLps`); every other member's is the level parameter `i`. -/
def recParam (lps : List LevelParam) (i : Nat) : LevelParam := lps.getD i i

/-- The context of one member's expressions. -/
structure ECx where
  cx : Ctx
  src : Ixon.Constant
  /-- the member's universe table, its variables read as level parameters -/
  univs : Array CLevel
  /-- `recur i` -/
  self : Nat → Option CName

def ECx.level (e : ECx) (i : UInt64) : ReadM CLevel :=
  match e.univs[i.toNat]? with
  | some l => pure l
  | none => malformed "universe table index is out of bounds"

def ECx.levels (e : ECx) (us : Array UInt64) : ReadM (List CLevel) :=
  us.toList.mapM e.level

def ECx.refAt (e : ECx) (i : UInt64) : ReadM (ConstRef Address) := do
  let some a := e.src.refs[i.toNat]? | malformed "reference index is out of bounds"
  let some r := resolve e.cx.store a | malformed s!"reference {a} is missing or has invalid ownership"
  pure r

def ECx.blobAt (e : ECx) (i : UInt64) : ReadM ByteArray := do
  let some a := e.src.refs[i.toNat]? | malformed "literal reference index is out of bounds"
  let some b := e.cx.blob a | malformed s!"literal blob {a} is missing"
  pure b

/-- One expression, against the converted sharing entries before it. -/
def convExpr (e : ECx) (tbl : Array (ReadM CExpr)) : Ixon.Expr → ReadM CExpr
  | .var i => pure (Ix.Kernel.Expr.mkBvar i.toNat)
  | .sort i => do pure (.sort (← e.level i))
  | .ref i us => do
    let r ← e.refAt i
    pure (.const (e.cx.nameOf r) (← e.levels us))
  | .recur i us => do
    let some n := e.self i.toNat | malformed "recursive reference is outside its block"
    pure (.const n (← e.levels us))
  | .prj i field v => do
    let r ← e.refAt i
    pure (.proj (e.cx.nameOf r) field.toNat (← convExpr e tbl v))
  | .str i => do
    let bytes ← e.blobAt i
    let some s := String.fromUTF8? bytes | malformed "string literal is not valid UTF-8"
    pure (.lit (.strVal s))
  | .nat i => do pure (.lit (.natVal (natural (← e.blobAt i))))
  | .app f a => do pure (.app (← convExpr e tbl f) (← convExpr e tbl a))
  | .lam c t b => do
    pure (.lam (← convExpr e tbl t) (← convExpr e tbl b) { pw := .never, contract := c })
  | .all c r t b => do
    pure (.forallE (← convExpr e tbl t) (← convExpr e tbl b)
      { pw := .never, contract := c, result := r })
  | .letE _ t v b => do
    pure (.letE (← convExpr e tbl t) (← convExpr e tbl v) (← convExpr e tbl b))
  | .share i =>
    match tbl[i.toNat]? with
    | some r => r
    | none => malformed "sharing reference is not to an earlier entry"

/-- A member's expression reader: the sharing table is converted once, each
entry against the entries before it (an entry that fails fails only the
expressions that use it). -/
structure MemberReader where
  ecx : ECx
  tbl : Array (ReadM CExpr)

def MemberReader.mk' (cx : Ctx) (src : Ixon.Constant) (param : Nat → LevelParam)
    (self : Nat → Option CName) : MemberReader := Id.run do
  let ecx : ECx := ⟨cx, src, src.univs.map (convUniv param), self⟩
  let mut tbl : Array (ReadM CExpr) := Array.mkEmpty src.sharing.size
  for entry in src.sharing do
    tbl := tbl.push (convExpr ecx tbl entry)
  return ⟨ecx, tbl⟩

def MemberReader.read (m : MemberReader) (e : Ixon.Expr) : ReadM CExpr :=
  convExpr m.ecx m.tbl e

/-! ## The reader's state

What the in-process modeller and the projection rewrite read about the
declarations before the current one (upstream con-leche's `StateD`, minus
the NDJSON tables). -/

structure State where
  constTypes : Std.HashMap CName (List LevelParam × CExpr) := {}
  heights : Std.HashMap CName Nat := {}
  indBlocks : Std.HashMap CName Ix.Kernel.Frontend.InModel.BlockRec := {}
  projOwners : Std.HashMap CName Ix.Kernel.Frontend.ProjRecOwner := {}
  projLevels : Std.HashMap CName CLevel := {}
  /-- projection functions rewritten to recursor form, and the records the
  modeller generated (counts, for the drivers' receipts) -/
  projRewrites : Nat := 0
  generated : Nat := 0
  deriving Inhabited

/-- Record a declaration's constants (`ExportC.noteDecl`). -/
def State.note (st : State) (d : CDecl) : State :=
  let cvs : List (CName × List LevelParam × CExpr × Option Nat) := match d with
    | .axiomDecl cv => [(cv.name, cv.levelParams, cv.type, none)]
    | .defnDecl cv _ h =>
      [(cv.name, cv.levelParams, cv.type, some (Ix.Kernel.Frontend.InModel.hintHeight h))]
    | .thmDecl cv _ => [(cv.name, cv.levelParams, cv.type, none)]
    | .opaqueDecl cv _ => [(cv.name, cv.levelParams, cv.type, none)]
    | .basisDecl k => k.decls.map fun ci =>
      (ci.toConstantVal.name, ci.toConstantVal.levelParams, ci.toConstantVal.type, none)
    | .quotDecl _ cv => [(cv.name, cv.levelParams, cv.type, none)]
    | .indDecl block _ => block.map fun ci =>
      (ci.toConstantVal.name, ci.toConstantVal.levelParams, ci.toConstantVal.type, none)
  cvs.foldl (fun st (n, lps, ty, h) =>
    { st with
      constTypes := st.constTypes.insert n (lps, ty)
      heights := match h with | some h => st.heights.insert n h | none => st.heights }) st

/-- A generated record: noted, and an artifact `T._model.proj_i.iota`
registers its field sort for the projection rewrite
(`ExportC.pushGenD`/`noteProjIota`). -/
def State.noteGenerated (st : State) (d : CDecl) : State :=
  let st := match d with
    | .thmDecl cv _ =>
      if Ix.Kernel.Frontend.isProjIotaName cv.name then
        match Ix.Kernel.Frontend.projIotaLevel cv.type with
        | some l => { st with projLevels := st.projLevels.insert cv.name l }
        | none => st
      else st
    | _ => st
  { st.note d with generated := st.generated + 1 }

/-- The projection-function rewrite at a definition or theorem record
(`ExportC.projRewriteD`). -/
def projRewrite (st : State) (cv : CVal) (value : CExpr) : Option CExpr := do
  let .proj T i (.bvar 0) := Ix.Kernel.Frontend.lamBody value | none
  let o ← st.projOwners[T]?
  guard (cv.levelParams == o.lps)
  let l ← st.projLevels[Ix.Kernel.Frontend.projIotaName T i]?
  Ix.Kernel.Frontend.projRecValue o l cv.type value i

/-! ## Records -/

/-- The result of reading one record: its declarations in fold order (the
modeller's generated records first), and what the reader's state learns
from it. The state is updated only by `State.commit`, after the record:
reading never modifies it, so a driver threads it uniquely. -/
structure Read where
  decls : Array CDecl := #[]
  /-- how many of `decls` (at the front) the modeller generated -/
  generated : Nat := 0
  /-- structure-like owners the projection rewrite serves -/
  owners : List Ix.Kernel.Frontend.ProjRecOwner := []
  /-- the block, by member name, for the modeller's nested rung -/
  blocks : List (CName × Ix.Kernel.Frontend.InModel.BlockRec) := []
  /-- projection functions rewritten -/
  projRewrites : Nat := 0

/-- The state after a record (in `ExportC.installIndD`'s order: owners,
block, generated records, the record's own declarations). -/
def State.commit (st : State) (r : Read) : State := Id.run do
  let mut st := st
  for o in r.owners do st := { st with projOwners := st.projOwners.insert o.T o }
  for (n, b) in r.blocks do st := { st with indBlocks := st.indBlocks.insert n b }
  for (d, i) in r.decls.zipIdx do
    st := if i < r.generated then st.noteGenerated d else st.note d
  return { st with projRewrites := st.projRewrites + r.projRewrites }

/-- The syntactic Π-telescope length (`ExportC.indPiTeleLen`). -/
def piTeleLen : CExpr → Nat
  | .forallE _ b _ => piTeleLen b + 1
  | _ => 0

def safetyWord : Ix.DefinitionSafety → String
  | .unsaf => "unsafe"
  | .part => "partial"
  | .safe => "safe"

/-- The safety policy of a definition (`ExportC.processLineCoreD`) of a kind
and a safety: a definition that is not safe, and an unsafe opaque, decline;
the reason. -/
def safetyDeclineOf (kind : Ix.DefKind) (safety : Ix.DefinitionSafety) : Option String :=
  match kind with
  | .defn => if safety == .safe then none else some s!"definition with safety '{safetyWord safety}'"
  | .opaq => if safety == .unsaf then some "unsafe opaque declaration" else none
  | .thm => none

/-- The safety policy of a definition record. The same for a singleton and
for every member of a block. -/
def safetyDecline (d : Ixon.Definition) : Option String :=
  safetyDeclineOf d.kind d.safety

/-- A definition's declaration from its header `cv` and its value's reading,
and whether the projection rewrite applied: the record-agnostic half of
`readDefinition`, which every front end lowers through. `hint` is the host's
hint; without one a definition gets the height rule's, over `heights`. -/
def lowerDefinition (hint : Option Ix.Kernel.ReducibilityHint) (st : State)
    (heights : CName → Nat) (cv : CVal) (value : CExpr) (kind : Ix.DefKind)
    (safety : Ix.DefinitionSafety) : ReadM (CDecl × Bool) := do
  let rewritten := projRewrite st cv value
  let value' := rewritten.getD value
  if let some why := safetyDeclineOf kind safety then declined why
  let decl := match kind with
    | .defn =>
      let hint := hint.getD (Ix.Kernel.Frontend.InModel.hintFor heights value')
      Ix.Kernel.Declaration.defnDecl cv value' hint
    | .thm => Ix.Kernel.Declaration.thmDecl cv value'
    | .opaq => Ix.Kernel.Declaration.opaqueDecl cv value
  pure (decl, rewritten.isSome && kind != .opaq)

/-- A definition member: its declaration (`ExportC.processLineCoreD`), and
whether the projection rewrite applied. `heights` are the definitional
heights so far (the block's earlier members included). -/
def readDefinition (cx : Ctx) (st : State) (heights : CName → Nat) (ref : ConstRef Address)
    (lps : List LevelParam) (mr : MemberReader) (d : Ixon.Definition) : ReadM (CDecl × Bool) := do
  let name := cx.nameOf ref
  let cv : CVal := ⟨name, lps, ← mr.read d.typ⟩
  let value ← mr.read d.value
  lowerDefinition (cx.hint ref) st heights cv value d.kind d.safety

/-- The members of a definition block that member `i`'s expressions name by
`recur`. -/
def recurDeps (c : Ixon.Constant) (d : Ixon.Definition) : Std.HashSet Nat := Id.run do
  -- per sharing entry, the recur targets it reaches
  let mut shared : Array (Std.HashSet Nat) := #[]
  for entry in c.sharing do
    shared := shared.push (go shared {} entry)
  return go shared (go shared {} d.typ) d.value
where
  go (shared : Array (Std.HashSet Nat)) (acc : Std.HashSet Nat) : Ixon.Expr → Std.HashSet Nat
    | .recur i _ => acc.insert i.toNat
    | .prj _ _ v => go shared acc v
    | .app f a => go shared (go shared acc f) a
    | .lam _ t b => go shared (go shared acc t) b
    | .all _ _ t b => go shared (go shared acc t) b
    | .letE _ t v b => go shared (go shared (go shared acc t) v) b
    | .share i => (shared[i.toNat]?.getD {}).fold (·.insert ·) acc
    | _ => acc

/-- A definition block's members in an order where each follows the members
it references; `none` on a cycle. A member may name itself: the checker then
checks its value in the environment before the member is added
(`checkDefnVal`), where the reference does not resolve. -/
def defOrder (deps : Array (Std.HashSet Nat)) : Option (Array Nat) := Id.run do
  let n := deps.size
  let mut done : Array Bool := Array.replicate n false
  let mut out : Array Nat := #[]
  for _ in [0:n] do
    let mut progressed := false
    for i in [0:n] do
      if !done[i]! && (deps[i]!).toList.all (fun j => j == i || j ≥ n || done[j]!) then
        done := done.set! i true
        out := out.push i
        progressed := true
    if out.size == n then return some out
    unless progressed do return none
  return if out.size == n then some out else none

/-- A recursor's declared counts. -/
structure RecCounts where
  params : Nat
  motives : Nat
  minors : Nat
  indices : Nat
  k : Bool

/-- An inductive block as a front end reads it, before lowering: the block's
declared parameter count; its types in motive order, each with its declared
parameter and index counts; its constructors in the block's order, each with
its parameter and field counts, and their names per type; its recursors in
motive order, each with its declared counts and its rules. -/
structure BlockRead where
  numParams : Nat
  types : Array (CVal × Nat × Nat)
  ctors : Array (CVal × Nat × Nat)
  ctorNames : Array (List CName)
  recs : Array (CVal × RecCounts × List Ix.Kernel.RecRule)

/-- An inductive block's declarations: one `indDecl`, preceded by the
modeller's records for a nested or mutual block (`ExportC.validateIndD` and
`installIndD`). The record-agnostic half of `readInductive`, which every
front end lowers through. -/
def lowerInductive (st : State) (rb : BlockRead) : ReadM Read := do
  let ⟨nPd, types, ctors, ctorNames, recs⟩ := rb
  -- the stream's own consistency checks (`validateIndD`)
  let nTypes := types.size
  let nCtors := ctors.size
  let numNested := match recs[0]? with
    | some (_, r, _) => r.motives - nTypes
    | none => 0
  let nested := numNested != 0
  let kExpected? : Option Bool :=
    match types.toList, ctorNames.toList, ctors.toList with
    | [(ty, _, _)], [[_]], [(_, _, nF)] =>
      match ty.type.piResult with
      | .sort s => some (nF == 0 && Ix.Kernel.Level.isEquiv s .zero == some true)
      | _ => none
    | _, _, _ => some false
  unless nested do
    for (cv, r, _) in recs do
      unless r.params == nPd do
        malformed s!"recursor {cv.name} declares {r.params} parameters; the block declares {nPd}"
      unless r.motives == nTypes do
        malformed s!"recursor {cv.name} declares {r.motives} motives; the block has {nTypes} types"
      unless r.minors == nCtors do
        malformed s!"recursor {cv.name} declares {r.minors} minor premises; the block has {nCtors} constructors"
      if let some kE := kExpected? then
        unless r.k == kE do
          malformed s!"recursor {cv.name} declares k := {r.k}; the generated recursor is{if kE then "" else " not"} K-like"
      if let .str T "rec" := cv.name then
        for (ty, _, _) in types do
          if ty.name == T then
            if let some n := ty.type.piSortTeleLen? then
              unless nPd + r.indices == n do
                malformed s!"recursor {cv.name} declares {r.indices} indices; {T} has {n - nPd}"
  -- the block's constants
  let typeInfos : List CInfo := types.toList.map fun (cv, _, _) => .indInfo cv {}
  let ctorInfos : List CInfo := ctors.toList.map fun (cv, nP, nF) => .ctorInfo cv nP nF
  let recInfos : List CInfo := recs.toList.map fun (cv, r, rules) =>
    .recInfo cv (r.params + r.motives + r.minors + r.indices) (r.params + r.motives + r.minors) rules
  let block := typeInfos ++ ctorInfos ++ recInfos
  -- shape flags the export carries and Ixon does not: recursive and
  -- reflexive occurrences, read off the constructors' field domains
  let memberNames := types.toList.map (·.1.name)
  let fieldDoms := ctors.toList.flatMap fun (cv, _, _) =>
    (Ix.Kernel.Frontend.stripPisAll cv.type).1.map (·.1)
  let isRec := fieldDoms.any fun d => memberNames.any (Ix.Kernel.Frontend.occursConstFast · d)
  let isReflexive := fieldDoms.any fun d =>
    let (bs, body) := Ix.Kernel.Frontend.stripPisAll d
    !bs.isEmpty && memberNames.any (Ix.Kernel.Frontend.headIs · body)
  -- the projection rewrite's owners (`registerProjOwners`)
  let ownerTypes := types.toList.zip ctorNames.toList |>.map fun ((cv, nP, nIdx), cs) =>
    (cv.name, cv.levelParams, cv.type, nP, nIdx, cs, isRec)
  let ownerCtors := ctors.toList.map fun (cv, _, nF) => (cv.name, nF, cv.type)
  let ownerRecs := recs.toList.map fun (cv, r, _) =>
    (cv.name, cv.levelParams, cv.type, r.motives, r.minors)
  let owners := Ix.Kernel.Frontend.projRecOwners block ownerTypes ownerCtors ownerRecs
  -- the in-process modeller
  let b : Ix.Kernel.Frontend.InModel.BlockRec :=
    ⟨types.toList.zip ctorNames.toList |>.map fun ((cv, nP, nIdx), cs) =>
        { cv, nP, nIdx, ctors := cs, isRec, isReflexive, numNested },
     ctors.toList.map fun (cv, nP, nF) => { cv, nP, nF },
     recs.toList.map fun (cv, r, rules) =>
       { cv, nP := r.params, nM := r.motives, nm := r.minors, nI := r.indices, rules }⟩
  let blocks := b.types.map (·.cv.name, b)
  let decl := Ix.Kernel.Declaration.indDecl block nPd
  if Ix.Kernel.Frontend.InModel.wants b then
    -- the block's own members are visible to the nested rung, as in the
    -- decoder (`installIndD` registers the block before generating)
    let ctx : Ix.Kernel.Frontend.InModel.Ctx :=
      ⟨fun n => st.constTypes[n]?, fun n => st.heights.getD n 0,
       fun n => if memberNames.contains n then some b else st.indBlocks[n]?⟩
    match Ix.Kernel.Frontend.InModel.generate ctx b with
    | .error why => declined s!"in-process model of {(types[0]?.map (·.1.name)).getD .anonymous}: {why}"
    | .ok gen => pure { decls := gen.toArray.push decl, generated := gen.length, owners, blocks }
  else
    pure { decls := #[decl], owners, blocks }

/-- An inductive block with its recursors, read from its records and lowered
by `lowerInductive`. -/
def readInductive (cx : Ctx) (st : State) (owner : Address) (c : Ixon.Constant)
    (ms : Array Ixon.MutConst) : ReadM Read := do
  let some shape := cx.index.blocks[owner]?
    | declined "inductive block without a recursor in the input"
  let self : Nat → Option CName := fun i =>
    if i < ms.size then some (cx.nameOf (.member owner i)) else none
  let indcs : Array (Nat × Ixon.Inductive) :=
    shape.order.filterMap fun i => match (ms[i]? : Option Ixon.MutConst) with
      | some (.indc ind) => some (i, ind)
      | _ => none
  unless indcs.size == shape.order.size do malformed "recursor motive is not a member of its block"
  let some (_, first) := indcs[0]? | malformed "empty inductive block"
  if indcs.any (·.2.isUnsafe) then declined "unsafe inductive declaration"
  let nPd := first.params.toNat
  unless indcs.all (·.2.params.toNat == nPd) do
    declined "inductive block whose type records disagree on numParams"
  let blockLps := List.range first.lvls.toNat
  let mrInd := MemberReader.mk' cx c id self
  -- types, in motive order
  let mut types : Array (CVal × Nat × Nat) := #[]
  for (i, ind) in indcs do
    types := types.push (⟨cx.nameOf (.member owner i), List.range ind.lvls.toNat,
      ← mrInd.read ind.typ⟩,
      ind.params.toNat, ind.indices.toNat)
  -- constructors, in the block's own order
  let mut ctors : Array (CVal × Nat × Nat) := #[]
  let mut ctorNames : Array (List CName) := #[]
  for (i, ind) in indcs do
    let mut names : List CName := []
    for (ctor, j) in ind.ctors.zipIdx do
      unless ctor.cidx.toNat == j do malformed "constructor index differs from its position"
      if ctor.isUnsafe then declined "unsafe inductive declaration"
      let cv : CVal :=
        ⟨cx.nameOf (.ctor owner i j), List.range ctor.lvls.toNat, ← mrInd.read ctor.typ⟩
      unless nPd + ctor.fields.toNat == piTeleLen cv.type do
        malformed s!"constructor {cv.name} declares {ctor.fields} fields at {nPd} parameters; \
          its type has {piTeleLen cv.type} binders"
      ctors := ctors.push (cv, ctor.params.toNat, ctor.fields.toNat)
      names := names ++ [cv.name]
    ctorNames := ctorNames.push names
  -- recursors, in motive order
  let mut recs : Array (CVal × RecCounts × List Ix.Kernel.RecRule) := #[]
  for ref in shape.recs do
    let some entry := cx.index.recs[ref]? | malformed "unindexed recursor"
    let .member rOwner j := ref | malformed "recursor reference is a constructor"
    let some rc := cx.store rOwner | malformed "recursor record is missing"
    let some (_, r) := (recursorMembers rc).find? (·.1 == j) | malformed "recursor member is missing"
    if r.isUnsafe then declined "unsafe inductive declaration"
    let rself : Nat → Option CName := fun i => match rc.info with
      | .muts rms => if i < rms.size then some (cx.nameOf (.member rOwner i)) else none
      | _ => if i == 0 then some entry.name else none
    let lps := recLps entry.large blockLps
    let mr := MemberReader.mk' cx rc (recParam lps) rself
    let cv : CVal := ⟨entry.name, lps, ← mr.read r.typ⟩
    let some major := inductiveAt cx.store entry.major
      | declined s!"recursor {entry.name}: its major premise is not an inductive"
    unless major.ctors.size == r.rules.size do
      malformed s!"recursor {entry.name} has {r.rules.size} rules for {major.ctors.size} constructors"
    let .member mb mi := entry.major | malformed "recursor major is a constructor"
    let mut rules : List Ix.Kernel.RecRule := []
    for (rule, k) in r.rules.zipIdx do
      rules := rules ++ [Ix.Kernel.RecRule.mk (cx.nameOf (.ctor mb mi k)) rule.fields.toNat 0 .inert
        (← mr.read rule.rhs) false false false]
    recs := recs.push (cv, ⟨r.params.toNat, r.motives.toNat, r.minors.toNat, r.indices.toNat, r.k⟩,
      rules)
  lowerInductive st ⟨nPd, types, ctors, ctorNames, recs⟩

/-- One primary or projection record: its declarations. The state is read,
not changed; `State.commit` applies what the record taught. -/
def readRecord (cx : Ctx) (st : State) (owner : Address) (c : Ixon.Constant) : ReadM Read := do
  match c.info with
  | .dPrj _ | .iPrj _ | .rPrj _ | .cPrj _ =>
    if (resolveSource cx.store owner c).isNone then
      malformed "projection record has invalid tables, owner, kind, or position"
    pure {}
  | .defn d =>
    let self : Nat → Option CName := fun i => if i == 0 then some (cx.nameOf (.member owner 0)) else none
    let (decl, rw) ← readDefinition cx st (st.heights.getD · 0) (.member owner 0)
      (List.range d.lvls.toNat) (.mk' cx c id self) d
    pure { decls := #[decl], projRewrites := if rw then 1 else 0 }
  | .recr _ =>
    unless cx.index.recs.contains (.member owner 0) do
      declined "recursor whose inductive block is not in the input"
    pure {}
  | .axio a =>
    if a.isUnsafe then declined "unsafe axiom"
    let mr := MemberReader.mk' cx c id (fun _ => none)
    let cv : CVal := ⟨cx.nameOf (.member owner 0), List.range a.lvls.toNat, ← mr.read a.typ⟩
    pure { decls := #[Ix.Kernel.Declaration.axiomDecl cv] }
  | .quot q =>
    let mr := MemberReader.mk' cx c id (fun _ => none)
    let cv : CVal := ⟨cx.nameOf (.member owner 0), List.range q.lvls.toNat, ← mr.read q.typ⟩
    let kind : Ix.Kernel.QuotKind := match q.kind with
      | .type => .type | .ctor => .ctor | .lift => .lift | .ind => .ind
    pure { decls := #[Ix.Kernel.Declaration.quotDecl kind cv] }
  | .muts ms =>
    if ms.any (fun | .indc _ => true | _ => false) then
      if ms.any (fun | .defn _ => true | _ => false) then
        malformed "a block mixes inductives and definitions"
      readInductive cx st owner c ms
    else if ms.all (fun | .recr _ => true | _ => false) then
      for j in [0:ms.size] do
        unless cx.index.recs.contains (.member owner j) do
          declined "recursor whose inductive block is not in the input"
      pure {}
    else if ms.all (fun | .defn _ => true | _ => false) then
      let defs : Array Ixon.Definition := ms.filterMap fun | .defn d => some d | _ => none
      -- the safety policy first, member by member: a `partial` block (the
      -- `_unsafe_rec` companions) declines as its members would one by one
      if let some why := defs.findSome? safetyDecline then declined why
      let some order := defOrder (defs.map (recurDeps c))
        | declined "mutually recursive definition block"
      let self : Nat → Option CName := fun i =>
        if i < ms.size then some (cx.nameOf (.member owner i)) else none
      let mr := MemberReader.mk' cx c id self
      let mut blockHeights : Std.HashMap CName Nat := {}
      let mut out : Array CDecl := #[]
      let mut rewrites := 0
      for i in order do
        let heights : CName → Nat := fun n => blockHeights.getD n (st.heights.getD n 0)
        let (decl, rw) ← readDefinition cx st heights (.member owner i)
          (List.range defs[i]!.lvls.toNat) mr defs[i]!
        if let .defnDecl cv _ h := decl then
          blockHeights := blockHeights.insert cv.name (Ix.Kernel.Frontend.InModel.hintHeight h)
        if rw then rewrites := rewrites + 1
        out := out.push decl
      pure { decls := out, projRewrites := rewrites }
    else malformed "a block mixes recursors and definitions"

/-! ## The constants a literal references

`Ix.Kernel.Expr.constsResolve` counts a `Nat` literal as a reference to the
`Nat` basis trio (`Nat`, `Nat.zero`, `Nat.succ`) and a `String` literal as a
reference to that trio and the seven string-support constants (`String`,
`String.ofList`, `List`, `List.nil`, `List.cons`, `Char`, `Char.ofNat`), and
the checker declines a string literal while those are not installed. An
Ixon record that only uses a literal names none of them (its `nat`/`str`
nodes point at blobs), so a dependency order over table references alone can
put a literal user before the support: `String.instInhabited`, whose value
is `⟨""⟩`, comes before `String.ofList` and `Char.ofNat` in such an order of
Init, and without these edges blocks 760 records. `literalEdges` adds those implicit references as
dependency edges, as the environment check adds a pinned `Nat` operation's certificate
ground (`natOpDeps`). The `Nat` trio is the prelude's `Nat` block, which
every order here puts first, so only the string edges change an order; the
`Nat` edges keep the relation complete for the blocking report. -/

/-- Whether a record's expressions contain a `Nat` literal and a `String`
literal: `(nat, str)`. Every expression is walked once: the top-level
expressions without following `share`, and each sharing entry. -/
def literalKinds (c : Ixon.Constant) : Bool × Bool :=
  let exprs : Array Ixon.Expr := c.sharing ++ match c.info with
    | .defn d => #[d.typ, d.value]
    | .recr r => #[r.typ] ++ r.rules.map (·.rhs)
    | .axio a => #[a.typ]
    | .quot q => #[q.typ]
    | .muts ms => ms.flatMap fun
      | .defn d => #[d.typ, d.value]
      | .indc i => #[i.typ] ++ i.ctors.map (·.typ)
      | .recr r => #[r.typ] ++ r.rules.map (·.rhs)
    | _ => #[]
  exprs.foldl go (false, false)
where
  go (acc : Bool × Bool) : Ixon.Expr → Bool × Bool
    | .nat _ => (true, acc.2)
    | .str _ => (acc.1, true)
    | .prj _ _ v => go acc v
    | .app f a => go (go acc f) a
    | .lam _ t b => go (go acc t) b
    | .all _ _ t b => go (go acc t) b
    | .letE _ t v b => go (go (go acc t) v) b
    | _ => acc

/-- The constants a `Nat` literal references (`Expr.constsResolve`). -/
def natLitSupportNames : List CName :=
  [Ix.Kernel.natName, Ix.Kernel.natZeroName, Ix.Kernel.natSuccName]

/-- The constants a `String` literal references (`Expr.constsResolve`). -/
def strLitSupportNames : List CName :=
  natLitSupportNames ++
    [Ix.Kernel.stringName, Ix.Kernel.stringOfListName, Ix.Kernel.listName, Ix.Kernel.listNilName,
     Ix.Kernel.listConsName, Ix.Kernel.charName, Ix.Kernel.charOfNatName]

/-- Dependency edges from every record that contains a literal to the records
(block addresses) of the constants the literal references, under a pin table.
A support constant the table does not pin contributes no edge (the checker
then declines the literal, as it would anyway). -/
def literalEdges (pins : Std.HashMap (ConstRef Address) CName)
    (records : Array (Address × Ixon.Constant)) : Std.HashMap Address (Array Address) := Id.run do
  let byName : Std.HashMap CName Address := pins.fold (fun m r n => m.insert n r.block) {}
  let targets (names : List CName) : Array Address :=
    names.foldl (fun acc n => match byName[n]? with
      | some a => if acc.contains a then acc else acc.push a
      | none => acc) #[]
  let natTargets := targets natLitSupportNames
  let strTargets := targets strLitSupportNames
  let mut out : Std.HashMap Address (Array Address) := {}
  for (a, c) in records do
    let (nat, str) := literalKinds c
    let ts := (if str then strTargets else if nat then natTargets else #[]).filter (· != a)
    unless ts.isEmpty do out := out.insert a ts
  return out

/-! ## Streams -/

/-- The first record under each address. -/
def recordMap (records : Array (Address × Ixon.Constant)) : Std.HashMap Address Ixon.Constant :=
  records.foldl (fun m (a, c) => if m.contains a then m else m.insert a c) {}

/-- The records' store: the supplied records first, then a fallback (the
prelude's records).

The compiler compiles `storeOf` at its full arity, three arguments, so a
partial application `storeOf records` rebuilds the map at every lookup. A
driver that looks records up more than a few times binds `recordMap records`
first and closes over it, as `contextOf` does. -/
def storeOf (records : Array (Address × Ixon.Constant)) (fallback : Store := fun _ => none) :
    Store :=
  let m := recordMap records
  fun a => m[a]? <|> fallback a

/-- Read records in order into declarations (the fold's input before
`preparePrelude`). Duplicate record addresses are rejected, as by Ix's own
reader. The error carries the record's position. -/
def readRecords (cx : Ctx) (st : State) (records : Array (Address × Ixon.Constant)) :
    Except (ReadError × Nat) (State × Array CDecl) := do
  let mut seen : Std.HashSet Address := {}
  let mut st := st
  let mut out : Array CDecl := #[]
  for ((a, c), i) in records.zipIdx do
    if seen.contains a then throw (.malformed s!"duplicate record address {a}", i)
    seen := seen.insert a
    match readRecord cx st a c with
    | .ok r =>
      st := st.commit r
      out := out ++ r.decls
    | .error e => throw (e, i)
  return (st, out)

end Ix.Kernel.Reader
