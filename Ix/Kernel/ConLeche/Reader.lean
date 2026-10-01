/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import ConLeche.Frontend.InModel
import ConLeche.Frontend.Prepare
import Ix.Address.Core
import Ix.Ixon.Types
import Ix.Kernel.Ref

/-! # Ixon records as con-leche declarations (plan v4, L4)

This reader turns decoded Ixon records into the `Array ConLeche.Declaration`
that con-leche's verified fold `ConLeche.Cached.checkDecls` consumes. It is
the Ixon counterpart of con-leche's NDJSON decoder (`Frontend/ExportC.lean`,
not ported): the same record shapes, the same projection rewrite
(`Frontend/ProjRec.lean`) and the same in-process modeller for nested and
mutual blocks (`Frontend/InModel.lean`), both imported verbatim. Its output
then goes through `Frontend.preparePrelude` (imported verbatim) and the fold.

## Soundness: nothing here is trusted

`ConLeche.model_exists` holds for every `ds : Array Declaration` that
`checkDecls .verified pins ds` accepts, at every pin list. So no property of
this reader is needed for the consistency of what the fold accepts: a wrong
name, a wrong grouping, a wrong rule order or a wrong level parameter can
only make the fold reject or decline, or make it accept a different
environment than the records describe, which is still a modelled one. What
the reader does decide is coverage, and the faithfulness of the accepted
environment to the Ixon records; the latter is L5's fidelity theorem.

## Keys (decision D1 (b))

The kernel key stays `ConLeche.Name`. A constant reference `ConstRef Address`
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
* **Pinned names** (`Pins.names`): con-leche's own pinned names and no
  others: the basis (`Eq`, `Nat`, `PUnit`, `Empty`, `False`, the `Quot`
  package), the prelude's `And` and `Bool`, the literal support (`String`,
  `String.ofList`, `List`, `Char`, `Char.ofNat`), the structural and
  pin-certified Nat operations, the standard axioms with `Iff` and
  `Nonempty`, the compiler-trust family with `True`, and `sorryAx`. The table
  maps a `ConstRef Address` to its pinned name; it is generated from the
  compiled Init records (`Benchmarks/Kernel/ConLechePinGen.lean`, which
  checks every entry through con-leche) and committed
  (`Ix/Kernel/ConLeche/PinData.lean`); the reader never reads Ixon metadata.
  `pinMap` refuses a table that is not a partial injection or that uses the
  reserved root or a derived shape. Con-leche itself compares every pinned
  name's declaration with its pinned shape (basis blocks up to `canon`, with
  a reserved-name reject otherwise; literal support and Nat operations by
  exact type shapes and certified recurrences; the standard and trust axioms
  by `matchesPin`), so a table entry on a constant of another shape is
  rejected or declined, never accepted under the pinned name.
* **Level parameters** are positional except in two places where con-leche
  reads them by name. The standard-axiom pins (`matchesPin`) compare level
  parameter names, so the pinned constants and their recursors carry Lean's
  own level names (`Pins.levels`, from the same generator; a block's
  constructors take its members' names). And con-leche recognises a large
  eliminator by the spelling `elim :: lps` of its level parameters, so a
  recursor with one level more than its block names its parameter `0` with
  a fresh name and its parameter `k + 1` as the block's `k`. Both rename a
  constant's own parameters only; references instantiate by position.

## Regrouping

* An inductive `muts` block becomes one `indDecl`: its members in motive
  order, their constructors in `cidx` order, then every recursor that
  eliminates the block (from separate `recr` or recursor-`muts` records, or
  from the block itself), in motive order. Rule constructors are the major
  carrier's constructors in `cidx` order (a nested auxiliary recursor's
  rules are its container's constructors). The block's records emit at the
  block's position; recursor records emit nothing.
* A definition `muts` block becomes one declaration per member, in an order
  where every member follows the members it references (a genuine cycle is
  declined: the kernel has no mutual definitions).
* `defn`/`axio`/`quot` singletons become one declaration each; projection
  records emit nothing (they are only checked to resolve).
* Every binder carries `pw := .never` (con-leche's annotation pass computes
  the datum); Ixon v3 binder contracts are erased, as by Ix's own reader.
* Definitions get the kernel's height rule `regular (1 + max height)` unless
  the host supplies a hint (the census supplies the compiler's own).
-/

namespace Ix.Kernel.ConLecheReader

open Ix.Kernel (ConstRef)

abbrev CName := ConLeche.Name
abbrev CExpr := ConLeche.Expr
abbrev CLevel := ConLeche.Level
abbrev CDecl := ConLeche.Declaration
abbrev CInfo := ConLeche.ConstantInfo
abbrev CVal := ConLeche.ConstantVal

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

/-- Level parameter `i`. -/
def levelName (i : Nat) : CName := .num .anonymous i

def levelNames (n : Nat) : List CName := (List.range n).map levelName

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
names (decision D1 (b)). -/
theorem keyName_injective {r s : ConstRef Address} (h : keyName r = keyName s) : r = s := by
  cases r with
  | member b i =>
    cases s with
    | member b' i' =>
      simp only [keyName, blockName, ConLeche.Name.num.injEq, ConLeche.Name.str.injEq,
        true_and] at h
      obtain ⟨hb, hi⟩ := h
      rw [addressHex_injective hb, hi]
    | ctor b' i' c' => simp [keyName, blockName] at h
  | ctor b i c =>
    cases s with
    | member b' i' => simp [keyName, blockName] at h
    | ctor b' i' c' =>
      simp only [keyName, blockName, ConLeche.Name.num.injEq, ConLeche.Name.str.injEq,
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

/-- Names the frontend derives from others; a pin may not take one. -/
def derivedShape : CName → Bool
  | .str _ s => s == "rec" || s.startsWith "rec_" || s == "_model"
  | n => n.isProjFnShape

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

/-- The pinned names and the level-parameter names a reading uses. -/
structure Pins where
  names : Std.HashMap (ConstRef Address) CName := {}
  /-- level-parameter names for pinned constants and their blocks'
  recursors (`matchesPin` compares the standard axioms' level parameters
  by name) -/
  levels : Std.HashMap (ConstRef Address) (List CName) := {}

/-! ## Stores and references -/

abbrev Store := Address → Option Ixon.Constant

def emptyTables (c : Ixon.Constant) : Bool :=
  c.sharing.isEmpty && c.refs.isEmpty && c.univs.isEmpty

/-- The reference a record address denotes: a singleton is member 0 of
itself, a projection the member (or constructor) of its owning block, a
`muts` block nothing. The same resolution as Ix's own reader
(`Ix.Kernel.Ingress.referenceSourceBy`). -/
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

/-- Everything a record is read against: the stores, the pins, the
recursor index and the host's (optional, untrusted) reducibility hints. -/
structure Ctx where
  store : Store
  blob : Address → Option ByteArray
  pins : Pins
  index : RecIndex
  hint : ConstRef Address → Option ConLeche.ReducibilityHint := fun _ => none

def Ctx.nameOf (cx : Ctx) (r : ConstRef Address) : CName :=
  match cx.index.recs[r]? with
  | some e => e.name
  | none => cx.pins.names.getD r (keyName r)

/-- A constant's level-parameter names: the table's where it has a list of
the right length, positional otherwise. -/
def Ctx.lpsOf (cx : Ctx) (r : ConstRef Address) (lvls : Nat) : List CName :=
  match cx.pins.levels[r]? with
  | some ns => if ns.length == lvls then ns else levelNames lvls
  | none => levelNames lvls

/-- A recursor's level-parameter names: the table's, or the block's
behind a fresh elimination level for a large eliminator (Lean's
`elim :: lps`, which con-leche recognises by name). -/
def Ctx.recLps (cx : Ctx) (r : ConstRef Address) (large : Bool) (lvls : Nat)
    (blockLps : List CName) : List CName :=
  match cx.pins.levels[r]? with
  | some ns => if ns.length == lvls then ns else fallback
  | none => fallback
where
  fallback : List CName :=
    if large then
      let elim := (List.range (lvls + 1)).map levelName |>.find? (!blockLps.contains ·)
      elim.getD (levelName lvls) :: blockLps
    else blockLps

/-! ## Expressions -/

/-- Little-endian natural-number payload (Ix's `Ingress.natural`). -/
def natural (bytes : ByteArray) : Nat :=
  bytes.data.foldr (fun byte rest => byte.toNat + 256 * rest) 0

def convUniv (param : Nat → CName) : Ixon.Univ → CLevel
  | .zero => .zero
  | .succ u => .succ (convUniv param u)
  | .max a b => .max (convUniv param a) (convUniv param b)
  | .imax a b => .imax (convUniv param a) (convUniv param b)
  | .var i => .param (param i.toNat)

/-- The naming of a member's universe variables: variable `i` is its
`i`-th level parameter. -/
def paramOf (lps : List CName) (i : Nat) : CName := lps.getD i (levelName i)

/-- The context of one member's expressions. -/
structure ECx where
  cx : Ctx
  src : Ixon.Constant
  /-- the member's universe table under its level naming -/
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
  | .var i => pure (ConLeche.Expr.mkBvar i.toNat)
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
  | .lam _ t b => do pure (.lam (← convExpr e tbl t) (← convExpr e tbl b) ⟨.never⟩)
  | .all _ _ t b => do pure (.forallE (← convExpr e tbl t) (← convExpr e tbl b) ⟨.never⟩)
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

def MemberReader.mk' (cx : Ctx) (src : Ixon.Constant) (param : Nat → CName)
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
declarations before the current one (con-leche's `StateD`, minus the
NDJSON tables). -/

structure State where
  constTypes : Std.HashMap CName (List CName × CExpr) := {}
  heights : Std.HashMap CName Nat := {}
  indBlocks : Std.HashMap CName ConLeche.Frontend.InModel.BlockRec := {}
  projOwners : Std.HashMap CName ConLeche.Frontend.ProjRecOwner := {}
  projLevels : Std.HashMap CName CLevel := {}
  /-- projection functions rewritten to recursor form, and the records the
  modeller generated (counts, for the drivers' receipts) -/
  projRewrites : Nat := 0
  generated : Nat := 0
  deriving Inhabited

/-- Record a declaration's constants (`ExportC.noteDecl`). -/
def State.note (st : State) (d : CDecl) : State :=
  let cvs : List (CName × List CName × CExpr × Option Nat) := match d with
    | .axiomDecl cv => [(cv.name, cv.levelParams, cv.type, none)]
    | .defnDecl cv _ h =>
      [(cv.name, cv.levelParams, cv.type, some (ConLeche.Frontend.InModel.hintHeight h))]
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
      if ConLeche.Frontend.isProjIotaName cv.name then
        match ConLeche.Frontend.projIotaLevel cv.type with
        | some l => { st with projLevels := st.projLevels.insert cv.name l }
        | none => st
      else st
    | _ => st
  { st.note d with generated := st.generated + 1 }

/-- The projection-function rewrite at a definition or theorem record
(`ExportC.projRewriteD`). -/
def projRewrite (st : State) (cv : CVal) (value : CExpr) : Option CExpr := do
  let .proj T i (.bvar 0) := ConLeche.Frontend.lamBody value | none
  let o ← st.projOwners[T]?
  guard (cv.levelParams == o.lps)
  let l ← st.projLevels[ConLeche.Frontend.projIotaName T i]?
  ConLeche.Frontend.projRecValue o l cv.type value i

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
  owners : List ConLeche.Frontend.ProjRecOwner := []
  /-- the block, by member name, for the modeller's nested rung -/
  blocks : List (CName × ConLeche.Frontend.InModel.BlockRec) := []
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

/-- A definition member: its declaration (`ExportC.processLineCoreD`), and
whether the projection rewrite applied. `heights` are the definitional
heights so far (the block's earlier members included). -/
def readDefinition (cx : Ctx) (st : State) (heights : CName → Nat) (ref : ConstRef Address)
    (lps : List CName) (mr : MemberReader) (d : Ixon.Definition) : ReadM (CDecl × Bool) := do
  let name := cx.nameOf ref
  let cv : CVal := ⟨name, lps, ← mr.read d.typ⟩
  let value ← mr.read d.value
  let rewritten := projRewrite st cv value
  let value' := rewritten.getD value
  let decl ← match d.kind with
    | .defn => do
      unless d.safety == .safe do
        declined s!"definition with safety '{safetyWord d.safety}'"
      let hint := (cx.hint ref).getD (ConLeche.Frontend.InModel.hintFor heights value')
      pure (ConLeche.Declaration.defnDecl cv value' hint)
    | .thm => pure (ConLeche.Declaration.thmDecl cv value')
    | .opaq => do
      if d.safety == .unsaf then declined "unsafe opaque declaration"
      pure (ConLeche.Declaration.opaqueDecl cv value)
  pure (decl, rewritten.isSome && d.kind != .opaq)

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
it references; `none` on a cycle. -/
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

/-- An inductive block with its recursors: one `indDecl`, preceded by the
modeller's records for a nested or mutual block (`ExportC.validateIndD` and
`installIndD`). -/
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
  let blockLps := cx.lpsOf (.member owner (indcs[0]!.1)) first.lvls.toNat
  let mrInd := MemberReader.mk' cx c (paramOf blockLps) self
  let lpsAt (lvls : UInt64) : List CName :=
    if lvls == first.lvls then blockLps else levelNames lvls.toNat
  -- types, in motive order
  let mut types : Array CVal := #[]
  let mut tyRecs : Array (Nat × Ixon.Inductive) := #[]
  for (i, ind) in indcs do
    types := types.push ⟨cx.nameOf (.member owner i), lpsAt ind.lvls, ← mrInd.read ind.typ⟩
    tyRecs := tyRecs.push (i, ind)
  -- constructors, in the block's own order
  let mut ctors : Array (CVal × Nat × Nat) := #[]
  let mut ctorNames : Array (List CName) := #[]
  for (i, ind) in indcs do
    let mut names : List CName := []
    for (ctor, j) in ind.ctors.zipIdx do
      unless ctor.cidx.toNat == j do malformed "constructor index differs from its position"
      if ctor.isUnsafe then declined "unsafe inductive declaration"
      let cv : CVal := ⟨cx.nameOf (.ctor owner i j), lpsAt ctor.lvls, ← mrInd.read ctor.typ⟩
      unless nPd + ctor.fields.toNat == piTeleLen cv.type do
        malformed s!"constructor {cv.name} declares {ctor.fields} fields at {nPd} parameters; \
          its type has {piTeleLen cv.type} binders"
      ctors := ctors.push (cv, ctor.params.toNat, ctor.fields.toNat)
      names := names ++ [cv.name]
    ctorNames := ctorNames.push names
  -- recursors, in motive order
  let mut recs : Array (CVal × Ixon.Recursor × List ConLeche.RecRule) := #[]
  for ref in shape.recs do
    let some entry := cx.index.recs[ref]? | malformed "unindexed recursor"
    let .member rOwner j := ref | malformed "recursor reference is a constructor"
    let some rc := cx.store rOwner | malformed "recursor record is missing"
    let some (_, r) := (recursorMembers rc).find? (·.1 == j) | malformed "recursor member is missing"
    if r.isUnsafe then declined "unsafe inductive declaration"
    let rself : Nat → Option CName := fun i => match rc.info with
      | .muts rms => if i < rms.size then some (cx.nameOf (.member rOwner i)) else none
      | _ => if i == 0 then some entry.name else none
    let lps := cx.recLps ref entry.large r.lvls.toNat blockLps
    let mr := MemberReader.mk' cx rc (paramOf lps) rself
    let cv : CVal := ⟨entry.name, lps, ← mr.read r.typ⟩
    let some major := inductiveAt cx.store entry.major
      | declined s!"recursor {entry.name}: its major premise is not an inductive"
    unless major.ctors.size == r.rules.size do
      malformed s!"recursor {entry.name} has {r.rules.size} rules for {major.ctors.size} constructors"
    let .member mb mi := entry.major | malformed "recursor major is a constructor"
    let mut rules : List ConLeche.RecRule := []
    for (rule, k) in r.rules.zipIdx do
      rules := rules ++ [ConLeche.RecRule.mk (cx.nameOf (.ctor mb mi k)) rule.fields.toNat 0 .inert
        (← mr.read rule.rhs) false false false]
    recs := recs.push (cv, r, rules)
  -- the stream's own consistency checks (`validateIndD`)
  let nTypes := types.size
  let nCtors := ctors.size
  let numNested := match recs[0]? with
    | some (_, r, _) => r.motives.toNat - nTypes
    | none => 0
  let nested := numNested != 0
  let kExpected? : Option Bool :=
    match types.toList, ctorNames.toList, ctors.toList with
    | [ty], [[_]], [(_, _, nF)] =>
      match ty.type.piResult with
      | .sort s => some (nF == 0 && ConLeche.Level.isEquiv s .zero == some true)
      | _ => none
    | _, _, _ => some false
  unless nested do
    for (cv, r, _) in recs do
      unless r.params.toNat == nPd do
        malformed s!"recursor {cv.name} declares {r.params} parameters; the block declares {nPd}"
      unless r.motives.toNat == nTypes do
        malformed s!"recursor {cv.name} declares {r.motives} motives; the block has {nTypes} types"
      unless r.minors.toNat == nCtors do
        malformed s!"recursor {cv.name} declares {r.minors} minor premises; the block has {nCtors} constructors"
      if let some kE := kExpected? then
        unless r.k == kE do
          malformed s!"recursor {cv.name} declares k := {r.k}; the generated recursor is{if kE then "" else " not"} K-like"
      if let .str T "rec" := cv.name then
        for ty in types do
          if ty.name == T then
            if let some n := ty.type.piSortTeleLen? then
              unless nPd + r.indices.toNat == n do
                malformed s!"recursor {cv.name} declares {r.indices} indices; {T} has {n - nPd}"
  -- the block's constants
  let typeInfos : List CInfo := types.toList.map (.indInfo · {})
  let ctorInfos : List CInfo := ctors.toList.map fun (cv, nP, nF) => .ctorInfo cv nP nF
  let recInfos : List CInfo := recs.toList.map fun (cv, r, rules) =>
    let nP := r.params.toNat; let nM := r.motives.toNat
    let nm := r.minors.toNat; let nI := r.indices.toNat
    .recInfo cv (nP + nM + nm + nI) (nP + nM + nm) rules
  let block := typeInfos ++ ctorInfos ++ recInfos
  -- shape flags the export carries and Ixon does not: recursive and
  -- reflexive occurrences, read off the constructors' field domains
  let memberNames := types.toList.map (·.name)
  let fieldDoms := ctors.toList.flatMap fun (cv, _, _) =>
    (ConLeche.Frontend.stripPisAll cv.type).1.map (·.1)
  let isRec := fieldDoms.any fun d => memberNames.any (ConLeche.Frontend.occursConstFast · d)
  let isReflexive := fieldDoms.any fun d =>
    let (bs, body) := ConLeche.Frontend.stripPisAll d
    !bs.isEmpty && memberNames.any (ConLeche.Frontend.headIs · body)
  -- the projection rewrite's owners (`registerProjOwners`)
  let ownerTypes := (types.zip tyRecs).toList.zip ctorNames.toList |>.map fun ((cv, (_, ind)), cs) =>
    (cv.name, cv.levelParams, cv.type, ind.params.toNat, ind.indices.toNat, cs, isRec)
  let ownerCtors := ctors.toList.map fun (cv, _, nF) => (cv.name, nF, cv.type)
  let ownerRecs := recs.toList.map fun (cv, r, _) =>
    (cv.name, cv.levelParams, cv.type, r.motives.toNat, r.minors.toNat)
  let owners := ConLeche.Frontend.projRecOwners block ownerTypes ownerCtors ownerRecs
  -- the in-process modeller
  let b : ConLeche.Frontend.InModel.BlockRec :=
    ⟨(types.zip tyRecs).toList.zip ctorNames.toList |>.map fun ((cv, (_, ind)), cs) =>
        { cv, nP := ind.params.toNat, nIdx := ind.indices.toNat, ctors := cs, isRec,
          isReflexive, numNested },
     ctors.toList.map fun (cv, nP, nF) => { cv, nP, nF },
     recs.toList.map fun (cv, r, rules) =>
       { cv, nP := r.params.toNat, nM := r.motives.toNat, nm := r.minors.toNat,
         nI := r.indices.toNat, rules }⟩
  let blocks := b.types.map (·.cv.name, b)
  let decl := ConLeche.Declaration.indDecl block nPd
  if ConLeche.Frontend.InModel.wants b then
    -- the block's own members are visible to the nested rung, as in the
    -- decoder (`installIndD` registers the block before generating)
    let ctx : ConLeche.Frontend.InModel.Ctx :=
      ⟨fun n => st.constTypes[n]?, fun n => st.heights.getD n 0,
       fun n => if memberNames.contains n then some b else st.indBlocks[n]?⟩
    match ConLeche.Frontend.InModel.generate ctx b with
    | .error why => declined s!"in-process model of {(types[0]?.map (·.name)).getD .anonymous}: {why}"
    | .ok gen => pure { decls := gen.toArray.push decl, generated := gen.length, owners, blocks }
  else
    pure { decls := #[decl], owners, blocks }

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
    let lps := cx.lpsOf (.member owner 0) d.lvls.toNat
    let (decl, rw) ← readDefinition cx st (st.heights.getD · 0) (.member owner 0) lps
      (.mk' cx c (paramOf lps) self) d
    pure { decls := #[decl], projRewrites := if rw then 1 else 0 }
  | .recr _ =>
    unless cx.index.recs.contains (.member owner 0) do
      declined "recursor whose inductive block is not in the input"
    pure {}
  | .axio a =>
    if a.isUnsafe then declined "unsafe axiom"
    let lps := cx.lpsOf (.member owner 0) a.lvls.toNat
    let mr := MemberReader.mk' cx c (paramOf lps) (fun _ => none)
    let cv : CVal := ⟨cx.nameOf (.member owner 0), lps, ← mr.read a.typ⟩
    pure { decls := #[ConLeche.Declaration.axiomDecl cv] }
  | .quot q =>
    let lps := cx.lpsOf (.member owner 0) q.lvls.toNat
    let mr := MemberReader.mk' cx c (paramOf lps) (fun _ => none)
    let cv : CVal := ⟨cx.nameOf (.member owner 0), lps, ← mr.read q.typ⟩
    let kind : ConLeche.QuotKind := match q.kind with
      | .type => .type | .ctor => .ctor | .lift => .lift | .ind => .ind
    pure { decls := #[ConLeche.Declaration.quotDecl kind cv] }
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
      let some order := defOrder (defs.map (recurDeps c))
        | declined "mutually recursive definition block"
      let self : Nat → Option CName := fun i =>
        if i < ms.size then some (cx.nameOf (.member owner i)) else none
      let mut readers : List (List CName × MemberReader) := []
      let mut blockHeights : Std.HashMap CName Nat := {}
      let mut out : Array CDecl := #[]
      let mut rewrites := 0
      for i in order do
        let lps := cx.lpsOf (.member owner i) defs[i]!.lvls.toNat
        let mr ← match readers.lookup lps with
          | some mr => pure mr
          | none =>
            let mr := MemberReader.mk' cx c (paramOf lps) self
            readers := (lps, mr) :: readers
            pure mr
        let heights : CName → Nat := fun n => blockHeights.getD n (st.heights.getD n 0)
        let (decl, rw) ← readDefinition cx st heights (.member owner i) lps mr defs[i]!
        if let .defnDecl cv _ h := decl then
          blockHeights := blockHeights.insert cv.name (ConLeche.Frontend.InModel.hintHeight h)
        if rw then rewrites := rewrites + 1
        out := out.push decl
      pure { decls := out, projRewrites := rewrites }
    else malformed "a block mixes recursors and definitions"

/-! ## The constants a literal references

`ConLeche.Expr.constsResolve` counts a `Nat` literal as a reference to the
`Nat` basis trio (`Nat`, `Nat.zero`, `Nat.succ`) and a `String` literal as a
reference to that trio and the seven string-support constants (`String`,
`String.ofList`, `List`, `List.nil`, `List.cons`, `Char`, `Char.ofNat`), and
the checker declines a string literal while those are not installed. An
Ixon record that only uses a literal names none of them (its `nat`/`str`
nodes point at blobs), so a dependency order over table references alone can
put a literal user before the support: `String.instInhabited`, whose value
is `⟨""⟩`, came before `String.ofList` and `Char.ofNat` in the L4a census
and blocked 760 records. `literalEdges` adds those implicit references as
dependency edges, as the census adds a pinned `Nat` operation's certificate
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
  [ConLeche.natName, ConLeche.natZeroName, ConLeche.natSuccName]

/-- The constants a `String` literal references (`Expr.constsResolve`). -/
def strLitSupportNames : List CName :=
  natLitSupportNames ++
    [ConLeche.stringName, ConLeche.stringOfListName, ConLeche.listName, ConLeche.listNilName,
     ConLeche.listConsName, ConLeche.charName, ConLeche.charOfNatName]

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

/-- The records' store: the supplied records first, then a fallback (the
prelude's records). -/
def storeOf (records : Array (Address × Ixon.Constant)) (fallback : Store := fun _ => none) :
    Store :=
  let m : Std.HashMap Address Ixon.Constant :=
    records.foldl (fun m (a, c) => if m.contains a then m else m.insert a c) {}
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

end Ix.Kernel.ConLecheReader
