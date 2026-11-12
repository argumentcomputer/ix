module

public import IxC.Ixon.Types

/-!
# A record's modes, by position

The run-program reading (`IxC.Resource.Read`) takes every mode from the record
that holds it, by position, and from nowhere else:

* a binder's mode (`Ixon.AllMode`: the bound variable's mode and the result
  mode of the binder's own arrow, for a `lam` as for an `all`) at its node in
  the record's binder blocks: one block per root expression, and one per
  variant of a sharing entry that has a binder; the nodes in pre-order, one per
  `lam`, per `all`, and per `share` of an entry with a binder (a share node
  names the variant its entry is read at);
* a `let`'s mode in its header (`View.letE`);
* a constructor field's mode in its constructor (`fieldMode`).

This module is the one place that knows how a record spells them. In the
records of this format the binder modes are the contracts inline in the
expression (`Ixon.BinderContract`, `Ixon.ValueContract`, `Ixon.LetContract`),
mapped here to the modes: usage `many` with shared/unique ownership and
unrestricted/local locality is `many`, `unique`, `borrowed` or
`uniqueBorrowed`; usage `affine` is `once` (shared only); usage `erased` is
`erased` (shared and unrestricted only); usage `linear` has no mode. A `lam`
carries no result mode in this format, so its result mode is `shared`. Every
sharing entry has one variant, and no field has a mode of its own (every field
is `inherited`).

The reading matches the blocks to the expressions itself (`IxC.Resource.Read`):
a node of the wrong kind, a missing or surplus node, or a share node naming a
variant with no block is a malformed record.
-/

@[expose] public section

namespace IxC.Resource

open Ixon

/-- A binder block's key: a root's (`shared = false`, `index` the root's number
in `binderRoots` order) or a sharing entry's at one of its variants. -/
structure BlockKey where
  shared : Bool
  index : Nat
  variant : Nat
  deriving BEq, DecidableEq, Repr, Inhabited

/-- A numbered node of a binder block: a binder with its mode, or a share site
naming the variant of the entry it reads. -/
inductive ModeNode where
  | binder (m : AllMode)
  | share (variant : Nat)
  deriving BEq, Repr, Inhabited

/-- An expression node as the reading sees it: binders without their modes
(those are read by position), a `let` with its mode. -/
inductive View where
  | sort
  | var (i : Nat)
  | ref (i : Nat)
  | recur (i : Nat)
  | prj (ty field : Nat) (e : Ixon.Expr)
  | str (i : Nat)
  | nat (i : Nat)
  | app (f a : Ixon.Expr)
  | lam (ty body : Ixon.Expr)
  | all (ty body : Ixon.Expr)
  | letE (m : LetMode) (ty val body : Ixon.Expr)
  | share (i : Nat)

/-- The mode of a binder contract of this format. -/
def binderModeOf (c : BinderContract) : Except String BinderMode :=
  match c.uses, c.value.owned, c.value.locality with
  | .many, .shared, .unrestricted => pure .many
  | .many, .shared, .local => pure .borrowed
  | .many, .unique, .unrestricted => pure .unique
  | .many, .unique, .local => pure .uniqueBorrowed
  | .affine, .shared, .unrestricted => pure .once
  | .affine, .shared, .local => pure .onceBorrowed
  | .erased, .shared, .unrestricted => pure .erased
  | .linear, _, _ => throw "binder usage `linear` has no mode"
  | _, _, _ => throw "binder contract has no mode"

/-- The result mode of an `all`'s value contract. -/
def resultModeOf (v : ValueContract) : ResultMode :=
  match v.owned, v.locality with
  | .shared, .unrestricted => .shared
  | .shared, .local => .borrowed
  | .unique, .unrestricted => .unique
  | .unique, .local => .uniqueBorrowed

/-- The mode of a `let` contract. -/
def letModeOf (c : LetContract) : Except String LetMode := do
  match c.kind with
  | .value => return .value (← binderModeOf c.binder)
  | .borrowShared =>
    if c.binder == BinderContract.mk .many .localShared then return .borrow
    else throw "borrowing let with a non-default binder contract has no mode"

/-- The reading's view of a node. -/
def view : Ixon.Expr → Except String View
  | .sort _ => pure .sort
  | .var i => pure (.var i.toNat)
  | .ref i _ => pure (.ref i.toNat)
  | .recur i _ => pure (.recur i.toNat)
  | .prj t f e => pure (.prj t.toNat f.toNat e)
  | .str i => pure (.str i.toNat)
  | .nat i => pure (.nat i.toNat)
  | .app f a => pure (.app f a)
  | .lam _ t b => pure (.lam t b)
  | .all _ _ t b => pure (.all t b)
  | .letE c t v b => return .letE (← letModeOf c) t v b
  | .share i => pure (.share i.toNat)

/-- A record's root expressions, in the order its binder blocks number them: a
definition's type and value; an axiom's or quotient's type; a recursor's type
and its rules' right-hand sides; an inductive's type and its constructors'
types; a block's members in order, each contributing its roots. -/
def binderRoots : ConstantInfo → Array Ixon.Expr
  | .defn d => #[d.typ, d.value]
  | .recr r => #[r.typ] ++ r.rules.map (·.rhs)
  | .axio a => #[a.typ]
  | .quot q => #[q.typ]
  | .cPrj _ | .rPrj _ | .iPrj _ | .dPrj _ => #[]
  | .muts ms => ms.foldl (init := #[]) fun acc m => acc ++ match m with
    | .defn d => #[d.typ, d.value]
    | .indc i => #[i.typ] ++ i.ctors.map (·.typ)
    | .recr r => #[r.typ] ++ r.rules.map (·.rhs)

/-- Whether `e` has a binder, directly or through the sharing entries before it
(`full`, one flag per earlier entry). -/
def hasBinderUnder (full : Array Bool) : Ixon.Expr → Bool
  | .lam .. | .all .. => true
  | .app f a => hasBinderUnder full f || hasBinderUnder full a
  | .letE _ t v b => hasBinderUnder full t || hasBinderUnder full v || hasBinderUnder full b
  | .prj _ _ v => hasBinderUnder full v
  | .share n => full[n.toNat]?.getD false
  | _ => false

/-- Whether each sharing entry has a binder. -/
def binderfulEntries (sharing : Array Ixon.Expr) : Array Bool :=
  sharing.foldl (fun out e => out.push (hasBinderUnder out e)) #[]

/-- The numbered nodes of `e` in pre-order with their inline modes. -/
def inlineNodes (full : Array Bool) : Ixon.Expr → Array ModeNode → Except String (Array ModeNode)
  | .lam c t b, acc => do
    let m : AllMode := { input := ← binderModeOf c }
    inlineNodes full b (← inlineNodes full t (acc.push (.binder m)))
  | .all c r t b, acc => do
    let m : AllMode := { input := ← binderModeOf c, result := resultModeOf r }
    inlineNodes full b (← inlineNodes full t (acc.push (.binder m)))
  | .app f a, acc => do inlineNodes full a (← inlineNodes full f acc)
  | .letE _ t v b, acc => do
    inlineNodes full b (← inlineNodes full v (← inlineNodes full t acc))
  | .prj _ _ v, acc => inlineNodes full v acc
  | .share n, acc => pure (if full[n.toNat]?.getD false then acc.push (.share 0) else acc)
  | _, acc => pure acc

/-- A record's binder blocks. An absent block has no node. -/
structure RecordModes where
  blocks : Array (BlockKey × Array ModeNode) := #[]
  /-- per sharing entry, whether it has a binder (so whether its share sites are
  numbered nodes) -/
  binderful : Array Bool := #[]
  deriving Inhabited

/-- The nodes of the block at `k`. -/
def RecordModes.block? (rm : RecordModes) (k : BlockKey) : Option (Array ModeNode) :=
  (rm.blocks.find? (·.1 == k)).map (·.2)

/-- Whether the share sites of entry `n` are numbered nodes. -/
def RecordModes.binderfulAt (rm : RecordModes) (n : Nat) : Bool :=
  rm.binderful[n]?.getD false

/-- **The record's modes** (this format: from the inline contracts). -/
def recordModes (c : Ixon.Constant) : Except String RecordModes := do
  let full := binderfulEntries c.sharing
  let mut blocks : Array (BlockKey × Array ModeNode) := #[]
  for (root, i) in (binderRoots c.info).zipIdx do
    let nodes ← inlineNodes full root #[]
    unless nodes.isEmpty do blocks := blocks.push ({ shared := false, index := i, variant := 0 }, nodes)
  for (e, n) in c.sharing.zipIdx do
    if full[n]?.getD false then
      blocks := blocks.push ({ shared := true, index := n, variant := 0 }, ← inlineNodes full e #[])
  return { blocks, binderful := full }

/-- The mode of field `field` of constructor `ctor` of member `member` (this
format: every field is `inherited`). -/
def fieldMode (_c : Ixon.Constant) (_member _ctor _field : Nat) : FieldMode := .inherited

end IxC.Resource

end
