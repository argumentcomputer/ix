module

public import IxC.Ixon.Types
public import IxC.Ixon.ModeRead

/-!
# A record's modes, by position

The run-program reading (`IxC.Resource.Read`) takes every mode from the record
that holds it, by position, and from nowhere else (`IxC.Ixon.ModeRead`):

* a binder's mode (`Ixon.AllMode`: the bound variable's mode and the result
  mode of the binder's own arrow, for a `lam` as for an `all`) at its node in
  the record's binder-data section: one block per root expression, and one per
  variant of a sharing entry that has a binder; the nodes in pre-order, one per
  `lam`, per `all`, and per `share` of an entry with a binder (a share node
  names the variant its entry is read at);
* a `let`'s mode in its header (`Ixon.Expr.letE`);
* a constructor field's mode in its constructor (`Constructor.fieldModes`).

This module is the one place that knows how a record spells them. The reading
matches the blocks to the expressions itself (`IxC.Resource.Read`): a node of
the wrong kind, a missing or surplus node, or a share node naming a variant
with no block is a malformed record.
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
  | .lam t b => pure (.lam t b)
  | .all t b => pure (.all t b)
  | .letE _ m t v b => pure (.letE m t v b)
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
  | .letE _ _ t v b => hasBinderUnder full t || hasBinderUnder full v || hasBinderUnder full b
  | .prj _ _ v => hasBinderUnder full v
  | .share n => full[n.toNat]?.getD false
  | _ => false

/-- Whether each sharing entry has a binder. -/
def binderfulEntries (sharing : Array Ixon.Expr) : Array Bool :=
  sharing.foldl (fun out e => out.push (hasBinderUnder out e)) #[]

/-- The number of numbered nodes of `e`: its `lam`s, its `all`s, and its share
sites of entries with a binder. -/
def nodeCount (full : Array Bool) : Ixon.Expr → Nat
  | .lam t b | .all t b => 1 + nodeCount full t + nodeCount full b
  | .app f a => nodeCount full f + nodeCount full a
  | .letE _ _ t v b => nodeCount full t + nodeCount full v + nodeCount full b
  | .prj _ _ v => nodeCount full v
  | .share n => if full[n.toNat]?.getD false then 1 else 0
  | _ => 0

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

/-- The positions, among `e`'s numbered nodes in its own block, of its leading
`lam`s (or `all`s, with `alls`), up to its first sharing reference (a binder past
it has its node in the entry's block). The reading does not use it: since V2 a
telescope, `ifaceErased`'s included, is read through sharing references by
`readTele`. It locates a leading binder's node in a root block (their suite's
`eraseBinder`). -/
def leadingBinders (full : Array Bool) (alls : Bool) : Nat → Ixon.Expr → Nat → Except String (List Nat)
  | 0, _, _ => pure []
  | n + 1, e, pos =>
    match e, alls with
    | .lam t b, false | .all t b, true =>
      return pos :: (← leadingBinders full alls n b (pos + 1 + nodeCount full t))
    | _, _ => pure []

/-- A section node as the reading sees it: a binder with its mode (whatever its
datum), or a share site with its variant. -/
def modeNode : BinderNode → ModeNode
  | .share v => .share v.toNat
  | n => .binder (n.mode?.getD {})

/-- **The record's modes**: its binder-data section's blocks, each node with its
mode. -/
def recordModes (c : Ixon.Constant) : Except String RecordModes := do
  let full := binderfulEntries c.sharing
  let blocks := c.binders.map fun b =>
    (({ shared := b.shared, index := b.index.toNat, variant := b.variant.toNat } : BlockKey),
      b.nodes.map modeNode)
  return { blocks, binderful := full }

/-- The mode of field `field` of constructor `ctor` of member `member`
(`inherited` where the record has no such field). -/
def fieldMode (c : Ixon.Constant) (member ctor field : Nat) : FieldMode :=
  match c.info with
  | .muts ms => match ms[member]? with
    | some (.indc ind) => match ind.ctors[ctor]? with
      | some k => k.fieldMode field
      | none => .inherited
    | _ => .inherited
  | _ => .inherited

/-- Whether every constructor field of the record is `inherited`. -/
def fieldModesDefault (c : Ixon.Constant) : Bool :=
  match c.info with
  | .muts ms => ms.zipIdx.all fun (m, i) => match m with
    | .indc ind => ind.ctors.zipIdx.all fun (ctor, ci) =>
      (List.range ctor.fields.toNat).all fun f => fieldMode c i ci f == .inherited
    | _ => true
  | _ => true

end IxC.Resource

end
