module
public import IxC.Ixon.Types

/-!
# A record's modes, by position

A checker reads a record's modes where the record holds them:
* a binder's: at its node in the record's binder-data section, by position: the
  block (a root's, `shared = false`, or a sharing entry's at one of its variants,
  `shared = true`) and the node's ordinal among the block's numbered nodes (the
  expression's `lam`, `all` and binderful `share` nodes in pre-order, as the
  section numbers them). A share node has no mode; it names the variant its
  entry is read at;
* a constructor's field modes: `Constructor.fieldModes` (`fieldMode`);
* a definition's assertions: `Definition.asserts`;
* a `let`'s: its header, in the expression (`Expr.letE`'s mode).

These are the accessors the mode checker reads through.
-/

@[expose] public section

namespace Ixon

/-- A binder's position in a record's binder-data section: its block
(`shared`, `index`, `variant`, as `BinderBlock`'s fields) and its ordinal among
the block's nodes. -/
structure BinderPos where
  shared : Bool
  index : UInt64
  variant : UInt64
  ordinal : Nat
  deriving BEq, DecidableEq, Repr, Inhabited, Hashable

/-- The nodes of block `(shared, index, variant)` of `c`'s section. -/
def Constant.blockNodes? (c : Constant) (shared : Bool) (index variant : UInt64) :
    Option (Array BinderNode) :=
  (c.binders.find? fun b => b.shared == shared && b.index == index && b.variant == variant).map
    (·.nodes)

/-- The mode of the binder at `p` in `c`'s section: `none` where the section has
no node there, or a share node. -/
def Constant.binderModeAt? (c : Constant) (p : BinderPos) : Option AllMode := do
  let nodes ← c.blockNodes? p.shared p.index p.variant
  let node ← nodes[p.ordinal]?
  node.mode?

/-- The mode of field `i` of a constructor (`inherited` past its last field). -/
def Constructor.fieldMode (ctor : Constructor) (i : Nat) : FieldMode := ctor.fieldModes.get i

end Ixon

end
