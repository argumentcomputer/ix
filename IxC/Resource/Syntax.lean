module

public import IxC.Ixon.Types
public import IxC.Kernel.Ref

/-!
# Run programs

A run program is what `runR` runs and what the mode checker checks: one
definition per constant of a claim's closure (`RunDef`), read from the records
(`IxC.Resource.Read`). It is erased (types and proofs are `Term.irr`), it
carries the records' modes at its binders, and it records at every relevant
node the node's **class** (`Cls`): how the value it yields is represented.

Everything is first-order and positional: arrays and lists, de Bruijn indices,
constants by record-level reference (`Ref`), no maps.
-/

@[expose] public section

namespace IxC.Resource

open Ixon

/-- A constant, by the record that holds it: a member of a block, or a
constructor of an inductive member. -/
abbrev Ref := Ix.Kernel.ConstRef Address

instance : Inhabited Ref := ⟨.member ⟨ByteArray.empty⟩ 0⟩

instance : Repr Ref where
  reprPrec r _ := match r with
    | .member b i => s!"member {b} {i}"
    | .ctor b i c => s!"ctor {b} {i} {c}"

/-- **The class of a value**: how a run represents the values of a type.
* `irr`: a type, a type former or a proof. Never evaluated; `runR` binds `irr`.
* `imm`: an immediate, with no presence on the heap: a field-less constructor,
  or a bounded number (`Imm.bits`). Nothing confines, transfers or revokes it.
* `leaf`: a counted, immutable heap value (a number cell). Uniqueness never
  applies to it, a borrow of it is enforced on its own binder only, and reading
  it out of a container does not confine it.
* `val`: anything else, with the full discipline.

Neither `imm` nor `leaf` licenses a representation to a compiler: they say how
the reference evaluator treats the values, not how compiled code stores them. -/
inductive Cls where
  | irr
  | imm
  | leaf
  | val
  deriving BEq, DecidableEq, Repr, Inhabited

/-- The union of two lists of indices. -/
def natUnion (a b : List Nat) : List Nat :=
  b.foldl (fun acc x => if acc.contains x then acc else x :: acc) a

/-- **The class of `Nat`** (and so of `Nat`'s trivial wrappers, `Fin n`): one
definition, so a different choice is a change here. `leaf`: a number may be
large, so it is a counted heap value; it is never unique, and a borrow of it is
a borrow of its binder. (`imm` would make every `Nat` an immediate, `val` an
ordinary cell.) -/
def natClass : Cls := .leaf

/-- **A type's mode skeleton**: the modes a value of the type carries at its
arrows. `data` is an inductive type or a sort, `dataApp` its application to a
type argument's skeleton, `arrow` a function type with its binder's mode and its
result's, `unknown` a type headed by a variable or a definition (its modes
cannot be read without unfolding it). -/
inductive Skel where
  | data
  | dataApp (head arg : Skel)
  | arrow (input : BinderMode) (dom : Skel) (result : ResultMode) (cod : Skel)
  | unknown
  deriving BEq, Repr, Inhabited

namespace Skel

/-- A skeleton with no mode but the default: the values of such a type carry no
mode. `unknown` counts as default (`admits`). -/
def isDefault : Skel → Bool
  | .data | .unknown => true
  | .dataApp f a => f.isDefault && a.isDefault
  | .arrow i d r c => i == .many && r == .shared && d.isDefault && c.isDefault

/-- **The unknown-skeleton rule**: whether a value of skeleton `src` may flow
to a position of skeleton `dest`. Skeletons must be equal (no subsumption),
and a position whose skeleton is `unknown` admits only values whose modes are
all default, and a value read from one is treated as mode-free: every flow into
such a position is checked, so every value found there is mode-free. One
definition, so a different rule is a change here. -/
def admits : Skel → Skel → Bool
  | .unknown, s => s.isDefault
  | d, .unknown => d.isDefault
  | .data, .data => true
  | .dataApp f a, .dataApp g b => admits f g && admits a b
  | .arrow i d r c, .arrow i' d' r' c' => i == i' && r == r' && admits d d' && admits c c'
  | d, s => d.isDefault && s.isDefault

end Skel

/-- A parameter or binder: its mode, the class of its values, the skeleton of
its type. -/
structure Param where
  mode : BinderMode := .many
  cls : Cls := .val
  skel : Skel := .unknown
  deriving BEq, Repr, Inhabited

/-- What a case alternative is applied to: a field of the matched constructor,
an irrelevant argument (a recursor's induction hypothesis, never computed), or
`()` (a matcher's argument for a field-less pattern). -/
inductive FieldArg where
  | field (i : Nat)
  | irr
  | unit
  deriving BEq, DecidableEq, Repr, Inhabited

/-- One constructor's alternative in a case: the argument position holding it
and what it is applied to. -/
structure CaseAlt where
  alt : Nat
  args : Array FieldArg
  deriving BEq, Repr, Inhabited

/-- **A case shape**: a recursor whose minor premises do not read their
induction hypotheses, or a definition recognised as one (a matcher,
`casesOn`, `ite`). `arity` arguments make a full application; `major` is the
major premise's position; `alts` gives, per constructor of `ind` in order, the
alternative's position and arguments. -/
structure CaseInfo where
  ind : Ref
  arity : Nat
  major : Nat
  alts : Array CaseAlt
  deriving BEq, Repr, Inhabited

/-- **Run terms.** De Bruijn indices; every relevant node carries its class. -/
inductive Term where
  /-- A type, a type former or a proof: not evaluated. -/
  | irr
  | var (i : Nat) (c : Cls)
  | const (r : Ref) (c : Cls)
  /-- An application; `c` is the class of its value. -/
  | app (f a : Term) (c : Cls)
  /-- A closure: its parameter, its arrow's result mode and class, the de Bruijn
  indices of its relevant free variables (its captures), its body. -/
  | lam (p : Param) (res : ResultMode) (resCls : Cls) (fvs : Array Nat) (body : Term)
  /-- `let (@m x : T) := val; body` (`d` the class of `x`), or a `borrow`. -/
  | letE (m : LetMode) (d : Cls) (val body : Term)
  /-- A full application of a case shape: its major premise, its alternatives by
  constructor (evaluated by need, in the enclosing scope), and the arguments
  past its arity. -/
  | case (k : CaseInfo) (major : Term) (alts : Array Term) (extra : Array Term) (c : Cls)
  | natLit (n : Nat)
  | strLit (s : String)
  /-- Field `i` of a value of the structure `s` (an inductive member). -/
  | proj (s : Ref) (i : Nat) (e : Term) (c : Cls)
  deriving Inhabited

/-- A constructor field: its binder's mode (`erased`, or `many`), its field
mode, the class of its values. -/
structure Field where
  mode : BinderMode := .many
  fmode : FieldMode := .inherited
  cls : Cls := .val
  deriving BEq, Repr, Inhabited

/-- The primitives: the role table's `Nat` operations, constructors and
comparisons (the comparisons give `Bool`'s constructors `t` and `f`). -/
inductive Prim where
  | zero | succ | pred
  | add | sub | mul | div | mod | pow | gcd
  | land | lor | xor | shiftLeft | shiftRight
  | beq (t f : Ref) | ble (t f : Ref)
  deriving BEq, Repr, Inhabited

/-- A primitive's arity. -/
def Prim.arity : Prim → Nat
  | .zero => 0
  | .succ | .pred => 1
  | _ => 2

/-- **A constant of a run program.** -/
inductive RunDef where
  /-- A definition's run body under its parameters, with its result mode, class
  and skeleton. With no parameter it is a static: run once, then shared. -/
  | body (params : Array Param) (result : ResultMode) (resCls : Cls) (resSkel : Skel) (t : Term)
  /-- A constructor of the inductive member `ind`: its index, its parameter
  count, its fields. -/
  | ctor (ind : Ref) (cidx nParams : Nat) (fields : Array Field)
  /-- An inductive type, with its constructors. -/
  | ind (ctors : Array Ref)
  /-- A case shape; entered only through `Term.case`. -/
  | caseDef (info : CaseInfo)
  | prim (p : Prim)
  /-- A member of the claim's extern set: runs as an `ExternOracle` says. -/
  | extern (params : Array Param) (result : ResultMode) (resCls : Cls) (resSkel : Skel)
  /-- A constant with no run body (an axiom or opaque outside the extern set,
  an unsafe or `partial` constant, a theorem, a recursor): `runR` stops at a
  call, and the checker checks calls against its interface. -/
  | stuck (params : Array Param) (result : ResultMode) (resCls : Cls) (resSkel : Skel)
  deriving Inhabited

/-- **A run program**: its constants, the inductive member that is `Nat`, and
`Bool`'s constructors (for the comparisons), when the role table binds them. -/
structure Prog where
  defs : Array (Ref × RunDef) := #[]
  nat : Option Ref := none
  deriving Inhabited

/-- A constant's run definition. -/
def Prog.find? (P : Prog) (r : Ref) : Option RunDef :=
  (P.defs.find? (·.1 == r)).map (·.2)

/-- A constructor's inductive and its index: `none` if `r` is no constructor. -/
def Prog.ctorOf? (P : Prog) (r : Ref) : Option (Ref × Nat × Nat × Array Field) :=
  match P.find? r with
  | some (.ctor ind cidx nP fields) => some (ind, cidx, nP, fields)
  | _ => none

/-- An inductive's constructors. -/
def Prog.ctorsOf (P : Prog) (ind : Ref) : Array Ref :=
  match P.find? ind with
  | some (.ind cs) => cs
  | _ => #[]

/-- A field's being relevant and not erased: what is evaluated and stored. -/
def Field.kept (f : Field) : Bool := f.mode != .erased && f.cls != .irr

/-- **A trivial wrapper**: an inductive with one constructor, whose kept
fields are exactly one, at index `i` (its values may be represented by that
field's, when the field's class is `imm` or `leaf`). -/
def Prog.wrapperField? (P : Prog) (ind : Ref) : Option Nat := do
  let cs := P.ctorsOf ind
  guard (cs.size == 1)
  let c ← cs[0]?
  let (_, _, _, fields) ← P.ctorOf? c
  let kept := (fields.zipIdx.filter fun (f, _) => f.kept).map (·.2)
  guard (kept.size == 1)
  kept[0]?

/-- The arity of a constant: how many arguments a call enters it with. -/
def RunDef.arity : RunDef → Nat
  | .body ps .. | .extern ps .. | .stuck ps .. => ps.size
  | .ctor _ _ nP fields => nP + fields.size
  | .ind _ => 0
  | .caseDef k => k.arity
  | .prim p => p.arity

end IxC.Resource

end
