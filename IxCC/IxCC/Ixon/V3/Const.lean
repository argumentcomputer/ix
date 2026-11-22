import IxCC.Ixon.Kinds
import IxCC.Ixon.Address
import IxCC.Ixon.Univ
import IxCC.Ixon.V3.Expr

/-! Ixon v5 declarations: definition assertions (`Definition.asserts`),
constructor field modes (`Constructor.fieldModes`), and the binder-data section
(`Constant.binders`). Their canonical bytes are the v5 encoding of
`IxCC.Ixon.V3.Wire`. -/

namespace IxCC.Ixon.V3

structure Definition where
  kind : DefKind
  safety : DefinitionSafety
  asserts : DefAsserts := {}
  lvls : UInt64
  typ : Expr
  value : Expr
  deriving BEq, DecidableEq, Repr, Inhabited

/-- A definition's assertions are canonical: none on a theorem. -/
def Definition.assertsCanonical (d : Definition) : Bool :=
  d.kind != .thm || d.asserts == {}

structure RecursorRule where
  fields : UInt64
  rhs : Expr
  deriving BEq, DecidableEq, Repr, Inhabited

structure Recursor where
  k : Bool
  isUnsafe : Bool
  lvls : UInt64
  params : UInt64
  indices : UInt64
  motives : UInt64
  minors : UInt64
  typ : Expr
  rules : Array RecursorRule
  deriving BEq, DecidableEq, Repr, Inhabited

structure Axiom where
  isUnsafe : Bool
  lvls : UInt64
  typ : Expr
  deriving BEq, Repr, Inhabited

structure Quotient where
  kind : QuotKind
  lvls : UInt64
  typ : Expr
  deriving BEq, Repr, Inhabited

structure Constructor where
  isUnsafe : Bool
  lvls : UInt64
  cidx : UInt64
  params : UInt64
  fields : UInt64
  fieldModes : FieldModes fields.toNat := .inherited
  typ : Expr
  deriving Repr, Inhabited

instance : BEq Constructor where
  beq a b := a.isUnsafe == b.isUnsafe && a.lvls == b.lvls && a.cidx == b.cidx &&
    a.params == b.params && a.fields == b.fields &&
    a.fieldModes.toArray == b.fieldModes.toArray && a.typ == b.typ

instance : DecidableEq Constructor := fun a b =>
  match a, b with
  | ⟨u1, l1, c1, p1, f1, fm1, t1⟩, ⟨u2, l2, c2, p2, f2, fm2, t2⟩ =>
    if hu : u1 = u2 then
      if hl : l1 = l2 then
        if hc : c1 = c2 then
          if hp : p1 = p2 then
            if hf : f1 = f2 then by
              subst hu hl hc hp hf
              exact if hfm : fm1 = fm2 then
                if ht : t1 = t2 then isTrue (by subst hfm ht; rfl)
                else isFalse (fun h => ht (by cases h; rfl))
              else isFalse (fun h => hfm (by cases h; rfl))
            else isFalse (fun h => hf (by cases h; rfl))
          else isFalse (fun h => hp (by cases h; rfl))
        else isFalse (fun h => hc (by cases h; rfl))
      else isFalse (fun h => hl (by cases h; rfl))
    else isFalse (fun h => hu (by cases h; rfl))

/-- The mode of field `i` of a constructor (`inherited` past its last field). -/
def Constructor.fieldMode (ctor : Constructor) (i : Nat) : FieldMode :=
  ctor.fieldModes.get i

structure Inductive where
  isUnsafe : Bool
  lvls : UInt64
  params : UInt64
  indices : UInt64
  typ : Expr
  ctors : Array Constructor
  deriving BEq, DecidableEq, Repr, Inhabited

structure InductiveProj where
  idx : UInt64
  block : Address
  deriving BEq, Repr, Inhabited

structure ConstructorProj where
  idx : UInt64
  cidx : UInt64
  block : Address
  deriving BEq, Repr, Inhabited

structure RecursorProj where
  idx : UInt64
  block : Address
  deriving BEq, Repr, Inhabited

structure DefinitionProj where
  idx : UInt64
  block : Address
  deriving BEq, Repr, Inhabited

inductive MutConst where
  | defn : Definition → MutConst
  | indc : Inductive → MutConst
  | recr : Recursor → MutConst
  deriving BEq, DecidableEq, Repr, Inhabited

inductive ConstantInfo where
  | defn : Definition → ConstantInfo
  | recr : Recursor → ConstantInfo
  | axio : Axiom → ConstantInfo
  | quot : Quotient → ConstantInfo
  | cPrj : ConstructorProj → ConstantInfo
  | rPrj : RecursorProj → ConstantInfo
  | iPrj : InductiveProj → ConstantInfo
  | dPrj : DefinitionProj → ConstantInfo
  | muts : Array MutConst → ConstantInfo
  deriving BEq, Repr, Inhabited

namespace ConstantInfo

def CONST_DEFN : UInt64 := 0
def CONST_RECR : UInt64 := 1
def CONST_AXIO : UInt64 := 2
def CONST_QUOT : UInt64 := 3
def CONST_CPRJ : UInt64 := 4
def CONST_RPRJ : UInt64 := 5
def CONST_IPRJ : UInt64 := 6
def CONST_DPRJ : UInt64 := 7

/-- A record's root expressions in the order the binder-data section numbers
them (matching `_root_.Ixon.ConstantInfo.binderRoots`): a definition's type and
value; an axiom's or quotient's type; a recursor's type and its rules'
right-hand sides; an inductive's type and its constructors' types; a block's
members in order. A projection has none. -/
def binderRoots : ConstantInfo → Array Expr
  | .defn d => #[d.typ, d.value]
  | .recr r => #[r.typ] ++ r.rules.map (·.rhs)
  | .axio a => #[a.typ]
  | .quot q => #[q.typ]
  | .cPrj _ | .rPrj _ | .iPrj _ | .dPrj _ => #[]
  | .muts ms => ms.foldl (init := #[]) fun acc m => acc ++ match m with
    | .defn d => #[d.typ, d.value]
    | .indc i => #[i.typ] ++ i.ctors.map (·.typ)
    | .recr r => #[r.typ] ++ r.rules.map (·.rhs)

/-- Largest universe level parameter count among the record's members. -/
def maxLvls : ConstantInfo → Nat
  | .defn d => d.lvls.toNat
  | .recr r => r.lvls.toNat
  | .axio a => a.lvls.toNat
  | .quot q => q.lvls.toNat
  | .cPrj _ | .rPrj _ | .iPrj _ | .dPrj _ => 0
  | .muts ms => ms.foldl (init := 0) fun acc m => max acc <| match m with
    | .defn d => d.lvls.toNat
    | .indc i => i.lvls.toNat
    | .recr r => r.lvls.toNat

/-- Whether any member of the record is unsafe or partial (in which case a
complete binder-data section carries `.undecided` on every binder). -/
def uncheckedSafety : ConstantInfo → Bool
  | .defn d => d.safety != .safe
  | .recr r => r.isUnsafe
  | .axio a => a.isUnsafe
  | .quot _ => false
  | .cPrj _ | .rPrj _ | .iPrj _ | .dPrj _ => false
  | .muts ms => ms.any fun
    | .defn d => d.safety != .safe
    | .indc i => i.isUnsafe
    | .recr r => r.isUnsafe

end ConstantInfo

/-- Recover the member table used when a constant is entered as its own
evaluation/checking frame. Standalone definitions and recursors behave as
singleton blocks; projections, axioms, quotients, and inductive projections
have no local `recur` members. -/
def selfMutsOf : ConstantInfo → Array MutConst
  | .muts members => members
  | .defn definition => #[.defn definition]
  | .recr recursor => #[.recr recursor]
  | _ => #[]

/-- A top-level constant with sharing, refs, univs tables, and its binder-data
section (blocks sorted by `(shared, index, variant)`). -/
structure Constant where
  info : ConstantInfo
  sharing : Array Expr
  refs : Array Address
  univs : Array Univ
  binders : Array BinderBlock := #[]
  deriving BEq, Repr, Inhabited

namespace Constant

def FLAG_MUTS : UInt8 := 0xC
def FLAG : UInt8 := 0xD

/-- The record's modes outside its binder-data section are canonical: no theorem
asserts anything. -/
def modesCanonical (c : Constant) : Bool :=
  match c.info with
  | .defn d => d.assertsCanonical
  | .muts ms => ms.all fun
    | .defn d => d.assertsCanonical
    | _ => true
  | _ => true

/-- The nodes of block `(shared, index, variant)` of `c`'s binder-data section. -/
def blockNodes? (c : Constant) (shared : Bool) (index variant : UInt64) :
    Option (Array BinderNode) :=
  (c.binders.find? fun b => b.shared == shared && b.index == index && b.variant == variant).map
    (·.nodes)

/-- The binder node at `p` in `c`'s binder-data section. -/
def binderNodeAt? (c : Constant) (p : BinderPos) : Option BinderNode := do
  let nodes ← c.blockNodes? p.shared p.index p.variant
  nodes[p.ordinal]?

/-- The mode of the binder at `p` in `c`'s section (`none` if missing or a
share node). -/
def binderModeAt? (c : Constant) (p : BinderPos) : Option AllMode := do
  let node ← c.binderNodeAt? p
  node.mode?

end Constant

/-! ## Embedded expression enumeration

This is the authoritative body order consumed by the sharing-table checker.
It covers every expression in a constant payload; projections contain none. -/

def Definition.exprs (d : Definition) : List Expr := [d.typ, d.value]

def Recursor.exprs (r : Recursor) : List Expr :=
  r.typ :: r.rules.toList.map (·.rhs)

def Axiom.exprs (a : Axiom) : List Expr := [a.typ]

def Quotient.exprs (q : Quotient) : List Expr := [q.typ]

def Constructor.exprs (c : Constructor) : List Expr := [c.typ]

def Inductive.exprs (i : Inductive) : List Expr :=
  i.typ :: i.ctors.toList.flatMap Constructor.exprs

def MutConst.exprs : MutConst → List Expr
  | .defn d => d.exprs
  | .indc i => i.exprs
  | .recr r => r.exprs

def ConstantInfo.exprs : ConstantInfo → List Expr
  | .defn d => d.exprs
  | .recr r => r.exprs
  | .axio a => a.exprs
  | .quot q => q.exprs
  | .cPrj _ | .rPrj _ | .iPrj _ | .dPrj _ => []
  | .muts ms => ms.toList.flatMap MutConst.exprs

end IxCC.Ixon.V3
