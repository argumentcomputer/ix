module
public import Ix.Aiur.Stages.Simple

/-!
Stage 4 (Concrete) IR — post monomorphization.

Same term shape as `Simple`, but over `Concrete.Typ` that has no `.mvar` and no
parametric `.app`. Every polymorphic decl has been specialised and renamed via
`concretizeName`. The lowering pass `toBytecode` consumes only `Concrete.Term`,
so `typSize` has no `.mvar` / `.app` arms to reject.
-/

public section

namespace Aiur

namespace Concrete

/-- Types after monomorphization — no mvars, no parametric apps. -/
inductive Typ where
  | unit
  | field
  | tuple    : Array Typ → Typ
  | array    : Typ → Nat → Typ
  | pointer  : Typ → Typ
  /-- Monomorphic reference. The `Global` is the concretized (mangled) name. -/
  | ref      : Global → Typ
  | function : List Typ → Typ → Typ
  deriving Repr, BEq, Hashable, Inhabited

inductive Pattern
  | wildcard
  | field : G → Pattern
  | ref : Global → Array Local → Pattern
  | tuple : Array Local → Pattern
  | array : Array Local → Pattern
  deriving Repr, BEq, Hashable, Inhabited

/-- Plain inductive form so each sub-Term is a direct constructor child,
making `sizeOf` propagate naturally through Lean's auto-derivation.

Each constructor inlines `typ : Typ` and `escapes : Bool` as the first two
arguments. Accessors `Term.typ` and `Term.escapes` pattern-match across all
constructors. -/
inductive Term : Type where
  | unit (typ : Typ) (escapes : Bool) : Term
  | var (typ : Typ) (escapes : Bool) (l : Local) : Term
  | ref (typ : Typ) (escapes : Bool) (g : Global) : Term
  | field (typ : Typ) (escapes : Bool) (g : G) : Term
  | tuple (typ : Typ) (escapes : Bool) (ts : Array Term) : Term
  | array (typ : Typ) (escapes : Bool) (ts : Array Term) : Term
  | ret (typ : Typ) (escapes : Bool) (sub : Term) : Term
  | letVar (typ : Typ) (escapes : Bool) (l : Local) (v : Term) (b : Term) : Term
  | letWild (typ : Typ) (escapes : Bool) (v : Term) (b : Term) : Term
  /-- `letLoad typ escapes dst dstTyp src body` — see `Simple.letLoad`. -/
  | letLoad (typ : Typ) (escapes : Bool) (dst : Local) (dstTyp : Typ) (src : Local) (b : Term) : Term
  | match (typ : Typ) (escapes : Bool) (scrut : Local)
          (cases : Array (Pattern × Term)) (defaultOpt : Option Term) : Term
  | app (typ : Typ) (escapes : Bool) (g : Global) (args : List Term) (unconstrained : Bool) : Term
  | add (typ : Typ) (escapes : Bool) (a : Term) (b : Term) : Term
  | sub (typ : Typ) (escapes : Bool) (a : Term) (b : Term) : Term
  | mul (typ : Typ) (escapes : Bool) (a : Term) (b : Term) : Term
  | eqZero (typ : Typ) (escapes : Bool) (a : Term) : Term
  | proj (typ : Typ) (escapes : Bool) (a : Term) (n : Nat) : Term
  | get (typ : Typ) (escapes : Bool) (a : Term) (n : Nat) : Term
  | slice (typ : Typ) (escapes : Bool) (a : Term) (i : Nat) (j : Nat) : Term
  | set (typ : Typ) (escapes : Bool) (a : Term) (n : Nat) (v : Term) : Term
  | store (typ : Typ) (escapes : Bool) (a : Term) : Term
  | load (typ : Typ) (escapes : Bool) (a : Term) : Term
  | ptrVal (typ : Typ) (escapes : Bool) (a : Term) : Term
  | assertEq (typ : Typ) (escapes : Bool) (a : Term) (b : Term) (r : Term) : Term
  | ioGetInfo (typ : Typ) (escapes : Bool) (k : Term) : Term
  | ioSetInfo (typ : Typ) (escapes : Bool) (k i l r : Term) : Term
  | ioRead (typ : Typ) (escapes : Bool) (i : Term) (n : Nat) : Term
  | ioWrite (typ : Typ) (escapes : Bool) (d r : Term) : Term
  | u8BitDecomposition (typ : Typ) (escapes : Bool) (a : Term) : Term
  | u8ShiftLeft (typ : Typ) (escapes : Bool) (a : Term) : Term
  | u8ShiftRight (typ : Typ) (escapes : Bool) (a : Term) : Term
  | u8Xor (typ : Typ) (escapes : Bool) (a : Term) (b : Term) : Term
  | u8Add (typ : Typ) (escapes : Bool) (a : Term) (b : Term) : Term
  | u8Sub (typ : Typ) (escapes : Bool) (a : Term) (b : Term) : Term
  | u8And (typ : Typ) (escapes : Bool) (a : Term) (b : Term) : Term
  | u8Or (typ : Typ) (escapes : Bool) (a : Term) (b : Term) : Term
  | u8LessThan (typ : Typ) (escapes : Bool) (a : Term) (b : Term) : Term
  | u32LessThan (typ : Typ) (escapes : Bool) (a : Term) (b : Term) : Term
  | debug (typ : Typ) (escapes : Bool) (label : String) (t : Option Term) (r : Term) : Term
  deriving Repr, Inhabited

/-- Get the type annotation of a Concrete.Term, regardless of constructor. -/
def Term.typ : Term → Typ
  | .unit t _ | .var t _ _ | .ref t _ _ | .field t _ _
  | .tuple t _ _ | .array t _ _ | .ret t _ _
  | .letVar t _ _ _ _ | .letWild t _ _ _ | .letLoad t _ _ _ _ _
  | .match t _ _ _ _ | .app t _ _ _ _
  | .add t _ _ _ | .sub t _ _ _ | .mul t _ _ _ | .eqZero t _ _
  | .proj t _ _ _ | .get t _ _ _ | .slice t _ _ _ _ | .set t _ _ _ _
  | .store t _ _ | .load t _ _ | .ptrVal t _ _
  | .assertEq t _ _ _ _ | .ioGetInfo t _ _ | .ioSetInfo t _ _ _ _ _
  | .ioRead t _ _ _ | .ioWrite t _ _ _
  | .u8BitDecomposition t _ _ | .u8ShiftLeft t _ _ | .u8ShiftRight t _ _
  | .u8Xor t _ _ _ | .u8Add t _ _ _ | .u8Sub t _ _ _
  | .u8And t _ _ _ | .u8Or t _ _ _ | .u8LessThan t _ _ _ | .u32LessThan t _ _ _
  | .debug t _ _ _ _ => t

/-- Get the escapes flag of a Concrete.Term. -/
def Term.escapes : Term → Bool
  | .unit _ e | .var _ e _ | .ref _ e _ | .field _ e _
  | .tuple _ e _ | .array _ e _ | .ret _ e _
  | .letVar _ e _ _ _ | .letWild _ e _ _ | .letLoad _ e _ _ _ _
  | .match _ e _ _ _ | .app _ e _ _ _
  | .add _ e _ _ | .sub _ e _ _ | .mul _ e _ _ | .eqZero _ e _
  | .proj _ e _ _ | .get _ e _ _ | .slice _ e _ _ _ | .set _ e _ _ _
  | .store _ e _ | .load _ e _ | .ptrVal _ e _
  | .assertEq _ e _ _ _ | .ioGetInfo _ e _ | .ioSetInfo _ e _ _ _ _
  | .ioRead _ e _ _ | .ioWrite _ e _ _
  | .u8BitDecomposition _ e _ | .u8ShiftLeft _ e _ | .u8ShiftRight _ e _
  | .u8Xor _ e _ _ | .u8Add _ e _ _ | .u8Sub _ e _ _
  | .u8And _ e _ _ | .u8Or _ e _ _ | .u8LessThan _ e _ _ | .u32LessThan _ e _ _
  | .debug _ e _ _ _ => e

structure Constructor where
  nameHead : String
  argTypes : List Typ
  deriving Repr, BEq, Inhabited

structure DataType where
  name : Global
  constructors : List Constructor
  deriving Repr, BEq, Inhabited

/-- Monomorphic function. No `params`. -/
structure Function where
  name : Global
  inputs : List (Local × Typ)
  output : Typ
  body : Term
  entry : Bool
  deriving Repr

inductive Declaration
  | function : Function → Declaration
  | dataType : DataType → Declaration
  | constructor : DataType → Constructor → Declaration
  deriving Repr, Inhabited

abbrev Decls := IndexMap Global Declaration

end Concrete

end Aiur

end
