import Compilatrix.Key
import Compilatrix.Src.Prim
import Compilatrix.Src.NatMap
import Compilatrix.Ixon.V3.Contracts

/-! # Lam syntax

The second IR of the rebuilt pipeline (design note
`plans/x86-v2/02-erasure-middle.md` §4.1): an untyped, call-by-value λ
calculus with box-passing erasure's `box` (□), checked constructor keys on
`con`, `case` alternatives and `proj` (D19), explicit `tick`s where erasure
elides a SrcEval charge, and `trap`. Erasure (`Lam.erase`) produces it from a
checked Src program.

* Variables are de Bruijn indices; a `name` slot is forced (and charged) at
  each read, as in SrcEval.
* A λ's `Mode` is static and inert in `eval`: it records which slots reach
  the binder (`name` only for by-name variants of `lazy` constants, the minor
  binders of erased recursors and the by-name IH binders of their minors),
  checked by `Lam.ModesOk`.
* Recursion is only through `glob`: the globals are one top-level letrec.
  Every global carries a structural key (`Key.GKey`), and a program's keys
  are pairwise distinct (`Lam.WellFormed`).
* The constructor table gives each key its source tag (the constructor
  index, for readback) and its kept-field arity. -/

namespace Compilatrix.Lam

open Compilatrix.Ixon

/-- Dense global index; never content-addressed. -/
abbrev GlobalId := Nat

inductive Lit where
  | nat (n : Nat)
  | str (s : String)
  deriving DecidableEq, Repr, Inhabited

/-- Src's `PrimOp`, one to one, plus operations only proved rewrites
introduce (`natBlt`, from `Nat.decLt` by case-of-case). -/
inductive Prim where
  | natAdd | natSub | natMul | natDiv | natMod | natPow | natGcd | natBeq | natBle
  | natLand | natLor | natXor | natShl | natShr | natPred
  | natBlt
  deriving DecidableEq, Repr, Inhabited

namespace Prim

def ofSrc : Src.PrimOp → Prim
  | .add => .natAdd | .sub => .natSub | .mul => .natMul | .div => .natDiv | .mod => .natMod
  | .pow => .natPow | .gcd => .natGcd | .beq => .natBeq | .ble => .natBle | .land => .natLand
  | .lor => .natLor | .xor => .natXor | .shiftLeft => .natShl | .shiftRight => .natShr
  | .pred => .natPred

def arity : Prim → Nat
  | .natPred => 1
  | _ => 2

def name : Prim → String
  | .natAdd => "natAdd" | .natSub => "natSub" | .natMul => "natMul" | .natDiv => "natDiv"
  | .natMod => "natMod" | .natPow => "natPow" | .natGcd => "natGcd" | .natBeq => "natBeq"
  | .natBle => "natBle" | .natLand => "natLand" | .natLor => "natLor" | .natXor => "natXor"
  | .natShl => "natShl" | .natShr => "natShr" | .natPred => "natPred" | .natBlt => "natBlt"

/-- The exact meaning on literals (Src's `PrimOp.eval2` for the shared
operations, so both levels agree by definition); `none` on an arity
mismatch. -/
def sem (p : Prim) (ns : List Nat) : Option Src.PrimResult :=
  match p, ns with
  | .natBlt, [a, b] => some (.bool (decide (a < b)))
  | .natBlt, _ => none
  | .natPred, [a] => some (Src.PrimOp.pred.eval2 a 0)
  | .natPred, _ => none
  | p, [a, b] => some ((srcOp p).eval2 a b)
  | _, _ => none
where
  srcOp : Prim → Src.PrimOp
    | .natAdd => .add | .natSub => .sub | .natMul => .mul | .natDiv => .div | .natMod => .mod
    | .natPow => .pow | .natGcd => .gcd | .natBeq => .beq | .natBle => .ble | .natLand => .land
    | .natLor => .lor | .natXor => .xor | .natShl => .shiftLeft | .natShr => .shiftRight
    | .natPred | .natBlt => .add

end Prim

/-- Evaluation mode of an application and the static mode of a λ binder. -/
inductive Mode where
  | strict
  | name
  deriving DecidableEq, Repr, Inhabited

mutual

inductive Term where
  /-- de Bruijn index; forces a `name` slot (charged). -/
  | var (i : Nat)
  /-- A global, evaluated by name at each use (charged). -/
  | glob (g : GlobalId)
  /-- `m` is static and inert; the written contract is carried. -/
  | lam (m : Mode) (c : V3.BinderContract) (b : Term)
  /-- `name` passes a thunk slot. -/
  | app (f a : Term) (m : Mode)
  /-- Strict. -/
  | letE (c : V3.LetContract) (v b : Term)
  /-- Saturated; kept fields only; a checked key (D19). -/
  | con (c : Key.CtorKey) (fields : List Term)
  | case (s : Term) (alts : List Alt) (dflt : Option Term)
  /-- Kept-field index `i` of constructor `c`. -/
  | proj (c : Key.CtorKey) (i : Nat) (s : Term)
  | lit (l : Lit)
  /-- Saturated. -/
  | prim (p : Prim) (args : List Term)
  /-- One clock unit, else transparent. -/
  | tick (t : Term)
  | box
  | trap

/-- A `case` alternative: the constructor key, its kept-field arity, and the
body under the fields (field `i` of `n` is de Bruijn index `n - 1 - i`). -/
inductive Alt where
  | mk (key : Key.CtorKey) (arity : Nat) (body : Term)

end

deriving instance Repr for Term, Alt

instance : Inhabited Term := ⟨.box⟩

namespace Alt

def key : Alt → Key.CtorKey | .mk k _ _ => k
def arity : Alt → Nat | .mk _ n _ => n
def body : Alt → Term | .mk _ _ b => b

end Alt

/-- A global: its key, closed body and result contract (the source Π's
result, 06 S35). -/
structure Global where
  key : Key.GKey
  body : Term
  result : V3.ValueContract := .shared
  deriving Inhabited

/-- A constructor-table row: the key's source tag (constructor index) and
kept-field arity. -/
structure CtorInfo where
  key : Key.CtorKey
  tag : Nat
  arity : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Keys the semantics needs: `Nat` literals peel into the pinned `Nat`
constructors, and Boolean primitives return the pinned `Bool` ones. -/
structure Known where
  natZero : Option Key.CtorKey := none
  natSucc : Option Key.CtorKey := none
  boolFalse : Option Key.CtorKey := none
  boolTrue : Option Key.CtorKey := none
  deriving Inhabited

structure Program where
  globals : Src.NatMap Global
  /-- Globals are numbered `0 … size - 1`. -/
  size : Nat
  /-- One global per Src root, in the Src program's root order. -/
  roots : List GlobalId
  ctors : List CtorInfo
  known : Known
  deriving Inhabited

namespace Program

def global? (P : Program) (g : GlobalId) : Option Global := P.globals.get? g

/-- The constructor-table row of a key. -/
def ctor? (P : Program) (c : Key.CtorKey) : Option CtorInfo := P.ctors.find? (·.key == c)

/-- Globals in id order (structural on the count). -/
def globalList (P : Program) : List (GlobalId × Global) :=
  (List.range P.size).filterMap fun g => (P.global? g).map (g, ·)

end Program

/-! ## Utilities -/

namespace Term

/-- `app* f args` with the given modes. -/
def apps (f : Term) (args : List (Term × Mode)) : Term :=
  args.foldl (fun t (a, m) => .app t a m) f

/-- `λ^n` with the given binder modes (outermost first), default contracts. -/
def lams (ms : List Mode) (b : Term) : Term :=
  ms.foldr (fun m acc => .lam m {} acc) b

/-- Set the modes of the leading λs (outermost first); `none` if there are
fewer λs than modes. -/
def setModes : List Mode → Term → Option Term
  | [], t => some t
  | m :: ms, .lam _ c b => (setModes ms b).map (.lam m c)
  | _ :: _, _ => none

/-- The modes of the leading λ-telescope. -/
def teleModes : Term → List Mode
  | .lam m _ b => m :: teleModes b
  | _ => []

mutual

/-- Number of nodes. -/
def nodes : Term → Nat
  | .var _ | .glob _ | .lit _ | .box | .trap => 1
  | .lam _ _ b | .tick b => b.nodes + 1
  | .app f a _ | .letE _ f a => f.nodes + a.nodes + 1
  | .con _ fs | .prim _ fs => nodesList fs + 1
  | .case s alts d => s.nodes + nodesAlts alts + nodesOpt d + 1
  | .proj _ _ s => s.nodes + 1

def nodesList : List Term → Nat
  | [] => 0
  | t :: ts => t.nodes + nodesList ts

def nodesAlts : List Alt → Nat
  | [] => 0
  | .mk _ _ b :: as => b.nodes + nodesAlts as

def nodesOpt : Option Term → Nat
  | none => 0
  | some t => t.nodes

end

end Term

end Compilatrix.Lam
