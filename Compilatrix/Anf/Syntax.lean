import Compilatrix.Lam.Syntax

/-! # Anf syntax

The third IR of the rebuilt pipeline (design note
`plans/x86-v2/02-erasure-middle.md` §6.1): A-normal form with second-class
join points and known calls, produced from Lam by ANF conversion
(`Anf.convert`, P1) and rewritten by the middle-end passes P2–P4.

* Every intermediate value is named by a `bind`; operands are atoms (a
  variable, a literal or □).
* **Value variables and join points have separate de Bruijn index spaces.**
  A `bind` binds one value variable; a `case` alternative binds its fields
  (field `i` of `n` at index `n - 1 - i`); a join point's body binds its
  parameters the same way (parameter `i` of `n` at `n - 1 - i`); an `fn`'s
  body sees its captured environment extended by its parameters.
* `join n rec b e` binds a join point of arity `n` over `e`; with `rec` it is
  also in scope in its own body `b` (a loop). Jumps are expressions, so they
  occur in tail position only; an `fn` body starts with no join point in
  scope.
* `call g as` is a known call of a global of arity `as.length`; `app f as`
  applies an unknown function (arity dispatch, gone after P8); `fn ps b` is a
  local, non-recursive closure of arity `ps.length ≥ 1` (gone after P8).
* `glob g` is the value of a global: a closure for a function global (free),
  or the body's value for a CAF (`ps = []`, evaluated at each use).
* `tick` charges one clock unit and is otherwise transparent; `trap` traps.
* Globals carry their structural key (`Key.GKey`), binder contracts and
  result contract (06 S35); `con`, `case` alternatives and `proj` carry
  checked constructor keys (D19). The constructor table and the pinned keys
  are Lam's. -/

namespace Compilatrix.Anf

open Compilatrix.Ixon

abbrev GlobalId := Nat

/-- An operand. -/
inductive Atom where
  | var (i : Nat)
  | lit (l : Lam.Lit)
  | box
  deriving DecidableEq, Repr, Inhabited

mutual

/-- The right-hand side of a `bind`. -/
inductive Bind where
  | atom (a : Atom)
  /-- Saturated; kept fields only. -/
  | con (c : Key.CtorKey) (as : List Atom)
  /-- Kept-field index `i` of constructor `c`. -/
  | proj (c : Key.CtorKey) (i : Nat) (x : Atom)
  /-- Saturated. -/
  | prim (p : Lam.Prim) (as : List Atom)
  /-- The value of a global: a closure (free) or a CAF's value (charged). -/
  | glob (g : GlobalId)
  /-- A known call: `as.length` is the arity of `g`. -/
  | call (g : GlobalId) (as : List Atom)
  /-- An unknown call (arity dispatch). -/
  | app (f : Atom) (as : List Atom)
  /-- A local closure of arity `ps.length ≥ 1`. -/
  | fn (ps : List V3.BinderContract) (b : Exp)

inductive Exp where
  | bind (c : V3.LetContract) (b : Bind) (e : Exp)
  /-- A join point of arity `arity` over `e`; recursive when `rec`. -/
  | join (arity : Nat) (rec : Bool) (b : Exp) (e : Exp)
  /-- Tail position only. -/
  | jump (j : Nat) (as : List Atom)
  | case (x : Atom) (alts : List Alt) (dflt : Option Exp)
  | ret (a : Atom)
  | tick (e : Exp)
  | trap

/-- A `case` alternative: key, kept-field arity and body under the fields. -/
inductive Alt where
  | mk (key : Key.CtorKey) (arity : Nat) (body : Exp)

end

deriving instance Repr for Bind, Exp, Alt

instance : Inhabited Bind := ⟨.atom .box⟩
instance : Inhabited Exp := ⟨.trap⟩

namespace Alt

def key : Alt → Key.CtorKey | .mk k _ _ => k
def arity : Alt → Nat | .mk _ n _ => n
def body : Alt → Exp | .mk _ _ b => b

end Alt

/-- The contract of a binder a pass introduces (02 §11: `many`/`shared`). -/
def freshLet : V3.LetContract := { nonDep := true }

/-- A global: key, parameter contracts (`[]` for a CAF), result contract and
body over the parameters (parameter `i` of `n` at index `n - 1 - i`). -/
structure GDef where
  key : Key.GKey
  ps : List V3.BinderContract
  result : V3.ValueContract := .shared
  body : Exp
  deriving Inhabited

def GDef.arity (d : GDef) : Nat := d.ps.length

structure Program where
  globals : Src.NatMap GDef
  /-- Globals are numbered `0 … size - 1`. -/
  size : Nat
  /-- One global per Lam root, in Lam's root order. -/
  roots : List GlobalId
  ctors : List Lam.CtorInfo
  known : Lam.Known
  deriving Inhabited

namespace Program

def global? (P : Program) (g : GlobalId) : Option GDef := P.globals.get? g

def ctor? (P : Program) (c : Key.CtorKey) : Option Lam.CtorInfo := P.ctors.find? (·.key == c)

/-- The arity of a global (`none` if absent). -/
def arity? (P : Program) (g : GlobalId) : Option Nat := (P.global? g).map (·.arity)

/-- Globals in id order. -/
def globalList (P : Program) : List (GlobalId × GDef) :=
  (List.range P.size).filterMap fun g => (P.global? g).map (g, ·)

/-- Replace the global list (ids `0 … n - 1` in order). -/
def withGlobals (P : Program) (gs : List GDef) : Program :=
  { P with globals := Src.NatMap.ofList (gs.zipIdx.map fun (g, i) => (i, g)), size := gs.length }

end Program

/-! ## Utilities -/

mutual

/-- Number of nodes. -/
def Exp.nodes : Exp → Nat
  | .bind _ b e => b.nodes + e.nodes + 1
  | .join _ _ b e => b.nodes + e.nodes + 1
  | .jump _ as => as.length + 1
  | .case _ alts d => Exp.altsNodes alts + Exp.optNodes d + 1
  | .ret _ | .trap => 1
  | .tick e => e.nodes + 1

def Bind.nodes : Bind → Nat
  | .atom _ | .glob _ | .proj .. => 1
  | .con _ as | .prim _ as | .call _ as | .app _ as => as.length + 1
  | .fn _ b => b.nodes + 1

def Exp.altsNodes : List Alt → Nat
  | [] => 0
  | .mk _ _ b :: as => b.nodes + Exp.altsNodes as

def Exp.optNodes : Option Exp → Nat
  | none => 0
  | some e => e.nodes

end

def Atom.beq : Atom → Atom → Bool
  | .var i, .var j => i == j
  | .lit a, .lit b => a == b
  | .box, .box => true
  | _, _ => false

instance : BEq Atom := ⟨Atom.beq⟩

def atomsBeq : List Atom → List Atom → Bool
  | [], [] => true
  | a :: as, b :: bs => a.beq b && atomsBeq as bs
  | _, _ => false

mutual

/-- Structural equality, by structural recursion: shrink compares arms
(`Walk.sameArms`) on the recheck path, which the kernel evaluates (M1.K1;
the derived form was compiled by well-founded recursion). -/
def Exp.beq : Exp → Exp → Bool
  | .bind c b e, .bind c' b' e' => c == c' && b.beq b' && e.beq e'
  | .join n r b e, .join n' r' b' e' => n == n' && r == r' && b.beq b' && e.beq e'
  | .jump j as, .jump j' as' => j == j' && atomsBeq as as'
  | .case x alts d, .case x' alts' d' => x.beq x' && Exp.altsBeq alts alts' && Exp.optBeq d d'
  | .ret a, .ret a' => a.beq a'
  | .tick e, .tick e' => e.beq e'
  | .trap, .trap => true
  | _, _ => false
termination_by structural e _ => e

def Bind.beq : Bind → Bind → Bool
  | .atom a, .atom a' => a.beq a'
  | .con c as, .con c' as' => decide (c = c') && atomsBeq as as'
  | .proj c i x, .proj c' i' x' => decide (c = c') && i == i' && x.beq x'
  | .prim p as, .prim p' as' => p == p' && atomsBeq as as'
  | .glob g, .glob g' => g == g'
  | .call g as, .call g' as' => g == g' && atomsBeq as as'
  | .app f as, .app f' as' => f.beq f' && atomsBeq as as'
  | .fn ps b, .fn ps' b' => ps == ps' && b.beq b'
  | _, _ => false
termination_by structural b _ => b

def Exp.altsBeq : List Alt → List Alt → Bool
  | [], [] => true
  | .mk k n b :: as, .mk k' n' b' :: as' =>
    decide (k = k') && n == n' && b.beq b' && Exp.altsBeq as as'
  | _, _ => false
termination_by structural as _ => as

def Exp.optBeq : Option Exp → Option Exp → Bool
  | none, none => true
  | some e, some e' => e.beq e'
  | _, _ => false
termination_by structural o _ => o

end

instance : BEq Exp := ⟨Exp.beq⟩

/-- Programs compared global by global (tests and `produce`). -/
def Program.beq (P Q : Program) : Bool :=
  P.size == Q.size && P.roots == Q.roots &&
  (List.range P.size).all fun g => match P.global? g, Q.global? g with
    | some a, some b => decide (a.key = b.key) && a.ps == b.ps && a.body.beq b.body
    | none, none => true
    | _, _ => false

end Compilatrix.Anf
