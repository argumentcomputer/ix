import IxCC.Fir.Syntax

/-! # Own syntax (Phase 1 fragment)

The ownership IR (design note 03 §3.1) as far as the Phase 1 fragment
(03 §4.4) needs it: Fir with explicit allocation and ownership annotations.

* `alloc c args κ` allocates a constructor of kind `κ` (a field-less one is
  an immediate, 06 S4); `proj` is a borrowed projection; every other
  right-hand side is Fir's (`fir`: `arg`, `prim`, `call`).
* Parameters carry a signature (`PSig`: mode, kind, representation), join
  points their parameters' signatures and the outer tokens their body owns
  (`φ`), functions a signature and a region-frame flag, programs a clone map.

In Phase 1 every allocation is `shared` and immortal, every parameter
`owned` and `shared`, every `φ` empty, there is no region frame and no
clone: exactly the image of `Own.immortal` (`Own.checkImmortal`). The RC
forms (`inc`, `dec`, `isShared`, `takeUnique`, `reuse`, `dropCredit`,
`freeze`, `view`), credits and regions are Phase 2 (03 §3–§5) and are not
in this syntax yet. -/

namespace IxCC.Own

open IxCC.Ixon
open IxCC.Fir (Var FunId JoinId Arg)

/-- A parameter's signature. -/
structure PSig where
  mode : Mode
  kind : Kind
  rep : Fir.Rep
  deriving DecidableEq, Repr, Inhabited

/-- The Phase 1 parameter signature: owned, shared, `rep`. -/
def PSig.plain (rep : Fir.Rep) : PSig := { mode := .owned, kind := .shared, rep }

/-- A function's signature; results are always owned. -/
structure Sig where
  params : List PSig
  result : Kind
  deriving DecidableEq, Repr, Inhabited

inductive Rhs where
  /-- `arg`, `prim` and `call` (a Fir `ctor` or `proj` here is stuck). -/
  | fir (r : Fir.Rhs)
  /-- A cell of kind `κ` holding `c` (a field-less `c` is an immediate). -/
  | alloc (c : Fir.CtorInfo) (args : List Arg) (κ : Kind)
  /-- Borrowed: its lender is the root lender of `x`. -/
  | proj (x : Var) (c : Key.CtorKey) (i : Nat)
  deriving DecidableEq, Repr, Inhabited

mutual

inductive Code where
  | bind (x : Var) (rhs : Rhs) (k : Code)
  /-- `φ`: the outer tokens the body owns (the loop invariant of a recursive
  join point, 06 S30). -/
  | jp (j : JoinId) (ps : List (Var × PSig)) (φ : List (Var × Nat)) (rec : Bool) (body k : Code)
  | jmp (j : JoinId) (args : List Arg)
  | case (x : Var) (alts : List Alt) (dflt : Option Code)
  | ret (a : Arg)
  | tcall (f : FunId) (args : List Arg)
  | trap

inductive Alt where
  | mk (key : Key.CtorKey) (body : Code)

end

deriving instance Repr for Code, Alt

instance : Inhabited Code := ⟨.trap⟩

/-- A function: its signature, parameters and body, and what it carries
from Fir unchanged (key, contracts, name supply), so that erasure gives the
Fir function back exactly. -/
structure Fun where
  key : Key.GKey
  sig : Sig
  params : List Var
  body : Code
  regionFrame : Bool := false
  result : V3.ValueContract := .shared
  contracts : List V3.BinderContract := []
  letContracts : List (Var × V3.LetContract) := []
  vars : Nat := 0
  joins : Nat := 0
  deriving Inhabited

structure Program where
  funs : Src.NatMap Fun
  size : Nat
  /-- Clone map (unique and borrow clones, 03 §6.2); empty in Phase 1. -/
  clones : List (FunId × FunId) := []
  exports : List FunId
  ctors : List Lam.CtorInfo
  known : Lam.Known
  deriving Inhabited

namespace Program

def fun? (P : Program) (f : FunId) : Option Fun := P.funs.get? f

def funList (P : Program) : List (FunId × Fun) :=
  (List.range P.size).filterMap fun f => (P.fun? f).map (f, ·)

def ctorInfo? (P : Program) (c : Key.CtorKey) : Option Fir.CtorInfo := Fir.CtorInfo.ofKey P.ctors c

end Program

/-! ## Sizes -/

mutual

def Code.size : Code → Nat
  | .bind _ _ k => k.size + 1
  | .jp _ _ _ _ b k => b.size + k.size + 1
  | .case _ alts d => Code.altsSize alts + Code.optSize d + 2
  | .jmp .. | .ret _ | .tcall .. | .trap => 1

def Code.altsSize : List Alt → Nat
  | [] => 0
  | .mk _ b :: as => b.size + Code.altsSize as

def Code.optSize : Option Code → Nat
  | none => 0
  | some c => c.size

end

theorem Code.size_pos (c : Code) : 0 < c.size := by
  cases c <;> simp [Code.size]

end IxCC.Own
