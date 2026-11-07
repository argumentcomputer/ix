import IxCC.Lam.Syntax
import IxCC.Own.Kind

/-! # Fir syntax

The first-order IR below Anf (design note `plans/x86-v2/03-ownership.md`
§2.1, Phase 1 fragment): functions keyed by `Key.GKey`, known saturated
calls and tail calls, join points (recursive or not), `case` over
constructor keys (with `Nat` literals peeling as `Nat.zero`/`Nat.succ`),
projections, constructor applications and primitives. There are no
closures: Anf → Fir (`Fir.lower`) declines a program that still has an `fn`,
an `app` or a function-valued `glob` until P8 (Phase 2) defunctionalises it.

* **Variables are names** (`Var := Nat`), unique per function: parameters,
  `bind`s, join-point parameters and case-arm projections each bind a fresh
  one (a deterministic name supply, `Fun.vars` bounds them). Join points are
  named the same way (`Fun.joins`).
* `case x alts dflt` selects by key; an alternative binds no fields, its
  body projects them (`proj x c i`), as 03 §2.1 has it.
* `bind x (call f as) k` is a non-tail call; `tcall f as` a tail call; `jmp`
  appears only in tail position (it is a terminator). A recursive join point
  is in scope in its own body.
* Every value is `tobj` in Phase 1 (06 S33): a pointer or an immediate.
  □ is the immediate operand `Arg.erased`.
* Constructor info is a function of the checked key and Lam's constructor
  table (`CtorInfo.ofKey`, D19, 06 S43): tag and field count; every field is
  an object field of kind `shared` in Phase 1.

Phase 2 forms of 03 §2.1 that Phase 1 never produces are not in this syntax:
`Rhs.const` (statics, `Fir.Statics`), `Rhs.box`/`unbox` (word
representations) and `Program.globals`. Fir has no `tick`: Anf's ticks are
erased at Anf → Fir (06 S31). -/

namespace IxCC.Fir

open IxCC.Ixon

abbrev Var := Nat
abbrev FunId := Nat
abbrev JoinId := Nat

/-- Constructor shape (03 §2.1): a function of the checked key and the
constructor table (`ofKey`). `nobj` object fields, then `nscalar` scalar
fields; `fieldKinds` from v3 field contracts (default `shared`). -/
structure CtorInfo where
  key : Key.CtorKey
  tag : Nat
  nobj : Nat
  nscalar : Nat := 0
  fieldKinds : List Own.Kind
  deriving DecidableEq, Repr, Inhabited

namespace CtorInfo

/-- The constructor info of a key: its tag and kept-field arity from the
table, every field an object field of kind `shared` (Phase 1: no scalar
fields, no written field contracts yet). -/
def ofKey (table : List Lam.CtorInfo) (c : Key.CtorKey) : Option CtorInfo :=
  (table.find? (·.key == c)).map fun r =>
    { key := c, tag := r.tag, nobj := r.arity, fieldKinds := List.replicate r.arity .shared }

/-- Number of fields. -/
def arity (c : CtorInfo) : Nat := c.nobj + c.nscalar

/-- A field-less constructor: an immediate from Own down (06 S4). -/
def fieldless (c : CtorInfo) : Bool := c.arity == 0

end CtorInfo

/-- Value representation (06 S33), decided in Anf → Fir: `tobj` everywhere
in Phase 1. -/
inductive Rep where
  | obj
  | tobj
  | word
  | erased
  deriving DecidableEq, Repr, Inhabited

/-- An operand: a variable, a literal, or □ (an immediate). -/
inductive Arg where
  | var (x : Var)
  | lit (l : Lam.Lit)
  | erased
  deriving DecidableEq, Repr, Inhabited

inductive Rhs where
  | arg (a : Arg)
  /-- Saturated: `args.length = c.arity`. -/
  | ctor (c : CtorInfo) (args : List Arg)
  /-- Field `i` of `x` as constructor `c` (a `Nat` peels). -/
  | proj (x : Var) (c : Key.CtorKey) (i : Nat)
  /-- Saturated. -/
  | prim (op : Lam.Prim) (args : List Arg)
  /-- A known, saturated, non-tail call. -/
  | call (f : FunId) (args : List Arg)
  deriving DecidableEq, Repr, Inhabited

mutual

inductive Code where
  | bind (x : Var) (rhs : Rhs) (k : Code)
  /-- Join point `j` with `params` over `k`; `rec`: `body` may jump to `j`
  (a loop, 06 S30). -/
  | jp (j : JoinId) (params : List Var) (rec : Bool) (body k : Code)
  | jmp (j : JoinId) (args : List Arg)
  | case (x : Var) (alts : List Alt) (dflt : Option Code)
  | ret (a : Arg)
  | tcall (f : FunId) (args : List Arg)
  | trap

/-- A `case` alternative: a constructor key and the arm. -/
inductive Alt where
  | mk (key : Key.CtorKey) (body : Code)

end

deriving instance Repr for Code, Alt

instance : Inhabited Code := ⟨.trap⟩

namespace Alt

def key : Alt → Key.CtorKey | .mk k _ => k
def body : Alt → Code | .mk _ b => b

end Alt

/-- A function (03 §2.1): key, parameters with their representation, body,
and the contracts carried from Anf. -/
structure Fun where
  key : Key.GKey
  params : List (Var × Rep)
  body : Code
  result : V3.ValueContract := .shared
  contracts : List V3.BinderContract := []
  /-- `let borrow` sites (`LetKind.borrowShared` binds). -/
  letContracts : List (Var × V3.LetContract) := []
  /-- Variables are below `vars`, join points below `joins`. -/
  vars : Nat := 0
  joins : Nat := 0
  deriving Inhabited

def Fun.arity (f : Fun) : Nat := f.params.length

structure Program where
  funs : Src.NatMap Fun
  /-- Functions are numbered `0 … size - 1` (Anf's global ids). -/
  size : Nat
  /-- One function per Anf root, in root order. -/
  exports : List FunId
  /-- Lam's constructor table (for `CtorInfo.ofKey` and readback). -/
  ctors : List Lam.CtorInfo
  known : Lam.Known
  deriving Inhabited

namespace Program

def fun? (P : Program) (f : FunId) : Option Fun := P.funs.get? f

/-- Functions in id order. -/
def funList (P : Program) : List (FunId × Fun) :=
  (List.range P.size).filterMap fun f => (P.fun? f).map (f, ·)

def ctorInfo? (P : Program) (c : Key.CtorKey) : Option CtorInfo := CtorInfo.ofKey P.ctors c

end Program

/-! ## Sizes -/

mutual

def Code.size : Code → Nat
  | .bind _ _ k => k.size + 1
  | .jp _ _ _ b k => b.size + k.size + 1
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

def Program.nodes (P : Program) : Nat := P.funList.foldl (fun n (_, f) => n + f.body.size) 0

end IxCC.Fir
