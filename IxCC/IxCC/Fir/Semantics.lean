import IxCC.Fir.Syntax
import IxCC.Sem.Result

/-! # Fir semantics

The clocked big-step semantics of Fir. As in Lam and
Anf, the clock is a **depth bound**: a charge evaluates the rest of its
computation at `k - 1`, and sequenced computations each run at `k`.

**Charges**: entering a function body (`call`, `tcall`, and the
entry of `run`) and a **recursive jump**, a `jmp j` inside the body of a
recursive join point `j`. The jump from a join point's scope into
it is free, recursive or not. Fir has no `tick`: Anf's ticks and Anf's
charges on non-recursive jumps are gone, so Fir charges a subset of
the events Anf charges, and `Fir.tickBound` bounds the difference.

* Variables are looked up in a persistent map (`Env`); `bind` inserts.
* Join points form a stack (`List JEntry`): `jp` pushes an entry with the
  current environment; a jump to `j` runs `j`'s body in the environment it
  was defined in, extended by the arguments, with the join stack **below**
  `j`'s entry (exactly the join points in scope at `j`'s definition), plus
  `j` itself, now charged, when `j` is recursive. So a jump charges exactly
  when it occurs inside `j`'s own body.
* `case` and `proj` read a value as a constructor (`Val.asCtor`): a `Nat`
  literal peels as `Nat.zero`/`Nat.succ` (the pinned keys). They select and
  project by key, as Anf does; `case` takes the first alternative with the
  value's key, else the default, else is stuck.
* `prim` is exact on `Nat`; Boolean results are the pinned `Bool`
  constructors. Fir never returns `resource`.
* □ (`erased`) is stuck under `case`, `proj` and `prim`; scope,
  arity and key errors are stuck.

The semantics is never evaluated on the recheck path (D17). It recurses
well-founded on the clock, then on the size of the code plus the sizes of
the uncharged join bodies on the stack (a free jump pops at least its own
entry). -/

namespace IxCC.Fir

open IxCC.Sem (Result Obs)

inductive Val where
  | lit (l : Lam.Lit)
  | ctor (c : CtorInfo) (fields : List Val)
  | erased
  deriving Repr, Inhabited

abbrev Env := Src.NatMap Val

namespace Val

/-- A value as a constructor: `Nat` literals peel with the pinned keys. -/
def asCtor (K : Lam.Known) : Val → Option (Key.CtorKey × List Val)
  | .ctor c fs => some (c.key, fs)
  | .lit (.nat 0) => K.natZero.map (·, [])
  | .lit (.nat (n + 1)) => K.natSucc.map (·, [.lit (.nat n)])
  | _ => none

def shape : Val → String
  | .lit (.nat n) => s!"lit {n}"
  | .lit (.str _) => "str"
  | .ctor c fs => s!"ctor#{c.tag}/{fs.length}"
  | .erased => "erased"

mutual

/-- Structural equality. -/
def beq : Val → Val → Bool
  | .lit a, .lit b => a == b
  | .ctor c fs, .ctor d gs => decide (c = d) && beqList fs gs
  | .erased, .erased => true
  | _, _ => false

def beqList : List Val → List Val → Bool
  | [], [] => true
  | a :: as, b :: bs => beq a b && beqList as bs
  | _, _ => false

end

instance : BEq Val := ⟨beq⟩

end Val

def Arg.eval (ρ : Env) : Arg → Option Val
  | .var x => ρ.get? x
  | .lit l => some (.lit l)
  | .erased => some .erased

def evalArgs (ρ : Env) : List Arg → Option (List Val)
  | [] => some []
  | a :: as =>
    match a.eval ρ, evalArgs ρ as with
    | some v, some vs => some (v :: vs)
    | _, _ => none

/-- Bind variables to values pairwise. -/
def bindAll (ρ : Env) : List Var → List Val → Env
  | x :: xs, v :: vs => bindAll (ρ.insert x v) xs vs
  | _, _ => ρ

/-- Literal arguments of a primitive. -/
def natArgs : List Val → Option (List Nat)
  | [] => some []
  | .lit (.nat n) :: vs => (natArgs vs).map (n :: ·)
  | _ => none

/-- The value of a Boolean: the pinned constructor, with its info. -/
def boolVal (P : Program) (b : Bool) : Option Val :=
  match (if b then P.known.boolTrue else P.known.boolFalse) with
  | some c => (P.ctorInfo? c).map (.ctor · [])
  | none => none

/-- A saturated primitive on evaluated arguments (as Anf's `primResult`). -/
def primResult (P : Program) (p : Lam.Prim) (vs : List Val) : Result Val :=
  match natArgs vs with
  | some ns =>
    match p.sem ns with
    | some (.nat n) => .ok (.lit (.nat n))
    | some (.bool b) => Result.ofOption (boolVal P b)
    | none => .stuck
  | none => .stuck

/-- A right-hand side other than a call. -/
def evalRhs (P : Program) (ρ : Env) : Rhs → Result Val
  | .arg a => Result.ofOption (a.eval ρ)
  | .ctor c as =>
    match evalArgs ρ as with
    | some vs => if vs.length = c.arity then .ok (.ctor c vs) else .stuck
    | none => .stuck
  | .proj x c i =>
    match ρ.get? x with
    | some v =>
      match v.asCtor P.known with
      | some (c', fs) => if c' = c then Result.ofOption fs[i]? else .stuck
      | none => .stuck
    | none => .stuck
  | .prim op as =>
    match evalArgs ρ as with
    | some vs => primResult P op vs
    | none => .stuck
  | .call .. => .stuck

/-! ## Join points -/

/-- A join point on the stack: its definition-time environment, parameters
and body; `charged` inside its own body (recursive join points only). -/
structure JEntry where
  id : JoinId
  charged : Bool
  env : Env
  params : List Var
  body : Code
  isRec : Bool

/-- What a free jump may still run: the body size of an uncharged entry. -/
def JEntry.weight (e : JEntry) : Nat := if e.charged then 0 else e.body.size

def jweight : List JEntry → Nat
  | [] => 0
  | e :: J => e.weight + jweight J

/-- The entry of `j` and the stack below it. -/
def lookupJ (j : JoinId) : List JEntry → Option (JEntry × List JEntry)
  | [] => none
  | e :: J => if e.id = j then some (e, J) else lookupJ j J

theorem lookupJ_weight (j : JoinId) :
    ∀ {J : List JEntry} {e : JEntry} {rest : List JEntry},
      lookupJ j J = some (e, rest) → e.weight + jweight rest ≤ jweight J
  | [], _, _, h => by simp [lookupJ] at h
  | e' :: J, e, rest, h => by
    simp only [lookupJ] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [jweight]
    · have := lookupJ_weight j h
      simp only [jweight]
      omega

/-- The stack a jump to `e` runs its body with. -/
def JEntry.after (e : JEntry) (rest : List JEntry) : List JEntry :=
  if e.isRec then { e with charged := true } :: rest else rest

theorem JEntry.jweight_after (e : JEntry) (rest : List JEntry) :
    jweight (e.after rest) = jweight rest := by
  unfold JEntry.after
  split <;> simp [jweight, JEntry.weight]

/-! ## Evaluation -/

mutual

def eval (P : Program) (k : Nat) (ρ : Env) (J : List JEntry) (c : Code) : Result Val :=
  match c with
  | .bind x (.call f as) c' =>
    match evalArgs ρ as with
    | some vs =>
      match evalCall P k f vs with
      | .ok v => eval P k (ρ.insert x v) J c'
      | .timeout => .timeout
      | .resource r => .resource r
      | .trap => .trap
      | .stuck => .stuck
    | none => .stuck
  | .bind x r c' =>
    match evalRhs P ρ r with
    | .ok v => eval P k (ρ.insert x v) J c'
    | .timeout => .timeout
    | .resource r => .resource r
    | .trap => .trap
    | .stuck => .stuck
  | .jp j ps r b c' =>
    eval P k ρ ({ id := j, charged := false, env := ρ, params := ps, body := b, isRec := r } :: J) c'
  | .jmp j as =>
    match _h : lookupJ j J, evalArgs ρ as with
    | some (e, rest), some vs =>
      if vs.length = e.params.length then
        if _hc : e.charged then
          match k with
          | 0 => .timeout
          | k + 1 => eval P k (bindAll e.env e.params vs) (e.after rest) e.body
        else eval P k (bindAll e.env e.params vs) (e.after rest) e.body
      else .stuck
    | _, _ => .stuck
  | .case x alts d =>
    match ρ.get? x with
    | some v =>
      match v.asCtor P.known with
      | some (key, _) => evalAlts P k ρ J key alts d
      | none => .stuck
    | none => .stuck
  | .ret a => Result.ofOption (a.eval ρ)
  | .tcall f as =>
    match evalArgs ρ as with
    | some vs => evalCall P k f vs
    | none => .stuck
  | .trap => .trap
termination_by (k, c.size + jweight J)
decreasing_by
  all_goals simp_wf
  all_goals first
    | (apply Prod.Lex.left; omega)
    | (apply Prod.Lex.right
       have hw := lookupJ_weight j _h
       rw [JEntry.jweight_after]
       simp only [JEntry.weight, _hc, Bool.false_eq_true, ↓reduceIte] at hw
       simp only [Code.size]
       omega)
    | (apply Prod.Lex.right
       simp only [Code.size, jweight, JEntry.weight, Bool.false_eq_true, ↓reduceIte]
       omega)
    | (apply Prod.Lex.right
       simp only [Code.size]
       omega)

/-- The first alternative with key `key`, else the default, else stuck. -/
def evalAlts (P : Program) (k : Nat) (ρ : Env) (J : List JEntry) (key : Key.CtorKey)
    (alts : List Alt) (d : Option Code) : Result Val :=
  match alts with
  | [] =>
    match d with
    | some c => eval P k ρ J c
    | none => .stuck
  | .mk key' body :: rest =>
    if key' = key then eval P k ρ J body else evalAlts P k ρ J key rest d
termination_by (k, Code.altsSize alts + Code.optSize d + jweight J + 1)
decreasing_by
  all_goals simp_wf
  all_goals apply Prod.Lex.right
  all_goals simp only [Code.altsSize, Code.optSize]
  all_goals first
    | omega
    | (have := Code.size_pos body; omega)

/-- Enter function `f` (charged). -/
def evalCall (P : Program) (k : Nat) (f : FunId) (vs : List Val) : Result Val :=
  match P.fun? f with
  | some fd =>
    if vs.length = fd.params.length then
      match k with
      | 0 => .timeout
      | k + 1 => eval P k (bindAll .leaf (fd.params.map (·.1)) vs) [] fd.body
    else .stuck
  | none => .stuck
termination_by (k, 0)

end

/-- Run function `f` on argument values (the entry is charged). -/
def run (P : Program) (k : Nat) (f : FunId) (args : List Val) : Result Val :=
  evalCall P k f args

/-! ## Readback -/

mutual

/-- First-order values as shared observations: a `Nat` literal is a `Nat`,
a constructor its tag with its fields, a string its UTF-8 bytes; □ has
none. -/
def readback : Val → Option Obs
  | .lit (.nat n) => some (.nat n)
  | .lit (.str s) => some (.bytes s.toUTF8.toList)
  | .ctor c fs => if c.arity == fs.length then (readbackList fs).map (.ctor c.tag) else none
  | .erased => none

def readbackList : List Val → Option (List Obs)
  | [] => some []
  | v :: vs =>
    match readback v, readbackList vs with
    | some o, some os => some (o :: os)
    | _, _ => none

end

end IxCC.Fir
