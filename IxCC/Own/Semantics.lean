import IxCC.Own.Syntax
import IxCC.Own.Heap

/-! # Own semantics

The clocked big-step semantics of Own over the abstract heap (design note
03 §3.2), with the allocation policy as an argument (`AllocPol`, 03 §4.4).
It charges exactly where Fir does (03 C6): function entry, tail calls and
recursive jumps, with the same depth clock and the same join-point stack
discipline (`Fir.Semantics`), so an Own program and its erasure run in lock
step, `timeout` included.

* `alloc c args κ`: a field-less `c` gives `ctor0 c` and no cell (06 S4);
  otherwise a fresh cell `live 1 dyn` under `.rc` and `live 1 static` under
  `.immortal`. The kind is recorded and unused.
* `proj` and `case` read a live cell, a field-less constructor or a `Nat`
  literal as a constructor; a dead cell, □ or a closure-free mismatch is
  stuck (03 C5).
* `prim` is exact on `Nat`; Boolean results are the pinned field-less
  constructors. Own never returns `resource` (its heap is unbounded).

Never evaluated on the recheck path (D17). -/

namespace IxCC.Own

open IxCC.Sem (Result)
open IxCC.Fir (Var FunId JoinId Arg)

abbrev Env := Src.NatMap RVal

def evalArg (ρ : Env) : Arg → Option RVal
  | .var x => ρ.get? x
  | .lit l => some (.lit l)
  | .erased => some .erased

def evalArgs (ρ : Env) : List Arg → Option (List RVal)
  | [] => some []
  | a :: as =>
    match evalArg ρ a, evalArgs ρ as with
    | some v, some vs => some (v :: vs)
    | _, _ => none

def bindAll (ρ : Env) : List Var → List RVal → Env
  | x :: xs, v :: vs => bindAll (ρ.insert x v) xs vs
  | _, _ => ρ

def natArgs : List RVal → Option (List Nat)
  | [] => some []
  | .lit (.nat n) :: vs => (natArgs vs).map (n :: ·)
  | _ => none

def Program.tables (P : Program) : Tables := { ctors := P.ctors, known := P.known }

/-- A field-less constructor as an immediate. -/
def ctor0Of (T : Tables) (c : Key.CtorKey) : Option RVal :=
  match Fir.CtorInfo.ofKey T.ctors c with
  | some info => if info.fieldless then some (.ctor0 info) else none
  | none => none

def primResult (T : Tables) (p : Lam.Prim) (vs : List RVal) : Result RVal :=
  match natArgs vs with
  | some ns =>
    match p.sem ns with
    | some (.nat n) => .ok (.lit (.nat n))
    | some (.bool b) =>
      match (if b then T.known.boolTrue else T.known.boolFalse) with
      | some c => Result.ofOption (ctor0Of T c)
      | none => .stuck
    | none => .stuck
  | none => .stuck

/-- A right-hand side other than a call. -/
def evalRhs (pol : AllocPol) (T : Tables) (ρ : Env) (H : Heap) : Rhs → Result (RVal × Heap)
  | .fir (.arg a) =>
    match evalArg ρ a with
    | some v => .ok (v, H)
    | none => .stuck
  | .fir (.prim op as) =>
    match evalArgs ρ as with
    | some vs => (primResult T op vs).map (·, H)
    | none => .stuck
  | .fir _ => .stuck
  | .alloc c as _ =>
    match evalArgs ρ as with
    | some vs =>
      if vs.length = c.arity then
        if c.fieldless then .ok (.ctor0 c, H) else .ok (H.alloc pol { ctor := c, fields := vs })
      else .stuck
    | none => .stuck
  | .proj x c i =>
    match ρ.get? x with
    | some v =>
      match v.asCtor T.known H with
      | some (c', fs) => if c' = c then (Result.ofOption fs[i]?).map (·, H) else .stuck
      | none => .stuck
    | none => .stuck

/-! ## Join points (as in Fir) -/

structure JEntry where
  id : JoinId
  charged : Bool
  env : Env
  params : List Var
  body : Code
  isRec : Bool

def JEntry.weight (e : JEntry) : Nat := if e.charged then 0 else e.body.size

def jweight : List JEntry → Nat
  | [] => 0
  | e :: J => e.weight + jweight J

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

def JEntry.after (e : JEntry) (rest : List JEntry) : List JEntry :=
  if e.isRec then { e with charged := true } :: rest else rest

theorem JEntry.jweight_after (e : JEntry) (rest : List JEntry) :
    jweight (e.after rest) = jweight rest := by
  unfold JEntry.after
  split <;> simp [jweight, JEntry.weight]

/-! ## Evaluation -/

mutual

def eval (pol : AllocPol) (P : Program) (k : Nat) (ρ : Env) (J : List JEntry) (H : Heap)
    (c : Code) : Result (RVal × Heap) :=
  match c with
  | .bind x (.fir (.call f as)) c' =>
    match evalArgs ρ as with
    | some vs =>
      match evalCall pol P k f vs H with
      | .ok (v, H') => eval pol P k (ρ.insert x v) J H' c'
      | .timeout => .timeout
      | .resource r => .resource r
      | .trap => .trap
      | .stuck => .stuck
    | none => .stuck
  | .bind x r c' =>
    match evalRhs pol P.tables ρ H r with
    | .ok (v, H') => eval pol P k (ρ.insert x v) J H' c'
    | .timeout => .timeout
    | .resource r => .resource r
    | .trap => .trap
    | .stuck => .stuck
  | .jp j ps _ r b c' =>
    eval pol P k ρ ({ id := j, charged := false, env := ρ, params := ps.map (·.1), body := b
                      isRec := r } :: J) H c'
  | .jmp j as =>
    match _h : lookupJ j J, evalArgs ρ as with
    | some (e, rest), some vs =>
      if vs.length = e.params.length then
        if _hc : e.charged then
          match k with
          | 0 => .timeout
          | k + 1 => eval pol P k (bindAll e.env e.params vs) (e.after rest) H e.body
        else eval pol P k (bindAll e.env e.params vs) (e.after rest) H e.body
      else .stuck
    | _, _ => .stuck
  | .case x alts d =>
    match ρ.get? x with
    | some v =>
      match v.asCtor P.known H with
      | some (key, _) => evalAlts pol P k ρ J H key alts d
      | none => .stuck
    | none => .stuck
  | .ret a =>
    match evalArg ρ a with
    | some v => .ok (v, H)
    | none => .stuck
  | .tcall f as =>
    match evalArgs ρ as with
    | some vs => evalCall pol P k f vs H
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

def evalAlts (pol : AllocPol) (P : Program) (k : Nat) (ρ : Env) (J : List JEntry) (H : Heap)
    (key : Key.CtorKey) (alts : List Alt) (d : Option Code) : Result (RVal × Heap) :=
  match alts with
  | [] =>
    match d with
    | some c => eval pol P k ρ J H c
    | none => .stuck
  | .mk key' body :: rest =>
    if key' = key then eval pol P k ρ J H body else evalAlts pol P k ρ J H key rest d
termination_by (k, Code.altsSize alts + Code.optSize d + jweight J + 1)
decreasing_by
  all_goals simp_wf
  all_goals apply Prod.Lex.right
  all_goals simp only [Code.altsSize, Code.optSize]
  all_goals first
    | omega
    | (have := Code.size_pos body; omega)

def evalCall (pol : AllocPol) (P : Program) (k : Nat) (f : FunId) (vs : List RVal) (H : Heap) :
    Result (RVal × Heap) :=
  match P.fun? f with
  | some fd =>
    if vs.length = fd.params.length then
      match k with
      | 0 => .timeout
      | k + 1 => eval pol P k (bindAll .leaf fd.params vs) [] H fd.body
    else .stuck
  | none => .stuck
termination_by (k, 0)

end

/-- Run function `f` on argument values over heap `H` (the entry is
charged). -/
def run (pol : AllocPol) (P : Program) (k : Nat) (f : FunId) (args : List RVal) (H : Heap := {}) :
    Result (RVal × Heap) :=
  evalCall pol P k f args H

end IxCC.Own
