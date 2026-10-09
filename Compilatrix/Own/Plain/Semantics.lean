import Compilatrix.Own.Plain.Program
import Compilatrix.Own.Rc.Release
import Compilatrix.Own.Semantics

/-! Executable plain-RC semantics. The source clock/join discipline is the
existing Fir/Own discipline; inc and total dropAll stutter at that clock.
Plain.Proof.Candidate proves refinement for the actual checked body map.
-/

namespace Compilatrix.Own.Plain
open Compilatrix.Sem (Result)
open Compilatrix.Fir (Var FunId JoinId)

def Program.tables (P : Program) : Own.Tables :=
  { ctors := P.source.ctors, known := P.source.known }

mutual
def Code.size : Code → Nat
  | .act _ k | .bind _ _ k => k.size + 1
  | .jp _ _ _ _ b k => b.size + k.size + 1
  | .case _ alts d => Code.altsSize alts + Code.optSize d + 2
  | _ => 1
def Code.altsSize : List Alt → Nat
  | [] => 0
  | .mk _ b :: rest => b.size + Code.altsSize rest
def Code.optSize : Option Code → Nat
  | none => 0
  | some c => c.size
end

theorem Code.size_pos (c : Code) : 0 < c.size := by
  cases c <;> simp [Code.size]

def evalAction (ρ : Own.Env) (H : Own.Heap) : Action → Result Own.Heap
  | .inc x n =>
    match ρ.get? x with
    | some v => Result.ofOption (Rc.inc H v n)
    | none => .stuck
  | .dec x =>
    match ρ.get? x with
    | some v => Result.ofOption (Rc.dropAll H [v])
    | none => .stuck

def evalRhs (T : Own.Tables) (ρ : Own.Env) (H : Own.Heap) (r : Fir.Rhs) :
    Result (Own.RVal × Own.Heap) :=
  Own.evalRhs .rc T ρ H (match r with
    | .ctor c args => .alloc c args .shared
    | .proj x c i => .proj x c i
    | _ => .fir r)

structure JEntry where
  id : JoinId
  charged : Bool
  env : Own.Env
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

mutual
def eval (P : Program) (k : Nat) (ρ : Own.Env) (J : List JEntry) (H : Own.Heap)
    (c : Code) : Result (Own.RVal × Own.Heap) :=
  match c with
  | .act a c' =>
    match evalAction ρ H a with
    | .ok H' => eval P k ρ J H' c'
    | .timeout => .timeout
    | .resource r => .resource r
    | .trap => .trap
    | .stuck => .stuck
  | .bind x (.call f args) c' =>
    match Own.evalArgs ρ args with
    | some vs =>
      match evalCall P k f vs H with
      | .ok (v, H') => eval P k (ρ.insert x v) J H' c'
      | .timeout => .timeout
      | .resource r => .resource r
      | .trap => .trap
      | .stuck => .stuck
    | none => .stuck
  | .bind x r c' =>
    match evalRhs P.tables ρ H r with
    | .ok (v, H') => eval P k (ρ.insert x v) J H' c'
    | .timeout => .timeout
    | .resource r => .resource r
    | .trap => .trap
    | .stuck => .stuck
  | .jp j ps _ rec body c' =>
    eval P k ρ ({
      id := j, charged := false, env := ρ, params := ps,
      body, isRec := rec } :: J) H c'
  | .jmp j args =>
    match _h : lookupJ j J, Own.evalArgs ρ args with
    | some (e, rest), some vs =>
      if vs.length = e.params.length then
        if _hc : e.charged then
          match k with
          | 0 => .timeout
          | k + 1 => eval P k (Own.bindAll e.env e.params vs) (e.after rest) H e.body
        else eval P k (Own.bindAll e.env e.params vs) (e.after rest) H e.body
      else .stuck
    | _, _ => .stuck
  | .case x alts d =>
    match ρ.get? x with
    | some v =>
      match v.asCtor P.source.known H with
      | some (key, _) => evalAlts P k ρ J H key alts d
      | none => .stuck
    | none => .stuck
  | .ret a =>
    match Own.evalArg ρ a with
    | some v => .ok (v, H)
    | none => .stuck
  | .tcall f args =>
    match Own.evalArgs ρ args with
    | some vs => evalCall P k f vs H
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

def evalAlts (P : Program) (k : Nat) (ρ : Own.Env) (J : List JEntry) (H : Own.Heap)
    (key : Key.CtorKey) (alts : List Alt) (d : Option Code) : Result (Own.RVal × Own.Heap) :=
  match alts with
  | [] => match d with
    | some c => eval P k ρ J H c
    | none => .stuck
  | .mk key' body :: rest =>
    if key' = key then eval P k ρ J H body else evalAlts P k ρ J H key rest d
termination_by (k, Code.altsSize alts + Code.optSize d + jweight J + 1)
decreasing_by
  all_goals simp_wf
  all_goals apply Prod.Lex.right
  all_goals simp only [Code.altsSize, Code.optSize]
  all_goals first
    | omega
    | (have := Code.size_pos body; omega)

def evalCall (P : Program) (k : Nat) (f : FunId) (vs : List Own.RVal) (H : Own.Heap) :
    Result (Own.RVal × Own.Heap) :=
  match P.source.fun? f, P.bodies.get? f with
  | some fd, some body =>
    if vs.length = fd.params.length then
      match k with
      | 0 => .timeout
      | k + 1 => eval P k (Own.bindAll .leaf (fd.params.map (·.1)) vs) [] H body
    else .stuck
  | _, _ => .stuck
termination_by (k, 0)
end

def run (P : Program) (k : Nat) (f : FunId) (args : List Own.RVal) (H : Own.Heap := {}) :
    Result (Own.RVal × Own.Heap) := evalCall P k f args H

end Compilatrix.Own.Plain
