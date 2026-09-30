import Compilatrix.Ixon.Univ

/-! # Universe profiles and zero conditions

Level-exact relevance (D18; research note `relevance-checker.md` §4.1).
Whether a position is a proof depends only on which universe parameters of
its constant are zero: the *zero condition* of its type's sort. SrcEval
decides a condition at the concrete levels it carries (`PropWhen.holds`);
the relevance checker and erasure decide it at a *profile*, the list of which
parameters are zero (`PropWhen.holdsP`). `holds_profile` says the two agree,
and `inst_holds` says instantiating a callee's condition with the call's
universe arguments commutes with evaluating those arguments, so a closure
walked by profiles decides every position exactly as SrcEval does.

Everything here is structural recursion over lists and universes, so the
kernel can evaluate it (D17). -/

namespace Compilatrix.Src

open Compilatrix.Ixon

/-- Concrete universe instantiation. -/
abbrev Levels := List Nat

/-- Which universe parameters are zero (out-of-range parameters read as
zero, as `evalUniv` reads them). -/
abbrev Profile := List Bool

/-- Evaluate a universe at a concrete instantiation (out-of-range parameters
read as zero; well-formed programs have none). -/
def evalUniv (ls : Levels) : Univ → Nat
  | .zero => 0
  | .succ u => evalUniv ls u + 1
  | .max a b => Nat.max (evalUniv ls a) (evalUniv ls b)
  | .imax a b => let vb := evalUniv ls b; if vb == 0 then 0 else Nat.max (evalUniv ls a) vb
  | .var i => ls.getD i.toNat 0

/-- The profile of a concrete instantiation. -/
def profileOf (ls : Levels) : Profile := ls.map (· == 0)

/-- A zero condition: `never`, or exactly when every listed universe
parameter is zero (`allZero []` is always). Ix.Kernel's `PropWhen`. On a λ it
says when the λ is a proof (the β guard of rule A1); on any other position,
when the position is a proof. -/
inductive PropWhen where
  | never
  | allZero (params : List Nat)
  deriving BEq, DecidableEq, Repr, Inhabited, Hashable

namespace PropWhen

def always : PropWhen := .allZero []

/-- At a concrete instantiation. -/
def holds (ls : Levels) : PropWhen → Bool
  | .never => false
  | .allZero ps => ps.all fun p => ls.getD p 0 == 0

/-- At a profile. -/
def holdsP (prof : Profile) : PropWhen → Bool
  | .never => false
  | .allZero ps => ps.all fun p => prof.getD p true

/-- The λ's regime at an instantiation: `false` when it is a proof there. -/
def allowsBeta (ls : Levels) (c : PropWhen) : Bool := !c.holds ls

/-- Conjunction. -/
def and : PropWhen → PropWhen → PropWhen
  | .never, _ => .never
  | _, .never => .never
  | .allZero ps, .allZero qs => .allZero (ps ++ qs)

/-- The parameters a condition names. -/
def params : PropWhen → List Nat
  | .never => []
  | .allZero ps => ps

/-- Drop repeated parameters (the condition is unchanged). -/
def dedup : PropWhen → PropWhen
  | .never => .never
  | .allZero ps => .allZero ps.eraseDups

end PropWhen

/-- The zero condition of a universe: exact for every form, with no
normalisation (`zero` ↦ always, `succ` ↦ never, `max` ↦ both, `imax _ b` ↦
`b`, a parameter ↦ itself; Ix.Kernel's `zeroCondition`). -/
def zeroCond : Univ → PropWhen
  | .zero => .always
  | .succ _ => .never
  | .max a b => (zeroCond a).and (zeroCond b)
  | .imax _ b => zeroCond b
  | .var i => .allZero [i.toNat]

/-- A callee's condition over its own parameters, as a condition over the
caller's, given the call's universe arguments (out-of-range parameters read
as `zero`). -/
def PropWhen.inst (us : List Univ) : PropWhen → PropWhen
  | .never => .never
  | .allZero ps => ps.foldr (fun p c => (zeroCond (us.getD p .zero)).and c) .always

namespace Profile

/-- A callee's profile, given the call's universe arguments under the
caller's profile. -/
def inst (prof : Profile) (us : List Univ) : Profile :=
  us.map fun u => (zeroCond u).holdsP prof

/-- Exactly `n` entries (missing ones read as zero), so equal profiles of one
constant compare equal. -/
def normalize (prof : Profile) (n : Nat) : Profile :=
  (List.range n).map fun i => prof.getD i true

/-- `z` for a zero parameter, `s` for a nonzero one (diagnostics). -/
def render (prof : Profile) : String :=
  String.ofList (prof.map fun z => if z then 'z' else 's')

end Profile

/-! ## Exactness -/

private theorem getD_map {α β : Type} (f : α → β) (l : List α) (n : Nat) (d : α) :
    (l.map f).getD n (f d) = f (l.getD n d) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[n]? <;> rfl

theorem PropWhen.holds_profile (c : PropWhen) (ls : Levels) :
    c.holds ls = c.holdsP (profileOf ls) := by
  cases c with
  | never => rfl
  | allZero ps =>
    simp only [holds, holdsP, profileOf]
    congr 1
    funext p
    rw [show true = ((0 : Nat) == 0) from rfl, getD_map]

theorem PropWhen.and_holds (a b : PropWhen) (ls : Levels) :
    (a.and b).holds ls = (a.holds ls && b.holds ls) := by
  cases a <;> cases b <;> simp [and, holds, List.all_append]

theorem zeroCond_holds (ls : Levels) (u : Univ) :
    (zeroCond u).holds ls = (evalUniv ls u == 0) := by
  induction u with
  | zero => rfl
  | succ u _ => simp [zeroCond, PropWhen.holds, evalUniv]
  | max a b iha ihb =>
    rw [zeroCond, PropWhen.and_holds, iha, ihb]
    simp only [evalUniv]
    cases h : (evalUniv ls a == 0) <;> cases h' : (evalUniv ls b == 0) <;>
      simp_all [Nat.max_def] <;> split <;> omega
  | imax a b _ ihb =>
    rw [zeroCond, ihb]
    simp only [evalUniv]
    by_cases h : evalUniv ls b = 0
    · simp [h]
    · have hm : Nat.max (evalUniv ls a) (evalUniv ls b) ≠ 0 := by
        unfold Nat.max
        have := Nat.le_max_right (evalUniv ls a) (evalUniv ls b)
        omega
      rw [beq_false_of_ne h]
      simp only [Bool.false_eq_true, ite_false]
      rw [beq_false_of_ne hm]
  | var i => simp [zeroCond, PropWhen.holds, evalUniv]

theorem PropWhen.inst_holds (c : PropWhen) (us : List Univ) (ls : Levels) :
    (c.inst us).holds ls = c.holds (us.map (evalUniv ls)) := by
  cases c with
  | never => rfl
  | allZero ps =>
    induction ps with
    | nil => rfl
    | cons p ps ih =>
      simp only [inst, List.foldr_cons] at ih ⊢
      rw [and_holds, ih, zeroCond_holds]
      simp only [holds, List.all_cons]
      congr 1
      rw [show (0 : Nat) = evalUniv ls .zero from rfl, getD_map]

theorem Profile.inst_profileOf (us : List Univ) (ls : Levels) :
    (profileOf ls).inst us = profileOf (us.map (evalUniv ls)) := by
  simp only [inst, profileOf, List.map_map]
  congr 1
  funext u
  simp only [Function.comp_apply]
  rw [show List.map (fun x => x == 0) ls = profileOf ls from rfl, ← PropWhen.holds_profile,
    zeroCond_holds]

end Compilatrix.Src
