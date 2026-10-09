import Compilatrix.Own.Rc.Proof.Shape
import Compilatrix.Own.Plain.Semantics
import Compilatrix.Src.Proof.NatMap

/-! Bounds for all environment locations, including obsolete lexical entries.
Heap growth preserves these bounds; allocation can therefore establish the
older-field invariant without assuming a source simulation. -/

set_option autoImplicit false
namespace Compilatrix.Own.Plain

def Bounded (n : Nat) : RVal → Prop
  | .loc l => l < n
  | _ => True

def ValuesBounded (n : Nat) (vs : List RVal) : Prop := ∀ v, v ∈ vs → Bounded n v
def EnvBounded (n : Nat) (ρ : Own.Env) : Prop := ∀ x v, ρ.get? x = some v → Bounded n v
def StackBounded (n : Nat) (J : List JEntry) : Prop := ∀ e, e ∈ J → EnvBounded n e.env

theorem Bounded.mono {n m : Nat} {v : RVal} (h : Bounded n v) (hn : n ≤ m) : Bounded m v := by
  cases v <;> simp_all [Bounded]; omega

theorem EnvBounded.mono {n m : Nat} {ρ : Own.Env} (h : EnvBounded n ρ) (hn : n ≤ m) :
    EnvBounded m ρ := fun x v hv => (h x v hv).mono hn

theorem StackBounded.mono {n m : Nat} {J : List JEntry} (h : StackBounded n J) (hn : n ≤ m) :
    StackBounded m J := fun e he => (h e he).mono hn

theorem envBounded_empty (n : Nat) : EnvBounded n .leaf := by intro x v h; cases h

theorem EnvBounded.insert {n : Nat} {ρ : Own.Env} (h : EnvBounded n ρ)
    (x : Fir.Var) {v : RVal} (hv : Bounded n v) : EnvBounded n (ρ.insert x v) := by
  intro y w hw
  rw [Src.NatMap.get?_insert] at hw
  split at hw
  · cases hw; exact hv
  · exact h y w hw

theorem EnvBounded.bindAll {n : Nat} {ρ : Own.Env} (h : EnvBounded n ρ)
    (params : List Fir.Var) {vs : List RVal} (hv : ValuesBounded n vs) :
    EnvBounded n (Own.bindAll ρ params vs) := by
  induction params generalizing ρ vs with
  | nil => exact h
  | cons x xs ih =>
    cases vs with
    | nil => exact h
    | cons v vs =>
      exact ih (h.insert x (hv v (by simp))) (fun w hw => hv w (by simp [hw]))

theorem EnvBounded.arg {n : Nat} {ρ : Own.Env} (h : EnvBounded n ρ)
    {a : Fir.Arg} {v : RVal} (ha : Own.evalArg ρ a = some v) : Bounded n v := by
  cases a with
  | var x => exact h x v ha
  | lit l => cases ha; trivial
  | erased => cases ha; trivial

theorem EnvBounded.args {n : Nat} {ρ : Own.Env} (h : EnvBounded n ρ)
    (args : List Fir.Arg) {vs : List RVal} (ha : Own.evalArgs ρ args = some vs) : ValuesBounded n vs := by
  induction args generalizing vs with
  | nil => cases ha; simp [ValuesBounded]
  | cons a args ih =>
    cases hv : Own.evalArg ρ a with
    | none => simp [Own.evalArgs, hv] at ha
    | some v =>
      cases hs : Own.evalArgs ρ args with
      | none => simp [Own.evalArgs, hv, hs] at ha
      | some values =>
        simp only [Own.evalArgs, hv, hs, Option.some.injEq] at ha
        subst vs
        intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · exact h.arg hv
        · exact ih hs w hw

theorem den_bounded {H : Heap} {v : RVal} {w : Fir.Val} (h : Proof.Den H v w) : Bounded H.size v := by
  cases v with
  | loc l =>
    obtain ⟨rc, mode, body, fields, hc, _, _⟩ := Proof.den_loc h
    exact Proof.cell?_some hc
  | _ => trivial

theorem dens_bounded {H : Heap} {vs : List RVal} {ws : List Fir.Val}
    (h : Sem.Forall2 (Proof.Den H) vs ws) : ValuesBounded H.size vs := by
  induction h with
  | nil => simp [ValuesBounded]
  | cons hd hs ih =>
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact den_bounded hd
    · exact ih v hv

theorem StackBounded.lookup {n : Nat} {J : List JEntry} (h : StackBounded n J)
    {j : Fir.JoinId} {e : JEntry} {rest : List JEntry} (hl : lookupJ j J = some (e, rest)) :
    EnvBounded n e.env ∧ StackBounded n rest := by
  induction J with
  | nil => simp [lookupJ] at hl
  | cons e₀ J ih =>
    by_cases he : e₀.id = j
    · have hh : e₀ = e ∧ J = rest := by simpa [lookupJ, he] using hl
      rcases hh with ⟨rfl, rfl⟩
      exact ⟨h e₀ (by simp), fun x hx => h x (by simp [hx])⟩
    · apply ih (fun x hx => h x (by simp [hx]))
      simpa [lookupJ, he] using hl

theorem StackBounded.after {n : Nat} {e : JEntry} {rest : List JEntry}
    (h : StackBounded n rest) (he : EnvBounded n e.env) : StackBounded n (e.after rest) := by
  intro x hx
  cases hr : e.isRec with
  | false => exact h x (by simpa [JEntry.after, hr] using hx)
  | true =>
    simp only [JEntry.after, hr, ↓reduceIte, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact he
    · exact h x hx

end Compilatrix.Own.Plain
