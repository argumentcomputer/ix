import Compilatrix.Own.Plain.Proof.Prefixes
import Compilatrix.Own.Plain.Proof.Environment

/-! Canonical cleanup retains variables by lexical identity, while the heap
proof counts aliased values with multiplicity. Carried argument tokens survive
cleanup even when an old live variable points to the very same location. -/

set_option autoImplicit false

namespace Compilatrix.Own.Plain

open Rc
open Compilatrix.Sem (Result)

def retained (captured live : List Fir.Var) : List Fir.Var :=
  live.filter captured.contains

theorem envRoots_cons {ρ : Own.Env} {x : Fir.Var} {xs : List Fir.Var} {roots : List RVal}
    (h : EnvRoots ρ (x :: xs) roots) :
    ∃ v vs, ρ.get? x = some v ∧ EnvRoots ρ xs vs ∧ roots = v :: vs := by
  cases hx : ρ.get? x with
  | none => simp [EnvRoots, Own.evalArgs, Own.evalArg, hx] at h
  | some v =>
    cases ht : Own.evalArgs ρ (xs.map Fir.Arg.var) with
    | none => simp [EnvRoots, Own.evalArgs, Own.evalArg, hx, ht] at h
    | some vs =>
      exact ⟨v, vs, rfl, ht, by simpa [EnvRoots, Own.evalArgs, Own.evalArg, hx, ht] using h.symm⟩

theorem drops_sound (ρ : Own.Env) (H : Heap) (captured live : List Fir.Var)
    {external : Nat → Nat} {carry roots : List RVal}
    (hr : EnvRoots ρ live roots) (hb : Balance H external (carry ++ roots)) :
    ∃ H' kept, evalActions ρ H (drops captured live) = .ok H' ∧
      EnvRoots ρ (retained captured live) kept ∧ Balance H' external (carry ++ kept) ∧
      (∀ v, v ∈ kept → v ∈ roots) ∧
      (∀ v, v ∈ carry ++ kept → H.value? v = H'.value? v) ∧
      (∀ v, ExternalRoot external v → H.value? v = H'.value? v) := by
  induction live generalizing H carry roots with
  | nil =>
    have he : roots = [] := by simpa [EnvRoots, Own.evalArgs] using hr.symm
    subst roots
    exact ⟨H, [], rfl, rfl, hb, fun _ h => h, fun _ _ => rfl, fun _ _ => rfl⟩
  | cons x xs ih =>
    obtain ⟨v, vs, hx, ht, he⟩ := envRoots_cons hr
    subst roots
    cases hc : captured.contains x with
    | true =>
      have hmem : x ∈ captured := by simpa using hc
      have hb₀ : Balance H external ((carry ++ [v]) ++ vs) := by
        simpa [List.append_assoc] using hb
      obtain ⟨H', kept, hrun, hk, hb', hsub, hval, hext⟩ := ih H ht hb₀
      refine ⟨H', v :: kept, ?_, ?_, ?_, ?_, ?_, hext⟩
      · simpa [drops, hmem] using hrun
      · simp only [retained, List.filter_cons, hc, ↓reduceIte]
        change Own.evalArgs ρ ((x :: retained captured xs).map Fir.Arg.var) = some (v :: kept)
        simp [Own.evalArgs, Own.evalArg, hx, show Own.evalArgs ρ ((retained captured xs).map Fir.Arg.var) = some kept from hk]
      · simpa [List.append_assoc] using hb'
      · intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hsub w hw)
      · simpa [List.append_assoc] using hval
    | false =>
      have hmem : x ∉ captured := by simpa using hc
      obtain ⟨H₁, hstep, hb₁, hv₁, he₁⟩ := evalAction_dec_owned hx (balance_rotate hb)
      obtain ⟨H₂, kept, hrun, hk, hb₂, hsub, hv₂, he₂⟩ := ih H₁ ht hb₁
      refine ⟨H₂, kept, ?_, ?_, hb₂, ?_, ?_, ?_⟩
      · simp [drops, hmem, evalActions, hstep, Result.bind, hrun]
      · simpa only [retained, List.filter_cons, hc, Bool.false_eq_true, ↓reduceIte] using hk
      · intro w hw
        exact List.mem_cons_of_mem _ (hsub w hw)
      · intro w hw
        have hm : w ∈ carry ++ vs := by
          rcases List.mem_append.mp hw with hw | hw
          · exact List.mem_append_left _ hw
          · exact List.mem_append_right _ (hsub w hw)
        exact (hv₁ w hm).trans (hv₂ w hw)
      · intro w hw
        exact (he₁ w hw).trans (he₂ w hw)


end Compilatrix.Own.Plain
