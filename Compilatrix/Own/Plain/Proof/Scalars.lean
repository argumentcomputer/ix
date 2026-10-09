import Compilatrix.Own.Plain.Proof.Values
import Compilatrix.Own.Plain.Check
import Compilatrix.Own.Plain.Proof.Actions
import Compilatrix.Own.Plain.Proof.Unfold

/-! Immediate primitive results do not acquire heap references. This narrow
scratch interface uses exactly the fieldless Boolean-pin requirement of the
existing immortal proof, without importing that monolithic simulation. The
final composition must derive the requirement from the admitted source. -/

set_option autoImplicit false

namespace Compilatrix.Own.Plain

open Rc
open Compilatrix.Sem (Result)

theorem primResult_immediate {F : Fir.Program} {H : Heap}
    {op : Lam.Prim} {vs : List RVal} {ws : List Fir.Val} {w : Fir.Val}
    (hpins : BoolPinsOk F) (hargs : Sem.Forall2 (Proof.Den H) vs ws)
    (hresult : Fir.primResult F op ws = .ok w) :
    ∃ v, Own.primResult { ctors := F.ctors, known := F.known } op vs = .ok v ∧
      Proof.Den H v w ∧ ∀ l, v ≠ .loc l := by
  unfold Fir.primResult at hresult
  unfold Own.primResult
  rw [Values.natArgs_den hargs]
  cases hn : Fir.natArgs ws with
  | none => simp [hn] at hresult
  | some ns =>
    simp only [hn] at hresult ⊢
    cases hs : op.sem ns with
    | none => simp [hs] at hresult
    | some pr =>
      cases pr with
      | nat n =>
        simp only [hs, Result.ok.injEq] at hresult
        subst w
        exact ⟨.lit (.nat n), by simp [hs], Proof.den_lit H _, by intro l; simp⟩
      | bool b =>
        simp only [hs] at hresult ⊢
        cases hpin : (if b then F.known.boolTrue else F.known.boolFalse) with
        | none => simp [Fir.boolVal, hpin, Result.ofOption] at hresult
        | some key =>
          simp only [Fir.boolVal, hpin, Fir.Program.ctorInfo?] at hresult
          cases hi : Fir.CtorInfo.ofKey F.ctors key with
          | none => simp [hi, Result.ofOption] at hresult
          | some info =>
            have ha := hpins b key info hpin hi
            have hfieldless : info.fieldless = true := by
              simp [Fir.CtorInfo.fieldless, ha]
            simp only [hi, Option.map_some, Result.ofOption, Result.ok.injEq] at hresult
            subst w
            exact ⟨.ctor0 info, by simp [hpin, ctor0Of, hi, hfieldless, Result.ofOption],
              Proof.den_ctor0 H _, by intro l; simp⟩

theorem balance_immediate {H : Heap} {external : Nat → Nat}
    {roots : List RVal} {v : RVal}
    (hb : Balance H external roots) (hv : ∀ l, v ≠ .loc l) :
    Balance H external (v :: roots) := by
  intro l
  simpa [refsIn, hv l] using hb l

theorem primitive_owned (P : Program) (k : Nat) (ρ : Own.Env) (J : List JEntry)
    (H : Heap) (x : Fir.Var) (op : Lam.Prim) (args : List Fir.Arg) (c : Code)
    {external : Nat → Nat} {roots vs : List RVal} {ws : List Fir.Val} {w : Fir.Val}
    (hpins : BoolPinsOk P.source) (hb : Balance H external roots)
    (ha : Own.evalArgs ρ args = some vs) (hd : Sem.Forall2 (Proof.Den H) vs ws)
    (hr : Fir.primResult P.source op ws = .ok w) :
    ∃ v, eval P k ρ J H (.bind x (.prim op args) c) =
        eval P k (ρ.insert x v) J H c ∧
      Proof.Den H v w ∧ Balance H external (v :: roots) := by
  obtain ⟨v, hv, hden, himm⟩ := primResult_immediate hpins hd hr
  refine ⟨v, ?_, hden, balance_immediate hb himm⟩
  rw [eval_bindRhs P k ρ J H x (.prim op args) c (by intro f as h; cases h)]
  have he : evalRhs P.tables ρ H (.prim op args) = .ok (v, H) := by
    simp [evalRhs, Own.evalRhs, ha, Program.tables, hv, Result.map]
  rw [he, Result.bind_ok]


end Compilatrix.Own.Plain
