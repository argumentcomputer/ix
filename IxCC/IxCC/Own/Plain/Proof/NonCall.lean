import IxCC.Own.Plain.Proof.Scalars
import IxCC.Fir.Proof.Unfold
import IxCC.Own.Plain.Proof.ResultCompose

/-! A source binding that calls nothing either is stuck or succeeds (`fir_rhs_pure`): the
pure outcomes the physical simulation over the typing context splits on. -/

set_option autoImplicit false

namespace IxCC.Own.Plain

open Rc
open IxCC.Sem (Result)

def PureOutcome {α : Type} (r : Result α) : Prop := r = .stuck ∨ ∃ v, r = .ok v

theorem ofOption_pure {α : Type} (o : Option α) : PureOutcome (Result.ofOption o) := by
  cases o <;> simp [PureOutcome, Result.ofOption]

/-- A scalar primitive (`op.isArr = false`; an array primitive may trap) is stuck or returns. -/
theorem fir_primitive_pure (F : Fir.Program) (op : Lam.Prim) (vs : List Fir.Val)
    (hp : op.isArr = false) :
    PureOutcome (Fir.primResult F op vs) := by
  have ha := Fir.arrResult_of_not_arr hp vs
  cases hn : Fir.natArgs vs with
  | none => simp [Fir.primResult, hn, ha, PureOutcome]
  | some ns =>
    cases hs : op.sem ns with
    | none => simp [Fir.primResult, hn, hs, ha, PureOutcome]
    | some result =>
      cases result with
      | nat n => simp [Fir.primResult, hn, hs, PureOutcome]
      | bool b => simpa only [Fir.primResult, hn, hs] using ofOption_pure (Fir.boolVal F b)

/-- A binding that calls nothing and is not an array primitive (`rhs.isArrPrim = false`, proved
by `rfl` for every other right-hand side form) is stuck or succeeds. -/
theorem fir_rhs_pure (F : Fir.Program) (ρ : Fir.Env) (rhs : Fir.Rhs)
    (hr : rhs.isArrPrim = false := by rfl) :
    PureOutcome (Fir.evalRhs F ρ rhs) := by
  cases rhs with
  | arg a => exact ofOption_pure (a.eval ρ)
  | ctor ctor args =>
    cases ha : Fir.evalArgs ρ args with
    | none => simp [Fir.evalRhs, ha, PureOutcome]
    | some vs =>
      by_cases hl : vs.length = ctor.arity
      · simp [Fir.evalRhs, ha, hl, PureOutcome]
      · simp [Fir.evalRhs, ha, hl, PureOutcome]
  | proj x key i =>
    cases hx : ρ.get? x with
    | none => simp [Fir.evalRhs, hx, PureOutcome]
    | some v =>
      cases hc : v.asCtor F.known with
      | none => simp [Fir.evalRhs, hx, hc, PureOutcome]
      | some pair =>
        obtain ⟨key', fields⟩ := pair
        by_cases hk : key' = key
        · simpa [Fir.evalRhs, hx, hc, hk] using ofOption_pure fields[i]?
        · simp [Fir.evalRhs, hx, hc, hk, PureOutcome]
  | prim op args =>
    cases ha : Fir.evalArgs ρ args with
    | none => simp [Fir.evalRhs, ha, PureOutcome]
    | some vs => simpa only [Fir.evalRhs, ha] using fir_primitive_pure F op vs hr
  | call f args => exact Or.inl rfl

end IxCC.Own.Plain
