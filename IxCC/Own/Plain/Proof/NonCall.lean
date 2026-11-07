import IxCC.Own.Plain.Proof.CtorStep
import IxCC.Own.Plain.Proof.ResultCompose

/-! Lift the actual non-call ownership steps into the code induction. The
only continuation premise is the local induction hypothesis; the eventual
checked-program theorem discharges it by source-code/clock induction. -/

set_option autoImplicit false

namespace IxCC.Own.Plain

open Rc
open IxCC.Sem (Result)

def PureOutcome {α : Type} (r : Result α) : Prop := r = .stuck ∨ ∃ v, r = .ok v

theorem ofOption_pure {α : Type} (o : Option α) : PureOutcome (Result.ofOption o) := by
  cases o <;> simp [PureOutcome, Result.ofOption]

theorem fir_primitive_pure (F : Fir.Program) (op : Lam.Prim) (vs : List Fir.Val) :
    PureOutcome (Fir.primResult F op vs) := by
  cases hn : Fir.natArgs vs with
  | none => simp [Fir.primResult, hn, PureOutcome]
  | some ns =>
    cases hs : op.sem ns with
    | none => simp [Fir.primResult, hn, hs, PureOutcome]
    | some result =>
      cases result with
      | nat n => simp [Fir.primResult, hn, hs, PureOutcome]
      | bool b => simpa only [Fir.primResult, hn, hs] using ofOption_pure (Fir.boolVal F b)

theorem fir_rhs_pure (F : Fir.Program) (ρ : Fir.Env) (rhs : Fir.Rhs) :
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
    | some vs => simpa only [Fir.evalRhs, ha] using fir_primitive_pure F op vs
  | call f args => exact Or.inl rfl

theorem nonCall_refines {functions : Signatures} {H : Heap} {external : Nat → Nat}
    {live : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env} {roots : List RVal}
    {joins : Joins} {Jf : List Fir.JEntry} {Jo : List JEntry}
    (h : State functions H external live ρf ρo roots joins Jf Jo)
    (P : Program) (k : Nat) (x : Fir.Var) (rhs : Fir.Rhs) (body : Fir.Code)
    (hpins : BoolPinsOk P.source) (hx : x ∉ live)
    (hs : rhsIn functions live rhs = true) (hn : ∀ f args, rhs ≠ .call f args)
    (ih : ∀ w v H',
      State functions H' external (live ++ [x]) (ρf.insert x w) (ρo.insert x v)
        (roots ++ [v]) joins Jf Jo →
      ResultRel H' external (Fir.eval P.source k (ρf.insert x w) Jf body)
        (eval P k (ρo.insert x v) Jo H' (lowerCode (live ++ [x]) joins body))) :
    ResultRel H external (Fir.eval P.source k ρf Jf (.bind x rhs body))
      (eval P k ρo Jo H (lowerCode live joins (.bind x rhs body))) := by
  rcases fir_rhs_pure P.source ρf rhs with hstuck | ⟨w, hw⟩
  · rw [Fir.eval_bindRhs P.source k ρf Jf x rhs body hn, hstuck]
    exact .stuck
  · obtain ⟨v, H', hstep, hstate, hpreserve⟩ := nonCall_step h P k x rhs body hpins hx hs hn hw
    rw [Fir.eval_bindRhs P.source k ρf Jf x rhs body hn, hw, Result.bind_ok, hstep]
    exact (ih w v H' hstate).preheap (fun root value _ hd => hpreserve root value hd)


end IxCC.Own.Plain
