import IxCC.Cfg.Rc.Proof.Entry
import IxCC.Cfg.Rc.Proof.Reach

set_option autoImplicit false
namespace IxCC.Cfg.Rc
open IxCC.Sem (Result)

def SimAt (F : Fir.Program) (bodies : Src.NatMap Own.Plain.Code) (P : Program) (clock : Nat) : Prop :=
  ∀ fr ρ saved H code stk, At F P fr ρ saved code →
    Reach P clock (.run fr stk H) stk (Own.Plain.eval {source := F, bodies} clock ρ saved H code)

/-- The source call charge is matched by the actual checked target entry.
Only a strictly smaller-clock induction hypothesis is used. -/
theorem call_reach {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
    (checked : checkScopedProgram F bodies P = true) (clock : Nat)
    (ih : ∀ k < clock, SimAt F bodies P k) (f : Nat) (vs : List Own.RVal)
    (stk : List (Frame × Fir.Var)) (H : Own.Heap) :
    Reach P clock (.call f vs stk H) stk (Own.Plain.evalCall {source := F, bodies} clock f vs H) := by
  rw [Own.Plain.evalCall_eq]
  cases hf : F.fun? f with
  | none => simp only [Result.ofOption, Result.bind]; exact Reach.stuck
  | some fd =>
    simp only [Result.ofOption, Result.bind_ok]
    cases hb : bodies.get? f with
    | none => simp only [Result.ofOption, Result.bind]; exact Reach.stuck
    | some body =>
      simp only [Result.ofOption, Result.bind_ok, Own.Plain.callFun]
      by_cases arity : vs.length = fd.params.length
      · simp only [arity, ↓reduceIte]
        obtain ⟨fr, step, frame⟩ := checked_entry_step checked (checked_source_dense checked hf) hf hb vs arity stk H
        exact Reach.charge step (fun k smaller => ih k (by omega) _ _ _ _ _ _ frame)
      · simp only [arity, ↓reduceIte]
        exact Reach.stuck


end IxCC.Cfg.Rc
