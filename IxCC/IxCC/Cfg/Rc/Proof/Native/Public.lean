import IxCC.Cfg.Rc.Proof.Native.Indices

/-! Bind the public release entry to the actual accepted native program. This
module only exposes the existing executable assembly; it assumes no physical
simulation and does not alter admission or the release ABI. -/
set_option autoImplicit false
namespace IxCC.Cfg.Rc.Public.Spec
open Native.Spec

def assemble (original : Rt.Lowered) (l : Native.Layout) : Lowered :=
  { runtime := { original with program :=
      { original.program with funcs := original.program.funcs.push (dropWrapper l.decProc) } }
    drop := original.program.funcs.size }

theorem lower_parts {config : Rt.Config} {F : Fir.Program}
    {bodies : Src.NatMap Own.Plain.Code} {P : Program} {lowered : Lowered}
    (accepted : Public.lower config F bodies P = .ok lowered) :
    ∃ original, Native.lower config F bodies P = .ok original ∧
      lowered = assemble original (layoutOf P) ∧ lowered.runtime.program.check = .ok () := by
  change ((do
    let original ← Native.lower config F bodies P
    let result := assemble original (layoutOf P)
    result.runtime.program.check
    return result) : Except String Lowered) = .ok lowered at accepted
  cases hn : Native.lower config F bodies P with
  | error e => rw [hn] at accepted; cases accepted
  | ok original =>
    simp only [hn, bind, Except.bind] at accepted
    cases hc : (assemble original (layoutOf P)).runtime.program.check with
    | error e => rw [hc] at accepted; cases accepted
    | ok u =>
      cases u
      simp only [hc, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at accepted
      subst lowered
      exact ⟨original, rfl, rfl, hc⟩

theorem assemble_drop (original : Rt.Lowered) (l : Native.Layout) :
    (assemble original l).runtime.program.funcs[(assemble original l).drop]? =
      some (dropWrapper l.decProc) := by
  simp [assemble, Array.getElem?_push_size]

theorem assemble_existing (original : Rt.Lowered) (l : Native.Layout) {f : Nat}
    (hf : f < original.program.funcs.size) :
    (assemble original l).runtime.program.funcs[f]? = original.program.funcs[f]? := by
  simpa only [assemble, Array.getElem?_eq_getElem hf] using
    (Array.getElem?_push_lt (x := dropWrapper l.decProc) hf)

theorem accepted_drop {config : Rt.Config} {F : Fir.Program}
    {bodies : Src.NatMap Own.Plain.Code} {P : Program} {lowered : Lowered}
    (accepted : Public.lower config F bodies P = .ok lowered) :
    lowered.runtime.program.funcs[lowered.drop]? =
      some (dropWrapper (layoutOf P).decProc) := by
  obtain ⟨original, _, rfl, _⟩ := lower_parts accepted
  exact assemble_drop original (layoutOf P)





end IxCC.Cfg.Rc.Public.Spec
