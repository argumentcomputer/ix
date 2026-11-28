import IxCC.Cfg.Rc.Proof.Physical.Bridge.ProjectionCursor

import IxCC.Cfg.Rc.Proof.Native.Activation

import IxCC.Cfg.Rc.Proof.Ordinary
import IxCC.Own.Plain.Proof.Projection
import IxCC.Own.Plain.Proof.Scalars

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Proof.Physical.Bridge.Scalar
open IxCC.Rt.Rc
open IxCC IxCC.Cfg.Rc IxCC.Cfg.Rc.Native
open IxCC.Cfg.Rc.Native.Spec IxCC.Rt.Rc.Procs

theorem source_projection {F : Fir.Program} {H : Own.Heap} {external : Nat → Nat}
    {live : List Fir.Var} {sourceEnv : Fir.Env} {ownedEnv : Own.Env} {roots : List Own.RVal}
    (denEnv : Own.Plain.EnvDen H live sourceEnv ownedEnv)
    (balance : Own.Rc.Balance H external roots)
    {y i : Nat} {key : Key.CtorKey} (member : y ∈ live) {logical : Fir.Val}
    (evaluation : Fir.evalRhs F sourceEnv (.proj y key i) = .ok logical) :
    ∃ value, Own.evalRhs .rc ({ctors := F.ctors, known := F.known} : Own.Tables)
      ownedEnv H (.proj y key i) = .ok (value, H) ∧
      Own.Proof.Den H value logical ∧ Own.Rc.CanDup H value ∧
      (∀ {imm : List Fir.Var}, Own.Plain.ImmEnv ownedEnv imm →
        imm.contains y = true → Own.Plain.ImmVal value) := by
  obtain ⟨parent, source, ho, hf, hd⟩ := denEnv y member
  simp only [Fir.evalRhs, hf] at evaluation
  cases hc : source.asCtor F.known with
  | none => simp [hc] at evaluation
  | some pair =>
    obtain ⟨key', fields⟩ := pair
    by_cases equal : key' = key
    · subst key'
      have index : fields[i]? = some logical := by
        cases hi : fields[i]? with
        | none => simp [hc, hi, Sem.Result.ofOption] at evaluation
        | some value =>
          have equal : value = logical := by simpa [hc, hi, Sem.Result.ofOption] using evaluation
          simpa [equal] using hi
      obtain ⟨values, view, fieldsDen⟩ := (Own.Plain.Values.asCtor_den F.known hd).1 key fields hc
      obtain ⟨value, field, den⟩ := fieldsDen.get' index
      refine ⟨value, ?_, den, Own.Plain.asCtor_field_canDup balance view (List.mem_of_getElem? field), ?_⟩
      · simp [Own.evalRhs, ho, view, field, Sem.Result.ofOption, Sem.Result.map]
      · intro imm himm hy_imm
        obtain ⟨parent', ho', hp_imm⟩ := himm y (List.contains_iff_mem.mp hy_imm)
        have hpeq : parent' = parent := Option.some.inj (ho'.symm.trans ho)
        subst parent'
        exact Own.Plain.asCtor_field_imm hp_imm view (List.mem_of_getElem? field)
    · simp [hc, equal] at evaluation

end IxCC.Cfg.Rc.Proof.Physical.Bridge.Scalar
