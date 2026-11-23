import IxCC.Cfg.Rc.Proof.Physical.Admission
import IxCC.Cfg.Rc.Proof.Native.CallEntry
import IxCC.Cfg.Rc.Proof.CallStep

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native.Spec

/-- An ordinary checked source destination is below the original Fir bound,
even when the physical function also has reserved marker destinations. -/
theorem checked_bind_real {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
    {borrows : Own.Plain.BorrowSigs} {uniqs : Own.Plain.UniqSigs}
    (checked : checkScopedProgram F bodies P borrows uniqs = true)
    {source : Cfg.Frame} {ρ : Own.Env} {saved : List Own.Plain.JEntry}
    {x : Nat} {rhs : Fir.Rhs} {code : Own.Plain.Code} {rslots : Src.NatMap Own.RVal}
    (atBinding : At F P source ρ saved (.bind x rhs code) rslots)
    {sourceFunction : Fir.Fun} (sourceLookup : F.fun? source.fn = some sourceFunction)
    (ordinary : reserved P.base.size (.bind x (Own.immRhs rhs)) = false)
    (nonReuse : isReuseOp P.base.size (.bind x (Own.immRhs rhs)) = false) :
    x < funcFirst bodies source.fn sourceFunction := by
  obtain ⟨fd, scope, params, acc, next, supply, low, slotBase, lookup, range, layout, cursor,
    sub, bounded, loSlot, slotSub, names, vb, rc, joins⟩ := atBinding
  obtain ⟨terminal, blockLookup⟩ := Cfg.Proof.impl_head layout
  have member : .bind x (Own.immRhs rhs) ∈
      acc.reverse ++ Cfg.Proof.spine (skeleton P.base.size supply (.bind x rhs code) F.ctors slotBase) := by
    simp [skeleton, Cfg.Proof.spine]
  have accepted := List.all_eq_true.mp
    (functionBounds_block (checked_source_bounds checked range sourceLookup lookup) blockLookup).2.1
    (.bind x (Own.immRhs rhs)) member
  simp only [instrBound, ordinary, nonReuse, Bool.false_eq_true, ↓reduceIte,
    Bool.and_eq_true, decide_eq_true_eq] at accepted
  exact accepted.1


end IxCC.Cfg.Rc.Native.Spec
