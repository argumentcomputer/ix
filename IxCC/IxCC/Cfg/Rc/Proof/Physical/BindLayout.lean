import IxCC.Cfg.Rc.Proof.Physical.Admission
import IxCC.Cfg.Rc.Proof.State

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native
open Spec
open Cfg.Proof (Impl spine)

/-- The checked lexical layout identifies the exact binding instruction and
its source continuation for the value produced by a physical operation. -/
theorem bind_layout {F : Fir.Program} {P : Program} {source : Cfg.Frame} {ρ : Own.Env}
    {saved : List Own.Plain.JEntry} {x : Fir.Var} {rhs : Fir.Rhs} {code : Own.Plain.Code}
    {rslots : Src.NatMap Own.RVal}
    (before : At F P source ρ saved (.bind x rhs code) rslots) (value : Own.RVal) :
    ∃ tail, source.rest = .bind x (Own.immRhs rhs) :: tail ∧
      At F P {source with rest := tail, env := source.env.insert x value}
        (ρ.insert x value) saved code rslots := by
  obtain ⟨fd, scope, params, acc, next, first, lo, slotBase, lookup, range, layout, cursor,
    sub, below, loSlot, slotSub, scopedNames, vb, rc, joins⟩ := before
  simp only [names, Bool.and_eq_true, decide_eq_true_eq] at scopedNames
  simp only [varsBelow, Bool.and_eq_true, decide_eq_true_eq] at vb
  change Impl fd.block? source.fn scope source.blk params (.bind x (Own.immRhs rhs) :: acc) next
    (skeleton P.base.size first code F.ctors slotBase) at layout
  change source.rest = .bind x (Own.immRhs rhs) :: spine (skeleton P.base.size first code F.ctors slotBase) at cursor
  refine ⟨_, cursor, fd, scope, params, .bind x (Own.immRhs rhs) :: acc, next, first, x+1, slotBase,
    lookup, range, layout, rfl, Cfg.Proof.Sub.insert sub x value, ?_, vb.1,
    slotSub.insert_var vb.1 value, scopedNames.2, vb.2, rc, ?_⟩
  · intro y actual found
    by_cases equal : y = x
    · subst y
      exact Nat.lt_succ_self x
    · rw [Src.NatMap.get?_insert_ne _ _ equal] at found
      exact Nat.lt_of_lt_of_le (below y actual found) (by omega)
  · apply (joins.agree ?_).mono (show lo ≤ x+1 by omega)
    intro y hy
    exact Src.NatMap.get?_insert_ne _ _ (by omega : y ≠ x)

theorem checked_binding_real
    {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
    {borrows : Own.Plain.BorrowSigs} {uniqs : Own.Plain.UniqSigs}
    (checked : checkScopedProgram F bodies P borrows uniqs = true)
    {source : Cfg.Frame} {ρ : Own.Env} {saved : List Own.Plain.JEntry}
    {x : Fir.Var} {rhs : Fir.Rhs} {code : Own.Plain.Code} {rslots : Src.NatMap Own.RVal}
    (before : At F P source ρ saved (.bind x rhs code) rslots)
    {sourceFunction : Fir.Fun} (sourceLookup : F.fun? source.fn = some sourceFunction)
    (unreserved : reserved P.base.size (.bind x (Own.immRhs rhs)) = false)
    (nonReuse : isReuseOp P.base.size (.bind x (Own.immRhs rhs)) = false) :
    x < funcFirst bodies source.fn sourceFunction := by
  obtain ⟨fd, scope, params, acc, next, first, lo, slotBase, lookup, range, layout, cursor,
    sub, below, loSlot, slotSub, scopedNames, vb, rc, joins⟩ := before
  obtain ⟨terminal, blockLookup⟩ := Cfg.Proof.impl_head layout
  have checkedFunction := checked_source_bounds checked range sourceLookup lookup
  have each := (functionBounds_block checkedFunction blockLookup).2.1
  have member : Cfg.Instr.bind x (Own.immRhs rhs) ∈
      acc.reverse ++ spine (skeleton P.base.size first (.bind x rhs code) F.ctors slotBase) := by
    simp [skeleton, spine]
  have bound := List.all_eq_true.mp each _ member
  simp only [instrBound, unreserved, nonReuse, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true,
    decide_eq_true_eq] at bound
  exact bound.1



end IxCC.Cfg.Rc.Native
