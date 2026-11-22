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
    (before : At F P source ρ saved (.bind x rhs code)) (value : Own.RVal) :
    ∃ tail, source.rest = .bind x (Own.immRhs rhs) :: tail ∧
      At F P {source with rest := tail, env := source.env.insert x value}
        (ρ.insert x value) saved code := by
  obtain ⟨fd, scope, params, acc, next, first, lo, lookup, range, layout, cursor,
    sub, below, scopedNames, joins⟩ := before
  simp only [names, Bool.and_eq_true, decide_eq_true_eq] at scopedNames
  change Impl fd.block? source.fn scope source.blk params (.bind x (Own.immRhs rhs) :: acc) next
    (skeleton P.base.size first code) at layout
  change source.rest = .bind x (Own.immRhs rhs) :: spine (skeleton P.base.size first code) at cursor
  refine ⟨_, cursor, fd, scope, params, .bind x (Own.immRhs rhs) :: acc, next, first, x+1,
    lookup, range, layout, rfl, Cfg.Proof.Sub.insert sub x value, ?_, scopedNames.2, ?_⟩
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
    (checked : checkScopedProgram F bodies P = true)
    {source : Cfg.Frame} {ρ : Own.Env} {saved : List Own.Plain.JEntry}
    {x : Fir.Var} {rhs : Fir.Rhs} {code : Own.Plain.Code}
    (before : At F P source ρ saved (.bind x rhs code))
    {sourceFunction : Fir.Fun} (sourceLookup : F.fun? source.fn = some sourceFunction)
    (unreserved : reserved P.base.size (.bind x (Own.immRhs rhs)) = false) : x < sourceFunction.vars := by
  obtain ⟨fd, scope, params, acc, next, first, lo, lookup, range, layout, cursor,
    sub, below, scopedNames, joins⟩ := before
  obtain ⟨terminal, blockLookup⟩ := Cfg.Proof.impl_head layout
  have checkedFunction := checked_source_bounds checked range sourceLookup lookup
  have each := (functionBounds_block checkedFunction blockLookup).2.1
  have member : Cfg.Instr.bind x (Own.immRhs rhs) ∈
      acc.reverse ++ spine (skeleton P.base.size first (.bind x rhs code)) := by
    simp [skeleton, spine]
  have bound := List.all_eq_true.mp each _ member
  simp only [instrBound, unreserved, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true,
    decide_eq_true_eq] at bound
  exact bound.1



end IxCC.Cfg.Rc.Native
