import IxCC.Cfg.Rc.Proof.State

set_option autoImplicit false
namespace IxCC.Cfg.Rc
open Cfg.Proof (Impl spine)

/-- Declaring a join adds only saved lexical metadata, never RC tokens or a
target step. Its body gets the exact separate slot supply assigned by lowering. -/
theorem At.join {F : Fir.Program} {P : Program} {fr : Frame} {ρ : Own.Env}
    {saved : List Own.Plain.JEntry} {j : Fir.JoinId} {ps captured : List Fir.Var}
    {rec : Bool} {body k : Own.Plain.Code} {slots : Src.NatMap Own.RVal}
    (stateRel : At F P fr ρ saved (.jp j ps captured rec body k) slots) :
    At F P fr ρ
      ({ id := j, charged := false, env := ρ, params := ps, body, isRec := rec } :: saved) k slots := by
  obtain ⟨fd, scope, params, acc, next, first, lo, slotBase, lookup, range, layout, cursor,
    env, below, loSlot, slotSub, scopedNames, vb, rc, joins⟩ := stateRel
  simp only [skeleton, Impl] at layout
  simp only [skeleton, spine] at cursor
  simp only [names, Bool.and_eq_true] at scopedNames
  simp only [varsBelow, Bool.and_eq_true] at vb
  simp only [reuseCtorsOk, Bool.and_eq_true] at rc
  refine ⟨fd, _, params, acc, next, first, lo, slotBase, lookup, range, layout.1, cursor,
    env, below, loSlot, slotSub, scopedNames.2, vb.2, rc.2, ?_⟩
  apply Joins.cons
    (e := { id := j, charged := false, env := ρ, params := ps, body, isRec := rec })
    (bj := next + Cfg.Lower.count (skeleton P.base.size first k F.ctors slotBase))
    (first := first + actionCount k) (loBody := paramBound lo ps)
    (ps := ps.map (·, Own.PSig.plain .tobj)) joins (Nat.le_refl lo)
  · simp [Function.comp_def]
  · intro h; cases h
  · exact layout.2
  · exact env
  · exact below
  · intro p hp
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
    exact of_decide_eq_true ((List.all_eq_true.mp scopedNames.1.1) x hx)
  · exact paramBound_base lo ps
  · exact paramBound_le loSlot (fun x hx => of_decide_eq_true ((List.all_eq_true.mp vb.1.1) x hx))
  · intro p hp
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
    exact paramBound_mem lo hx
  · exact scopedNames.1.2
  · exact vb.1.2
  · exact rc.1


end IxCC.Cfg.Rc
