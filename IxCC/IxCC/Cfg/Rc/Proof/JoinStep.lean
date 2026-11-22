import IxCC.Cfg.Rc.Proof.State

set_option autoImplicit false
namespace IxCC.Cfg.Rc
open Cfg.Proof (Impl spine)

/-- Declaring a join adds only saved lexical metadata, never RC tokens or a
target step. Its body gets the exact separate slot supply assigned by lowering. -/
theorem At.join {F : Fir.Program} {P : Program} {fr : Frame} {ρ : Own.Env}
    {saved : List Own.Plain.JEntry} {j : Fir.JoinId} {ps captured : List Fir.Var}
    {rec : Bool} {body k : Own.Plain.Code}
    (stateRel : At F P fr ρ saved (.jp j ps captured rec body k)) :
    At F P fr ρ
      ({ id := j, charged := false, env := ρ, params := ps, body, isRec := rec } :: saved) k := by
  obtain ⟨fd, scope, params, acc, next, first, lo, lookup, range, layout, cursor,
    env, below, scopedNames, joins⟩ := stateRel
  simp only [skeleton, Impl] at layout
  simp only [skeleton, spine] at cursor
  simp only [names, Bool.and_eq_true] at scopedNames
  refine ⟨fd, _, params, acc, next, first, lo, lookup, range, layout.1, cursor,
    env, below, scopedNames.2, ?_⟩
  apply Joins.cons
    (e := { id := j, charged := false, env := ρ, params := ps, body, isRec := rec })
    (bj := next + Cfg.Lower.count (skeleton P.base.size first k))
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
  · intro p hp
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
    exact paramBound_mem lo hx
  · exact scopedNames.1.2


end IxCC.Cfg.Rc
