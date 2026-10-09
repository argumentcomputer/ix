import Compilatrix.Cfg.Rc.Proof.State
import Compilatrix.Cfg.Rc.Proof.Reach
import Compilatrix.Cfg.Rc.Proof.Ordinary

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc
open Compilatrix.Sem (Result)
open Cfg.Proof (Impl ImplArms ImplOpt spine)
open Cfg.Lower (armEdges count countAlts)

theorem alts_reach (F : Fir.Program) (bodies : Src.NatMap Own.Plain.Code) (P : Program)
    (clock bound : Nat) (fr : Frame) (ρ : Own.Env) (saved : List Own.Plain.JEntry)
    (H : Own.Heap) (stk : List (Frame × Fir.Var)) (key : Key.CtorKey)
    (alts : List Own.Plain.Alt) (d : Option Own.Plain.Code) (next first : Nat)
    (fd : Cfg.Fun) (scope : Cfg.Lower.JScope) (lo : Nat)
    (lookup : P.base.fun? fr.fn = some fd) (range : fr.fn < F.size)
    (arms : ImplArms fd.block? fr.fn scope next (skeletonAlts P.base.size first alts))
    (opt : ImplOpt fd.block? fr.fn scope (next + countAlts (skeletonAlts P.base.size first alts))
      (skeletonOpt P.base.size (first + actionCountAlts alts) d))
    (armsNames : namesAlts lo alts = true) (optNames : namesOpt lo d = true)
    (env : EnvSub ρ fr.env) (below : Cfg.Proof.Below lo ρ)
    (joins : Joins P.base.size fd.block? fr.fn fr.env lo scope saved)
    (small : Own.Plain.Code.altsSize alts + Own.Plain.Code.optSize d < bound)
    (ih : ∀ (code : Own.Plain.Code), code.size < bound → ∀ after, At F P after ρ saved code →
      Reach P clock (.run after stk H) stk (Own.Plain.eval {source := F, bodies} clock ρ saved H code))
    (dispatch : step P (.run fr stk H) =
      match selectEdge key (armEdges next (skeletonAlts P.base.size first alts))
        (d.map fun _ => ({target := next + countAlts (skeletonAlts P.base.size first alts)} : Edge)) with
      | some e => takeEdge fd fr stk H e
      | none => .stuck) :
    Reach P clock (.run fr stk H) stk
      (Own.Plain.evalAlts {source := F, bodies} clock ρ saved H key alts d) := by
  match alts, d with
  | [], none => rw [Own.Plain.evalAlts_nil]; exact Reach.stuck
  | [], some code =>
    rw [Own.Plain.evalAlts_nil]
    simp only [skeletonAlts, countAlts, actionCountAlts, Nat.add_zero, skeletonOpt, ImplOpt] at opt
    have codeNames : names lo code = true := optNames
    obtain ⟨term, hb⟩ := Cfg.Proof.impl_head opt
    refine Reach.free ?_ (ih code (by
      simp only [Own.Plain.Code.altsSize, Own.Plain.Code.optSize] at small
      omega)
      {fr with blk := next, rest := spine (skeleton P.base.size first code)}
      ⟨fd, scope, [], [], next + 1, first, lo, lookup, range, opt, rfl, env, below, codeNames, joins⟩)
    rw [dispatch]
    simp only [skeletonAlts, armEdges, selectEdge, Option.map_some, countAlts, Nat.add_zero]
    rw [Cfg.Proof.takeEdge_eq (vs := []) hb rfl (by simp)]
    simp [Own.bindAll]
  | .mk key' code :: rest, d =>
    rw [Own.Plain.evalAlts_cons]
    simp only [skeletonAlts, ImplArms] at arms
    simp only [namesAlts, Bool.and_eq_true] at armsNames
    by_cases equal : key' = key
    · simp only [equal, ↓reduceIte]
      obtain ⟨term, hb⟩ := Cfg.Proof.impl_head arms.1
      have codeSmall : code.size < bound := by
        simp only [Own.Plain.Code.altsSize] at small
        omega
      refine Reach.free ?_ (ih code codeSmall
        {fr with blk := next, rest := spine (skeleton P.base.size first code)}
        ⟨fd, scope, [], [], next + 1, first, lo, lookup, range, arms.1, rfl,
          env, below, armsNames.1, joins⟩)
      rw [dispatch]
      simp only [skeletonAlts, armEdges, selectEdge, equal, ↓reduceIte]
      rw [Cfg.Proof.takeEdge_eq (vs := []) hb rfl (by simp)]
      simp [Own.bindAll]
    · simp only [equal, ↓reduceIte]
      have labels : next + countAlts (skeletonAlts P.base.size first (.mk key' code :: rest)) =
          next + 1 + count (skeleton P.base.size first code) +
            countAlts (skeletonAlts P.base.size (first + actionCount code) rest) := by
        simp only [skeletonAlts, countAlts]
        omega
      refine alts_reach F bodies P clock bound fr ρ saved H stk key rest d
        (next + 1 + count (skeleton P.base.size first code)) (first + actionCount code)
        fd scope lo lookup range arms.2 ?_ armsNames.2 optNames env below joins ?_ ih ?_
      · rw [← labels]
        simpa only [actionCountAlts, Nat.add_assoc] using opt
      · simp only [Own.Plain.Code.altsSize] at small
        omega
      · rw [dispatch, labels]
        simp only [skeletonAlts, armEdges, selectEdge, equal, ↓reduceIte]
termination_by alts.length

theorem case_reach {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
    (checked : checkScopedProgram F bodies P = true) (clock : Nat)
    {fr : Frame} {ρ : Own.Env} {saved : List Own.Plain.JEntry} {x : Fir.Var}
    {alts : List Own.Plain.Alt} {d : Option Own.Plain.Code}
    (stateRel : At F P fr ρ saved (.case x alts d)) (H : Own.Heap)
    (stk : List (Frame × Fir.Var))
    (ih : ∀ (code : Own.Plain.Code), code.size < (Own.Plain.Code.case x alts d).size →
      ∀ after, At F P after ρ saved code →
        Reach P clock (.run after stk H) stk (Own.Plain.eval {source := F, bodies} clock ρ saved H code)) :
    Reach P clock (.run fr stk H) stk
      (Own.Plain.eval {source := F, bodies} clock ρ saved H (.case x alts d)) := by
  obtain ⟨fd, scope, params, acc, next, first, lo, lookup, range, layout, cursor,
    env, below, scopedNames, joins⟩ := stateRel
  simp only [skeleton, Impl] at layout
  simp only [skeleton, spine] at cursor
  simp only [names, Bool.and_eq_true] at scopedNames
  rw [Own.Plain.eval_case]
  cases hx : ρ.get? x with
  | none => simp only [Sem.Result.ofOption, Sem.Result.bind]; exact Reach.stuck
  | some value =>
    simp only [Sem.Result.ofOption, Sem.Result.bind_ok]
    cases tag : value.asCtor F.known H with
    | none => exact Reach.stuck
    | some pair =>
      obtain ⟨key, fields⟩ := pair
      refine alts_reach F bodies P clock _ fr ρ saved H stk key alts d next first fd scope lo
        lookup range layout.2.1 layout.2.2 scopedNames.1 scopedNames.2 env below joins
        (by simp only [Own.Plain.Code.size]; omega) ih ?_
      simp only [step, cursor]
      rw [Cfg.Proof.step_run_term cursor lookup layout.1]
      simp only [Cfg.Proof.termStep, Cfg.Proof.caseTerm, env x value hx]
      have known : P.base.known = F.known :=
        congrArg Own.Tables.known (generate_tables (checkProgram_parts (checkScopedProgram_parts checked).1).2)
      rw [known, tag]
      cases d <;> rfl



end Compilatrix.Cfg.Rc
