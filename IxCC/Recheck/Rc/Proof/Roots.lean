import IxCC.Recheck.Rc.Proof.Exports
import IxCC.Recheck.Rc.Proof.FrontLanguage

set_option autoImplicit false
namespace IxCC.Recheck.RcReplay

private theorem rootsOf_finalConfig (cfg : Config) (f : Front)
    (rows : List (Nat × (Ixon.Address × Src.CId) × Fir.FunId × (Lir.FunId × String))) :
    Recheck.rootsOf (finalConfig cfg f) f.src f.cfg.base f.lowered rows =
      Recheck.rootsOf cfg f.src f.cfg.base f.lowered rows := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    obtain ⟨i, ⟨address, constant⟩, fn, ⟨loweredFn, symbol⟩⟩ := row
    simp only [Recheck.rootsOf]
    rw [ih]
    rfl

/-- The artifact's actual declared root rows, independent of the backend's
selected provenance override. -/
theorem run_roots {cfg : Config} {P : Src.Program} {c : Cert} {a : Artifact}
    (accepted : run cfg P c = .ok a) :
    a.roots = Recheck.rootsOf cfg a.front.src a.front.cfg.base a.front.lowered
      ((List.range a.front.src.roots.length).zip
        (a.front.src.roots.zip (a.front.cfg.base.exports.zip a.front.lowered.roots))) := by
  unfold run at accepted
  cases hf : runFront cfg P c with
  | error error => rw [hf] at accepted; cases accepted
  | ok f =>
    rw [hf] at accepted
    simp only [bind, Except.bind] at accepted
    change (backTyped (finalConfig cfg f) f
      ((f.src.roots.head?.map (·.1)).getD default) c.base >>= _) = .ok a at accepted
    cases hb : backTyped (finalConfig cfg f) f
        ((f.src.roots.head?.map (·.1)).getD default) c.base with
    | error error =>
      rw [hb] at accepted
      cases accepted
    | ok tuple =>
      obtain ⟨xv, xl, stacked, program, exports⟩ := tuple
      rw [hb] at accepted
      simp only [bind, Except.bind] at accepted
      change ((do
        Recheck.checkSymbols stacked.exports
        let backend ← (Backend.finish xl.main stacked program exports
          ((finalConfig cfg f).provenance.getD (Recheck.defaultProvenance
            ((f.src.roots.head?.map (·.1)).getD default)))).mapError Err.ofBackend
        return { front := f, backend := backend, roots := (Recheck.rootsOf (finalConfig cfg f)
          f.src f.cfg.base f.lowered ((List.range f.src.roots.length).zip
            (f.src.roots.zip (f.cfg.base.exports.zip f.lowered.roots)))) }) : Except Err Artifact) = .ok a
        at accepted
      cases symbols : Recheck.checkSymbols stacked.exports with
      | error error => rw [symbols] at accepted; cases accepted
      | ok unit =>
        rw [symbols] at accepted
        simp only [bind, Except.bind] at accepted
        cases finished : Backend.finish xl.main stacked program exports
            ((finalConfig cfg f).provenance.getD (Recheck.defaultProvenance
              ((f.src.roots.head?.map (·.1)).getD default))) with
        | error error => rw [finished] at accepted; cases accepted
        | ok backend =>
          simp only [finished, Except.mapError, pure, Except.pure, Except.ok.injEq] at accepted
          subst a
          exact rootsOf_finalConfig cfg f _

theorem runFront_params {cfg : Config} {P : Src.Program} {c : Cert} {f : Front}
    (accepted : runFront cfg P c = .ok f) {index fn : Nat}
    (root : f.cfg.base.exports[index]? = some fn) :
    Recheck.cfgParams f.cfg.base fn ≤ Recheck.maxParams := by
  refine Recheck.checkParams_ok (runFront_native accepted).1 (index, fn)
    (List.mem_map.mpr ⟨(fn, index), ?_, rfl⟩)
  have lookup : f.cfg.base.exports.zipIdx[index]? = some (fn, index) := by
    simp [List.getElem?_zipIdx, root]
  exact List.mem_of_getElem? lookup

/-- The artifact's root list and the loaded language name the same physical
entry, parameter count and source-discovered readback type. -/
theorem roots_entry {cfg : Config} {P : Src.Program} {c : Cert} {a : Artifact}
    (accepted : run cfg P c = .ok a) (model : Rt.Model) {index : Nat} {root : Root}
    (entry : a.roots[index]? = some root) :
    (a.front.loaded model).entries[index]? =
      some {fn := root.fn, params := root.params, ty := root.ty} := by
  rw [run_roots accepted] at entry
  obtain ⟨j, address, constant, fx, fn, symbol, row, rootFn, rootParams, rootType⟩ :=
    Recheck.rootsOf_get entry
  simp only [List.getElem?_zip_eq_some] at row
  obtain ⟨_, source, exported, lowered⟩ := row
  have shape := public_roots (runFront_native (run_parts accepted).1).2
  have equal : fn = fx := by
    have same := congrArg (·[index]?) shape
    simp only [List.getElem?_map, lowered, exported, Option.map_some, Option.some.injEq] at same
    exact same
  subst fx
  simp only [Front.loaded, Rt.Loaded.ofLowered, Rt.entriesOf_get, lowered,
    Option.map_some, Option.some.injEq, Rt.Entry.mk.injEq]
  refine ⟨rootFn.symm, by rw [rootParams]; rfl, ?_⟩
  simp only [Front.tys, source, Option.bind_some, rootType]




end IxCC.Recheck.RcReplay
