import IxCC.Cfg.Rc.Proof.State

set_option autoImplicit false
namespace IxCC.Cfg.Rc
open Cfg.Proof (spine)

/-- Construct the simulation invariant at a real checked function entry. All
function, body, block and name facts come from the executable gate. -/
theorem checked_entry_step {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
    (checked : checkScopedProgram F bodies P = true) {f : Nat} (range : f < F.size)
    {source : Fir.Fun} {body : Own.Plain.Code} (sourceLookup : F.fun? f = some source)
    (bodyLookup : bodies.get? f = some body) (vs : List Own.RVal)
    (arity : vs.length = source.params.length) (stk : List (Frame × Fir.Var)) (H : Own.Heap) :
    ∃ fr, step P (.call f vs stk H) = .next (.run fr stk H) true ∧
      At F P fr (Own.bindAll .leaf (source.params.map (·.1)) vs) [] body := by
  obtain ⟨fd, table, targetLookup, tableLookup, source', body', sourceLookup', bodyLookup',
    lowering, bounds, collected⟩ := checked_entry (checkScopedProgram_parts checked).1 range
  have hs : source' = source := Option.some.inj (sourceLookup'.symm.trans sourceLookup)
  have hc : body' = body := Option.some.inj (bodyLookup'.symm.trans bodyLookup)
  subst source'; subst body'
  subst fd
  let ownFd : Own.Fun := { Own.immFun source with
    body := skeleton F.size source.vars body
    vars := source.vars + actionCount body }
  obtain ⟨term, entry⟩ := Cfg.Proof.block_zero f ownFd
  have paramsEq : (ownFd.params.zip ownFd.sig.params).map (·.1) = ownFd.params :=
    Cfg.Proof.zip_fst (by simp [ownFd, Own.immFun])
  let fr : Frame := {
    fn := f
    blk := 0
    rest := spine ownFd.body
    env := Own.bindAll .leaf ownFd.params vs }
  have size := generate_size (checkProgram_parts (checkScopedProgram_parts checked).1).2
  obtain ⟨lo, paramsBound, scopedNames, _⟩ := checked_names checked range sourceLookup bodyLookup
  refine ⟨fr, ?_, ?_⟩
  · change Cfg.step .rc P.base (.call f vs stk H) = _
    have len : vs.length = (ownFd.params.zip ownFd.sig.params).length := by
      simp [ownFd, Own.immFun, arity]
    have actual := Cfg.Proof.step_call (pol := Own.AllocPol.rc) targetLookup entry len (stk := stk) (H := H)
    simpa only [paramsEq] using actual
  · refine ⟨_, [], ownFd.params.zip ownFd.sig.params, [], 1, source.vars, lo,
      targetLookup, range, ?_, ?_, ?_, ?_, scopedNames, .nil⟩
    · rw [size]
      exact Cfg.Proof.function_impl f ownFd
    · simp only [fr, ownFd, size]
    · exact fun _ _ h => h
    · exact Cfg.Proof.below_bindAll (Cfg.Proof.below_leaf lo) paramsBound vs


end IxCC.Cfg.Rc
