import IxCC.Recheck.Rc.Replay
import IxCC.Cfg.Rc.Proof.PublicApi
import IxCC.Recheck.Proof.Parts

set_option autoImplicit false
namespace IxCC.Recheck.RcReplay

theorem backTyped_parts {cfg : Config} {f : Front} {root : Ixon.Address} {c : Recheck.Cert} {xv : Xv.VProgram}
    {xl : Xv.LProgram} {stacked : Xv.Stacking.Stacked} {program : X86.Program} {exports : List (String × X86.BlockId)}
    (h : backTyped cfg f root c = .ok (xv, xl, stacked, program, exports)) :
    Xv.Select.select f.lowered.program = .ok xv ∧ Xv.Validate.run cfg.env xv c.alloc = .ok xl ∧
      Backend.lay xl ({ Recheck.backendConfig cfg f.lowered root c with reps := f.reps }) = .ok (stacked, program, exports) := by
  unfold backTyped at h
  simp only [bind, Except.bind, Except.mapError] at h
  cases hs : Xv.Select.select f.lowered.program with
  | error e => simp [hs] at h
  | ok xv' =>
    simp only [hs] at h
    cases hv : Xv.Validate.program cfg.env xv' c.alloc with
    | error e => simp [hv] at h
    | ok u =>
      simp only [hv] at h
      cases ha : Xv.Alloc.applyProgram xv' c.alloc with
      | error e => simp [ha] at h
      | ok xl' =>
        simp only [ha] at h
        cases hl : Backend.lay xl' ({ Recheck.backendConfig cfg f.lowered root c with reps := f.reps }) with
        | error e => simp [hl] at h
        | ok r =>
          obtain ⟨st, pr, ex⟩ := r
          simp only [hl, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
          refine ⟨rfl, ?_, hl⟩
          unfold Xv.Validate.run
          rw [hv]
          exact ha

/-- The provenance selected by the actual RC replay, retaining its Phase 3
policy when the user has not supplied an explicit note. -/
def finalConfig (cfg : Config) (f : Front) : Config :=
  { cfg with provenance := some (cfg.provenance.getD
    (.ixir1Policy ((f.src.roots.head?.map (·.1)).getD default) 3 1)) }

def emittedConfig (cfg : Config) (f : Front) (c : Recheck.Cert) : Backend.Config :=
  { Recheck.backendConfig (finalConfig cfg f) f.lowered
      ((f.src.roots.head?.map (·.1)).getD default) c with reps := f.reps }

/-- The replay path emits the exact selected and validated program, with its
additional raw-word drop representation and the actual certificate layouts. -/
theorem run_parts {cfg : Config} {P : Src.Program} {c : Cert} {a : Artifact}
    (accepted : run cfg P c = .ok a) :
    runFront cfg P c = .ok a.front ∧ ∃ xv : Xv.VProgram, ∃ xl : Xv.LProgram,
      Xv.Select.select a.front.lowered.program = .ok xv ∧
      Xv.Validate.run cfg.env xv c.base.alloc = .ok xl ∧
      Backend.emit xl (emittedConfig cfg a.front c.base) = .ok a.backend ∧
      Backend.SymbolsApart a.backend := by
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
          obtain ⟨selected, validated, laid⟩ := backTyped_parts hb
          refine ⟨rfl, xv, xl, selected, validated, ?_, ?_⟩
          · have checked : Backend.checkSymbols stacked.exports = .ok () := by
              unfold Recheck.checkSymbols at symbols
              unfold Backend.checkSymbols
              split at symbols
              · rename_i absent
                simp only [Recheck.sharedSymbol?] at absent
                rw [absent]
                rfl
              · cases symbols
            unfold Backend.emit emittedConfig
            simp only [bind, Except.bind]
            rw [laid]
            simp only [checked]
            exact finished
          · have apart := Recheck.checkSymbols_ok symbols
            have equality := Recheck.finish_stacked finished
            show (backend.stacked.exports.map (·.symbol)).Nodup
            rw [equality]
            exact apart

theorem emittedConfig_drop (cfg : Config) (f : Front) (c : Recheck.Cert) :
    (emittedConfig cfg f c).reps f.drop = some [.word] := by
  exact Cfg.Rc.Public.reps_drop ⟨f.lowered, f.drop⟩




end IxCC.Recheck.RcReplay
