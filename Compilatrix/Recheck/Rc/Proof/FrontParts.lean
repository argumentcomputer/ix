import Compilatrix.Recheck.Rc.Replay

set_option autoImplicit false
namespace Compilatrix.Recheck.RcReplay

/-- The public native lowering and parameter check executed by RC replay. -/
theorem runFront_native {cfg : Config} {P : Src.Program} {c : Cert} {f : Front}
    (accepted : runFront cfg P c = .ok f) :
    Recheck.checkParams cfg f.cfg.base (f.cfg.base.exports.zipIdx.map fun (g, i) => (i, g)) = .ok () ∧
    Cfg.Rc.Public.lower {names := cfg.names} f.fir f.own.bodies f.cfg =
      .ok ⟨f.lowered, f.drop⟩ := by
  unfold runFront at accepted
  cases hfront : Recheck.front cfg P c.base with
  | error e => rw [hfront] at accepted; cases accepted
  | ok sc =>
    obtain ⟨src, checked⟩ := sc
    rw [hfront] at accepted
    simp only [bind, Except.bind] at accepted
    cases herase : Lam.erase src checked with
    | error e => rw [herase] at accepted; cases accepted
    | ok ls =>
      obtain ⟨lam, st⟩ := ls
      simp only [herase, Except.mapError] at accepted
      cases hanf : Anf.Pipeline.run c.base.mid lam with
      | error e => rw [hanf] at accepted; cases accepted
      | ok anf =>
        simp only [hanf, Except.mapError, bind, Except.bind] at accepted
        cases hfir : Fir.lower anf with
        | error e => rw [hfir] at accepted; cases accepted
        | ok fir =>
          simp only [hfir, Except.mapError, bind, Except.bind] at accepted
          cases hown : Own.Plain.Certificate.admit fir c.own with
          | error e => rw [hown] at accepted; cases accepted
          | ok own =>
            simp only [hown, Except.mapError, bind, Except.bind] at accepted
            cases hgen : Cfg.Rc.generate fir own.bodies with
            | none => rw [hgen] at accepted; cases accepted
            | some candidate =>
              simp only [hgen] at accepted
              cases hscope : Cfg.Rc.checkScopedProgram fir own.bodies candidate with
              | false => simp [hscope] at accepted
              | true =>
                simp only [hscope, Bool.true_eq_false, ↓reduceIte, pure, Except.pure,
                  bind, Except.bind] at accepted
                cases hparams : Recheck.checkParams cfg candidate.base
                    (candidate.base.exports.zipIdx.map fun (f, i) => (i, f)) with
                | error e => rw [hparams] at accepted; cases accepted
                | ok unit =>
                  cases unit
                  simp only [hparams, bind, Except.bind] at accepted
                  cases hnative : Cfg.Rc.Public.lower { names := cfg.names }
                      fir own.bodies candidate with
                  | error e => rw [hnative] at accepted; cases accepted
                  | ok lowered =>
                    simp only [hnative, Except.mapError, bind, Except.bind,
                      pure, Except.pure, Except.ok.injEq] at accepted
                    subst accepted
                    exact ⟨hparams, hnative⟩


end Compilatrix.Recheck.RcReplay
