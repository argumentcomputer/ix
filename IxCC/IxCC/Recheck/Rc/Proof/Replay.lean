import IxCC.Cfg.Rc.Proof.Language
import IxCC.Recheck.Rc.Replay
import IxCC.Recheck.Proof.Middle
import IxCC.Own.Plain.Proof.Certificate

/-! Compose the actual certificate-consuming front end with the abstract RC
Cfg machine. This deliberately retains the existing accepted stage-S source
boundary; physical memory/runtime/backend composition is still separate. -/
set_option autoImplicit false
namespace IxCC.Recheck.RcReplay

theorem runFront_spec {cfg : Config} {P : Src.Program} {c : Cert} {f : Front}
    (accepted : runFront cfg P c = .ok f) :
    Recheck.front cfg P c.base = .ok (f.src, f.checked) ∧
    (∃ st, Lam.erase f.src f.checked = .ok (f.lam, st)) ∧
    Recheck.anfOf c.base f.src f.lam = .ok f.anf ∧
    Fir.lower f.anf = .ok f.fir ∧
    Own.Plain.Certificate.admit f.fir c.own = .ok f.own ∧
    Cfg.Rc.generate f.fir f.own.bodies = some f.cfg ∧
    Cfg.Rc.checkScopedProgram f.fir f.own.bodies f.cfg = true := by
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
      cases hanf : Recheck.anfOf c.base src lam with
      | error e => rw [hanf] at accepted; cases accepted
      | ok anf =>
        simp only [hanf, bind, Except.bind] at accepted
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
                    exact ⟨rfl, ⟨st, herase⟩, hanf, hfir, hown, hgen, hscope⟩

/-- Every accepted RC certificate front end refines its actual stage-S source
through the abstract checked RC Cfg machine, on every covered input
(`Front.Covered`). No execution-agreement premise is supplied by a caller,
producer or certificate. -/
theorem source_refines_cfg {cfg : Config} {P : Src.Program} {c : Cert} {f : Front}
    (accepted : runFront cfg P c = .ok f) :
    Sem.RefinesOn (f.Covered c) (⟨f.src, f.checked⟩ : Lam.Erase.Proof.CheckedProgram) f.cfg := by
  obtain ⟨_, ⟨st, herase⟩, hanf, hfir, _, _, hscope⟩ := runFront_spec accepted
  exact Sem.RefinesOn.refines_trans (Lam.Erase.Proof.erase_refines herase)
    ((Recheck.anfOf_refines hanf).trans_refines
      (Cfg.Rc.checked_lower_refines hfir hscope))


/-- **The checker runs on a budgeted map.** The verifier runs the ownership checker three times on
the admitted map (`Certificate.admit`, the program gate `checkScopedProgram`, and `Public.lower`);
every run judges a map whose captured work (`Own.Plain.Certificate.capturedWork`: one per variable
a jump's target captures, one per captured entry at a declaration) is at most
`Anf.maxCapturedWork`, because `admit` refused any other before the checker first ran. -/
theorem runFront_budget {cfg : Config} {P : Src.Program} {c : Cert} {f : Front}
    (accepted : runFront cfg P c = .ok f) :
    Own.Plain.Certificate.capturedWork f.own.bodies ≤ Anf.maxCapturedWork :=
  Own.Plain.Certificate.admit_budget (runFront_spec accepted).2.2.2.2.1

/-- **The source-domain check runs on a bounded program.** Each of the three runs of the checker
starts with the source-domain check (`programDomain`), which walks every parameter of every
function and join point; the program they judge has at most `Anf.maxParamTotal` of them
(`Own.Plain.Certificate.paramTotal`), because `admit` refused any other first. -/
theorem runFront_paramTotal {cfg : Config} {P : Src.Program} {c : Cert} {f : Front}
    (accepted : runFront cfg P c = .ok f) :
    Own.Plain.Certificate.paramTotal f.fir ≤ Anf.maxParamTotal :=
  Own.Plain.Certificate.admit_paramTotal (runFront_spec accepted).2.2.2.2.1

end IxCC.Recheck.RcReplay
