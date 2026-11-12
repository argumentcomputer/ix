import IxCC.Recheck
import IxCC.Recheck.Proof.Compile
import IxCC.Recheck.Rc.Produce
import IxCC.Recheck.Rc.Proof.ObjectSound
import IxCC.Own.Plain.Proof.Language
import IxCC.Own.Plain.Proof.Certificate

/-! # End-to-End Compiler & Contract-Aware `Own.Plain` Soundness Bridge

Connects contract-aware `Own.Plain` verification (`checkContractPlainMap`,
`Program.checkWithContracts`, `Certificate.admitWithContracts`, and
`checked_contract_program_refines`) to:
1. Language-level simulation and refinement (`checked_contract_call_sim`,
   `checked_contract_refines_lang`, `checked_contract_lower_refines`,
   `checkedContractPass`, and `Recheck.Rc.contract_source_refines`);
2. Contract-aware `Recheck.run` / `Recheck.runWithContracts` and
   `Recheck.compile` / `Recheck.compileWithContracts` (`recheck_sound`,
   `recheck_contract_own_refines`, `compile_sound`,
   `compileWithContracts_sound`);
3. Automatic RC policy selection (`RcReplay.produceAuto` / `RcReplay.compileAuto`)
   across the `.zeroRc` and `.plainRc` paths and the immortal fallback taken when
   plain RC is selected but refused (`produceAuto_zeroRc_sound`,
   `produceAuto_plainRc_sound`, `produceAuto_immortal_sound`,
   `compileAuto_zeroRc_sound`, `compileAuto_plainRc_sound`,
   `compileAuto_immortal_sound`). -/

set_option autoImplicit false

namespace IxCC.Own.Plain

open IxCC.Sem (Result ClockMono Obs Lang Sim Forall2)

theorem checked_contract_call_sim {F : Fir.Program} {candidate : Src.NatMap Code}
    (checked : checkContractPlainMap F candidate = true) {f : Fir.FunId} (hf : f < F.size)
    (ns : List Nat) :
    Sim (fun w p => Proof.Den p.2 p.1 w) id
      (fun k => Fir.run F k f (Fir.litArgs ns))
      (fun k => run { source := F, bodies := candidate } k f (litArgs ns) {}) where
  forward k _ := ⟨k, (checked_contract_program_refines checked k hf (dens_lits {} ns)
    (balance_lits_empty ns)).refines⟩
  timeout k h := by
    have related := (checked_contract_program_refines checked k hf (dens_lits {} ns)
      (balance_lits_empty ns)).refines
    change Fir.evalCall F k f (Fir.litArgs ns) = .timeout at h
    rw [h] at related
    exact Result.Refines.timeout_iff.mp related

theorem checked_contract_refines_lang {F : Fir.Program} {candidate : Src.NatMap Code}
    (checked : checkContractPlainMap F candidate = true)
    (exports : ∀ f, f ∈ F.exports → f < F.size) :
    Sem.Refines F ({ source := F, bodies := candidate } : Program) := by
  refine Sem.Refines.of_sim (R := Lang.ObsEq) (fun _ _ h => h) fun i => ⟨id, ?_⟩
  obtain ⟨r, ns⟩ := i
  show Sim _ _ (Fir.firRun F (r, ns))
    (plainRun { source := F, bodies := candidate } (r, ns))
  unfold Fir.firRun plainRun
  simp only
  cases hr : F.exports[r]? with
  | none => exact { forward := fun _ _ => ⟨0, .stuck⟩, timeout := fun _ h => nomatch h }
  | some f =>
    simp only
    have hf := exports f (List.mem_of_getElem? hr)
    cases hfd : F.fun? f with
    | none => exact { forward := fun _ _ => ⟨0, .stuck⟩, timeout := fun _ h => nomatch h }
    | some fd =>
      simp only
      by_cases he : ns.length = fd.params.length
      · simp only [Sem.entryRun, he, ↓reduceIte]
        exact (checked_contract_call_sim checked hf ns).mono fun w p hd => by
          show Fir.obsV w = obsV p
          rw [obsV_den hd]
      · by_cases hlt : ns.length < fd.params.length
        · simp only [Sem.entryRun, he, hlt, ↓reduceIte]
          by_cases hn : ns = []
          · simp only [hn, ↓reduceIte]
            exact Sim.okConst (R := Lang.ObsEq (S := Fir.Program) (T := Program))
              (show Fir.obsV .erased = obsV (.erased, {}) by rw [obsV_erased]; rfl)
          · simp only [hn, ↓reduceIte]
            exact Sim.laterConst (R := Lang.ObsEq (S := Fir.Program) (T := Program))
              (show Fir.obsV .erased = obsV (.erased, {}) by rw [obsV_erased]; rfl) (fun k h => h)
        · simp only [Sem.entryRun, he, hlt, ↓reduceIte]
          exact Sim.bindStuck (checked_contract_call_sim checked hf (ns.take fd.params.length))
            fun _ _ _ => rfl

theorem checked_or_contract_refines_lang {F : Fir.Program} {candidate : Src.NatMap Code}
    (checked : (Program.check F candidate || Program.checkWithContracts F candidate) = true)
    (exports : ∀ f, f ∈ F.exports → f < F.size) :
    Sem.Refines F ({ source := F, bodies := candidate } : Program) :=
  checked_contract_refines_lang
    ((Program.check_or_checkWithContracts_iff F candidate).mp checked) exports

theorem checked_contract_lower_refines {A : Anf.Program} {F : Fir.Program}
    {candidate : Src.NatMap Code} (lowered : Fir.lower A = .ok F)
    (checked : checkContractPlainMap F candidate = true) :
    Sem.Refines A ({ source := F, bodies := candidate } : Program) :=
  (Fir.Proof.lower_refines lowered).trans
    (checked_contract_refines_lang checked (exports_of_lower lowered))

theorem Certificate.admitWithContracts_lower_refines {A : Anf.Program} {F : Fir.Program}
    {j : Lean.Json} {P : Program}
    (lowered : Fir.lower A = .ok F)
    (accepted : Certificate.admitWithContracts F j = .ok P) :
    Sem.Refines A P := by
  obtain ⟨hsrc, hcheck⟩ := Certificate.admitWithContracts_parts accepted
  have hp : ({ source := F, bodies := P.bodies } : Program) = P := by
    cases P
    simp only at hsrc
    subst hsrc
    rfl
  rw [← hp]
  exact checked_contract_lower_refines lowered hcheck

def checkedContractPass : Sem.Transform Fir.Program Program where
  name := "Own.Plain.checkWithContracts"
  Cert := Src.NatMap Code
  pre F := ∃ A, Fir.lower A = .ok F
  run F candidate := if Program.check F candidate || Program.checkWithContracts F candidate then
    .ok { source := F, bodies := candidate }
    else .error "own.plain: unsupported source or invalid ownership proposal"
  post P := (∃ A, Fir.lower A = .ok P.source) ∧
    checkContractPlainMap P.source P.bodies = true
  correct F candidate P admitted accepted := by
    obtain ⟨A, lowered⟩ := admitted
    split at accepted
    · next checked =>
      cases accepted
      have hc := (Program.check_or_checkWithContracts_iff F candidate).mp checked
      exact ⟨⟨⟨A, lowered⟩, hc⟩,
        checked_contract_refines_lang hc (exports_of_lower lowered)⟩
    · cases accepted

def lowerCheckedContractPass : Sem.Transform Anf.Program Program :=
  Fir.Proof.lowerPass.comp checkedContractPass (fun _ h => h)

end IxCC.Own.Plain

namespace IxCC.Recheck.Rc

/-- Contract-aware front-end runner accepting both unannotated (`Program.check`)
and contract-annotated (`Program.checkWithContracts`) `Own.Plain` proposals. -/
def runContractFront (cfg : Config) (P : Src.Program) (c : Cert)
    (candidate : Src.NatMap Own.Plain.Code) : Except Err Front := do
  let (src, checked) ← Recheck.front cfg P c
  let (lam, _) ← (Lam.erase src checked).mapError Err.ofErase
  let anf ← Recheck.anfOf c src lam
  let fir ← (Fir.lower anf).mapError Err.ofFir
  if Own.Plain.Program.check fir candidate || Own.Plain.Program.checkWithContracts fir candidate then
    pure { src, checked, lam, anf, fir, own := { source := fir, bodies := candidate } }
  else
    throw { stage := .cert, code := "own.plain", message := "unsupported source or invalid ownership proposal" }

theorem runContractFront_spec {cfg : Config} {P : Src.Program} {c : Cert}
    {candidate : Src.NatMap Own.Plain.Code} {f : Front}
    (accepted : runContractFront cfg P c candidate = .ok f) :
    Recheck.front cfg P c = .ok (f.src, f.checked) ∧
    (∃ st, Lam.erase f.src f.checked = .ok (f.lam, st)) ∧
    Recheck.anfOf c f.src f.lam = .ok f.anf ∧
    Fir.lower f.anf = .ok f.fir ∧
    f.own = ({ source := f.fir, bodies := candidate } : Own.Plain.Program) ∧
    Own.Plain.checkContractPlainMap f.fir candidate = true := by
  unfold runContractFront at accepted
  cases hfront : Recheck.front cfg P c with
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
      cases hanf : Recheck.anfOf c src lam with
      | error e => rw [hanf] at accepted; cases accepted
      | ok anf =>
        simp only [hanf] at accepted
        cases hfir : Fir.lower anf with
        | error e => rw [hfir] at accepted; cases accepted
        | ok fir =>
          simp only [hfir] at accepted
          split at accepted
          · next hcheck =>
            simp only [pure, Except.pure, Except.ok.injEq] at accepted
            subst accepted
            exact ⟨rfl, ⟨st, herase⟩, hanf, hfir, rfl,
              (Own.Plain.Program.check_or_checkWithContracts_iff fir candidate).mp hcheck⟩
          · cases accepted

theorem runFront_implies_runContractFront {cfg : Config} {P : Src.Program} {c : Cert}
    {candidate : Src.NatMap Own.Plain.Code} {f : Front}
    (accepted : runFront cfg P c candidate = .ok f) :
    runContractFront cfg P c candidate = .ok f := by
  obtain ⟨hfront, ⟨st, herase⟩, hanf, hfir, hown, hcheck⟩ := runFront_spec accepted
  unfold runContractFront
  rw [hfront]
  simp only [bind, Except.bind, herase, Except.mapError, hanf, hfir]
  have hor : (Own.Plain.Program.check f.fir candidate ||
      Own.Plain.Program.checkWithContracts f.fir candidate) = true :=
    Bool.or_eq_true_iff.mpr (.inl hcheck)
  simp only [hor, ↓reduceIte, pure, Except.pure, Except.ok.injEq]
  cases f
  simp only at hown
  subst hown
  rfl

theorem contract_source_refines {cfg : Config} {P : Src.Program} {c : Cert}
    {candidate : Src.NatMap Own.Plain.Code} {f : Front}
    (accepted : runContractFront cfg P c candidate = .ok f) :
    Sem.RefinesOn (Recheck.Covered c.mid f.src f.lam f.anf) (⟨f.src, f.checked⟩ : Lam.Erase.Proof.CheckedProgram)
      f.own := by
  obtain ⟨_, ⟨st, herase⟩, hanf, hfir, hown, hcheck⟩ := runContractFront_spec accepted
  rw [hown]
  exact Sem.RefinesOn.refines_trans (Lam.Erase.Proof.erase_refines herase)
    ((anfOf_refines hanf).trans_refines
      (Own.Plain.checked_contract_lower_refines hfir hcheck))

end IxCC.Recheck.Rc

namespace IxCC.Recheck

open IxCC.Sem (Obs Lang)
open IxCC.Lam.Erase.Proof (CheckedProgram)

theorem runWithContracts_parts {cfg : Config} {P : Src.Program} {c : Cert} {artifact : Artifact}
    (accepted : runWithContracts cfg P c = .ok artifact) :
    run cfg P c = .ok artifact ∧
      Own.Plain.checkContractPlainMap artifact.fir (Own.Plain.Program.canonical artifact.fir).bodies = true := by
  unfold runWithContracts at accepted
  cases hrun : run cfg P c with
  | error e => rw [hrun] at accepted; cases accepted
  | ok a =>
    rw [hrun] at accepted
    simp only [bind, Except.bind] at accepted
    split at accepted
    · next hown =>
      simp only [pure, Except.pure, Except.ok.injEq] at accepted
      subst accepted
      exact ⟨rfl, (Artifact.checkContractOwn_iff a).mp hown⟩
    · cases accepted

theorem compileInputWithContracts_parts {cfg : Config} {inp : Input} {cert : Cert} {artifact : Artifact}
    (accepted : compileInputWithContracts cfg inp = .ok (cert, artifact)) :
    produce (cfg.forInput inp) inp = .ok cert ∧
      runWithContracts (cfg.forInput inp) inp.program cert = .ok artifact := by
  unfold compileInputWithContracts at accepted
  simp only [bind, Except.bind] at accepted
  cases produced : produce (cfg.forInput inp) inp with
  | error e => simp [produced] at accepted
  | ok c =>
    simp only [produced] at accepted
    cases replayed : runWithContracts (cfg.forInput inp) inp.program c with
    | error e => simp [replayed] at accepted
    | ok a =>
      simp only [replayed, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at accepted
      obtain ⟨rfl, rfl⟩ := accepted
      exact ⟨rfl, replayed⟩

theorem compileWithContracts_parts {cfg : Config} {bytes : ByteArray} {equations : Lean.Json}
    {roots : List String} {cert : Cert} {artifact : Artifact}
    (accepted : compileWithContracts cfg bytes equations roots = .ok (cert, artifact)) :
    ∃ inp, ingress bytes equations roots = .ok inp ∧
      produce (cfg.forInput inp) inp = .ok cert ∧
      runWithContracts (cfg.forInput inp) inp.program cert = .ok artifact := by
  unfold compileWithContracts at accepted
  simp only [bind, Except.bind] at accepted
  cases ingested : ingress bytes equations roots with
  | error e => simp [ingested] at accepted
  | ok inp =>
    simp only [ingested] at accepted
    exact ⟨inp, rfl, compileInputWithContracts_parts accepted⟩

/-- When a rechecked artifact passes `Artifact.checkContractOwn`, its canonical
`Own.Plain.Program` refines the checked source `(⟨artifact.src, artifact.checked⟩)`
via `checked_contract_program_refines`. -/
theorem recheck_contract_own_refines {cfg : Config} {P : Src.Program} {cert : Cert} {artifact : Artifact}
    (accepted : run cfg P cert = .ok artifact)
    (hown : artifact.checkContractOwn = true) :
    Sem.RefinesOn (artifact.front.Covered cert) (⟨artifact.src, artifact.checked⟩ : CheckedProgram)
      (Own.Plain.Program.canonical artifact.fir) := by
  obtain ⟨hlir, _⟩ := run_parts accepted
  obtain ⟨_, ⟨st, herase⟩, hanf, hfir, _, _, _, _⟩ := runLir_spec hlir
  have hcheck := (Artifact.checkContractOwn_iff artifact).mp hown
  exact Sem.RefinesOn.refines_trans (Lam.Erase.Proof.erase_refines herase)
    ((anfOf_refines hanf).trans_refines
      (Own.Plain.checked_contract_lower_refines hfir hcheck))

/-- End-to-end soundness of `Recheck.run` (`recheck_sound`). -/
theorem recheck_sound {cfg : Config} {P : Src.Program} {cert : Cert} {artifact : Artifact}
    (accepted : run cfg P cert = .ok artifact)
    (driver : X86.Driver) (valid : driver.Ok artifact.backend.encoded.text.size)
    (input : Nat × List Nat) (hi : artifact.front.Covered cert input) :
    (∀ clock output, Lang.run (artifact.linked driver) input clock = .ok output →
      (∃ sourceClock value, Lang.run (⟨artifact.src, artifact.checked⟩ : CheckedProgram) input sourceClock = .ok value ∧
        artifact.front.view input.1 (Lang.obs value) = some output) ∨ artifact.front.GoesWrong input) ∧
    (¬ artifact.front.GoesWrong input → ∀ clock, ¬ (Lang.run (artifact.linked driver) input clock).GoesWrong) ∧
    ((∀ clock, Lang.run (⟨artifact.src, artifact.checked⟩ : CheckedProgram) input clock = .timeout) →
      (∀ clock, Lang.run (artifact.linked driver) input clock = .timeout) ∨
        ∃ clock failure, Lang.run (artifact.linked driver) input clock = .resource failure) :=
  sound accepted driver valid input hi

/-- End-to-end soundness of `Recheck.runWithContracts`, combining canonical
contract-aware `Own.Plain` refinement with linked x86 object soundness. -/
theorem recheckWithContracts_sound {cfg : Config} {P : Src.Program} {cert : Cert} {artifact : Artifact}
    (accepted : runWithContracts cfg P cert = .ok artifact)
    (driver : X86.Driver) (valid : driver.Ok artifact.backend.encoded.text.size)
    (input : Nat × List Nat) (hi : artifact.front.Covered cert input) :
    Sem.RefinesOn (artifact.front.Covered cert) (⟨artifact.src, artifact.checked⟩ : CheckedProgram)
      (Own.Plain.Program.canonical artifact.fir) ∧
    Sem.RefinesOn (artifact.front.Covered cert) artifact.front.source (artifact.linked driver) ∧
    ((∀ clock output, Lang.run (artifact.linked driver) input clock = .ok output →
      (∃ sourceClock value, Lang.run (⟨artifact.src, artifact.checked⟩ : CheckedProgram) input sourceClock = .ok value ∧
        artifact.front.view input.1 (Lang.obs value) = some output) ∨ artifact.front.GoesWrong input) ∧
    (¬ artifact.front.GoesWrong input → ∀ clock, ¬ (Lang.run (artifact.linked driver) input clock).GoesWrong) ∧
    ((∀ clock, Lang.run (⟨artifact.src, artifact.checked⟩ : CheckedProgram) input clock = .timeout) →
      (∀ clock, Lang.run (artifact.linked driver) input clock = .timeout) ∨
        ∃ clock failure, Lang.run (artifact.linked driver) input clock = .resource failure)) := by
  obtain ⟨hrun, hcheck⟩ := runWithContracts_parts accepted
  have hown : artifact.checkContractOwn = true :=
    (Artifact.checkContractOwn_iff artifact).mpr hcheck
  exact ⟨recheck_contract_own_refines hrun hown,
    object_refines hrun driver valid,
    sound hrun driver valid input hi⟩

/-- End-to-end soundness of `Recheck.compileWithContracts`. -/
theorem compileWithContracts_sound {cfg : Config} {bytes : ByteArray} {equations : Lean.Json}
    {roots : List String} {cert : Cert} {artifact : Artifact}
    (accepted : compileWithContracts cfg bytes equations roots = .ok (cert, artifact))
    (driver : X86.Driver) (valid : driver.Ok artifact.backend.encoded.text.size)
    (input : Nat × List Nat) (hi : artifact.front.Covered cert input) :
    Sem.RefinesOn (artifact.front.Covered cert) (⟨artifact.src, artifact.checked⟩ : CheckedProgram)
      (Own.Plain.Program.canonical artifact.fir) ∧
    Sem.RefinesOn (artifact.front.Covered cert) artifact.front.source (artifact.linked driver) ∧
    ((∀ clock output, Lang.run (artifact.linked driver) input clock = .ok output →
      (∃ sourceClock value, Lang.run (⟨artifact.src, artifact.checked⟩ : CheckedProgram) input sourceClock = .ok value ∧
        artifact.front.view input.1 (Lang.obs value) = some output) ∨ artifact.front.GoesWrong input) ∧
    (¬ artifact.front.GoesWrong input → ∀ clock, ¬ (Lang.run (artifact.linked driver) input clock).GoesWrong) ∧
    ((∀ clock, Lang.run (⟨artifact.src, artifact.checked⟩ : CheckedProgram) input clock = .timeout) →
      (∀ clock, Lang.run (artifact.linked driver) input clock = .timeout) ∨
        ∃ clock failure, Lang.run (artifact.linked driver) input clock = .resource failure)) := by
  obtain ⟨inp, _, _, replayed⟩ := compileWithContracts_parts accepted
  exact recheckWithContracts_sound replayed driver valid input hi

end IxCC.Recheck

namespace IxCC.Compiler

open IxCC.Sem (Obs Lang)
open IxCC.Lam.Erase.Proof (CheckedProgram)

/-- End-to-end soundness of `Recheck.run` (`Compiler.recheck_sound`). -/
theorem recheck_sound {cfg : Recheck.Config} {P : Src.Program} {cert : Recheck.Cert}
    {artifact : Recheck.Artifact}
    (accepted : Recheck.run cfg P cert = .ok artifact)
    (driver : X86.Driver) (valid : driver.Ok artifact.backend.encoded.text.size)
    (input : Nat × List Nat) (hi : artifact.front.Covered cert input) :
    (∀ clock output, Lang.run (artifact.linked driver) input clock = .ok output →
      (∃ sourceClock value, Lang.run (⟨artifact.src, artifact.checked⟩ : CheckedProgram) input sourceClock = .ok value ∧
        artifact.front.view input.1 (Lang.obs value) = some output) ∨ artifact.front.GoesWrong input) ∧
    (¬ artifact.front.GoesWrong input → ∀ clock, ¬ (Lang.run (artifact.linked driver) input clock).GoesWrong) ∧
    ((∀ clock, Lang.run (⟨artifact.src, artifact.checked⟩ : CheckedProgram) input clock = .timeout) →
      (∀ clock, Lang.run (artifact.linked driver) input clock = .timeout) ∨
        ∃ clock failure, Lang.run (artifact.linked driver) input clock = .resource failure) :=
  Recheck.recheck_sound accepted driver valid input hi

/-- End-to-end soundness of `Recheck.compileInput` (`Compiler.compileInput_sound`). -/
theorem compileInput_sound {cfg : Recheck.Config} {inp : Recheck.Input}
    {cert : Recheck.Cert} {artifact : Recheck.Artifact}
    (accepted : Recheck.compileInput cfg inp = .ok (cert, artifact))
    (driver : X86.Driver) (valid : driver.Ok artifact.backend.encoded.text.size)
    (input : Nat × List Nat) (hi : artifact.front.Covered cert input) :
    (∀ clock output, Lang.run (artifact.linked driver) input clock = .ok output →
      (∃ sourceClock value, Lang.run (⟨artifact.src, artifact.checked⟩ : CheckedProgram) input sourceClock = .ok value ∧
        artifact.front.view input.1 (Lang.obs value) = some output) ∨ artifact.front.GoesWrong input) ∧
    (¬ artifact.front.GoesWrong input → ∀ clock, ¬ (Lang.run (artifact.linked driver) input clock).GoesWrong) ∧
    ((∀ clock, Lang.run (⟨artifact.src, artifact.checked⟩ : CheckedProgram) input clock = .timeout) →
      (∀ clock, Lang.run (artifact.linked driver) input clock = .timeout) ∨
        ∃ clock failure, Lang.run (artifact.linked driver) input clock = .resource failure) :=
  Recheck.sound (Recheck.compileInput_parts accepted).2 driver valid input hi

/-- End-to-end soundness of byte-input `Recheck.compile` (`Compiler.compile_sound`). -/
theorem compile_sound {cfg : Recheck.Config} {bytes : ByteArray} {equations : Lean.Json}
    {roots : List String} {cert : Recheck.Cert} {artifact : Recheck.Artifact}
    (accepted : Recheck.compile cfg bytes equations roots = .ok (cert, artifact))
    (driver : X86.Driver) (valid : driver.Ok artifact.backend.encoded.text.size)
    (input : Nat × List Nat) (hi : artifact.front.Covered cert input) :
    (∀ clock output, Lang.run (artifact.linked driver) input clock = .ok output →
      (∃ sourceClock value, Lang.run (⟨artifact.src, artifact.checked⟩ : CheckedProgram) input sourceClock = .ok value ∧
        artifact.front.view input.1 (Lang.obs value) = some output) ∨ artifact.front.GoesWrong input) ∧
    (¬ artifact.front.GoesWrong input → ∀ clock, ¬ (Lang.run (artifact.linked driver) input clock).GoesWrong) ∧
    ((∀ clock, Lang.run (⟨artifact.src, artifact.checked⟩ : CheckedProgram) input clock = .timeout) →
      (∀ clock, Lang.run (artifact.linked driver) input clock = .timeout) ∨
        ∃ clock failure, Lang.run (artifact.linked driver) input clock = .resource failure) :=
  Recheck.compiled_sound accepted driver valid input hi

/-- What `RcReplay.produceImmortal` computed: the zero-RC certificate and its
`Recheck.run`. -/
theorem produceImmortal_parts {cfg : Recheck.Config} {inp : Recheck.Input}
    {front : Recheck.RcReplay.ProducedFir} {p : Recheck.Produced} {a : Recheck.Artifact}
    (h : Recheck.RcReplay.produceImmortal cfg inp front = .ok (p, a)) :
    Recheck.RcReplay.finishZeroRcCert cfg front = .ok p ∧ Recheck.run cfg inp.program p.cert = .ok a := by
  unfold Recheck.RcReplay.produceImmortal at h
  simp only [bind, Except.bind] at h
  cases hf : Recheck.RcReplay.finishZeroRcCert cfg front with
  | error e => simp [hf] at h
  | ok p' =>
    simp only [hf] at h
    cases hr : Recheck.run cfg inp.program p'.cert with
    | error e => simp [hr] at h
    | ok a' =>
      simp only [hr, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, hr⟩

/-- What `RcReplay.producePlain` computed: the plain-RC certificate and its
`RcReplay.run`. -/
theorem producePlain_parts {cfg : Recheck.Config} {inp : Recheck.Input}
    {front : Recheck.RcReplay.ProducedFir} {p : Recheck.RcReplay.Produced}
    {a : Recheck.RcReplay.Artifact}
    (h : Recheck.RcReplay.producePlain cfg inp front = .ok (p, a)) :
    Recheck.RcReplay.finishPlainRcCert cfg front = .ok p ∧
      Recheck.RcReplay.run cfg inp.program p.cert = .ok a := by
  unfold Recheck.RcReplay.producePlain at h
  simp only [bind, Except.bind] at h
  cases hf : Recheck.RcReplay.finishPlainRcCert cfg front with
  | error e => simp [hf] at h
  | ok p' =>
    simp only [hf] at h
    cases hr : Recheck.RcReplay.run cfg inp.program p'.cert with
    | error e => simp [hr] at h
    | ok a' =>
      simp only [hr, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, hr⟩

/-- Decomposition of `RcReplay.produceAuto` when it selects `.zeroRc` (including
contract-annotated zero-RC programs). -/
theorem produceAuto_zeroRc_parts {cfg : Recheck.Config} {inp : Recheck.Input}
    {cert : Recheck.Cert} {artifact : Recheck.Artifact} {alloc : List Xv.Alloc.Outcome}
    (accepted : Recheck.RcReplay.produceAuto cfg inp = .ok (.zeroRc cert artifact alloc)) :
    ∃ front p,
      Recheck.RcReplay.produceFir (cfg.forInput inp) inp = .ok front ∧
      Own.Plain.selectRcPolicyForSrc front.src front.fir = .zeroRc ∧
      Recheck.RcReplay.finishZeroRcCert (cfg.forInput inp) front = .ok p ∧
      p.cert = cert ∧ p.alloc = alloc ∧
      Recheck.run (cfg.forInput inp) inp.program cert = .ok artifact := by
  unfold Recheck.RcReplay.produceAuto at accepted
  simp only [bind, Except.bind] at accepted
  cases hfront : Recheck.RcReplay.produceFir (cfg.forInput inp) inp with
  | error e => simp [hfront] at accepted
  | ok front =>
    simp only [hfront] at accepted
    cases hpol : Own.Plain.selectRcPolicyForSrc front.src front.fir with
    | zeroRc =>
      simp only [hpol] at accepted
      cases hi : Recheck.RcReplay.produceImmortal (cfg.forInput inp) inp front with
      | error e => simp [hi] at accepted
      | ok r =>
        obtain ⟨p, a⟩ := r
        simp only [hi, pure, Except.pure, Except.ok.injEq,
          Recheck.RcReplay.AutoCompiled.zeroRc.injEq] at accepted
        obtain ⟨rfl, rfl, rfl⟩ := accepted
        obtain ⟨hfin, hrun⟩ := produceImmortal_parts hi
        exact ⟨front, p, rfl, hpol, hfin, rfl, rfl, hrun⟩
    | plainRc =>
      simp only [hpol] at accepted
      cases hpl : Recheck.RcReplay.producePlain (cfg.forInput inp) inp front with
      | ok r =>
        obtain ⟨p, a⟩ := r
        simp [hpl, pure, Except.pure] at accepted
      | error reason =>
        simp only [hpl] at accepted
        cases hi : Recheck.RcReplay.produceImmortal (cfg.forInput inp) inp front with
        | error e => simp [hi] at accepted
        | ok r =>
          obtain ⟨p, a⟩ := r
          simp [hi, pure, Except.pure] at accepted

/-- Decomposition of `RcReplay.produceAuto` when it selects `.plainRc`. -/
theorem produceAuto_plainRc_parts {cfg : Recheck.Config} {inp : Recheck.Input}
    {cert : Recheck.RcReplay.Cert} {artifact : Recheck.RcReplay.Artifact}
    {alloc : List Xv.Alloc.Outcome}
    (accepted : Recheck.RcReplay.produceAuto cfg inp = .ok (.plainRc cert artifact alloc)) :
    ∃ front p,
      Recheck.RcReplay.produceFir (cfg.forInput inp) inp = .ok front ∧
      Own.Plain.selectRcPolicyForSrc front.src front.fir = .plainRc ∧
      Recheck.RcReplay.finishPlainRcCert (cfg.forInput inp) front = .ok p ∧
      p.cert = cert ∧ p.alloc = alloc ∧
      Recheck.RcReplay.run (cfg.forInput inp) inp.program cert = .ok artifact := by
  unfold Recheck.RcReplay.produceAuto at accepted
  simp only [bind, Except.bind] at accepted
  cases hfront : Recheck.RcReplay.produceFir (cfg.forInput inp) inp with
  | error e => simp [hfront] at accepted
  | ok front =>
    simp only [hfront] at accepted
    cases hpol : Own.Plain.selectRcPolicyForSrc front.src front.fir with
    | zeroRc =>
      simp only [hpol] at accepted
      cases hi : Recheck.RcReplay.produceImmortal (cfg.forInput inp) inp front with
      | error e => simp [hi] at accepted
      | ok r =>
        obtain ⟨p, a⟩ := r
        simp [hi, pure, Except.pure] at accepted
    | plainRc =>
      simp only [hpol] at accepted
      cases hpl : Recheck.RcReplay.producePlain (cfg.forInput inp) inp front with
      | ok r =>
        obtain ⟨p, a⟩ := r
        simp only [hpl, pure, Except.pure, Except.ok.injEq,
          Recheck.RcReplay.AutoCompiled.plainRc.injEq] at accepted
        obtain ⟨rfl, rfl, rfl⟩ := accepted
        obtain ⟨hfin, hrun⟩ := producePlain_parts hpl
        exact ⟨front, p, rfl, hpol, hfin, rfl, rfl, hrun⟩
      | error reason =>
        simp only [hpl] at accepted
        cases hi : Recheck.RcReplay.produceImmortal (cfg.forInput inp) inp front with
        | error e => simp [hi] at accepted
        | ok r =>
          obtain ⟨p, a⟩ := r
          simp [hi, pure, Except.pure] at accepted

/-- Decomposition of `RcReplay.produceAuto` when it falls back to the immortal
policy: plain RC was selected, its certificate or replay was refused with
`reason`, and the zero-RC certificate was rechecked by `Recheck.run`. -/
theorem produceAuto_immortal_parts {cfg : Recheck.Config} {inp : Recheck.Input}
    {cert : Recheck.Cert} {artifact : Recheck.Artifact} {alloc : List Xv.Alloc.Outcome}
    {reason : Recheck.Err}
    (accepted : Recheck.RcReplay.produceAuto cfg inp = .ok (.immortal cert artifact alloc reason)) :
    ∃ front p,
      Recheck.RcReplay.produceFir (cfg.forInput inp) inp = .ok front ∧
      Own.Plain.selectRcPolicyForSrc front.src front.fir = .plainRc ∧
      Recheck.RcReplay.producePlain (cfg.forInput inp) inp front = .error reason ∧
      Recheck.RcReplay.finishZeroRcCert (cfg.forInput inp) front = .ok p ∧
      p.cert = cert ∧ p.alloc = alloc ∧
      Recheck.run (cfg.forInput inp) inp.program cert = .ok artifact := by
  unfold Recheck.RcReplay.produceAuto at accepted
  simp only [bind, Except.bind] at accepted
  cases hfront : Recheck.RcReplay.produceFir (cfg.forInput inp) inp with
  | error e => simp [hfront] at accepted
  | ok front =>
    simp only [hfront] at accepted
    cases hpol : Own.Plain.selectRcPolicyForSrc front.src front.fir with
    | zeroRc =>
      simp only [hpol] at accepted
      cases hi : Recheck.RcReplay.produceImmortal (cfg.forInput inp) inp front with
      | error e => simp [hi] at accepted
      | ok r =>
        obtain ⟨p, a⟩ := r
        simp [hi, pure, Except.pure] at accepted
    | plainRc =>
      simp only [hpol] at accepted
      cases hpl : Recheck.RcReplay.producePlain (cfg.forInput inp) inp front with
      | ok r =>
        obtain ⟨p, a⟩ := r
        simp [hpl, pure, Except.pure] at accepted
      | error reason' =>
        simp only [hpl] at accepted
        cases hi : Recheck.RcReplay.produceImmortal (cfg.forInput inp) inp front with
        | error e => simp [hi] at accepted
        | ok r =>
          obtain ⟨p, a⟩ := r
          simp only [hi, pure, Except.pure, Except.ok.injEq,
            Recheck.RcReplay.AutoCompiled.immortal.injEq] at accepted
          obtain ⟨rfl, rfl, rfl, rfl⟩ := accepted
          obtain ⟨hfin, hrun⟩ := produceImmortal_parts hi
          exact ⟨front, p, rfl, hpol, hpl, hfin, rfl, rfl, hrun⟩

/-- End-to-end soundness of `RcReplay.produceAuto` on the `.zeroRc` path
(covering both scalar closures and contract-annotated zero-RC heap closures). -/
theorem produceAuto_zeroRc_sound {cfg : Recheck.Config} {inp : Recheck.Input}
    {cert : Recheck.Cert} {artifact : Recheck.Artifact} {alloc : List Xv.Alloc.Outcome}
    (accepted : Recheck.RcReplay.produceAuto cfg inp = .ok (.zeroRc cert artifact alloc))
    (driver : X86.Driver) (valid : driver.Ok artifact.backend.encoded.text.size)
    (input : Nat × List Nat) (hi : artifact.front.Covered cert input) :
    (∀ clock output, Lang.run (artifact.linked driver) input clock = .ok output →
      (∃ sourceClock value, Lang.run (⟨artifact.src, artifact.checked⟩ : CheckedProgram) input sourceClock = .ok value ∧
        artifact.front.view input.1 (Lang.obs value) = some output) ∨ artifact.front.GoesWrong input) ∧
    (¬ artifact.front.GoesWrong input → ∀ clock, ¬ (Lang.run (artifact.linked driver) input clock).GoesWrong) ∧
    ((∀ clock, Lang.run (⟨artifact.src, artifact.checked⟩ : CheckedProgram) input clock = .timeout) →
      (∀ clock, Lang.run (artifact.linked driver) input clock = .timeout) ∨
        ∃ clock failure, Lang.run (artifact.linked driver) input clock = .resource failure) := by
  obtain ⟨_, _, _, _, _, _, _, hrun⟩ := produceAuto_zeroRc_parts accepted
  exact Recheck.sound hrun driver valid input hi

/-- End-to-end soundness of `RcReplay.produceAuto` on the `.plainRc` path. -/
theorem produceAuto_plainRc_sound {cfg : Recheck.Config} {inp : Recheck.Input}
    {cert : Recheck.RcReplay.Cert} {artifact : Recheck.RcReplay.Artifact}
    {alloc : List Xv.Alloc.Outcome}
    (accepted : Recheck.RcReplay.produceAuto cfg inp = .ok (.plainRc cert artifact alloc))
    (driver : X86.Driver) (valid : driver.Ok artifact.backend.encoded.text.size)
    (input : Nat × List Nat) (hi : artifact.front.Covered cert input) :
    (∀ clock output, Lang.run (artifact.linked driver) input clock = .ok output →
      (∃ sourceClock value,
        Lang.run (⟨artifact.front.src, artifact.front.checked⟩ : CheckedProgram)
          input sourceClock = .ok value ∧
        artifact.front.view input.1 (Lang.obs value) = some output) ∨ artifact.front.GoesWrong input) ∧
    (¬ artifact.front.GoesWrong input →
      ∀ clock, ¬ (Lang.run (artifact.linked driver) input clock).GoesWrong) ∧
    ((∀ clock, Lang.run (⟨artifact.front.src, artifact.front.checked⟩ : CheckedProgram)
        input clock = .timeout) →
      (∀ clock, Lang.run (artifact.linked driver) input clock = .timeout) ∨
        ∃ clock resource, Lang.run (artifact.linked driver) input clock = .resource resource) := by
  obtain ⟨_, _, _, _, _, _, _, hrun⟩ := produceAuto_plainRc_parts accepted
  exact Recheck.RcReplay.sound hrun driver valid input hi

/-- End-to-end soundness of `RcReplay.produceAuto` on its immortal fallback
(plain RC selected but refused). -/
theorem produceAuto_immortal_sound {cfg : Recheck.Config} {inp : Recheck.Input}
    {cert : Recheck.Cert} {artifact : Recheck.Artifact} {alloc : List Xv.Alloc.Outcome}
    {reason : Recheck.Err}
    (accepted : Recheck.RcReplay.produceAuto cfg inp = .ok (.immortal cert artifact alloc reason))
    (driver : X86.Driver) (valid : driver.Ok artifact.backend.encoded.text.size)
    (input : Nat × List Nat) (hi : artifact.front.Covered cert input) :
    (∀ clock output, Lang.run (artifact.linked driver) input clock = .ok output →
      (∃ sourceClock value, Lang.run (⟨artifact.src, artifact.checked⟩ : CheckedProgram) input sourceClock = .ok value ∧
        artifact.front.view input.1 (Lang.obs value) = some output) ∨ artifact.front.GoesWrong input) ∧
    (¬ artifact.front.GoesWrong input → ∀ clock, ¬ (Lang.run (artifact.linked driver) input clock).GoesWrong) ∧
    ((∀ clock, Lang.run (⟨artifact.src, artifact.checked⟩ : CheckedProgram) input clock = .timeout) →
      (∀ clock, Lang.run (artifact.linked driver) input clock = .timeout) ∨
        ∃ clock failure, Lang.run (artifact.linked driver) input clock = .resource failure) := by
  obtain ⟨_, _, _, _, _, _, _, _, hrun⟩ := produceAuto_immortal_parts accepted
  exact Recheck.sound hrun driver valid input hi

/-- End-to-end soundness of `RcReplay.compileAuto` on the `.zeroRc` path. -/
theorem compileAuto_zeroRc_sound {cfg : Recheck.Config} {bytes : ByteArray} {equations : Lean.Json}
    {roots : List String}
    {cert : Recheck.Cert} {artifact : Recheck.Artifact} {alloc : List Xv.Alloc.Outcome}
    (accepted : Recheck.RcReplay.compileAuto cfg bytes equations roots = .ok (.zeroRc cert artifact alloc))
    (driver : X86.Driver) (valid : driver.Ok artifact.backend.encoded.text.size)
    (input : Nat × List Nat) (hi : artifact.front.Covered cert input) :
    (∀ clock output, Lang.run (artifact.linked driver) input clock = .ok output →
      (∃ sourceClock value, Lang.run (⟨artifact.src, artifact.checked⟩ : CheckedProgram) input sourceClock = .ok value ∧
        artifact.front.view input.1 (Lang.obs value) = some output) ∨ artifact.front.GoesWrong input) ∧
    (¬ artifact.front.GoesWrong input → ∀ clock, ¬ (Lang.run (artifact.linked driver) input clock).GoesWrong) ∧
    ((∀ clock, Lang.run (⟨artifact.src, artifact.checked⟩ : CheckedProgram) input clock = .timeout) →
      (∀ clock, Lang.run (artifact.linked driver) input clock = .timeout) ∨
        ∃ clock failure, Lang.run (artifact.linked driver) input clock = .resource failure) := by
  unfold Recheck.RcReplay.compileAuto at accepted
  simp only [bind, Except.bind] at accepted
  cases hing : Recheck.ingress bytes equations roots with
  | error e => simp [hing] at accepted
  | ok inp =>
    simp only [hing] at accepted
    exact produceAuto_zeroRc_sound accepted driver valid input hi

/-- End-to-end soundness of `RcReplay.compileAuto` on the `.plainRc` path. -/
theorem compileAuto_plainRc_sound {cfg : Recheck.Config} {bytes : ByteArray} {equations : Lean.Json}
    {roots : List String}
    {cert : Recheck.RcReplay.Cert} {artifact : Recheck.RcReplay.Artifact}
    {alloc : List Xv.Alloc.Outcome}
    (accepted : Recheck.RcReplay.compileAuto cfg bytes equations roots = .ok (.plainRc cert artifact alloc))
    (driver : X86.Driver) (valid : driver.Ok artifact.backend.encoded.text.size)
    (input : Nat × List Nat) (hi : artifact.front.Covered cert input) :
    (∀ clock output, Lang.run (artifact.linked driver) input clock = .ok output →
      (∃ sourceClock value,
        Lang.run (⟨artifact.front.src, artifact.front.checked⟩ : CheckedProgram)
          input sourceClock = .ok value ∧
        artifact.front.view input.1 (Lang.obs value) = some output) ∨ artifact.front.GoesWrong input) ∧
    (¬ artifact.front.GoesWrong input →
      ∀ clock, ¬ (Lang.run (artifact.linked driver) input clock).GoesWrong) ∧
    ((∀ clock, Lang.run (⟨artifact.front.src, artifact.front.checked⟩ : CheckedProgram)
        input clock = .timeout) →
      (∀ clock, Lang.run (artifact.linked driver) input clock = .timeout) ∨
        ∃ clock resource, Lang.run (artifact.linked driver) input clock = .resource resource) := by
  unfold Recheck.RcReplay.compileAuto at accepted
  simp only [bind, Except.bind] at accepted
  cases hing : Recheck.ingress bytes equations roots with
  | error e => simp [hing] at accepted
  | ok inp =>
    simp only [hing] at accepted
    exact produceAuto_plainRc_sound accepted driver valid input hi

/-- End-to-end soundness of `RcReplay.compileAuto` on its immortal fallback. -/
theorem compileAuto_immortal_sound {cfg : Recheck.Config} {bytes : ByteArray} {equations : Lean.Json}
    {roots : List String}
    {cert : Recheck.Cert} {artifact : Recheck.Artifact} {alloc : List Xv.Alloc.Outcome}
    {reason : Recheck.Err}
    (accepted : Recheck.RcReplay.compileAuto cfg bytes equations roots =
      .ok (.immortal cert artifact alloc reason))
    (driver : X86.Driver) (valid : driver.Ok artifact.backend.encoded.text.size)
    (input : Nat × List Nat) (hi : artifact.front.Covered cert input) :
    (∀ clock output, Lang.run (artifact.linked driver) input clock = .ok output →
      (∃ sourceClock value, Lang.run (⟨artifact.src, artifact.checked⟩ : CheckedProgram) input sourceClock = .ok value ∧
        artifact.front.view input.1 (Lang.obs value) = some output) ∨ artifact.front.GoesWrong input) ∧
    (¬ artifact.front.GoesWrong input → ∀ clock, ¬ (Lang.run (artifact.linked driver) input clock).GoesWrong) ∧
    ((∀ clock, Lang.run (⟨artifact.src, artifact.checked⟩ : CheckedProgram) input clock = .timeout) →
      (∀ clock, Lang.run (artifact.linked driver) input clock = .timeout) ∨
        ∃ clock failure, Lang.run (artifact.linked driver) input clock = .resource failure) := by
  unfold Recheck.RcReplay.compileAuto at accepted
  simp only [bind, Except.bind] at accepted
  cases hing : Recheck.ingress bytes equations roots with
  | error e => simp [hing] at accepted
  | ok inp =>
    simp only [hing] at accepted
    exact produceAuto_immortal_sound accepted driver valid input hi

end IxCC.Compiler

namespace IxCC.Recheck

/-- **What ingress established** (`Recheck.ingress`): the envelope decoded to
`inp.env`; the certified kernel's tiered entry accepted the whole environment
(`Src.KernelFront.accept`, at the front end's batch limits: it ran on exactly
the envelope's binding section, records and blobs, `accept_spec`); the
program is IxCC's reading of the records the seeds reach
(`Src.Ingress.reach` from the seeds of the whole sidecar and the kernel's
admitted role table, each reached record within IxCC's consumer budget in what
is read of it; a theorem's proof read only where a proof seed reaches it,
`Src.Program.byStatement`), for the chosen roots, with the pinned identities of
the kernel's admitted role table, its resource binding validated, and it is
read against the kernel's reading (`Reading.build`), whose index the annotator
asks. The decode no longer implies that every record of the artifact is within
IxCC's consumer budget: only the reached ones are, by `reach`. The acceptance
gives, through the kernel's theorems, the reading's fidelity, a model and the
strong model of the logical environment, at IxCC's hash, under the artifact's
own table and behind its own prelude; it is not the end-to-end statements'
first premise, which is about the closure of the seeds under the default table
and the committed prelude. -/
theorem ingress_parts {bytes : ByteArray} {equations : Lean.Json}
    {roots : List String} {inp : Input}
    (h : ingress bytes equations roots = .ok inp) :
    Ixon.V3.decodeAnonymousEnv bytes = .ok inp.env ∧
    Src.KernelFront.accept inp.env Src.KernelFront.defaultLimits = .ok inp.kernel.acc ∧
    Src.KernelFront.AcceptedFrom inp.env Src.KernelFront.defaultLimits inp.kernel.acc ∧
    Ix.Kernel.Admission.checkBytesTieredUsing (Src.KernelFront.preludeSource inp.kernel.acc.pre)
      Src.KernelFront.hash inp.kernel.acc.binding inp.kernel.acc.limits inp.kernel.acc.records
      inp.kernel.acc.blobs inp.kernel.acc.hints.lookup = .ok (inp.kernel.acc.env, inp.kernel.acc.tier) ∧
    Src.Resource.validate inp.program = .ok () ∧
    Src.KernelFront.Reading.build inp.kernel.acc inp.program = .ok inp.kernel.rd ∧
    inp.kernel.fe = Ix.Kernel.mkFEnv inp.kernel.acc.env ∧
    ∃ rawHints chosen records rawProg,
      Src.Hints.ofK1Json equations = .ok rawHints ∧
      selectRoots rawHints.roots roots = .ok chosen ∧
      chosen.isEmpty = false ∧
      Src.Ingress.reach inp.env (Src.Ingress.Seeds.of rawHints
        (Src.KernelFront.pinsOfTable inp.kernel.acc.table)) = .ok records ∧
      Src.Ingress.readConsts inp.env records (chosen.map (·.1)) = .ok rawProg ∧
      inp.program = { rawProg with
        known := Src.Pinned.known
          { rawProg with known := { pins := Src.KernelFront.pinsOfTable inp.kernel.acc.table } },
        resource := inp.hints.resource } := by
  unfold ingress at h
  cases henv : Ixon.V3.decodeAnonymousEnv bytes with
  | error e => simp [henv, bind, Except.bind, Except.mapError] at h
  | ok env =>
    rw [henv] at h
    simp only [Except.mapError, bind, Except.bind] at h
    cases hhints : Src.Hints.ofK1Json equations with
    | error e => rw [hhints] at h; cases h
    | ok rawHints =>
      rw [hhints] at h
      simp only at h
      cases hchosen : selectRoots rawHints.roots roots with
      | error e => rw [hchosen] at h; cases h
      | ok chosen =>
        rw [hchosen] at h
        simp only at h
        cases hempty : chosen.isEmpty with
        | true => simp [hempty] at h
        | false =>
          rw [hempty] at h
          simp only [Bool.false_eq_true, ↓reduceIte, pure, Except.pure] at h
          cases hacc : Src.KernelFront.accept env with
          | error e => rw [hacc] at h; cases h
          | ok acc =>
            rw [hacc] at h
            simp only at h
            cases hreach : Src.Ingress.reach env (Src.Ingress.Seeds.of rawHints
                (Src.KernelFront.pinsOfTable acc.table)) with
            | error e => rw [hreach] at h; cases h
            | ok records =>
              rw [hreach] at h
              simp only at h
              cases hprog : Src.Ingress.readConsts env records (chosen.map (·.1)) with
              | error e => rw [hprog] at h; cases h
              | ok rawProg =>
                rw [hprog] at h
                simp only at h
                -- the resource binding (its `mapError` unfolded to a `match`)
                split at h
                · cases h
                · rename_i u hv
                  split at hv
                  · cases hv
                  · rename_i v hval
                    -- the reading against the kernel's
                    split at h
                    · cases h
                    · rename_i rd0 hb
                      split at hb
                      · cases hb
                      · rename_i rd hrd
                        injection hb with hb
                        subst hb
                        injection h with h
                        subst h
                        have hspec := Src.KernelFront.accept_spec hacc
                        exact ⟨rfl, hacc, hspec.1, hspec.2, hval, hrd, rfl,
                          rawHints, chosen, records, rawProg, rfl, hchosen, hempty, hreach, hprog, rfl⟩

/-- Projection from `Recheck.run` to the front-end recheck step `Recheck.front`
(`Src.Table.ofCert`, then `Src.Recheck.annotation`, which runs `Lazify.run`). -/
theorem run_front {cfg : Config} {P : Src.Program} {c : Cert} {a : Artifact}
    (h : run cfg P c = .ok a) :
    front cfg P c = .ok (a.src, a.checked) :=
  (runLir_spec (run_parts h).1).1

/-- Projection from `Recheck.RcReplay.run` to the front-end recheck step
`Recheck.front` (`Src.Table.ofCert`, then `Src.Recheck.annotation`, which runs `Lazify.run`). -/
theorem RcReplay.run_front {cfg : Config} {P : Src.Program} {c : RcReplay.Cert}
    {a : RcReplay.Artifact} (h : RcReplay.run cfg P c = .ok a) :
    front cfg P c.base = .ok (a.front.src, a.front.checked) :=
  (RcReplay.runFront_spec (RcReplay.run_parts h).1).1

end IxCC.Recheck
