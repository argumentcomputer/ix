import IxCC.Fir.Proof.Retained
import IxCC.Recheck.Rc.Proof.Replay
import IxCC.Cfg.Rc.Proof.Native.ReturnedObservation

/-! Retain source witnesses directly through the actual Fir lowering. The
physical induction can consume these witnesses without comparing its heap
with an independently executed abstract Cfg heap. -/
set_option autoImplicit false
namespace IxCC.Recheck.RcReplay
open IxCC.Sem (Lang)
open IxCC.Rt.Rc.Procs
open IxCC.Cfg.Rc.Native.Spec

/-- The actual Anf value and Fir representation behind a source observation. -/
def SourceFirWitness (A : Anf.Program) (observation : Option Sem.Obs)
    (logical : Fir.Val) : Prop :=
  ∃ value, Anf.obsV value = observation ∧ Fir.Proof.FirWitness A value logical

theorem source_fir_retained {cfg : Config} {P : Src.Program} {c : Cert} {f : Front}
    (accepted : runFront cfg P c = .ok f) (i : Nat × List Nat) :
    Sem.Behaviour.Refines
      (fun value logical => SourceFirWitness f.anf
        (Lang.obs (S := Lam.Erase.Proof.CheckedProgram) value) logical)
      (Lang.behaviour (⟨f.src, f.checked⟩ : Lam.Erase.Proof.CheckedProgram) i)
      (Lang.behaviour f.fir i) := by
  obtain ⟨_, ⟨st, erased⟩, anf, fir, _, _, _⟩ := runFront_spec accepted
  have front := (Lam.Erase.Proof.erase_refines erased).trans
    (Anf.Pipeline.Proof.run_correct anf)
  have tail := (Fir.Proof.lower_retained fir i).refines
    (Lang.mono f.anf i) (Lang.mono f.fir i)
  exact ((front i).trans tail).mono fun _ _ ⟨value, observed, retained⟩ =>
    ⟨value, observed.symm, retained⟩

/-- An actual Fir success exposes its retained source witness, unless the
accepted source itself reaches stuck. No typing or observation is assumed. -/
theorem source_fir_success {cfg : Config} {P : Src.Program} {c : Cert} {f : Front}
    (accepted : runFront cfg P c = .ok f) {i : Nat × List Nat} {k : Nat}
    {logical : Fir.Val} (success : Fir.firRun f.fir i k = .ok logical) :
    (∃ k' value,
      Lang.run (⟨f.src, f.checked⟩ : Lam.Erase.Proof.CheckedProgram) i k' = .ok value ∧
      SourceFirWitness f.anf (Lang.obs (S := Lam.Erase.Proof.CheckedProgram) value) logical) ∨
    ∃ k', Lang.run (⟨f.src, f.checked⟩ : Lam.Erase.Proof.CheckedProgram) i k' = .stuck := by
  have behavior : Lang.behaviour f.fir i = .terminates logical :=
    (Sem.behaviour_eq_terminates_iff (Lang.mono f.fir i)).2 ⟨k, success⟩
  have related := source_fir_retained accepted i
  rw [behavior] at related
  rcases related.of_terminates with ⟨value, terminated, witness⟩ | stuck
  · obtain ⟨k', run⟩ := (Sem.behaviour_eq_terminates_iff
      (Lang.mono (⟨f.src, f.checked⟩ : Lam.Erase.Proof.CheckedProgram) i)).1 terminated
    exact .inl ⟨k', value, run, witness⟩
  · exact .inr ((Sem.behaviour_eq_stuck_iff
      (Lang.mono (⟨f.src, f.checked⟩ : Lam.Erase.Proof.CheckedProgram) i)).1 stuck)

theorem SourceFirWitness.observations {A : Anf.Program} {observation : Option Sem.Obs}
    {logical : Fir.Val} (witness : SourceFirWitness A observation logical) :
    Fir.obsV logical = observation := by
  obtain ⟨value, observed, related⟩ := witness
  exact related.observations.symm.trans observed

theorem SourceFirWitness.value {A : Anf.Program} {observation : Sem.Obs}
    {logical : Fir.Val} (witness : SourceFirWitness A (some observation) logical) :
    ∃ value, Fir.Proof.VR A value logical ∧ Fir.obsV logical = some observation := by
  obtain ⟨value, observed, related⟩ := witness
  rcases related with related | ⟨unobserved, _⟩
  · exact ⟨value, related, (Fir.Proof.vr_obs related).symm.trans observed⟩
  · rw [observed] at unobserved
    cases unobserved

/-- Read the actual physical return memory through the accepted source tree
view. Its heap, extent, address map and readback fuel come from Returned. -/
theorem SourceFirWitness.observe {A : Anf.Program} {source target : Sem.Obs}
    {logical : Fir.Val} (witness : SourceFirWitness A (some source) logical)
    {P : Cfg.Rc.Program} {pairs : List (Nat × Cfg.Fun)} {lp : Lir.Program}
    {origin : Own.Heap} {originAddresses : AddressMap} {external : Nat → Nat}
    {context base limit : Lir.Word} {regionBytes : Nat}
    (returned : Returned P pairs lp origin originAddresses external context base limit regionBytes logical)
    {signature : Rt.Sig} {type : Rt.FoTy}
    (viewed : Readback.treeView A.ctors signature type source = some target) :
    Rt.readback signature (regionBytes / 8) returned.memory type returned.word = some target := by
  obtain ⟨value, related, observed⟩ := witness.value
  exact returned.observe related observed viewed

/-! ## Contract-Aware Source/Certificate Admission and Replay -/

theorem checkPlainMap_implies_contract {F : Fir.Program}
    {bodies : Src.NatMap Own.Plain.Code}
    (checked : Own.Plain.checkPlainMap F bodies = true) :
    Own.Plain.checkContractPlainMap F bodies = true := by
  obtain ⟨domain, pins, canonical⟩ := Own.Plain.checkPlainMap_parts checked
  have bodyEq : (Own.Plain.Program.canonical F).bodies = bodies :=
    congrArg Own.Plain.Program.bodies canonical.symm
  simp only [Own.Plain.checkContractPlainMap, Bool.and_eq_true, Own.Plain.bodyMapEq_iff, and_assoc]
  exact ⟨Own.Plain.programDomain_implies_contractProgramDomain domain, pins, bodyEq⟩

theorem admit_implies_admitContract {F : Fir.Program} {j : Lean.Json}
    {P : Own.Plain.Program} (accepted : Own.Plain.Certificate.admit F j = .ok P) :
    Own.Plain.Certificate.admitContract F j = .ok P := by
  unfold Own.Plain.Certificate.admit at accepted
  unfold Own.Plain.Certificate.admitContract
  cases hd : Own.Plain.Certificate.decode F j with
  | error e =>
    simp only [hd, bind, Except.bind] at accepted
    cases accepted
  | ok bodies =>
    simp only [hd, bind, Except.bind] at accepted ⊢
    split at accepted
    · next checked =>
      cases accepted
      simp [checkPlainMap_implies_contract checked, pure, Except.pure]
    · cases accepted

theorem admitContract_parts {F : Fir.Program} {j : Lean.Json}
    {P : Own.Plain.Program} (accepted : Own.Plain.Certificate.admitContract F j = .ok P) :
    P.source = F ∧ Own.Plain.checkContractPlainMap F P.bodies = true := by
  unfold Own.Plain.Certificate.admitContract at accepted
  cases hd : Own.Plain.Certificate.decode F j with
  | error e =>
    simp only [hd, bind, Except.bind] at accepted
    cases accepted
  | ok bodies =>
    simp only [hd, bind, Except.bind] at accepted
    split at accepted
    · next checked =>
      cases accepted
      exact ⟨rfl, checked⟩
    · cases accepted

def checkContractProgram (F : Fir.Program) (bodies : Src.NatMap Own.Plain.Code)
    (candidate : Cfg.Rc.Program) : Bool :=
  Own.Plain.checkContractPlainMap F bodies &&
    match Cfg.Rc.generate F bodies with
    | none => false
    | some expected => Cfg.Rc.programEq expected candidate

def checkContractScopedProgram (F : Fir.Program) (bodies : Src.NatMap Own.Plain.Code)
    (P : Cfg.Rc.Program) : Bool :=
  checkContractProgram F bodies P && Cfg.Rc.programNames F bodies && Cfg.Rc.sourceDense F

def lowerPublicWithContracts (config : Rt.Config) (F : Fir.Program)
    (bodies : Src.NatMap Own.Plain.Code) (P : Cfg.Rc.Program) :
    Except String Cfg.Rc.Public.Lowered :=
  Cfg.Rc.Public.lower config (Own.Plain.normalizeProgramContracts F) bodies P

/-- Contract-aware certificate front end accepting surface ownership annotations
(`0`, `1`, `&`, `*`, `!`, `~`, `let borrow`) via `admitContract` and
`checkContractScopedProgram`. -/
def runFrontWithContracts (cfg : Config) (P : Src.Program) (c : Cert) : Except Err Front := do
  let (src, checked) ← Recheck.front cfg P c.base
  let (lam, _) ← (Lam.erase src checked).mapError Err.ofErase
  let anf ← (Anf.Pipeline.run c.base.mid lam).mapError fun message =>
    { stage := .anf, code := "anf.replay", message }
  let fir ← (Fir.lower anf).mapError Err.ofFir
  let own ← (Own.Plain.Certificate.admitContract fir c.own).mapError fun message =>
    { stage := .cert, code := "own.plain", message }
  let some candidate := Cfg.Rc.generate fir own.bodies |
    throw { stage := .rt, code := "rc.cfg", message := "ownership candidate lowering declined" }
  unless checkContractScopedProgram fir own.bodies candidate do
    throw { stage := .rt, code := "rc.scope", message := "scoped dense-source RC gate refused" }
  Recheck.checkParams cfg candidate.base (candidate.base.exports.zipIdx.map fun (f, i) => (i, f))
  let lowered ← (lowerPublicWithContracts { names := cfg.names } fir own.bodies candidate).mapError fun message =>
    { stage := .rt, code := "rc.lower", message }
  return {
    src, checked, lam, anf, fir, own, cfg := candidate
    lowered := lowered.runtime, drop := lowered.drop }

def runWithContracts (cfg : Config) (P : Src.Program) (c : Cert) : Except Err Artifact := do
  let f ← runFrontWithContracts cfg P c
  let root := (f.src.roots.head?.map (·.1)).getD default
  let provenance := cfg.provenance.getD (.ixir1Policy root 3 1)
  let cfg := { cfg with provenance := some provenance }
  let (_, xl, stacked, program, exports) ← backTyped cfg f root c.base
  Recheck.checkSymbols stacked.exports
  let backend ← (Backend.finish xl.main stacked program exports provenance).mapError Err.ofBackend
  let rows := (List.range f.src.roots.length).zip
    (f.src.roots.zip (f.cfg.base.exports.zip f.lowered.roots))
  return { front := f, backend, roots := Recheck.rootsOf cfg f.src f.cfg.base f.lowered rows }

theorem lowerFunction_normalizeFunContracts (limit f : Nat)
    (fd : Fir.Fun) (body : Own.Plain.Code) :
    Cfg.Rc.lowerFunction limit f (Own.Plain.normalizeFunContracts fd) body =
      Cfg.Rc.lowerFunction limit f fd body := rfl

theorem entries_normalizeProgramContracts (F : Fir.Program)
    (bodies : Src.NatMap Own.Plain.Code) (fs : List Nat) :
    Cfg.Rc.entries (Own.Plain.normalizeProgramContracts F) bodies fs =
      Cfg.Rc.entries F bodies fs := by
  induction fs with
  | nil => rfl
  | cons f rest ih =>
    unfold Cfg.Rc.entries
    have hsz : (Own.Plain.normalizeProgramContracts F).size = F.size := rfl
    rw [hsz, Own.Plain.normalizeProgramContracts_fun?, ih]
    cases F.fun? f <;> rfl

theorem generate_normalizeProgramContracts (F : Fir.Program)
    (bodies : Src.NatMap Own.Plain.Code) :
    Cfg.Rc.generate (Own.Plain.normalizeProgramContracts F) bodies =
      Cfg.Rc.generate F bodies := by
  unfold Cfg.Rc.generate
  have hsz : (Own.Plain.normalizeProgramContracts F).size = F.size := rfl
  rw [hsz, entries_normalizeProgramContracts]
  rfl

theorem checkProgram_normalizeProgramContracts (F : Fir.Program)
    (bodies : Src.NatMap Own.Plain.Code) (candidate : Cfg.Rc.Program) :
    Cfg.Rc.checkProgram (Own.Plain.normalizeProgramContracts F) bodies candidate =
      checkContractProgram F bodies candidate := by
  unfold Cfg.Rc.checkProgram checkContractProgram
  rw [Own.Plain.checkPlainMap_normalizeProgramContracts, generate_normalizeProgramContracts]
  rfl

theorem programNames_normalizeProgramContracts (F : Fir.Program)
    (bodies : Src.NatMap Own.Plain.Code) :
    Cfg.Rc.programNames (Own.Plain.normalizeProgramContracts F) bodies =
      Cfg.Rc.programNames F bodies := by
  unfold Cfg.Rc.programNames
  have hsz : (Own.Plain.normalizeProgramContracts F).size = F.size := rfl
  rw [hsz]
  refine congrArg ((List.range F.size).all ·) (funext fun f => ?_)
  rw [Own.Plain.normalizeProgramContracts_fun?]
  cases F.fun? f <;> cases bodies.get? f <;> rfl

private theorem entriesAux_map {α β : Type} (f : α → β) (m : Src.NatMap α)
    (k w : Nat) (acc : List (Nat × α)) :
    Src.NatMap.entriesAux (m.map f) k w (acc.map fun p => (p.1, f p.2)) =
      (Src.NatMap.entriesAux m k w acc).map fun p => (p.1, f p.2) := by
  induction m generalizing k w acc with
  | leaf => rfl
  | node v z o iz io =>
    cases v <;> simp [Src.NatMap.map, Src.NatMap.entriesAux, iz, io]

private theorem toList_map {α β : Type} (f : α → β) (m : Src.NatMap α) :
    (m.map f).toList = m.toList.map fun p => (p.1, f p.2) :=
  entriesAux_map f m 0 1 []

theorem sourceDense_normalizeProgramContracts (F : Fir.Program) :
    Cfg.Rc.sourceDense (Own.Plain.normalizeProgramContracts F) =
      Cfg.Rc.sourceDense F := by
  unfold Cfg.Rc.sourceDense Own.Plain.normalizeProgramContracts
  dsimp only
  rw [toList_map, List.all_map]
  rfl

theorem checkScopedProgram_normalizeProgramContracts (F : Fir.Program)
    (bodies : Src.NatMap Own.Plain.Code) (candidate : Cfg.Rc.Program) :
    Cfg.Rc.checkScopedProgram (Own.Plain.normalizeProgramContracts F) bodies candidate =
      checkContractScopedProgram F bodies candidate := by
  unfold Cfg.Rc.checkScopedProgram checkContractScopedProgram
  rw [checkProgram_normalizeProgramContracts, programNames_normalizeProgramContracts,
    sourceDense_normalizeProgramContracts]

theorem checkProgram_implies_checkContractProgram {F : Fir.Program}
    {bodies : Src.NatMap Own.Plain.Code} {candidate : Cfg.Rc.Program}
    (checked : Cfg.Rc.checkProgram F bodies candidate = true) :
    checkContractProgram F bodies candidate = true := by
  simp only [Cfg.Rc.checkProgram, checkContractProgram, Bool.and_eq_true] at checked ⊢
  exact ⟨checkPlainMap_implies_contract checked.1, checked.2⟩

theorem checkScopedProgram_implies_checkContractScopedProgram {F : Fir.Program}
    {bodies : Src.NatMap Own.Plain.Code} {P : Cfg.Rc.Program}
    (checked : Cfg.Rc.checkScopedProgram F bodies P = true) :
    checkContractScopedProgram F bodies P = true := by
  simp only [Cfg.Rc.checkScopedProgram, checkContractScopedProgram, Bool.and_eq_true] at checked ⊢
  exact ⟨⟨checkProgram_implies_checkContractProgram checked.1.1, checked.1.2⟩, checked.2⟩

theorem lowerPublicWithContracts_of_checkProgram {config : Rt.Config}
    {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Cfg.Rc.Program}
    (checked : Cfg.Rc.checkProgram F bodies P = true) :
    lowerPublicWithContracts config F bodies P = Cfg.Rc.Public.lower config F bodies P := by
  have hc : Cfg.Rc.checkProgram (Own.Plain.normalizeProgramContracts F) bodies P = true := by
    rw [checkProgram_normalizeProgramContracts]
    exact checkProgram_implies_checkContractProgram checked
  unfold lowerPublicWithContracts Cfg.Rc.Public.lower Cfg.Rc.Native.lower
  simp [checked, hc]

theorem runFront_implies_runFrontWithContracts {cfg : Config} {P : Src.Program}
    {c : Cert} {f : Front} (accepted : runFront cfg P c = .ok f) :
    runFrontWithContracts cfg P c = .ok f := by
  unfold runFront at accepted
  unfold runFrontWithContracts
  cases hfront : Recheck.front cfg P c.base with
  | error e => rw [hfront] at accepted; cases accepted
  | ok sc =>
    obtain ⟨src, checked⟩ := sc
    rw [hfront] at accepted
    simp only [bind, Except.bind] at accepted ⊢
    cases herase : Lam.erase src checked with
    | error e => rw [herase] at accepted; cases accepted
    | ok ls =>
      obtain ⟨lam, st⟩ := ls
      simp only [herase, Except.mapError] at accepted ⊢
      cases hanf : Anf.Pipeline.run c.base.mid lam with
      | error e => rw [hanf] at accepted; cases accepted
      | ok anf =>
        simp only [hanf] at accepted ⊢
        cases hfir : Fir.lower anf with
        | error e => rw [hfir] at accepted; cases accepted
        | ok fir =>
          simp only [hfir] at accepted ⊢
          cases hown : Own.Plain.Certificate.admit fir c.own with
          | error e => rw [hown] at accepted; cases accepted
          | ok own =>
            have hown' := admit_implies_admitContract hown
            simp only [hown] at accepted
            simp only [hown']
            cases hgen : Cfg.Rc.generate fir own.bodies with
            | none => rw [hgen] at accepted; cases accepted
            | some candidate =>
              simp only [hgen] at accepted ⊢
              cases hscope : Cfg.Rc.checkScopedProgram fir own.bodies candidate with
              | false => simp [hscope] at accepted
              | true =>
                have hscope' := checkScopedProgram_implies_checkContractScopedProgram hscope
                have hcheck : Cfg.Rc.checkProgram fir own.bodies candidate = true :=
                  (Cfg.Rc.checkScopedProgram_parts hscope).1
                simp only [hscope, ↓reduceIte, pure, Except.pure] at accepted
                simp only [hscope', ↓reduceIte, pure, Except.pure,
                  lowerPublicWithContracts_of_checkProgram hcheck]
                exact accepted

theorem run_implies_runWithContracts {cfg : Config} {P : Src.Program}
    {c : Cert} {artifact : Artifact} (accepted : run cfg P c = .ok artifact) :
    runWithContracts cfg P c = .ok artifact := by
  unfold run at accepted
  unfold runWithContracts
  cases hf : runFront cfg P c with
  | error e => rw [hf] at accepted; cases accepted
  | ok f =>
    rw [hf] at accepted
    rw [runFront_implies_runFrontWithContracts hf]
    exact accepted

theorem runFrontWithContracts_spec {cfg : Config} {P : Src.Program} {c : Cert} {f : Front}
    (accepted : runFrontWithContracts cfg P c = .ok f) :
    Recheck.front cfg P c.base = .ok (f.src, f.checked) ∧
    (∃ st, Lam.erase f.src f.checked = .ok (f.lam, st)) ∧
    Anf.Pipeline.run c.base.mid f.lam = .ok f.anf ∧
    Fir.lower f.anf = .ok f.fir ∧
    Own.Plain.Certificate.admitContract f.fir c.own = .ok f.own ∧
    Cfg.Rc.generate f.fir f.own.bodies = some f.cfg ∧
    checkContractScopedProgram f.fir f.own.bodies f.cfg = true := by
  unfold runFrontWithContracts at accepted
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
        simp only [hanf] at accepted
        cases hfir : Fir.lower anf with
        | error e => rw [hfir] at accepted; cases accepted
        | ok fir =>
          simp only [hfir] at accepted
          cases hown : Own.Plain.Certificate.admitContract fir c.own with
          | error e => rw [hown] at accepted; cases accepted
          | ok own =>
            simp only [hown] at accepted
            cases hgen : Cfg.Rc.generate fir own.bodies with
            | none => rw [hgen] at accepted; cases accepted
            | some candidate =>
              simp only [hgen] at accepted
              cases hscope : checkContractScopedProgram fir own.bodies candidate with
              | false => simp [hscope] at accepted
              | true =>
                simp only [hscope, ↓reduceIte, pure, Except.pure] at accepted
                cases hparams : Recheck.checkParams cfg candidate.base
                    (candidate.base.exports.zipIdx.map fun (f, i) => (i, f)) with
                | error e => rw [hparams] at accepted; cases accepted
                | ok u =>
                  cases u
                  simp only [hparams] at accepted
                  cases hnative : lowerPublicWithContracts { names := cfg.names }
                      fir own.bodies candidate with
                  | error e => rw [hnative] at accepted; cases accepted
                  | ok lowered =>
                    simp only [hnative, Except.ok.injEq] at accepted
                    subst accepted
                    exact ⟨rfl, ⟨st, herase⟩, hanf, hfir, hown, hgen, hscope⟩

theorem source_fir_retained_withContracts {cfg : Config} {P : Src.Program} {c : Cert} {f : Front}
    (accepted : runFrontWithContracts cfg P c = .ok f) (i : Nat × List Nat) :
    Sem.Behaviour.Refines
      (fun value logical => SourceFirWitness f.anf
        (Lang.obs (S := Lam.Erase.Proof.CheckedProgram) value) logical)
      (Lang.behaviour (⟨f.src, f.checked⟩ : Lam.Erase.Proof.CheckedProgram) i)
      (Lang.behaviour f.fir i) := by
  obtain ⟨_, ⟨st, erased⟩, anf, fir, _, _, _⟩ := runFrontWithContracts_spec accepted
  have front := (Lam.Erase.Proof.erase_refines erased).trans
    (Anf.Pipeline.Proof.run_correct anf)
  have tail := (Fir.Proof.lower_retained fir i).refines
    (Lang.mono f.anf i) (Lang.mono f.fir i)
  exact ((front i).trans tail).mono fun _ _ ⟨value, observed, retained⟩ =>
    ⟨value, observed.symm, retained⟩

theorem source_fir_success_withContracts {cfg : Config} {P : Src.Program} {c : Cert} {f : Front}
    (accepted : runFrontWithContracts cfg P c = .ok f) {i : Nat × List Nat} {k : Nat}
    {logical : Fir.Val} (success : Fir.firRun f.fir i k = .ok logical) :
    (∃ k' value,
      Lang.run (⟨f.src, f.checked⟩ : Lam.Erase.Proof.CheckedProgram) i k' = .ok value ∧
      SourceFirWitness f.anf (Lang.obs (S := Lam.Erase.Proof.CheckedProgram) value) logical) ∨
    ∃ k', Lang.run (⟨f.src, f.checked⟩ : Lam.Erase.Proof.CheckedProgram) i k' = .stuck := by
  have behavior : Lang.behaviour f.fir i = .terminates logical :=
    (Sem.behaviour_eq_terminates_iff (Lang.mono f.fir i)).2 ⟨k, success⟩
  have related := source_fir_retained_withContracts accepted i
  rw [behavior] at related
  rcases related.of_terminates with ⟨value, terminated, witness⟩ | stuck
  · obtain ⟨k', run⟩ := (Sem.behaviour_eq_terminates_iff
      (Lang.mono (⟨f.src, f.checked⟩ : Lam.Erase.Proof.CheckedProgram) i)).1 terminated
    exact .inl ⟨k', value, run, witness⟩
  · exact .inr ((Sem.behaviour_eq_stuck_iff
      (Lang.mono (⟨f.src, f.checked⟩ : Lam.Erase.Proof.CheckedProgram) i)).1 stuck)

theorem plainRun_normalizeProgramContracts (F : Fir.Program)
    (bodies : Src.NatMap Own.Plain.Code) (i : Nat × List Nat) (k : Nat) :
    Own.Plain.plainRun { source := Own.Plain.normalizeProgramContracts F, bodies } i k =
      Own.Plain.plainRun { source := F, bodies } i k := by
  unfold Own.Plain.plainRun
  have hex : (Own.Plain.normalizeProgramContracts F).exports = F.exports := rfl
  rw [hex]
  cases F.exports[i.1]? with
  | none => rfl
  | some f =>
    dsimp only
    rw [Own.Plain.normalizeProgramContracts_fun?]
    cases F.fun? f with
    | none => rfl
    | some fd =>
      simp only [Option.map_some, Own.Plain.normalizeFunContracts, Own.Plain.run_normalizeProgramContracts]

theorem checked_contract_call_sim {F : Fir.Program} {candidate : Src.NatMap Own.Plain.Code}
    (checked : Own.Plain.checkContractPlainMap F candidate = true)
    {f : Fir.FunId} (hf : f < F.size) (ns : List Nat) :
    Sem.Sim (fun w p => Own.Proof.Den p.2 p.1 w) id
      (fun k => Fir.run F k f (Fir.litArgs ns))
      (fun k => Own.Plain.run { source := F, bodies := candidate } k f (Own.Plain.litArgs ns) {}) where
  forward k _ := ⟨k, (Own.Plain.checked_contract_program_refines checked k hf
    (Own.Plain.dens_lits {} ns) (Own.Plain.balance_lits_empty ns)).refines⟩
  timeout k h := by
    have related := (Own.Plain.checked_contract_program_refines checked k hf
      (Own.Plain.dens_lits {} ns) (Own.Plain.balance_lits_empty ns)).refines
    change Fir.evalCall F k f (Fir.litArgs ns) = .timeout at h
    rw [h] at related
    exact Sem.Result.Refines.timeout_iff.mp related

theorem checked_contract_refines_lang {F : Fir.Program} {candidate : Src.NatMap Own.Plain.Code}
    (checked : Own.Plain.checkContractPlainMap F candidate = true)
    (exports : ∀ f, f ∈ F.exports → f < F.size) :
    Sem.Refines F ({ source := F, bodies := candidate } : Own.Plain.Program) := by
  refine Sem.Refines.of_sim (R := Lang.ObsEq) (fun _ _ h => h) fun i => ⟨id, ?_⟩
  obtain ⟨r, ns⟩ := i
  show Sem.Sim _ _ (Fir.firRun F (r, ns))
    (Own.Plain.plainRun { source := F, bodies := candidate } (r, ns))
  unfold Fir.firRun Own.Plain.plainRun
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
          show Fir.obsV w = Own.Plain.obsV p
          rw [Own.Plain.obsV_den hd]
      · by_cases hlt : ns.length < fd.params.length
        · simp only [Sem.entryRun, he, hlt, ↓reduceIte]
          by_cases hn : ns = []
          · simp only [hn, ↓reduceIte]
            exact Sem.Sim.okConst (R := Lang.ObsEq (S := Fir.Program) (T := Own.Plain.Program))
              (show Fir.obsV .erased = Own.Plain.obsV (.erased, {}) by
                rw [Own.Plain.obsV_erased]; rfl)
          · simp only [hn, ↓reduceIte]
            exact Sem.Sim.laterConst (R := Lang.ObsEq (S := Fir.Program) (T := Own.Plain.Program))
              (show Fir.obsV .erased = Own.Plain.obsV (.erased, {}) by
                rw [Own.Plain.obsV_erased]; rfl) (fun k h => h)
        · simp only [Sem.entryRun, he, hlt, ↓reduceIte]
          exact Sem.Sim.bindStuck (checked_contract_call_sim checked hf (ns.take fd.params.length))
            fun _ _ _ => rfl

theorem checked_contract_refines_cfg {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code}
    {P : Cfg.Rc.Program} (checked : checkContractScopedProgram F bodies P = true) :
    Sem.Refines ({ source := F, bodies } : Own.Plain.Program) P := by
  have hnorm : Cfg.Rc.checkScopedProgram (Own.Plain.normalizeProgramContracts F) bodies P = true := by
    rw [checkScopedProgram_normalizeProgramContracts]
    exact checked
  have href := Cfg.Rc.checked_refines_lang hnorm
  intro i
  have hbeh : Lang.behaviour ({ source := Own.Plain.normalizeProgramContracts F, bodies } : Own.Plain.Program) i =
      Lang.behaviour ({ source := F, bodies } : Own.Plain.Program) i := by
    unfold Lang.behaviour Sem.behaviour
    exact congrArg Sem.behaviour (funext fun k => plainRun_normalizeProgramContracts F bodies i k)
  rw [← hbeh]
  exact href i

theorem source_refines_cfg_withContracts {cfg : Config} {P : Src.Program} {c : Cert} {f : Front}
    (accepted : runFrontWithContracts cfg P c = .ok f) :
    Sem.Refines (⟨f.src, f.checked⟩ : Lam.Erase.Proof.CheckedProgram) f.cfg := by
  obtain ⟨_, ⟨st, herase⟩, hanf, hfir, _, _, hscope⟩ := runFrontWithContracts_spec accepted
  have hplain : Own.Plain.checkContractPlainMap f.fir f.own.bodies = true := by
    simp only [checkContractScopedProgram, checkContractProgram, Bool.and_eq_true] at hscope
    exact hscope.1.1.1
  have hfirOwn := (Fir.Proof.lower_refines hfir).trans
    (checked_contract_refines_lang hplain (Own.Plain.exports_of_lower hfir))
  exact (Lam.Erase.Proof.erase_refines herase).trans
    ((Anf.Pipeline.Proof.run_correct hanf).trans
      (hfirOwn.trans (checked_contract_refines_cfg hscope)))

end IxCC.Recheck.RcReplay
