import IxCC.Own.Plain.Proof.Candidate
import IxCC.Own.Plain.Proof.OwnedAccepts
import IxCC.Own.Plain.Proof.Mono
import IxCC.Fir.Proof.Lang
import IxCC.Recheck.Run
import IxCC.Lam.Erase.Proof.Correct
import IxCC.Anf.Proof.Pass.Pipeline
import IxCC.Recheck.Proof.Middle

/-! The checked plain-RC program as the existing Nat-input language. This
companion keeps the current source entry convention, observes complete values,
and derives its simulation from the actual checked map. Export bounds are an
explicit source-admission fact, to be discharged by successful Fir.lower. -/

set_option autoImplicit false

namespace IxCC.Own.Plain
open IxCC.Sem (Result ClockMono Obs Lang Sim Forall2)

def litArgs (ns : List Nat) : List RVal := ns.map fun n => .lit (.nat n)

def obsV (p : RVal × Heap) : Option Obs := (p.2.value? p.1).bind Fir.obsV

def plainRun (P : Program) (i : Nat × List Nat) (k : Nat) : Result (RVal × Heap) :=
  match P.source.exports[i.1]? with
  | some f =>
    match P.source.fun? f with
    | some fd => Sem.entryRun fd.params.length (.erased, {})
        (fun ns k => run P k f (litArgs ns) {}) i.2 k
    | none => .stuck
  | none => .stuck

instance : Lang (Nat × List Nat) Program where
  Val := RVal × Heap
  run := plainRun
  mono P i := by
    unfold plainRun
    split
    · split
      · exact Sem.entryRun_mono (fun ns => run_mono P _ _ _) _
      · exact ClockMono.const _
    · exact ClockMono.const _
  obs := obsV

theorem lang_run (P : Program) (i : Nat × List Nat) : Lang.run P i = plainRun P i := rfl

theorem obsV_den {H : Heap} {v : RVal} {w : Fir.Val} (h : Proof.Den H v w) :
    obsV (v, H) = Fir.obsV w := by
  simp only [obsV, show H.value? v = some w from h, Option.bind_some]

theorem obsV_erased (H : Heap) : obsV (.erased, H) = none := by
  rw [obsV_den (Proof.den_erased H)]
  rfl

theorem dens_lits (H : Heap) (ns : List Nat) :
    Forall2 (Proof.Den H) (litArgs ns) (Fir.litArgs ns) := by
  induction ns with
  | nil => exact .nil
  | cons n ns ih => exact .cons (Proof.den_lit H _) ih

theorem refsIn_lits (l : Nat) (ns : List Nat) : Rc.refsIn l (litArgs ns) = 0 := by
  induction ns with
  | nil => rfl
  | cons n ns ih => simpa [litArgs, Rc.refsIn] using ih

theorem balance_lits_empty (ns : List Nat) : Rc.Balance {} (fun _ => 0) (litArgs ns) := by
  intro l
  simp [Rc.dynCount, Heap.cell?, refsIn_lits, Rc.edgeCount, Rc.total]

theorem ResultRel.refines {before : Heap} {external : Nat → Nat}
    {source : Result Fir.Val} {target : Result (RVal × Heap)}
    (h : ResultRel before external source target) :
    Result.Refines (fun w p => Proof.Den p.2 p.1 w) source target := by
  cases h with
  | ok hd _ _ => exact .ok hd
  | timeout => exact .timeout
  | trap => exact .trap
  | resource r => exact .resource r
  | stuck => exact .stuck

/-- An accepted map simulates the source on a numbered function called with natural-number
arguments (the ownership checker's refinement, `checkOwned_refines`). -/
theorem owned_call_sim {F : Fir.Program} {candidate : Src.NatMap Code}
    (checked : checkOwned F candidate = true) {f : Fir.FunId} (hf : f < F.size)
    (ns : List Nat) :
    Sim (fun w p => Proof.Den p.2 p.1 w) id
      (fun k => Fir.run F k f (Fir.litArgs ns))
      (fun k => run { source := F, bodies := candidate } k f (litArgs ns) {}) where
  forward k _ := ⟨k, (checkOwned_refines checked k hf (dens_lits {} ns)
    (balance_lits_empty ns)).refines⟩
  timeout k h := by
    have related := (checkOwned_refines checked k hf (dens_lits {} ns)
      (balance_lits_empty ns)).refines
    change Fir.evalCall F k f (Fir.litArgs ns) = .timeout at h
    rw [h] at related
    exact Result.Refines.timeout_iff.mp related

theorem owned_refines_lang {F : Fir.Program} {candidate : Src.NatMap Code}
    (checked : checkOwned F candidate = true)
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
        exact (owned_call_sim checked hf ns).mono fun w p hd => by
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
          exact Sim.bindStuck (owned_call_sim checked hf (ns.take fd.params.length))
            fun _ _ _ => rfl




theorem checked_call_sim {F : Fir.Program} {candidate : Src.NatMap Code}
    (checked : checkPlainMap F candidate = true) {f : Fir.FunId} (hf : f < F.size)
    (ns : List Nat) :
    Sim (fun w p => Proof.Den p.2 p.1 w) id
      (fun k => Fir.run F k f (Fir.litArgs ns))
      (fun k => run { source := F, bodies := candidate } k f (litArgs ns) {}) :=
  owned_call_sim (checkPlainMap_checkOwned checked) hf ns

theorem checked_refines_lang {F : Fir.Program} {candidate : Src.NatMap Code}
    (checked : checkPlainMap F candidate = true)
    (exports : ∀ f, f ∈ F.exports → f < F.size) :
    Sem.Refines F ({ source := F, bodies := candidate } : Program) :=
  owned_refines_lang (checkPlainMap_checkOwned checked) exports

/-- The caller need not assume export well-formedness for an admitted Fir
program: the actual lowering checks it and preserves the admitted roots. -/
theorem exports_of_lower {A : Anf.Program} {F : Fir.Program}
    (lowered : Fir.lower A = .ok F) : ∀ f, f ∈ F.exports → f < F.size := by
  have fields := Fir.Proof.lower_fields lowered
  simpa only [fields.1, fields.2.1] using (Fir.Proof.lower_ok lowered).2.2.1

/-- The first composed heap stage: both passes execute their real admitted
programs; all source metadata facts come from successful Fir.lower. -/
theorem checked_lower_refines {A : Anf.Program} {F : Fir.Program}
    {candidate : Src.NatMap Code} (lowered : Fir.lower A = .ok F)
    (checked : checkPlainMap F candidate = true) :
    Sem.Refines A ({ source := F, bodies := candidate } : Program) :=
  (Fir.Proof.lower_refines lowered).trans
    (checked_refines_lang checked (exports_of_lower lowered))

/-- The same stage for any map the ownership checker accepts. -/
theorem owned_lower_refines {A : Anf.Program} {F : Fir.Program}
    {candidate : Src.NatMap Code} (lowered : Fir.lower A = .ok F)
    (checked : checkOwned F candidate = true) :
    Sem.Refines A ({ source := F, bodies := candidate } : Program) :=
  (Fir.Proof.lower_refines lowered).trans
    (owned_refines_lang checked (exports_of_lower lowered))

/-- Executable certificate-taking stage. Unsupported or malformed ownership
proposals are rejected; its certificate is the actual map evaluated by run. -/
def checkedPass : Sem.Transform Fir.Program Program where
  name := "Own.Plain.check"
  Cert := Src.NatMap Code
  pre F := ∃ A, Fir.lower A = .ok F
  run F candidate := if checkPlainMap F candidate then
    .ok { source := F, bodies := candidate }
    else .error "own.plain: unsupported source or invalid ownership proposal"
  post P := (∃ A, Fir.lower A = .ok P.source) ∧
    checkPlainMap P.source P.bodies = true
  correct F candidate P admitted accepted := by
    obtain ⟨A, lowered⟩ := admitted
    split at accepted
    · next checked =>
      cases accepted
      exact ⟨⟨⟨A, lowered⟩, checked⟩,
        checked_refines_lang checked (exports_of_lower lowered)⟩
    · cases accepted

def lowerCheckedPass : Sem.Transform Anf.Program Program :=
  Fir.Proof.lowerPass.comp checkedPass (fun _ h => h)






end IxCC.Own.Plain

namespace IxCC.Recheck.Rc

/-! Executable scratch front-end companion. The ownership proposal is still
an explicit argument until certificate/native integration; all earlier passes
are the existing production functions on their actual certificate fields. -/

structure Front where
  src : Src.Program
  checked : Src.Relevance.Checked
  lam : Lam.Program
  anf : Anf.Program
  fir : Fir.Program
  own : Own.Plain.Program

def runFront (cfg : Config) (P : Src.Program) (c : Cert)
    (candidate : Src.NatMap Own.Plain.Code) : Except Err Front := do
  let (src, checked) ← Recheck.front cfg P c
  let (lam, _) ← (Lam.erase src checked).mapError Err.ofErase
  let anf ← Recheck.anfOf c src lam
  let fir ← (Fir.lower anf).mapError Err.ofFir
  if Own.Plain.checkPlainMap fir candidate then
    pure { src, checked, lam, anf, fir, own := { source := fir, bodies := candidate } }
  else
    throw { stage := .cert, code := "own.plain", message := "unsupported source or invalid ownership proposal" }

theorem runFront_spec {cfg : Config} {P : Src.Program} {c : Cert}
    {candidate : Src.NatMap Own.Plain.Code} {f : Front}
    (accepted : runFront cfg P c candidate = .ok f) :
    Recheck.front cfg P c = .ok (f.src, f.checked) ∧
    (∃ st, Lam.erase f.src f.checked = .ok (f.lam, st)) ∧
    Recheck.anfOf c f.src f.lam = .ok f.anf ∧
    Fir.lower f.anf = .ok f.fir ∧
    f.own = ({ source := f.fir, bodies := candidate } : Own.Plain.Program) ∧
    Own.Plain.checkPlainMap f.fir candidate = true := by
  unfold runFront at accepted
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
        simp only [hanf, bind, Except.bind] at accepted
        cases hfir : Fir.lower anf with
        | error e => rw [hfir] at accepted; cases accepted
        | ok fir =>
          simp only [hfir, Except.mapError, bind, Except.bind] at accepted
          split at accepted
          · next hcheck =>
            simp only [pure, Except.pure, Except.ok.injEq] at accepted
            subst accepted
            exact ⟨rfl, ⟨st, herase⟩, hanf, hfir, rfl, hcheck⟩
          · cases accepted

/-- SrcEval relative composition through actual front/erase/middle/Fir and
the checked RC proposal, on every covered input (`Recheck.Covered`). No premise
assumes source-target execution agreement. This ends at the abstract heap;
Cfg/runtime/backend remain separate steps. -/
theorem source_refines {cfg : Config} {P : Src.Program} {c : Cert}
    {candidate : Src.NatMap Own.Plain.Code} {f : Front}
    (accepted : runFront cfg P c candidate = .ok f) :
    Sem.RefinesOn (Recheck.Covered c.mid f.src f.lam f.anf) (⟨f.src, f.checked⟩ : Lam.Erase.Proof.CheckedProgram)
      f.own := by
  obtain ⟨_, ⟨st, herase⟩, hanf, hfir, hown, hcheck⟩ := runFront_spec accepted
  rw [hown]
  exact Sem.RefinesOn.refines_trans (Lam.Erase.Proof.erase_refines herase)
    ((Recheck.anfOf_refines hanf).trans_refines
      (Own.Plain.checked_lower_refines hfir hcheck))




end IxCC.Recheck.Rc
