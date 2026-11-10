import IxCC.Anf.Proof.Pass.Shrink
import IxCC.Anf.Proof.Pass.Inline
import IxCC.Anf.Proof.Pass.Prune
import IxCC.Anf.Proof.Convert.Correct
import IxCC.Anf.Proof.Spec.Run
import IxCC.Anf.Pipeline

/-! # The middle end is correct

`Pipeline.run` is P1 followed by the certificate's steps. P1 gives a
program whose ids are exactly `0 … size - 1` (`convert_wf`; Lam programs
with a gap below their size are declined, `convert-dense`), every P2, P3,
P4 and prune step keeps that shape and refines its input
(`Shrink.Proof.run_refines`, `Inline.Proof.round_refines`,
`Specialize.Proof.run_refines`, `Prune.Proof.run_refines`), and refinement
composes (`Sem.Refines.trans`): `run_correct` holds for every certificate
the re-run accepts. The step lemmas still take P4's correctness as a
premise (`SpecCorrect`, now `spec_correct`); `run_correct_noSpec` states
the result for certificates without P4 steps without it. -/

set_option autoImplicit false

namespace IxCC.Anf.Pipeline.Proof

open IxCC.Anf.PassProof

/-- What a successful conversion is made of. -/
theorem convert_unfold {L : Lam.Program} {Q : Program} (h : convert L = .ok Q) :
    (List.range L.size).all (fun g => (L.global? g).isSome) = true ∧ ∃ gs,
      (L.globalList.mapM fun (p : GlobalId × Lam.Global) => do
        let gd ← (Convert.global (Convert.arities L) p.2).mapError (s!"global {p.1}: " ++ ·)
        return (p.1, gd)) = .ok gs ∧
      Q = { globals := Src.NatMap.ofList gs, size := L.size, roots := L.roots, ctors := L.ctors,
            known := L.known } := by
  unfold convert at h
  cases hm : Lam.modesOk L with
  | false =>
    simp only [hm] at h
    obtain ⟨_, he, _⟩ := Lam.ModesOk.bind_ok h
    cases he
  | true => ?_
  simp only [hm, ↓reduceIte] at h
  cases hr : L.roots.all (Convert.rootStrict L) with
  | false =>
    simp only [hr] at h
    obtain ⟨_, he, _⟩ := Lam.ModesOk.bind_ok h
    cases he
  | true => ?_
  simp only [hr, ↓reduceIte] at h
  cases hdn : (List.range L.size).all (fun g => (L.global? g).isSome) with
  | false =>
    simp only [hdn] at h
    obtain ⟨_, he, _⟩ := Lam.ModesOk.bind_ok h
    cases he
  | true => ?_
  simp only [hdn, ↓reduceIte] at h
  obtain ⟨gs, hgs, h⟩ := Lam.ModesOk.bind_ok h
  cases h
  exact ⟨rfl, gs, hgs, rfl⟩

/-- P1's output has the ids `0 … size - 1`. -/
theorem convert_wf {L : Lam.Program} {Q : Program} (h : convert L = .ok Q) : Q.WF := by
  obtain ⟨-, hsize, -, -, -, -, hgl⟩ := Convert.Proof.convert_spec h
  obtain ⟨hdense, gs, hgs, rfl⟩ := convert_unfold h
  refine ⟨fun g gd hg => ?_, fun g hg => ?_⟩
  · obtain ⟨hlen, hall⟩ := Lam.ModesOk.mapM_ok hgs
    have hkeys : gs.map (·.1) = L.globalList.map (·.1) := by
      apply List.ext_getElem?
      intro j
      simp only [List.getElem?_map]
      cases hj : L.globalList[j]? with
      | none =>
        have : gs[j]? = none := by rw [List.getElem?_eq_none_iff] at hj ⊢; omega
        simp [this]
      | some p =>
        obtain ⟨y', hy', hf'⟩ := hall j p hj
        obtain ⟨gd', _, hret'⟩ := Lam.ModesOk.bind_ok hf'
        cases hret'
        simp [hy']
    have hn : (gs.map (·.1)).Nodup := by rw [hkeys]; exact Lam.Program.globalList_keys_nodup L
    have hmem := Convert.Proof.natMap_ofList_mem hn hg
    have : g ∈ L.globalList.map (·.1) := by rw [← hkeys]; exact List.mem_map.2 ⟨_, hmem, rfl⟩
    obtain ⟨⟨g', gl⟩, hgl', rfl⟩ := List.mem_map.1 this
    exact (Lam.Program.mem_globalList.1 hgl').1
  · have := List.all_eq_true.1 hdense g (List.mem_range.2 hg)
    obtain ⟨gl, hgl'⟩ := Option.isSome_iff_exists.1 this
    obtain ⟨gd, hgd, -⟩ := hgl g gl hgl' hg
    exact ⟨gd, hgd⟩

/-- The size check passes its program through unchanged. -/
theorem checkGlobalNodes_ok {P Q : Program} (h : checkGlobalNodes P = .ok Q) : Q = P := by
  unfold checkGlobalNodes at h
  split at h
  · cases h; rfl
  · cases h

/-- The Lam size check passes its program through unchanged. -/
theorem checkLamNodes_ok {L L' : Lam.Program} (h : checkLamNodes L = .ok L') : L = L' := by
  unfold checkLamNodes at h
  split at h
  · cases h; rfl
  · cases h

/-- P4's correctness: every certificate the re-run accepts gives a
refinement of the input with ids `0 … size - 1`. -/
def SpecCorrect : Prop :=
  ∀ (c : Specialize.Cert) (P Q : Program), P.WF → Specialize.run c P = .ok Q → Q.WF ∧ Sem.Refines P Q

/-- **P4 is correct** (`Specialize.Proof.run_refines`). -/
theorem spec_correct : SpecCorrect := fun _ _ _ hw h => Specialize.Proof.run_refines hw h

/-- A step other than P4. -/
def Step.NoSpec : Step → Prop
  | .specialize _ => False
  | _ => True

theorem step_correct (p : Shrink.Params) :
    ∀ (s : Step) (P Q : Program), (Step.NoSpec s ∨ SpecCorrect) → P.WF → s.run p P = .ok Q →
      Q.WF ∧ Sem.Refines P Q
  | .shrink c, P, Q, _, hw, h => by
    simp only [Step.run] at h
    obtain ⟨x, hs, hc⟩ := Lam.ModesOk.bind_ok h
    cases checkGlobalNodes_ok hc
    exact Shrink.Proof.run_refines hw hs
  | .inline r, P, Q, _, hw, h => by
    simp only [Step.run] at h
    obtain ⟨x, hr, hc⟩ := Lam.ModesOk.bind_ok h
    unfold checkGlobalNodes at hc
    split at hc
    · cases hc
      exact Inline.Proof.round_refines hw hr
    · cases hc
  | .specialize c, P, Q, hs, hw, h => by
    rcases hs with hs | hs
    · exact hs.elim
    · simp only [Step.run] at h
      obtain ⟨x, hspec, hc⟩ := Lam.ModesOk.bind_ok h
      unfold checkGlobalNodes at hc
      split at hc
      · cases hc
        exact hs c P Q hw hspec
      · cases hc
  | .prune, P, Q, _, hw, h => by
    simp only [Step.run] at h
    cases h
    exact Prune.Proof.run_refines hw

theorem steps_correct (p : Shrink.Params) : ∀ (steps : List Step) (P Q : Program),
    (∀ s ∈ steps, Step.NoSpec s ∨ SpecCorrect) → P.WF →
    steps.foldlM (fun P s => s.run p P) P = .ok Q → Q.WF ∧ Sem.Refines P Q
  | [], P, Q, _, hw, h => by
    simp only [List.foldlM_nil] at h
    cases h
    exact ⟨hw, Sem.Refines.refl P⟩
  | s :: steps, P, Q, hs, hw, h => by
    simp only [List.foldlM_cons] at h
    obtain ⟨P1, h1, h2⟩ := Lam.ModesOk.bind_ok h
    obtain ⟨hw1, hr1⟩ := step_correct p s P P1 (hs s List.mem_cons_self) hw h1
    obtain ⟨hw2, hr2⟩ := steps_correct p steps P1 Q (fun s' hs' => hs s' (List.mem_cons_of_mem _ hs')) hw1 h2
    exact ⟨hw2, hr1.trans hr2⟩



/-- **The middle end is correct**: if the re-run accepts a certificate, its
output refines the Lam program. -/
theorem run_correct {cert : Cert} {L : Lam.Program} {Q : Program}
    (h : run cert L = .ok Q) : Sem.Refines L Q := by
  unfold run at h
  obtain ⟨P, h1, h2⟩ := Lam.ModesOk.bind_ok h
  obtain ⟨P0, h0, hc⟩ := Lam.ModesOk.bind_ok h1
  obtain ⟨L', hl, h0⟩ := Lam.ModesOk.bind_ok h0
  rw [← checkLamNodes_ok hl] at h0
  have hP : P = P0 := checkGlobalNodes_ok hc
  rw [hP] at h2
  exact (Convert.Proof.convert_refines h0).trans
    (steps_correct cert.shrink cert.steps P0 Q (fun _ _ => .inr spec_correct) (convert_wf h0) h2).2

/-- **The middle end is correct** for every certificate without P4 steps:
if the re-run accepts it, its output refines the Lam program. -/
theorem run_correct_noSpec {cert : Cert} (hno : ∀ s ∈ cert.steps, Step.NoSpec s) {L : Lam.Program}
    {Q : Program} (h : run cert L = .ok Q) : Sem.Refines L Q := by
  unfold run at h
  obtain ⟨P, h1, h2⟩ := Lam.ModesOk.bind_ok h
  obtain ⟨P0, h0, hc⟩ := Lam.ModesOk.bind_ok h1
  obtain ⟨L', hl, h0⟩ := Lam.ModesOk.bind_ok h0
  rw [← checkLamNodes_ok hl] at h0
  have hP : P = P0 := checkGlobalNodes_ok hc
  rw [hP] at h2
  exact (Convert.Proof.convert_refines h0).trans
    (steps_correct cert.shrink cert.steps P0 Q (fun s hs => .inl (hno s hs)) (convert_wf h0) h2).2

/-! ## The traced shape (decision D-1) -/

theorem run_correct_traced {cert : Cert} {L : Lam.Program} {Q : Program}
    (h : run cert L = .ok Q) : Sem.TRefines L Q :=
  Sem.Refines.ofPure (run_correct h)

theorem run_correct_noSpec_traced {cert : Cert} (hno : ∀ s ∈ cert.steps, Step.NoSpec s) {L : Lam.Program}
    {Q : Program} (h : run cert L = .ok Q) : Sem.TRefines L Q :=
  Sem.Refines.ofPure (run_correct_noSpec hno h)

end IxCC.Anf.Pipeline.Proof
