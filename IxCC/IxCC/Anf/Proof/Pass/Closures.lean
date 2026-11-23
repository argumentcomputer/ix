import IxCC.Anf.Pipeline.Closures
import IxCC.Anf.Proof.Entry
import IxCC.Anf.Proof.Pass.Pipeline
import IxCC.Anf.Proof.Pass.FirstOrder
import IxCC.Anf.Proof.Pass.DeadParam
import IxCC.Anf.Proof.Defun.Narrow
import IxCC.Fir.Proof.FirstOrder

/-! # The closures step is correct

`closures_correct`: on a program whose ids are `0 … size - 1` (what the
certificate's middle end gives, `run_wf`), the closures step's output has
that shape, is first order, and refines its input on every input of the
declared count: unchanged when plain; otherwise the entries refine on those
inputs (`Entry.Proof.run_refines`), make them inputs of exactly their root's
arity (`Entry.Proof.run_exactArity`), on which P8 refines (`Defun.Proof.correct`),
and the post-P8 optimization steps (`runPost`: known-dispatch P2 shrink, post-P8
P3 inline, pruning, P9 flow-directed dispatch narrowing, P5 dead-parameter
stripping, and the size check) each preserve `WF`, `FirstOrder`, tables, and
refine their input.

`fir.closures` is unreachable after the step (`closures_lower_ne_closures`),
and the step changes nothing that `Fir.lower` accepted with its roots at
their declared counts (`closures_of_lower`). The pinned keys are kept and
the constructor table only grows by closure rows (`closures_tables`), which
is what the readback reads. -/

set_option autoImplicit false

namespace IxCC.Anf.Pipeline.Proof

open IxCC.Anf.PassProof

/-! ## Post-P8 step tables (strictly `[propext]`, no `Classical.choice`) -/

private theorem shrink_tables {p : Shrink.Params} {c : Shrink.Cert} {P Q : Program}
    (h : Shrink.run p c P = .ok Q) : Q.known = P.known ∧ Q.ctors = P.ctors := by
  unfold Shrink.run at h
  obtain ⟨gs, -, h⟩ := Lam.ModesOk.bind_ok h
  cases h
  exact ⟨rfl, rfl⟩

private theorem inline_tables {P Q : Program} {r : Inline.Round} {f : Walk.Fires}
    (h : Inline.round P r = .ok (Q, f)) : Q.known = P.known ∧ Q.ctors = P.ctors := by
  unfold Inline.round at h
  obtain ⟨rs, -, h⟩ := Lam.ModesOk.bind_ok h
  cases h
  exact ⟨rfl, rfl⟩

theorem postStep_tables {prm : Shrink.Params} {s : PostStep} {P Q : Program}
    (h : s.run prm P = .ok Q) : Q.known = P.known ∧ Q.ctors = P.ctors := by
  cases s with
  | shrink c =>
    simp only [PostStep.run] at h
    split at h
    · obtain ⟨P1, hs, hc⟩ := Lam.ModesOk.bind_ok h
      rw [checkGlobalNodes_ok hc]
      exact shrink_tables hs
    · cases h
  | inline r =>
    simp only [PostStep.run] at h
    split at h
    · obtain ⟨x, hr, hc⟩ := Lam.ModesOk.bind_ok h
      rw [checkGlobalNodes_ok hc]
      exact inline_tables hr
    · cases h
  | prune =>
    simp only [PostStep.run, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact prune_tables P
  | narrow c =>
    simp only [PostStep.run] at h
    rw [checkGlobalNodes_ok h]
    have ht := Defun.Narrow.Proof.run_tables c P
    exact ⟨ht.1, ht.2.1⟩
  | deadParam =>
    simp only [PostStep.run] at h
    rw [checkGlobalNodes_ok h]
    exact DeadParam.Proof.run_tables P

theorem postSteps_tables (prm : Shrink.Params) :
    ∀ (steps : List PostStep) (P Q : Program),
      steps.foldlM (fun Q s => s.run prm Q) P = .ok Q →
      Q.known = P.known ∧ Q.ctors = P.ctors
  | [], P, Q, h => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact ⟨rfl, rfl⟩
  | s :: rest, P, Q, h => by
    simp only [List.foldlM_cons] at h
    obtain ⟨P1, h1, h2⟩ := Lam.ModesOk.bind_ok h
    obtain ⟨hk1, hc1⟩ := postStep_tables h1
    obtain ⟨hk2, hc2⟩ := postSteps_tables prm rest P1 Q h2
    exact ⟨hk2.trans hk1, hc2.trans hc1⟩

theorem runPost_tables {pc : PostCert} {P Q : Program} (h : runPost pc P = .ok Q) :
    Q.known = P.known ∧ Q.ctors = P.ctors := by
  unfold runPost at h
  cases hs : pc.steps with
  | nil =>
    rw [hs] at h
    rw [checkGlobalNodes_ok h]
    exact ⟨rfl, rfl⟩
  | cons s rest =>
    rw [hs] at h
    obtain ⟨P1, h1, h2⟩ := Lam.ModesOk.bind_ok h
    split at h2
    · rw [checkGlobalNodes_ok h2]
      exact postSteps_tables pc.shrink (s :: rest) P P1 h1
    · cases h2

/-! ## Post-P8 step correctness (`WF`, `FirstOrder`, `Sem.Refines`) -/

theorem postStep_correct (prm : Shrink.Params) (s : PostStep) (P Q : Program)
    (hw : P.WF) (hfo : Anf.FirstOrder P) (h : s.run prm P = .ok Q) :
    Q.WF ∧ Anf.FirstOrder Q ∧ Sem.Refines P Q := by
  cases s with
  | shrink c =>
    simp only [PostStep.run] at h
    split at h
    · obtain ⟨P1, hs, hc⟩ := Lam.ModesOk.bind_ok h
      rw [checkGlobalNodes_ok hc]
      obtain ⟨hw1, href⟩ := Shrink.Proof.run_refines hw hs
      exact ⟨hw1, shrink_firstOrder hw hfo hs, href⟩
    · cases h
  | inline r =>
    simp only [PostStep.run] at h
    split at h
    · obtain ⟨⟨P1, f⟩, hr, hc⟩ := Lam.ModesOk.bind_ok h
      rw [checkGlobalNodes_ok hc]
      obtain ⟨hw1, href⟩ := Inline.Proof.round_refines hw hr
      exact ⟨hw1, inline_firstOrder hw hfo hr, href⟩
    · cases h
  | prune =>
    simp only [PostStep.run, pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨hw1, href⟩ := Prune.Proof.run_refines hw
    exact ⟨hw1, prune_firstOrder hw hfo, href⟩
  | narrow c =>
    simp only [PostStep.run] at h
    rw [checkGlobalNodes_ok h]
    obtain ⟨hw1, href⟩ := Defun.Narrow.Proof.run_refines (c := c) hw
    exact ⟨hw1, Defun.Narrow.Proof.run_firstOrder hw hfo, href⟩
  | deadParam =>
    simp only [PostStep.run] at h
    rw [checkGlobalNodes_ok h]
    obtain ⟨hw1, href⟩ := DeadParam.Proof.run_refines hw
    exact ⟨hw1, DeadParam.Proof.run_firstOrder hw hfo, href⟩

theorem postSteps_correct (prm : Shrink.Params) :
    ∀ (steps : List PostStep) (P Q : Program),
      P.WF → Anf.FirstOrder P →
      steps.foldlM (fun Q s => s.run prm Q) P = .ok Q →
      Q.WF ∧ Anf.FirstOrder Q ∧ Sem.Refines P Q
  | [], P, Q, hw, hfo, h => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact ⟨hw, hfo, Sem.Refines.refl P⟩
  | s :: rest, P, Q, hw, hfo, h => by
    simp only [List.foldlM_cons] at h
    obtain ⟨P1, h1, h2⟩ := Lam.ModesOk.bind_ok h
    obtain ⟨hw1, hfo1, href1⟩ := postStep_correct prm s P P1 hw hfo h1
    obtain ⟨hw2, hfo2, href2⟩ := postSteps_correct prm rest P1 Q hw1 hfo1 h2
    exact ⟨hw2, hfo2, href1.trans href2⟩

theorem runPost_firstOrder {pc : PostCert} {P Q : Program}
    (hfo : Anf.FirstOrder P) (h : runPost pc P = .ok Q) : Anf.FirstOrder Q := by
  unfold runPost at h
  cases hs : pc.steps with
  | nil =>
    rw [hs] at h
    rw [checkGlobalNodes_ok h]
    exact hfo
  | cons s rest =>
    rw [hs] at h
    obtain ⟨P1, _, h2⟩ := Lam.ModesOk.bind_ok h
    split at h2
    · next hfo1 =>
      rw [checkGlobalNodes_ok h2]
      exact hfo1
    · cases h2

theorem runPost_correct {pc : PostCert} {P Q : Program}
    (hw : P.WF) (hfo : Anf.FirstOrder P) (h : runPost pc P = .ok Q) :
    Q.WF ∧ Anf.FirstOrder Q ∧ Sem.Refines P Q := by
  unfold runPost at h
  cases hs : pc.steps with
  | nil =>
    rw [hs] at h
    rw [checkGlobalNodes_ok h]
    exact ⟨hw, hfo, Sem.Refines.refl P⟩
  | cons s rest =>
    rw [hs] at h
    obtain ⟨P1, h1, h2⟩ := Lam.ModesOk.bind_ok h
    split at h2
    · rw [checkGlobalNodes_ok h2]
      exact postSteps_correct pc.shrink (s :: rest) P P1 hw hfo h1
    · cases h2

/-! ## The closures step -/

/-- The certificate's middle end gives ids `0 … size - 1`. -/
theorem run_wf {cert : Cert} {L : Lam.Program} {Q : Program} (h : run cert L = .ok Q) : Q.WF := by
  unfold run at h
  obtain ⟨P, h1, h2⟩ := Lam.ModesOk.bind_ok h
  obtain ⟨P0, h0, hc⟩ := Lam.ModesOk.bind_ok h1
  obtain ⟨L', hl, h0⟩ := Lam.ModesOk.bind_ok h0
  rw [← checkLamNodes_ok hl] at h0
  have hP : P = P0 := checkGlobalNodes_ok hc
  rw [hP] at h2
  exact (steps_correct cert.shrink cert.steps P0 Q (fun _ _ => .inr spec_correct) (convert_wf h0) h2).1

theorem closures_of_plain {decl : List Nat} {P : Program} {post : Option PostCert}
    (h : plain decl P = true) : closures decl P post = .ok P := by
  simp [closures, h]

/-- What a successful step is made of. -/
theorem closures_cases {decl : List Nat} {P Q : Program} {post : Option PostCert}
    (h : closures decl P post = .ok Q) :
    (plain decl P = true ∧ Q = P) ∨
      ∃ E Q8 pc, Entry.run decl P = .ok E ∧ Anf.defun E = .ok Q8 ∧ runPost pc Q8 = .ok Q := by
  unfold closures at h
  split at h
  · rename_i hp
    cases h
    exact .inl ⟨hp, rfl⟩
  · right
    obtain ⟨E, hE, h2⟩ := Lam.ModesOk.bind_ok h
    obtain ⟨Q8, h8, hr⟩ := Lam.ModesOk.bind_ok h2
    refine ⟨E, Q8, _, ?_, h8, hr⟩
    cases he : Entry.run decl P with
    | error e => rw [he] at hE; cases hE
    | ok E' => rw [he] at hE; cases hE; rfl

/-- The output of the step is first order. -/
theorem closures_firstOrder {decl : List Nat} {P Q : Program} {post : Option PostCert}
    (h : closures decl P post = .ok Q) : Anf.FirstOrder Q := by
  rcases closures_cases h with ⟨hp, rfl⟩ | ⟨E, Q8, pc, -, h8, hr⟩
  · simp only [plain, Bool.and_eq_true] at hp
    exact hp.1
  · exact runPost_firstOrder (Defun.Proof.defun_firstOrder h8) hr

/-- **The closures step is correct**: ids `0 … size - 1`, first order, and
a refinement of its input on every input of the declared count. -/
theorem closures_correct {decl : List Nat} {P Q : Program} {post : Option PostCert}
    (hw : P.WF) (h : closures decl P post = .ok Q) :
    Q.WF ∧ Anf.FirstOrder Q ∧ Sem.RefinesOn (Entry.DeclExact decl) P Q := by
  rcases closures_cases h with ⟨hp, rfl⟩ | ⟨E, Q8, pc, he, h8, hr⟩
  · simp only [plain, Bool.and_eq_true] at hp
    exact ⟨hw, hp.1, (Sem.Refines.refl _).on _⟩
  · have hwE := Entry.Proof.run_wf hw he
    have h8c := Defun.Proof.step_correct hwE h8
    have h8fo := Defun.Proof.defun_firstOrder h8
    obtain ⟨hwQ, hfoQ, hpostR⟩ := runPost_correct h8c.1 h8fo hr
    refine ⟨hwQ, hfoQ, ?_⟩
    exact ((Entry.Proof.run_refines hw he).trans
      (h8c.2.mono fun i hi => Entry.Proof.run_exactArity hw he hi)).trans_refines hpostR

theorem rows_keys : ∀ (srcs : List Defun.Source) (tag : Nat), ∀ r ∈ Defun.rows srcs tag,
    ∃ f j, r.key = .clo f j
  | [], _, r, h => by simp [Defun.rows] at h
  | s :: ss, tag, r, h => by
    simp only [Defun.rows, List.mem_append, List.mem_map, List.mem_range] at h
    rcases h with ⟨j, -, rfl⟩ | h
    · exact ⟨s.key, j, rfl⟩
    · exact rows_keys ss _ r h

/-- What the readback reads is kept: the pinned keys, and the constructor
table up to closure rows appended. -/
theorem closures_tables {decl : List Nat} {P Q : Program} {post : Option PostCert}
    (h : closures decl P post = .ok Q) :
    Q.known = P.known ∧ ∃ rs, Q.ctors = P.ctors ++ rs ∧ ∀ r ∈ rs, ∃ f j, r.key = .clo f j := by
  rcases closures_cases h with ⟨-, rfl⟩ | ⟨E, Q8, pc, he, h8, hr⟩
  · exact ⟨rfl, [], by simp, by simp⟩
  · obtain ⟨hpk, hpct⟩ := runPost_tables hr
    obtain ⟨hk, hct⟩ := Entry.Proof.run_tables he
    obtain ⟨gs, acc, parents, -, rfl⟩ := Defun.Proof.run_ran (Defun.Proof.defun_run h8)
    exact ⟨hpk.trans hk, _, by rw [hpct, ← hct]; rfl, rows_keys _ _⟩

/-- **`fir.closures` is unreachable after the closures step.** -/
theorem closures_lower_ne_closures {decl : List Nat} {P Q : Program} {post : Option PostCert}
    (h : closures decl P post = .ok Q)
    (fns apps globs : List GlobalId) : Fir.lower Q ≠ .error (.closures fns apps globs) :=
  Fir.Proof.lower_ne_closures (closures_firstOrder h) fns apps globs

/-- **No silent change**: a program `Fir.lower` accepts whose roots take their
declared counts passes the step unchanged. -/
theorem closures_of_lower {decl : List Nat} {P : Program} {post : Option PostCert} {F : Fir.Program}
    (hl : Fir.lower P = .ok F) (hr : rootsAgree decl P = true) :
    closures decl P post = .ok P :=
  closures_of_plain (by simp only [plain, Bool.and_eq_true]; exact ⟨Fir.Proof.lower_ok_firstOrder hl, hr⟩)

end IxCC.Anf.Pipeline.Proof
