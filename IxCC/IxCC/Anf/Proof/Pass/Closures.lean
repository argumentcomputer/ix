import IxCC.Anf.Pipeline.Closures
import IxCC.Anf.Proof.Entry
import IxCC.Anf.Proof.Pass.Pipeline
import IxCC.Fir.Proof.FirstOrder

/-! # The closures step is correct

`closures_correct`: on a program whose ids are `0 … size - 1` (what the
certificate's middle end gives, `run_wf`), the closures step's output has
that shape, is first order, and refines its input on every input of the
declared count: unchanged when plain; otherwise the entries refine on those
inputs (`Entry.Proof.run_refines`), make them inputs of exactly their root's
arity (`Entry.Proof.run_exactArity`), on which P8 refines
(`Defun.Proof.correct`), and the size check passes its program through.

`fir.closures` is unreachable after the step (`closures_lower_ne_closures`),
and the step changes nothing that `Fir.lower` accepted with its roots at
their declared counts (`closures_of_lower`). The pinned keys are kept and
the constructor table only grows by closure rows (`closures_tables`), which
is what the readback reads. -/

set_option autoImplicit false

namespace IxCC.Anf.Pipeline.Proof

open IxCC.Anf.PassProof

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

theorem closures_of_plain {decl : List Nat} {P : Program} (h : plain decl P = true) :
    closures decl P = .ok P := by
  simp [closures, h]

/-- What a successful step is made of. -/
theorem closures_cases {decl : List Nat} {P Q : Program} (h : closures decl P = .ok Q) :
    (plain decl P = true ∧ Q = P) ∨
      ∃ E Q8, Entry.run decl P = .ok E ∧ Anf.defun E = .ok Q8 ∧ checkGlobalNodes Q8 = .ok Q := by
  unfold closures at h
  split at h
  · rename_i hp
    cases h
    exact .inl ⟨hp, rfl⟩
  · right
    obtain ⟨E, hE, h2⟩ := Lam.ModesOk.bind_ok h
    obtain ⟨Q8, h8, hc⟩ := Lam.ModesOk.bind_ok h2
    refine ⟨E, Q8, ?_, h8, hc⟩
    cases he : Entry.run decl P with
    | error e => rw [he] at hE; cases hE
    | ok E' => rw [he] at hE; cases hE; rfl

/-- The output of the step is first order. -/
theorem closures_firstOrder {decl : List Nat} {P Q : Program} (h : closures decl P = .ok Q) :
    Anf.FirstOrder Q := by
  rcases closures_cases h with ⟨hp, rfl⟩ | ⟨E, Q8, -, h8, hc⟩
  · simp only [plain, Bool.and_eq_true] at hp
    exact hp.1
  · rw [checkGlobalNodes_ok hc]
    exact Defun.Proof.defun_firstOrder h8

/-- **The closures step is correct**: ids `0 … size - 1`, first order, and
a refinement of its input on every input of the declared count. -/
theorem closures_correct {decl : List Nat} {P Q : Program} (hw : P.WF) (h : closures decl P = .ok Q) :
    Q.WF ∧ Anf.FirstOrder Q ∧ Sem.RefinesOn (Entry.DeclExact decl) P Q := by
  refine ⟨?_, closures_firstOrder h, ?_⟩ <;>
    rcases closures_cases h with ⟨-, rfl⟩ | ⟨E, Q8, he, h8, hc⟩
  · exact hw
  · rw [checkGlobalNodes_ok hc]
    exact (Defun.Proof.step_correct (Entry.Proof.run_wf hw he) h8).1
  · exact (Sem.Refines.refl _).on _
  · rw [checkGlobalNodes_ok hc]
    have hwE := Entry.Proof.run_wf hw he
    have h8r := (Defun.Proof.step_correct hwE h8).2
    exact (Entry.Proof.run_refines hw he).trans
      (h8r.mono fun i hi => Entry.Proof.run_exactArity hw he hi)

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
theorem closures_tables {decl : List Nat} {P Q : Program} (h : closures decl P = .ok Q) :
    Q.known = P.known ∧ ∃ rs, Q.ctors = P.ctors ++ rs ∧ ∀ r ∈ rs, ∃ f j, r.key = .clo f j := by
  rcases closures_cases h with ⟨-, rfl⟩ | ⟨E, Q8, he, h8, hc⟩
  · exact ⟨rfl, [], by simp, by simp⟩
  · rw [checkGlobalNodes_ok hc]
    obtain ⟨hk, hct⟩ := Entry.Proof.run_tables he
    obtain ⟨gs, acc, parents, -, rfl⟩ := Defun.Proof.run_ran (Defun.Proof.defun_run h8)
    exact ⟨hk, _, by rw [← hct]; rfl, rows_keys _ _⟩

/-- **`fir.closures` is unreachable after the closures step.** -/
theorem closures_lower_ne_closures {decl : List Nat} {P Q : Program} (h : closures decl P = .ok Q)
    (fns apps globs : List GlobalId) : Fir.lower Q ≠ .error (.closures fns apps globs) :=
  Fir.Proof.lower_ne_closures (closures_firstOrder h) fns apps globs

/-- **No silent change**: a program `Fir.lower` accepts whose roots take their
declared counts passes the step unchanged. -/
theorem closures_of_lower {decl : List Nat} {P : Program} {F : Fir.Program} (hl : Fir.lower P = .ok F)
    (hr : rootsAgree decl P = true) : closures decl P = .ok P :=
  closures_of_plain (by simp only [plain, Bool.and_eq_true]; exact ⟨Fir.Proof.lower_ok_firstOrder hl, hr⟩)

end IxCC.Anf.Pipeline.Proof
