module

public import IxC.Kernel.Cached.Policy
public import IxC.Kernel.Verify.Cached.AgreeFloor

public section

/-!
# The strict fold is the user-axiom fold without user axioms

`IxC/Kernel/Cached/Policy.lean` proves that, over records none of which is a
user axiom, the fold under any axiom policy is the certified fold `checkDecls`
(`checkDeclsUnder_eq_checkDecls`). This module proves the converse: the
certified fold accepts no user axiom, because its axiom arm admits only
role-keyed axioms (`checkStdAxiomDeclC_eligible`). Together,
`checkDecls_iff_userAxioms`: the certified fold accepts exactly what the fold
that admits user axioms accepts without any. So a host may run the
user-axiom fold alone: an accept whose user axioms are none is the certified
fold's accept, and nothing the certified fold accepts is lost.
-/

namespace Ix.Kernel.Cached

open Ix.Kernel

variable {ev : Evidences md}

/-- **The strict axiom arm declines every eligible key**: an eligible key is no
role key, so it is not `Quot.sound`, `propext`, `Classical.choice` or `sorryAx`,
and every other axiom declines. -/
theorem checkStdAxiomDeclC_eligible (mode : CheckMode) (fe : FEnv md) (cv : ConstantVal md)
    (h : cv.name.isCustomAxiomEligible = true) :
    Yields (checkStdAxiomDeclC mode fe cv) (fun _ => False) := by
  unfold checkStdAxiomDeclC
  rw [if_neg (Key.isCustomAxiomEligible_ne_quotSound h)]
  refine Yields.bind' (checkConstantValC_name mode fe cv) fun p hp => ?_
  obtain ⟨cvA, jty⟩ := p
  have hn : cvA.name = cv.name := hp
  have hpx : ¬cvA.name = propextName := by rw [hn]; exact Key.isCustomAxiomEligible_ne_propext h
  have hch : ¬cvA.name = choiceName := by rw [hn]; exact Key.isCustomAxiomEligible_ne_choice h
  have hso : ¬cvA.name = sorryAxName := by rw [hn]; exact Key.isCustomAxiomEligible_ne_sorryAx h
  have hstd : ¬stdAxiomOkF fe cvA = true := by
    unfold stdAxiomOkF
    rw [if_neg hpx, if_neg hch]
    exact Bool.false_ne_true
  dsimp only
  rw [if_neg hstd, if_neg (fun h' => h'.elim hpx hch), if_neg hso]
  exact Yields.ofThrow

/-- The certified fold's step declines a user axiom. -/
theorem annotDeclStep_userAxiom (mode : CheckMode) (p : Nat × FEnv md × Array (PendingCheck md))
    {cv : ConstantVal md} (h : cv.name.isCustomAxiomEligible = true) (s : CState md)
    (q : Nat × FEnv md × Array (PendingCheck md)) (s' : CState md) :
    annotDeclStep mode ev p (.axiomDecl cv) s ≠ .ok (q, s') := by
  intro hok
  obtain ⟨fe', pend', -, hstep⟩ := annotDeclStep_ok hok
  have hy : Yields (checkDeclStepC mode ev p.2.1 (.axiomDecl cv)) (fun _ => False) := by
    unfold checkDeclStepC
    ybind
    rw [checkDeclC_axiomDecl]
    exact checkStdAxiomDeclC_eligible mode p.2.1 cv h
  have hy' : Yields (annotStepC mode ev p.1 p.2.1 p.2.2 (.axiomDecl cv)) (fun _ => False) :=
    Yields.bind' hy fun _ hf => hf.elim
  exact hy' s (fe', pend') s' hstep

/-- An accepting phase-A run accepted a step at each of its records. -/
theorem InstallRun.step_of_mem {mode : CheckMode} {ds : List (Declaration md)}
    {p p' : Nat × FEnv md × Array (PendingCheck md)} {s s' : CState md}
    (r : InstallRun mode ev ds p s p' s') :
    ∀ pd ∈ ds, ∃ q s₀ q' s₀', annotDeclStep mode ev q pd s₀ = .ok (q', s₀') := by
  induction r with
  | nil => intro pd hpd; exact absurd hpd List.not_mem_nil
  | cons hstep _ ih =>
    intro pd hpd
    rcases List.mem_cons.mp hpd with rfl | hpd
    · exact ⟨_, _, _, _, hstep⟩
    · exact ih pd hpd

/-- **The certified fold accepts no user axiom.** -/
theorem checkDecls_userAxioms_nil {mode : CheckMode} {ds : Array (Declaration md)} {env : Env md}
    (h : checkDecls mode ev ds = .ok env) : userAxiomsOfDecls ds.toList = [] := by
  obtain ⟨fc, -⟩ := checkDecls_fullyChecked mode h
  obtain ⟨n, s, r⟩ := fc.1.run
  refine List.eq_nil_iff_forall_not_mem.mpr fun cv hcv => ?_
  obtain ⟨hmem, helig⟩ := mem_userAxiomsOfDecls_iff.mp hcv
  obtain ⟨q, s₀, q', s₀', hok⟩ := r.step_of_mem _ hmem
  exact annotDeclStep_userAxiom mode q helig s₀ q' s₀' hok

/-- **The certified fold is the user-axiom fold without user axioms**:
`checkDecls` accepts exactly when `checkDeclsWithUserAxioms` accepts with the
same environment and the records declare no user axiom. -/
theorem checkDecls_iff_userAxioms (mode : CheckMode) (ds : Array (Declaration md)) (env : Env md) :
    checkDecls mode ev ds = .ok env ↔
      checkDeclsWithUserAxioms mode ev ds = .ok env ∧ userAxiomsOfDecls ds.toList = [] := by
  constructor
  · intro h
    have hnone := checkDecls_userAxioms_nil h
    exact ⟨by rw [checkDeclsWithUserAxioms_eq_checkDecls mode ev ds hnone]; exact h, hnone⟩
  · rintro ⟨h, hnone⟩
    rw [checkDeclsWithUserAxioms_eq_checkDecls mode ev ds hnone] at h
    exact h

end Ix.Kernel.Cached
