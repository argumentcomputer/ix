module

public import ConLeche.Semantics.DeclIndRun
public import ConLeche.Semantics.IndBlockFacts

@[expose] public section

/-!
# The inductive block's syntactic residue, on the **run** records
(task #161 S11b, THE SEPARATION)

`SetBase/IndBlockR.lean` collects what the block folds *preserve* —
monotonicity, freshness, the name guards, the stored entries, the
η-closure — and states it over the `DeclIndRun` family.  The graded lane
consumes those facts, and since S11b it consumes them from
`DeclIndRun` (`SetBase/DeclIndRun.lean`), so each one is re-stated
here at the run record.

**Every proof below is its `IndBlockR` twin's, with the valuation
column deleted.**  None of them ever read a `∀ φ` conjunct: they walk
`MemberValR`'s freshness guard and the folds' cons shapes, which is
exactly what survives the projection.  The duplication is
compile-time coupled in the way S11a recorded — both copies destructure
the same record shape, so a record change breaks both loudly — and it
is what route (a) buys instead of the run→derivation lemmas route (b)
would have owed (see `Bridge/DeclIndRun.lean`'s header for the
priced comparison).

-/

namespace ConLeche.Semantics

open ConLeche.Term ConLeche.Verify

/-! ## The projection fold -/

/-- The projection-function fold is an `ExtEta` extension, run half. -/
theorem projInstallRun_ext {μ : CheckMode} {F : Nat}
    {T ctorName : Name} {lps : List Name} {nP nF : Nat} :
    ∀ (idxs : List Nat) {env' env₄ : Env},
      ProjInstallRun μ F T ctorName lps nP nF env' idxs env₄ →
      ExtEta env' env₄ := by
  intro idxs
  induction idxs with
  | nil =>
    intro env' env₄ h
    subst h
    exact ExtEta.refl _
  | cons i rest ih =>
    intro env' env₄ h
    obtain ⟨env'', hstep, htail⟩ := h
    refine ExtEta.trans ?_ (ih htail)
    rcases hstep with hfn | ⟨-, rfl⟩
    · obtain ⟨cvj, mcv, mval, mhint, pty, rhsA, -, -, -, hfresh, -, -,
        -, -, -, -, -, -, -, -, -, -, rfl⟩ := hfn
      exact ExtEta.cons (Option.isNone_iff_eq_none.mp hfresh)
        (fun _ _ hh => ConstantInfo.noConfusion hh)
    · exact ExtEta.refl _

/-! ## The provisioning's syntactic residue -/

/-- Provisioning only extends, run half. -/
theorem provisionRecsRunS_mono {μ : CheckMode} {F : Nat}
    {blockNames : List Name} :
    ∀ (recs : List ConstantInfo) {envAcc envSelf : Env}
      {checked : List (ConstantVal × Nat × Nat × List RecRule)},
      ProvisionRecsRun μ F blockNames envAcc recs envSelf checked →
      ∀ (n : Name) (ci : ConstantInfo),
        envAcc.find? n = some ci → envSelf.find? n = some ci := by
  intro recs
  induction recs with
  | nil =>
    intro envAcc envSelf checked h n ci hf
    obtain ⟨rfl, -⟩ := h
    exact hf
  | cons ci₀ rest ih =>
    intro envAcc envSelf checked h n ci hf
    obtain ⟨cvA, mI, rP, rules, rest', -, hmv, hrec, -⟩ := h
    obtain ⟨type', ⟨hfresh, -, -, -, -, -, -, -, -, -⟩, rfl, -⟩ := hmv
    exact ih hrec n ci (Env.find?_cons_of_fresh
      (c := .recInfo _ mI rP []) (Option.isNone_iff_eq_none.mp hfresh)
      hf)

/-- No provisioned member is stored *before* the fold runs, run half. -/
theorem provisionRecsRunS_fresh {μ : CheckMode} {F : Nat}
    {blockNames : List Name} :
    ∀ (recs : List ConstantInfo) {envAcc envSelf : Env}
      {checked : List (ConstantVal × Nat × Nat × List RecRule)},
      ProvisionRecsRun μ F blockNames envAcc recs envSelf checked →
      ∀ ci ∈ recs, envAcc.find? ci.name = none := by
  intro recs
  induction recs with
  | nil =>
    intro envAcc envSelf checked h ci hci
    exact nomatch hci
  | cons ci₀ rest ih =>
    intro envAcc envSelf checked h ci hci
    obtain ⟨cvA, mI, rP, rules, rest', -, hmv, hprov', -⟩ := h
    obtain ⟨type', hcv, hcvA, -⟩ := id hmv
    have hnameA : cvA.name = ci₀.name := by rw [hcvA]; rfl
    have hfresh : envAcc.find? cvA.name = none := by
      rw [hnameA]
      exact Option.isNone_iff_eq_none.mp hcv.1
    rcases List.mem_cons.mp hci with heq | hci'
    · rw [heq, ← hnameA]; exact hfresh
    · rcases hf : envAcc.find? ci.name with _ | ci₂
      · rfl
      · exfalso
        have hnone := ih hprov' ci hci'
        rw [Env.find?_cons_of_fresh (c := .recInfo cvA mI rP [])
          hfresh hf] at hnone
        exact nomatch hnone

/-- Each provisioned member's name passes the two name guards, run
half. -/
theorem provisionRecsRunS_nameGuards {μ : CheckMode} {F : Nat}
    {blockNames : List Name} :
    ∀ (recs : List ConstantInfo) {envAcc envSelf : Env}
      {checked : List (ConstantVal × Nat × Nat × List RecRule)},
      ProvisionRecsRun μ F blockNames envAcc recs envSelf checked →
      ∀ ci ∈ recs, ci.name.isProjFnShape = false ∧
        reservedBasisNames.contains ci.name = false := by
  intro recs
  induction recs with
  | nil =>
    intro envAcc envSelf checked h ci hci
    exact nomatch hci
  | cons ci₀ rest ih =>
    intro envAcc envSelf checked h ci hci
    obtain ⟨cvA, mI, rP, rules, rest', -, hmv, hprov', -⟩ := h
    obtain ⟨type', hcv, -, -⟩ := id hmv
    rcases List.mem_cons.mp hci with heq | hci'
    · rw [heq]
      exact ⟨hcv.2.2.1, hcv.2.1⟩
    · exact ih hprov' ci hci'

/-- …and so does every group member's, run half. -/
theorem indRecsRun_nameGuards {μ : CheckMode} {F : Nat}
    {blockNames : List Name} {env₂ env₃ : Env}
    {recs : List ConstantInfo}
    (h : IndRecsRun μ F blockNames env₂ recs env₃) :
    ∀ ci ∈ recs, ci.name.isProjFnShape = false ∧
      reservedBasisNames.contains ci.name = false := by
  rcases h with ⟨rfl, -⟩ | ⟨-, -, envSelf, checked, hprov, -⟩
  · intro ci hci; exact nomatch hci
  · exact provisionRecsRunS_nameGuards recs hprov

/-- The install fold introduces no former, run half. -/
theorem indRecsFoldRun_noInd {μ : CheckMode} {F : Nat}
    {blockNames : List Name} {envBase envSelf : Env} :
    ∀ (checked : List (ConstantVal × Nat × Nat × List RecRule))
      {acc out : Env},
      IndRecsRun.IndRecsFoldRun μ F blockNames envBase envSelf
        acc checked out →
      ∀ (T : Name) (cvT : ConstantVal) (caps : IndCaps),
        out.find? T = some (.indInfo cvT caps) →
        acc.find? T = some (.indInfo cvT caps) := by
  intro checked
  induction checked with
  | nil =>
    intro acc out h T cvT caps hf
    subst h
    exact hf
  | cons c rest ih =>
    intro acc out h T cvT caps hf
    obtain ⟨rules', -, htail⟩ := h
    have h1 := ih htail T cvT caps hf
    rw [Env.find?_cons] at h1
    split at h1
    · exact ConstantInfo.noConfusion (Option.some.inj h1)
    · exact h1

/-- The recursor phase introduces no former, run half. -/
theorem indRecsRun_noInd {μ : CheckMode} {F : Nat}
    {blockNames : List Name} {env₂ env₃ : Env}
    {recs : List ConstantInfo}
    (h : IndRecsRun μ F blockNames env₂ recs env₃) :
    ∀ (T : Name) (cvT : ConstantVal) (caps : IndCaps),
      env₃.find? T = some (.indInfo cvT caps) →
      env₂.find? T = some (.indInfo cvT caps) := by
  rcases h with ⟨-, rfl⟩ | ⟨-, -, envSelf, checked, -, hfold⟩
  · exact fun _ _ _ hf => hf
  · exact indRecsFoldRun_noInd checked hfold

/-- No group member is stored before the group phase runs, run half. -/
theorem indRecsRun_fresh {μ : CheckMode} {F : Nat}
    {blockNames : List Name} {env₂ env₃ : Env}
    {recs : List ConstantInfo}
    (h : IndRecsRun μ F blockNames env₂ recs env₃) :
    ∀ ci ∈ recs, env₂.find? ci.name = none := by
  rcases h with ⟨rfl, -⟩ | ⟨-, -, envSelf, checked, hprov, -⟩
  · intro ci hci; exact nomatch hci
  · exact provisionRecsRunS_fresh recs hprov

/-- Every provisioned member is stored, run half. -/
theorem provisionRecsRunS_stored {μ : CheckMode} {F : Nat}
    {blockNames : List Name} :
    ∀ (recs : List ConstantInfo) {envAcc envSelf : Env}
      {checked : List (ConstantVal × Nat × Nat × List RecRule)},
      ProvisionRecsRun μ F blockNames envAcc recs envSelf checked →
      ∀ ci ∈ recs, (envSelf.find? ci.name).isSome = true := by
  intro recs
  induction recs with
  | nil =>
    intro envAcc envSelf checked h ci hci
    exact nomatch hci
  | cons ci₀ rest ih =>
    intro envAcc envSelf checked h ci hci
    obtain ⟨cvA, mI, rP, rules, rest', -, hmv, hprov', -⟩ := h
    obtain ⟨type', -, hcvAdef, -⟩ := hmv
    rcases List.mem_cons.mp hci with rfl | hci'
    · have : envSelf.find? cvA.name = some (.recInfo cvA mI rP []) :=
        provisionRecsRunS_mono rest hprov' _ _
          (Env.find?_cons_self (.recInfo cvA mI rP []) envAcc)
      rw [show ci.name = cvA.name by rw [hcvAdef]; rfl, this]
      rfl
    · exact ih hprov' ci hci'

/-- Provisioning only extends: stored entries stay stored, run half. -/
theorem provisionRecsRunS_mem {μ : CheckMode} {F : Nat}
    {blockNames : List Name} :
    ∀ (recs : List ConstantInfo) {envAcc envSelf : Env}
      {checked : List (ConstantVal × Nat × Nat × List RecRule)},
      ProvisionRecsRun μ F blockNames envAcc recs envSelf checked →
      ∀ c ∈ envAcc.consts, c ∈ envSelf.consts := by
  intro recs
  induction recs with
  | nil =>
    intro envAcc envSelf checked h c hc
    obtain ⟨rfl, -⟩ := h
    exact hc
  | cons ci₀ rest ih =>
    intro envAcc envSelf checked h c hc
    obtain ⟨cvA, mI, rP, rules, rest', -, -, hprov', -⟩ := h
    exact ih hprov' c (List.mem_cons_of_mem _ hc)

/-! ## The member fold's syntactic residue -/

/-- The member fold only extends, run half. -/
theorem indMembersRun_mono {μ : CheckMode} {F : Nat}
    {blockNames : List Name} {caps : IndCaps} :
    ∀ (members : List ConstantInfo) {env env₂ : Env},
      IndMembersRun μ F blockNames caps env members env₂ →
      ∀ (n : Name) (ci : ConstantInfo),
        env.find? n = some ci → env₂.find? n = some ci := by
  intro members
  induction members with
  | nil =>
    intro env env₂ h n ci hf
    subst h
    exact hf
  | cons ci₀ rest ih =>
    intro env env₂ h n ci hf
    obtain ⟨cvA, hmv, hmatch⟩ := h
    obtain ⟨type', hcv, hcvA, -⟩ := id hmv
    have hfresh : env.find? cvA.name = none := by
      rw [show cvA.name = ci₀.toConstantVal.name by rw [hcvA]]
      exact Option.isNone_iff_eq_none.mp hcv.1
    cases ci₀ with
    | indInfo cv caps' =>
      exact ih hmatch n ci
        (Env.find?_cons_of_fresh (c := .indInfo cvA caps) hfresh hf)
    | ctorInfo cv nP nF =>
      exact ih hmatch n ci
        (Env.find?_cons_of_fresh (c := .ctorInfo cvA nP nF) hfresh hf)
    | axiomInfo cv => exact nomatch hmatch
    | defnInfo cv v hint => exact nomatch hmatch
    | thmInfo cv v => exact nomatch hmatch
    | recInfo cv mI rP rules => exact nomatch hmatch
    | projInfo e => exact nomatch hmatch

/-- Every member the fold walks is stored at its end, run half. -/
theorem indMembersRun_stored {μ : CheckMode} {F : Nat}
    {blockNames : List Name} {caps : IndCaps} :
    ∀ (members : List ConstantInfo) {env env₂ : Env},
      IndMembersRun μ F blockNames caps env members env₂ →
      ∀ ci ∈ members, (env₂.find? ci.name).isSome = true := by
  intro members
  induction members with
  | nil =>
    intro env env₂ h ci hci
    exact nomatch hci
  | cons ci₀ rest ih =>
    intro env env₂ h ci hci
    obtain ⟨cvA, hmv, hmatch⟩ := h
    obtain ⟨type', hcv, hcvA, -⟩ := id hmv
    have hnameA : cvA.name = ci₀.name := by rw [hcvA]; rfl
    rcases List.mem_cons.mp hci with heq | hci'
    · rw [heq, ← hnameA]
      cases ci₀ with
      | indInfo cv caps' =>
        rw [show (env₂.find? cvA.name)
            = some (ConstantInfo.indInfo cvA caps) from
          indMembersRun_mono rest hmatch _ _
            (Env.find?_cons_self (.indInfo cvA caps) env)]
        rfl
      | ctorInfo cv nP nF =>
        rw [show (env₂.find? cvA.name)
            = some (ConstantInfo.ctorInfo cvA nP nF) from
          indMembersRun_mono rest hmatch _ _
            (Env.find?_cons_self (.ctorInfo cvA nP nF) env)]
        rfl
      | axiomInfo cv => exact nomatch hmatch
      | defnInfo cv v hint => exact nomatch hmatch
      | thmInfo cv v => exact nomatch hmatch
      | recInfo cv mI rP rules => exact nomatch hmatch
      | projInfo e => exact nomatch hmatch
    · cases ci₀ with
      | indInfo cv caps' => exact ih hmatch ci hci'
      | ctorInfo cv nP nF => exact ih hmatch ci hci'
      | axiomInfo cv => exact nomatch hmatch
      | defnInfo cv v hint => exact nomatch hmatch
      | thmInfo cv v => exact nomatch hmatch
      | recInfo cv mI rP rules => exact nomatch hmatch
      | projInfo e => exact nomatch hmatch

/-- No member is stored *before* the fold runs, run half. -/
theorem indMembersRun_fresh {μ : CheckMode} {F : Nat}
    {blockNames : List Name} {caps : IndCaps} :
    ∀ (members : List ConstantInfo) {env env₂ : Env},
      IndMembersRun μ F blockNames caps env members env₂ →
      ∀ ci ∈ members, env.find? ci.name = none := by
  intro members
  induction members with
  | nil =>
    intro env env₂ h ci hci
    exact nomatch hci
  | cons ci₀ rest ih =>
    intro env env₂ h ci hci
    obtain ⟨cvA, hmv, hmatch⟩ := h
    obtain ⟨type', hcv, hcvA, -⟩ := id hmv
    have hnameA : cvA.name = ci₀.name := by rw [hcvA]; rfl
    have hfresh : env.find? cvA.name = none := by
      rw [hnameA]
      exact Option.isNone_iff_eq_none.mp hcv.1
    rcases List.mem_cons.mp hci with heq | hci'
    · rw [heq, ← hnameA]; exact hfresh
    · rcases hf : env.find? ci.name with _ | ci₂
      · rfl
      · exfalso
        cases ci₀ with
        | indInfo cv caps' =>
          have hnone := ih hmatch ci hci'
          rw [Env.find?_cons_of_fresh (c := .indInfo cvA caps)
            hfresh hf] at hnone
          exact nomatch hnone
        | ctorInfo cv nP nF =>
          have hnone := ih hmatch ci hci'
          rw [Env.find?_cons_of_fresh (c := .ctorInfo cvA nP nF)
            hfresh hf] at hnone
          exact nomatch hnone
        | axiomInfo cv => exact nomatch hmatch
        | defnInfo cv v hint => exact nomatch hmatch
        | thmInfo cv v => exact nomatch hmatch
        | recInfo cv mI rP rules => exact nomatch hmatch
        | projInfo e => exact nomatch hmatch

/-- Each member's name passes the two name guards, run half. -/
theorem indMembersRun_nameGuards {μ : CheckMode} {F : Nat}
    {blockNames : List Name} {caps : IndCaps} :
    ∀ (members : List ConstantInfo) {env env₂ : Env},
      IndMembersRun μ F blockNames caps env members env₂ →
      ∀ ci ∈ members, ci.name.isProjFnShape = false ∧
        reservedBasisNames.contains ci.name = false := by
  intro members
  induction members with
  | nil =>
    intro env env₂ h ci hci
    exact nomatch hci
  | cons ci₀ rest ih =>
    intro env env₂ h ci hci
    obtain ⟨cvA, hmv, hmatch⟩ := h
    obtain ⟨type', hcv, -, -⟩ := id hmv
    rcases List.mem_cons.mp hci with heq | hci'
    · rw [heq]
      exact ⟨hcv.2.2.1, hcv.2.1⟩
    · cases ci₀ with
      | indInfo cv caps' => exact ih hmatch ci hci'
      | ctorInfo cv nP nF => exact ih hmatch ci hci'
      | axiomInfo cv => exact nomatch hmatch
      | defnInfo cv v hint => exact nomatch hmatch
      | thmInfo cv v => exact nomatch hmatch
      | recInfo cv mI rP rules => exact nomatch hmatch
      | projInfo e => exact nomatch hmatch

/-- The former's stored entry, run half. -/
theorem indMembersRun_indEntry {μ : CheckMode} {F : Nat}
    {blockNames : List Name} {caps : IndCaps} :
    ∀ (members : List ConstantInfo) {env env₂ : Env},
      IndMembersRun μ F blockNames caps env members env₂ →
      ∀ (cv : ConstantVal) (caps₂ : IndCaps),
        ConstantInfo.indInfo cv caps₂ ∈ members →
        ∃ cvA : ConstantVal, cvA.name = cv.name ∧
          cvA.levelParams = cv.levelParams ∧
          env₂.find? cv.name = some (.indInfo cvA caps) := by
  intro members
  induction members with
  | nil =>
    intro env env₂ h cv caps₂ hci
    exact nomatch hci
  | cons ci₀ rest ih =>
    intro env env₂ h cv caps₂ hci
    obtain ⟨cvA, hmv, hmatch⟩ := h
    obtain ⟨type', hcv, hcvA, -⟩ := id hmv
    have hnameA : cvA.name = ci₀.toConstantVal.name := by rw [hcvA]
    have hlpsA : cvA.levelParams = ci₀.toConstantVal.levelParams := by
      rw [hcvA]
    rcases List.mem_cons.mp hci with heq | hci'
    · subst heq
      refine ⟨cvA, hnameA, hlpsA, ?_⟩
      rw [show cv.name = cvA.name from hnameA.symm]
      exact indMembersRun_mono rest hmatch _ _
        (Env.find?_cons_self (.indInfo cvA caps) env)
    · cases ci₀ with
      | indInfo cv' caps' => exact ih hmatch cv caps₂ hci'
      | ctorInfo cv' nP nF => exact ih hmatch cv caps₂ hci'
      | axiomInfo cv' => exact nomatch hmatch
      | defnInfo cv' v hint => exact nomatch hmatch
      | thmInfo cv' v => exact nomatch hmatch
      | recInfo cv' mI rP rules => exact nomatch hmatch
      | projInfo e => exact nomatch hmatch

/-- The constructor member's stored entry, run half. -/
theorem indMembersRun_ctorEntry {μ : CheckMode} {F : Nat}
    {blockNames : List Name} {caps : IndCaps} :
    ∀ (members : List ConstantInfo) {env env₂ : Env},
      IndMembersRun μ F blockNames caps env members env₂ →
      ∀ (cv : ConstantVal) (nP nF : Nat),
        ConstantInfo.ctorInfo cv nP nF ∈ members →
        ∃ cvA : ConstantVal,
          env₂.find? cv.name = some (.ctorInfo cvA nP nF) := by
  intro members
  induction members with
  | nil =>
    intro env env₂ h cv nP nF hci
    exact nomatch hci
  | cons ci₀ rest ih =>
    intro env env₂ h cv nP nF hci
    obtain ⟨cvA, hmv, hmatch⟩ := h
    obtain ⟨type', hcv, hcvA, -⟩ := id hmv
    have hnameA : cvA.name = ci₀.toConstantVal.name := by rw [hcvA]
    rcases List.mem_cons.mp hci with heq | hci'
    · subst heq
      refine ⟨cvA, ?_⟩
      rw [show cv.name = cvA.name from hnameA.symm]
      exact indMembersRun_mono rest hmatch _ _
        (Env.find?_cons_self (.ctorInfo cvA nP nF) env)
    · cases ci₀ with
      | indInfo cv' caps' => exact ih hmatch cv nP nF hci'
      | ctorInfo cv' nP' nF' => exact ih hmatch cv nP nF hci'
      | axiomInfo cv' => exact nomatch hmatch
      | defnInfo cv' v hint => exact nomatch hmatch
      | thmInfo cv' v => exact nomatch hmatch
      | recInfo cv' mI rP rules => exact nomatch hmatch
      | projInfo e => exact nomatch hmatch

/-- A former stored after the member fold is either the base's or the
block's own, run half. -/
theorem indMembersRun_indNew {μ : CheckMode} {F : Nat}
    {blockNames : List Name} {caps : IndCaps} :
    ∀ (members : List ConstantInfo) {env env₂ : Env},
      IndMembersRun μ F blockNames caps env members env₂ →
      ∀ (T : Name) (cvT : ConstantVal) (caps' : IndCaps),
        env₂.find? T = some (.indInfo cvT caps') →
        env.find? T = some (.indInfo cvT caps') ∨
          (caps' = caps ∧ ∃ (cv : ConstantVal) (caps₂ : IndCaps),
            ConstantInfo.indInfo cv caps₂ ∈ members ∧ cv.name = T) := by
  intro members
  induction members with
  | nil =>
    intro env env₂ h T cvT caps' hf
    subst h
    exact Or.inl hf
  | cons ci₀ rest ih =>
    intro env env₂ h T cvT caps' hf
    obtain ⟨cvA, hmv, hmatch⟩ := h
    obtain ⟨type', hcv, hcvA, -⟩ := id hmv
    have hnameA : cvA.name = ci₀.toConstantVal.name := by rw [hcvA]
    cases ci₀ with
    | indInfo cv' caps'' =>
      rcases ih hmatch T cvT caps' hf with hf' | ⟨rfl, cv, caps₂,
        hmem, hcvn⟩
      · rw [Env.find?_cons] at hf'
        split at hf'
        · next he =>
          obtain ⟨rfl, rfl⟩ :=
            ConstantInfo.indInfo.inj (Option.some.inj hf')
          exact Or.inr ⟨rfl, cv', caps'', List.mem_cons_self,
            hnameA.symm.trans he⟩
        · exact Or.inl hf'
      · exact Or.inr ⟨rfl, cv, caps₂, List.mem_cons_of_mem _ hmem,
          hcvn⟩
    | ctorInfo cv' nP nF =>
      rcases ih hmatch T cvT caps' hf with hf' | ⟨rfl, cv, caps₂,
        hmem, hcvn⟩
      · rw [Env.find?_cons] at hf'
        split at hf'
        · exact ConstantInfo.noConfusion (Option.some.inj hf')
        · exact Or.inl hf'
      · exact Or.inr ⟨rfl, cv, caps₂, List.mem_cons_of_mem _ hmem,
          hcvn⟩
    | axiomInfo cv' => exact nomatch hmatch
    | defnInfo cv' v hint => exact nomatch hmatch
    | thmInfo cv' v => exact nomatch hmatch
    | recInfo cv' mI rP rules => exact nomatch hmatch
    | projInfo e => exact nomatch hmatch

/-! ## The group phase's keep-fact -/

/-- Every provisioned member's checked name is fresh in the group's
base environment, run half. -/
theorem provisionRecsRun_checkedFresh {μ : CheckMode} {F : Nat}
    {blockNames : List Name} :
    ∀ (recs : List ConstantInfo) {envAcc envSelf : Env}
      {checked : List (ConstantVal × Nat × Nat × List RecRule)},
      ProvisionRecsRun μ F blockNames envAcc recs envSelf checked →
      ∀ c ∈ checked, envAcc.find? c.1.name = none := by
  intro recs
  induction recs with
  | nil =>
    intro envAcc envSelf checked h c hc
    obtain ⟨-, rfl⟩ := h
    exact nomatch hc
  | cons ci₀ rest ih =>
    intro envAcc envSelf checked h c hc
    obtain ⟨cvA, mI, rP, rules, rest', -, hmv, hprov', rfl⟩ := h
    obtain ⟨type', ⟨hfresh, -, -, -, -, -, -, -, -, -⟩, rfl, -⟩ := hmv
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact Option.isNone_iff_eq_none.mp hfresh
    · have hnone := ih hprov' c hc'
      rw [Env.find?_cons] at hnone
      split at hnone
      · exact nomatch hnone
      · exact hnone

/-- The install fold leaves alone every name it does not cons, run
half. -/
theorem indRecsFoldRun_keep {μ : CheckMode} {F : Nat}
    {blockNames : List Name} {envBase envSelf : Env} :
    ∀ (checked : List (ConstantVal × Nat × Nat × List RecRule))
      {acc out : Env},
      IndRecsRun.IndRecsFoldRun μ F blockNames envBase envSelf
        acc checked out →
      ∀ n : Name, (∀ c ∈ checked, c.1.name ≠ n) →
        out.find? n = acc.find? n := by
  intro checked
  induction checked with
  | nil =>
    intro acc out h n _
    subst h
    rfl
  | cons c rest ih =>
    intro acc out h n hne
    obtain ⟨rules', -, htail⟩ := h
    rw [ih htail n (fun c' hc' => hne c' (List.mem_cons_of_mem _ hc')),
      Env.find?_cons]
    exact if_neg (hne c List.mem_cons_self)

/-- **The recursor group keeps the base environment's lookups**, run
half. -/
theorem indRecsRun_keep {μ : CheckMode} {F : Nat}
    {blockNames : List Name} {env₂ env₃ : Env}
    {recs : List ConstantInfo}
    (h : IndRecsRun μ F blockNames env₂ recs env₃) :
    ∀ (n : Name) (ci : ConstantInfo),
      env₂.find? n = some ci → env₃.find? n = some ci := by
  rcases h with ⟨-, rfl⟩ | ⟨-, -, envSelf, checked, hprov, hfold⟩
  · exact fun _ _ hf => hf
  · intro n ci hf
    refine (indRecsFoldRun_keep checked hfold n ?_).trans hf
    intro c hc hcn
    have hnone := provisionRecsRun_checkedFresh recs hprov c hc
    rw [hcn, hf] at hnone
    exact nomatch hnone

/-- The group phase is an `ExtEta` extension, run half. -/
theorem indRecsRun_ext {μ : CheckMode} {F : Nat}
    {blockNames : List Name} {env₂ env₃ : Env}
    {recs : List ConstantInfo}
    (h : IndRecsRun μ F blockNames env₂ recs env₃) :
    ExtEta env₂ env₃ :=
  ⟨fun n ci hf _ => indRecsRun_keep h n ci hf, indRecsRun_noInd h⟩

/-! ## The group's rule facts, from the runs

**The one place the run projection is not free** (task #161 S11b,
finding): `RuleFacts`'s last conjunct is a *denotation* — the fired
rule's right-hand side reads — because that is what an `EnvFacts` at the
swapped environment asks of a stored rule (`EnvFacts.rec_rhs_denotes`).
`iotaRulesFactsR` gets it from `IotaRuleR`'s front-door row, which the
run record does not carry.

The answer is the S10 seal's own (residual A): the reading comes from
the *run*, through the consumer's own acceptance walk, not from a
derivation.  So the supplier is a **premise** here — `hden`, "an
`inferTypeCore` verdict on a closed expression is a reading" — and the
graded lane discharges it with `acceptedReads_of` composed with
`denoteMeta_erase`.  The collapsed lane keeps `iotaRulesFactsR`
unchanged; neither lane re-proves the syntactic six. -/

/-- **Every rule the per-recursor fold returns carries its model-free
facts** — off `IotaRulesRun` plus a reading supplier. -/
theorem iotaRulesFactsRun {μ : CheckMode} {F : Nat}
    {env₂ envSelf : Env} {cvalSelf : TConstVal} {f : Name → Name}
    (hup : FoldUpS env₂ envSelf)
    (hden : ∀ e : Expr, e.hasFvar = false →
      e.looseBVarsBounded 0 = true →
      (∃ t', inferTypeCore μ envSelf F 0 e = .ok t') →
      ∀ φ : Name → Nat,
        ∃ Rv, denoteClosed cvalSelf envSelf φ e = some Rv)
    {cvA : ConstantVal} {mI rP : Nat} :
    ∀ (j : Nat) (rules rules' : List RecRule),
      IotaRulesRun μ F env₂ envSelf f cvA.name cvA.levelParams
        cvA.type mI rP j rules rules' →
      ∀ rl ∈ rules', RuleFacts envSelf cvalSelf cvA mI rP rl := by
  intro j rules
  induction rules generalizing j with
  | nil =>
    intro rules' h rl hrl
    rw [h] at hrl
    exact nomatch hrl
  | cons r rest ih =>
    intro rules' h rl hrl
    obtain ⟨r', rest', hkit, hrec, rfl⟩ := h
    rcases List.mem_cons.mp hrl with heqrl | hrl'
    · rw [heqrl]
      obtain ⟨cvjK, cnPK, cnFK, rhsA, hfcK, hnfK, hrb, hrf, hann, hrlp,
        hrres, hstripRhs, hityK, fire, hr'eq, hbranch⟩ := hkit
      have hr'rhs : RecRule.rhs r' = rhsA := by rw [hr'eq]; rfl
      have hr'ctor : RecRule.ctor r' = RecRule.ctor r := by rw [hr'eq]; rfl
      have hr'fire : RecRule.fire r' = fire := by rw [hr'eq]; rfl
      obtain ⟨hrhsAw, hrhsAb⟩ := annotate_syntax hann hrf hrb
      have hfcS : envSelf.find? (RecRule.ctor r')
          = some (.ctorInfo cvjK cnPK cnFK) := by
        rw [hr'ctor]
        rcases hup _ _ hfcK with h' |
          ⟨cv, mI', rP', rules₀, rules₁, heq, -⟩
        · exact h'
        · exact nomatch heq
      have hkeep : ∀ (n : Name) (ci : ConstantInfo),
          (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) →
          env₂.find? n = some ci → envSelf.find? n = some ci := by
        intro n ci hnr hf
        rcases hup _ _ hf with h' | ⟨cv, mI', rP', rules₀, rules₁, heq, -⟩
        · exact h'
        · exact absurd heq (hnr _ _ _ _)
      refine ⟨by rw [hr'rhs]; exact hrhsAw, by rw [hr'rhs]; exact hrlp,
        by rw [hr'rhs]; exact hrres, by rw [hr'rhs]; exact hrhsAb, ?_,
        ⟨cvjK, cnPK, cnFK, hfcS⟩, ?_, ?_, ?_⟩
      · -- the nested shape facts, from `nestedRuleShape`
        intro lvls pins hfireN
        rw [hr'fire] at hfireN
        rcases hbranch with ⟨-, hfireP, -⟩ | ⟨-, hrest⟩
        · rw [hfireP] at hfireN; exact nomatch hfireN
        rcases hrest with ⟨hfireI, -⟩ | ⟨lvls₀, pins₀, hfireN₀, hthmN⟩
        · rw [hfireI] at hfireN; exact nomatch hfireN
        rw [hfireN₀] at hfireN
        obtain ⟨rfl, rfl⟩ := RecRuleFire.nested.inj hfireN
        obtain ⟨hshape, -⟩ := hthmN
        obtain ⟨hrPmI, hlvls, hpins, pre, dom, body, bm, D, hstrip,
          hfn, hargs, -⟩ := nestedRuleShape_inv hshape
        exact ⟨hrPmI, hlvls, hpins, pre, dom, body, bm, D, hstrip,
          hfn, hargs⟩
      · -- a fired rule: the parameter bound and the rhs's reading
        intro hfire
        refine ⟨?_, fun φ => ?_⟩
        · rcases hbranch with ⟨hplain, -, -⟩ | ⟨-, hrest⟩
          · exact recRulePlain_params_le hplain
          rcases hrest with ⟨hfireI, -⟩ | ⟨lvls₀, pins₀, hfireN₀, hthmN⟩
          · exact absurd (by rw [hr'fire, hfireI]) hfire
          exact (nestedRuleShape_inv hthmN.1).1
        · obtain ⟨t', hty'⟩ := hityK
          obtain ⟨Rv, hRv⟩ := hden rhsA hrhsAw hrhsAb ⟨t', hty'⟩ φ
          exact ⟨Rv, by rw [hr'rhs]; exact hRv⟩
      · -- the K bit is the install's own lookup, moved to `envSelf`
        intro hb
        refine recRuleKOf_mono hkeep ?_
        rw [hr'eq] at hb ⊢
        exact hb
      · -- the η-rescue bit, likewise
        intro hb
        refine recRuleEtaOf_mono hkeep ?_
        rw [hr'eq] at hb ⊢
        exact hb
    · exact ih (j + 1) rest' hrec rl hrl'

set_option maxHeartbeats 1600000 in
/-- **The provisioning and the install fold, run together** — run
half of `indRecsFoldFacts`, generalised over the rule facts exactly as
its twin is. -/
theorem indRecsFoldFactsRun {μ : CheckMode} {F : Nat}
    {blockNames : List Name}
    {envSelf envBase : Env}
    (RF : ConstantVal → Nat → Nat → RecRule → Prop)
    (hfire : ∀ (cvA : ConstantVal) (mI rP : Nat)
      (rules rules' : List RecRule),
      blockNames.contains cvA.name = true →
      envSelf.find? cvA.name = some (.recInfo cvA mI rP []) →
      IotaRulesRun μ F envBase envSelf
        (fun n => if blockNames.contains n then n.str "_model" else n)
        cvA.name cvA.levelParams cvA.type mI rP 0 rules rules' →
      ∀ rl ∈ rules', RF cvA mI rP rl) :
    ∀ (recs : List ConstantInfo) {envP envF env₃ : Env}
      {checked : List (ConstantVal × Nat × Nat × List RecRule)},
      SwapShList envP.consts envF.consts →
      SwapNResS envP envF →
      FoldUpS envF envSelf →
      (∀ (n : Name) (ci : ConstantInfo),
        envP.find? n = some ci → envSelf.find? n = some ci) →
      envP.find? eqName = some eqA →
      (∀ c ∈ envF.consts, c ∈ envSelf.consts ∨
        ∃ (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule),
          c = .recInfo cv mI rP rules ∧
          ∀ rl ∈ rules, RF cv mI rP rl) →
      (∀ (n : Name) (cv : ConstantVal) (mI rP : Nat)
        (rules : List RecRule),
        envF.find? n = some (.recInfo cv mI rP rules) →
        envSelf.find? n = some (.recInfo cv mI rP rules) ∨
        ∀ rl ∈ rules, RF cv mI rP rl) →
      (∀ ci ∈ recs, blockNames.contains ci.name = true) →
      ProvisionRecsRun μ F blockNames envP recs envSelf checked →
      IndRecsRun.IndRecsFoldRun μ F blockNames envBase envSelf
        envF checked env₃ →
      SwapShList envSelf.consts env₃.consts ∧
      SwapNResS envSelf env₃ ∧
      (∀ c ∈ env₃.consts, c ∈ envSelf.consts ∨
        ∃ (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule),
          c = .recInfo cv mI rP rules ∧
          ∀ rl ∈ rules, RF cv mI rP rl) ∧
      ∀ (n : Name) (cv : ConstantVal) (mI rP : Nat)
        (rules : List RecRule),
        env₃.find? n = some (.recInfo cv mI rP rules) →
        envSelf.find? n = some (.recInfo cv mI rP rules) ∨
        ∀ rl ∈ rules, RF cv mI rP rl := by
  intro recs
  induction recs with
  | nil =>
    intro envP envF env₃ checked hsw hnres hupF hupP heqP
      hents hentF hbn hprov hfold
    obtain ⟨rfl, rfl⟩ := hprov
    subst hfold
    exact ⟨hsw, hnres, hents, hentF⟩
  | cons ci₀ rest ih =>
    intro envP envF env₃ checked hsw hnres hupF hupP heqP
      hents hentF hbn hprov hfold
    obtain ⟨cvA, mI, rP, rules, rest', hciE, hmv, hprov', rfl⟩ := hprov
    obtain ⟨rules', hiot, hfold'⟩ := hfold
    obtain ⟨type', ⟨hfresh0, hres0, -, -, -, -, -, -, -, -⟩, hcvAdef,
      -⟩ := hmv
    have hnameA : cvA.name = ci₀.toConstantVal.name := by
      rw [hcvAdef]
    have hfreshP : envP.find? cvA.name = none := by
      rw [hnameA]; exact Option.isNone_iff_eq_none.mp hfresh0
    have hres : reservedBasisNames.contains cvA.name = false := by
      rw [hnameA]; exact hres0
    have hcg : SwapCongr envP envF := SwapShList.congr hsw
    have hselfA : envSelf.find? cvA.name
        = some (.recInfo cvA mI rP []) :=
      provisionRecsRunS_mono rest hprov' _ _
        (Env.find?_cons_self (.recInfo cvA mI rP []) envP)
    have hbnA : blockNames.contains cvA.name = true := by
      rw [hnameA]; exact hbn ci₀ List.mem_cons_self
    have heqfF : envF.find? eqName = some eqA :=
      hcg.findUp eqName eqA heqP
        (fun _ _ _ _ h => ConstantInfo.noConfusion h)
    have hfacts := hfire cvA mI rP rules rules' hbnA hselfA hiot
    have hfreshF : envF.find? cvA.name = none := by
      rcases hF : envF.find? cvA.name with _ | ciF
      · rfl
      · have := hcg.isSomeEq cvA.name
        rw [hF, hfreshP] at this
        exact nomatch this.symm
    refine ?_
    have hsw' : SwapShList
        (Env.consts ⟨.recInfo cvA mI rP [] :: envP.consts⟩)
        (Env.consts ⟨.recInfo cvA mI rP rules' :: envF.consts⟩) :=
      SwapShList.cons (Or.inr ⟨cvA, mI, rP, rules', rfl, rfl⟩) hsw
    have hnres' : SwapNResS ⟨.recInfo cvA mI rP [] :: envP.consts⟩
        ⟨.recInfo cvA mI rP rules' :: envF.consts⟩ := by
      intro n cv mI₀ rP₀ rules₀ h₀ h₃
      rw [Env.find?_cons] at h₀ h₃
      split at h₀
      · next hn =>
        rw [if_pos (show (ConstantInfo.recInfo cvA mI rP rules').name
          = n from hn)] at h₃
        obtain ⟨rfl, -, -, -⟩ :=
          ConstantInfo.recInfo.inj (Option.some.inj h₀)
        exact Or.inr (by rw [← hn]; exact hres)
      · next hn =>
        rw [if_neg (show ¬(ConstantInfo.recInfo cvA mI rP rules').name
          = n from hn)] at h₃
        exact hnres n cv mI₀ rP₀ rules₀ h₀ h₃
    have hupF' : FoldUpS ⟨.recInfo cvA mI rP rules' :: envF.consts⟩
        envSelf := by
      intro n ci hfx
      rw [Env.find?_cons] at hfx
      split at hfx
      · next hn =>
        obtain rfl := Option.some.inj hfx
        exact Or.inr ⟨cvA, mI, rP, rules', [], rfl, by
          rw [← hn]; exact hselfA⟩
      · exact hupF n ci hfx
    have hupP' : ∀ (n : Name) (ci : ConstantInfo),
        (Env.find? ⟨.recInfo cvA mI rP [] :: envP.consts⟩ n) = some ci →
        envSelf.find? n = some ci := by
      intro n ci hfx
      rw [Env.find?_cons] at hfx
      split at hfx
      · next hn =>
        obtain rfl := Option.some.inj hfx
        rw [← hn]; exact hselfA
      · exact hupP n ci hfx
    have heqP' : Env.find? ⟨.recInfo cvA mI rP [] :: envP.consts⟩ eqName
        = some eqA :=
      Env.find?_cons_of_fresh (c := .recInfo _ mI rP []) hfreshP heqP
    have hents' : ∀ c ∈ (Env.consts
        ⟨.recInfo cvA mI rP rules' :: envF.consts⟩),
        c ∈ envSelf.consts ∨
        ∃ (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule),
          c = .recInfo cv mI rP rules ∧
          ∀ rl ∈ rules, RF cv mI rP rl := by
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc'
      · exact Or.inr ⟨cvA, mI, rP, rules', rfl, hfacts⟩
      · exact hents c hc'
    have hentF' : ∀ (n : Name) (cv : ConstantVal) (mI₀ rP₀ : Nat)
        (rules₀ : List RecRule),
        Env.find? ⟨.recInfo cvA mI rP rules' :: envF.consts⟩ n
          = some (.recInfo cv mI₀ rP₀ rules₀) →
        envSelf.find? n = some (.recInfo cv mI₀ rP₀ rules₀) ∨
        ∀ rl ∈ rules₀, RF cv mI₀ rP₀ rl := by
      intro n cv mI₀ rP₀ rules₀ hfx
      rw [Env.find?_cons] at hfx
      split at hfx
      · obtain ⟨rfl, rfl, rfl, rfl⟩ :=
          ConstantInfo.recInfo.inj (Option.some.inj hfx)
        exact Or.inr hfacts
      · exact hentF n cv mI₀ rP₀ rules₀ hfx
    exact ih hsw' hnres' hupF' hupP' heqP' hents' hentF'
      (fun ci hci => hbn ci (List.mem_cons_of_mem _ hci)) hprov' hfold'

/-! ## `declIndEtaClosedRun` — the ind kind's η-closure, on the run
record -/

/-- **The inductive block preserves the η-family closure**, from
`DeclIndRun` alone (task #161 S11b).

`declIndEtaClosed`'s proof verbatim, at the run family: it reads the
member fold's `indNew`/`mono`/`ctorEntry`, the group's `noInd`/`keep`,
and the three post-member phases' `ExtEta` extensions — no valuation
anywhere.  This is what `declStep_preserves` hands `declEtaStepRun` now that
the graded fold's ind premise is the run record. -/
theorem declIndEtaClosedRun {μ : CheckMode} {F : Nat} {env env₂ : Env}
    {block : List ConstantInfo}
    (hE : EtaFamiliesClosed env)
    (h : DeclIndRun μ F env block env₂) :
    EtaFamiliesClosed env₂ := by
  obtain ⟨hsplit, hmain⟩ := h
  rcases hmain with ⟨cvT, capsT, cvC, nP, nF, hIfilt, hCfilt, harm⟩ |
    ⟨-, envM, hmem, hrecs⟩
  · -- the single-constructor arm
    obtain ⟨envM, envR, hmem, hrecs, -, -, hproj⟩ := harm
    have hmemFil : ∀ {p : ConstantInfo → Bool} {x : ConstantInfo},
        block.filter p = [x] → x ∈ block := by
      intro p x hfil
      have hx : x ∈ block.filter p := by
        rw [hfil]; exact List.mem_singleton_self _
      exact (List.mem_filter.mp hx).1
    have hCin : ConstantInfo.ctorInfo cvC nP nF ∈ block := hmemFil hCfilt
    have hCnon : ConstantInfo.ctorInfo cvC nP nF ∈ block.filter
        (fun ci => match ci with
          | .recInfo _ _ _ _ => false | _ => true) :=
      List.mem_filter.mpr ⟨hCin, rfl⟩
    have hx : ExtEta envM env₂ :=
      ExtEta.trans (indRecsRun_ext hrecs) (projInstallRun_ext _ hproj)
    intro T cvT' caps' hf he hr
    rcases indMembersRun_indNew _ hmem T cvT' caps'
      (hx.2 T cvT' caps' hf) with hfE | ⟨rfl, -⟩
    · obtain ⟨cvC', hfC⟩ := hE T cvT' caps' hfE he hr
      exact ⟨cvC', hx.1 _ _ (indMembersRun_mono _ hmem _ _ hfC)
        (fun _ _ _ _ hh => nomatch hh)⟩
    · obtain ⟨cvA', hfA⟩ :=
        indMembersRun_ctorEntry _ hmem cvC nP nF hCnon
      exact ⟨cvA', hx.1 _ _ hfA (fun _ _ _ _ hh => nomatch hh)⟩
  · -- the generic arm: an empty capability record
    intro T cvT' caps' hf he hr
    have hfM := indRecsRun_noInd hrecs T cvT' caps' hf
    rcases indMembersRun_indNew _ hmem T cvT' caps' hfM with
      hfE | ⟨rfl, -⟩
    · obtain ⟨cvC, hfC⟩ := hE T cvT' caps' hfE he hr
      exact ⟨cvC, indRecsRun_keep hrecs _ _
        (indMembersRun_mono _ hmem _ _ hfC)⟩
    · exact absurd he (by decide)

end ConLeche.Semantics
