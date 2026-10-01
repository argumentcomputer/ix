module

public import ConLeche.Verify.Extend.Modeled

public section

/-!
# Ind

The bookkeeping the `checkModeled` member fold establishes about the
environment it returns: which names it installs, which kinds they get,
that nothing else moves, and the two side invariants
(`EtaFamiliesClosedO`, `BlockCapsPinned`) the block install threads.

Everything here is stated over `Env`/`Expr` alone, with no valuation in
sight; the soundness statements that read a valuation live one tier up
(`ConLeche/Model/IndCaps.lean`, `ConLeche/Semantics/EnvFactsCons.lean`).
-/

set_option linter.unusedSimpArgs false

namespace ConLeche

variable {mode : CheckMode}

open Expr

/-- A successful fold's members were all fresh at their own step, hence
already fresh at any earlier point. -/
theorem checkIndMember_fold_names {blockNames : List Name}
    {caps : IndCaps} :
    ∀ (rest : List ConstantInfo) (env' env₂ : Env),
    rest.foldlM (checkIndMember (fueledOps mode F) blockNames caps) env' = .ok env₂ →
    ∀ ci ∈ rest, env'.find? ci.name = none
  | [], _, _, _, ci, hci => nomatch hci
  | ci₀ :: rest, env', env₂, h, ci, hci => by
    rw [List.foldlM_cons] at h
    simp only [Bind.bind, Except.bind] at h
    cases hstep : checkIndMember (fueledOps mode F) blockNames caps env' ci₀ with
    | error e => rw [hstep] at h; exact nomatch h
    | ok env₁ =>
    rw [hstep] at h
    obtain ⟨cvA, cvm, mval, hmcvm, hccv, hms, hfm, hlps, hrenf, hkind⟩ :=
      checkIndMember_inv hstep
    obtain ⟨hfind0, -⟩ := checkConstantVal_inv hccv
    rw [List.mem_cons] at hci
    rcases hci with rfl | hci
    · exact hfind0
    · have hnone₁ := checkIndMember_fold_names rest env₁ env₂ h ci hci
      have henv₁ : ∃ ci₁, env₁ = (⟨ci₁ :: env'.consts⟩ : Env) := by
        rcases hkind with ⟨-, rfl⟩ | ⟨cv, nP, nF, -, rfl⟩
        · exact ⟨_, rfl⟩
        · exact ⟨_, rfl⟩
      obtain ⟨ci₁, rfl⟩ := henv₁
      rw [Env.find?_cons] at hnone₁
      split at hnone₁
      · exact nomatch hnone₁
      · exact hnone₁

/-- Members installed by the fold never carry a model-shaped name
(`checkMemberVal` rejects them). -/
theorem checkIndFold_modelfree {blockNames : List Name}
    {caps : IndCaps} :
    ∀ (rest : List ConstantInfo) (env' env₂ : Env),
    rest.foldlM (checkIndMember (fueledOps mode F) blockNames caps) env' = .ok env₂ →
    ∀ ci ∈ rest, ci.name.isModelSuffix = false
  | [], _, _, _, ci, hci => nomatch hci
  | ci₀ :: rest, env', env₂, h, ci, hci => by
    rw [List.foldlM_cons] at h
    simp only [Bind.bind, Except.bind] at h
    cases hstep : checkIndMember (fueledOps mode F) blockNames caps env' ci₀ with
    | error e => rw [hstep] at h; exact nomatch h
    | ok env₁ =>
    rw [hstep] at h
    rw [List.mem_cons] at hci
    rcases hci with rfl | hci
    · obtain ⟨cvA, cvm, mval, hmcvm, hccv, hms, hfm, hlps, hrenf, hkind⟩ :=
        checkIndMember_inv hstep
      obtain ⟨-, -, -, -, -, -, tyA, stype, u, -, -, -, -, -, hcvA⟩ :=
        checkConstantVal_inv hccv
      rw [hcvA] at hms
      rcases hkind with ⟨⟨cv, caps', rfl⟩, -⟩ | ⟨cv, nP, nF, rfl, -⟩ <;>
        exact hms
    · exact checkIndFold_modelfree rest env₁ env₂ h ci hci


/-- Members installed by the fold never carry a
projection-function-shaped name. -/
theorem checkIndFold_projshape {blockNames : List Name}
    {caps : IndCaps} :
    ∀ (rest : List ConstantInfo) (env' env₂ : Env),
    rest.foldlM (checkIndMember (fueledOps mode F) blockNames caps) env' = .ok env₂ →
    ∀ ci ∈ rest, ci.name.isProjFnShape = false
  | [], _, _, _, ci, hci => nomatch hci
  | ci₀ :: rest, env', env₂, h, ci, hci => by
    rw [List.foldlM_cons] at h
    simp only [Bind.bind, Except.bind] at h
    cases hstep : checkIndMember (fueledOps mode F) blockNames caps env' ci₀ with
    | error e => rw [hstep] at h; exact nomatch h
    | ok env₁ =>
    rw [hstep] at h
    rw [List.mem_cons] at hci
    rcases hci with rfl | hci
    · obtain ⟨cvA, cvm, mval, hmcvm, hccv, hms, hfm, hlps, hrenf, hkind⟩ :=
        checkIndMember_inv hstep
      obtain ⟨-, -, hpshape0, -, -, -, tyA, stype, u, -, -, -, -, -,
        hcvA⟩ := checkConstantVal_inv hccv
      exact hpshape0
    · exact checkIndFold_projshape rest env₁ env₂ h ci hci

/-- The member fold adds only block-named inductive-former or
constructor constants. -/
theorem checkIndFold_find_new {blockNames : List Name}
    {caps : IndCaps} :
    ∀ (rest : List ConstantInfo) (env' env₂ : Env),
    (∀ ci ∈ rest, blockNames.contains ci.name = true) →
    rest.foldlM (checkIndMember (fueledOps mode F) blockNames caps) env' = .ok env₂ →
    ∀ (n : Name) (ci : ConstantInfo), env₂.find? n = some ci →
    env'.find? n = some ci ∨
      (blockNames.contains n = true ∧
        ((∃ cv, ci = .indInfo cv caps) ∨
          ∃ cv nP nF, ci = .ctorInfo cv nP nF))
  | [], _, _, _, h, n, ci, hf => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact Or.inl hf
  | ci₀ :: rest, env', env₂, hns, h, n, ci, hf => by
    rw [List.foldlM_cons] at h
    simp only [Bind.bind, Except.bind] at h
    cases hstep : checkIndMember (fueledOps mode F) blockNames caps env' ci₀ with
    | error e => rw [hstep] at h; exact nomatch h
    | ok env₁ => ?_
    rw [hstep] at h
    obtain ⟨cvA, cvm, mval, hmcvm, hccv, hms, hfm, hlps, hrenf, hkind⟩ :=
      checkIndMember_inv hstep
    obtain ⟨hfind0, -, -, -, -, -, tyA, stype, u, -, -, -, -, -,
      hcvA⟩ := checkConstantVal_inv hccv
    have hnameA : cvA.name = ci₀.name := by rw [hcvA]; rfl
    have hbn₀ : blockNames.contains cvA.name = true := by
      rw [hnameA]
      exact hns ci₀ List.mem_cons_self
    rcases checkIndFold_find_new rest env₁ env₂
      (fun ci' hci' => hns ci' (List.mem_cons_of_mem _ hci')) h n ci hf
      with hf' | hnew
    · rcases hkind with ⟨⟨cv, caps', rfl⟩, rfl⟩ | ⟨cv, nP, nF, rfl, rfl⟩
      · rw [Env.find?_cons] at hf'
        split at hf'
        · next hh =>
          obtain rfl := Option.some.inj hf'
          refine Or.inr ⟨?_, Or.inl ⟨cvA, rfl⟩⟩
          rw [← hh]
          exact hbn₀
        · exact Or.inl hf'
      · rw [Env.find?_cons] at hf'
        split at hf'
        · next hh =>
          obtain rfl := Option.some.inj hf'
          refine Or.inr ⟨?_, Or.inr ⟨cvA, nP, nF, rfl⟩⟩
          rw [← hh]
          exact hbn₀
        · exact Or.inl hf'
    · exact Or.inr hnew


/-- Every successfully folded member is an inductive former or a
constructor. -/
theorem checkIndFold_kinds {blockNames : List Name} {caps : IndCaps} :
    ∀ (rest : List ConstantInfo) (env' env₂ : Env),
    rest.foldlM (checkIndMember (fueledOps mode F) blockNames caps) env' = .ok env₂ →
    ∀ ci ∈ rest, (∃ cv caps', ci = .indInfo cv caps') ∨
      ∃ cv nP nF, ci = .ctorInfo cv nP nF
  | [], _, _, _, ci, hci => nomatch hci
  | ci₀ :: rest, env', env₂, h, ci, hci => by
    rw [List.foldlM_cons] at h
    simp only [Bind.bind, Except.bind] at h
    cases hstep : checkIndMember (fueledOps mode F) blockNames caps env' ci₀ with
    | error e => rw [hstep] at h; exact nomatch h
    | ok env₁ =>
    rw [hstep] at h
    rw [List.mem_cons] at hci
    rcases hci with rfl | hci
    · obtain ⟨cvA, cvm, mval, hmcvm, hccv, hms, hfm, hlps, hrenf, hkind⟩ :=
        checkIndMember_inv hstep
      rcases hkind with ⟨⟨cv, caps', rfl⟩, -⟩ | ⟨cv, nP, nF, rfl, -⟩
      · exact Or.inl ⟨cv, caps', rfl⟩
      · exact Or.inr ⟨cv, nP, nF, rfl⟩
    · exact checkIndFold_kinds rest env₁ env₂ h ci hci


/-- The member fold preserves stored lookups exactly (every install is
fresh). -/
theorem checkIndFold_find_preserved {blockNames : List Name}
    {caps : IndCaps} :
    ∀ (rest : List ConstantInfo) (env' env₂ : Env),
    rest.foldlM (checkIndMember (fueledOps mode F) blockNames caps) env' = .ok env₂ →
    ∀ (n : Name) (ci : ConstantInfo), env'.find? n = some ci →
    env₂.find? n = some ci
  | [], _, _, h, n, ci, hf => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact hf
  | ci₀ :: rest, env', env₂, h, n, ci, hf => by
    rw [List.foldlM_cons] at h
    simp only [Bind.bind, Except.bind] at h
    cases hstep : checkIndMember (fueledOps mode F) blockNames caps env' ci₀ with
    | error e => rw [hstep] at h; exact nomatch h
    | ok env₁ => ?_
    rw [hstep] at h
    obtain ⟨cvA, cvm, mval, hmcvm, hccv, hms, hfm, hlps, hrenf, hkind⟩ :=
      checkIndMember_inv hstep
    obtain ⟨hfind0, -, -, -, -, -, tyA, stype, u, -, -, -, -, -,
      hcvA⟩ := checkConstantVal_inv hccv
    have hfindA : env'.find? cvA.name = none := by
      rw [show cvA.name = ci₀.name from by rw [hcvA]; rfl]
      exact hfind0
    have henv₁ : ∃ ci₁ : ConstantInfo, ci₁.name = cvA.name ∧
        env₁ = ⟨ci₁ :: env'.consts⟩ := by
      rcases hkind with ⟨-, rfl⟩ | ⟨cv, nP, nF, -, rfl⟩
      · exact ⟨_, rfl, rfl⟩
      · exact ⟨_, rfl, rfl⟩
    obtain ⟨ci₁, hname₁, rfl⟩ := henv₁
    refine checkIndFold_find_preserved rest _ env₂ h n ci ?_
    rw [Env.find?_cons_of_isSome (by rw [hname₁]; exact hfindA)
      (by rw [hf]; rfl)]
    exact hf

/-- The eta families of stored formers *outside* the block are closed:
their capability constructor is stored at the record's arities.  The
block-fold form of the threaded `EtaFamiliesClosed` (which cannot hold
for a former whose constructor is still pending). -/
@[expose] def EtaFamiliesClosedO (blockNames : List Name) (env : Env) : Prop :=
  ∀ (T : Name) (cvT : ConstantVal) (caps : IndCaps),
    env.find? T = some (.indInfo cvT caps) → caps.eta = true →
    reservedBasisNames.contains T = false →
    blockNames.contains T = false →
    ∃ cvC, env.find? caps.etaCtor =
      some (.ctorInfo cvC caps.etaParams caps.etaFields)

/-- Stored block formers carry exactly the fold's capability record. -/
def BlockCapsPinned (blockNames : List Name) (caps : IndCaps)
    (env : Env) : Prop :=
  ∀ (n : Name) (cvS : ConstantVal) (capsS : IndCaps),
    blockNames.contains n = true →
    env.find? n = some (.indInfo cvS capsS) → capsS = caps

/-- The outside-families invariant steps at any fresh *block* install:
a block name is never an outside former's name. -/
theorem EtaFamiliesClosedO.cons {blockNames : List Name} {env : Env}
    {c₀ : ConstantInfo} (h : EtaFamiliesClosedO blockNames env)
    (hfresh : env.find? c₀.name = none)
    (hbn : blockNames.contains c₀.name = true) :
    EtaFamiliesClosedO blockNames ⟨c₀ :: env.consts⟩ := by
  intro T cvT caps hfT hcape hres hTb
  have hTne : T ≠ c₀.name := by
    intro he
    rw [he, hbn] at hTb
    exact nomatch hTb
  rw [Env.find?_cons, if_neg (fun hh => hTne hh.symm)] at hfT
  obtain ⟨cvC, hfC⟩ := h T cvT caps hfT hcape hres hTb
  exact ⟨cvC, by
    rw [Env.find?_cons_of_isSome hfresh (by rw [hfC]; rfl)]
    exact hfC⟩

/-- The member fold only extends the environment: stored lookups stay
stored. -/
theorem checkIndFold_mono {blockNames : List Name} {caps : IndCaps} :
    ∀ (rest : List ConstantInfo) (env' env₂ : Env),
    rest.foldlM (checkIndMember (fueledOps mode F) blockNames caps) env' =
      .ok env₂ →
    ∀ n, (env'.find? n).isSome = true → (env₂.find? n).isSome = true
  | [], _, _, h, n, hn => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hn
  | ci :: rest, env', env₂, h, n, hn => by
    rw [List.foldlM_cons] at h
    simp only [Bind.bind, Except.bind] at h
    cases hstep : checkIndMember (fueledOps mode F) blockNames caps env'
        ci with
    | error e => rw [hstep] at h; exact nomatch h
    | ok env₁ => ?_
    rw [hstep] at h
    obtain ⟨cvA, cvm, mval, hmcvm, hccv, -, -, -, -, hkind⟩ :=
      checkIndMember_inv hstep
    have henv₁ : ∃ ci₁ : ConstantInfo, env₁ = ⟨ci₁ :: env'.consts⟩ := by
      rcases hkind with ⟨-, rfl⟩ | ⟨cv, nP, nF, -, rfl⟩
      · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
    obtain ⟨ci₁, rfl⟩ := henv₁
    refine checkIndFold_mono rest _ env₂ h n ?_
    rw [Env.find?_cons]
    by_cases hh : ci₁.name = n
    · rw [if_pos hh]
      rfl
    · rw [if_neg hh]
      exact hn

/-- After the member fold every folded member is stored. -/
theorem checkIndFold_stored {blockNames : List Name} {caps : IndCaps} :
    ∀ (rest : List ConstantInfo) (env' env₂ : Env),
    rest.foldlM (checkIndMember (fueledOps mode F) blockNames caps) env' =
      .ok env₂ →
    ∀ ci ∈ rest, (env₂.find? ci.name).isSome = true
  | [], _, _, _, ci, hci => nomatch hci
  | ci₀ :: rest, env', env₂, h, ci, hci => by
    rw [List.foldlM_cons] at h
    simp only [Bind.bind, Except.bind] at h
    cases hstep : checkIndMember (fueledOps mode F) blockNames caps env'
        ci₀ with
    | error e => rw [hstep] at h; exact nomatch h
    | ok env₁ => ?_
    rw [hstep] at h
    obtain ⟨cvA, cvm, mval, hmcvm, hccv, -, -, -, -, hkind⟩ :=
      checkIndMember_inv hstep
    obtain ⟨-, -, -, -, -, -, tyA, stype, u, -, -, -, -, -, hcvA⟩ :=
      checkConstantVal_inv hccv
    have hnameA : cvA.name = ci₀.name := by rw [hcvA]; rfl
    have henv₁ : ∃ ci₁ : ConstantInfo, ci₁.name = cvA.name ∧
        env₁ = ⟨ci₁ :: env'.consts⟩ := by
      rcases hkind with ⟨-, rfl⟩ | ⟨cv, nP, nF, -, rfl⟩
      · exact ⟨_, rfl, rfl⟩
      · exact ⟨_, rfl, rfl⟩
    obtain ⟨ci₁, hname₁, rfl⟩ := henv₁
    rcases List.mem_cons.mp hci with rfl | hci
    · refine checkIndFold_mono rest _ env₂ h ci.name ?_
      rw [Env.find?_cons, if_pos (by rw [hname₁, hnameA])]
      rfl
    · exact checkIndFold_stored rest _ env₂ h ci hci

end ConLeche
