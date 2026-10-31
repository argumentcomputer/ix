module

public import IxC.Kernel.Verify.Cached.Reference
import IxC.Kernel.Verify.Cached.KnotCongr

public section

/-!
# Per-block admission: the specification of the deferred fold

LOCALITY §6(c) and §7 (G5). The executed fold `Cached.checkDecls` installs
every declaration first (phase A) and checks the recorded value groups
afterwards (phase B, on tasks), each against the prefix view of the final
index at the size it had when the record was made. **Per-block admission**
(`checkDeclsPB`) checks each step's records right after the step, at the index
the step returned. The two accept exactly the same inputs with the same
environment (`checkDecls_ok_iff_PB`); only the reported failure can differ,
because the first failure is found in another order. So the deferral is for
parallelism, not correctness, and the per-block fold is the specification
later statements may use; the executed code keeps its parallel phase B.

The argument: phase A is the same in both folds (a per-block step starts with
the same `annotDeclStep`); every record's view is a prefix of the index at
which it is checked (`RecordsAt`: its `vis` is the size of the environment it
was installed at, which every later index extends); and a record's check
reads the index only through that view (`checkPending_view_congr`), whose
lookups are the install environment's at every later index
(`restrictTo_find?_of_extends`).
-/

namespace Ix.Kernel.Cached

open Ix.Kernel

variable {mode : CheckMode} {ev : Evidences md}

/-! ## The per-block fold -/

/-- **Per-block admission of one declaration**: phase A's step, then the
records that step added, each checked at the index the step returned, from a
fresh memo state. -/
def admitStep (mode : CheckMode) (ev : Evidences md)
    (p : Nat × FEnv md × Array (PendingCheck md)) (pd : Declaration md) :
    StateT (CState md) (Except (CheckError md × Nat)) (Nat × FEnv md × Array (PendingCheck md)) :=
  fun s =>
    match annotDeclStep mode ev p pd s with
    | .error e => .error e
    | .ok (q, s') =>
      match checkPendingList mode q.2.1 (q.2.2.toList.drop p.2.2.size) with
      | .error e => .error e
      | .ok () => .ok (q, s')

/-- **The per-block fold**: `admitStep` over the declarations, from the
empty index and memo state, then the units check (`checkUnits`), as the
deferred fold ends. -/
def checkDeclsPB (mode : CheckMode) (ev : Evidences md) (ds : Array (Declaration md)) :
    Except (CheckError md × Nat) (Env md) :=
  match (ds.toList.foldlM (admitStep mode ev) (0, mkFEnv Env.empty, #[])) {} with
  | .ok (p, _) => checkUnits ds >>= fun _ => .ok p.2.1.env
  | .error e => .error e

/-! ## Records and their views -/

/-- A step's new records are made at the index it started from: each one's
view is that index's counter. -/
theorem annotStepC_vis (mode : CheckMode) (i : Nat) (fe : FEnv md)
    (pend : Array (PendingCheck md)) (pd : Declaration md) :
    Yields (annotStepC mode ev i fe pend pd)
      (fun r => ∃ new, r.2.toList = pend.toList ++ new ∧ ∀ pc ∈ new, pc.vis = fe.visibleBelow) := by
  have hord : ∀ pd', Yields (do pure (← checkDeclStepC mode ev fe pd', pend) :
      (CheckCM md) (FEnv md × Array (PendingCheck md)))
      (fun r => ∃ new, r.2.toList = pend.toList ++ new ∧ ∀ pc ∈ new, pc.vis = fe.visibleBelow) :=
    fun _ => Yields.bind fun _ => Yields.pure ⟨[], by simp, by simp⟩
  unfold annotStepC
  cases pd with
  | defnDecl cv value hint =>
    simp only []
    split
    · exact hord _
    · exact Yields.bind fun _ => Yields.pure ⟨[_], Array.toList_push, by simp⟩
  | thmDecl cv value =>
    simp only []
    exact Yields.bind fun _ => Yields.bind fun _ => Yields.pure ⟨[_], Array.toList_push, by simp⟩
  | opaqueDecl cv value =>
    simp only []
    exact Yields.bind fun _ => Yields.pure ⟨[_], Array.toList_push, by simp⟩
  | axiomDecl cv => exact hord _
  | basisDecl kind => exact hord _
  | quotDecl k cv => exact hord _
  | indDecl block nP => exact hord _

/-- **The records' views are prefixes of `env`**: each record's view is the
size of an environment `env` extends (the one it was installed at). -/
def RecordsAt (env : Env md) (pend : List (PendingCheck md)) : Prop :=
  ∀ pc ∈ pend, ∃ (E : Env md) (new : List (ConstantInfo md)),
    pc.vis = E.consts.length ∧ env.consts = new ++ E.consts

theorem RecordsAt.nil (env : Env md) : RecordsAt env [] := fun _ h => (List.not_mem_nil h).elim

/-- The records' views stay prefixes along an extension. -/
theorem RecordsAt.extend {env env' : Env md} {pend : List (PendingCheck md)}
    (h : RecordsAt env pend) {more : List (ConstantInfo md)} (hext : env'.consts = more ++ env.consts) :
    RecordsAt env' pend := by
  intro pc hpc
  obtain ⟨E, new, hv, he⟩ := h pc hpc
  exact ⟨E, more ++ new, hv, by rw [hext, he, List.append_assoc]⟩

/-- A name-unique environment's suffixes are name-unique. -/
theorem NodupNames.of_extends {env env' : Env md} {more : List (ConstantInfo md)}
    (h : NodupNames env') (hext : env'.consts = more ++ env.consts) : NodupNames env := by
  unfold NodupNames at h ⊢
  rw [hext, List.map_append] at h
  exact (List.nodup_append.mp h).2.1

/-- **A record's check reads the index only through its view.** -/
theorem checkPending_view_congr {fe₁ fe₂ : FEnv md} {pc : PendingCheck md}
    (h : (fe₁.restrictTo pc.vis).find? = (fe₂.restrictTo pc.vis).find?) (s : CState md) :
    checkPending mode fe₁ pc s = checkPending mode fe₂ pc s := by
  simp only [checkPending, coreKnotI_congr h, opSIxC_congr h, annotValC_congr h]

/-- Two canonical, name-unique indices extending one environment `E` have
the same view at `E`'s size. -/
theorem view_eq_of_extends {fe₁ fe₂ : FEnv md} {E : Env md}
    {new₁ new₂ : List (ConstantInfo md)}
    (c₁ : fe₁ = mkFEnv fe₁.env) (n₁ : NodupNames fe₁.env) (x₁ : fe₁.env.consts = new₁ ++ E.consts)
    (c₂ : fe₂ = mkFEnv fe₂.env) (n₂ : NodupNames fe₂.env) (x₂ : fe₂.env.consts = new₂ ++ E.consts) :
    (fe₁.restrictTo E.consts.length).find? = (fe₂.restrictTo E.consts.length).find? :=
  funext fun n => by
    rw [restrictTo_find?_of_extends c₁ n₁ x₁, restrictTo_find?_of_extends c₂ n₂ x₂]

/-- One record of a list whose views are prefixes. -/
theorem RecordsAt.single {env : Env md} {pend : List (PendingCheck md)} (h : RecordsAt env pend)
    {pc : PendingCheck md} (hpc : pc ∈ pend) : RecordsAt env [pc] := by
  intro x hx
  rw [List.mem_singleton.mp hx]
  exact h pc hpc

/-- **A record checked at one index is checked at every later one**: at
two canonical, name-unique indices, the later extending the earlier, a
record whose view is a prefix of the earlier is checked alike. -/
theorem checkPending_transport {fe₁ fe₂ : FEnv md} {pc : PendingCheck md}
    (c₁ : fe₁ = mkFEnv fe₁.env) (n₁ : NodupNames fe₁.env)
    (c₂ : fe₂ = mkFEnv fe₂.env) (n₂ : NodupNames fe₂.env)
    {more : List (ConstantInfo md)} (hext : fe₂.env.consts = more ++ fe₁.env.consts)
    (h₁ : RecordsAt fe₁.env [pc]) (s : CState md) :
    checkPending mode fe₁ pc s = checkPending mode fe₂ pc s := by
  obtain ⟨E, new₁, hv, x₁⟩ := h₁ pc (List.mem_singleton_self pc)
  apply checkPending_view_congr
  rw [hv]
  exact view_eq_of_extends c₁ n₁ x₁ c₂ n₂ (by rw [hext, x₁, List.append_assoc])

/-! ## Phase A's step keeps the records' views -/

/-- One accepting phase-A step from a canonical index whose records' views
are prefixes keeps them prefixes, with the step's new records made at the
index it started from. -/
theorem annotDeclStep_records {p p₁ : Nat × FEnv md × Array (PendingCheck md)}
    {pd : Declaration md} {s s₁ : CState md}
    (hstep : annotDeclStep mode ev p pd s = .ok (p₁, s₁))
    (hfe : p.2.1 = mkFEnv p.2.1.env) (hrec : RecordsAt p.2.1.env p.2.2.toList) :
    p₁.2.1 = mkFEnv p₁.2.1.env ∧
      (∃ more, p₁.2.1.env.consts = more ++ p.2.1.env.consts) ∧
      (NodupNames p.2.1.env → NodupNames p₁.2.1.env) ∧
      RecordsAt p₁.2.1.env p₁.2.2.toList ∧
      ∃ new, p₁.2.2.toList = p.2.2.toList ++ new := by
  obtain ⟨i, fe, pend⟩ := p
  obtain ⟨fe₁, pend₁, rfl, hstepC⟩ := annotDeclStep_ok hstep
  simp only at hfe hrec hstepC ⊢
  obtain ⟨hpush, -⟩ := annotStepC_push mode i (PushChain.self hfe) pend pd s (fe₁, pend₁) s₁ hstepC
  obtain ⟨new, hnew, hvis⟩ := annotStepC_vis mode i fe pend pd s (fe₁, pend₁) s₁ hstepC
  obtain ⟨more, hmore⟩ := hpush.2.1
  refine ⟨hpush.1, ⟨more, hmore⟩, hpush.2.2, fun pc hpc => ?_, ⟨new, hnew⟩⟩
  simp only at hnew
  rw [hnew] at hpc
  rcases List.mem_append.mp hpc with hold | hnw
  · exact RecordsAt.extend hrec hmore pc hold
  · refine ⟨fe.env, more, ?_, hmore⟩
    rw [hvis pc hnw]
    calc fe.visibleBelow = (mkFEnv fe.env).visibleBelow := by rw [← hfe]
      _ = fe.env.consts.length := mkFEnv_visibleBelow _


/-! ## The two folds accept alike -/

/-- The new records of a step, as the records past the step's start. -/
theorem drop_new {pend : Array (PendingCheck md)} {l new : List (PendingCheck md)}
    (h : l = pend.toList ++ new) : l.drop pend.size = new := by
  rw [h, ← Array.length_toList, List.drop_left]

/-- **An accepting per-block fold is an accepting install run whose records
all check at the final index.** -/
theorem admit_foldlM_inv :
    ∀ (ds : List (Declaration md)) (p : Nat × FEnv md × Array (PendingCheck md)) (s : CState md)
      {q : Nat × FEnv md × Array (PendingCheck md)} {s' : CState md},
      (ds.foldlM (admitStep mode ev) p) s = .ok (q, s') →
      p.2.1 = mkFEnv p.2.1.env → NodupNames p.2.1.env → RecordsAt p.2.1.env p.2.2.toList →
      (∀ pc ∈ p.2.2.toList, ∃ s'', checkPending mode p.2.1 pc {} = .ok ((), s'')) →
      InstallRun mode ev ds p s q s' ∧
        ∀ pc ∈ q.2.2.toList, ∃ s'', checkPending mode q.2.1 pc {} = .ok ((), s'')
  | [], p, s, q, s', h, _, _, _, hB => by
    simp only [List.foldlM_nil, pure, StateT.pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨.nil p s, hB⟩
  | pd :: ds, p, s, q, s', h, hfe, hnd, hrec, hB => by
    rw [List.foldlM_cons] at h
    simp only [Bind.bind, StateT.bind] at h
    cases hstep : admitStep mode ev p pd s with
    | error e => simp only [hstep, Except.bind] at h; exact nomatch h
    | ok r =>
      obtain ⟨p₁, s₁⟩ := r
      simp only [hstep, Except.bind] at h
      unfold admitStep at hstep
      cases ha : annotDeclStep mode ev p pd s with
      | error e => simp only [ha] at hstep; exact nomatch hstep
      | ok r' =>
        obtain ⟨p₁', s₁'⟩ := r'
        simp only [ha] at hstep
        cases hl : checkPendingList mode p₁'.2.1 (p₁'.2.2.toList.drop p.2.2.size) with
        | error e => simp only [hl] at hstep; exact nomatch hstep
        | ok u =>
          simp only [hl, Except.ok.injEq, Prod.mk.injEq] at hstep
          obtain ⟨rfl, rfl⟩ := hstep
          obtain ⟨hfe₁, ⟨more, hmore⟩, hnd₁, hrec₁, new, hnew⟩ := annotDeclStep_records ha hfe hrec
          have hnd₁' := hnd₁ hnd
          have hB₁ : ∀ pc ∈ p₁'.2.2.toList, ∃ s'', checkPending mode p₁'.2.1 pc {} = .ok ((), s'') := by
            intro pc hpc
            rw [hnew] at hpc
            rcases List.mem_append.mp hpc with hold | hnw
            · obtain ⟨s'', hs⟩ := hB pc hold
              exact ⟨s'', by
                rw [← checkPending_transport hfe hnd hfe₁ hnd₁' hmore (hrec.single hold)]
                exact hs⟩
            · exact checkPendingList_records mode p₁'.2.1 _ hl pc (by rw [drop_new hnew]; exact hnw)
          obtain ⟨hrun, hBq⟩ := admit_foldlM_inv ds p₁' s₁' h hfe₁ hnd₁' hrec₁ hB₁
          exact ⟨.cons ha hrun, hBq⟩

/-- **An accepting install run whose records all check at the final index is
an accepting per-block fold.** -/
theorem installRun_admit {ds : List (Declaration md)}
    {p q : Nat × FEnv md × Array (PendingCheck md)} {s s' : CState md}
    (hrun : InstallRun mode ev ds p s q s') :
    p.2.1 = mkFEnv p.2.1.env → RecordsAt p.2.1.env p.2.2.toList → NodupNames q.2.1.env →
    (∀ pc ∈ q.2.2.toList, ∃ s'', checkPending mode q.2.1 pc {} = .ok ((), s'')) →
    (ds.foldlM (admitStep mode ev) p) s = .ok (q, s') := by
  induction hrun with
  | nil p s => intro _ _ _ _; rfl
  | @cons pd ds p p₁ q s s₁ s' hstep rest ih =>
    intro hfe hrec hnd hB
    obtain ⟨hfe₁, -, -, hrec₁, new, hnew⟩ := annotDeclStep_records hstep hfe hrec
    obtain ⟨hchain, newq, hq⟩ := installRun_trace mode rest (PushChain.self hfe₁)
    obtain ⟨moreq, hmoreq⟩ := hchain.2.1
    have hnd₁ : NodupNames p₁.2.1.env := NodupNames.of_extends hnd hmoreq
    have hl : checkPendingList mode p₁.2.1 (p₁.2.2.toList.drop p.2.2.size) = .ok () := by
      apply checkPendingList_ok
      intro pc hpc
      rw [drop_new hnew] at hpc
      have hpc₁ : pc ∈ p₁.2.2.toList := by rw [hnew]; exact List.mem_append_right _ hpc
      obtain ⟨s'', hs⟩ := hB pc (by rw [hq]; exact List.mem_append_left _ hpc₁)
      exact ⟨s'', by
        rw [checkPending_transport hfe₁ hnd₁ hchain.1 hnd hmoreq (hrec₁.single hpc₁)]
        exact hs⟩
    rw [List.foldlM_cons]
    simp only [Bind.bind, StateT.bind]
    have hadmit : admitStep mode ev p pd s = .ok (p₁, s₁) := by
      unfold admitStep
      simp only [hstep, hl]
    rw [hadmit]
    exact ih hfe₁ hrec₁ hnd hB

/-- **Deferring the value checks changes no accepted environment**
(LOCALITY §7, G5): the executed fold and the per-block fold accept the same
declarations with the same environment. (The reported failure can differ.) -/
theorem checkDecls_ok_iff_PB {ds : Array (Declaration md)} {env : Env md} :
    checkDecls mode ev ds = .ok env ↔ checkDeclsPB mode ev ds = .ok env := by
  constructor
  · intro h
    have hu := checkDecls_units mode h
    obtain ⟨fc, rfl⟩ := checkDecls_fullyChecked mode h
    obtain ⟨n, s, r⟩ := fc.1.run
    have hchain := installRun_trace mode r (PushChain.refl Env.empty)
    have hfold := installRun_admit r rfl (RecordsAt.nil _) (hchain.1.2.2 List.nodup_nil)
      fc.records
    unfold checkDeclsPB
    rw [hfold]
    show (checkUnits ds >>= fun _ => Except.ok _) = _
    rw [hu]
    rfl
  · intro h
    unfold checkDeclsPB at h
    cases hf : (ds.toList.foldlM (admitStep mode ev) (0, mkFEnv Env.empty, #[])) {} with
    | error e => rw [hf] at h; exact nomatch h
    | ok r =>
      obtain ⟨⟨n, fe, pend⟩, s⟩ := r
      rw [hf] at h
      change (checkUnits ds >>= fun _ => Except.ok fe.env) = _ at h
      have hu : checkUnits ds = .ok () := by
        cases hu : checkUnits ds with
        | error e => rw [hu] at h; exact nomatch h
        | ok v => rfl
      rw [hu] at h
      obtain rfl : fe.env = env := Except.ok.inj h
      obtain ⟨hrun, hB⟩ := admit_foldlM_inv ds.toList _ _ hf rfl List.nodup_nil
        (RecordsAt.nil _) (fun _ h => (List.not_mem_nil h).elim)
      let e : InstalledEnv mode ev ds.toList := ⟨fe, pend, n, s, hrun⟩
      refine fullyChecked_checkDecls mode ⟨e, fun i => ?_⟩ hu
      unfold GroupChecked
      cases hi : e.pend[i]? with
      | none => trivial
      | some pc =>
        exact hB pc (List.mem_iff_getElem?.mpr ⟨i, by rw [Array.getElem?_toList]; exact hi⟩)

end Ix.Kernel.Cached
