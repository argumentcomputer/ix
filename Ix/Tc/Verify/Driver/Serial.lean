import Ix.Tc.Verify.Driver.Enumeration

/-!
# Serial `checkEnvAnon` composition

This file connects the result-only public driver API back to the successful
per-item checker calls which produced it.  A failed call always contributes
at least one `CheckResult` for a well-formed production work item, so an
all-success result array yields a concrete serial success trace.

`CheckSuccessSound` is the named C2 adapter: it consumes an actual successful
`TcM.checkConst` execution and returns the reusable semantic admission rule
needed by dependency-order composition.  The serial corollary therefore does
not assume `AllAccepted` directly.
-/

namespace Ix.Tc

/-- Every public result row reports success. -/
def AllCheckResultsSucceeded (results : Array CheckResult) : Prop :=
  ∀ result, result ∈ results → result.err? = none

@[simp] theorem finishAnonCheckItem_results
    (cfg : CheckCfg) (before : AnonCheckLoopState)
    (item : AnonWorkItem) (checker : TcState .anon)
    (err? : Option String) :
    (finishAnonCheckItem cfg before item checker err?).results =
      before.results ++ item.targets.map fun target => ⟨target, err?⟩ := by
  simp [finishAnonCheckItem]
  split <;> rfl

/-- One loop step never removes an already emitted result. -/
theorem runAnonCheckItem_preserves_result
    (cfg : CheckCfg) (before : AnonCheckLoopState)
    (item : AnonWorkItem) {result : CheckResult}
    (hresult : result ∈ before.results) :
    result ∈ (runAnonCheckItem cfg before item).results := by
  cases hrun : (TcM.checkConst
      (⟨item.primary, ()⟩ : KId .anon)).run before.checker with
  | ok value checker =>
      cases value
      simp only [runAnonCheckItem, hrun, finishAnonCheckItem_results]
      exact Array.mem_append.mpr (.inl hresult)
  | error err checker =>
      simp only [runAnonCheckItem, hrun, finishAnonCheckItem_results]
      exact Array.mem_append.mpr (.inl hresult)

/-- The recursive serial loop never removes an existing result. -/
theorem runAnonCheckList_preserves_result
    (cfg : CheckCfg) (work : List AnonWorkItem)
    (before : AnonCheckLoopState) {result : CheckResult}
    (hresult : result ∈ before.results) :
    result ∈ (runAnonCheckList cfg work before).results := by
  induction work generalizing before with
  | nil => exact hresult
  | cons item rest ih =>
      apply ih
      exact runAnonCheckItem_preserves_result cfg before item hresult

/-- A failed checker call contributes a row carrying that failure for every
target of the item. -/
theorem runAnonCheckItem_error_result
    (cfg : CheckCfg) (before : AnonCheckLoopState)
    (item : AnonWorkItem) {err : TcError .anon} {checker : TcState .anon}
    (hrun : (TcM.checkConst
      (⟨item.primary, ()⟩ : KId .anon)).run before.checker =
        .error err checker)
    {target : Address} (htarget : target ∈ item.targets) :
    (⟨target, some (toString err)⟩ : CheckResult) ∈
      (runAnonCheckItem cfg before item).results := by
  simp only [runAnonCheckItem, hrun, finishAnonCheckItem_results]
  apply Array.mem_append.mpr
  exact .inr (Array.mem_map_of_mem htarget)

/-- Exact successful-call trace of the serial production loop.  Cache
clearing is retained in the indexed next accumulator. -/
inductive SerialChecksSucceeded (cfg : CheckCfg) :
    AnonCheckLoopState → List AnonWorkItem → Prop
  | nil (state) : SerialChecksSucceeded cfg state []
  | cons {before : AnonCheckLoopState} {item : AnonWorkItem}
      {rest : List AnonWorkItem} {checker : TcState .anon} :
      (TcM.checkConst
        (⟨item.primary, ()⟩ : KId .anon)).run before.checker =
          .ok () checker →
      SerialChecksSucceeded cfg
        (finishAnonCheckItem cfg before item checker none) rest →
      SerialChecksSucceeded cfg before (item :: rest)

/-- An all-success public result array exposes the exact successful checker
call for every work item.  Nonempty target arrays are essential: without
them a failing item could emit no observable row. -/
theorem serialChecksSucceeded_of_results
    (cfg : CheckCfg) (work : List AnonWorkItem)
    (before : AnonCheckLoopState)
    (hnonempty : ∀ item, item ∈ work →
      ∃ target, target ∈ item.targets)
    (hresults : AllCheckResultsSucceeded
      (runAnonCheckList cfg work before).results) :
    SerialChecksSucceeded cfg before work := by
  induction work generalizing before with
  | nil => exact .nil before
  | cons item rest ih =>
      cases hrun : (TcM.checkConst
          (⟨item.primary, ()⟩ : KId .anon)).run before.checker with
      | ok value checker =>
          cases value
          apply SerialChecksSucceeded.cons hrun
          apply ih
          · intro candidate hcandidate
            exact hnonempty candidate (by simp [hcandidate])
          · simpa [runAnonCheckList, runAnonCheckItem, hrun] using hresults
      | error err checker =>
          exfalso
          obtain ⟨target, htarget⟩ := hnonempty item (by simp)
          let failed : CheckResult := ⟨target, some (toString err)⟩
          have hfailedStep : failed ∈
              (runAnonCheckItem cfg before item).results := by
            exact runAnonCheckItem_error_result cfg before item hrun htarget
          have hfailedFinal : failed ∈
              (runAnonCheckList cfg rest
                (runAnonCheckItem cfg before item)).results :=
            runAnonCheckList_preserves_result cfg rest _ hfailedStep
          have hnone := hresults failed (by
            simpa [runAnonCheckList] using hfailedFinal)
          simp [failed] at hnone

namespace SerialChecksSucceeded

/-- Every list member has a concrete successful production call somewhere
in the serial trace. -/
theorem successfulStep {cfg : CheckCfg} {initial : AnonCheckLoopState}
    {work : List AnonWorkItem}
    (h : SerialChecksSucceeded cfg initial work)
    {item : AnonWorkItem} (hitem : item ∈ work) :
    ∃ before : AnonCheckLoopState, ∃ checker : TcState .anon,
      (TcM.checkConst
        (⟨item.primary, ()⟩ : KId .anon)).run before.checker =
          .ok () checker := by
  induction h with
  | nil state => simp at hitem
  | @cons before head rest checker hrun hrest ih =>
      rcases List.mem_cons.mp hitem with hhead | htail
      · subst item
        exact ⟨before, checker, hrun⟩
      · exact ih htail

end SerialChecksSucceeded

/-- The concrete C2 adapter used by the serial corollary.  Its premise is an
actual successful `TcM.checkConst` call; its conclusion is the reusable
dependency-relative admission rule produced by the K3/E0 per-item theorem. -/
def CheckSuccessSound (baseline : VerifyWorld)
    (catalog : DependencyCatalog) (work : Array AnonWorkItem) : Prop :=
  ∀ item, item ∈ work →
    ∀ {before : AnonCheckLoopState} {checker : TcState .anon},
      (TcM.checkConst
        (⟨item.primary, ()⟩ : KId .anon)).run before.checker =
          .ok () checker →
      ∀ current, baseline ≤ current →
        (∀ {target}, catalog.dependsOn item.root target →
          catalog.blockOf target ≠ item.root →
          current.AcceptsAddress target) →
        ∃ after, current ≤ after ∧ WorkItemAccepted after item

/-- A successful serial trace plus the concrete C2 adapter constructs the
abstract admission predicate needed by topological composition. -/
theorem SerialChecksSucceeded.allAccepted
    {cfg : CheckCfg} {initial : AnonCheckLoopState}
    {work : Array AnonWorkItem} {baseline : VerifyWorld}
    {catalog : DependencyCatalog}
    (htrace : SerialChecksSucceeded cfg initial work.toList)
    (hsound : CheckSuccessSound baseline catalog work) :
    AllAccepted baseline catalog work := by
  intro item hitem current hbaseline hdeps
  have hitemList : item ∈ work.toList := by simpa using hitem
  obtain ⟨before, checker, hrun⟩ := htrace.successfulStep hitemList
  exact hsound item hitem hrun current hbaseline hdeps

namespace AnonWorkEnvWF

/-- Normal form of the public serial driver on a structurally valid Ixon
environment. -/
theorem checkEnvAnon_eq_serial {env : Ixon.Env}
    (h : AnonWorkEnvWF env) (cfg : CheckCfg) :
    checkEnvAnon env cfg = .ok
      (runAnonCheckList cfg (expectedAnonWork env).toList
        (initialAnonCheckLoopState env cfg)).results := by
  unfold checkEnvAnon
  rw [h.buildAnonWork_eq_expected]
  rfl

/-- E1's production serial-driver corollary.  All emitted rows succeeding is
converted to concrete per-item success traces, those traces are interpreted
through the C2 success rule, and the resulting admissions are reordered by
the proved collapsed-block schedule. -/
theorem checkEnvAnon_subjectWF
    {env : Ixon.Env} (h : AnonWorkEnvWF env)
    (hblock : IxonEnv.BlockOfIdempotent env)
    {baseline : VerifyWorld} {assumptions : FiniteAddressSet}
    (hdeps : DepsClosed (IxonEnv.dependencyCatalog env hblock)
      (expectedAnonWork env) h.subjects assumptions)
    (hwf : WellFoundedBlocks (IxonEnv.dependencyCatalog env hblock)
      (expectedAnonWork env) h.subjects)
    (hassumptions : AssumptionsWF baseline assumptions)
    (hdisjoint : h.subjects.Disjoint assumptions)
    (hsound : CheckSuccessSound baseline
      (IxonEnv.dependencyCatalog env hblock) (expectedAnonWork env))
    (cfg : CheckCfg) {results : Array CheckResult}
    (hrun : checkEnvAnon env cfg = .ok results)
    (hresults : AllCheckResultsSucceeded results) :
    SubjectWF baseline (IxonEnv.dependencyCatalog env hblock)
      (expectedAnonWork env) h.subjects assumptions := by
  rw [h.checkEnvAnon_eq_serial cfg] at hrun
  have hresultsEq := Except.ok.inj hrun
  rw [← hresultsEq] at hresults
  have hnonempty : ∀ item, item ∈ (expectedAnonWork env).toList →
      ∃ target, target ∈ item.targets := by
    intro item hitem
    refine ⟨item.primary, ?_⟩
    exact h.expected_primary_mem_targets (by simpa using hitem)
  have htrace := serialChecksSucceeded_of_results cfg
    (expectedAnonWork env).toList (initialAnonCheckLoopState env cfg)
    hnonempty hresults
  exact acceptedWorkset_subjectWF (htrace.allAccepted hsound)
    h.expectedAnonWork_covers hdeps hwf hassumptions hdisjoint

end AnonWorkEnvWF

end Ix.Tc
