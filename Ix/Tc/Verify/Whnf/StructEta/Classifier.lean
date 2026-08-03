import Ix.Tc.Verify.Whnf.StructEta.RecursionClassifier

/-!
# Struct-eta classifier state closure

RecursionClassifier verifies the cached recursion classifier and the recursor-type scan in
isolation.  This slice composes the first of those contracts through the
actual `isStructLike` dispatcher.  In particular, all defensive rejection
branches retain the state delivered by lazy lookup, while the one qualified
inductive branch inherits the complete cache-transaction proof.

The result contract is intentionally state-only.  Being non-recursive with
one constructor and no indices is not, by itself, a Theory proof of the
struct-eta equation selected later in the reducer.
-/

namespace Ix.Tc
namespace RecM

/-- Exact typed/effect input for the recursor declaration instance scanned by
struct eta.

Production first observes one concrete declaration through `tryGetConst` and
then instantiates that declaration's polymorphic type at the recursor
application's universe arguments.  This boundary is indexed by that lookup
equation and owns the finite walker coverage plus the admission-derived
translation of its successful result.  It cannot supply a different
declaration or bypass the actual instantiation computation. -/
structure StructEtaRecursorInputOracle
    (trProj : RawProjRel) (world : VerifyWorld)
    (support : RunSupport) : Prop where
  instantiate :
    ∀ {layer : WhnfLayer} {semantics : CacheSemantics}
      {uvars : Nat} {Delta : KVLCtx}
      {recId : KId .anon} {before after : TcState .anon}
      {entry : KConst .anon} {recUs : Array (KUniv .anon)},
    TcM.tryGetConst recId before = .ok (some entry) after →
      TcM.WF
        (WhnfStateInv layer semantics trProj world support uvars Delta)
        after (TcM.instantiateUnivParams entry.ty recUs)
        (fun recTy _ =>
          support recTy ∧ ∃ recTyV,
            TrKExprS world.venv uvars world.nameOf trProj Delta recTy recTyV)

/-- The production structure classifier preserves the complete WHNF
invariant on missing and non-inductive declarations, malformed inductive
shapes, cache hits, lazy-ingress errors, and every recursion-classifier exit.

The write oracle is indexed by the queried inductive because a provisional
`true` marker and a final computed Boolean have distinct semantic authority.
-/
theorem isStructLike_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
    {id : KId .anon} {s : TcState .anon}
    (hmethods :
      Methods.WFAt layer semantics trProj world support uvars methods)
    (hinputs : ConstructorTelescopeInputSupport support)
    (hctorInputs : ConstructorTelescopeInputOracle trProj world support)
    (hfault : TcM.LazyFaultPreserves
      (WhnfStateInv layer semantics trProj world support uvars Delta))
    (hwrites : IsRecCacheWriteOracle semantics world support methods id) :
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Delta) s
      ((isStructLike id).run methods) (fun _ _ => True) := by
  unfold isStructLike
  rw [ReaderT.run_bind, ReaderT.run_monadLift]
  apply TcM.WF.bind (TcM.tryGetConst_wf hfault id s)
  intro found afterLookup _
  cases found with
  | none => exact TcM.WF.pure fun _ => trivial
  | some entry =>
      cases entry <;> simp only
      all_goals try exact TcM.WF.pure (Q := fun _ _ => True) (fun _ => trivial)
      case indc name levelParams lvls params indices isUnsafe block memberIdx
          ty ctors leanAll =>
        split
        · exact TcM.WF.pure fun _ => trivial
        · rw [ReaderT.run_bind]
          apply TcM.WF.bind
            (computedIsRec_wf (s := afterLookup) hmethods hinputs hctorInputs
              hfault hwrites)
          intro recursive afterRec _
          exact TcM.WF.pure fun _ => trivial

/-- Fixed-method state rule for production's non-backtracking optional
wrapper.  A caught error becomes `none` in the callback's partial post-state,
so the invariant proved by the error arm is the one that must be retained. -/
theorem tryOptional_state_wf {I : TcState .anon → Prop}
    {methods : Methods .anon} {x : RecM .anon α} {s : TcState .anon}
    (hx : TcM.WF I s (x.run methods) (fun _ _ => True)) :
    TcM.WF I s ((tryOptional x).run methods) (fun _ _ => True) := by
  intro hI
  have hrunWF := hx hI
  rw [tryOptional_run]
  cases hrun : x.run methods s with
  | ok value after =>
      rw [hrun] at hrunWF
      exact ⟨hrunWF.1, trivial⟩
  | error err after =>
      rw [hrun] at hrunWF
      exact ⟨hrunWF.1, trivial⟩

/-- Fixed-method optional wrapper retaining the successful payload's exact
postcondition.  This is the form needed when the payload is the trusted
inductive certificate returned by `getMajorInductiveId_trusted_wf`. -/
theorem tryOptional_fixed_wf
    {I : TcState .anon → Prop} {methods : Methods .anon}
    {x : RecM .anon α} {s : TcState .anon}
    {Q : α → TcState .anon → Prop}
    (hx : TcM.WF I s (x.run methods) Q) :
    TcM.WF I s ((tryOptional x).run methods)
      (fun result after => match result with
        | some value => Q value after
        | none => True) := by
  intro hI
  have hrunWF := hx hI
  rw [tryOptional_run]
  cases hrun : x.run methods s with
  | ok value after =>
      rw [hrun] at hrunWF
      exact hrunWF
  | error err after =>
      rw [hrun] at hrunWF
      exact ⟨hrunWF.1, trivial⟩

/-- Exact remaining callback boundary after the recursor-type prefix has
selected a candidate inductive.  Classifier uses this interface to close the
dispatcher without pretending that the inference probes, universe walker,
or generated intern requests are state-free. -/
def StructEtaAfterInductivePreserves (I : TcState .anon → Prop)
    (methods : Methods .anon) : Prop :=
  ∀ recUs spine recr rule indId s,
    TcM.WF I s
      ((tryStructEtaAfterInductive recUs spine recr rule indId).run methods)
      (fun _ _ => True)

/-- Legacy state-only contract for an arbitrary infer-only back-edge.  The
production struct-eta path below no longer consumes this authority: it
instantiates `Methods.WF` at the exact major and inferred outputs.  The
definition remains for the older state-only K-synthesis lemmas. -/
def InferOnlyCallbackPreserves (I : TcState .anon → Prop)
    (methods : Methods .anon) : Prop :=
  ∀ e s,
    TcM.WF I s ((inferOnlyRec e).run methods) (fun _ _ => True)

/-- Remaining effect boundary after all structure and H3 probes succeed.
It consists precisely of universe instantiation followed by the finite
projection/application rebuild. -/
def StructEtaFinishPreserves (I : TcState .anon → Prop)
    (methods : Methods .anon) : Prop :=
  ∀ recUs spine recr rule indId major majorSortW s,
    TcM.WF I s
      ((finishStructEtaAfterSort recUs spine recr rule indId major
        majorSortW).run methods)
      (fun _ _ => True)

/-- Compose structure classification with two exact infer-only calls and the
exact WHNF call on the inferred sort.  Each predecessor-table call is
instantiated from `Methods.WF` at a supported structural translation; the
resulting post-inductive contract leaves only `finishStructEtaAfterSort` as
an explicit state boundary. -/
theorem tryStructEtaAfterInductive_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
    {recUs : Array (KUniv .anon)} {spine : Array (KExpr .anon)}
    {recr : IotaInfo .anon} {rule : RecRule .anon} {indId : KId .anon}
    {s : TcState .anon}
    (hmethods :
      Methods.WFAt layer semantics trProj world support uvars methods)
    (hinputs : ConstructorTelescopeInputSupport support)
    (hctorInputs : ConstructorTelescopeInputOracle trProj world support)
    (hfault : TcM.LazyFaultPreserves
      (WhnfStateInv layer semantics trProj world support uvars Delta))
    (hwrites : IsRecCacheWriteOracle semantics world support methods indId)
    {majorV : Lean4Lean.VExpr}
    (hmajorSupport : support spine[recr.majorIdx]!)
    (hmajorTr : TrKExprS world.venv uvars world.nameOf trProj Delta
      spine[recr.majorIdx]! majorV)
    (hfinish : StructEtaFinishPreserves
      (WhnfStateInv layer semantics trProj world support uvars Delta)
      methods) :
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Delta) s
      ((tryStructEtaAfterInductive recUs spine recr rule indId).run methods)
      (fun _ _ => True) := by
  unfold tryStructEtaAfterInductive
  rw [ReaderT.run_bind]
  apply TcM.WF.bind
    (isStructLike_wf hmethods hinputs hctorInputs hfault hwrites)
  intro structLike afterStruct _
  cases structLike with
  | false => exact TcM.WF.pure fun _ => trivial
  | true =>
      simp only [Bool.not_true, Bool.false_eq_true, if_false, pure_bind]
      rw [ReaderT.run_bind]
      apply TcM.WF.bind
        ((tryOptionalInferOnlyRec_wf
          (s := afterStruct) hmajorSupport hmajorTr) methods hmethods)
      intro foundMajorTy afterMajor hfoundMajorTy
      cases foundMajorTy with
      | none => exact TcM.WF.pure fun _ => trivial
      | some majorTy =>
          obtain ⟨hmajorTySupport, majorTyV, hmajorTy, _⟩ :=
            hfoundMajorTy
          obtain ⟨majorTyStructuralV, hmajorTyTr, _⟩ := hmajorTy
          rw [ReaderT.run_bind]
          apply TcM.WF.bind
            ((tryOptionalInferOnlyRec_wf
              (s := afterMajor) hmajorTySupport hmajorTyTr) methods hmethods)
          intro foundMajorSort afterSort hfoundMajorSort
          cases foundMajorSort with
          | none => exact TcM.WF.pure fun _ => trivial
          | some majorSort =>
              obtain ⟨hmajorSortSupport, majorSortV, hmajorSort, _⟩ :=
                hfoundMajorSort
              obtain ⟨majorSortStructuralV, hmajorSortTr, _⟩ := hmajorSort
              rw [ReaderT.run_bind]
              apply TcM.WF.bind
                ((tryOptionalWhnfRec_wf
                  (s := afterSort) hmajorSortSupport hmajorSortTr)
                  methods hmethods)
              intro foundMajorSortW afterWhnf _hfoundMajorSortW
              cases foundMajorSortW with
              | none => exact TcM.WF.pure fun _ => trivial
              | some majorSortW =>
                  exact hfinish recUs spine recr rule indId
                    spine[recr.majorIdx]! majorSortW afterWhnf

/-- Trusted-result refinement of the struct-eta prefix.  The successful
optional scan retains its selected-ID trust proof; misses and caught errors
remain state-only. -/
theorem tryStructEtaIota_trusted_prefix_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
    {recId : KId .anon} {recr : IotaInfo .anon}
    {recUs : Array (KUniv .anon)} {spine : Array (KExpr .anon)}
    {s : TcState .anon}
    (hmethods :
      Methods.WFAt layer semantics trProj world support uvars methods)
    (hinputs : MajorTelescopeInputSupport support)
    (hrecInputs : StructEtaRecursorInputOracle trProj world support)
    (hfault : ∀ {current : KVLCtx},
      TcM.LazyFaultPreserves
        (WhnfStateInv layer semantics trProj world support uvars current))
    (hreferences : TrustedReferences world support)
    (hafter : ∀ indId afterScan,
      world.trusted indId →
      TcM.WF
        (WhnfStateInv layer semantics trProj world support uvars Delta)
        afterScan
        ((tryStructEtaAfterInductive recUs spine recr recr.rules[0]!
          indId).run methods)
        (fun _ _ => True)) :
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Delta) s
      ((tryStructEtaIota recId recr recUs spine).run methods)
      (fun _ _ => True) := by
  unfold tryStructEtaIota
  by_cases hrules : (recr.rules.size != 1) = true
  · simp only [hrules, if_true]
    exact TcM.WF.pure fun _ => trivial
  · simp only [hrules, Bool.false_eq_true, if_false]
    by_cases hlevels : (recUs.size.toUInt64 != recr.lvls) = true
    · simp only [hlevels, if_true]
      exact TcM.WF.pure fun _ => trivial
    · simp only [hlevels, Bool.false_eq_true, if_false, pure_bind]
      rw [ReaderT.run_bind, ReaderT.run_monadLift]
      apply TcM.WF.bind
        (Q₁ := fun found after =>
          TcM.tryGetConst recId s = .ok found after)
        (TcM.WF.mono
          (TcM.WF.with_run_eq
            (TcM.tryGetConst_wf (hfault (current := Delta)) recId s))
          (fun _ _ h => h.2) (fun _ _ _ => trivial))
      intro found afterLookup hlookup
      cases found with
      | none => exact TcM.WF.pure fun _ => trivial
      | some entry =>
          simp only
          rw [ReaderT.run_bind]
          apply TcM.WF.bind (tryOptional_fixed_wf (by
            rw [ReaderT.run_bind, ReaderT.run_monadLift, monadLift_self]
            apply TcM.WF.bind (hrecInputs.instantiate hlookup)
            intro recTy afterInst hrecTy
            obtain ⟨hrecSupport, recTyV, hrecTr⟩ := hrecTy
            exact getMajorInductiveId_trusted_wf hmethods hinputs hfault
              hreferences
              (recr.params + recr.motives + recr.minors +
                recr.indices).toUInt64
              hrecSupport hrecTr))
          intro foundInd afterScan htrusted
          cases foundInd with
          | none => exact TcM.WF.pure fun _ => trivial
          | some indId =>
              exact hafter indId afterScan htrusted

/-- State-only compatibility form of the complete struct-eta prefix.  Its
successful branch is implemented through the trusted refinement above, so it
cannot accidentally regress to an untyped raw recursor scan. -/
theorem tryStructEtaIota_prefix_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
    {recId : KId .anon} {recr : IotaInfo .anon}
    {recUs : Array (KUniv .anon)} {spine : Array (KExpr .anon)}
    {s : TcState .anon}
    (hmethods :
      Methods.WFAt layer semantics trProj world support uvars methods)
    (hinputs : MajorTelescopeInputSupport support)
    (hrecInputs : StructEtaRecursorInputOracle trProj world support)
    (hfault : ∀ {current : KVLCtx},
      TcM.LazyFaultPreserves
        (WhnfStateInv layer semantics trProj world support uvars current))
    (hreferences : TrustedReferences world support)
    (hafter : StructEtaAfterInductivePreserves
      (WhnfStateInv layer semantics trProj world support uvars Delta)
      methods) :
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Delta) s
      ((tryStructEtaIota recId recr recUs spine).run methods)
      (fun _ _ => True) :=
  tryStructEtaIota_trusted_prefix_wf hmethods hinputs hrecInputs hfault
    hreferences (fun indId afterScan _ =>
      hafter recUs spine recr recr.rules[0]! indId afterScan)

/-- Full state-preservation contract for the struct-eta dispatcher.  It is
exhaustive over concrete control flow; the remaining premises are narrowly
scoped semantic/effect authorities for recursion-cache writes, callbacks,
and the successful finite rebuild tail. -/
theorem tryStructEtaIota_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
    {recId : KId .anon} {recr : IotaInfo .anon}
    {recUs : Array (KUniv .anon)} {spine : Array (KExpr .anon)}
    {s : TcState .anon}
    (hmethods :
      Methods.WFAt layer semantics trProj world support uvars methods)
    (hinputs : ConstructorTelescopeInputSupport support)
    (hctorInputs : ConstructorTelescopeInputOracle trProj world support)
    (hrecInputs : StructEtaRecursorInputOracle trProj world support)
    (hfault : ∀ {current : KVLCtx},
      TcM.LazyFaultPreserves
        (WhnfStateInv layer semantics trProj world support uvars current))
    (hreferences : TrustedReferences world support)
    (hwrites : ∀ id, world.trusted id →
      IsRecCacheWriteOracle semantics world support methods id)
    {majorV : Lean4Lean.VExpr}
    (hmajorSupport : support spine[recr.majorIdx]!)
    (hmajorTr : TrKExprS world.venv uvars world.nameOf trProj Delta
      spine[recr.majorIdx]! majorV)
    (hfinish : StructEtaFinishPreserves
      (WhnfStateInv layer semantics trProj world support uvars Delta)
      methods) :
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Delta) s
      ((tryStructEtaIota recId recr recUs spine).run methods)
      (fun _ _ => True) := by
  apply tryStructEtaIota_trusted_prefix_wf hmethods hinputs hrecInputs hfault
    hreferences
  intro indId afterScan htrusted
  exact tryStructEtaAfterInductive_wf hmethods hinputs hctorInputs
    (hfault (current := Delta))
    (hwrites indId htrusted) hmajorSupport hmajorTr hfinish

end RecM
end Ix.Tc
