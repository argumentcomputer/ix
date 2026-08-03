import Ix.Tc.Verify.Infer.LeafCases
import Ix.Tc.Verify.Whnf.Delta.StableCache

/-!
# Constant inference

This module verifies required constant lookup, universe-arity checking, and
type instantiation.  The trusted world currently retains only `RawExprRel`
for declaration types; inference needs the stronger typed `TrKExprS`
relation.  `TrustedConstTypes` names that boundary explicitly so the final K2
closure must derive it from declaration admission rather than silently
upgrading raw syntax correspondence.
-/

namespace Ix.Tc

namespace TcM

/-- A successful optional constant lookup returns a value that is installed
in the successful post-state. -/
theorem tryGetConst_loaded_wf {I : TcState .anon → Prop}
    (hfault : LazyFaultPreserves I) (id : KId .anon) (s : TcState .anon) :
    TcM.WF I s (TcM.tryGetConst id)
      (fun found after => ∀ c, found = some c →
        after.env.get? id = some c) := by
  unfold TcM.tryGetConst
  apply TcM.WF.bind
    (Q₁ := fun read after => read = after)
    (TcM.WF.get fun _ => rfl)
  intro read before hread
  subst read
  split
  · next c hget =>
      exact TcM.WF.pure fun _ result hresult => by
        cases hresult
        exact hget
  · apply TcM.WF.bind
      (Q₁ := fun read after => read = after)
      (TcM.WF.get fun _ => rfl)
    intro read beforeFault hread
    subst read
    apply TcM.WF.bind
      (Q₁ := fun _ _ => True)
      (TcM.lazyIngressAddr_wf hfault id.addr beforeFault)
    intro _ afterFault _
    apply TcM.WF.bind
      (Q₁ := fun read after => read = after)
      (TcM.WF.get fun _ => rfl)
    intro read after hread
    subst read
    split
    · next c hget =>
        exact TcM.WF.pure fun _ result hresult => by
          cases hresult
          exact hget
    · split
      · exact TcM.WF.throw fun _ => trivial
      · exact TcM.WF.pure fun _ result hresult => by
          cases hresult

/-- Required lookup has the same installed-result property; the optional
miss is converted to the production `unknownConst` error. -/
theorem getConst_loaded_wf {I : TcState .anon → Prop}
    (hfault : LazyFaultPreserves I) (id : KId .anon) (s : TcState .anon) :
    TcM.WF I s (TcM.getConst id)
      (fun c after => after.env.get? id = some c) := by
  unfold TcM.getConst
  apply TcM.WF.bind (TcM.tryGetConst_loaded_wf hfault id s)
  intro found after hfound
  cases found with
  | none => exact TcM.WF.throw fun _ => trivial
  | some c => exact TcM.WF.pure fun _ => hfound c rfl

end TcM

/-- Typed declaration-type evidence missing from the current raw trusted
catalog interface.  K2 closure must construct this for every trusted
constant that a supported run can infer. -/
def TrustedConstTypes (trProj : RawProjRel) (world : VerifyWorld) : Prop :=
  ∀ {id : KId .anon} {c : KConst .anon},
    world.trusted id → world.catalog id = some c →
    ∃ name ci,
      TrustedConstRel trProj world id c name ci ∧
      TrKExprS world.venv ci.uvars world.nameOf trProj [] c.ty ci.type

/-- Finite universe-walker census and its two level-resource obligations for
every supported constant syntax that can reach the uncached dispatcher. -/
def ConstInferCensus (world : VerifyWorld) (support : RunSupport)
    (requests : List WalkerRequest) : Prop :=
  ∀ {id : KId .anon} {us : Array (KUniv .anon)}
      {info : ExprInfo .anon} {c : KConst .anon},
    support (.const id us info) → world.catalog id = some c →
    WalkerRequest.instUniv c.ty us ∈ requests ∧
      DeltaInstantiationResources us c.ty

namespace TrustedConstRel

/-- Instantiate the structurally translated type of one trusted constant in
the caller's universe and mixed context.  The empty-array fast path is
handled separately because production deliberately skips the walker there. -/
theorem instantiatedType
    {trProj : RawProjRel} {world : VerifyWorld}
    {id : KId .anon} {c : KConst .anon} {name : Lean.Name}
    {ci : Lean4Lean.VConstant}
    (h : TrustedConstRel trProj world id c name ci)
    (htype : TrKExprS world.venv ci.uvars world.nameOf trProj []
      c.ty ci.type)
    {uvars : Nat} (theory : WhnfTheory trProj world uvars)
    {us : Array (KUniv .anon)} {result : KExpr .anon}
    (hus : ∀ level ∈ us, (KUniv.toVLevel level).WF uvars)
    (harity : us.size = ci.uvars)
    (hspec : KExpr.instantiateUnivParamsSpec c.ty us = .ok result)
    (resources : DeltaInstantiationResources us c.ty)
    {Delta : KVLCtx} (hDelta : KVLCtx.WF world.venv uvars Delta) :
    TrKExpr world.venv uvars world.nameOf trProj Delta result
      (ci.type.instL (us.toList.map KUniv.toVLevel)) := by
  by_cases hempty : us.isEmpty
  · have husEmpty : us = #[] := Array.empty_of_isEmpty hempty
    subst us
    have hresult : result = c.ty := by
      simpa [KExpr.instantiateUnivParamsSpec] using hspec.symm
    subst result
    have hzero : ci.uvars = 0 := by
      simpa using harity.symm
    have htype0 :
        TrKExprS world.venv 0 world.nameOf trProj [] c.ty ci.type := by
      simpa only [hzero] using htype
    have htypeU :
        TrKExprS world.venv uvars world.nameOf trProj [] c.ty ci.type :=
      htype0.monoU (Nat.zero_le uvars) (by trivial)
    have htypeDelta :
        TrKExprS world.venv uvars world.nameOf trProj Delta c.ty ci.type := by
      simpa only [KVLCtx.appendOuter] using
        htypeU.weakRight world.venvWF.ordered theory.literalWF
          theory.projections (by trivial) Delta
    obtain ⟨sort, hciType⟩ := h.wf
    have hciLevels : ci.type.LevelWF 0 := by
      have hlevels := hciType.levelWF (by trivial)
      simpa only [hzero] using hlevels.1
    have hinst : ci.type.instL [] = ci.type := by
      simpa [Lean4Lean.VLevel.params] using hciLevels.instL_id
    simpa [hinst] using
      htypeDelta.trKExpr world.venvWF.ordered theory.literalWF
        theory.projections.wf hDelta
  · have hspec' : KExpr.instUnivSpec c.ty us = .ok result := by
      simpa [KExpr.instantiateUnivParamsSpec, hempty] using hspec
    have hresult :=
      TrKExprS.instL world.venvWF theory.literalWF theory.projections
        hus harity.symm htype (by trivial) hspec'
          resources.addrFaithful resources.levelSize
    simpa only [KVLCtx.instL, KVLCtx.appendOuter] using
      hresult.weakRight world.venvWF.ordered theory.literalWF
        theory.projections (by trivial) Delta

end TrustedConstRel

namespace RecM

/-- The complete non-recursive constant branch: trusted lazy lookup, exact
arity check, request-certified universe instantiation, and Theory typing of
the source constant by the instantiated declaration type. -/
theorem inferUncached_const_wf
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {s : TcState .anon}
    {inferRec : KExpr .anon → RecM .anon (KExpr .anon)}
    {inferOnly : Bool} {id : KId .anon}
    {us : Array (KUniv .anon)} {info : ExprInfo .anon}
    {sourceV : Lean4Lean.VExpr}
    (theory : WhnfTheory trProj world uvars)
    (hfault : TcM.LazyFaultPreserves
      (WhnfStateInv layer semantics trProj world support uvars Delta))
    (hreferences : RecM.TrustedReferences world support)
    (htypes : TrustedConstTypes trProj world)
    (hcensus : ConstInferCensus world support requests)
    (hsourceSupport : support (.const id us info))
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta
      (.const id us info) sourceV) :
    RecM.WF layer semantics trProj world support uvars Delta s
      (inferUncached inferRec inferOnly (.const id us info))
      (fun ty _ => support ty ∧
        InferPost trProj world uvars Delta sourceV ty) := by
  cases hsource with
  | const hname hlookup hus harity =>
      rename_i sourceName sourceCi
      unfold inferUncached
      apply RecM.WF.bind
        (RecM.WF.withInv <| RecM.WF.liftTcM <|
          TcM.getConst_loaded_wf hfault id s)
      intro c after hget
      rcases hget with ⟨hI, hloaded⟩
      have hcatalog : world.catalog id = some c :=
        hI.1.core.loaded hloaded
      have htrusted : world.trusted id := by
        apply hreferences hsourceSupport
        rfl
      obtain ⟨resolvedName, ci, hrel, htype⟩ :=
        htypes htrusted hcatalog
      have hnameEq := Option.some.inj (hrel.nameEq.symm.trans hname)
      cases hnameEq
      have hciEq := Option.some.inj (hrel.lookup.symm.trans hlookup)
      cases hciEq
      have hcheck : c.lvls.toNat = us.size := by
        exact hrel.uvars.trans harity.symm
      have hcheckNe : (c.lvls.toNat != us.size) = false := by
        simp [hcheck]
      simp only [hcheckNe, Bool.false_eq_true, if_false, pure_bind]
      obtain ⟨hmem, resources⟩ := hcensus hsourceSupport hcatalog
      apply RecM.WF.mono
        (RecM.WF.withInv <| RecM.WF.liftTcM <|
          TcM.instantiateUnivParams_whnf_wf hrun.collisionFree
            (hrun.coverage.instUniv hmem))
      · intro result final hresult
        rcases hresult with ⟨hIfinal, hspec, hresultSupport⟩
        refine ⟨hresultSupport,
          sourceCi.type.instL (us.toList.map KUniv.toVLevel), ?_, ?_⟩
        · exact hrel.instantiatedType htype theory hus harity hspec
            resources hIfinal.2.1.wf
        · exact Lean4Lean.VEnv.HasType.const hlookup
            (by
              intro level hlevel
              obtain ⟨source, hsourceLevel, rfl⟩ := List.mem_map.1 hlevel
              exact hus source (by simpa using hsourceLevel))
            (by simpa using harity)
      · intro _ _ _
        trivial

end RecM

end Ix.Tc
