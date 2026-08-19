import Ix.Tc.Verify.Whnf.NoDelta.ProjectionDefinition

/-!
# Quotient no-delta field

The quotient helper normalizes the major through the predecessor WHNF table,
recognizes `Quot.mk`, interns the first reduced application, and rebuilds the
trailing suffix.  This slice proves that complete operational path, including
callback errors and every generated intern, from finite input and request
coverage.
-/

namespace Ix.Tc

/-- Finite generated-node plan for one selected quotient reduction.

The plan is indexed by both production spine decompositions and the exact
selected function/major indices.  Consequently it covers the initial
`f representative` application and every application after the quotient
major, without requiring global closure of the finite run support. -/
structure QuotientReductionRequestCensus
    (requests : List WalkerRequest) (support : RunSupport) : Prop where
  reduce : ∀ {source head majorWhnf mkHead : KExpr .anon}
      {args mkArgs : Array (KExpr .anon)} {prims : Primitives .anon}
      {fIdx majorIdx : Nat} {mkId : KId .anon}
      {mkUs : Array (KUniv .anon)} {mkInfo : ExprInfo .anon},
    support source →
    source.collectSpine = (head, args) →
    majorWhnf.collectSpine = (mkHead, mkArgs) →
    mkHead = .const mkId mkUs mkInfo →
    (mkId.addr != prims.quotCtor.addr) = false →
    (mkArgs.size != 3) = false →
    let base := KExpr.mkApp args[fIdx]! mkArgs[2]!
    support base ∧
      ∃ final, RecM.FinishAppRequests requests
        (args.extract (majorIdx + 1) args.size).toList base final

/-- Semantic authority for an observed successful quotient reduction.
Operational state and support are excluded: Quotient proves them directly.  The
eventual Theory refinement splits the `Quot.lift` registered equation from
the proof-irrelevant `Quot.ind` result. -/
structure QuotientReductionReflection (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld)
    (support : RunSupport) : Prop where
  success : ∀ {uvars : Nat} {Delta : KVLCtx}
      {methods : Methods .anon} {source result : KExpr .anon}
      {sourceV : Lean4Lean.VExpr} {s sf : TcState .anon},
    Methods.WFAt .noAccel semantics trProj world support uvars methods →
    support source →
    TrKExprS world.venv uvars world.nameOf trProj Delta source sourceV →
    WhnfStateInv .noAccel semantics trProj world support uvars Delta s →
    (RecM.tryQuotReduce source).run methods s =
      .ok (some result) sf →
    WhnfMeaning trProj world uvars Delta source result

namespace RecM

set_option maxHeartbeats 800000

/-- The common body reached after selecting the `Quot.lift` or `Quot.ind`
function and major indices. -/
def tryQuotReduceSelected (prims : Primitives m)
    (args : Array (KExpr m)) (fIdx majorIdx : Nat) :
    RecM m (Option (KExpr m)) := do
  let majorWhnf ← whnfRec args[majorIdx]!
  let (mkHead, mkArgs) := majorWhnf.collectSpine
  let .const mkId _ _ := mkHead | return none
  if mkId.addr != prims.quotCtor.addr then
    return none
  if mkArgs.size != 3 then
    return none
  let mut result ← TcM.intern (KExpr.mkApp args[fIdx]! mkArgs[2]!)
  for arg in args.extract (majorIdx + 1) args.size do
    result ← TcM.intern (KExpr.mkApp result arg)
  return some result

/-- State and generated-result closure of the selected common quotient body.
The major callback is justified from its actual spine position; no arbitrary
child-support assumption is inferred from support for the parent. -/
theorem tryQuotReduceSelected_inv_wf
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    (census : QuotientReductionRequestCensus requests support)
    (inputs : NoDeltaInputSupport support)
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {uvars : Nat} {Delta : KVLCtx}
    {source head : KExpr .anon} {sourceV : Lean4Lean.VExpr}
    {args : Array (KExpr .anon)} {prims : Primitives .anon}
    {fIdx majorIdx : Nat} {s : TcState .anon}
    (hsourceSupport : support source)
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta source
      sourceV)
    (hspine : source.collectSpine = (head, args))
    (hfIdx : fIdx < args.size) (hmajorIdx : majorIdx < args.size) :
    RecM.WF .noAccel semantics trProj world support uvars Delta s
      (tryQuotReduceSelected prims args fIdx majorIdx)
      (fun result _ => match result with
        | none => True
        | some reduced => support reduced) := by
  have hmajorSupport : support args[majorIdx]! := by
    have hsupported :=
      (inputs.spine hsourceSupport hspine).2 majorIdx hmajorIdx
    simpa only [getElem!_pos args majorIdx hmajorIdx] using hsupported
  have _hfunctionSupport : support args[fIdx]! := by
    have hsupported := (inputs.spine hsourceSupport hspine).2 fIdx hfIdx
    simpa only [getElem!_pos args fIdx hfIdx] using hsupported
  have hmajorGet :
      args[majorIdx]? = some args[majorIdx]! := by
    rw [getElem?_pos args majorIdx hmajorIdx,
      getElem!_pos args majorIdx hmajorIdx]
  have hspineTr := trAppSpine_of_collectSpine hsource hspine
  obtain ⟨majorV, majorType, hmajorType, hmajorTr⟩ :=
    hspineTr.argument (arg := args[majorIdx]!) <|
      Array.mem_toList_iff.mpr (Array.mem_of_getElem? hmajorGet)
  unfold tryQuotReduceSelected
  apply RecM.WF.bind (whnfRec_wf hmajorSupport hmajorTr)
  intro majorWhnf afterWhnf hmajorPost
  generalize hmkSpine : majorWhnf.collectSpine = mkSpine
  rcases mkSpine with ⟨mkHead, mkArgs⟩
  cases mkHead with
  | const mkId mkUs mkInfo =>
      cases hctor : (mkId.addr != prims.quotCtor.addr) with
      | true =>
          simp only [hctor, if_true]
          exact RecM.WF.pure fun _ => trivial
      | false =>
          simp only [hctor, Bool.false_eq_true, if_false]
          cases hsize : (mkArgs.size != 3) with
          | true =>
              simp only [if_true]
              exact RecM.WF.pure fun _ => trivial
          | false =>
              simp only [Bool.false_eq_true, if_false, pure_bind]
              let base : KExpr .anon :=
                KExpr.mkApp args[fIdx]! mkArgs[2]!
              obtain ⟨hbase, final, plan⟩ :=
                census.reduce (prims := prims) (fIdx := fIdx)
                  (majorIdx := majorIdx) hsourceSupport hspine hmkSpine rfl
                  hctor hsize
              apply RecM.WF.bind <| RecM.WF.liftTcM <|
                TcM.intern_whnf_wf hrun.collisionFree hbase
              intro actualBase afterBase hactualBase
              have hactualBaseEq : actualBase = base := hactualBase.1
              subst actualBase
              rw [projectionDefinitionFinish_eq]
              apply RecM.WF.bind (plan.finishAppResult_wf hrun hbase)
              intro actualFinal afterFinal hactualFinal
              rcases hactualFinal with
                ⟨hactualFinalEq, hfinalSupport⟩
              subst actualFinal
              exact RecM.WF.pure fun _ => hfinalSupport
  | var | fvar | sort | app | lam | all | letE | prj | nat | str =>
      simp only
      exact RecM.WF.pure fun _ => trivial

/-- State and generated-result closure of the complete production quotient
helper, including both arity policies and every miss. -/
theorem tryQuotReduce_inv_wf
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    (census : QuotientReductionRequestCensus requests support)
    (inputs : NoDeltaInputSupport support)
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {uvars : Nat} {Delta : KVLCtx}
    {source : KExpr .anon} {sourceV : Lean4Lean.VExpr}
    {s : TcState .anon}
    (hsourceSupport : support source)
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta source
      sourceV) :
    RecM.WF .noAccel semantics trProj world support uvars Delta s
      (tryQuotReduce source)
      (fun result _ => match result with
        | none => True
        | some reduced => support reduced) := by
  unfold tryQuotReduce
  generalize hspine : source.collectSpine = spine
  rcases spine with ⟨head, args⟩
  cases head with
  | const id us headInfo =>
      simp only [pure_bind]
      apply RecM.WF.bind (prims_wf (s := s))
      intro prims afterRead hread
      rcases hread with ⟨hprims, hafterRead⟩
      subst afterRead
      cases hlift : (id.addr == prims.quotLift.addr) with
      | true =>
          simp only [if_true]
          by_cases hsize : args.size < 6
          · simp only [hsize, if_pos]
            exact RecM.WF.pure fun _ => trivial
          · simp only [hsize, if_false]
            have hfIdx : 3 < args.size := by omega
            have hmajorIdx : 5 < args.size := by omega
            exact
              tryQuotReduceSelected_inv_wf hrun census inputs
                (semantics := semantics) (trProj := trProj) (world := world)
                hsourceSupport hsource hspine hfIdx hmajorIdx
      | false =>
          simp only [Bool.false_eq_true, if_false]
          cases hind : (id.addr == prims.quotInd.addr) with
          | false =>
              simp only [Bool.false_eq_true, if_false]
              exact RecM.WF.pure fun _ => trivial
          | true =>
              simp only [if_true]
              by_cases hsize : args.size < 5
              · simp only [hsize, if_pos]
                exact RecM.WF.pure fun _ => trivial
              · simp only [hsize, if_false]
                have hfIdx : 3 < args.size := by omega
                have hmajorIdx : 4 < args.size := by omega
                exact
                  tryQuotReduceSelected_inv_wf hrun census inputs
                    (semantics := semantics) (trProj := trProj)
                    (world := world) hsourceSupport hsource hspine
                    hfIdx hmajorIdx
  | var | fvar | sort | app | lam | all | letE | prj | nat | str =>
      simp only
      exact RecM.WF.pure fun _ => trivial

/-- Complete quotient optional-reducer field. -/
theorem tryQuotReduce_optional_wf_of_contexts
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    (census : QuotientReductionRequestCensus requests support)
    (inputs : NoDeltaInputSupport support)
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld}
    (reflection : QuotientReductionReflection semantics trProj world
      support) :
    OptionalReduction.WF .noAccel semantics trProj world support
      tryQuotReduce := by
  intro uvars Delta source sourceV s hsourceSupport hsource
  have hstate :=
    tryQuotReduce_inv_wf hrun census inputs
      (semantics := semantics) (trProj := trProj) (world := world)
      (s := s) hsourceSupport hsource
  intro methods hmethods hI
  have hpost := hstate methods hmethods hI
  match hrunQuot : (tryQuotReduce source).run methods s with
  | .error err sf =>
      rw [hrunQuot] at hpost
      exact ⟨hpost.1, trivial⟩
  | .ok none sf =>
      rw [hrunQuot] at hpost
      exact ⟨hpost.1, trivial⟩
  | .ok (some result) sf =>
      rw [hrunQuot] at hpost
      exact ⟨hpost.1, hpost.2,
        reflection.success hmethods hsourceSupport hsource hI hrunQuot⟩

end RecM
end Ix.Tc
