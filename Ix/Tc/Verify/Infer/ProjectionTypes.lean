import Ix.Tc.Verify.Infer.ProjectionClassification

/-!
# Projection inference

The syntax dispatcher first infers the projected value and then delegates to
`inferProj`.  Unlike ordinary syntax cases, soundness of that helper is not a
consequence of `TrProjOK`: the latter only states closure, well-formedness,
uniqueness, and context transport for the abstract projection relation.  It
does not connect the production inductive/constructor lookup algorithm to the
Theory type of a selected projection.

This module therefore isolates that remaining semantic boundary explicitly.
`ProjectionInference.WF` is the dispatcher-facing contract for `inferProj`;
`ProjectionInference.Context.wf` below constructs it from the concrete helper
proof and the narrow declaration/projection oracle.  The dispatcher theorem
proves all surrounding behavior—child support, the recursive value-inference
edge, error propagation, and composition with the helper—without treating a
successful helper execution as semantic evidence by itself.
-/

namespace Ix.Tc

/-- Finite child coverage for a supported projection source.  Run support is
finite and intentionally not closed under arbitrary syntax descent. -/
def ProjectionValueSupport (support : RunSupport) : Prop :=
  ∀ {structId : KId .anon} {field : UInt64} {val : KExpr .anon}
      {info : ExprInfo .anon},
    support (.prj structId field val info) → support val

/-- Finite support for the head and arguments returned by the production
application-spine collector. -/
def ProjectionSpineSupport (support : RunSupport) : Prop :=
  ∀ {source head : KExpr .anon} {args : Array (KExpr .anon)},
    support source → source.collectSpine = (head, args) →
      support head ∧ ∀ arg, arg ∈ args.toList → support arg

/-- Universe-walker requests selected by a supported projection inference.
The first request instantiates the inductive declaration for its Prop check;
the second instantiates the sole constructor returned by the exact catalog
lookup. -/
def ProjectionInferenceCensus (world : VerifyWorld) (support : RunSupport)
    (requests : List WalkerRequest) : Prop :=
  ∀ {source : KExpr .anon} {id : KId .anon}
      {levels : Array (KUniv .anon)} {info : ExprInfo .anon}
      {args : Array (KExpr .anon)} {c : KConst .anon},
    support source →
    source.collectSpine = (.const id levels info, args) →
    world.catalog id = some c →
    match c with
    | .indc (ty := indTy) (ctors := ctors) .. =>
        WalkerRequest.instUniv indTy levels ∈ requests ∧
          ∀ {ctorId : KId .anon} {ctor : KConst .anon},
            ctors[0]? = some ctorId →
            world.catalog ctorId = some ctor →
            WalkerRequest.instUniv ctor.ty levels ∈ requests
    | _ => True

namespace ProjectionInference

/-- Semantic plan for the exact constructor type selected by production.
The universe walker chooses `instantiated`; the parameter loop chooses every
substituted intermediate; this plan can only interpret those concrete
results, not replace them. -/
structure ConstructorTypingPlan
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (uvars : Nat) (Delta : KVLCtx) (structId : KId .anon)
    (field : UInt64) (val : KExpr .anon)
    (projectedV : Lean4Lean.VExpr) (args : Array (KExpr .anon))
    (levels : Array (KUniv .anon)) (numParams : Nat)
    (ctorTy : KExpr .anon) : Prop where
  instantiated : ∀ {instantiated : KExpr .anon},
    KExpr.instantiateUnivParamsSpec ctorTy levels = .ok instantiated →
    ∃ instantiatedV,
      TrKExpr world.venv uvars world.nameOf trProj Delta instantiated
          instantiatedV ∧
        RecM.ProjectionParameterPlan trProj world support uvars Delta args
          (List.range'
            ([0:numParams] : _root_.Std.Legacy.Range).start
            ([0:numParams] : _root_.Std.Legacy.Range).size
            ([0:numParams] : _root_.Std.Legacy.Range).step)
          instantiatedV ∧
        ∀ {parameterized : KExpr .anon}
            {parameterizedV : Lean4Lean.VExpr},
          support parameterized →
          TrKExpr world.venv uvars world.nameOf trProj Delta parameterized
            parameterizedV →
          RecM.ProjectionFieldPlan trProj world support uvars Delta structId field
            val projectedV
            (List.range'
              ([0:field.toNat + 1] : _root_.Std.Legacy.Range).start
              ([0:field.toNat + 1] : _root_.Std.Legacy.Range).size
              ([0:field.toNat + 1] : _root_.Std.Legacy.Range).step)
            parameterizedV

/-- The irreducible semantic boundary between the concrete catalog layout
and the abstract Theory projection relation.  Every premise is evidence
already established by the production path: the inferred value type's exact
spine, address agreement, both immutable catalog entries, sole-constructor
selection, and the source projection witness. -/
def DeclarationOracle (trProj : RawProjRel) (world : VerifyWorld)
    (support : RunSupport) (uvars : Nat) : Prop :=
  ∀ {Delta : KVLCtx} {structId headId : KId .anon} {field : UInt64}
      {val : KExpr .anon} {valV projectedV valTyV reducedTyV : Lean4Lean.VExpr}
      {structName : Lean.Name} {levels : Array (KUniv .anon)}
      {headInfo : ExprInfo .anon} {args : Array (KExpr .anon)}
      {indName : Mode.anon.F Name}
      {indLevelParams : Mode.anon.F (Array Name)}
      {indLvls indParams indIndices : UInt64} {indUnsafe : Bool}
      {indBlock : KId .anon} {indMemberIdx : UInt64}
      {indTy : KExpr .anon} {ctors : Array (KId .anon)}
      {indLeanAll : Mode.anon.F (Array (KId .anon))}
      {ctorId : KId .anon} {ctor : KConst .anon},
    world.nameOf structId.addr = some structName →
    TrKExprS world.venv uvars world.nameOf trProj Delta val valV →
    trProj uvars Delta.toCtx structName field.toNat valV projectedV →
    world.venv.HasType uvars Delta.toCtx valV valTyV →
    world.venv.IsDefEqU uvars Delta.toCtx valTyV reducedTyV →
    RecM.TrAppSpine world.venv uvars world.nameOf trProj Delta
      (.const headId levels headInfo) args.toList reducedTyV →
    headId.addr = structId.addr →
    world.catalog headId = some
      (.indc indName indLevelParams indLvls indParams indIndices indUnsafe
        indBlock indMemberIdx indTy ctors indLeanAll) →
    ctors.size = 1 →
    ctors[0]? = some ctorId →
    world.catalog ctorId = some ctor →
    ConstructorTypingPlan trProj world support uvars Delta structId field val
      projectedV args levels indParams.toNat ctor.ty

/-- Dispatcher-facing operational and semantic contract for the production
`inferProj` helper.  The source projection evidence supplies both the resolved
structure name and the abstract Theory projection witness.  A successful
helper result must remain in finite support and type that projected Theory
expression; every error must preserve the full checker invariant.

`Context.wf` constructs this contract below.  Its one semantic premise is the
narrow `DeclarationOracle`, rather than an assertion that `TrProjOK` alone is
strong enough to justify projection inference. -/
def WF (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (uvars : Nat) : Prop :=
  ∀ {Delta : KVLCtx} {s : TcState .anon}
      {structId : KId .anon} {field : UInt64} {val valTy : KExpr .anon}
      {valV projectedV : Lean4Lean.VExpr} {structName : Lean.Name},
    world.nameOf structId.addr = some structName →
    TrKExprS world.venv uvars world.nameOf trProj Delta val valV →
    trProj uvars Delta.toCtx structName field.toNat valV projectedV →
    support valTy →
    InferPost trProj world uvars Delta valV valTy →
    RecM.WF .noAccel semantics trProj world support uvars Delta s
      (RecM.inferProj structId field val valTy)
      (fun result _ => support result ∧
        InferPost trProj world uvars Delta projectedV result)

/-- Complete concrete resources for projection inference at one universe
count.  Only `oracle` is semantic; the remaining fields are finite execution,
support, state, and already-verified helper contracts. -/
structure Context
    {alpha : Type} (initial : TcState .anon) (program : TcM .anon alpha)
    (requests : List WalkerRequest) (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (uvars : Nat) : Type where
  run : RunAssumptions initial program requests support
  theory : WhnfTheory trProj world uvars
  whnf : DirectWhnf.WFAt semantics trProj world support uvars
  components : ForallComponentSupport support
  sorts : SortComponentResources support
  substitution : SubstitutionResources support
  fault : ∀ Delta : KVLCtx,
    TcM.LazyFaultPreserves
      (WhnfStateInv .noAccel semantics trProj world support uvars Delta)
  classifier : ∀ Delta : KVLCtx,
    RecM.ProjectionWhnfPreservesAt .noAccel semantics trProj world support
      uvars Delta
  spines : ProjectionSpineSupport support
  census : ProjectionInferenceCensus world support requests
  oracle : DeclarationOracle trProj world support uvars

end ProjectionInference

namespace RecM

/-- Concrete production proof of `inferProj`, relative only to the finite
run census, the loose-binder state callback, and the declaration/projection
semantic oracle isolated above. -/
theorem inferProj_wf
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {uvars : Nat} {Delta : KVLCtx}
    {s : TcState .anon} {structId : KId .anon} {field : UInt64}
    {val valTy : KExpr .anon} {valV projectedV : Lean4Lean.VExpr}
    {structName : Lean.Name}
    (theory : WhnfTheory trProj world uvars)
    (hwhnf : DirectWhnf.WFAt semantics trProj world support uvars)
    (hcomponents : ForallComponentSupport support)
    (hsorts : SortComponentResources support)
    (hsubst : SubstitutionResources support)
    (hfault : TcM.LazyFaultPreserves
      (WhnfStateInv .noAccel semantics trProj world support uvars Delta))
    (hclassifier : ProjectionWhnfPreservesAt .noAccel semantics trProj world
      support uvars Delta)
    (hspines : ProjectionSpineSupport support)
    (hcensus : ProjectionInferenceCensus world support requests)
    (horacle : ProjectionInference.DeclarationOracle trProj world support
      uvars)
    (hname : world.nameOf structId.addr = some structName)
    (hval : TrKExprS world.venv uvars world.nameOf trProj Delta val valV)
    (hproj : trProj uvars Delta.toCtx structName field.toNat valV projectedV)
    (hvalTySupport : support valTy)
    (hvalTy : InferPost trProj world uvars Delta valV valTy) :
    RecM.WF .noAccel semantics trProj world support uvars Delta s
      (inferProj structId field val valTy)
      (fun result _ => support result ∧
        InferPost trProj world uvars Delta projectedV result) := by
  rcases hvalTy with ⟨valTyV, hvalTyTr, hvalType⟩
  obtain ⟨valTyCoreV, hvalTyCore, hvalTyCoreEq⟩ := hvalTyTr
  unfold inferProj
  apply RecM.WF.bind
    (RecM.WF.withInv <| hwhnf hvalTySupport hvalTyCore)
  intro reducedTy afterWhnf hreduced
  rcases hreduced with
    ⟨hI, hreducedSupport, reducedTyV, hreducedTr, hreduceEq⟩
  rcases hspine : reducedTy.collectSpine with ⟨head, args⟩
  have hvalTyReduced : world.venv.IsDefEqU uvars Delta.toCtx valTyV
      reducedTyV :=
    hvalTyCoreEq.symm.trans world.venvWF hI.2.1.wf hreduceEq
  have hspineSupport := hspines hreducedSupport hspine
  have hspineTr := RecM.trAppSpine_of_collectSpine hreducedTr hspine
  cases head with
  | const headId levels headInfo =>
      by_cases haddr : headId.addr = structId.addr
      · have haddrTest : (headId.addr != structId.addr) = false := by
          simp [haddr]
        simp only [haddrTest, Bool.false_eq_true, if_false]
        apply RecM.WF.bind
          (RecM.WF.withInv <| RecM.WF.liftTcM <|
            TcM.tryGetConst_loaded_wf hfault headId afterWhnf)
        intro foundInd afterInd hfoundInd
        rcases hfoundInd with ⟨hIInd, hloadedInd⟩
        cases foundInd with
        | none => exact RecM.WF.throw fun _ => trivial
        | some indEntry =>
            cases indEntry <;> simp only
            case pos.some.indc indName indLevelParams indLvls indParams indIndices
                indUnsafe indBlock indMemberIdx indTy ctors indLeanAll =>
              have hcatalogInd : world.catalog headId = some
                  (.indc indName indLevelParams indLvls indParams indIndices
                    indUnsafe indBlock indMemberIdx indTy ctors indLeanAll) :=
                hIInd.1.core.loaded (hloadedInd _ rfl)
              obtain ⟨hindRequest, hctorRequest⟩ :=
                hcensus hreducedSupport hspine hcatalogInd
              simp only [pure_bind]
              by_cases hctorCount : ctors.size = 1
              · have hcountTest : (ctors.size != 1) = false := by
                  simp [hctorCount]
                simp only [hcountTest, Bool.false_eq_true, if_false]
                have hclassRequest :
                    ProjectionInductiveInstantiationRequest world requests
                      headId levels := by
                  intro c hcatalog
                  have hc : c =
                      .indc indName indLevelParams indLvls indParams
                        indIndices indUnsafe indBlock indMemberIdx indTy ctors
                        indLeanAll :=
                    Option.some.inj (hcatalog.symm.trans hcatalogInd)
                  subst c
                  exact hindRequest
                apply RecM.WF.bind
                  (inductiveAppIsProp_state_wf hrun hfault hclassifier
                    hclassRequest)
                intro isPropStruct afterClass _
                generalize hctorId : ctors[0]! = ctorId
                have hctorGet : ctors[0]? = some ctorId := by
                  grind
                apply RecM.WF.bind
                  (RecM.WF.withInv <| RecM.WF.liftTcM <|
                    TcM.tryGetConst_loaded_wf hfault ctorId afterClass)
                intro foundCtor afterCtor hfoundCtor
                rcases hfoundCtor with ⟨hICtor, hloadedCtor⟩
                cases foundCtor with
                | none => exact RecM.WF.throw fun _ => trivial
                | some ctor =>
                    have hcatalogCtor : world.catalog ctorId = some ctor :=
                      hICtor.1.core.loaded (hloadedCtor _ rfl)
                    have hctorMem :=
                      hctorRequest hctorGet hcatalogCtor
                    apply RecM.WF.bind
                      (RecM.WF.liftTcM <|
                        TcM.instantiateUnivParams_whnf_wf
                          hrun.collisionFree
                          (hrun.coverage.instUniv hctorMem))
                    intro instantiated afterInst hinstantiated
                    rcases hinstantiated with
                      ⟨hinstantiatedSpec, hinstantiatedSupport⟩
                    have hctorPlan := horacle hname hval hproj hvalType
                      hvalTyReduced hspineTr haddr hcatalogInd hctorCount
                      hctorGet hcatalogCtor
                    obtain ⟨instantiatedV, hinstantiatedTr, hparams,
                        hfields⟩ :=
                      hctorPlan.instantiated hinstantiatedSpec
                    apply RecM.WF.bind
                      (instantiateProjParams_wf theory hwhnf hcomponents
                        hsubst hrun.collisionFree hinstantiatedSupport
                        hinstantiatedTr hparams)
                    intro parameterized afterParams hparameterized
                    rcases hparameterized with
                      ⟨hparameterizedSupport, parameterizedV,
                        hparameterizedTr⟩
                    exact inferProjFields_wf theory hwhnf hcomponents hsorts
                      hsubst hrun.collisionFree hparameterizedSupport
                      hparameterizedTr
                      (hfields hparameterizedSupport hparameterizedTr)
              · have hcountTest : (ctors.size != 1) = true := by
                  simp [hctorCount]
                simp only [hcountTest, if_true]
                exact RecM.WF.throw fun _ => trivial
            all_goals exact RecM.WF.throw fun _ => trivial
      · have haddrTest : (headId.addr != structId.addr) = true := by
          simp [haddr]
        simp only [haddrTest, if_true]
        exact RecM.WF.throw fun _ => trivial
  | var | fvar | sort | app | lam | all | letE | prj | nat | str =>
      exact RecM.WF.throw fun _ => trivial

end RecM

namespace ProjectionInference

/-- The concrete context constructs the former whole-helper obligation. -/
theorem Context.wf
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat}
    (context : Context initial program requests semantics trProj world support
      uvars) :
    WF semantics trProj world support uvars := by
  intro Delta s structId field val valTy valV projectedV structName
    hname hval hproj hvalTySupport hvalTy
  exact RecM.inferProj_wf context.run context.theory context.whnf
    context.components context.sorts context.substitution
    (context.fault Delta) (context.classifier Delta) context.spines
    context.census context.oracle hname hval hproj hvalTySupport hvalTy

end ProjectionInference

namespace RecM

/-- Complete projection case of the uncached inference dispatcher, relative
to the dispatcher-facing `inferProj` contract constructed above. -/
theorem inferUncached_prj_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {Delta : KVLCtx} {s : TcState .anon} {inferOnly : Bool}
    {structId : KId .anon} {field : UInt64} {val : KExpr .anon}
    {info : ExprInfo .anon} {sourceV : Lean4Lean.VExpr}
    (hinputs : ProjectionValueSupport support)
    (hprojection : ProjectionInference.WF semantics trProj world support
      uvars)
    (hsourceSupport : support (.prj structId field val info))
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta
      (.prj structId field val info) sourceV) :
    RecM.WF .noAccel semantics trProj world support uvars Delta s
      (inferUncached inferCall inferOnly (.prj structId field val info))
      (fun result _ => support result ∧
        InferPost trProj world uvars Delta sourceV result) := by
  cases hsource with
  | prj hname hvalTr hproj =>
      unfold inferUncached
      apply RecM.WF.bind
        (RecM.WF.withInv <|
          RecM.inferCall_wf (hinputs hsourceSupport) hvalTr)
      intro valTy afterValue hvaluePost
      rcases hvaluePost with
        ⟨_, hvalTySupport, valTyV, hvalTyTr, hvalType⟩
      exact hprojection hname hvalTr hproj hvalTySupport
        ⟨valTyV, hvalTyTr, hvalType⟩

end RecM

end Ix.Tc
