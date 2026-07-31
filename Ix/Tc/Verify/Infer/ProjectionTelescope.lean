import Init.Data.Range.Lemmas
import Ix.Tc.Verify.Infer.LetTypes
import Ix.Tc.Verify.Infer.FunctionTypes

/-!
# Projection telescope exposure

Projection inference repeatedly peels constructor and inductive telescopes.
Production uses a syntactic `all` fast path and otherwise invokes the ordinary
WHNF reducer.  This module proves that both paths expose the same supported
Theory forall view; the diagnostic string affects only the error payload.
-/

namespace Ix.Tc

/-- A concrete argument is admissible for every supported Π view that the
production peeler may expose from `inputV`.  The universal formulation avoids
choosing a particular structural translation before WHNF has run; translation
uniqueness makes all successful views definitionally coherent. -/
def ProjectionArgumentFits (trProj : RawProjRel) (world : VerifyWorld)
    (support : RunSupport) (uvars : Nat) (Delta : KVLCtx)
    (inputV : Lean4Lean.VExpr) (arg : KExpr .anon) : Prop :=
  ∀ {dom cod : KExpr .anon} {domV codV : Lean4Lean.VExpr},
    support dom → support cod →
    world.venv.IsType uvars Delta.toCtx domV →
    world.venv.IsType uvars (domV :: Delta.toCtx) codV →
    TrKExprS world.venv uvars world.nameOf trProj Delta dom domV →
    TrKExprS world.venv uvars world.nameOf trProj
      ((none, .vlam domV) :: Delta) cod codV →
    world.venv.IsDefEqU uvars Delta.toCtx inputV (.forallE domV codV) →
    ∃ argV,
      TrKExprS world.venv uvars world.nameOf trProj Delta arg argV ∧
        world.venv.HasType uvars Delta.toCtx argV domV

namespace RecM

/-- Both paths through `peelProjForall` return a supported concrete Π whose
structural components denote a forall definitionally equal to the input
type.  All helper errors preserve the complete no-acceleration invariant. -/
theorem peelProjForall_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {Delta : KVLCtx} {s : TcState .anon} {input : KExpr .anon}
    {inputV : Lean4Lean.VExpr} {err : String}
    (hwhnf : DirectWhnf.WFAt semantics trProj world support uvars)
    (hcomponents : ForallComponentSupport support)
    (hinputSupport : support input)
    (hinput : TrKExpr world.venv uvars world.nameOf trProj Delta input
      inputV) :
    RecM.WF .noAccel semantics trProj world support uvars Delta s
      (peelProjForall input err)
      (fun result _ => ForallView trProj world support uvars Delta inputV
        result.1 result.2) := by
  obtain ⟨inputCoreV, hinputCore, hinputEq⟩ := hinput
  cases input <;> simp only [peelProjForall]
  case all name bi dom cod info =>
    apply RecM.WF.pure
    intro _
    obtain ⟨hdomSupport, hcodSupport⟩ := hcomponents hinputSupport
    cases hinputCore with
    | all hdomType hcodType hdomTr hcodTr =>
        exact ⟨_, _, hdomSupport, hcodSupport, hdomType, hcodType,
          hdomTr, hcodTr, hinputEq.symm⟩
  all_goals
    simp only [pure_bind]
    apply RecM.WF.bind (hwhnf hinputSupport hinputCore)
    intro reduced after hred
    rcases hred with
      ⟨hreducedSupport, reducedV, hreducedTr, hcoreReduced⟩
    cases reduced <;> simp only
    case all name bi dom cod info =>
      apply RecM.WF.pure
      intro hI
      obtain ⟨hdomSupport, hcodSupport⟩ :=
        hcomponents hreducedSupport
      cases hreducedTr with
      | all hdomType hcodType hdomTr hcodTr =>
          exact ⟨_, _, hdomSupport, hcodSupport, hdomType, hcodType,
            hdomTr, hcodTr,
            hinputEq.symm.trans world.venvWF hI.2.1.wf.toCtx
              hcoreReduced⟩
    all_goals
      exact RecM.WF.throw fun _ => trivial

/-- Substitute one pre-certified argument into an already exposed Π body.
This is the semantic core shared by constructor parameters and preceding
fields; callers remain responsible for proving that the concrete argument is
the one production actually selected. -/
private theorem substProjForallBody_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {Delta : KVLCtx} {s : TcState .anon}
    {inputV : Lean4Lean.VExpr} {dom body arg : KExpr .anon}
    (theory : WhnfTheory trProj world uvars)
    (hsubst : SubstitutionResources support)
    (hcollision : support.CollisionFree)
    (hview : ForallView trProj world support uvars Delta inputV dom body)
    (hargSupport : support arg)
    (hfits : ProjectionArgumentFits trProj world support uvars Delta
      inputV arg) :
    RecM.WF .noAccel semantics trProj world support uvars Delta s
      (TcM.runIntern (subst body arg 0))
      (fun result _ => support result ∧
        ∃ resultV,
          TrKExpr world.venv uvars world.nameOf trProj Delta result
            resultV) := by
  rcases hview with
    ⟨domV, bodyV, hdomSupport, hbodySupport, hdomType, hbodyType,
      hdomTr, hbodyTr, hinputEq⟩
  obtain ⟨argV, hargTr, hargType⟩ :=
    hfits hdomSupport hbodySupport hdomType hbodyType hdomTr hbodyTr
      hinputEq
  have hbounds := hsubst.bounds (depth := 0) hbodySupport hargSupport
  have hresultTr : TrKExprS world.venv uvars world.nameOf trProj Delta
      (KExpr.substSpec body arg 0) (bodyV.inst argV) :=
    TrKExprS.instN_lbr world.venvWF.ordered theory.projections.weakN
      theory.projections.instN hbounds.2.1 hargTr hargType hbodyTr
      (.zero : KVLCtx.KInstN Delta argV domV 0 0
        ((none, .vlam domV) :: Delta) Delta)
      rfl hbounds.2.2.2.2
  apply RecM.WF.mono
    (RecM.WF.withInv <| RecM.WF.liftTcM <|
      hsubst.whnf_wf hcollision hbodySupport hargSupport)
  · intro result final hpost
    rcases hpost with ⟨hIfinal, rfl, hresultSupport, _⟩
    exact ⟨hresultSupport, bodyV.inst argV,
      hresultTr.trKExpr world.venvWF.ordered theory.literalWF
        theory.projections.wf hIfinal.2.1.wf⟩
  · intro _ _ _
    trivial

/-- One successful constructor-parameter step: expose a Π, validate the
pre-certified argument against that view, and execute production's dependent
substitution.  The returned concrete type remains supported and has a Theory
translation for the next telescope iteration. -/
private theorem instantiateProjParamBody_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {Delta : KVLCtx} {s : TcState .anon}
    {current arg : KExpr .anon} {currentV : Lean4Lean.VExpr}
    {err : String}
    (theory : WhnfTheory trProj world uvars)
    (hwhnf : DirectWhnf.WFAt semantics trProj world support uvars)
    (hcomponents : ForallComponentSupport support)
    (hsubst : SubstitutionResources support)
    (hcollision : support.CollisionFree)
    (hcurrentSupport : support current)
    (hargSupport : support arg)
    (hcurrent : TrKExpr world.venv uvars world.nameOf trProj Delta current
      currentV)
    (hfits : ProjectionArgumentFits trProj world support uvars Delta
      currentV arg) :
    RecM.WF .noAccel semantics trProj world support uvars Delta s
      (do
        let (_, body) ← peelProjForall current err
        TcM.runIntern (subst body arg 0))
      (fun result _ => support result ∧
        ∃ resultV,
          TrKExpr world.venv uvars world.nameOf trProj Delta result
            resultV) := by
  apply RecM.WF.bind
    (RecM.peelProjForall_wf hwhnf hcomponents hcurrentSupport hcurrent)
  intro exposed afterPeel hview
  rcases exposed with ⟨dom, body⟩
  exact substProjForallBody_wf theory hsubst hcollision hview hargSupport
    hfits

/-- The named production parameter step has exactly the semantic body above
and always yields the substituted telescope to the surrounding range loop. -/
theorem instantiateProjParamStep_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {Delta : KVLCtx} {s : TcState .anon}
    {args : Array (KExpr .anon)} {i : Nat} (hidx : i < args.size)
    {current : KExpr .anon} {currentV : Lean4Lean.VExpr}
    (theory : WhnfTheory trProj world uvars)
    (hwhnf : DirectWhnf.WFAt semantics trProj world support uvars)
    (hcomponents : ForallComponentSupport support)
    (hsubst : SubstitutionResources support)
    (hcollision : support.CollisionFree)
    (hcurrentSupport : support current)
    (hargSupport : support args[i])
    (hcurrent : TrKExpr world.venv uvars world.nameOf trProj Delta current
      currentV)
    (hfits : ProjectionArgumentFits trProj world support uvars Delta
      currentV args[i]) :
    RecM.WF .noAccel semantics trProj world support uvars Delta s
      (instantiateProjParamStep args i current)
      (fun action _ => match action with
        | .done result | .yield result =>
            support result ∧ ∃ resultV,
              TrKExpr world.venv uvars world.nameOf trProj Delta result
                resultV) := by
  have hstep :
      instantiateProjParamStep args i current =
        ((do
          let (_, body) ← peelProjForall current
            "projection: expected forall in ctor type"
          TcM.runIntern (subst body args[i] 0)) >>= fun result =>
            pure (.yield result)) := by
    funext methods state
    unfold instantiateProjParamStep
    simp [hidx, bind_pure_comp]
  rw [hstep]
  apply RecM.WF.bind
    (instantiateProjParamBody_wf theory hwhnf hcomponents hsubst hcollision
      hcurrentSupport hargSupport hcurrent hfits)
  intro result after hpost
  exact RecM.WF.pure fun _ => hpost

/-- Execution-indexed semantic input for a finite constructor-parameter
telescope.  Each entry certifies exactly the array access and Π application
performed by the corresponding production iteration.  The continuation is
parametric in the concrete substituted result, so this plan cannot choose or
replace any intermediate produced by `subst`. -/
def ProjectionParameterPlan
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (uvars : Nat) (Delta : KVLCtx) (args : Array (KExpr .anon)) :
    List Nat → Lean4Lean.VExpr → Prop
  | [], _ => True
  | i :: indices, currentV =>
      ∃ hidx : i < args.size,
        support (args[i]'hidx) ∧
        ProjectionArgumentFits trProj world support uvars Delta currentV
          (args[i]'hidx) ∧
        ∀ {next : KExpr .anon} {nextV : Lean4Lean.VExpr},
          support next →
          TrKExpr world.venv uvars world.nameOf trProj Delta next nextV →
          ProjectionParameterPlan trProj world support uvars Delta args
            indices nextV

/-- List-normalized form of the production parameter loop.  Every successful
iteration yields the exact substituted type to the tail; errors from Π
exposure or substitution retain the complete no-acceleration invariant. -/
theorem instantiateProjParamsList_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {Delta : KVLCtx}
    (theory : WhnfTheory trProj world uvars)
    (hwhnf : DirectWhnf.WFAt semantics trProj world support uvars)
    (hcomponents : ForallComponentSupport support)
    (hsubst : SubstitutionResources support)
    (hcollision : support.CollisionFree)
    {args : Array (KExpr .anon)} :
    ∀ (indices : List Nat) {current : KExpr .anon}
        {currentV : Lean4Lean.VExpr} {s : TcState .anon},
      support current →
      TrKExpr world.venv uvars world.nameOf trProj Delta current currentV →
      ProjectionParameterPlan trProj world support uvars Delta args indices
        currentV →
      RecM.WF .noAccel semantics trProj world support uvars Delta s
        (forIn (m := RecM .anon) indices current
          (instantiateProjParamStep args))
        (fun result _ => support result ∧
          ∃ resultV,
            TrKExpr world.venv uvars world.nameOf trProj Delta result
              resultV)
  | [], current, currentV, s, hcurrentSupport, hcurrent, _ => by
      rw [List.forIn_nil]
      exact RecM.WF.pure fun _ =>
        ⟨hcurrentSupport, currentV, hcurrent⟩
  | i :: indices, current, currentV, s, hcurrentSupport, hcurrent,
      hplan => by
      rcases hplan with
        ⟨hidx, hargSupport, hfits, htail⟩
      rw [List.forIn_cons]
      apply RecM.WF.bind
        (instantiateProjParamStep_wf hidx theory hwhnf hcomponents hsubst
          hcollision hcurrentSupport hargSupport hcurrent hfits)
      intro action after hpost
      cases action with
      | done result =>
          exact RecM.WF.pure fun _ => hpost
      | yield next =>
          rcases hpost with ⟨hnextSupport, nextV, hnext⟩
          exact instantiateProjParamsList_wf theory hwhnf hcomponents hsubst
            hcollision indices hnextSupport hnext
            (htail hnextSupport hnext)

/-- The exact production range loop, reduced to the verified list fold above.
The plan mentions the normalized range explicitly, making both the number and
order of parameter substitutions auditable. -/
theorem instantiateProjParams_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {Delta : KVLCtx} {s : TcState .anon}
    (theory : WhnfTheory trProj world uvars)
    (hwhnf : DirectWhnf.WFAt semantics trProj world support uvars)
    (hcomponents : ForallComponentSupport support)
    (hsubst : SubstitutionResources support)
    (hcollision : support.CollisionFree)
    {args : Array (KExpr .anon)} {numParams : Nat}
    {ctorTy : KExpr .anon} {ctorTyV : Lean4Lean.VExpr}
    (hctorSupport : support ctorTy)
    (hctor : TrKExpr world.venv uvars world.nameOf trProj Delta ctorTy
      ctorTyV)
    (hplan : ProjectionParameterPlan trProj world support uvars Delta args
      (List.range'
        ([0:numParams] : _root_.Std.Legacy.Range).start
        ([0:numParams] : _root_.Std.Legacy.Range).size
        ([0:numParams] : _root_.Std.Legacy.Range).step)
      ctorTyV) :
    RecM.WF .noAccel semantics trProj world support uvars Delta s
      (instantiateProjParams args numParams ctorTy)
      (fun result _ => support result ∧
        ∃ resultV,
          TrKExpr world.venv uvars world.nameOf trProj Delta result
            resultV) := by
  unfold instantiateProjParams
  rw [_root_.Std.Legacy.Range.forIn_eq_forIn_range']
  exact instantiateProjParamsList_wf theory hwhnf hcomponents hsubst
    hcollision _ hctorSupport hctor hplan

/-- The requested Theory projection has the domain exposed by every
supported Π view of the current constructor-field telescope. -/
def ProjectionFieldResultFits
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (uvars : Nat) (Delta : KVLCtx) (inputV projectedV : Lean4Lean.VExpr) :
    Prop :=
  ∀ {dom body : KExpr .anon} {domV bodyV : Lean4Lean.VExpr},
    support dom → support body →
    world.venv.IsType uvars Delta.toCtx domV →
    world.venv.IsType uvars (domV :: Delta.toCtx) bodyV →
    TrKExprS world.venv uvars world.nameOf trProj Delta dom domV →
    TrKExprS world.venv uvars world.nameOf trProj
      ((none, .vlam domV) :: Delta) body bodyV →
    world.venv.IsDefEqU uvars Delta.toCtx inputV (.forallE domV bodyV) →
    world.venv.HasType uvars Delta.toCtx projectedV domV

/-- Semantic inputs for exactly one production field iteration.  The
selected branch certifies the resulting projection type.  A preceding branch
certifies only the concrete projection node that production interns and
substitutes; it cannot choose the subsequent telescope result. -/
structure ProjectionFieldStepPlan
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (uvars : Nat) (Delta : KVLCtx) (structId : KId .anon)
    (field : UInt64) (val : KExpr .anon) (projectedV : Lean4Lean.VExpr)
    (i : Nat) (currentV : Lean4Lean.VExpr) : Prop where
  selected : i = field.toNat →
    ProjectionFieldResultFits trProj world support uvars Delta currentV
      projectedV
  preceding : i ≠ field.toNat →
    support (KExpr.mkPrj structId i.toUInt64 val) ∧
      ProjectionArgumentFits trProj world support uvars Delta currentV
        (KExpr.mkPrj structId i.toUInt64 val)

/-- Success postcondition that distinguishes the stopping field from an
intermediate telescope yielded to the surrounding traversal. -/
def ProjectionFieldActionPost
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (uvars : Nat) (Delta : KVLCtx) (projectedV : Lean4Lean.VExpr) :
    ForInStep (KExpr .anon) → Prop
  | .done result =>
      support result ∧ InferPost trProj world uvars Delta projectedV result
  | .yield next =>
      support next ∧ ∃ nextV,
        TrKExpr world.venv uvars world.nameOf trProj Delta next nextV

/-- Recursive inference followed by the direct sort exposure used by both
Prop-elimination guards.  The result is intentionally forgotten here: branch
soundness needs the callback and helper state contracts, while the pure guard
decides only whether execution continues or throws. -/
private theorem inferProjectionFieldSort_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {Delta : KVLCtx} {s : TcState .anon}
    {dom : KExpr .anon} {domV : Lean4Lean.VExpr}
    (hwhnf : DirectWhnf.WFAt semantics trProj world support uvars)
    (hsorts : SortComponentResources support)
    (hdomSupport : support dom)
    (hdom : TrKExprS world.venv uvars world.nameOf trProj Delta dom domV) :
    RecM.WF .noAccel semantics trProj world support uvars Delta s
      (do
        let fieldSortTy ← inferCall dom
        ensureSortDirect fieldSortTy)
      (fun _ _ => True) := by
  apply RecM.WF.bind
    (RecM.WF.withInv <| RecM.inferCall_wf hdomSupport hdom)
  intro fieldSortTy after hpost
  rcases hpost with
    ⟨_, hfieldSortSupport, fieldSortV, hfieldSortTr, _⟩
  exact RecM.WF.mono
    (RecM.ensureSortDirect_wf hwhnf hsorts hfieldSortSupport hfieldSortTr)
    (fun _ _ _ => trivial) (fun _ _ _ => trivial)

/-- A selected field returns the exact concrete domain exposed by production,
with the requested Theory projection typed by that domain. -/
private theorem finishSelectedProjectionField_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {Delta : KVLCtx} {s : TcState .anon}
    {inputV projectedV : Lean4Lean.VExpr}
    {dom body : KExpr .anon}
    (theory : WhnfTheory trProj world uvars)
    (hview : ForallView trProj world support uvars Delta inputV dom body)
    (hfits : ProjectionFieldResultFits trProj world support uvars Delta
      inputV projectedV) :
    RecM.WF .noAccel semantics trProj world support uvars Delta s
      (pure (.done dom))
      (fun action _ =>
        ProjectionFieldActionPost trProj world support uvars Delta projectedV
          action) := by
  apply RecM.WF.pure
  intro hI
  rcases hview with
    ⟨domV, bodyV, hdomSupport, hbodySupport, hdomType, hbodyType,
      hdomTr, hbodyTr, hinputEq⟩
  refine ⟨hdomSupport, domV, ?_, ?_⟩
  · exact hdomTr.trKExpr world.venvWF.ordered theory.literalWF
      theory.projections.wf hI.2.1.wf
  · exact hfits hdomSupport hbodySupport hdomType hbodyType hdomTr hbodyTr
      hinputEq

/-- A preceding field interns the exact projection node and substitutes it
through the exposed dependent body.  Both intern and substitution errors keep
their partial states inside the full checker invariant. -/
private theorem finishPrecedingProjectionField_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {Delta : KVLCtx} {s : TcState .anon}
    {structId : KId .anon} {i : Nat} {val : KExpr .anon}
    {inputV projectedV : Lean4Lean.VExpr}
    {dom body : KExpr .anon}
    (theory : WhnfTheory trProj world uvars)
    (hsubst : SubstitutionResources support)
    (hcollision : support.CollisionFree)
    (hview : ForallView trProj world support uvars Delta inputV dom body)
    (hprojSupport : support (KExpr.mkPrj structId i.toUInt64 val))
    (hfits : ProjectionArgumentFits trProj world support uvars Delta inputV
      (KExpr.mkPrj structId i.toUInt64 val)) :
    RecM.WF .noAccel semantics trProj world support uvars Delta s
      (do
        let proj ← TcM.intern (KExpr.mkPrj structId i.toUInt64 val)
        let result ← TcM.runIntern (subst body proj 0)
        pure (.yield result))
      (fun action _ =>
        ProjectionFieldActionPost trProj world support uvars Delta projectedV
          action) := by
  apply RecM.WF.bind
    (RecM.WF.withInv <| RecM.WF.liftTcM <|
      TcM.intern_whnf_wf hcollision hprojSupport)
  intro proj afterIntern hintern
  rcases hintern with ⟨_, rfl, _⟩
  apply RecM.WF.bind
    (substProjForallBody_wf theory hsubst hcollision hview hprojSupport
      hfits)
  intro result afterSubst hresult
  exact RecM.WF.pure fun _ => hresult

/-- Complete contract for one production field step.  It covers the selected
and preceding branches, both Prop guards, recursive inference and direct WHNF
errors, exact projection interning, and dependent substitution. -/
theorem inferProjFieldStep_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {Delta : KVLCtx} {s : TcState .anon}
    {structId : KId .anon} {field : UInt64} {val current : KExpr .anon}
    {isPropStruct : Bool} {i : Nat}
    {currentV projectedV : Lean4Lean.VExpr}
    (theory : WhnfTheory trProj world uvars)
    (hwhnf : DirectWhnf.WFAt semantics trProj world support uvars)
    (hcomponents : ForallComponentSupport support)
    (hsorts : SortComponentResources support)
    (hsubst : SubstitutionResources support)
    (hcollision : support.CollisionFree)
    (hcurrentSupport : support current)
    (hcurrent : TrKExpr world.venv uvars world.nameOf trProj Delta current
      currentV)
    (hplan : ProjectionFieldStepPlan trProj world support uvars Delta
      structId field val projectedV i currentV) :
    RecM.WF .noAccel semantics trProj world support uvars Delta s
      (inferProjFieldStep structId field val isPropStruct i current)
      (fun action _ =>
        ProjectionFieldActionPost trProj world support uvars Delta projectedV
          action) := by
  unfold inferProjFieldStep
  apply RecM.WF.bind
    (RecM.peelProjForall_wf hwhnf hcomponents hcurrentSupport hcurrent)
  intro exposed afterPeel hview
  rcases exposed with ⟨dom, body⟩
  simp only
  rcases hview with
    ⟨domV, bodyV, hdomSupport, hbodySupport, hdomType, hbodyType,
      hdomTr, hbodyTr, hinputEq⟩
  have hview : ForallView trProj world support uvars Delta currentV dom body :=
    ⟨domV, bodyV, hdomSupport, hbodySupport, hdomType, hbodyType,
      hdomTr, hbodyTr, hinputEq⟩
  have hdomSupport' : support dom := by simpa using hdomSupport
  have hdomTr' :
      TrKExprS world.venv uvars world.nameOf trProj Delta dom domV := by
    simpa using hdomTr
  split
  · rename_i hselected
    have hi : i = field.toNat := eq_of_beq hselected
    have hresult : ProjectionFieldResultFits trProj world support uvars Delta
        currentV projectedV := hplan.selected hi
    cases isPropStruct with
    | false =>
        simp only [Bool.false_eq_true, if_false]
        exact finishSelectedProjectionField_wf theory hview hresult
    | true =>
        simp only [if_true, pure_bind]
        rw [← bind_assoc]
        apply RecM.WF.bind
          (inferProjectionFieldSort_wf hwhnf hsorts hdomSupport' hdomTr')
        intro fieldLevel afterSort _
        split
        · exact RecM.WF.throw fun _ => trivial
        · exact finishSelectedProjectionField_wf theory hview hresult
  · rename_i hnotSelected
    have hi : i ≠ field.toNat := fun heq =>
      hnotSelected (beq_iff_eq.mpr heq)
    obtain ⟨hprojSupport, hfits⟩ := hplan.preceding hi
    cases isPropStruct with
    | false =>
        simp only [Bool.false_eq_true, if_false]
        exact finishPrecedingProjectionField_wf theory hsubst hcollision
          hview hprojSupport hfits
    | true =>
        simp only [if_true, pure_bind]
        rw [← bind_assoc]
        apply RecM.WF.bind
          (inferProjectionFieldSort_wf hwhnf hsorts hdomSupport' hdomTr')
        intro fieldLevel afterSort _
        split
        · exact RecM.WF.throw fun _ => trivial
        · exact finishPrecedingProjectionField_wf theory hsubst hcollision
            hview hprojSupport hfits

/-- The semantic plan for a field-index suffix.  Only a yielded concrete
telescope activates the continuation; a selected field terminates the
production fold immediately. -/
def ProjectionFieldPlan
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (uvars : Nat) (Delta : KVLCtx) (structId : KId .anon)
    (field : UInt64) (val : KExpr .anon) (projectedV : Lean4Lean.VExpr) :
    List Nat → Lean4Lean.VExpr → Prop
  | [], _ => True
  | i :: indices, currentV =>
      ProjectionFieldStepPlan trProj world support uvars Delta structId field
          val projectedV i currentV ∧
        ∀ {next : KExpr .anon} {nextV : Lean4Lean.VExpr},
          support next →
          TrKExpr world.venv uvars world.nameOf trProj Delta next nextV →
          ProjectionFieldPlan trProj world support uvars Delta structId field
            val projectedV indices nextV

/-- Final semantic state of the early-return accumulator generated by Lean's
`for` elaboration.  `some` carries a selected field type; `none` carries the
last yielded telescope and will be rejected by production as unreachable. -/
def ProjectionFieldLoopPost
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (uvars : Nat) (Delta : KVLCtx) (projectedV : Lean4Lean.VExpr) :
    Option (KExpr .anon) × KExpr .anon → Prop
  | (some result, _) =>
      support result ∧ InferPost trProj world uvars Delta projectedV result
  | (none, current) =>
      support current ∧ ∃ currentV,
        TrKExpr world.venv uvars world.nameOf trProj Delta current currentV

/-- Lift one named field step into the production loop accumulator, recording
whether it stops with `some` or yields `none` and a new telescope. -/
private theorem inferProjFieldLoopStep_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {Delta : KVLCtx} {s : TcState .anon}
    {structId : KId .anon} {field : UInt64} {val current : KExpr .anon}
    {isPropStruct : Bool} {i : Nat}
    {currentV projectedV : Lean4Lean.VExpr}
    (theory : WhnfTheory trProj world uvars)
    (hwhnf : DirectWhnf.WFAt semantics trProj world support uvars)
    (hcomponents : ForallComponentSupport support)
    (hsorts : SortComponentResources support)
    (hsubst : SubstitutionResources support)
    (hcollision : support.CollisionFree)
    (hcurrentSupport : support current)
    (hcurrent : TrKExpr world.venv uvars world.nameOf trProj Delta current
      currentV)
    (hplan : ProjectionFieldStepPlan trProj world support uvars Delta
      structId field val projectedV i currentV) :
    RecM.WF .noAccel semantics trProj world support uvars Delta s
      (inferProjFieldsLoopStep structId field val isPropStruct i
        ((none : Option (KExpr .anon)), current))
      (fun action _ => match action with
        | .done pair =>
            ∃ result,
              pair = (some result, current) ∧
                support result ∧
                InferPost trProj world uvars Delta projectedV result
        | .yield pair =>
            ∃ next nextV,
              pair = (none, next) ∧
                support next ∧
                TrKExpr world.venv uvars world.nameOf trProj Delta next
                  nextV) := by
  unfold inferProjFieldsLoopStep
  apply RecM.WF.bind
    (inferProjFieldStep_wf theory hwhnf hcomponents hsorts hsubst hcollision
      hcurrentSupport hcurrent hplan)
  intro action after hpost
  cases action with
  | done result =>
      exact RecM.WF.pure fun _ => ⟨result, rfl, hpost⟩
  | yield next =>
      rcases hpost with ⟨hnextSupport, nextV, hnext⟩
      exact RecM.WF.pure fun _ =>
        ⟨next, nextV, rfl, hnextSupport, hnext⟩

/-- List-normalized proof of the production field fold.  A `.done` action
returns immediately; a `.yield` action passes the exact substituted
telescope and its semantic-plan continuation to the remaining indices. -/
theorem inferProjFieldsList_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {Delta : KVLCtx}
    (theory : WhnfTheory trProj world uvars)
    (hwhnf : DirectWhnf.WFAt semantics trProj world support uvars)
    (hcomponents : ForallComponentSupport support)
    (hsorts : SortComponentResources support)
    (hsubst : SubstitutionResources support)
    (hcollision : support.CollisionFree)
    {structId : KId .anon} {field : UInt64} {val : KExpr .anon}
    {isPropStruct : Bool} {projectedV : Lean4Lean.VExpr} :
    ∀ (indices : List Nat) {current : KExpr .anon}
        {currentV : Lean4Lean.VExpr} {s : TcState .anon},
      support current →
      TrKExpr world.venv uvars world.nameOf trProj Delta current currentV →
      ProjectionFieldPlan trProj world support uvars Delta structId field val
        projectedV indices currentV →
      RecM.WF .noAccel semantics trProj world support uvars Delta s
        (forIn (m := RecM .anon) indices
          ((none : Option (KExpr .anon)), current)
          (inferProjFieldsLoopStep structId field val isPropStruct))
        (fun pair _ =>
          ProjectionFieldLoopPost trProj world support uvars Delta projectedV
            pair)
  | [], current, currentV, s, hcurrentSupport, hcurrent, _ => by
      rw [List.forIn_nil]
      exact RecM.WF.pure fun _ =>
        ⟨hcurrentSupport, currentV, hcurrent⟩
  | i :: indices, current, currentV, s, hcurrentSupport, hcurrent,
      hplan => by
      rcases hplan with ⟨hstepPlan, htail⟩
      rw [List.forIn_cons]
      apply RecM.WF.bind
        (inferProjFieldLoopStep_wf theory hwhnf hcomponents hsorts hsubst
          hcollision hcurrentSupport hcurrent hstepPlan)
      intro action after hpost
      cases action with
      | done pair =>
          rcases hpost with ⟨result, rfl, hresult⟩
          exact RecM.WF.pure fun _ => hresult
      | yield pair =>
          rcases hpost with
            ⟨next, nextV, rfl, hnextSupport, hnext⟩
          exact inferProjFieldsList_wf theory hwhnf hcomponents hsorts hsubst
            hcollision indices hnextSupport hnext
            (htail hnextSupport hnext)

/-- The exact production field traversal, including Lean's generated
early-return accumulator and the final unreachable error when no index stops
the range.  Successful results are supported concrete types of the requested
Theory projection. -/
theorem inferProjFields_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {Delta : KVLCtx} {s : TcState .anon}
    (theory : WhnfTheory trProj world uvars)
    (hwhnf : DirectWhnf.WFAt semantics trProj world support uvars)
    (hcomponents : ForallComponentSupport support)
    (hsorts : SortComponentResources support)
    (hsubst : SubstitutionResources support)
    (hcollision : support.CollisionFree)
    {structId : KId .anon} {field : UInt64} {val ctorTy : KExpr .anon}
    {isPropStruct : Bool} {ctorTyV projectedV : Lean4Lean.VExpr}
    (hctorSupport : support ctorTy)
    (hctor : TrKExpr world.venv uvars world.nameOf trProj Delta ctorTy
      ctorTyV)
    (hplan : ProjectionFieldPlan trProj world support uvars Delta structId
      field val projectedV
      (List.range'
        ([0:field.toNat + 1] : _root_.Std.Legacy.Range).start
        ([0:field.toNat + 1] : _root_.Std.Legacy.Range).size
        ([0:field.toNat + 1] : _root_.Std.Legacy.Range).step)
      ctorTyV) :
    RecM.WF .noAccel semantics trProj world support uvars Delta s
      (inferProjFields structId field val isPropStruct ctorTy)
      (fun result _ => support result ∧
        InferPost trProj world uvars Delta projectedV result) := by
  unfold inferProjFields
  rw [_root_.Std.Legacy.Range.forIn_eq_forIn_range']
  apply RecM.WF.bind
    (inferProjFieldsList_wf (structId := structId) (field := field)
      (val := val) (isPropStruct := isPropStruct) (projectedV := projectedV)
      (s := s) theory hwhnf hcomponents hsorts hsubst hcollision _
      hctorSupport hctor hplan)
  intro pair after hpost
  rcases pair with ⟨found, current⟩
  cases found with
  | none =>
      exact RecM.WF.throw fun _ => trivial
  | some result =>
      exact RecM.WF.pure fun _ => hpost

end RecM

end Ix.Tc
