import Ix.Tc.Verify.DefEq.FinalWhnf.StructureEtaFields
import Ix.Tc.Verify.DefEq.CheapReduction

/-!
# Structure-eta common-base scan

The fast structure-eta path recognizes constructor fields that normalize to
projections of one common base.  This module verifies the exact recursive
scan, including the uncaught field WHNF, caught base WHNF, projection-shape
checks, collision-safe base-address comparison, and every partial-error
state.  A successful result carries the semantic projection equality for
each scanned field.
-/

namespace Ix.Tc

open Lean4Lean (VExpr)

/-- Invert the structural translation of one concrete projection while
retaining the resolved structure name and raw projection witness. -/
theorem TrKExprS.prj_components
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {id : KId .anon} {idx : UInt64}
    {value : KExpr .anon} {info : ExprInfo .anon} {projectedV : VExpr}
    (h : TrKExprS world.venv uvars world.nameOf trProj Delta
      (.prj id idx value info) projectedV) :
    ∃ structName valueV,
      world.nameOf id.addr = some structName ∧
      TrKExprS world.venv uvars world.nameOf trProj Delta value valueV ∧
      trProj Delta.toCtx structName idx.toNat valueV projectedV := by
  cases h with
  | prj hname hvalue hprojection =>
      exact ⟨_, _, hname, hvalue, hprojection⟩

/-- One constructor field denotes the corresponding projection of the base
returned by `etaExpansionBaseLoop`. -/
def EtaExpansionFieldAgreement (trProj : RawProjRel)
    (world : VerifyWorld) (uvars : Nat) (Delta : KVLCtx)
    (inductId : KId .anon) (field : Nat) (fieldV baseV : VExpr) : Prop :=
  ∃ structName projectedV,
    world.nameOf inductId.addr = some structName ∧
      trProj Delta.toCtx structName field baseV projectedV ∧
      world.venv.IsDefEqU uvars Delta.toCtx fieldV projectedV

/-- Semantic result of a common-base scan.  If a seed was supplied, a
successful scan retains that exact concrete seed; this makes the first-field
transition from `none` to `some` explicit in the induction. -/
def EtaExpansionBaseLoopPost (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (uvars : Nat)
    (Delta : KVLCtx) (inductId : KId .anon) (field fuel : Nat)
    (fieldV : Nat → VExpr)
    (seed result : Option (KExpr .anon)) : Prop :=
  match result with
  | none => True
  | some base =>
      support base ∧ ∃ baseV,
        TrKExprS world.venv uvars world.nameOf trProj Delta base baseV ∧
        (∀ prior, seed = some prior → base = prior) ∧
        ∀ offset, offset < fuel →
          EtaExpansionFieldAgreement trProj world uvars Delta inductId
            (field + offset) (fieldV offset) baseV

namespace RecM

/-- Exact proof of the common-base scanner. -/
theorem etaExpansionBaseLoop_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {state : TcState .anon}
    {inductId : KId .anon} {numParams field fuel : Nat}
    {args : Array (KExpr .anon)} {fieldV : Nat → VExpr}
    {seed : Option (KExpr .anon)}
    (theory : WhnfTheory trProj world uvars)
    (hcollision : support.CollisionFree)
    (hnoDelta : DefEqReduction.WFAt layer semantics trProj world support
      uvars whnfNoDelta)
    (hprojectionValue : ∀ {id : KId .anon} {idx : UInt64}
        {value : KExpr .anon} {info : ExprInfo .anon},
      support (.prj id idx value info) → support value)
    (hseed : match seed with
      | none => True
      | some base => ∃ baseV, support base ∧
          TrKExprS world.venv uvars world.nameOf trProj Delta base baseV)
    (hfieldSupport : ∀ offset, offset < fuel →
      support args[numParams + field + offset]!)
    (hfield : ∀ offset, offset < fuel →
      TrKExprS world.venv uvars world.nameOf trProj Delta
        args[numParams + field + offset]! (fieldV offset)) :
    RecM.WF layer semantics trProj world support uvars Delta state
      (etaExpansionBaseLoop inductId numParams args fuel field seed)
      (fun result _ =>
        EtaExpansionBaseLoopPost trProj world support uvars Delta inductId
          field fuel fieldV seed result) := by
  induction fuel generalizing state field fieldV seed with
  | zero =>
      simp only [etaExpansionBaseLoop]
      cases seed with
      | none =>
          exact RecM.WF.pure fun _ => trivial
      | some base =>
          rcases hseed with ⟨baseV, hbaseSupport, hbase⟩
          exact RecM.WF.pure fun _ =>
            ⟨hbaseSupport, baseV, hbase, fun prior hprior => by
              cases hprior
              rfl, fun offset hlt => by omega⟩
  | succ remaining ih =>
      simp only [etaExpansionBaseLoop]
      have hzero : 0 < remaining + 1 := by omega
      apply RecM.WF.bind <| RecM.WF.withInv <|
        hnoDelta (hfieldSupport 0 hzero) (hfield 0 hzero)
      intro reduced afterField hfieldReduced
      rcases hfieldReduced with
        ⟨hIField, hreducedSupport, reducedV, hreducedTr, hreduceEq⟩
      cases reduced <;> simp only
      all_goals first
        | exact RecM.WF.pure fun _ => trivial
        | skip
      case prj id idx value info =>
        obtain ⟨structName, valueV, hresolved, hvalueTr,
          hrawProjection⟩ := hreducedTr.prj_components
        cases hshape :
            (id.addr != inductId.addr || idx.toNat != field) with
        | true =>
            simp only [if_true]
            exact RecM.WF.pure fun _ => trivial
        | false =>
            have hshapeParts := Bool.or_eq_false_iff.mp hshape
            have hidAddr : id.addr = inductId.addr := eq_of_beq
              (show (id.addr == inductId.addr) = true by
                simpa using hshapeParts.1)
            have hid : id = inductId := KId.anon_eq_of_addr_eq hidAddr
            subst id
            have hidx : idx.toNat = field := eq_of_beq
              (show (idx.toNat == field) = true by
                simpa using hshapeParts.2)
            simp only [Bool.false_eq_true, if_false, pure_bind]
            unfold etaExpansionBaseAfterProjection
            have hvalueSupport := hprojectionValue hreducedSupport
            apply RecM.WF.bind <| RecM.WF.withInv <| tryOptional_wf <|
              RecM.WF.withInv <| hnoDelta hvalueSupport hvalueTr
            intro normalized afterValue hnormalized
            rcases hnormalized with ⟨hIValue, hnormalized⟩
            have hcontinue : ∀ {chosen : KExpr .anon} {chosenV : VExpr},
                support chosen →
                TrKExprS world.venv uvars world.nameOf trProj Delta
                  chosen chosenV →
                world.venv.IsDefEqU uvars Delta.toCtx
                  valueV chosenV →
                RecM.WF layer semantics trProj world support uvars Delta
                  afterValue
                  (etaExpansionBaseAfterValue inductId numParams args
                    remaining field seed chosen)
                  (fun result _ =>
                    EtaExpansionBaseLoopPost trProj world support uvars Delta
                      inductId field (remaining + 1) fieldV seed result) := by
              intro chosen chosenV hchosenSupport hchosen hvalueChosen
              unfold etaExpansionBaseAfterValue
              cases seed with
              | none =>
                  simp only
                  apply RecM.WF.mono <| RecM.WF.withInv <|
                    ih (state := afterValue) (field := field + 1)
                      (fieldV := fun offset => fieldV (offset + 1))
                      (seed := some chosen)
                      ⟨chosenV, hchosenSupport, hchosen⟩
                      (fun offset hlt => by
                        simpa only [Nat.add_assoc, Nat.add_left_comm,
                          Nat.add_comm] using
                            hfieldSupport (offset + 1) (by omega))
                      (fun offset hlt => by
                        simpa only [Nat.add_assoc, Nat.add_left_comm,
                          Nat.add_comm] using
                            hfield (offset + 1) (by omega))
                  · intro result final htail
                    rcases htail with ⟨hIFinal, htail⟩
                    cases result with
                    | none => trivial
                    | some resultBase =>
                        rcases htail with
                          ⟨hresultSupport, resultBaseV, hresultTr,
                            hseedResult, htailAgreement⟩
                        have hresultEq : resultBase = chosen :=
                          hseedResult chosen rfl
                        subst resultBase
                        have hDelta : KVLCtx.WF world.venv uvars Delta :=
                          hIFinal.2.1.wf
                        have hctx :=
                          (KVLCtx.IsDefEq.refl world.venvWF.ordered
                            hDelta).defeqCtx
                        have hchosenResult := hchosen.uniq world.venvWF
                          theory.literalWF theory.projections
                          (KVLCtx.IsDefEq.refl world.venvWF hDelta)
                          hresultTr
                        have hvalueResult := hvalueChosen.trans world.venvWF
                          hDelta hchosenResult
                        have hrawProjection' :
                            trProj Delta.toCtx structName field valueV
                              reducedV := by
                          simpa only [hidx] using hrawProjection
                        obtain ⟨resultProjectedV, hresultProjection⟩ :=
                          theory.projections.defeqDFC hctx hvalueResult
                            hrawProjection'
                        have hprojectionEq := theory.projections.uniq hctx
                          hrawProjection' hresultProjection hvalueResult
                        refine ⟨hresultSupport, resultBaseV, hresultTr,
                          ?_, ?_⟩
                        · intro prior hprior
                          contradiction
                        · intro offset hlt
                          cases offset with
                          | zero =>
                              exact ⟨structName, resultProjectedV,
                                hresolved, hresultProjection,
                                hreduceEq.trans world.venvWF hDelta
                                  hprojectionEq⟩
                          | succ offset =>
                              simpa only [Nat.succ_eq_add_one,
                                Nat.add_assoc, Nat.add_left_comm,
                                Nat.add_comm] using
                                  htailAgreement offset (by omega)
                  · intro _ _ _
                    trivial
              | some base =>
                  rcases hseed with ⟨baseV, hbaseSupport, hbase⟩
                  cases haddr : (base.addr != chosen.addr) with
                  | true =>
                      simp only [haddr, if_true]
                      exact RecM.WF.pure fun _ => trivial
                  | false =>
                      simp only [haddr, Bool.false_eq_true, if_false,
                        pure_bind]
                      have haddrEq : (base.addr == chosen.addr) = true := by
                        simpa using haddr
                      have hbaseChosen : base = chosen := by
                        have herase := hcollision.expr.addrFaithful
                          hbaseSupport hchosenSupport haddrEq
                        simpa only [KExpr.eraseMeta_anon] using herase
                      subst chosen
                      apply RecM.WF.mono <| RecM.WF.withInv <|
                        ih (state := afterValue) (field := field + 1)
                          (fieldV := fun offset => fieldV (offset + 1))
                          (seed := some base)
                          ⟨baseV, hbaseSupport, hbase⟩
                          (fun offset hlt => by
                            simpa only [Nat.add_assoc, Nat.add_left_comm,
                              Nat.add_comm] using
                                hfieldSupport (offset + 1) (by omega))
                          (fun offset hlt => by
                            simpa only [Nat.add_assoc, Nat.add_left_comm,
                              Nat.add_comm] using
                                hfield (offset + 1) (by omega))
                      · intro result final htail
                        rcases htail with ⟨hIFinal, htail⟩
                        cases result with
                        | none => trivial
                        | some resultBase =>
                            rcases htail with
                              ⟨hresultSupport, resultBaseV, hresultTr,
                                hseedResult, htailAgreement⟩
                            have hresultEq : resultBase = base :=
                              hseedResult base rfl
                            subst resultBase
                            have hDelta : KVLCtx.WF world.venv uvars Delta :=
                              hIFinal.2.1.wf
                            have hctx :=
                              (KVLCtx.IsDefEq.refl world.venvWF.ordered
                                hDelta).defeqCtx
                            have hchosenResult := hchosen.uniq world.venvWF
                              theory.literalWF theory.projections
                              (KVLCtx.IsDefEq.refl world.venvWF hDelta)
                              hresultTr
                            have hvalueResult := hvalueChosen.trans
                              world.venvWF hDelta hchosenResult
                            have hrawProjection' :
                                trProj Delta.toCtx structName field valueV
                                  reducedV := by
                              simpa only [hidx] using hrawProjection
                            obtain ⟨resultProjectedV, hresultProjection⟩ :=
                              theory.projections.defeqDFC hctx hvalueResult
                                hrawProjection'
                            have hprojectionEq := theory.projections.uniq
                              hctx hrawProjection' hresultProjection
                              hvalueResult
                            refine ⟨hresultSupport, resultBaseV, hresultTr,
                              ?_, ?_⟩
                            · intro prior hprior
                              cases hprior
                              rfl
                            · intro offset hlt
                              cases offset with
                              | zero =>
                                  exact ⟨structName, resultProjectedV,
                                    hresolved, hresultProjection,
                                    hreduceEq.trans world.venvWF hDelta
                                      hprojectionEq⟩
                              | succ offset =>
                                  simpa only [Nat.succ_eq_add_one,
                                    Nat.add_assoc, Nat.add_left_comm,
                                    Nat.add_comm] using
                                      htailAgreement offset (by omega)
                      · intro _ _ _
                        trivial
            cases normalized with
            | none =>
                have hvalueRefl : world.venv.IsDefEqU uvars Delta.toCtx
                    valueV valueV :=
                  Lean4Lean.VEnv.IsDefEqU.refl
                    (theory.exprWF hIValue.2.1 hvalueTr)
                exact hcontinue hvalueSupport hvalueTr hvalueRefl
            | some chosen =>
                rcases hnormalized with
                  ⟨_, hchosenSupport, chosenV, hchosen, hvalueChosen⟩
                exact hcontinue hchosenSupport hchosen hvalueChosen

/-- Public wrapper for the common-base scan started with no seed. -/
theorem etaExpansionBase_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {state : TcState .anon}
    {inductId : KId .anon} {numParams numFields : Nat}
    {args : Array (KExpr .anon)} {fieldV : Nat → VExpr}
    (theory : WhnfTheory trProj world uvars)
    (hcollision : support.CollisionFree)
    (hnoDelta : DefEqReduction.WFAt layer semantics trProj world support
      uvars whnfNoDelta)
    (hprojectionValue : ∀ {id : KId .anon} {idx : UInt64}
        {value : KExpr .anon} {info : ExprInfo .anon},
      support (.prj id idx value info) → support value)
    (hfieldSupport : ∀ field, field < numFields →
      support args[numParams + field]!)
    (hfield : ∀ field, field < numFields →
      TrKExprS world.venv uvars world.nameOf trProj Delta
        args[numParams + field]! (fieldV field)) :
    RecM.WF layer semantics trProj world support uvars Delta state
      (etaExpansionBase inductId numParams numFields args)
      (fun result _ => match result with
        | none => True
        | some base => support base ∧ ∃ baseV,
            TrKExprS world.venv uvars world.nameOf trProj Delta base baseV ∧
            ∀ field, field < numFields →
              EtaExpansionFieldAgreement trProj world uvars Delta inductId
                field (fieldV field) baseV) := by
  unfold etaExpansionBase
  apply RecM.WF.mono <|
    etaExpansionBaseLoop_wf theory hcollision hnoDelta hprojectionValue
      (seed := none) trivial
      (fun offset hlt => by simpa using hfieldSupport offset hlt)
      (fun offset hlt => by simpa using hfield offset hlt)
  · intro result final hpost
    cases result with
    | none => trivial
    | some base =>
        rcases hpost with
          ⟨hbaseSupport, baseV, hbase, _, hagreement⟩
        exact ⟨hbaseSupport, baseV, hbase, fun field hlt => by
          simpa using hagreement field hlt⟩
  · intro _ _ _
    trivial

end RecM

end Ix.Tc
