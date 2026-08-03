import Ix.Tc.Verify.DefEq.FinalWhnf.Contracts
import Ix.Tc.Verify.DefEq.NatOffset

/-!
# Final-WHNF Nat bridge

This module verifies the compact-Nat/constructor bridge at the head of the
final fallback chain.  A successful successor peel records both the exact
Theory successor shape and the predecessor's canonical Nat type; recursive
predecessor equality can therefore be lifted through `Nat.succ` without
assuming injectivity or reflection beyond the trusted primitive table.
-/

namespace Ix.Tc

open Lean4Lean (VExpr)

/-- Trusted primitive facts and finite support needed by the final Nat
comparison. -/
structure FinalWhnfNatResources (world : VerifyWorld)
    (support : RunSupport) : Prop where
  zero : RecM.NatZeroContext world
  collision : support.CollisionFree
  natContains : world.venv.contains ``Nat
  generated : ∀ n, support (RecM.natExprFromValue n : KExpr .anon)
  appArgument : ∀ {fn arg : KExpr .anon} {info : ExprInfo .anon},
    support (.app fn arg info) → support arg

namespace RecM

/-- Canonical Nat numerals have the canonical Nat type in every verified
context, derived directly from the trusted zero/successor declarations. -/
private theorem finalNatLit_hasType
    {trProj : RawProjRel} {world : VerifyWorld}
    {uvars : Nat} {Delta : KVLCtx} {prims : Primitives .anon}
    (hcatalog : TrustedCatalogRel trProj world)
    (htable : NoDeltaPrimitiveTableAgrees world prims)
    (hprims : world.venv.HasPrimitives) :
    ∀ n, world.venv.HasType uvars Delta.toCtx (.natLit n) .nat
  | 0 => by
      obtain ⟨ci, hlookup⟩ := htable.natZero.contains hcatalog
      have hci := hprims.natZero hlookup
      subst ci
      exact Lean4Lean.VEnv.HasType.const hlookup (by simp) rfl
  | n + 1 =>
      Lean4Lean.VEnv.HasType.app
        (natSucc_hasType hcatalog htable hprims)
        (finalNatLit_hasType hcatalog htable hprims n)

/-- Reading the primitive table and classifying a Nat-like head does not
change checker state.  No semantic fact is assigned to a negative result. -/
theorem isNatLike_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {Delta : KVLCtx} {state : TcState .anon} (source : KExpr .anon) :
    RecM.WF .noAccel semantics trProj world support uvars Delta state
      (isNatLike source) (fun _ after => after = state) := by
  unfold isNatLike
  apply RecM.WF.bind (RecM.WF.withInv (prims_wf (s := state)))
  intro runtimePrims afterRead hread
  rcases hread with ⟨_, hprims, hafterRead⟩
  subst runtimePrims
  subst afterRead
  cases source <;> simp only
  all_goals first
    | exact RecM.WF.pure fun _ => rfl
    | skip
  rename_i fn arg info
  cases fn <;> exact RecM.WF.pure fun _ => rfl

/-- Positive-result contract for one Nat successor peel. -/
def NatSuccOf.WFAt (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (uvars : Nat) : Prop :=
  ∀ {Delta state source sourceV},
    support source →
    TrKExprS world.venv uvars world.nameOf trProj Delta source sourceV →
    RecM.WF .noAccel semantics trProj world support uvars Delta state
      (natSuccOf source)
      (fun result _ => match result with
        | none => True
        | some predecessor =>
            support predecessor ∧ ∃ predecessorV,
              TrKExprS world.venv uvars world.nameOf trProj Delta
                predecessor predecessorV ∧
              world.venv.HasType uvars Delta.toCtx predecessorV .nat ∧
              sourceV = .app .natSucc predecessorV)

/-- The concrete successor recognizer is sound for compact positive literals
and explicit applications of the trusted `Nat.succ` primitive. -/
theorem natSuccOf_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {Delta : KVLCtx} {state : TcState .anon}
    {source : KExpr .anon} {sourceV : VExpr}
    (resources : FinalWhnfNatResources world support)
    (hsourceSupport : support source)
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta source
      sourceV) :
    RecM.WF .noAccel semantics trProj world support uvars Delta state
      (natSuccOf source)
      (fun result _ => match result with
        | none => True
        | some predecessor =>
            support predecessor ∧ ∃ predecessorV,
              TrKExprS world.venv uvars world.nameOf trProj Delta
                predecessor predecessorV ∧
              world.venv.HasType uvars Delta.toCtx predecessorV .nat ∧
              sourceV = .app .natSucc predecessorV) := by
  unfold natSuccOf
  apply RecM.WF.bind (RecM.WF.withInv (prims_wf (s := state)))
  intro runtimePrims afterRead hread
  rcases hread with ⟨hI, hprims, hafterRead⟩
  subst runtimePrims
  subst afterRead
  have htable := resources.zero.table state.prims hI.noAccel_primitives
  cases source with
  | nat value blob info =>
      cases value with
      | zero =>
          simp only [beq_self_eq_true, if_true]
          exact RecM.WF.pure fun _ => trivial
      | succ predecessor =>
          have hnonzero : (Nat.succ predecessor == 0) = false := by simp
          simp only [hnonzero, Bool.false_eq_true, if_false,
            Nat.succ_sub_one, pure_bind]
          apply RecM.WF.bind
            (RecM.WF.withInv <| RecM.WF.liftTcM <|
              TcM.intern_whnf_wf resources.collision
                (resources.generated predecessor))
          intro result afterIntern hresult
          rcases hresult with ⟨hIIntern, hresultEq, _⟩
          subst result
          exact RecM.WF.pure fun _ => by
            cases hsource
            have hpredTr : TrKExprS world.venv uvars world.nameOf trProj
                Delta (natExprFromValue predecessor : KExpr .anon)
                (.natLit predecessor) := by
              exact .nat (by simpa [Lean4Lean.VEnv.ContainsLits] using
                resources.natContains)
            have hpredType : world.venv.HasType uvars Delta.toCtx
                (.natLit predecessor) .nat :=
              finalNatLit_hasType hI.1.core.trustedCatalog htable
                resources.zero.theoryPrimitives predecessor
            exact ⟨resources.generated predecessor, .natLit predecessor,
              hpredTr, hpredType, rfl⟩
  | app fn arg info =>
      cases fn with
      | const id levels fnInfo =>
          cases haddr : id.addr == state.prims.natSucc.addr with
          | false =>
              simp only [haddr, Bool.false_eq_true, if_false]
              exact RecM.WF.pure fun _ => trivial
          | true =>
              simp only [haddr, if_true]
              exact RecM.WF.pure fun _ => by
                cases hsource with
                | app hfnType hargType hfn harg =>
                    cases hfn with
                    | const hname hlookup hlevels harity =>
                        have hid : id.addr = state.prims.natSucc.addr :=
                          eq_of_beq haddr
                        have hnameEq := Option.some.inj <|
                          hname.symm.trans <|
                            (congrArg world.nameOf hid).trans
                              htable.natSucc.2
                        subst_vars
                        have hci := resources.zero.theoryPrimitives.natSucc
                          hlookup
                        subst_vars
                        have hsize : levels.size = 0 := by
                          simpa using harity
                        have hlevelsEmpty : levels = #[] :=
                          Array.eq_empty_of_size_eq_zero hsize
                        subst levels
                        have hDelta : KVLCtx.WF world.venv uvars Delta :=
                          hI.2.1.wf
                        have hsucc := natSucc_hasType
                          (uvars := uvars) (Delta := Delta)
                          hI.1.core.trustedCatalog htable
                          resources.zero.theoryPrimitives
                        have hfunctionTypes := hfnType.uniqU world.venvWF
                          hDelta.toCtx hsucc
                        obtain ⟨_, hdomain⟩ :=
                          hfunctionTypes.forallE_inv world.venvWF
                            hDelta.toCtx |>.1
                        have hargNat := hargType.defeqU_r world.venvWF
                          hDelta.toCtx ⟨_, hdomain⟩
                        exact ⟨resources.appArgument hsourceSupport, _, harg,
                          hargNat, rfl⟩
      | _ =>
          simp only
          exact RecM.WF.pure fun _ => trivial
  | _ =>
      simp only
      exact RecM.WF.pure fun _ => trivial

namespace NatSuccOf

/-- Package the concrete successor recognizer. -/
theorem ofResources
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    (resources : FinalWhnfNatResources world support) :
    NatSuccOf.WFAt semantics trProj world support uvars := by
  intro Delta state source sourceV hsourceSupport hsource
  exact natSuccOf_wf resources hsourceSupport hsource

end NatSuccOf

/-- Soundness of zero/successor comparison after the literal pair misses. -/
theorem isDefEqNatAfterLiteral_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {Delta : KVLCtx} {state : TcState .anon}
    {left right : KExpr .anon} {leftV rightV : VExpr}
    (theory : WhnfTheory trProj world uvars)
    (resources : FinalWhnfNatResources world support)
    (hleftSupport : support left) (hrightSupport : support right)
    (hleft : TrKExprS world.venv uvars world.nameOf trProj Delta left leftV)
    (hright : TrKExprS world.venv uvars world.nameOf trProj Delta right
      rightV) :
    RecM.WF .noAccel semantics trProj world support uvars Delta state
      (isDefEqNatAfterLiteral left right)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU uvars Delta.toCtx leftV rightV) := by
  unfold isDefEqNatAfterLiteral
  apply RecM.WF.bind <|
    isNatZero_wf resources.zero hleftSupport hleft
  intro leftZero afterLeft hleftZero
  apply RecM.WF.bind <|
    isNatZero_wf resources.zero hrightSupport hright
  intro rightZero afterRight hrightZero
  cases leftZero with
  | true =>
      cases rightZero with
      | true =>
          simp only [Bool.true_and, if_true]
          exact RecM.WF.pure fun hI _ => by
            have hleftValue := hleftZero rfl
            have hrightValue := hrightZero rfl
            subst leftV
            subst rightV
            exact Lean4Lean.VEnv.IsDefEqU.refl <|
              hleft.wf world.venvWF.ordered theory.literalWF
                theory.projections.wf hI.2.1.wf
      | false =>
          simp only [Bool.true_and, Bool.false_eq_true, if_false]
          apply RecM.WF.bind <|
            natSuccOf_wf resources hleftSupport hleft
          intro leftPred afterLeftPred hleftPred
          apply RecM.WF.bind <|
            natSuccOf_wf resources hrightSupport hright
          intro rightPred afterRightPred hrightPred
          cases leftPred <;> cases rightPred <;>
            simp only
          · exact RecM.WF.pure fun _ h => by contradiction
          · exact RecM.WF.pure fun _ h => by contradiction
          · exact RecM.WF.pure fun _ h => by contradiction
          · rename_i leftPred rightPred
            rcases hleftPred with
              ⟨hleftPredSupport, leftPredV, hleftPredTr,
                hleftPredType, hleftShape⟩
            rcases hrightPred with
              ⟨hrightPredSupport, rightPredV, hrightPredTr,
                hrightPredType, hrightShape⟩
            apply RecM.WF.mono <| RecM.WF.withInv <|
              RecM.isDefEqCall_wf hleftPredSupport hrightPredSupport
                hleftPredTr hrightPredTr
            · intro answer final hanswer htrue
              rw [hleftShape, hrightShape]
              have htable := resources.zero.table final.prims
                hanswer.1.noAccel_primitives
              have hsucc := natSucc_hasType
                (uvars := uvars) (Delta := Delta)
                hanswer.1.1.core.trustedCatalog htable
                resources.zero.theoryPrimitives
              exact (hsucc.appDF <|
                (hanswer.2 htrue).of_l world.venvWF
                  hanswer.1.2.1.wf.toCtx hleftPredType).toU
            · intro _ _ _
              trivial
  | false =>
      cases rightZero <;>
        simp only [Bool.false_and, Bool.false_eq_true, if_false]
      all_goals
        apply RecM.WF.bind <|
          natSuccOf_wf resources hleftSupport hleft
        intro leftPred afterLeftPred hleftPred
        apply RecM.WF.bind <|
          natSuccOf_wf resources hrightSupport hright
        intro rightPred afterRightPred hrightPred
        cases leftPred <;> cases rightPred <;>
          simp only
        · exact RecM.WF.pure fun _ h => by contradiction
        · exact RecM.WF.pure fun _ h => by contradiction
        · exact RecM.WF.pure fun _ h => by contradiction
        · rename_i leftPred rightPred
          rcases hleftPred with
            ⟨hleftPredSupport, leftPredV, hleftPredTr,
              hleftPredType, hleftShape⟩
          rcases hrightPred with
            ⟨hrightPredSupport, rightPredV, hrightPredTr,
              hrightPredType, hrightShape⟩
          apply RecM.WF.mono <| RecM.WF.withInv <|
            RecM.isDefEqCall_wf hleftPredSupport hrightPredSupport
              hleftPredTr hrightPredTr
          · intro answer final hanswer htrue
            rw [hleftShape, hrightShape]
            have htable := resources.zero.table final.prims
              hanswer.1.noAccel_primitives
            have hsucc := natSucc_hasType
              (uvars := uvars) (Delta := Delta)
              hanswer.1.1.core.trustedCatalog htable
              resources.zero.theoryPrimitives
            exact (hsucc.appDF <|
              (hanswer.2 htrue).of_l world.venvWF
                hanswer.1.2.1.wf.toCtx hleftPredType).toU
          · intro _ _ _
            trivial

/-- Complete direct-literal plus zero/successor Nat comparison. -/
theorem isDefEqNat_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {Delta : KVLCtx} {state : TcState .anon}
    {left right : KExpr .anon} {leftV rightV : VExpr}
    (theory : WhnfTheory trProj world uvars)
    (resources : FinalWhnfNatResources world support)
    (hleftSupport : support left) (hrightSupport : support right)
    (hleft : TrKExprS world.venv uvars world.nameOf trProj Delta left leftV)
    (hright : TrKExprS world.venv uvars world.nameOf trProj Delta right
      rightV) :
    RecM.WF .noAccel semantics trProj world support uvars Delta state
      (isDefEqNat left right)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU uvars Delta.toCtx leftV rightV) := by
  cases left <;> cases right <;> simp only [isDefEqNat]
  all_goals
    first
    | exact isDefEqNatAfterLiteral_wf theory resources hleftSupport
        hrightSupport hleft hright
    | skip
  have hleftTr := hleft
  cases hleft
  cases hright
  exact RecM.WF.pure fun hI hanswer => by
    have hvalue := eq_of_beq hanswer
    subst_vars
    exact Lean4Lean.VEnv.IsDefEqU.refl <|
      hleftTr.wf world.venvWF.ordered theory.literalWF
        theory.projections.wf hI.2.1.wf

/-- Close the optional Nat gate itself. -/
theorem tryDefEqWhnfNat_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {Delta : KVLCtx} {state : TcState .anon}
    {left right : KExpr .anon} {leftV rightV : VExpr}
    (theory : WhnfTheory trProj world uvars)
    (resources : FinalWhnfNatResources world support)
    (hleftSupport : support left) (hrightSupport : support right)
    (hleft : TrKExprS world.venv uvars world.nameOf trProj Delta left leftV)
    (hright : TrKExprS world.venv uvars world.nameOf trProj Delta right
      rightV) :
    RecM.WF .noAccel semantics trProj world support uvars Delta state
      (tryDefEqWhnfNat left right)
      (fun result _ => match result with
        | none => True
        | some answer => answer = true →
            world.venv.IsDefEqU uvars Delta.toCtx leftV rightV) := by
  unfold tryDefEqWhnfNat
  apply RecM.WF.bind (isNatLike_wf left)
  intro leftLike afterLeft hafterLeft
  subst afterLeft
  apply RecM.WF.bind (isNatLike_wf right)
  intro rightLike afterRight hafterRight
  subst afterRight
  cases leftLike <;> cases rightLike <;>
    simp only [Bool.false_and, Bool.true_and, Bool.false_eq_true, if_false,
      if_true]
  all_goals
    first
    | exact RecM.WF.pure fun _ => trivial
    | skip
  apply RecM.WF.bind <|
    isDefEqNat_wf theory resources hleftSupport hrightSupport hleft hright
  intro answer after hanswer
  exact RecM.WF.pure fun _ => hanswer

namespace TryDefEqWhnfNat

/-- Package the concrete optional Nat bridge. -/
theorem ofResources
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    (theory : WhnfTheory trProj world uvars)
    (resources : FinalWhnfNatResources world support) :
    TryDefEqWhnfNat.WFAt .noAccel semantics trProj world support uvars := by
  intro Delta state left right leftV rightV hleftSupport hrightSupport
    hleft hright
  exact tryDefEqWhnfNat_wf theory resources hleftSupport hrightSupport
    hleft hright

end TryDefEqWhnfNat

/-- The Nat bridge followed by the exact remaining tail closes the complete
post-structural fallback. -/
theorem isDefEqWhnfAfterStructural_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {Delta : KVLCtx} {state : TcState .anon}
    {left right : KExpr .anon} {leftV rightV : VExpr}
    (hnat : TryDefEqWhnfNat.WFAt .noAccel semantics trProj world support
      uvars)
    (htail : IsDefEqWhnfAfterNat.WFAt .noAccel semantics trProj world
      support uvars)
    (hleftSupport : support left) (hrightSupport : support right)
    (hleft : TrKExprS world.venv uvars world.nameOf trProj Delta left leftV)
    (hright : TrKExprS world.venv uvars world.nameOf trProj Delta right
      rightV) :
    RecM.WF .noAccel semantics trProj world support uvars Delta state
      (isDefEqWhnfAfterStructural left right)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU uvars Delta.toCtx leftV rightV) := by
  unfold isDefEqWhnfAfterStructural
  apply RecM.WF.bind <|
    hnat hleftSupport hrightSupport hleft hright
  intro result afterNat hresult
  cases result with
  | none => exact htail hleftSupport hrightSupport hleft hright
  | some answer => exact RecM.WF.pure fun _ => hresult

namespace IsDefEqWhnfAfterStructural

/-- Package the concrete Nat prefix with the remaining fallback contract. -/
theorem ofNat
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    (theory : WhnfTheory trProj world uvars)
    (resources : FinalWhnfNatResources world support)
    (htail : IsDefEqWhnfAfterNat.WFAt .noAccel semantics trProj world
      support uvars) :
    IsDefEqWhnfAfterStructural.WFAt .noAccel semantics trProj world support
      uvars := by
  intro Delta state left right leftV rightV hleftSupport hrightSupport
    hleft hright
  exact isDefEqWhnfAfterStructural_wf
    (TryDefEqWhnfNat.ofResources theory resources) htail hleftSupport
    hrightSupport hleft hright

end IsDefEqWhnfAfterStructural

end RecM

end Ix.Tc
