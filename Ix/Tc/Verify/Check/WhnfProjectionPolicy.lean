import Ix.Tc.Verify.Check.WhnfBasicHelperPolicy

/-!
# Operational policy for WHNF projection reduction

This module proves inference-policy preservation for String-constructor
expansion, the accelerated `Fin.val`/`Decidable.rec` rewrite, constructor
field selection, and the complete ordinary projection pipeline.  Every
intern operation, lazy constructor lookup, recursive WHNF callback, miss,
and partial error is covered.
-/

namespace Ix.Tc

namespace RecM

set_option maxHeartbeats 800000

private theorem prims_preservesInferOnly (methods : Methods .anon) :
    ((prims : RecM .anon (Primitives .anon)).run methods).PreservesInferOnly := by
  unfold prims
  simp only [ReaderT.run_bind]
  apply TcM.PreservesInferOnly.bind TcM.PreservesInferOnly.get
  intro state
  exact TcM.PreservesInferOnly.pure state.prims

theorem strLitListToConstructor_preservesInferOnly
    {methods : Methods .anon} (charOfNat cons : KExpr .anon)
    (chars : List Char) (list : KExpr .anon) :
    TcM.PreservesInferOnly
      ((strLitListToConstructor charOfNat cons chars list).run methods) := by
  induction chars generalizing list with
  | nil =>
      unfold strLitListToConstructor
      exact TcM.PreservesInferOnly.pure list
  | cons char chars ih =>
      unfold strLitListToConstructor
      apply bindIntern_preservesInferOnly
      intro natLiteral
      apply bindIntern_preservesInferOnly
      intro charValue
      apply bindIntern_preservesInferOnly
      intro partialApp
      apply bindIntern_preservesInferOnly
      intro next
      exact ih next

theorem strLitToConstructorWithPrimitives_preservesInferOnly
    {methods : Methods .anon} (p : Primitives .anon) (value : String) :
    TcM.PreservesInferOnly
      ((strLitToConstructorWithPrimitives p value).run methods) := by
  rw [strLitToConstructorWithPrimitives_eq]
  refine bindIntern_preservesInferOnly (stringCharConst p) ?_
  intro charType
  refine bindIntern_preservesInferOnly (stringCharOfNat p) ?_
  intro charOfNat
  refine bindIntern_preservesInferOnly (stringMkConst p) ?_
  intro stringOfList
  refine bindIntern_preservesInferOnly (stringListNilZero p) ?_
  intro listNil
  refine bindIntern_preservesInferOnly
    (KExpr.mkApp listNil charType) ?_
  intro nil
  refine bindIntern_preservesInferOnly (stringListConsZero p) ?_
  intro listCons
  refine bindIntern_preservesInferOnly
    (KExpr.mkApp listCons charType) ?_
  intro cons
  apply bind_preservesInferOnly
    (strLitListToConstructor_preservesInferOnly charOfNat cons
      value.toList.reverse nil)
  intro list
  simp only [ReaderT.run_monadLift]
  exact intern_preservesInferOnly _

attribute [local irreducible] strLitToConstructor
  strLitToConstructorWithPrimitives

theorem strLitToConstructor_preservesInferOnly
    {methods : Methods .anon} (value : String) :
    ((strLitToConstructor value).run methods).PreservesInferOnly := by
  rw [strLitToConstructor_eq]
  intro before
  have htail :=
    strLitToConstructorWithPrimitives_preservesInferOnly
      (methods := methods) before.prims value before
  unfold prims
  simpa only [ReaderT.run_bind, EStateM.bind, get] using htail

theorem projectDecidableFinValMinor_preservesInferOnly
    {methods : Methods .anon} (id : KId .anon) (field : UInt64)
    (minor : KExpr .anon) :
    TcM.PreservesInferOnly
      ((projectDecidableFinValMinor id field minor).run methods) := by
  unfold projectDecidableFinValMinor
  cases minor with
  | lam name bi domain body info =>
      simp only [ReaderT.run_bind, ReaderT.run_monadLift]
      apply TcM.PreservesInferOnly.bind
        (TcM.PreservesInferOnly.runIntern
          (internExprM (KExpr.mkPrj id field body)))
      intro projection
      apply TcM.PreservesInferOnly.bind
        (TcM.PreservesInferOnly.runIntern
          (internExprM (KExpr.mkLam name bi domain projection)))
      intro result
      exact TcM.PreservesInferOnly.pure (some result)
  | var | fvar | sort | const | app | all | letE | prj | nat | str =>
      exact TcM.PreservesInferOnly.pure none

attribute [local irreducible] projectDecidableFinValMinor

theorem tryReduceFinValDecidableRec_preservesInferOnly
    {methods : Methods .anon} (id : KId .anon) (field : UInt64)
    (head : KExpr .anon) (args : Array (KExpr .anon)) :
    TcM.PreservesInferOnly
      ((tryReduceFinValDecidableRec id field head args).run methods) := by
  rw [tryReduceFinValDecidableRec_equation]
  refine bindTcM_preservesInferOnly TcM.PreservesInferOnly.get ?_
  intro state
  cases hnoAccel : state.noAccel with
  | true =>
      simp only [if_true]
      exact TcM.PreservesInferOnly.pure none
  | false =>
      simp only [Bool.false_eq_true, if_false, pure_bind]
      refine bind_preservesInferOnly
        (x := prims) (prims_preservesInferOnly methods) ?_
      intro p
      cases hfin : id.addr != p.fin.addr || field != 0 with
      | true =>
          simp only [if_true]
          exact TcM.PreservesInferOnly.pure none
      | false =>
          simp only [Bool.false_eq_true, if_false]
          cases head with
          | const recId recLevels recInfo =>
              cases hrec :
                  recId.addr != p.decidableRec.addr || args.size < 5 with
              | true =>
                  simp only [hrec, if_true]
                  exact TcM.PreservesInferOnly.pure none
              | false =>
                  simp only [hrec, Bool.false_eq_true, if_false]
                  cases args[1]! with
                  | lam motiveName motiveBi motiveDomain motiveBody
                      motiveInfo =>
                      refine bind_preservesInferOnly
                        (x := projectDecidableFinValMinor id field args[2]!)
                        (projectDecidableFinValMinor_preservesInferOnly
                          id field args[2]!) ?_
                      intro falseMinor
                      cases falseMinor with
                      | none => exact TcM.PreservesInferOnly.pure none
                      | some falseMinor =>
                          refine bind_preservesInferOnly
                            (x := projectDecidableFinValMinor id field args[3]!)
                            (projectDecidableFinValMinor_preservesInferOnly
                              id field args[3]!) ?_
                          intro trueMinor
                          cases trueMinor with
                          | none => exact TcM.PreservesInferOnly.pure none
                          | some trueMinor =>
                              refine bindIntern_preservesInferOnly
                                (KExpr.mkConst p.nat #[]) ?_
                              intro natType
                              refine bindIntern_preservesInferOnly
                                (KExpr.mkLam motiveName motiveBi
                                  motiveDomain natType) ?_
                              intro motive
                              refine bindIntern_preservesInferOnly
                                (KExpr.mkConst recId recLevels) ?_
                              intro result
                              refine bindIntern_preservesInferOnly
                                (KExpr.mkApp result args[0]!) ?_
                              intro result
                              refine bindIntern_preservesInferOnly
                                (KExpr.mkApp result motive) ?_
                              intro result
                              refine bindIntern_preservesInferOnly
                                (KExpr.mkApp result falseMinor) ?_
                              intro result
                              refine bindIntern_preservesInferOnly
                                (KExpr.mkApp result trueMinor) ?_
                              intro result
                              refine bindIntern_preservesInferOnly
                                (KExpr.mkApp result args[4]!) ?_
                              intro base
                              rw [projectionDefinitionFinish_eq]
                              refine bind_preservesInferOnly
                                (x := finishAppResult base args 5)
                                (finishAppResult_preservesInferOnly
                                  base args 5) ?_
                              intro result
                              exact TcM.PreservesInferOnly.pure (some result)
                  | var | fvar | sort | const | app | all | letE | prj |
                        nat | str =>
                      exact TcM.PreservesInferOnly.pure none
          | var | fvar | sort | app | lam | all | letE | prj | nat | str =>
              exact TcM.PreservesInferOnly.pure none

attribute [local irreducible] tryReduceFinValDecidableRec

theorem tryProjReduceTail_preservesInferOnly
    {methods : Methods .anon} (id : KId .anon) (field : UInt64)
    (value : KExpr .anon) :
    ((tryProjReduceTail id field value).run methods).PreservesInferOnly := by
  unfold tryProjReduceTail
  rcases hspine : value.collectSpine with ⟨head, args⟩
  refine bind_preservesInferOnly
    (x := tryReduceFinValDecidableRec id field head args)
    (tryReduceFinValDecidableRec_preservesInferOnly id field head args) ?_
  intro special
  cases special with
  | some result => exact TcM.PreservesInferOnly.pure (some result)
  | none =>
      cases head with
      | const ctorId levels info =>
          simp only [pure_bind]
          refine bindTcM_preservesInferOnly
            (TcM.PreservesInferOnly.tryGetConst ctorId) ?_
          intro found
          cases found with
          | none => exact TcM.PreservesInferOnly.pure none
          | some declaration =>
              cases declaration
              case ctor name levelParams cidx fields lvls params ind ty
                  leanAll =>
                exact TcM.PreservesInferOnly.pure
                  args[params.toNat + field.toNat]?
              all_goals exact TcM.PreservesInferOnly.pure none
      | var | fvar | sort | app | lam | all | letE | prj | nat | str =>
          exact TcM.PreservesInferOnly.pure none

theorem tryProjPrepare_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (value : KExpr .anon) :
    ((tryProjPrepare value).run methods).PreservesInferOnly := by
  unfold tryProjPrepare
  cases value with
  | str value blob info =>
      refine bind_preservesInferOnly
        (x := strLitToConstructor value)
        (strLitToConstructor_preservesInferOnly value) ?_
      intro expanded
      exact whnfRec_preservesInferOnly hmethods expanded
  | var idx name info => exact TcM.PreservesInferOnly.pure _
  | fvar id name info => exact TcM.PreservesInferOnly.pure _
  | sort level info => exact TcM.PreservesInferOnly.pure _
  | const id levels info => exact TcM.PreservesInferOnly.pure _
  | app fn arg info => exact TcM.PreservesInferOnly.pure _
  | lam name bi domain body info => exact TcM.PreservesInferOnly.pure _
  | all name bi domain body info => exact TcM.PreservesInferOnly.pure _
  | letE name type value body nondep info =>
      exact TcM.PreservesInferOnly.pure _
  | prj id field value info => exact TcM.PreservesInferOnly.pure _
  | nat value blob info => exact TcM.PreservesInferOnly.pure _

theorem tryProjReduce_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (id : KId .anon) (field : UInt64) (value : KExpr .anon) :
    ((tryProjReduce id field value).run methods).PreservesInferOnly := by
  unfold tryProjReduce
  refine bind_preservesInferOnly
    (x := tryProjPrepare value)
    (tryProjPrepare_preservesInferOnly hmethods value) ?_
  intro prepared
  exact tryProjReduceTail_preservesInferOnly id field prepared

end RecM

end Ix.Tc
