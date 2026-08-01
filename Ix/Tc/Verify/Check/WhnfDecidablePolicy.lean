import Ix.Tc.Verify.Check.WhnfBitVecPolicy

/-!
# Operational inference-policy frame for decidability reduction

This module verifies native Nat decidability and Int-literal normalization.
It covers validation-only proposition inference, caught inference misses,
recursive type normalization, canonical proof-term interning, application
rebuilding, and every accelerator fallback.
-/

namespace Ix.Tc

namespace RecM


private theorem prims_preservesInferOnly (methods : Methods .anon) :
    ((prims : RecM .anon (Primitives .anon)).run methods).PreservesInferOnly := by
  unfold prims
  simp only [ReaderT.run_bind]
  apply TcM.PreservesInferOnly.bind TcM.PreservesInferOnly.get
  intro state
  exact TcM.PreservesInferOnly.pure state.prims

theorem internIntLit_preservesInferOnly
    {methods : Methods .anon} (value : _root_.Int) :
    ((internIntLit value).run methods).PreservesInferOnly := by
  unfold internIntLit
  refine bind_preservesInferOnly (prims_preservesInferOnly methods) ?_
  intro p
  by_cases hnegative : value < 0
  · simp only [hnegative, if_pos]
    refine bindIntern_preservesInferOnly
      (natExprFromValue ((-value).toNat - 1) : KExpr .anon) ?_
    intro natExpr
    refine bindIntern_preservesInferOnly (.mkConst p.intNegSucc #[]) ?_
    intro ctor
    exact intern_preservesInferOnly (.mkApp ctor natExpr)
  · simp only [hnegative]
    refine bindIntern_preservesInferOnly
      (natExprFromValue value.toNat : KExpr .anon) ?_
    intro natExpr
    refine bindIntern_preservesInferOnly (.mkConst p.intOfNat #[]) ?_
    intro ctor
    exact intern_preservesInferOnly (.mkApp ctor natExpr)

attribute [local irreducible] internIntLit

theorem tryNormalizeIntDecidable_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (addr : Address) (args : Array (KExpr .anon)) :
    ((tryNormalizeIntDecidable addr args).run methods).PreservesInferOnly := by
  unfold tryNormalizeIntDecidable
  by_cases hsmall : args.size < 2
  · simp only [hsmall, if_pos]
    exact TcM.PreservesInferOnly.pure none
  · simp only [hsmall, if_false, pure_bind]
    refine bind_preservesInferOnly
      (whnfRec_preservesInferOnly hmethods args[0]!) ?_
    intro leftNormalized
    refine bind_preservesInferOnly
      (whnfRec_preservesInferOnly hmethods args[1]!) ?_
    intro rightNormalized
    refine bind_preservesInferOnly (prims_preservesInferOnly methods) ?_
    intro p
    cases hleft : extractIntLit leftNormalized p with
    | none => exact TcM.PreservesInferOnly.pure none
    | some leftValue =>
        simp only []
        cases hright : extractIntLit rightNormalized p with
        | none => exact TcM.PreservesInferOnly.pure none
        | some rightValue =>
            simp only []
            refine bind_preservesInferOnly
              (internIntLit_preservesInferOnly leftValue) ?_
            intro left
            refine bind_preservesInferOnly
              (internIntLit_preservesInferOnly rightValue) ?_
            intro right
            cases hsame : left.addr == args[0]!.addr &&
                right.addr == args[1]!.addr with
            | true =>
                simp only [if_true]
                exact TcM.PreservesInferOnly.pure none
            | false =>
                simp only [Bool.false_eq_true, if_false]
                let headId := if addr == p.intDecEq.addr then p.intDecEq
                  else if addr == p.intDecLe.addr then p.intDecLe
                  else p.intDecLt
                refine bindIntern_preservesInferOnly (.mkConst headId #[]) ?_
                intro head
                refine bindIntern_preservesInferOnly (.mkApp head left) ?_
                intro withLeft
                refine bindIntern_preservesInferOnly (.mkApp withLeft right) ?_
                intro applied
                refine bind_preservesInferOnly
                  (finishAppResult_preservesInferOnly applied args 2) ?_
                intro finished
                exact TcM.PreservesInferOnly.pure (some finished)

attribute [local irreducible] tryNormalizeIntDecidable

private theorem tryInferDecidableProp_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (source : KExpr .anon) :
    ((inferDecidableProp source).run methods).PreservesInferOnly := by
  unfold inferDecidableProp
  refine bind_preservesInferOnly
    (x := (read : RecM .anon (Methods .anon)))
    (TcM.PreservesInferOnly.pure methods) ?_
  intro callbackMethods
  refine bind_preservesInferOnly
    (tryOptional_preservesInferOnly
      (liftTcM_preservesInferOnly
        (TcM.PreservesInferOnly.withInferOnly
          (callbackMethods.infer source)))) ?_
  intro inferred
  cases inferred with
  | none => exact TcM.PreservesInferOnly.pure none
  | some sourceType =>
      simp only []
      refine bind_preservesInferOnly
        (whnfRec_preservesInferOnly hmethods sourceType) ?_
      intro normalizedType
      exact TcM.PreservesInferOnly.pure normalizedType.collectSpine.2[0]?

attribute [local irreducible] inferDecidableProp

private theorem buildNatDecidableTrue_preservesInferOnly
    {methods : Methods .anon} (p : Primitives .anon)
    (prop : KExpr .anon) (args : Array (KExpr .anon))
    (proofTrueFn : KId .anon) (u1 : KUniv .anon) :
    ((buildNatDecidableTrue p prop args proofTrueFn u1).run
      methods).PreservesInferOnly := by
  unfold buildNatDecidableTrue
  refine bindIntern_preservesInferOnly (.mkConst p.eqRefl #[u1]) ?_
  intro eqRefl
  refine bindIntern_preservesInferOnly (.mkConst p.boolType #[]) ?_
  intro boolTy
  refine bindIntern_preservesInferOnly (.mkConst p.boolTrue #[]) ?_
  intro boolTrue
  refine bindIntern_preservesInferOnly (.mkApp eqRefl boolTy) ?_
  intro reflHead
  refine bindIntern_preservesInferOnly (.mkApp reflHead boolTrue) ?_
  intro reflProof
  refine bindIntern_preservesInferOnly (.mkConst proofTrueFn #[]) ?_
  intro proofConst
  refine bindIntern_preservesInferOnly (.mkApp proofConst args[0]!) ?_
  intro proofLeft
  refine bindIntern_preservesInferOnly (.mkApp proofLeft args[1]!) ?_
  intro proofArgs
  refine bindIntern_preservesInferOnly (.mkApp proofArgs reflProof) ?_
  intro proof
  refine bindIntern_preservesInferOnly (.mkConst p.decidableIsTrue #[]) ?_
  intro isTrue
  refine bindIntern_preservesInferOnly (.mkApp isTrue prop) ?_
  intro result
  exact intern_preservesInferOnly (.mkApp result proof)

private theorem buildNatDecidableFalse_preservesInferOnly
    {methods : Methods .anon} (p : Primitives .anon)
    (prop : KExpr .anon) (args : Array (KExpr .anon))
    (proofFalseFn : KId .anon) (u1 : KUniv .anon) :
    ((buildNatDecidableFalse p prop args proofFalseFn u1).run
      methods).PreservesInferOnly := by
  unfold buildNatDecidableFalse
  refine bindIntern_preservesInferOnly (.mkConst p.eqRefl #[u1]) ?_
  intro eqRefl
  refine bindIntern_preservesInferOnly (.mkConst p.boolType #[]) ?_
  intro boolTy
  refine bindIntern_preservesInferOnly (.mkConst p.boolFalse #[]) ?_
  intro boolFalse
  refine bindIntern_preservesInferOnly (.mkApp eqRefl boolTy) ?_
  intro reflHead
  refine bindIntern_preservesInferOnly (.mkApp reflHead boolFalse) ?_
  intro reflProof
  refine bindIntern_preservesInferOnly (.mkConst proofFalseFn #[]) ?_
  intro proofConst
  refine bindIntern_preservesInferOnly (.mkApp proofConst args[0]!) ?_
  intro proofLeft
  refine bindIntern_preservesInferOnly (.mkApp proofLeft args[1]!) ?_
  intro proofArgs
  refine bindIntern_preservesInferOnly (.mkApp proofArgs reflProof) ?_
  intro proof
  refine bindIntern_preservesInferOnly (.mkConst p.decidableIsFalse #[]) ?_
  intro isFalse
  refine bindIntern_preservesInferOnly (.mkApp isFalse prop) ?_
  intro result
  exact intern_preservesInferOnly (.mkApp result proof)

attribute [local irreducible]
  buildNatDecidableTrue buildNatDecidableFalse

private theorem finishNatDecidable_preservesInferOnly
    {methods : Methods .anon} (p : Primitives .anon)
    (prop : KExpr .anon) (args : Array (KExpr .anon))
    (bResult isDecEq : Bool) (proofTrueFn proofFalseFn : KId .anon)
    (u1 : KUniv .anon) :
    ((do
      let resultExpr ← if bResult then do
          buildNatDecidableTrue p prop args proofTrueFn u1
        else if isDecEq then do
          buildNatDecidableFalse p prop args proofFalseFn u1
        else
          return none
      return some (← finishAppResult resultExpr args 2) :
      RecM .anon (Option (KExpr .anon))).run methods).PreservesInferOnly := by
  cases hb : bResult with
  | true =>
      simp only [if_true]
      refine bind_preservesInferOnly
        (buildNatDecidableTrue_preservesInferOnly p prop args proofTrueFn u1) ?_
      intro resultExpr
      refine bind_preservesInferOnly
        (finishAppResult_preservesInferOnly resultExpr args 2) ?_
      intro finished
      exact TcM.PreservesInferOnly.pure (some finished)
  | false =>
      simp only [Bool.false_eq_true, if_false]
      cases heq : isDecEq with
      | true =>
          simp only [if_true]
          refine bind_preservesInferOnly
            (buildNatDecidableFalse_preservesInferOnly p prop args
              proofFalseFn u1) ?_
          intro resultExpr
          refine bind_preservesInferOnly
            (finishAppResult_preservesInferOnly resultExpr args 2) ?_
          intro finished
          exact TcM.PreservesInferOnly.pure (some finished)
      | false =>
          simp only [Bool.false_eq_true, if_false]
          exact TcM.PreservesInferOnly.pure none

theorem tryReduceDecidable_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (source : KExpr .anon) :
    ((tryReduceDecidable source).run methods).PreservesInferOnly := by
  unfold tryReduceDecidable
  refine bindTcM_preservesInferOnly TcM.PreservesInferOnly.get ?_
  intro state
  cases hnoAccel : state.noAccel with
  | true =>
      simp only [if_true]
      exact TcM.PreservesInferOnly.pure none
  | false =>
      simp only [Bool.false_eq_true, if_false, pure_bind]
      rcases hspine : source.collectSpine with ⟨head, args⟩
      cases head with
      | const id levels info =>
          simp only []
          refine bind_preservesInferOnly (prims_preservesInferOnly methods) ?_
          intro p
          let isDecLe := id.addr == p.natDecLe.addr
          let isDecEq := id.addr == p.natDecEq.addr
          let isDecLt := id.addr == p.natDecLt.addr
          cases hint : id.addr == p.intDecLe.addr ||
              id.addr == p.intDecEq.addr || id.addr == p.intDecLt.addr with
          | true =>
              simp only [if_true]
              refine bind_preservesInferOnly
                (tryNormalizeIntDecidable_preservesInferOnly hmethods id.addr
                  args) ?_
              intro result
              exact TcM.PreservesInferOnly.pure result
          | false =>
              simp only [Bool.false_eq_true, if_false]
              cases hknown : !isDecLe && !isDecEq && !isDecLt with
              | true =>
                  simp only [if_true]
                  exact TcM.PreservesInferOnly.pure none
              | false =>
                  simp only [Bool.false_eq_true, if_false]
                  by_cases hsmall : args.size < 2
                  · simp only [hsmall, if_pos]
                    exact TcM.PreservesInferOnly.pure none
                  · simp only [hsmall, if_false]
                    focus
                      refine bind_preservesInferOnly
                        (whnfRec_preservesInferOnly hmethods args[0]!) ?_
                      intro leftNormalized
                      refine bind_preservesInferOnly
                        (whnfRec_preservesInferOnly hmethods args[1]!) ?_
                      intro rightNormalized
                      cases hleft : extractNatValue leftNormalized p with
                      | none => exact TcM.PreservesInferOnly.pure none
                      | some leftValue =>
                          simp only []
                          cases hright : extractNatValue rightNormalized p with
                          | none => exact TcM.PreservesInferOnly.pure none
                          | some rightValue =>
                              simp only []
                              cases hlt : id.addr == p.natDecLt.addr with
                              | true =>
                                  simp only [if_true]
                                  refine bindIntern_preservesInferOnly
                                    (natExprFromValue (leftValue + 1) :
                                      KExpr .anon) ?_
                                  intro succLeft
                                  refine bindIntern_preservesInferOnly
                                    (.mkConst p.natDecLe #[]) ?_
                                  intro decLe
                                  refine bindIntern_preservesInferOnly
                                    (.mkApp decLe succLeft) ?_
                                  intro appliedLeft
                                  refine bindIntern_preservesInferOnly
                                    (.mkApp appliedLeft args[1]!) ?_
                                  intro result
                                  refine bind_preservesInferOnly
                                    (finishAppResult_preservesInferOnly result
                                      args 2) ?_
                                  intro finished
                                  exact TcM.PreservesInferOnly.pure
                                    (some finished)
                              | false =>
                                  simp only [Bool.false_eq_true, if_false]
                                  refine bind_preservesInferOnly
                                    (tryInferDecidableProp_preservesInferOnly
                                      hmethods source) ?_
                                  intro propResult
                                  cases propResult with
                                  | none =>
                                      exact TcM.PreservesInferOnly.pure none
                                  | some prop =>
                                      simp only []
                                      let u1 : KUniv .anon :=
                                        .mkSucc .mkZero
                                      cases hle :
                                          id.addr == p.natDecLe.addr with
                                      | true =>
                                          simp only [if_true]
                                          exact
                                            finishNatDecidable_preservesInferOnly
                                              p prop args
                                              (leftValue.ble rightValue)
                                              isDecEq
                                              p.natLeOfBleEqTrue
                                              p.natNotLeOfNotBleEqTrue u1
                                      | false =>
                                          simp only [Bool.false_eq_true,
                                            if_false]
                                          exact
                                            finishNatDecidable_preservesInferOnly
                                              p prop args
                                              (leftValue == rightValue)
                                              isDecEq
                                              p.natEqOfBeqEqTrue
                                              p.natNeOfBeqEqFalse u1
      | var | fvar | sort | app | lam | all | letE | prj | nat | str =>
          exact TcM.PreservesInferOnly.pure none

end RecM

end Ix.Tc
