import Ix.Tc.Verify.Check.WhnfNatPolicy

/-!
# Operational inference-policy frame for BitVec reduction

This module verifies the bounded Nat evaluator used by BitVec predicates and
the complete `BitVec.toNat`, `BitVec.ult`, and `Decidable.decide` accelerator
pipeline.  All recursive WHNF calls, fallback paths, and rebuilt applications
restore the caller's inference policy.
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

theorem mkNatSucc_preservesInferOnly
    {methods : Methods .anon} (pred : KExpr .anon) :
    ((mkNatSucc pred).run methods).PreservesInferOnly := by
  unfold mkNatSucc
  refine bind_preservesInferOnly (prims_preservesInferOnly methods) ?_
  intro p
  exact TcM.PreservesInferOnly.pure _

theorem boolLitValue_preservesInferOnly
    {methods : Methods .anon} (source : KExpr .anon) :
    ((boolLitValue source).run methods).PreservesInferOnly := by
  unfold boolLitValue
  refine bind_preservesInferOnly (prims_preservesInferOnly methods) ?_
  intro p
  cases source with
  | const id levels info =>
      simp only []
      cases htrue : id.addr == p.boolTrue.addr with
      | true =>
          simp only [if_true]
          exact TcM.PreservesInferOnly.pure (some true)
      | false =>
          simp only [Bool.false_eq_true, if_false]
          split <;> exact TcM.PreservesInferOnly.pure _
  | var | fvar | sort | app | lam | all | letE | prj | nat | str =>
      exact TcM.PreservesInferOnly.pure none

theorem isNatStuckRecursorAddr_preservesInferOnly
    {methods : Methods .anon} (addr : Address) :
    ((isNatStuckRecursorAddr addr).run methods).PreservesInferOnly := by
  unfold isNatStuckRecursorAddr
  refine bind_preservesInferOnly (prims_preservesInferOnly methods) ?_
  intro p
  exact TcM.PreservesInferOnly.pure _

theorem isStuckNatPredicateProbe_preservesInferOnly
    {methods : Methods .anon} (source : KExpr .anon) :
    ((isStuckNatPredicateProbe source).run methods).PreservesInferOnly := by
  unfold isStuckNatPredicateProbe
  rcases hspine : source.collectSpine with ⟨head, args⟩
  cases head with
  | const id levels info =>
      refine bind_preservesInferOnly
        (isNatBinPredAddr_preservesInferOnly id.addr) ?_
      intro isPredicate
      refine bind_preservesInferOnly
        (isNatStuckRecursorAddr_preservesInferOnly id.addr) ?_
      intro isStuck
      exact TcM.PreservesInferOnly.pure (isPredicate || isStuck)
  | prj id field value info =>
      simp only []
      refine bind_preservesInferOnly (prims_preservesInferOnly methods) ?_
      intro p
      split
      · exact TcM.PreservesInferOnly.pure true
      · rcases hvalueSpine : value.collectSpine with ⟨valueHead, valueArgs⟩
        cases valueHead with
        | const valueId levels valueInfo =>
            exact isNatStuckRecursorAddr_preservesInferOnly valueId.addr
        | var | fvar | sort | app | lam | all | letE | prj | nat | str =>
            exact TcM.PreservesInferOnly.pure false
  | var | fvar | sort | app | lam | all | letE | nat | str =>
      simp only []
      exact TcM.PreservesInferOnly.pure false

theorem bitvecOfNatArgs_preservesInferOnly
    {methods : Methods .anon} (source : KExpr .anon) :
    ((bitvecOfNatArgs source).run methods).PreservesInferOnly := by
  unfold bitvecOfNatArgs
  refine bind_preservesInferOnly (prims_preservesInferOnly methods) ?_
  intro p
  rcases hspine : source.collectSpine with ⟨head, args⟩
  cases head with
  | const id levels info =>
      simp only []
      split
      · exact TcM.PreservesInferOnly.pure _
      · split
        · exact TcM.PreservesInferOnly.pure none
        · rcases htypeSpine : args[0]!.collectSpine with
            ⟨typeHead, typeArgs⟩
          cases typeHead with
          | const typeId typeLevels typeInfo =>
              simp only [pure_bind]
              split <;> exact TcM.PreservesInferOnly.pure _
          | var | fvar | sort | app | lam | all | letE | prj | nat | str =>
              exact TcM.PreservesInferOnly.pure none
  | var | fvar | sort | app | lam | all | letE | prj | nat | str =>
      simp only []
      exact TcM.PreservesInferOnly.pure none

private theorem tryEvalNatValueForPredFallback_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (hrec : ∀ source,
      ((tryEvalNatValueForPredFuel fuel source).run methods).PreservesInferOnly)
    (p : Primitives .anon) (source : KExpr .anon) :
    ((do
      let normalized ← whnfRec source
      if let some value := extractNatValue normalized p then
        return some value
      if normalized.addr == source.addr then
        return none
      tryEvalNatValueForPredFuel fuel normalized).run methods).PreservesInferOnly := by
  refine bind_preservesInferOnly
    (whnfRec_preservesInferOnly hmethods source) ?_
  intro normalized
  cases hvalue : extractNatValue normalized p with
  | some value =>
      simp only []
      exact TcM.PreservesInferOnly.pure (some value)
  | none =>
      simp only [pure_bind]
      split
      · exact TcM.PreservesInferOnly.pure none
      · exact hrec normalized

theorem tryEvalNatValueForPredFuel_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly) :
    ∀ fuel source,
      ((tryEvalNatValueForPredFuel fuel source).run methods).PreservesInferOnly
  | 0, source => by
      rw [tryEvalNatValueForPredFuel]
      exact TcM.PreservesInferOnly.pure none
  | fuel + 1, source => by
      rw [tryEvalNatValueForPredFuel]
      refine bind_preservesInferOnly (prims_preservesInferOnly methods) ?_
      intro p
      cases hliteral : extractNatLit source p with
      | some value =>
          simp only []
          exact TcM.PreservesInferOnly.pure (some value)
      | none =>
          simp only [pure_bind]
          refine bind_preservesInferOnly
            (isStuckNatPredicateProbe_preservesInferOnly source) ?_
          intro isStuck
          cases hstuck : isStuck with
          | true =>
              simp only [if_true]
              exact TcM.PreservesInferOnly.pure none
          | false =>
              simp only [Bool.false_eq_true, if_false]
              rcases hspine : source.collectSpine with ⟨head, args⟩
              cases head with
              | const id levels info =>
                  simp only []
                  cases hsucc :
                      id.addr == p.natSucc.addr && args.size == 1 with
                  | true =>
                      simp only [if_true]
                      refine bind_preservesInferOnly
                        (tryEvalNatValueForPredFuel_preservesInferOnly hmethods
                          fuel args[0]!) ?_
                      intro predResult
                      cases predResult with
                      | none => exact TcM.PreservesInferOnly.pure none
                      | some pred =>
                          exact TcM.PreservesInferOnly.pure (some (pred + 1))
                  | false =>
                      simp only [Bool.false_eq_true, if_false]
                      cases hpred :
                          id.addr == p.natPred.addr && args.size == 1 with
                      | true =>
                          simp only [if_true]
                          refine bind_preservesInferOnly
                            (tryEvalNatValueForPredFuel_preservesInferOnly
                              hmethods fuel args[0]!) ?_
                          intro predResult
                          cases predResult with
                          | none => exact TcM.PreservesInferOnly.pure none
                          | some value =>
                              exact TcM.PreservesInferOnly.pure
                                (some (value - 1))
                      | false =>
                          simp only [Bool.false_eq_true, if_false]
                          refine bind_preservesInferOnly
                            (isNatBinArithAddr_preservesInferOnly id.addr) ?_
                          intro isArith
                          cases hbinary : isArith && args.size == 2 with
                          | true =>
                              simp only [if_true]
                              refine bind_preservesInferOnly
                                (tryEvalNatValueForPredFuel_preservesInferOnly
                                  hmethods fuel args[0]!) ?_
                              intro leftResult
                              cases leftResult with
                              | none =>
                                  exact TcM.PreservesInferOnly.pure none
                              | some left =>
                                  simp only []
                                  refine bind_preservesInferOnly
                                    (tryEvalNatValueForPredFuel_preservesInferOnly
                                      hmethods fuel args[1]!) ?_
                                  intro rightResult
                                  cases rightResult with
                                  | none =>
                                      exact TcM.PreservesInferOnly.pure none
                                  | some right =>
                                      exact TcM.PreservesInferOnly.pure
                                        (computeNatBin id.addr
                                          PrimAddrs.canonical left right)
                          | false =>
                              simp only [Bool.false_eq_true, if_false]
                              exact
                                tryEvalNatValueForPredFallback_preservesInferOnly
                                  hmethods
                                  (tryEvalNatValueForPredFuel_preservesInferOnly
                                    hmethods fuel)
                                  p source
              | app f a info | letE _ _ _ _ _ info | prj _ _ _ info =>
                  simp only []
                  exact tryEvalNatValueForPredFallback_preservesInferOnly
                    hmethods
                    (tryEvalNatValueForPredFuel_preservesInferOnly hmethods
                      fuel)
                    p source
              | var | fvar | sort | lam | all | nat | str =>
                  exact TcM.PreservesInferOnly.pure none

theorem tryEvalNatValueForPred_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (source : KExpr .anon) (depth : Nat := 0) :
    ((tryEvalNatValueForPred source depth).run methods).PreservesInferOnly := by
  unfold tryEvalNatValueForPred
  exact tryEvalNatValueForPredFuel_preservesInferOnly hmethods _ source

theorem tryReduceBitvecToNat_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (value : KExpr .anon) :
    ((tryReduceBitvecToNat value).run methods).PreservesInferOnly := by
  unfold tryReduceBitvecToNat
  refine bind_preservesInferOnly
    (bitvecOfNatArgs_preservesInferOnly value) ?_
  intro parts
  cases parts with
  | none => exact TcM.PreservesInferOnly.pure none
  | some pair =>
      rcases pair with ⟨width, natExpr⟩
      simp only []
      refine bind_preservesInferOnly
        (whnfRec_preservesInferOnly hmethods natExpr) ?_
      intro normalized
      refine bind_preservesInferOnly (prims_preservesInferOnly methods) ?_
      intro p
      cases hvalue : extractNatValue normalized p with
      | none => exact TcM.PreservesInferOnly.pure none
      | some natValue =>
          simp only []
          cases hzero : natValue == 0 with
          | true =>
              simp only [if_true]
              exact TcM.PreservesInferOnly.pure _
          | false =>
              simp only [Bool.false_eq_true, if_false, pure_bind]
              refine bind_preservesInferOnly
                (tryEvalNatValueForPred_preservesInferOnly hmethods width) ?_
              intro widthResult
              cases widthResult with
              | none => exact TcM.PreservesInferOnly.pure none
              | some widthValue =>
                  by_cases hlarge : widthValue > (1 <<< 24)
                  · simp only [hlarge, if_pos]
                    exact TcM.PreservesInferOnly.pure none
                  · simp only [hlarge]
                    exact TcM.PreservesInferOnly.pure _

theorem bitvecToNatExpr_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (width value : KExpr .anon) :
    ((bitvecToNatExpr width value).run methods).PreservesInferOnly := by
  unfold bitvecToNatExpr
  refine bind_preservesInferOnly
    (tryReduceBitvecToNat_preservesInferOnly hmethods value) ?_
  intro direct
  cases direct with
  | some result => exact TcM.PreservesInferOnly.pure result
  | none =>
      simp only [pure_bind]
      refine bind_preservesInferOnly (prims_preservesInferOnly methods) ?_
      intro p
      refine bindIntern_preservesInferOnly (.mkConst p.bitVecToNat #[]) ?_
      intro head
      refine bindIntern_preservesInferOnly (.mkApp head width) ?_
      intro withWidth
      exact intern_preservesInferOnly (.mkApp withWidth value)

private theorem tryReduceBitvecUltFallback_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (p : Primitives .anon) (leftNat rightNat : KExpr .anon) :
    ((do
      let leftSucc ← mkNatSucc leftNat
      let ble ← TcM.intern (.mkConst p.natBle #[])
      let cmpLeft ← TcM.intern (.mkApp ble leftSucc)
      let cmp ← TcM.intern (.mkApp cmpLeft rightNat)
      let result ← whnfRec cmp
      if (← boolLitValue result).isSome then
        return some result
      return none).run methods).PreservesInferOnly := by
  refine bind_preservesInferOnly
    (mkNatSucc_preservesInferOnly leftNat) ?_
  intro leftSucc
  refine bindIntern_preservesInferOnly (.mkConst p.natBle #[]) ?_
  intro ble
  refine bindIntern_preservesInferOnly (.mkApp ble leftSucc) ?_
  intro cmpLeft
  refine bindIntern_preservesInferOnly (.mkApp cmpLeft rightNat) ?_
  intro cmp
  refine bind_preservesInferOnly
    (whnfRec_preservesInferOnly hmethods cmp) ?_
  intro result
  refine bind_preservesInferOnly
    (boolLitValue_preservesInferOnly result) ?_
  intro literal
  split <;> exact TcM.PreservesInferOnly.pure _

theorem tryReduceBitvecUlt_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (width left right : KExpr .anon) :
    ((tryReduceBitvecUlt width left right).run methods).PreservesInferOnly := by
  unfold tryReduceBitvecUlt
  refine bind_preservesInferOnly (prims_preservesInferOnly methods) ?_
  intro p
  refine bind_preservesInferOnly
    (bitvecToNatExpr_preservesInferOnly hmethods width left) ?_
  intro leftNat
  refine bind_preservesInferOnly
    (bitvecToNatExpr_preservesInferOnly hmethods width right) ?_
  intro rightNat
  refine bind_preservesInferOnly
    (whnfRec_preservesInferOnly hmethods rightNat) ?_
  intro rightNormalized
  cases hright : extractNatValue rightNormalized p with
  | none =>
      simp only [pure_bind]
      exact tryReduceBitvecUltFallback_preservesInferOnly hmethods p leftNat
        rightNat
  | some rightValue =>
      simp only []
      cases hzero : rightValue == 0 with
      | true =>
          simp only [if_true]
          refine bindIntern_preservesInferOnly
            (.mkConst p.boolFalse #[]) ?_
          intro result
          exact TcM.PreservesInferOnly.pure (some result)
      | false =>
          simp only [Bool.false_eq_true, if_false, pure_bind]
          refine bind_preservesInferOnly
            (whnfRec_preservesInferOnly hmethods leftNat) ?_
          intro leftNormalized
          cases hleft : extractNatValue leftNormalized p with
          | some leftValue =>
              simp only []
              refine bindIntern_preservesInferOnly
                (.mkConst (if leftValue < rightValue then p.boolTrue
                  else p.boolFalse) #[]) ?_
              intro result
              exact TcM.PreservesInferOnly.pure (some result)
          | none =>
              simp only []
              exact tryReduceBitvecUltFallback_preservesInferOnly hmethods p
                leftNat rightNat

theorem tryReduceBitvecLtProp_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (prop : KExpr .anon) :
    ((tryReduceBitvecLtProp prop).run methods).PreservesInferOnly := by
  unfold tryReduceBitvecLtProp
  refine bind_preservesInferOnly (prims_preservesInferOnly methods) ?_
  intro p
  rcases hspine : prop.collectSpine with ⟨head, args⟩
  cases head with
  | const id levels info =>
      simp only []
      split
      · exact TcM.PreservesInferOnly.pure none
      · simp only [pure_bind]
        rcases htypeSpine : args[0]!.collectSpine with
          ⟨typeHead, typeArgs⟩
        cases typeHead with
        | const typeId typeLevels typeInfo =>
            simp only []
            split
            · exact TcM.PreservesInferOnly.pure none
            · exact tryReduceBitvecUlt_preservesInferOnly hmethods typeArgs[0]!
                args[2]! args[3]!
        | var | fvar | sort | app | lam | all | letE | prj | nat | str =>
            exact TcM.PreservesInferOnly.pure none
  | var | fvar | sort | app | lam | all | letE | prj | nat | str =>
      simp only []
      exact TcM.PreservesInferOnly.pure none

theorem tryReduceBitvec_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (source : KExpr .anon) :
    ((tryReduceBitvec source).run methods).PreservesInferOnly := by
  unfold tryReduceBitvec
  refine bindTcM_preservesInferOnly TcM.PreservesInferOnly.get ?_
  intro state
  cases hnoAccel : state.noAccel with
  | true =>
      simp only [if_true]
      exact TcM.PreservesInferOnly.pure none
  | false =>
      simp only [Bool.false_eq_true, if_false, pure_bind]
      refine bind_preservesInferOnly (prims_preservesInferOnly methods) ?_
      intro p
      rcases hspine : source.collectSpine with ⟨head, args⟩
      cases head with
      | const id levels info =>
          simp only []
          cases htoNat :
              id.addr == p.bitVecToNat.addr && decide (args.size ≥ 2) with
          | true =>
              simp only [if_true]
              refine bind_preservesInferOnly
                (tryReduceBitvecToNat_preservesInferOnly hmethods args[1]!) ?_
              intro direct
              cases direct with
              | none => exact TcM.PreservesInferOnly.pure none
              | some result =>
                  refine bind_preservesInferOnly
                    (finishAppResult_preservesInferOnly result args 2) ?_
                  intro finished
                  exact TcM.PreservesInferOnly.pure (some finished)
          | false =>
              simp only [Bool.false_eq_true, if_false]
              cases hult :
                  id.addr == p.bitVecUlt.addr && decide (args.size ≥ 3) with
              | true =>
                  simp only [if_true]
                  refine bind_preservesInferOnly
                    (tryReduceBitvecUlt_preservesInferOnly hmethods args[0]!
                      args[1]! args[2]!) ?_
                  intro direct
                  cases direct with
                  | none => exact TcM.PreservesInferOnly.pure none
                  | some result =>
                      refine bind_preservesInferOnly
                        (finishAppResult_preservesInferOnly result args 3) ?_
                      intro finished
                      exact TcM.PreservesInferOnly.pure (some finished)
              | false =>
                  simp only [Bool.false_eq_true, if_false]
                  cases hdecide :
                      id.addr == p.decidableDecide.addr &&
                        decide (args.size ≥ 2) with
                  | true =>
                      simp only [if_true]
                      refine bind_preservesInferOnly
                        (tryReduceBitvecLtProp_preservesInferOnly hmethods
                          args[0]!) ?_
                      intro direct
                      cases direct with
                      | none => exact TcM.PreservesInferOnly.pure none
                      | some result =>
                          refine bind_preservesInferOnly
                            (finishAppResult_preservesInferOnly result args 2) ?_
                          intro finished
                          exact TcM.PreservesInferOnly.pure (some finished)
                  | false =>
                      simp only [Bool.false_eq_true, if_false]
                      exact TcM.PreservesInferOnly.pure none
      | var | fvar | sort | app | lam | all | letE | prj | nat | str =>
          exact TcM.PreservesInferOnly.pure none

end RecM

end Ix.Tc
