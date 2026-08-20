import Ix.Tc.Verify.Check.WhnfNativePolicy

/-!
# Operational inference-policy frame for native Nat reduction

This module closes the Nat reducer from its bounded successor-collapse loop
through binary arithmetic and predicates.  The proof covers the stuck-suffix
memo, callback and partial-error paths, local Nat-argument fuel, interning,
and application rebuilding.
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

theorem isNatBinArithAddr_preservesInferOnly
    {methods : Methods .anon} (addr : Address) :
    ((isNatBinArithAddr addr).run methods).PreservesInferOnly := by
  unfold isNatBinArithAddr
  refine bind_preservesInferOnly (prims_preservesInferOnly methods) ?_
  intro p
  exact TcM.PreservesInferOnly.pure _

theorem isNatBinPredAddr_preservesInferOnly
    {methods : Methods .anon} (addr : Address) :
    ((isNatBinPredAddr addr).run methods).PreservesInferOnly := by
  unfold isNatBinPredAddr
  refine bind_preservesInferOnly (prims_preservesInferOnly methods) ?_
  intro p
  exact TcM.PreservesInferOnly.pure _

theorem mkNatAdd_preservesInferOnly
    {methods : Methods .anon} (left right : KExpr .anon) :
    ((mkNatAdd left right).run methods).PreservesInferOnly := by
  unfold mkNatAdd
  refine bind_preservesInferOnly (prims_preservesInferOnly methods) ?_
  intro p
  exact TcM.PreservesInferOnly.pure _

theorem isNatSuccIhStep_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (step : KExpr .anon) :
    ((isNatSuccIhStep step).run methods).PreservesInferOnly := by
  unfold isNatSuccIhStep
  refine bind_preservesInferOnly
    (whnfRec_preservesInferOnly hmethods step) ?_
  intro reduced
  cases reduced with
  | lam name bi ty body info =>
      simp only []
      cases body with
      | lam innerName innerBi innerTy innerBody innerInfo =>
          simp only []
          rcases hspine : innerBody.collectSpine with ⟨head, args⟩
          cases head with
          | const id levels headInfo =>
              simp only []
              refine bind_preservesInferOnly
                (prims_preservesInferOnly methods) ?_
              intro p
              split
              · exact TcM.PreservesInferOnly.pure false
              · cases harg : args[0]! with
                | var index argName argInfo =>
                    split <;> exact TcM.PreservesInferOnly.pure _
                | fvar | sort | const | app | lam | all | letE | prj |
                      nat | str =>
                    exact TcM.PreservesInferOnly.pure false
          | var | fvar | sort | app | lam | all | letE | prj | nat | str =>
              simp only []
              exact TcM.PreservesInferOnly.pure false
      | var | fvar | sort | const | app | all | letE | prj | nat | str =>
          simp only []
          exact TcM.PreservesInferOnly.pure false
  | var | fvar | sort | const | app | all | letE | prj | nat | str =>
      simp only []
      exact TcM.PreservesInferOnly.pure false

theorem natRecLiteralParts_preservesInferOnly
    {methods : Methods .anon} (source : KExpr .anon) :
    ((natRecLiteralParts source).run methods).PreservesInferOnly := by
  unfold natRecLiteralParts
  rcases hspine : source.collectSpine with ⟨head, spine⟩
  cases head with
  | const id levels info =>
      refine bind_preservesInferOnly (prims_preservesInferOnly methods) ?_
      intro p
      split
      · exact TcM.PreservesInferOnly.pure none
      · simp only [pure_bind]
        refine bindTcM_preservesInferOnly
          (TcM.PreservesInferOnly.tryGetConst id) ?_
        intro found
        cases found with
        | none => exact TcM.PreservesInferOnly.pure none
        | some declaration =>
            cases declaration
            case recr name levelParams kind isUnsafe lvls params indices
                motives minors block memberIdx type rules leanAll =>
              simp only []
              split
              · exact TcM.PreservesInferOnly.pure none
              · cases hmajor :
                    spine[(params.toNat + motives.toNat + minors.toNat +
                      indices.toNat)]? with
                | none => exact TcM.PreservesInferOnly.pure none
                | some major =>
                    cases major with
                    | nat value blob majorInfo =>
                        exact TcM.PreservesInferOnly.pure _
                    | var | fvar | sort | const | app | lam | all | letE |
                          prj | str =>
                        exact TcM.PreservesInferOnly.pure none
            all_goals
              simp only []
              exact TcM.PreservesInferOnly.pure none
  | var | fvar | sort | app | lam | all | letE | prj | nat | str =>
      exact TcM.PreservesInferOnly.pure none

theorem tryReduceNatSuccLinearRec_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (arg : KExpr .anon) (offset : Nat) :
    ((tryReduceNatSuccLinearRec arg offset).run methods).PreservesInferOnly := by
  unfold tryReduceNatSuccLinearRec
  refine bind_preservesInferOnly
    (natRecLiteralParts_preservesInferOnly arg) ?_
  intro found
  cases found with
  | none => exact TcM.PreservesInferOnly.pure none
  | some parts =>
      simp only []
      cases hbase : parts.spine[parts.baseIdx]? with
      | none => exact TcM.PreservesInferOnly.pure none
      | some base =>
          cases hstep : parts.spine[parts.stepIdx]? with
          | none => exact TcM.PreservesInferOnly.pure none
          | some step =>
              refine bind_preservesInferOnly
                (isNatSuccIhStep_preservesInferOnly hmethods step) ?_
              intro isSuccStep
              cases hnot : !isSuccStep with
              | true =>
                  simp only [if_true]
                  exact TcM.PreservesInferOnly.pure none
              | false =>
                  simp only [Bool.false_eq_true, if_false, pure_bind]
                  refine bind_preservesInferOnly
                    (whnfRec_preservesInferOnly hmethods base) ?_
                  intro baseWhnf
                  refine bind_preservesInferOnly
                    (prims_preservesInferOnly methods) ?_
                  intro p
                  cases hvalue : extractNatValue baseWhnf p with
                  | some value =>
                      simp only []
                      exact TcM.PreservesInferOnly.pure _
                  | none =>
                      simp only []
                      split
                      · exact TcM.PreservesInferOnly.pure none
                      · refine bind_preservesInferOnly
                          (mkNatAdd_preservesInferOnly baseWhnf
                            (natExprFromValue (parts.major + offset))) ?_
                        intro result
                        exact TcM.PreservesInferOnly.pure (some result)

theorem isNatSuccSpine_preservesInferOnly
    {methods : Methods .anon} (source : KExpr .anon) :
    ((isNatSuccSpine source).run methods).PreservesInferOnly := by
  unfold isNatSuccSpine
  rcases hspine : source.collectSpine with ⟨head, args⟩
  cases head with
  | const id levels info =>
      refine bind_preservesInferOnly (prims_preservesInferOnly methods) ?_
      intro p
      exact TcM.PreservesInferOnly.pure _
  | var | fvar | sort | app | lam | all | letE | prj | nat | str =>
      exact TcM.PreservesInferOnly.pure false

theorem recordNatSuccStuck_preservesInferOnly
    {methods : Methods .anon} (visited : Array (Address × Address)) :
    ((recordNatSuccStuck visited).run methods).PreservesInferOnly := by
  unfold recordNatSuccStuck
  exact liftTcM_preservesInferOnly <|
    TcM.PreservesInferOnly.modify (fun _ => rfl)

theorem tryReduceNatSuccPeelMiss_preservesInferOnly
    {methods : Methods .anon} (normalized current : KExpr .anon)
    (offset : Nat) (visited : Array (Address × Address))
    (currentKey : Address × Address) :
    ((tryReduceNatSuccPeelMiss normalized current offset visited
      currentKey).run methods).PreservesInferOnly := by
  unfold tryReduceNatSuccPeelMiss
  refine bindTcM_preservesInferOnly
    (TcM.PreservesInferOnly.whnfKey normalized) ?_
  intro normalizedKey
  exact TcM.PreservesInferOnly.pure _

theorem tryReduceNatSuccPeelAfterKey_preservesInferOnly
    {methods : Methods .anon} (normalized current : KExpr .anon)
    (offset : Nat) (visited : Array (Address × Address))
    (currentKey : Address × Address) :
    ((tryReduceNatSuccPeelAfterKey normalized current offset visited
      currentKey).run methods).PreservesInferOnly := by
  unfold tryReduceNatSuccPeelAfterKey
  refine bindTcM_preservesInferOnly TcM.PreservesInferOnly.get ?_
  intro state
  split
  · refine bind_preservesInferOnly
      (recordNatSuccStuck_preservesInferOnly visited) ?_
    intro _
    exact TcM.PreservesInferOnly.pure _
  · exact tryReduceNatSuccPeelMiss_preservesInferOnly normalized current
      offset visited currentKey

theorem tryReduceNatSuccPeel_preservesInferOnly
    {methods : Methods .anon} (normalized current : KExpr .anon)
    (offset : Nat) (visited : Array (Address × Address)) :
    ((tryReduceNatSuccPeel normalized current offset visited).run methods).PreservesInferOnly := by
  unfold tryReduceNatSuccPeel
  refine bindTcM_preservesInferOnly
    (TcM.PreservesInferOnly.whnfKey current) ?_
  intro currentKey
  exact tryReduceNatSuccPeelAfterKey_preservesInferOnly normalized current
    offset visited currentKey

theorem tryReduceNatSuccAfterWhnf_preservesInferOnly
    {methods : Methods .anon} (normalized : KExpr .anon) (offset : Nat)
    (visited : Array (Address × Address)) :
    ((tryReduceNatSuccAfterWhnf normalized offset visited).run methods).PreservesInferOnly := by
  unfold tryReduceNatSuccAfterWhnf
  refine bind_preservesInferOnly (prims_preservesInferOnly methods) ?_
  intro p
  cases hliteral : extractNatLit normalized p with
  | some value =>
      simp only []
      exact TcM.PreservesInferOnly.pure _
  | none =>
      simp only [pure_bind]
      rcases hspine : normalized.collectSpine with ⟨head, args⟩
      refine bind_preservesInferOnly
        (isNatSuccSpine_preservesInferOnly normalized) ?_
      intro isSucc
      cases hsucc : isSucc with
      | true =>
          simp only [if_true]
          exact tryReduceNatSuccPeel_preservesInferOnly normalized args[0]!
            offset visited
      | false =>
          simp only [Bool.false_eq_true, if_false]
          refine bind_preservesInferOnly
            (recordNatSuccStuck_preservesInferOnly visited) ?_
          intro _
          exact TcM.PreservesInferOnly.pure _

theorem tryReduceNatSuccIterStep_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (state : KExpr .anon × Nat × Array (Address × Address)) :
    ((tryReduceNatSuccIterStep state).run methods).PreservesInferOnly := by
  rcases state with ⟨current, offset, visited⟩
  unfold tryReduceNatSuccIterStep
  refine bind_preservesInferOnly
    (tryReduceNatSuccLinearRec_preservesInferOnly hmethods current offset) ?_
  intro direct
  cases direct with
  | some result => exact TcM.PreservesInferOnly.pure _
  | none =>
      simp only [pure_bind]
      refine bind_preservesInferOnly
        (whnfModeRec_preservesInferOnly hmethods current .stuck) ?_
      intro normalized
      exact tryReduceNatSuccAfterWhnf_preservesInferOnly normalized offset
        visited

theorem tryReduceNatSuccIter_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (arg : KExpr .anon) :
    ((tryReduceNatSuccIter arg).run methods).PreservesInferOnly := by
  unfold tryReduceNatSuccIter
  refine bindTcM_preservesInferOnly
    (TcM.PreservesInferOnly.whnfKey arg) ?_
  intro entryKey
  refine bindTcM_preservesInferOnly TcM.PreservesInferOnly.get ?_
  intro state
  split
  · exact TcM.PreservesInferOnly.pure none
  · exact runBounded_preservesInferOnly
      (fun loopState =>
        tryReduceNatSuccIterStep_preservesInferOnly hmethods loopState)
      maxWhnfFuel.toNat (arg, 1, #[entryKey])

theorem tryReduceNatPredicate_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (addr : Address) (args : Array (KExpr .anon)) :
    ((tryReduceNatPredicate addr args).run methods).PreservesInferOnly := by
  unfold tryReduceNatPredicate
  refine bind_preservesInferOnly
    (whnfNatReducerArg_preservesInferOnly hmethods args[0]!) ?_
  intro leftResult
  cases leftResult with
  | none => exact TcM.PreservesInferOnly.pure none
  | some left =>
      simp only []
      refine bind_preservesInferOnly (prims_preservesInferOnly methods) ?_
      intro p
      cases hleft : extractNatLit left p with
      | none => exact TcM.PreservesInferOnly.pure none
      | some leftValue =>
          simp only []
          refine bind_preservesInferOnly
            (whnfNatReducerArg_preservesInferOnly hmethods args[1]!) ?_
          intro rightResult
          cases rightResult with
          | none => exact TcM.PreservesInferOnly.pure none
          | some right =>
              simp only []
              cases hright : extractNatLit right p with
              | none => exact TcM.PreservesInferOnly.pure none
              | some rightValue =>
                  simp only []
                  refine bindIntern_preservesInferOnly
                    (.mkConst
                      (if (if addr == p.natBeq.addr then
                          leftValue == rightValue
                        else leftValue.ble rightValue) then
                        p.boolTrue else p.boolFalse) #[]) ?_
                  intro result
                  refine bind_preservesInferOnly
                    (finishAppResult_preservesInferOnly result args 2) ?_
                  intro finished
                  exact TcM.PreservesInferOnly.pure (some finished)

theorem tryReduceNatWithSuccMode_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (source : KExpr .anon) (mode : NatSuccMode) :
    ((tryReduceNatWithSuccMode source mode).run methods).PreservesInferOnly := by
  unfold tryReduceNatWithSuccMode
  rcases hspine : source.collectSpine with ⟨head, args⟩
  cases head with
  | const id levels info =>
      refine bind_preservesInferOnly (prims_preservesInferOnly methods) ?_
      intro p
      cases hsucc : id.addr == p.natSucc.addr && args.size == 1 with
      | true =>
          simp only [if_true]
          cases hmode : mode == .stuck with
          | true =>
              simp only [if_true]
              exact TcM.PreservesInferOnly.pure none
          | false =>
              simp only [Bool.false_eq_true, if_false, pure_bind]
              exact tryReduceNatSuccIter_preservesInferOnly hmethods args[0]!
      | false =>
          simp only [Bool.false_eq_true, if_false, pure_bind]
          by_cases hsmall : args.size < 2
          · simp only [hsmall, if_pos]
            exact TcM.PreservesInferOnly.pure none
          · simp only [hsmall, if_false]
            focus
              refine bind_preservesInferOnly
                (isNatBinArithAddr_preservesInferOnly id.addr) ?_
              intro isArith
              refine bind_preservesInferOnly
                (isNatBinPredAddr_preservesInferOnly id.addr) ?_
              intro isPred
              cases hknown : !isArith && !isPred with
              | true =>
                  simp only [if_true]
                  exact TcM.PreservesInferOnly.pure none
              | false =>
                  simp only [Bool.false_eq_true, if_false]
                  cases hpred : isPred with
                  | true =>
                      simp only [if_true]
                      exact tryReduceNatPredicate_preservesInferOnly hmethods
                        id.addr args
                  | false =>
                      simp only [Bool.false_eq_true, if_false]
                      refine bind_preservesInferOnly
                        (whnfNatReducerArg_preservesInferOnly hmethods
                          args[0]!) ?_
                      intro leftResult
                      cases leftResult with
                      | none => exact TcM.PreservesInferOnly.pure none
                      | some left =>
                          simp only []
                          refine bind_preservesInferOnly
                            (whnfNatReducerArg_preservesInferOnly hmethods
                              args[1]!) ?_
                          intro rightResult
                          cases rightResult with
                          | none => exact TcM.PreservesInferOnly.pure none
                          | some right =>
                              simp only []
                              cases hleft : extractNatLit left p with
                              | none =>
                                  exact TcM.PreservesInferOnly.pure none
                              | some leftValue =>
                                  simp only []
                                  cases hright : extractNatLit right p with
                                  | none =>
                                      exact TcM.PreservesInferOnly.pure none
                                  | some rightValue =>
                                      simp only []
                                      cases harith : isArith with
                                      | true =>
                                          simp only [if_true]
                                          cases hcomputed : computeNatBin
                                              id.addr PrimAddrs.canonical
                                              leftValue rightValue with
                                          | none =>
                                              exact
                                                TcM.PreservesInferOnly.pure
                                                  none
                                          | some value =>
                                              simp only []
                                              refine bind_preservesInferOnly
                                                (finishAppResult_preservesInferOnly
                                                  (natExprFromValue value)
                                                  args 2) ?_
                                              intro result
                                              exact
                                                TcM.PreservesInferOnly.pure
                                                  (some result)
                                      | false =>
                                          simp only [Bool.false_eq_true,
                                            if_false]
                                          refine bindIntern_preservesInferOnly
                                            (.mkConst
                                              (if (if id.addr ==
                                                  p.natBeq.addr then
                                                  leftValue == rightValue
                                                else
                                                  leftValue.ble rightValue)
                                                then p.boolTrue
                                                else p.boolFalse) #[]) ?_
                                          intro result
                                          refine bind_preservesInferOnly
                                            (finishAppResult_preservesInferOnly
                                              result args 2) ?_
                                          intro finished
                                          exact
                                            TcM.PreservesInferOnly.pure
                                              (some finished)
  | var | fvar | sort | app | lam | all | letE | prj | nat | str =>
      exact TcM.PreservesInferOnly.pure none

end RecM

end Ix.Tc
