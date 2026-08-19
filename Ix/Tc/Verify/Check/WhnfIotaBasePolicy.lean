import Ix.Tc.Verify.Check.WhnfDecidablePolicy

/-!
# Operational inference-policy frame for iota rule execution

This module verifies ordinary and transient iota argument application,
constructor-rule selection, and the bounded Nat-offset parser used to expose
constructor layers before iota dispatch.  The mutually recursive offset
workers are proved together over their shared fuel, so their production
fallback behavior remains explicit.
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

theorem applyIotaArg_preservesInferOnly
    {methods : Methods .anon} (result arg : KExpr .anon)
    (transient : Bool) :
    ((applyIotaArg result arg transient).run methods).PreservesInferOnly := by
  unfold applyIotaArg
  cases transient with
  | false =>
      simp only [Bool.false_eq_true, if_false]
      exact intern_preservesInferOnly (.mkApp result arg)
  | true =>
      simp only [if_true]
      split <;> exact TcM.PreservesInferOnly.pure _

theorem applyIotaArgs_preservesInferOnly
    {methods : Methods .anon} (result : KExpr .anon)
    (args : Array (KExpr .anon)) (transient : Bool) :
    ((applyIotaArgs result args transient).run methods).PreservesInferOnly := by
  rw [applyIotaArgs_eq_foldlM, ← Array.foldlM_toList]
  generalize hitems : args.toList = items
  clear hitems
  induction items generalizing result with
  | nil => exact TcM.PreservesInferOnly.pure result
  | cons arg rest ih =>
      rw [List.foldlM_cons, ReaderT.run_bind]
      exact TcM.PreservesInferOnly.bind
        (applyIotaArg_preservesInferOnly result arg transient)
        (fun next => ih next)

theorem applyIotaRule_preservesInferOnly
    {methods : Methods .anon} (rule : RecRule .anon)
    (recUs : Array (KUniv .anon)) (recr : IotaInfo .anon)
    (spine ctorArgs : Array (KExpr .anon)) (ctorFields : Nat)
    (transient : Bool) :
    ((applyIotaRule rule recUs recr spine ctorArgs ctorFields transient).run
      methods).PreservesInferOnly := by
  unfold applyIotaRule
  refine bindTcM_preservesInferOnly
    (TcM.PreservesInferOnly.instantiateUnivParams rule.rhs recUs) ?_
  intro rhs
  refine bind_preservesInferOnly
    (applyIotaArgs_preservesInferOnly rhs (iotaPrefixArgs recr spine)
      transient) ?_
  intro prefixResult
  refine bind_preservesInferOnly
    (applyIotaArgs_preservesInferOnly prefixResult
      (iotaFieldArgs ctorArgs ctorFields) transient) ?_
  intro fieldResult
  exact applyIotaArgs_preservesInferOnly fieldResult
    (iotaTrailingArgs recr spine) transient

theorem tryApplyIotaCtor_preservesInferOnly
    {methods : Methods .anon} (recr : IotaInfo .anon)
    (recUs : Array (KUniv .anon)) (spine ctorArgs : Array (KExpr .anon))
    (cidx ctorFields : Nat) (transient : Bool) :
    ((tryApplyIotaCtor recr recUs spine ctorArgs cidx ctorFields transient).run
      methods).PreservesInferOnly := by
  unfold tryApplyIotaCtor
  cases hrule : recr.rules[cidx]? with
  | none => exact TcM.PreservesInferOnly.pure none
  | some rule =>
      simp only []
      by_cases hlevels : recUs.size.toUInt64 != recr.lvls
      · simp only [hlevels, if_pos]
        exact TcM.PreservesInferOnly.pure none
      · simp only [hlevels]
        by_cases hfields : ctorFields > ctorArgs.size
        · simp only [hfields, if_pos]
          exact TcM.PreservesInferOnly.pure none
        · simp only [hfields, if_false]
          simpa only [Bool.false_eq_true, if_false, pure_bind] using
            (bind_preservesInferOnly
              (methods := methods)
              (next := fun result => pure (some result))
              (applyIotaRule_preservesInferOnly rule recUs recr spine ctorArgs
                ctorFields transient)
              (fun result => by
                simpa only [ReaderT.run_pure] using
                  (TcM.PreservesInferOnly.pure (some result))))

mutual

theorem natOffsetFuel_preservesInferOnly
    {methods : Methods .anon} : ∀ fuel source,
    ((natOffsetFuel fuel source).run methods).PreservesInferOnly
  | 0, source => by
      rw [natOffsetFuel]
      exact TcM.PreservesInferOnly.pure none
  | fuel + 1, source => by
      rw [natOffsetFuel]
      rcases hspine : source.collectSpine with ⟨head, args⟩
      cases head with
      | const id levels info =>
          refine bind_preservesInferOnly (prims_preservesInferOnly methods) ?_
          intro p
          cases hsucc : id.addr == p.natSucc.addr && args.size == 1 with
          | true =>
              simp only [if_true]
              let arg := args[0]!
              refine bind_preservesInferOnly
                (natOffsetFuel_preservesInferOnly fuel arg) ?_
              intro result
              exact TcM.PreservesInferOnly.pure
                (some ((result.getD (arg, 0)).1,
                  (result.getD (arg, 0)).2 + 1))
          | false =>
              simp only [Bool.false_eq_true, if_false, pure_bind]
              cases hadd : id.addr == p.natAdd.addr && args.size == 2 with
              | false =>
                  simp only [Bool.false_eq_true, if_false]
                  exact TcM.PreservesInferOnly.pure none
              | true =>
                  simp only [if_true]
                  refine bind_preservesInferOnly
                    (evalNatOffsetLiteralFuel_preservesInferOnly fuel args[1]!) ?_
                  intro rhsResult
                  cases rhsResult with
                  | none => exact TcM.PreservesInferOnly.pure none
                  | some rhs =>
                      simp only []
                      let arg := args[0]!
                      refine bind_preservesInferOnly
                        (natOffsetFuel_preservesInferOnly fuel arg) ?_
                      intro result
                      exact TcM.PreservesInferOnly.pure
                        (some ((result.getD (arg, 0)).1,
                          (result.getD (arg, 0)).2 + rhs))
      | var | fvar | sort | app | lam | all | letE | prj | nat | str =>
          exact TcM.PreservesInferOnly.pure none

theorem evalNatOffsetLiteralFuel_preservesInferOnly
    {methods : Methods .anon} : ∀ fuel source,
    ((evalNatOffsetLiteralFuel fuel source).run methods).PreservesInferOnly
  | 0, source => by
      rw [evalNatOffsetLiteralFuel]
      exact TcM.PreservesInferOnly.pure none
  | fuel + 1, source => by
      rw [evalNatOffsetLiteralFuel]
      refine bind_preservesInferOnly (prims_preservesInferOnly methods) ?_
      intro p
      cases hliteral : extractNatValue source p with
      | some value =>
          simp only []
          exact TcM.PreservesInferOnly.pure (some value)
      | none =>
          simp only [pure_bind]
          rcases hspine : source.collectSpine with ⟨head, args⟩
          cases head with
          | const id levels info =>
              cases hpred : id.addr == p.natPred.addr && args.size == 1 with
              | true =>
                  simp only [hpred, if_true]
                  refine bind_preservesInferOnly
                    (evalNatOffsetLiteralFuel_preservesInferOnly fuel args[0]!) ?_
                  intro result
                  cases result with
                  | none => exact TcM.PreservesInferOnly.pure none
                  | some value =>
                      exact TcM.PreservesInferOnly.pure (some (value - 1))
              | false =>
                  simp only [hpred, Bool.false_eq_true, if_false]
                  refine bind_preservesInferOnly
                    (isNatBinArithAddr_preservesInferOnly id.addr) ?_
                  intro isArith
                  cases hbin : isArith && args.size == 2 with
                  | false =>
                      simp only [Bool.false_eq_true, if_false]
                      exact TcM.PreservesInferOnly.pure none
                  | true =>
                      simp only [if_true]
                      refine bind_preservesInferOnly
                        (evalNatOffsetLiteralFuel_preservesInferOnly fuel
                          args[0]!) ?_
                      intro leftResult
                      cases leftResult with
                      | none => exact TcM.PreservesInferOnly.pure none
                      | some left =>
                          simp only []
                          refine bind_preservesInferOnly
                            (evalNatOffsetLiteralFuel_preservesInferOnly fuel
                              args[1]!) ?_
                          intro rightResult
                          cases rightResult with
                          | none => exact TcM.PreservesInferOnly.pure none
                          | some right =>
                              exact TcM.PreservesInferOnly.pure
                                (computeNatBin id.addr PrimAddrs.canonical
                                  left right)
          | var | fvar | sort | app | lam | all | letE | prj | nat | str =>
              exact TcM.PreservesInferOnly.pure none

end

theorem natOffset_preservesInferOnly
    {methods : Methods .anon} (source : KExpr .anon) (depth : Nat) :
    ((natOffset source depth).run methods).PreservesInferOnly := by
  unfold natOffset
  exact natOffsetFuel_preservesInferOnly _ source

theorem natOffsetOrZero_preservesInferOnly
    {methods : Methods .anon} (source : KExpr .anon) (depth : Nat) :
    ((natOffsetOrZero source depth).run methods).PreservesInferOnly := by
  unfold natOffsetOrZero
  refine bind_preservesInferOnly
    (natOffset_preservesInferOnly source depth) ?_
  intro result
  exact TcM.PreservesInferOnly.pure (result.getD (source, 0))

theorem evalNatOffsetLiteral_preservesInferOnly
    {methods : Methods .anon} (source : KExpr .anon) (depth : Nat) :
    ((evalNatOffsetLiteral source depth).run methods).PreservesInferOnly := by
  unfold evalNatOffsetLiteral
  exact evalNatOffsetLiteralFuel_preservesInferOnly _ source

theorem cleanupNatOffsetMajor_preservesInferOnly
    {methods : Methods .anon} (source : KExpr .anon) :
    ((cleanupNatOffsetMajor source).run methods).PreservesInferOnly := by
  unfold cleanupNatOffsetMajor
  refine bind_preservesInferOnly
    (evalNatOffsetLiteral_preservesInferOnly source 0) ?_
  intro literalResult
  cases literalResult with
  | some value =>
      simp only [Option.isSome, if_true]
      exact TcM.PreservesInferOnly.pure none
  | none =>
      simp only [Option.isSome, Bool.false_eq_true, if_false, pure_bind]
      refine bind_preservesInferOnly
        (natOffset_preservesInferOnly source 0) ?_
      intro offsetResult
      cases offsetResult with
      | none => exact TcM.PreservesInferOnly.pure none
      | some baseOffset =>
          simp only []
          rcases baseOffset with ⟨base, offset⟩
          cases hzero : offset == 0 with
          | true =>
              simp only [if_true]
              exact TcM.PreservesInferOnly.pure none
          | false =>
              simp only [Bool.false_eq_true, if_false]
              let predOffset := offset - 1
              cases hpredZero : predOffset == 0 with
              | true =>
                  simp only [if_true]
                  refine bind_preservesInferOnly
                    (mkNatSucc_preservesInferOnly base) ?_
                  intro result
                  exact TcM.PreservesInferOnly.pure (some result)
              | false =>
                  simp only [Bool.false_eq_true, if_false]
                  refine bind_preservesInferOnly
                    (mkNatAdd_preservesInferOnly base
                      (natExprFromValue predOffset)) ?_
                  intro pred
                  refine bind_preservesInferOnly
                    (mkNatSucc_preservesInferOnly pred) ?_
                  intro result
                  exact TcM.PreservesInferOnly.pure (some result)

end RecM

end Ix.Tc
