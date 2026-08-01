import Ix.Tc.Verify.Check.DefEqPipelinePolicy

/-!
# Operational policy for DefEq's cache and recursion shell

The comparison tiers preserve `inferOnly`; this module proves that the
production tracing, cache, equivalence-manager, fuel, and balanced-depth
shell around those tiers preserves the same caller policy on success and on
every error path.
-/

namespace Ix.Tc

namespace RecM

attribute [local irreducible] EquivManager.addEquiv Std.HashMap.insert

private theorem modifyRec_preservesInferOnly
    {methods : Methods .anon} (update : TcState .anon → TcState .anon)
    (hupdate : ∀ state, (update state).inferOnly = state.inferOnly) :
    ((modify update : RecM .anon PUnit).run methods).PreservesInferOnly := by
  intro before
  exact hupdate before

private theorem finishDefEqCacheWrite_preservesInferOnly
    {methods : Methods .anon} (leftKey rightKey : EqKey)
    (cacheKey : Address × Address × Address) (cheapMode answer : Bool) :
    TcM.PreservesInferOnly
      ((do
        if answer then
          modify fun state => { state with
            equivManager := state.equivManager.addEquiv leftKey rightKey }
        if cheapMode then
          modify fun state => { state with env := { state.env with
            defEqCheapCache := state.env.defEqCheapCache.insert cacheKey answer
            defEqCache := if answer then
                state.env.defEqCache.insert cacheKey true
              else state.env.defEqCache } }
        else
          modify fun state => { state with env := { state.env with
            defEqCache := state.env.defEqCache.insert cacheKey answer } }
        pure answer : RecM .anon Bool).run methods) := by
  by_cases hanswer : answer
  · simp only [hanswer, if_true]
    apply bind_preservesInferOnly
      (modifyRec_preservesInferOnly
        (fun state => { state with
          equivManager := state.equivManager.addEquiv leftKey rightKey })
        fun _ => rfl)
    intro _
    by_cases hcheap : cheapMode
    · simp only [hcheap, if_true]
      apply bind_preservesInferOnly
        (modifyRec_preservesInferOnly
          (fun state => { state with env := { state.env with
            defEqCheapCache := state.env.defEqCheapCache.insert cacheKey true
            defEqCache := state.env.defEqCache.insert cacheKey true } })
          fun _ => rfl)
      intro _
      exact TcM.PreservesInferOnly.pure true
    · simp only [hcheap, Bool.false_eq_true, if_false]
      apply bind_preservesInferOnly
        (modifyRec_preservesInferOnly
          (fun state => { state with env := { state.env with
            defEqCache := state.env.defEqCache.insert cacheKey true } })
          fun _ => rfl)
      intro _
      exact TcM.PreservesInferOnly.pure true
  · simp only [hanswer, Bool.false_eq_true, if_false, pure_bind]
    by_cases hcheap : cheapMode
    · simp only [hcheap, if_true]
      apply bind_preservesInferOnly
        (modifyRec_preservesInferOnly
          (fun state => { state with env := { state.env with
            defEqCheapCache := state.env.defEqCheapCache.insert cacheKey false
            defEqCache := state.env.defEqCache } })
          fun _ => rfl)
      intro _
      exact TcM.PreservesInferOnly.pure false
    · simp only [hcheap, Bool.false_eq_true, if_false]
      apply bind_preservesInferOnly
        (modifyRec_preservesInferOnly
          (fun state => { state with env := { state.env with
            defEqCache := state.env.defEqCache.insert cacheKey false } })
          fun _ => rfl)
      intro _
      exact TcM.PreservesInferOnly.pure false

theorem isDefEqAfterRootCacheMiss_preservesInferOnly
    {methods : Methods .anon}
    (hinner : ∀ left right,
      ((isDefEqInner left right).run methods).PreservesInferOnly)
    (left right : KExpr .anon) (leftKey rightKey : EqKey)
    (cacheKey : Address × Address × Address) (cheapMode : Bool) :
    ((isDefEqAfterRootCacheMiss left right leftKey rightKey cacheKey
      cheapMode).run methods).PreservesInferOnly := by
  unfold isDefEqAfterRootCacheMiss
  refine bindTcM_preservesInferOnly
    (TcM.PreservesInferOnly.bumpStats _ fun _ => rfl) ?_
  intro _
  refine bindTcM_preservesInferOnly TcM.PreservesInferOnly.tick ?_
  intro _
  refine bindTcM_preservesInferOnly
    (TcM.PreservesInferOnly.modify fun _ => rfl) ?_
  intro _
  refine bindTcM_preservesInferOnly TcM.PreservesInferOnly.get ?_
  intro state
  by_cases hdepth : state.defEqDepth > maxDefEqDepth
  · simp only [hdepth, if_true]
    refine bindTcM_preservesInferOnly
      (TcM.PreservesInferOnly.modify fun _ => rfl) ?_
    intro _
    exact TcM.PreservesInferOnly.throw .maxRecDepth
  · simp only [hdepth, if_false, pure_bind]
    refine bind_preservesInferOnly
      (captureErrors_preservesInferOnly (hinner left right)) ?_
    intro result
    refine bindTcM_preservesInferOnly
      (TcM.PreservesInferOnly.modify fun _ => rfl) ?_
    intro _
    cases result with
    | error error => exact TcM.PreservesInferOnly.throw error
    | ok answer =>
        simp only
        exact finishDefEqCacheWrite_preservesInferOnly leftKey rightKey
          cacheKey cheapMode answer

private theorem finishRootCacheHit_preservesInferOnly
    {methods : Methods .anon} (leftKey rightKey : EqKey)
    (cacheKey : Address × Address × Address)
    (cheapMode cached fromCheap : Bool) :
    TcM.PreservesInferOnly
      ((do
        if fromCheap then
          modify fun state => { state with env := { state.env with
            defEqCheapCache := state.env.defEqCheapCache.insert cacheKey cached
            defEqCache := if cached then
                state.env.defEqCache.insert cacheKey true
              else state.env.defEqCache } }
        else
          modify fun state => { state with env := { state.env with
            defEqCache := state.env.defEqCache.insert cacheKey cached
            defEqCheapCache := if cheapMode then
                state.env.defEqCheapCache.insert cacheKey cached
              else state.env.defEqCheapCache } }
        if cached then
          modify fun state => { state with
            equivManager := state.equivManager.addEquiv leftKey rightKey }
        pure cached : RecM .anon Bool).run methods) := by
  intro before
  cases fromCheap <;> cases cheapMode <;> cases cached <;> rfl

theorem isDefEqAfterDirectCacheMiss_preservesInferOnly
    {methods : Methods .anon}
    (hrootMiss : ∀ left right leftKey rightKey cacheKey cheapMode,
      ((isDefEqAfterRootCacheMiss left right leftKey rightKey cacheKey
        cheapMode).run methods).PreservesInferOnly)
    (left right : KExpr .anon) (contextAddress : Address)
    (leftKey rightKey : EqKey)
    (cacheKey : Address × Address × Address) (cheapMode : Bool) :
    ((isDefEqAfterDirectCacheMiss left right contextAddress leftKey rightKey
      cacheKey cheapMode).run methods).PreservesInferOnly := by
  unfold isDefEqAfterDirectCacheMiss
  refine bindTcM_preservesInferOnly
    (TcM.PreservesInferOnly.withEquiv fun manager =>
      let (leftRoot, manager) := manager.findRootKey leftKey
      let (rightRoot, manager) := manager.findRootKey rightKey
      ((leftRoot, rightRoot), manager)) ?_
  intro roots
  rcases roots with ⟨leftRoot?, rightRoot?⟩
  cases leftRoot? with
  | none => exact hrootMiss left right leftKey rightKey cacheKey cheapMode
  | some leftRoot =>
      cases rightRoot? with
      | none => exact hrootMiss left right leftKey rightKey cacheKey cheapMode
      | some rightRoot =>
          simp only
          by_cases hchanged : leftRoot != leftKey || rightRoot != rightKey
          · simp only [hchanged, if_true]
            by_cases hscope : leftRoot.rootCacheScopeMatches rightRoot
                contextAddress (max left.lbr right.lbr)
            · simp only [hscope, if_true]
              let rootPair := canonicalPair leftRoot.exprAddr rightRoot.exprAddr
              let rootCacheKey := (rootPair.1, rootPair.2, contextAddress)
              refine bind_preservesInferOnly
                (show ((get : RecM .anon (TcState .anon)).run
                  methods).PreservesInferOnly by intro before; rfl) ?_
              intro cacheState
              cases hfull : cacheState.env.defEqCache[rootCacheKey]? with
              | some cached =>
                  simp only [pure_bind]
                  exact finishRootCacheHit_preservesInferOnly leftKey rightKey
                    cacheKey cheapMode cached false
              | none =>
                  by_cases hcheap : cheapMode
                  · simp only [hcheap, if_true]
                    refine bind_preservesInferOnly
                      (show ((get : RecM .anon (TcState .anon)).run
                        methods).PreservesInferOnly by intro before; rfl) ?_
                    intro cheapState
                    cases hcheapHit :
                        cheapState.env.defEqCheapCache[rootCacheKey]? with
                    | some cached =>
                        simp only [pure_bind]
                        exact finishRootCacheHit_preservesInferOnly leftKey
                          rightKey cacheKey cheapMode cached true
                    | none =>
                        simp only [pure_bind]
                        exact hrootMiss left right leftKey rightKey cacheKey
                          true
                  · simp only [hcheap, Bool.false_eq_true, if_false,
                      pure_bind]
                    exact hrootMiss left right leftKey rightKey cacheKey
                      false
            · simp only [hscope, Bool.false_eq_true, if_false]
              exact hrootMiss left right leftKey rightKey cacheKey cheapMode
          · simp only [hchanged, Bool.false_eq_true, if_false]
            exact hrootMiss left right leftKey rightKey cacheKey cheapMode

private theorem finishDirectFullCacheHit_preservesInferOnly
    {methods : Methods .anon} (leftKey rightKey : EqKey)
    (cacheKey : Address × Address × Address)
    (cheapMode cached : Bool) :
    TcM.PreservesInferOnly
      ((do
        if cheapMode then
          modify fun state => { state with env := { state.env with
            defEqCheapCache := state.env.defEqCheapCache.insert cacheKey cached } }
        if cached then
          modify fun state => { state with
            equivManager := state.equivManager.addEquiv leftKey rightKey }
        pure cached : RecM .anon Bool).run methods) := by
  intro before
  cases cheapMode <;> cases cached <;> rfl

private theorem finishDirectCheapCacheHit_preservesInferOnly
    {methods : Methods .anon} (leftKey rightKey : EqKey)
    (cacheKey : Address × Address × Address) (cached : Bool) :
    TcM.PreservesInferOnly
      ((do
        if cached then
          modify fun state => { state with
            env := { state.env with
              defEqCache := state.env.defEqCache.insert cacheKey true }
            equivManager := state.equivManager.addEquiv leftKey rightKey }
        pure cached : RecM .anon Bool).run methods) := by
  intro before
  cases cached <;> rfl

theorem isDefEq_preservesInferOnly
    {methods : Methods .anon}
    (hdirectMiss : ∀ left right contextAddress leftKey rightKey cacheKey
        cheapMode,
      ((isDefEqAfterDirectCacheMiss left right contextAddress leftKey rightKey
        cacheKey cheapMode).run methods).PreservesInferOnly)
    (left right : KExpr .anon) :
    ((isDefEq left right).run methods).PreservesInferOnly := by
  unfold isDefEq
  refine bindTcM_preservesInferOnly
    (TcM.PreservesInferOnly.stepTrace "deq" fun _ =>
      s!"{TcM.addr8 left.addr} ~ {TcM.addr8 right.addr}") ?_
  intro _
  refine bindTcM_preservesInferOnly
    (TcM.PreservesInferOnly.bumpStats _ fun _ => rfl) ?_
  intro _
  by_cases haddress : left.addr == right.addr
  · simp only [haddress, if_true]
    exact TcM.PreservesInferOnly.pure true
  · simp only [haddress, Bool.false_eq_true, if_false, pure_bind]
    refine bindTcM_preservesInferOnly
      (TcM.PreservesInferOnly.defEqCtxKey left right) ?_
    intro contextAddress
    let commonRadius := max left.lbr right.lbr
    let leftKey : EqKey :=
      ⟨left.addr, contextAddress, commonRadius, left.lbr⟩
    let rightKey : EqKey :=
      ⟨right.addr, contextAddress, commonRadius, right.lbr⟩
    refine bindTcM_preservesInferOnly
      (TcM.PreservesInferOnly.withEquiv
        (·.isEquiv leftKey rightKey)) ?_
    intro equivalent
    cases equivalent with
    | true => exact TcM.PreservesInferOnly.pure true
    | false =>
        simp only [Bool.false_eq_true, if_false]
        let pair := canonicalPair left.addr right.addr
        let cacheKey := (pair.1, pair.2, contextAddress)
        refine bind_preservesInferOnly
          (show ((get : RecM .anon (TcState .anon)).run
            methods).PreservesInferOnly by intro before; rfl) ?_
        intro cacheState
        let cheapMode := cacheState.cheapRecursionDepth > 0
        refine bind_preservesInferOnly
          (show ((get : RecM .anon (TcState .anon)).run
            methods).PreservesInferOnly by intro before; rfl) ?_
        intro fullState
        cases hfull : fullState.env.defEqCache[cacheKey]? with
        | some cached =>
            simp only
            by_cases hcheap : cacheState.cheapRecursionDepth > 0
            · simp only [hcheap]
              exact finishDirectFullCacheHit_preservesInferOnly leftKey
                rightKey cacheKey true cached
            · simp only [hcheap]
              exact finishDirectFullCacheHit_preservesInferOnly leftKey
                rightKey cacheKey false cached
        | none =>
            simp only
            by_cases hcheap : cacheState.cheapRecursionDepth > 0
            · simp only [hcheap]
              refine bind_preservesInferOnly
                (show ((get : RecM .anon (TcState .anon)).run
                  methods).PreservesInferOnly by intro before; rfl) ?_
              intro cheapState
              cases hcheapHit : cheapState.env.defEqCheapCache[cacheKey]? with
              | some cached =>
                  simp only
                  exact finishDirectCheapCacheHit_preservesInferOnly leftKey
                    rightKey cacheKey cached
              | none =>
                  simp only
                  exact hdirectMiss left right contextAddress leftKey rightKey
                    cacheKey true
            · simp only [hcheap]
              exact hdirectMiss left right contextAddress leftKey rightKey
                cacheKey false

theorem isDefEq_preservesInferOnly_of_inner
    {methods : Methods .anon}
    (hinner : ∀ left right,
      ((isDefEqInner left right).run methods).PreservesInferOnly)
    (left right : KExpr .anon) :
    ((isDefEq left right).run methods).PreservesInferOnly := by
  apply isDefEq_preservesInferOnly
  intro directLeft directRight contextAddress leftKey rightKey cacheKey
    cheapMode
  apply isDefEqAfterDirectCacheMiss_preservesInferOnly
  intro rootLeft rootRight rootLeftKey rootRightKey rootCacheKey
    rootCheapMode
  exact isDefEqAfterRootCacheMiss_preservesInferOnly hinner rootLeft rootRight
    rootLeftKey rootRightKey rootCacheKey rootCheapMode

end RecM

end Ix.Tc
