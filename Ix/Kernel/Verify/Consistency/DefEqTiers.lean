/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.DefEqQuick

/-!
# The non-reducing DefEq tiers under the contracts

Production conversion answers from three memos before any reduction, then
charges fuel and depth and runs the recursive tiers. This module proves every
tier up to the quick structural probe against the checker invariant with the
recursive callbacks abstracted by their contracts:

* the entry: statistics, the hash path, the equivalence-manager query with its
  path halving, the full cache, the cheap cache with its promotion, and the
  copies between partitions;
* the guarded representative probe after both partitions miss, whose hit
  composes the two representative chains with the root edge and records the
  original pair;
* the charged tail: fuel and depth accounting, the inner tiers under caught
  errors, and the manager and cache writes of a positive answer;
* the inner tiers: the quick structural probe of `DefEqQuick`, then the
  production seam `isDefEqInnerAfterQuick` under its contract.

Each proof follows the exact production control flow through the monad,
outcome by outcome, and preserves the invariant on every `false` and error
path. `DefEqSeamAssumptions` collects what remains: the reducing tail, the
transport of recorded chains to the caller's registration, the annotation
discipline of the hash path, and the binder premises. `DefEqTierResources`
collects the finite collision and walker data, each an instance of
`RunAssumptions`. `isDefEq_direct_tiers` is the `StepContracts.isDefEq`
field modulo those premises.
-/
namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

/-! ### Run equations of the recursive monad's primitives -/

theorem modify_run (update : TcState .anon → TcState .anon) (methods : Methods .anon)
    (state : TcState .anon) :
    (modify update : RecM .anon PUnit).run methods state = .ok ⟨⟩ (update state) := rfl

theorem get_run (methods : Methods .anon) (state : TcState .anon) :
    (get : RecM .anon (TcState .anon)).run methods state = .ok state state := rfl

theorem pure_run {α : Type} (value : α) (methods : Methods .anon) (state : TcState .anon) :
    (pure value : RecM .anon α).run methods state = .ok value state := rfl

theorem throw_run {α : Type} (err : TcError .anon) (methods : Methods .anon) (state : TcState .anon) :
    (throw err : RecM .anon α).run methods state = .error err state := rfl
/-- The caught-error wrapper of the inner tiers as a pure map on outcomes. -/
theorem tryExcept_run {α : Type} (action : RecM .anon α) (methods : Methods .anon)
    (state : TcState .anon) :
    (tryCatch (do let value ← action; pure (Except.ok value))
      (fun err => pure (Except.error err)) : RecM .anon (Except (TcError .anon) α)).run methods state =
      match action.run methods state with
      | .ok value after => .ok (.ok value) after
      | .error err after => .ok (.error err) after := by
  change EStateM.tryCatch (EStateM.bind (action.run methods) _) _ state = _
  unfold EStateM.tryCatch EStateM.bind
  cases action.run methods state <;> rfl

/-! ### Invariant preservation through the entry's bookkeeping -/

namespace CheckerInvariant

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {anchor entries : Model.Environment β} {source : Ixon.Env}
  {catalog : List (SourceCacheRequest source)} {locals : List FVarId}
  {context : Model.Context β} {bounds : List VLevel}

/-- An optional statistics update outside the environment, manager, and local
context preserves the invariant. -/
theorem afterBumpStats {before after : TcState .anon}
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (update : TcState .anon → TcState .anon)
    (env : ∀ state, (update state).env = state.env)
    (lctx : ∀ state, (update state).lctx = state.lctx)
    (loader : ∀ state, (update state).lazyFault = state.lazyFault)
    (manager : ∀ state, (update state).equivManager = state.equivManager)
    (run : TcM.bumpStats update before = .ok () after) :
    CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds after := by
  rw [bumpStats_eq] at run
  cases run
  split
  · exact valid.ofDefEqScalars (env _) (lctx _) (loader _) (manager _)
  · exact valid

/-- Fuel accounting preserves the invariant on both outcomes. -/
theorem tickOutcome {before : TcState .anon}
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before) :
    match TcM.tick before with
    | .ok _ after | .error _ after =>
        CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds after := by
  rw [tick_eq]
  by_cases fuel : (before.recFuel == 0) = true
  · rw [if_pos fuel]
    exact valid
  · rw [if_neg fuel]
    exact valid.ofDefEqScalars rfl rfl rfl rfl

end CheckerInvariant

/-- A recorded conversion of a pair is recorded at the pair's canonical key. -/
theorem AddressConversion.canonical {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {left right lo hi ctxAddr : Address}
    (canonical : canonicalPair left right = (lo, hi))
    (recorded : AddressConversion.{u,v} resolve entries left right ctxAddr) :
    AddressConversion.{u,v} resolve entries lo hi ctxAddr := by
  rcases canonicalPair_cases left right with same | swapped
  · rw [canonical] at same
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
    exact recorded
  · rw [canonical] at swapped
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj swapped
    exact recorded.symm

/-! ### The charged recursive tail -/

section Charged

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {anchor entries : Model.Environment β} {source : Ixon.Env}
  {catalog : List (SourceCacheRequest source)} {locals : List FVarId}
  {context : Model.Context β} {bounds : List VLevel}

/-- After every O(1) exit misses: statistics, fuel, the depth guard, the inner
tiers under caught errors, depth restoration, and the recording of a positive
answer in the manager and the caches. The inner tiers are abstracted by their
outcome at the caller's readings. -/
theorem isDefEqAfterRootCacheMiss_sound {methods : Methods .anon} {before : TcState .anon}
    {a b : KExpr .anon} {ta tb : AExpr β} {eqCtx lo hi : Address} {cheapMode : Bool}
    (inner : ∀ state,
      CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds state →
      ConversionPost.{u,v} resolve anchor entries source catalog locals context bounds ta tb
        ((RecM.isDefEqInner a b).run methods state))
    (origin : DefEqKeyOrigin.{u,v} resolve anchor entries source catalog locals context bounds a b eqCtx)
    (canonical : canonicalPair a.addr b.addr = (lo, hi))
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (leftReads : readScopedExpr? resolve locals a = some ta.erase)
    (leftTyped : ∃ type, TypingClaim.{u,v} entries context ta type)
    (rightReads : readScopedExpr? resolve locals b = some tb.erase)
    (rightTyped : ∃ type, TypingClaim.{u,v} entries context tb type) :
    ConversionPost.{u,v} resolve anchor entries source catalog locals context bounds ta tb
      ((RecM.isDefEqAfterRootCacheMiss a b ⟨a.addr, eqCtx, max a.lbr b.lbr, a.lbr⟩
        ⟨b.addr, eqCtx, max a.lbr b.lbr, b.lbr⟩ (lo, hi, eqCtx) cheapMode).run methods before) := by
  have recordEdge : ConversionClaim.{u,v} entries context ta tb →
      EqKeyChain.{u,v} resolve entries ⟨a.addr, eqCtx, max a.lbr b.lbr, a.lbr⟩
        ⟨b.addr, eqCtx, max a.lbr b.lbr, b.lbr⟩ :=
    fun claim => .edge (EqKeyConversion.ofClaim origin leftReads rightReads leftTyped rightTyped claim)
  have recordKey : ConversionClaim.{u,v} entries context ta tb →
      AddressConversion.{u,v} resolve entries lo hi eqCtx :=
    fun claim => (AddressConversion.ofClaim origin leftReads rightReads leftTyped rightTyped claim).canonical
      canonical
  unfold RecM.isDefEqAfterRootCacheMiss
  simp only [ReaderT.run_bind, ReaderT.run_monadLift]
  refine EStateM.bind_cases ?_ ?_
  · intro value s₀ statsRun
    cases value
    have valid₀ := valid.afterBumpStats (fun s => {s with deqMisses := s.deqMisses + 1})
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) statsRun
    try dsimp only
    refine EStateM.bind_cases ?_ ?_
    · intro value s₁ tickRun
      cases value
      have valid₁ : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds
          s₁ := by
        have outcome := valid₀.tickOutcome
        have tickRun' : TcM.tick s₀ = .ok () s₁ := tickRun
        rw [tickRun'] at outcome
        exact outcome
      try dsimp only
      refine EStateM.bind_cases ?_ ?_
      · intro value s₂ bumpRun
        rw [modify_run] at bumpRun
        obtain ⟨_, bumpEq⟩ := EStateM.Result.ok.inj bumpRun
        have valid₂ : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context
            bounds s₂ := by
          subst bumpEq
          exact valid₁.ofDefEqScalars rfl rfl rfl rfl
        try dsimp only
        refine EStateM.bind_cases ?_ ?_
        · intro current s₂' getRun
          rw [get_run] at getRun
          obtain ⟨currentEq, stateEq⟩ := EStateM.Result.ok.inj getRun
          subst currentEq stateEq
          try dsimp only
          split
          · simp only [ReaderT.run_bind]
            refine EStateM.bind_cases ?_ ?_
            · intro value s₃ restoreRun
              rw [modify_run] at restoreRun
              obtain ⟨_, restoreEq⟩ := EStateM.Result.ok.inj restoreRun
              try dsimp only
              refine EStateM.bind_cases ?_ ?_
              · intro value s h
                rw [throw_run] at h
                cases h
              · intro err s h
                rw [throw_run] at h
                cases h
                subst restoreEq
                exact valid₂.ofDefEqScalars rfl rfl rfl rfl
            · intro err s h
              rw [modify_run] at h
              cases h
          · simp only [ReaderT.run_bind]
            refine EStateM.bind_cases ?_ ?_
            · intro result s₃ catchRun
              rw [tryExcept_run] at catchRun
              have innerPost := inner s₂ valid₂
              cases innerRun : (RecM.isDefEqInner a b).run methods s₂ with
              | ok answer s₃' =>
                  rw [innerRun] at catchRun innerPost
                  dsimp only at catchRun
                  obtain ⟨resultEq, stateEq⟩ := EStateM.Result.ok.inj catchRun
                  subst resultEq stateEq
                  try dsimp only
                  simp only [ReaderT.run_bind]
                  refine EStateM.bind_cases ?_ ?_
                  · intro value s₄ restoreRun
                    rw [modify_run] at restoreRun
                    obtain ⟨_, restoreEq⟩ := EStateM.Result.ok.inj restoreRun
                    try dsimp only
                    refine EStateM.bind_cases ?_ ?_
                    · intro answer' s₄' pureRun
                      rw [pure_run] at pureRun
                      obtain ⟨answerEq, stateEq⟩ := EStateM.Result.ok.inj pureRun
                      subst answerEq stateEq
                      cases answer with
                      | false =>
                          have valid₄ : CheckerInvariant.{u,v} resolve anchor entries source catalog
                              locals context bounds s₄ := by
                            subst restoreEq
                            exact innerPost.ofDefEqScalars rfl rfl rfl rfl
                          simp only [Bool.false_eq_true, ↓reduceIte]
                          split
                          · simp only [ReaderT.run_bind]
                            refine EStateM.bind_cases ?_ ?_
                            · intro value s₅ writeRun
                              rw [modify_run] at writeRun
                              obtain ⟨_, writeEq⟩ := EStateM.Result.ok.inj writeRun
                              try dsimp only
                              rw [pure_run]
                              subst writeEq
                              exact valid₄.ofDefEqUpdate ⟨_, _, rfl⟩ rfl rfl
                                (valid₄.semantics.defEq.ofInsert (lo, hi, eqCtx) false (.inl rfl)
                                  (.inr rfl) (fun h => nomatch h))
                                valid₄.semantics.equivalence
                            · intro err s h
                              rw [modify_run] at h
                              cases h
                          · simp only [ReaderT.run_bind]
                            refine EStateM.bind_cases ?_ ?_
                            · intro value s₅ writeRun
                              rw [modify_run] at writeRun
                              obtain ⟨_, writeEq⟩ := EStateM.Result.ok.inj writeRun
                              try dsimp only
                              rw [pure_run]
                              subst writeEq
                              exact valid₄.ofDefEqUpdate ⟨_, _, rfl⟩ rfl rfl
                                (valid₄.semantics.defEq.ofInsert (lo, hi, eqCtx) false (.inr rfl)
                                  (.inl rfl) (fun h => nomatch h))
                                valid₄.semantics.equivalence
                            · intro err s h
                              rw [modify_run] at h
                              cases h
                      | true =>
                          obtain ⟨valid₃, claim⟩ := innerPost
                          have valid₄ : CheckerInvariant.{u,v} resolve anchor entries source catalog
                              locals context bounds s₄ := by
                            subst restoreEq
                            exact valid₃.ofDefEqScalars rfl rfl rfl rfl
                          simp only [↓reduceIte]
                          simp only [ReaderT.run_bind]
                          refine EStateM.bind_cases ?_ ?_
                          · intro value s₅ unionRun
                            rw [modify_run] at unionRun
                            obtain ⟨_, unionEq⟩ := EStateM.Result.ok.inj unionRun
                            have valid₅ : CheckerInvariant.{u,v} resolve anchor entries source catalog
                                locals context bounds s₅ := by
                              subst unionEq
                              exact valid₄.addEquiv (recordEdge claim)
                            try dsimp only
                            split
                            · simp only [ReaderT.run_bind]
                              refine EStateM.bind_cases ?_ ?_
                              · intro value s₆ writeRun
                                rw [modify_run] at writeRun
                                obtain ⟨_, writeEq⟩ := EStateM.Result.ok.inj writeRun
                                try dsimp only
                                rw [pure_run]
                                subst writeEq
                                exact ⟨valid₅.ofDefEqUpdate ⟨_, _, rfl⟩ rfl rfl
                                  (valid₅.semantics.defEq.ofInsert (lo, hi, eqCtx) true (.inr rfl)
                                    (.inr rfl) (fun _ => recordKey claim))
                                  valid₅.semantics.equivalence, claim⟩
                              · intro err s h
                                rw [modify_run] at h
                                cases h
                            · simp only [ReaderT.run_bind]
                              refine EStateM.bind_cases ?_ ?_
                              · intro value s₆ writeRun
                                rw [modify_run] at writeRun
                                obtain ⟨_, writeEq⟩ := EStateM.Result.ok.inj writeRun
                                try dsimp only
                                rw [pure_run]
                                subst writeEq
                                exact ⟨valid₅.ofDefEqUpdate ⟨_, _, rfl⟩ rfl rfl
                                  (valid₅.semantics.defEq.ofInsert (lo, hi, eqCtx) true (.inr rfl)
                                    (.inl rfl) (fun _ => recordKey claim))
                                  valid₅.semantics.equivalence, claim⟩
                              · intro err s h
                                rw [modify_run] at h
                                cases h
                          · intro err s h
                            rw [modify_run] at h
                            cases h
                    · intro err s h
                      rw [pure_run] at h
                      cases h
                  · intro err s h
                    rw [modify_run] at h
                    cases h
              | error err s₃' =>
                  rw [innerRun] at catchRun innerPost
                  dsimp only at catchRun
                  obtain ⟨resultEq, stateEq⟩ := EStateM.Result.ok.inj catchRun
                  subst resultEq stateEq
                  try dsimp only
                  simp only [ReaderT.run_bind]
                  refine EStateM.bind_cases ?_ ?_
                  · intro value s₄ restoreRun
                    rw [modify_run] at restoreRun
                    obtain ⟨_, restoreEq⟩ := EStateM.Result.ok.inj restoreRun
                    try dsimp only
                    refine EStateM.bind_cases ?_ ?_
                    · intro answer s h
                      rw [throw_run] at h
                      cases h
                    · intro err' s h
                      rw [throw_run] at h
                      cases h
                      subst restoreEq
                      exact innerPost.ofDefEqScalars rfl rfl rfl rfl
                  · intro err' s h
                    rw [modify_run] at h
                    cases h
            · intro err s h
              rw [tryExcept_run] at h
              cases innerRun : (RecM.isDefEqInner a b).run methods s₂ <;> rw [innerRun] at h <;>
                dsimp only at h <;> cases h
        · intro err s h
          rw [get_run] at h
          cases h
      · intro err s h
        rw [modify_run] at h
        cases h
    · intro err s₁ tickRun
      have outcome := valid₀.tickOutcome
      have tickRun' : TcM.tick s₀ = .error err s₁ := tickRun
      rw [tickRun'] at outcome
      exact outcome
  · intro err s₀ statsRun
    have statsRun' : TcM.bumpStats _ before = .error err s₀ := statsRun
    rw [bumpStats_eq] at statsRun'
    cases statsRun'


/-! ### The guarded representative probe -/

/-- After both direct partitions miss: representatives of both keys, the
scope guard, the root-derived cache probe in the full partition and, in cheap
mode, the cheap partition, the copy of a hit to the original key, and the
manager union after a positive hit. A hit composes the two representative
chains with the root edge into a chain between the original keys, which the
transport premise reads at the caller's registration. -/
theorem isDefEqAfterDirectCacheMiss_sound {methods : Methods .anon} {before : TcState .anon}
    {a b : KExpr .anon} {ta tb : AExpr β} {eqCtx lo hi : Address} {cheapMode : Bool}
    (transport : DefEqMemoTransport.{u,v} resolve anchor entries source catalog)
    (inner : ∀ state,
      CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds state →
      ConversionPost.{u,v} resolve anchor entries source catalog locals context bounds ta tb
        ((RecM.isDefEqInner a b).run methods state))
    (origin : DefEqKeyOrigin.{u,v} resolve anchor entries source catalog locals context bounds a b eqCtx)
    (canonical : canonicalPair a.addr b.addr = (lo, hi))
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (leftReads : readScopedExpr? resolve locals a = some ta.erase)
    (leftTyped : ∃ type, TypingClaim.{u,v} entries context ta type)
    (rightReads : readScopedExpr? resolve locals b = some tb.erase)
    (rightTyped : ∃ type, TypingClaim.{u,v} entries context tb type) :
    ConversionPost.{u,v} resolve anchor entries source catalog locals context bounds ta tb
      ((RecM.isDefEqAfterDirectCacheMiss a b eqCtx ⟨a.addr, eqCtx, max a.lbr b.lbr, a.lbr⟩
        ⟨b.addr, eqCtx, max a.lbr b.lbr, b.lbr⟩ (lo, hi, eqCtx) cheapMode).run methods before) := by
  have tail : ∀ state,
      CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds state →
      ConversionPost.{u,v} resolve anchor entries source catalog locals context bounds ta tb
        ((RecM.isDefEqAfterRootCacheMiss a b ⟨a.addr, eqCtx, max a.lbr b.lbr, a.lbr⟩
          ⟨b.addr, eqCtx, max a.lbr b.lbr, b.lbr⟩ (lo, hi, eqCtx) cheapMode).run methods state) :=
    fun _ valid' => isDefEqAfterRootCacheMiss_sound inner origin canonical valid' leftReads leftTyped
      rightReads rightTyped
  have recordKey : ConversionClaim.{u,v} entries context ta tb →
      AddressConversion.{u,v} resolve entries lo hi eqCtx :=
    fun claim => (AddressConversion.ofClaim origin leftReads rightReads leftTyped rightTyped claim).canonical
      canonical
  have read : EqKeyChain.{u,v} resolve entries ⟨a.addr, eqCtx, max a.lbr b.lbr, a.lbr⟩
      ⟨b.addr, eqCtx, max a.lbr b.lbr, b.lbr⟩ → ConversionClaim.{u,v} entries context ta tb :=
    transport locals context bounds a b ta tb eqCtx origin leftReads leftTyped rightReads rightTyped
  unfold RecM.isDefEqAfterDirectCacheMiss
  simp only [ReaderT.run_bind, ReaderT.run_monadLift]
  refine EStateM.bind_cases ?_ ?_
  · rintro ⟨aRoot?, bRoot?⟩ s₁ rootsRun
    have rootsRun' : TcM.withEquiv _ before = .ok (aRoot?, bRoot?) s₁ := rootsRun
    rw [withEquiv_eq] at rootsRun'
    obtain ⟨rootsEq, stateEq⟩ := EStateM.Result.ok.inj rootsRun'
    have roots := valid.semantics.equivalence.findRootKeys ⟨a.addr, eqCtx, max a.lbr b.lbr, a.lbr⟩
      ⟨b.addr, eqCtx, max a.lbr b.lbr, b.lbr⟩
    have valid₁ : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds
        s₁ := by
      subst stateEq
      exact valid.ofDefEqUpdate ⟨_, _, rfl⟩ rfl rfl
        (valid.semantics.defEq.ofMaps fun partition => by cases partition <;> rfl) roots.1
    have leftChain : ∀ root, aRoot? = some root →
        EqKeyChain.{u,v} resolve entries ⟨a.addr, eqCtx, max a.lbr b.lbr, a.lbr⟩ root :=
      fun root found => roots.2.1 root (by rw [rootsEq]; exact found)
    have rightChain : ∀ root, bRoot? = some root →
        EqKeyChain.{u,v} resolve entries ⟨b.addr, eqCtx, max a.lbr b.lbr, b.lbr⟩ root :=
      fun root found => roots.2.2 root (by rw [rootsEq]; exact found)
    try dsimp only
    cases aRoot? with
    | none => exact tail s₁ valid₁
    | some aRoot =>
    cases bRoot? with
    | none => exact tail s₁ valid₁
    | some bRoot =>
    try dsimp only
    split
    · split
      · rename_i _ scope
        rcases canonicalRoots : canonicalPair aRoot.exprAddr bRoot.exprAddr with ⟨rlo, rhi⟩
        try dsimp only
        have rootChain : ∀ partition : DefEqCachePartition,
            (partition.cache s₁)[(rlo, rhi, eqCtx)]? = some true →
            EqKeyChain.{u,v} resolve entries ⟨a.addr, eqCtx, max a.lbr b.lbr, a.lbr⟩
              ⟨b.addr, eqCtx, max a.lbr b.lbr, b.lbr⟩ := fun partition hit =>
          .trans (leftChain aRoot rfl) (.trans
            (.edge (valid₁.semantics.defEq.rootEdge partition scope canonicalRoots hit))
            (.symm (rightChain bRoot rfl)))
        simp only [ReaderT.run_bind]
        refine EStateM.bind_cases ?_ ?_
        · intro current s₂ getRun
          rw [get_run] at getRun
          obtain ⟨currentEq, stateEq⟩ := EStateM.Result.ok.inj getRun
          subst currentEq stateEq
          try dsimp only
          cases fullHit : s₁.env.defEqCache[(rlo, rhi, eqCtx)]? with
          | some cached =>
              try dsimp only
              simp only [ReaderT.run_bind]
              refine EStateM.bind_cases ?_ ?_
              · intro cached? s₃ pureRun
                rw [pure_run] at pureRun
                obtain ⟨cachedEq, stateEq⟩ := EStateM.Result.ok.inj pureRun
                subst cachedEq stateEq
                try dsimp only
                cases cached with
                | false =>
                    simp only [Bool.false_eq_true, ↓reduceIte]
                    simp only [ReaderT.run_bind]
                    refine EStateM.bind_cases ?_ ?_
                    · intro value s₄ writeRun
                      rw [modify_run] at writeRun
                      obtain ⟨_, writeEq⟩ := EStateM.Result.ok.inj writeRun
                      try dsimp only
                      rw [pure_run]
                      subst writeEq
                      exact valid₁.ofDefEqUpdate ⟨_, _, rfl⟩ rfl rfl
                        (valid₁.semantics.defEq.ofInsert (lo, hi, eqCtx) false (.inr rfl)
                          (by split <;> first | exact .inr rfl | exact .inl rfl)
                          (fun h => nomatch h))
                        valid₁.semantics.equivalence
                    · intro err s h
                      rw [modify_run] at h
                      cases h
                | true =>
                    have claim := read (rootChain .full fullHit)
                    simp only [Bool.false_eq_true, ↓reduceIte]
                    simp only [ReaderT.run_bind]
                    refine EStateM.bind_cases ?_ ?_
                    · intro value s₄ writeRun
                      rw [modify_run] at writeRun
                      obtain ⟨_, writeEq⟩ := EStateM.Result.ok.inj writeRun
                      have valid₄ : CheckerInvariant.{u,v} resolve anchor entries source catalog
                          locals context bounds s₄ := by
                        subst writeEq
                        exact valid₁.ofDefEqUpdate ⟨_, _, rfl⟩ rfl rfl
                          (valid₁.semantics.defEq.ofInsert (lo, hi, eqCtx) true (.inr rfl)
                            (by split <;> first | exact .inr rfl | exact .inl rfl)
                            (fun _ => recordKey claim))
                          valid₁.semantics.equivalence
                      try dsimp only
                      refine EStateM.bind_cases ?_ ?_
                      · intro value s₅ unionRun
                        rw [modify_run] at unionRun
                        obtain ⟨_, unionEq⟩ := EStateM.Result.ok.inj unionRun
                        try dsimp only
                        rw [pure_run]
                        subst unionEq
                        exact ⟨valid₄.addEquiv (rootChain .full fullHit), claim⟩
                      · intro err s h
                        rw [modify_run] at h
                        cases h
                    · intro err s h
                      rw [modify_run] at h
                      cases h
              · intro err s h
                rw [pure_run] at h
                cases h
          | none =>
              try dsimp only
              split
              · simp only [ReaderT.run_bind]
                refine EStateM.bind_cases ?_ ?_
                · intro current s₃ getRun
                  rw [get_run] at getRun
                  obtain ⟨currentEq, stateEq⟩ := EStateM.Result.ok.inj getRun
                  subst currentEq stateEq
                  try dsimp only
                  cases cheapHit : s₁.env.defEqCheapCache[(rlo, rhi, eqCtx)]? with
                  | some cached =>
                      try dsimp only
                      simp only [ReaderT.run_bind]
                      refine EStateM.bind_cases ?_ ?_
                      · intro cached? s₄ pureRun
                        rw [pure_run] at pureRun
                        obtain ⟨cachedEq, stateEq⟩ := EStateM.Result.ok.inj pureRun
                        subst cachedEq stateEq
                        try dsimp only
                        cases cached with
                        | false =>
                            simp only [Bool.false_eq_true, ↓reduceIte]
                            simp only [ReaderT.run_bind]
                            refine EStateM.bind_cases ?_ ?_
                            · intro value s₅ writeRun
                              rw [modify_run] at writeRun
                              obtain ⟨_, writeEq⟩ := EStateM.Result.ok.inj writeRun
                              try dsimp only
                              rw [pure_run]
                              subst writeEq
                              exact valid₁.ofDefEqUpdate ⟨_, _, rfl⟩ rfl rfl
                                (valid₁.semantics.defEq.ofInsert (lo, hi, eqCtx) false (.inl rfl)
                                  (.inr rfl) (fun h => nomatch h))
                                valid₁.semantics.equivalence
                            · intro err s h
                              rw [modify_run] at h
                              cases h
                        | true =>
                            have claim := read (rootChain .cheap cheapHit)
                            simp only [↓reduceIte]
                            simp only [ReaderT.run_bind]
                            refine EStateM.bind_cases ?_ ?_
                            · intro value s₅ writeRun
                              rw [modify_run] at writeRun
                              obtain ⟨_, writeEq⟩ := EStateM.Result.ok.inj writeRun
                              have valid₅ : CheckerInvariant.{u,v} resolve anchor entries source
                                  catalog locals context bounds s₅ := by
                                subst writeEq
                                exact valid₁.ofDefEqUpdate ⟨_, _, rfl⟩ rfl rfl
                                  (valid₁.semantics.defEq.ofInsert (lo, hi, eqCtx) true (.inr rfl)
                                    (.inr rfl) (fun _ => recordKey claim))
                                  valid₁.semantics.equivalence
                              try dsimp only
                              refine EStateM.bind_cases ?_ ?_
                              · intro value s₆ unionRun
                                rw [modify_run] at unionRun
                                obtain ⟨_, unionEq⟩ := EStateM.Result.ok.inj unionRun
                                have valid₆ : CheckerInvariant.{u,v} resolve anchor entries source
                                    catalog locals context bounds s₆ := by
                                  subst unionEq
                                  exact valid₅.addEquiv (rootChain .cheap cheapHit)
                                try dsimp only
                                rw [pure_run]
                                exact ⟨valid₆, claim⟩
                              · intro err s h
                                rw [modify_run] at h
                                cases h
                            · intro err s h
                              rw [modify_run] at h
                              cases h
                      · intro err s h
                        rw [pure_run] at h
                        cases h
                  | none =>
                      try dsimp only
                      simp only [ReaderT.run_bind]
                      refine EStateM.bind_cases ?_ ?_
                      · intro cached? s₄ pureRun
                        rw [pure_run] at pureRun
                        obtain ⟨cachedEq, stateEq⟩ := EStateM.Result.ok.inj pureRun
                        subst cachedEq stateEq
                        try dsimp only
                        exact tail s₁ valid₁
                      · intro err s h
                        rw [pure_run] at h
                        cases h
                · intro err s h
                  rw [get_run] at h
                  cases h
              · simp only [ReaderT.run_bind]
                refine EStateM.bind_cases ?_ ?_
                · intro cached? s₃ pureRun
                  rw [pure_run] at pureRun
                  obtain ⟨cachedEq, stateEq⟩ := EStateM.Result.ok.inj pureRun
                  subst cachedEq stateEq
                  try dsimp only
                  exact tail s₁ valid₁
                · intro err s h
                  rw [pure_run] at h
                  cases h
        · intro err s h
          rw [get_run] at h
          cases h
      · exact tail s₁ valid₁
    · exact tail s₁ valid₁
  · intro err s h
    have h' : TcM.withEquiv _ before = .error err s := h
    rw [withEquiv_eq] at h'
    cases h'


end Charged

/-! ### Direct cache hits at the entry -/

section EntryWrites

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {anchor entries : Model.Environment β} {source : Ixon.Env}
  {catalog : List (SourceCacheRequest source)} {locals : List FVarId}
  {context : Model.Context β} {bounds : List VLevel}

/-- Copying a full-partition answer into the cheap partition preserves the
invariant: a positive answer is already recorded at that key. -/
theorem CheckerInvariant.copyToCheap {state : TcState .anon}
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds state)
    (key : Address × Address × Address) (answer : Bool)
    (hit : state.env.defEqCache[key]? = some answer) :
    CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds
      {state with env := {state.env with defEqCheapCache := state.env.defEqCheapCache.insert key answer}} :=
  valid.ofDefEqUpdate ⟨_, _, rfl⟩ rfl rfl
    (valid.semantics.defEq.ofInsert key answer (.inl rfl) (.inr rfl) fun positive =>
      valid.semantics.defEq .full key (positive ▸ hit))
    valid.semantics.equivalence

/-- Promoting a positive cheap-partition answer to the full partition and the
manager preserves the invariant. -/
theorem CheckerInvariant.promoteCheapHit {state : TcState .anon}
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds state)
    (key : Address × Address × Address) (hit : state.env.defEqCheapCache[key]? = some true)
    {left right : EqKey} (chain : EqKeyChain.{u,v} resolve entries left right) :
    CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds
      {state with
        env := {state.env with defEqCache := state.env.defEqCache.insert key true}
        equivManager := state.equivManager.addEquiv left right} :=
  valid.ofDefEqUpdate ⟨_, _, rfl⟩ rfl rfl
    (valid.semantics.defEq.ofInsert key true (.inr rfl) (.inl rfl) fun _ =>
      valid.semantics.defEq .cheap key hit)
    (valid.semantics.equivalence.addEquiv chain)

end EntryWrites

/-! ### The seam and the assembled entry -/

section Seams

variable {β : Type u} (resolve : Address → Option (ConstRef β))
  (anchor entries : Model.Environment β) (source : Ixon.Env)
  (catalog : List (SourceCacheRequest source))

/-- What the direct tiers leave open. `inner` is the remaining recursive tail
after the quick structural probe, the obligation of the reducing tiers.
`transport` reads a certified chain of memo edges at the caller's
registration. `sameRawAnnotations` is the annotation discipline of the hash
path: readings of one raw term that the checker compares carry equal binder
annotations. `binders` are the binder-case premises. The last three are
boundaries of the set model rather than tier obligations: the model interprets
binder annotations, records memo entries at the registration where they were
proved, and supplies only whole-term typing to the contracts. -/
structure DefEqSeamAssumptions (depth : Nat) : Prop where
  inner : ∀ left right, SoundConversion.{u,v} resolve anchor entries source catalog left right
    ((RecM.isDefEqInnerAfterQuick left right).run (methodsN depth))
  transport : DefEqMemoTransport.{u,v} resolve anchor entries source catalog
  sameRawAnnotations : ∀ (context : Model.Context β) (a b : AExpr β), a.erase = b.erase →
    (∃ type, TypingClaim.{u,v} entries context a type) →
    (∃ type, TypingClaim.{u,v} entries context b type) → a.annotations = b.annotations
  binders : DefEqBinderAssumptions.{u,v} resolve anchor entries

end Seams

section Entry

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {anchor entries : Model.Environment β} {source : Ixon.Env}
  {catalog : List (SourceCacheRequest source)} {support : KExpr .anon → Prop}

/-- The recursive inner tiers: the quick structural probe, then the
remaining tail under its contract. -/
theorem isDefEqInner_sound {methods : Methods .anon}
    (recursive : DefEqContract.{u,v} resolve anchor entries source catalog methods)
    (frames : MethodsLocalState methods)
    (binders : DefEqBinderAssumptions.{u,v} resolve anchor entries)
    (resources : DefEqTierResources.{u,v} resolve anchor entries source catalog support)
    (inner : ∀ left right, SoundConversion.{u,v} resolve anchor entries source catalog left right
      ((RecM.isDefEqInnerAfterQuick left right).run methods))
    {locals : List FVarId} {context : Model.Context β} {bounds : List VLevel} {before : TcState .anon}
    {left right : KExpr .anon} {a b : AExpr β}
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (leftMember : support left) (rightMember : support right)
    (leftReads : readScopedExpr? resolve locals left = some a.erase)
    (leftTyped : ∃ type, TypingClaim.{u,v} entries context a type)
    (rightReads : readScopedExpr? resolve locals right = some b.erase)
    (rightTyped : ∃ type, TypingClaim.{u,v} entries context b type) :
    ConversionPost.{u,v} resolve anchor entries source catalog locals context bounds a b
      ((RecM.isDefEqInner left right).run methods before) := by
  have quick := quickDefEq_sound recursive frames binders resources valid leftMember rightMember
    leftReads leftTyped rightReads rightTyped
  unfold RecM.isDefEqInner
  simp only [ReaderT.run_bind]
  refine EStateM.bind_cases ?_ ?_
  · intro answer middle quickRun
    rw [quickRun] at quick
    cases answer with
    | true =>
        simp only [↓reduceIte]
        rw [pure_run]
        exact quick
    | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact inner left right locals context bounds middle a b quick leftReads leftTyped rightReads
          rightTyped
  · intro err middle quickRun
    rw [quickRun] at quick
    exact quick

/-- The conversion entry under the contracts of its recursive callbacks: the
hash path, the equivalence-manager query, both direct cache partitions, the
representative probe, and the charged recursive tail through the quick
structural tier, with the deeper tiers abstracted by `inner`. -/
theorem isDefEq_sound {methods : Methods .anon}
    (recursive : DefEqContract.{u,v} resolve anchor entries source catalog methods)
    (frames : MethodsLocalState methods)
    (transport : DefEqMemoTransport.{u,v} resolve anchor entries source catalog)
    (sameRawAnnotations : ∀ (context : Model.Context β) (a b : AExpr β), a.erase = b.erase →
      (∃ type, TypingClaim.{u,v} entries context a type) →
      (∃ type, TypingClaim.{u,v} entries context b type) → a.annotations = b.annotations)
    (binders : DefEqBinderAssumptions.{u,v} resolve anchor entries)
    (resources : DefEqTierResources.{u,v} resolve anchor entries source catalog support)
    (inner : ∀ left right, SoundConversion.{u,v} resolve anchor entries source catalog left right
      ((RecM.isDefEqInnerAfterQuick left right).run methods))
    (left right : KExpr .anon) (leftMember : support left) (rightMember : support right) :
    SoundConversion.{u,v} resolve anchor entries source catalog left right
      ((RecM.isDefEq left right).run methods) := by
  intro locals context bounds before a b valid leftReads leftTyped rightReads rightTyped
  have innerPost : ∀ state,
      CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds state →
      ConversionPost.{u,v} resolve anchor entries source catalog locals context bounds a b
        ((RecM.isDefEqInner left right).run methods state) :=
    fun _ valid' => isDefEqInner_sound recursive frames binders resources inner valid' leftMember
      rightMember leftReads leftTyped rightReads rightTyped
  unfold RecM.isDefEq
  simp only [ReaderT.run_bind, ReaderT.run_monadLift]
  refine EStateM.bind_cases ?_ ?_
  · intro value s₀ traceRun
    have traceRun' : TcM.stepTrace _ _ before = .ok value s₀ := traceRun
    rw [stepTrace_eq] at traceRun'
    obtain ⟨_, stateEq⟩ := EStateM.Result.ok.inj traceRun'
    subst stateEq
    try dsimp only
    refine EStateM.bind_cases ?_ ?_
    · intro value s₁ statsRun
      cases value
      have valid₁ := valid.afterBumpStats (fun s => {s with deqCalls := s.deqCalls + 1})
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) statsRun
      try dsimp only
      split
      · rename_i equal
        rw [pure_run]
        have same := beq_readScopedExpr? (resolve := resolve) (locals := locals) (depth := 0)
          (resources.faithful left right leftMember rightMember) (by rw [KExpr.beq_def]; exact equal)
        have erased : a.erase = b.erase :=
          Option.some.inj (leftReads.symm.trans (same.trans rightReads))
        cases AExpr.eq_of_erase_annotations erased
          (sameRawAnnotations context a b erased leftTyped rightTyped)
        exact ⟨valid₁, ConversionClaim.refl a⟩
      · simp only [ReaderT.run_bind, ReaderT.run_monadLift]
        refine EStateM.bind_cases ?_ ?_
        · intro eqCtx s₂ keyRun
          have keyRun' : TcM.defEqCtxKey left right s₁ = .ok eqCtx s₂ := keyRun
          have valid₂ := valid₁.defEqCtxKey keyRun'
          have origin := DefEqKeyOrigin.ofRun valid₁ keyRun'
          have read : EqKeyChain.{u,v} resolve entries ⟨left.addr, eqCtx, max left.lbr right.lbr, left.lbr⟩
              ⟨right.addr, eqCtx, max left.lbr right.lbr, right.lbr⟩ →
              ConversionClaim.{u,v} entries context a b :=
            transport locals context bounds left right a b eqCtx origin leftReads leftTyped rightReads
              rightTyped
          try dsimp only
          refine EStateM.bind_cases ?_ ?_
          · intro isEq s₃ queryRun
            have queryRun' : TcM.withEquiv _ s₂ = .ok isEq s₃ := queryRun
            rw [withEquiv_eq] at queryRun'
            obtain ⟨isEqEq, stateEq⟩ := EStateM.Result.ok.inj queryRun'
            have query := valid₂.semantics.equivalence.isEquiv
              ⟨left.addr, eqCtx, max left.lbr right.lbr, left.lbr⟩
              ⟨right.addr, eqCtx, max left.lbr right.lbr, right.lbr⟩
            have valid₃ : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context
                bounds s₃ := by
              subst stateEq
              exact valid₂.ofDefEqUpdate ⟨_, _, rfl⟩ rfl rfl (valid₂.semantics.defEq.setManager _)
                query.1
            try dsimp only
            cases isEq with
            | true =>
                simp only [↓reduceIte]
                rw [pure_run]
                exact ⟨valid₃, read (query.2 isEqEq)⟩
            | false =>
                simp only [Bool.false_eq_true, ↓reduceIte]
                rcases canonical : canonicalPair left.addr right.addr with ⟨lo, hi⟩
                try dsimp only
                simp only [ReaderT.run_bind]
                refine EStateM.bind_cases ?_ ?_
                · intro current s₃' getRun
                  rw [get_run] at getRun
                  obtain ⟨currentEq, stateEq⟩ := EStateM.Result.ok.inj getRun
                  subst currentEq stateEq
                  try dsimp only
                  refine EStateM.bind_cases ?_ ?_
                  · intro current s₃' getRun
                    rw [get_run] at getRun
                    obtain ⟨currentEq, stateEq⟩ := EStateM.Result.ok.inj getRun
                    subst currentEq stateEq
                    try dsimp only
                    cases fullHit : s₃.env.defEqCache[(lo, hi, eqCtx)]? with
                    | some cached =>
                        have hitChain : cached = true →
                            EqKeyChain.{u,v} resolve entries
                              ⟨left.addr, eqCtx, max left.lbr right.lbr, left.lbr⟩
                              ⟨right.addr, eqCtx, max left.lbr right.lbr, right.lbr⟩ :=
                          fun positive => .edge (valid₃.semantics.defEq.hitEdge .full canonical
                            (positive ▸ fullHit))
                        try dsimp only
                        split
                        · simp only [ReaderT.run_bind]
                          refine EStateM.bind_cases ?_ ?_
                          · intro value s₄ copyRun
                            rw [modify_run] at copyRun
                            obtain ⟨_, stateEq⟩ := EStateM.Result.ok.inj copyRun
                            subst stateEq
                            have valid₄ := valid₃.copyToCheap (lo, hi, eqCtx) cached fullHit
                            try dsimp only
                            cases cached with
                            | false =>
                                simp only [Bool.false_eq_true, ↓reduceIte]
                                rw [pure_run]
                                exact valid₄
                            | true =>
                                simp only [↓reduceIte]
                                simp only [ReaderT.run_bind]
                                refine EStateM.bind_cases ?_ ?_
                                · intro value s₅ unionRun
                                  rw [modify_run] at unionRun
                                  obtain ⟨_, stateEq⟩ := EStateM.Result.ok.inj unionRun
                                  subst stateEq
                                  try dsimp only
                                  rw [pure_run]
                                  exact ⟨valid₄.addEquiv (hitChain rfl), read (hitChain rfl)⟩
                                · intro err s h
                                  rw [modify_run] at h
                                  cases h
                          · intro err s h
                            rw [modify_run] at h
                            cases h
                        · cases cached with
                          | false =>
                              simp only [Bool.false_eq_true, ↓reduceIte]
                              rw [pure_run]
                              exact valid₃
                          | true =>
                              simp only [↓reduceIte]
                              simp only [ReaderT.run_bind]
                              refine EStateM.bind_cases ?_ ?_
                              · intro value s₄ unionRun
                                rw [modify_run] at unionRun
                                obtain ⟨_, stateEq⟩ := EStateM.Result.ok.inj unionRun
                                subst stateEq
                                try dsimp only
                                rw [pure_run]
                                exact ⟨valid₃.addEquiv (hitChain rfl), read (hitChain rfl)⟩
                              · intro err s h
                                rw [modify_run] at h
                                cases h
                    | none =>
                        try dsimp only
                        split
                        · simp only [ReaderT.run_bind]
                          refine EStateM.bind_cases ?_ ?_
                          · intro current s₃' getRun
                            rw [get_run] at getRun
                            obtain ⟨currentEq, stateEq⟩ := EStateM.Result.ok.inj getRun
                            subst currentEq stateEq
                            try dsimp only
                            cases cheapHit : s₃.env.defEqCheapCache[(lo, hi, eqCtx)]? with
                            | some cached =>
                                try dsimp only
                                cases cached with
                                | false =>
                                    simp only [Bool.false_eq_true, ↓reduceIte]
                                    rw [pure_run]
                                    exact valid₃
                                | true =>
                                    have chain : EqKeyChain.{u,v} resolve entries
                                        ⟨left.addr, eqCtx, max left.lbr right.lbr, left.lbr⟩
                                        ⟨right.addr, eqCtx, max left.lbr right.lbr, right.lbr⟩ :=
                                      .edge (valid₃.semantics.defEq.hitEdge .cheap canonical cheapHit)
                                    simp only [↓reduceIte]
                                    simp only [ReaderT.run_bind]
                                    refine EStateM.bind_cases ?_ ?_
                                    · intro value s₄ promoteRun
                                      rw [modify_run] at promoteRun
                                      obtain ⟨_, stateEq⟩ := EStateM.Result.ok.inj promoteRun
                                      subst stateEq
                                      try dsimp only
                                      rw [pure_run]
                                      exact ⟨valid₃.promoteCheapHit (lo, hi, eqCtx) cheapHit chain,
                                        read chain⟩
                                    · intro err s h
                                      rw [modify_run] at h
                                      cases h
                            | none =>
                                try dsimp only
                                exact isDefEqAfterDirectCacheMiss_sound transport innerPost origin
                                  canonical valid₃ leftReads leftTyped rightReads rightTyped
                          · intro err s h
                            rw [get_run] at h
                            cases h
                        · exact isDefEqAfterDirectCacheMiss_sound transport innerPost origin canonical
                            valid₃ leftReads leftTyped rightReads rightTyped
                  · intro err s h
                    rw [get_run] at h
                    cases h
                · intro err s h
                  rw [get_run] at h
                  cases h
          · intro err s h
            have h' : TcM.withEquiv _ s₂ = .error err s := h
            rw [withEquiv_eq] at h'
            cases h'
        · intro err s h
          have h' : TcM.ctxAddrForLbr (max left.lbr right.lbr) s₁ = .error err s := h
          obtain ⟨addr, after, ok⟩ := ctxAddrForLbr_ok (max left.lbr right.lbr) s₁
          rw [ok] at h'
          cases h'
    · intro err s h
      have h' : TcM.bumpStats _ before = .error err s := h
      rw [bumpStats_eq] at h'
      cases h'
  · intro err s h
    have h' : TcM.stepTrace _ _ before = .error err s := h
    rw [stepTrace_eq] at h'
    cases h'

/-- The `StepContracts.isDefEq` field modulo the seam: every operand pair in
the resource support, at the production table of the recursive callbacks. -/
theorem isDefEq_direct_tiers {depth : Nat}
    (recursive : MethodContracts.{u,v} resolve anchor entries source catalog (methodsN depth))
    (seams : DefEqSeamAssumptions.{u,v} resolve anchor entries source catalog depth)
    (resources : DefEqTierResources.{u,v} resolve anchor entries source catalog support)
    (left right : KExpr .anon) (leftMember : support left) (rightMember : support right) :
    SoundConversion.{u,v} resolve anchor entries source catalog left right
      ((RecM.isDefEq left right).run (methodsN depth)) :=
  isDefEq_sound recursive.toDefEqContract (MethodsLocalState.methodsN depth) seams.transport
    seams.sameRawAnnotations seams.binders resources seams.inner left right leftMember rightMember

/-- The exact field shape, with the resources stated for every expression. -/
theorem StepContracts.isDefEq_of_direct_tiers {depth : Nat}
    (seams : DefEqSeamAssumptions.{u,v} resolve anchor entries source catalog depth)
    (resources : DefEqTierResources.{u,v} resolve anchor entries source catalog fun _ => True) :
    MethodContracts.{u,v} resolve anchor entries source catalog (methodsN depth) →
    ∀ left right, SoundConversion.{u,v} resolve anchor entries source catalog left right
      ((RecM.isDefEq left right).run (methodsN depth)) :=
  fun recursive left right => isDefEq_direct_tiers recursive seams resources left right trivial trivial

end Entry

end Ix.Kernel.Consistency
