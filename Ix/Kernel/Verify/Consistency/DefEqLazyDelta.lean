/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.DefEqFinal

/-!
# The lazy-delta tier and the assembled reducing tiers

Tier 4 of production conversion is a bounded loop over operand pairs: the
Nat-offset probe, the gated Nat reducers, the accelerators, delta
classification of both heads, the asymmetric projection-app probe, rank
dispatch, the guarded same-head spine attempt, one- or two-sided unfolding
followed by no-delta normalization, and the finishing address and quick
checks. This module proves the loop sound against the checker invariant: the
loop state carries readable, typed operands convertible to the originals, an
answer `true` carries their conversion, and a stopped pair keeps the state
invariant. The optional reducers and probes are the seams of
`DefEqReducingSeams`; the structural pieces are proved: the finishing checks
through the hash path and the quick tier, the same-head spine comparison by
constant-instance and argument congruence, the speculative attempt's fuel
bookkeeping, the rejection-only cache as a memo probe whose write carries no
claim, and every lookup-based classification and ranking.

The last section assembles `isDefEqInnerAfterQuick_sound` from the upper
chain, the loop, and the stopped continuation, and states the corollary that
discharges the `inner` field of `DefEqSeamAssumptions`: the conversion body
is sound modulo `DefEqReducingSeams`, the memo transport, the annotation
discipline, the binder premises, and the finite resources.
-/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

/-! ### Outcomes of the loop -/

section LoopPosts

variable {β : Type u} (resolve : Address → Option (ConstRef β))
  (anchor entries : Model.Environment β) (source : Ixon.Env)
  (catalog : List (SourceCacheRequest source)) (locals : List FVarId)
  (context : Model.Context β) (bounds : List VLevel)

/-- The loop state: an invariant state and readable, typed operands
convertible to the originals. -/
def LazyPairInvariant (a b : AExpr β) (pair : KExpr .anon × KExpr .anon) (state : TcState .anon) :
    Prop :=
  CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds state ∧
  ∃ x y : AExpr β,
    readScopedExpr? resolve locals pair.1 = some x.erase ∧
    (∃ type, TypingClaim.{u,v} entries context x type) ∧
    readScopedExpr? resolve locals pair.2 = some y.erase ∧
    (∃ type, TypingClaim.{u,v} entries context y type) ∧
    ConversionClaim.{u,v} entries context a x ∧ ConversionClaim.{u,v} entries context b y

/-- The loop's outcome: an answer `true` carries the conversion, a stopped
pair is a loop state. -/
def LazyDeltaPost (a b : AExpr β) :
    EStateM.Result (TcError .anon) (TcState .anon) (LazyDeltaLoopResult .anon) → Prop
  | .ok (.answer true) after =>
      CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds after ∧
      ConversionClaim.{u,v} entries context a b
  | .ok (.answer false) after =>
      CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds after
  | .ok (.stopped left right) after =>
      LazyPairInvariant.{u,v} resolve anchor entries source catalog locals context bounds a b
        (left, right) after
  | .error _ after =>
      CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds after

/-- One iteration's outcome: a continued pair is a loop state, a terminal
result is a loop outcome. -/
def LazyStepPost (a b : AExpr β) :
    EStateM.Result (TcError .anon) (TcState .anon)
      (RecM.BoundedStep (KExpr .anon × KExpr .anon) (LazyDeltaLoopResult .anon)) → Prop
  | .ok (.next pair) after =>
      LazyPairInvariant.{u,v} resolve anchor entries source catalog locals context bounds a b pair after
  | .ok (.done result) after =>
      LazyDeltaPost.{u,v} resolve anchor entries source catalog locals context bounds a b
        (.ok result after)
  | .error _ after =>
      CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds after

end LoopPosts

section LoopLemmas

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {anchor entries : Model.Environment β} {source : Ixon.Env}
  {catalog : List (SourceCacheRequest source)} {locals : List FVarId}
  {context : Model.Context β} {bounds : List VLevel}

theorem LazyPairInvariant.refl {state : TcState .anon} {left right : KExpr .anon} {x y : AExpr β}
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds state)
    (leftReads : readScopedExpr? resolve locals left = some x.erase)
    (leftTyped : ∃ type, TypingClaim.{u,v} entries context x type)
    (rightReads : readScopedExpr? resolve locals right = some y.erase)
    (rightTyped : ∃ type, TypingClaim.{u,v} entries context y type) :
    LazyPairInvariant.{u,v} resolve anchor entries source catalog locals context bounds x y
      (left, right) state :=
  ⟨valid, x, y, leftReads, leftTyped, rightReads, rightTyped, ConversionClaim.refl x,
    ConversionClaim.refl y⟩

theorem LazyPairInvariant.lift {a b x y : AExpr β} {pair : KExpr .anon × KExpr .anon}
    {state : TcState .anon}
    (claimA : ConversionClaim.{u,v} entries context a x) (claimB : ConversionClaim.{u,v} entries context b y)
    (invariant : LazyPairInvariant.{u,v} resolve anchor entries source catalog locals context bounds x y
      pair state) :
    LazyPairInvariant.{u,v} resolve anchor entries source catalog locals context bounds a b pair state := by
  obtain ⟨valid, x', y', xReads, xTyped, yReads, yTyped, claimX, claimY⟩ := invariant
  exact ⟨valid, x', y', xReads, xTyped, yReads, yTyped, claimA.trans claimX, claimB.trans claimY⟩

theorem LazyDeltaPost.lift {a b x y : AExpr β}
    {result : EStateM.Result (TcError .anon) (TcState .anon) (LazyDeltaLoopResult .anon)}
    (claimA : ConversionClaim.{u,v} entries context a x) (claimB : ConversionClaim.{u,v} entries context b y)
    (post : LazyDeltaPost.{u,v} resolve anchor entries source catalog locals context bounds x y result) :
    LazyDeltaPost.{u,v} resolve anchor entries source catalog locals context bounds a b result := by
  cases result with
  | error err after => exact post
  | ok value after =>
      cases value with
      | answer answer =>
          cases answer with
          | false => exact post
          | true => exact ⟨post.1, claimA.trans (post.2.trans claimB.symm)⟩
      | stopped left right => exact LazyPairInvariant.lift claimA claimB post

theorem LazyStepPost.lift {a b x y : AExpr β}
    {result : EStateM.Result (TcError .anon) (TcState .anon)
      (RecM.BoundedStep (KExpr .anon × KExpr .anon) (LazyDeltaLoopResult .anon))}
    (claimA : ConversionClaim.{u,v} entries context a x) (claimB : ConversionClaim.{u,v} entries context b y)
    (post : LazyStepPost.{u,v} resolve anchor entries source catalog locals context bounds x y result) :
    LazyStepPost.{u,v} resolve anchor entries source catalog locals context bounds a b result := by
  cases result with
  | error err after => exact post
  | ok value after =>
      cases value with
      | next pair => exact LazyPairInvariant.lift claimA claimB post
      | done result => exact LazyDeltaPost.lift claimA claimB post

/-- A branch on any decidable condition, for any outcome property. -/
theorem RecM.ite_post {α : Type} {Post : EStateM.Result (TcError .anon) (TcState .anon) α → Prop}
    {c : Prop} [Decidable c] {left right : RecM .anon α} {methods : Methods .anon} {before : TcState .anon}
    (thenSound : c → Post (left.run methods before)) (elseSound : ¬ c → Post (right.run methods before)) :
    Post ((if c then left else right).run methods before) := by
  by_cases h : c
  · rw [if_pos h]
    exact thenSound h
  · rw [if_neg h]
    exact elseSound h

/-- An answer through the recursive callback on a reduced left operand. -/
theorem LazyStepPost.ofCallLeft {methods : Methods .anon}
    (recursive : DefEqContract.{u,v} resolve anchor entries source catalog methods)
    {before : TcState .anon} {left right : KExpr .anon} {x x' y : AExpr β}
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (claim : ConversionClaim.{u,v} entries context x x')
    (leftReads : readScopedExpr? resolve locals left = some x'.erase)
    (leftTyped : ∃ type, TypingClaim.{u,v} entries context x' type)
    (rightReads : readScopedExpr? resolve locals right = some y.erase)
    (rightTyped : ∃ type, TypingClaim.{u,v} entries context y type) :
    LazyStepPost.{u,v} resolve anchor entries source catalog locals context bounds x y
      ((RecM.isDefEqCall left right >>= fun answer =>
        pure (RecM.BoundedStep.done (LazyDeltaLoopResult.answer answer))).run methods before) := by
  simp only [ReaderT.run_bind, isDefEqCall_run]
  have conv := recursive.isDefEq left right locals context bounds before x' y valid leftReads leftTyped
    rightReads rightTyped
  cases run : methods.isDefEq left right before with
  | error err after =>
      rw [EStateM.run_bind_error run]
      rw [run] at conv
      exact conv
  | ok answer after =>
      rw [EStateM.run_bind_ok run]
      rw [run] at conv
      rw [pure_run]
      cases answer with
      | false => exact conv
      | true => exact ⟨conv.1, claim.trans conv.2⟩

/-- An answer through the recursive callback on a reduced right operand. -/
theorem LazyStepPost.ofCallRight {methods : Methods .anon}
    (recursive : DefEqContract.{u,v} resolve anchor entries source catalog methods)
    {before : TcState .anon} {left right : KExpr .anon} {x y y' : AExpr β}
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (claim : ConversionClaim.{u,v} entries context y y')
    (leftReads : readScopedExpr? resolve locals left = some x.erase)
    (leftTyped : ∃ type, TypingClaim.{u,v} entries context x type)
    (rightReads : readScopedExpr? resolve locals right = some y'.erase)
    (rightTyped : ∃ type, TypingClaim.{u,v} entries context y' type) :
    LazyStepPost.{u,v} resolve anchor entries source catalog locals context bounds x y
      ((RecM.isDefEqCall left right >>= fun answer =>
        pure (RecM.BoundedStep.done (LazyDeltaLoopResult.answer answer))).run methods before) := by
  simp only [ReaderT.run_bind, isDefEqCall_run]
  have conv := recursive.isDefEq left right locals context bounds before x y' valid leftReads leftTyped
    rightReads rightTyped
  cases run : methods.isDefEq left right before with
  | error err after =>
      rw [EStateM.run_bind_error run]
      rw [run] at conv
      exact conv
  | ok answer after =>
      rw [EStateM.run_bind_ok run]
      rw [run] at conv
      rw [pure_run]
      cases answer with
      | false => exact conv
      | true => exact ⟨conv.1, conv.2.trans claim.symm⟩

end LoopLemmas

/-! ### Lookups -/

section Lookups

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {anchor entries : Model.Environment β} {source : Ixon.Env}
  {catalog : List (SourceCacheRequest source)} {locals : List FVarId}
  {context : Model.Context β} {bounds : List VLevel}

theorem isDelta_keeps {methods : Methods .anon} {before : TcState .anon}
    (resources : DefEqReducingResources.{u,v} resolve anchor entries source catalog)
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (id : KId .anon) :
    KeepsInvariant.{u,v} resolve anchor entries source catalog locals context bounds
      ((RecM.isDelta id).run methods before) := by
  unfold RecM.isDelta
  simp only [ReaderT.run_bind, ReaderT.run_monadLift, monadLift_self]
  refine KeepsInvariant.lookup valid (resources.lookup before locals context bounds valid id.addr) ?_
  intro value state
  split <;> (try split) <;> exact ⟨_, rfl⟩

theorem isRegular_keeps {methods : Methods .anon} {before : TcState .anon}
    (resources : DefEqReducingResources.{u,v} resolve anchor entries source catalog)
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (id : KId .anon) :
    KeepsInvariant.{u,v} resolve anchor entries source catalog locals context bounds
      ((RecM.isRegular id).run methods before) := by
  unfold RecM.isRegular
  simp only [ReaderT.run_bind, ReaderT.run_monadLift, monadLift_self]
  refine KeepsInvariant.lookup valid (resources.lookup before locals context bounds valid id.addr) ?_
  intro value state
  split <;> exact ⟨_, rfl⟩

theorem defRankId_keeps {methods : Methods .anon} {before : TcState .anon}
    (resources : DefEqReducingResources.{u,v} resolve anchor entries source catalog)
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (id : KId .anon) :
    KeepsInvariant.{u,v} resolve anchor entries source catalog locals context bounds
      ((RecM.defRankId id).run methods before) := by
  unfold RecM.defRankId
  simp only [ReaderT.run_bind, ReaderT.run_monadLift, monadLift_self]
  refine KeepsInvariant.lookup valid (resources.lookup before locals context bounds valid id.addr) ?_
  intro value state
  split <;> (try split) <;> (try split) <;> exact ⟨_, rfl⟩

theorem classifyDeltaHead_keeps {methods : Methods .anon} {before : TcState .anon}
    (resources : DefEqReducingResources.{u,v} resolve anchor entries source catalog)
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (term : KExpr .anon) :
    KeepsInvariant.{u,v} resolve anchor entries source catalog locals context bounds
      ((RecM.classifyDeltaHead term).run methods before) := by
  unfold RecM.classifyDeltaHead
  cases headConstId term with
  | some id => exact isDelta_keeps resources valid id
  | none =>
      rw [pure_run]
      exact valid

theorem rankDeltaHead_keeps {methods : Methods .anon} {before : TcState .anon}
    (resources : DefEqReducingResources.{u,v} resolve anchor entries source catalog)
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (head : Option (KId .anon)) :
    KeepsInvariant.{u,v} resolve anchor entries source catalog locals context bounds
      ((RecM.rankDeltaHead head).run methods before) := by
  unfold RecM.rankDeltaHead
  cases head with
  | some id => exact defRankId_keeps resources valid id
  | none =>
      rw [pure_run]
      exact valid

end Lookups

/-! ### The same-head spine attempt -/

section SameHead

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {anchor entries : Model.Environment β} {source : Ixon.Env}
  {catalog : List (SourceCacheRequest source)}

/-- Two spines with one constant head that pass the universe gate compare
by argument congruence. -/
theorem trySameHeadSpine_sound {depth : Nat}
    (recursive : MethodContracts.{u,v} resolve anchor entries source catalog (methodsN depth))
    (seams : DefEqReducingSeams.{u,v} resolve anchor entries source catalog depth)
    (resources : DefEqReducingResources.{u,v} resolve anchor entries source catalog)
    (left right : KExpr .anon) :
    SoundOptionalConversion.{u,v} resolve anchor entries source catalog left right
      ((RecM.trySameHeadSpine left right).run (methodsN depth)) := by
  intro locals context bounds before a b valid leftReads leftTyped rightReads rightTyped
  unfold RecM.trySameHeadSpine
  rcases spineA : left.collectSpine with ⟨aHead, aArgs⟩
  rcases spineB : right.collectSpine with ⟨bHead, bArgs⟩
  try dsimp only
  cases aHead
  case const aId aUs aInfo =>
    cases bHead
    case const bId bUs bInfo =>
      try dsimp only
      refine RecM.ite_post (fun _ => OptionalConversionPost.pureNone valid) fun mismatch => ?_
      simp at mismatch
      obtain ⟨sameHead, sizes⟩ := mismatch
      refine RecM.ite_post (fun _ => OptionalConversionPost.pureNone valid) fun gate => ?_
      simp at gate
      obtain ⟨aEq, bEq, aHeadReads, bHeadReads, _, _, lengths, readings⟩ :=
        spine_parts seams.appHereditary leftReads leftTyped rightReads rightTyped
          (by rw [spineA, spineB]; exact sizes)
      rw [spineA] at aHeadReads readings
      rw [spineB] at bHeadReads readings
      try simp only [ReaderT.run_bind]
      have spine := allDefEqSpineArgs_sound recursive.toDefEqContract (pairs := aArgs.zip bArgs)
        (by rw [Array.toList_zip]; exact readings) valid
      cases runS : (RecM.allDefEqSpineArgs (aArgs.zip bArgs)).run (methodsN depth) before with
      | error err s₁ =>
          rw [EStateM.run_bind_error runS]
          rw [runS] at spine
          exact spine
      | ok answer s₁ =>
          rw [EStateM.run_bind_ok runS]
          rw [runS] at spine
          cases answer with
          | false =>
              simp only [Bool.not_false, ↓reduceIte]
              exact OptionalConversionPost.pureNone spine
          | true =>
              obtain ⟨valid₁, claims⟩ := spine
              simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
              refine OptionalConversionPost.pureSome valid₁ true fun _ => ?_
              rw [aEq, bEq]
              exact ConversionClaim.appN
                (ConversionClaim.constInstances aHeadReads bHeadReads sameHead gate
                  (fun u _ v _ => resources.tiers.sorts u v aInfo bInfo trivial trivial))
                lengths claims
    all_goals
      try dsimp only
      exact OptionalConversionPost.pureNone valid
  all_goals
    try dsimp only
    exact OptionalConversionPost.pureNone valid

/-- The speculative attempt: a local fuel slice around the attempt, restored
afterwards, with exhaustion reported as a miss. -/
theorem trySameHeadSpineSpeculative_sound {depth : Nat}
    (recursive : MethodContracts.{u,v} resolve anchor entries source catalog (methodsN depth))
    (seams : DefEqReducingSeams.{u,v} resolve anchor entries source catalog depth)
    (resources : DefEqReducingResources.{u,v} resolve anchor entries source catalog)
    (left right : KExpr .anon) :
    SoundOptionalConversion.{u,v} resolve anchor entries source catalog left right
      ((RecM.trySameHeadSpineSpeculative left right).run (methodsN depth)) := by
  intro locals context bounds before a b valid leftReads leftTyped rightReads rightTyped
  unfold RecM.trySameHeadSpineSpeculative
  try simp only [ReaderT.run_bind]
  rw [EStateM.run_bind_ok (get_run (methodsN depth) before)]
  try dsimp only
  refine RecM.ite_post (fun _ => OptionalConversionPost.pureNone valid) fun _ => ?_
  try simp only [ReaderT.run_bind]
  rw [EStateM.run_bind_ok (modify_run _ (methodsN depth) before)]
  try dsimp only
  have valid₁ : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds
      {before with recFuel := min before.recFuel sameHeadSpeculationAttemptFuel} :=
    valid.ofDefEqScalars rfl rfl rfl rfl
  have attempt := trySameHeadSpine_sound recursive seams resources left right locals context bounds
    {before with recFuel := min before.recFuel sameHeadSpeculationAttemptFuel} a b valid₁ leftReads
    leftTyped rightReads rightTyped
  have caught := tryExcept_run (RecM.trySameHeadSpine left right) (methodsN depth)
    {before with recFuel := min before.recFuel sameHeadSpeculationAttemptFuel}
  cases runT : (RecM.trySameHeadSpine left right).run (methodsN depth)
      {before with recFuel := min before.recFuel sameHeadSpeculationAttemptFuel} with
  | error err s₁ =>
      rw [runT] at caught attempt
      rw [EStateM.run_bind_ok caught]
      try dsimp only
      try simp only [ReaderT.run_bind]
      rw [EStateM.run_bind_ok (get_run (methodsN depth) s₁)]
      try dsimp only
      rw [EStateM.run_bind_ok (modify_run _ (methodsN depth) s₁)]
      try dsimp only
      cases err <;> (try dsimp only) <;> first
        | (rw [pure_run]; exact attempt.ofDefEqScalars rfl rfl rfl rfl)
        | (rw [throw_run]; exact attempt.ofDefEqScalars rfl rfl rfl rfl)
  | ok answer s₁ =>
      rw [runT] at caught attempt
      rw [EStateM.run_bind_ok caught]
      try dsimp only
      try simp only [ReaderT.run_bind]
      rw [EStateM.run_bind_ok (get_run (methodsN depth) s₁)]
      try dsimp only
      rw [EStateM.run_bind_ok (modify_run _ (methodsN depth) s₁)]
      try dsimp only
      rw [pure_run]
      cases answer with
      | none => exact attempt.ofDefEqScalars rfl rfl rfl rfl
      | some answer =>
          cases answer with
          | false => exact attempt.ofDefEqScalars rfl rfl rfl rfl
          | true => exact ⟨attempt.1.ofDefEqScalars rfl rfl rfl rfl, attempt.2⟩

/-- The guarded attempt behind the rejection-only cache: a cached rejection
skips the attempt, a genuine miss records it, and the record carries no claim. -/
theorem trySameHeadSpineCached_sound {depth : Nat}
    (recursive : MethodContracts.{u,v} resolve anchor entries source catalog (methodsN depth))
    (seams : DefEqReducingSeams.{u,v} resolve anchor entries source catalog depth)
    (resources : DefEqReducingResources.{u,v} resolve anchor entries source catalog)
    (speculative : Bool) (left right : KExpr .anon) :
    SoundOptionalConversion.{u,v} resolve anchor entries source catalog left right
      ((RecM.trySameHeadSpineCached speculative left right).run (methodsN depth)) := by
  intro locals context bounds before a b valid leftReads leftTyped rightReads rightTyped
  unfold RecM.trySameHeadSpineCached
  simp only [ReaderT.run_bind, ReaderT.run_monadLift, monadLift_self]
  obtain ⟨ctxAddr, s₁, keyRun⟩ := ctxAddrForLbr_ok (max left.lbr right.lbr) before
  have keyRun' : TcM.defEqCtxKey left right before = .ok ctxAddr s₁ := keyRun
  rw [EStateM.run_bind_ok keyRun']
  have valid₁ := valid.defEqCtxKey keyRun'
  try dsimp only
  rw [EStateM.run_bind_ok (get_run (methodsN depth) s₁)]
  try dsimp only
  refine RecM.ite_post (fun _ => OptionalConversionPost.pureNone valid₁) fun _ => ?_
  have attempt : OptionalConversionPost.{u,v} resolve anchor entries source catalog locals context bounds
      a b ((if speculative = true then RecM.trySameHeadSpineSpeculative left right
        else RecM.trySameHeadSpine left right).run (methodsN depth) s₁) :=
    RecM.ite_post
      (fun _ => trySameHeadSpineSpeculative_sound recursive seams resources left right locals context
        bounds s₁ a b valid₁ leftReads leftTyped rightReads rightTyped)
      (fun _ => trySameHeadSpine_sound recursive seams resources left right locals context bounds s₁ a b
        valid₁ leftReads leftTyped rightReads rightTyped)
  try simp only [ReaderT.run_bind]
  cases runA : (if speculative = true then RecM.trySameHeadSpineSpeculative left right
      else RecM.trySameHeadSpine left right).run (methodsN depth) s₁ with
  | error err s₂ =>
      rw [EStateM.run_bind_error runA]
      rw [runA] at attempt
      exact attempt
  | ok answer s₂ =>
      rw [EStateM.run_bind_ok runA]
      rw [runA] at attempt
      cases answer with
      | some answer =>
          try dsimp only
          rw [pure_run]
          exact attempt
      | none =>
          try dsimp only
          try simp only [ReaderT.run_bind]
          rw [EStateM.run_bind_ok (modify_run _ (methodsN depth) s₂)]
          try dsimp only
          rw [pure_run]
          exact attempt.ofDefEqFailure _

end SameHead

/-! ### The loop iteration -/

section Iteration

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {anchor entries : Model.Environment β} {source : Ixon.Env}
  {catalog : List (SourceCacheRequest source)} {locals : List FVarId}
  {context : Model.Context β} {bounds : List VLevel}

/-- The finishing checks of a productive iteration. -/
theorem finishDefEqLazyDeltaStep_sound {depth : Nat}
    (recursive : MethodContracts.{u,v} resolve anchor entries source catalog (methodsN depth))
    (annotations : SameRawAnnotations.{u,v} entries)
    (binders : DefEqBinderAssumptions.{u,v} resolve anchor entries)
    (resources : DefEqReducingResources.{u,v} resolve anchor entries source catalog)
    {before : TcState .anon} {left right : KExpr .anon} {x y : AExpr β}
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (leftReads : readScopedExpr? resolve locals left = some x.erase)
    (leftTyped : ∃ type, TypingClaim.{u,v} entries context x type)
    (rightReads : readScopedExpr? resolve locals right = some y.erase)
    (rightTyped : ∃ type, TypingClaim.{u,v} entries context y type) :
    LazyStepPost.{u,v} resolve anchor entries source catalog locals context bounds x y
      ((RecM.finishDefEqLazyDeltaStep left right).run (methodsN depth) before) := by
  unfold RecM.finishDefEqLazyDeltaStep
  refine RecM.ite_post (fun same => ?_) fun _ => ?_
  · rw [pure_run]
    exact ⟨valid, ConversionClaim.ofAddrEq (resources.tiers.faithful left right trivial trivial) annotations
      same leftReads leftTyped rightReads rightTyped⟩
  · simp only [ReaderT.run_bind]
    have quick := quickDefEq_sound recursive.toDefEqContract (MethodsLocalState.methodsN depth) binders
      resources.tiers valid trivial trivial leftReads leftTyped rightReads rightTyped
    cases runQ : (RecM.quickDefEq left right).run (methodsN depth) before with
    | error err s₁ =>
        rw [EStateM.run_bind_error runQ]
        rw [runQ] at quick
        exact quick
    | ok answer s₁ =>
        rw [EStateM.run_bind_ok runQ]
        rw [runQ] at quick
        cases answer with
        | true =>
            simp only [↓reduceIte]
            rw [pure_run]
            exact ⟨quick.1, quick.2⟩
        | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            rw [pure_run]
            exact LazyPairInvariant.refl quick leftReads leftTyped rightReads rightTyped

/-- One-sided unfolding of the left operand. -/
theorem defEqLazyDeltaStepWithLeftDelta_sound {depth : Nat}
    (recursive : MethodContracts.{u,v} resolve anchor entries source catalog (methodsN depth))
    (seams : DefEqReducingSeams.{u,v} resolve anchor entries source catalog depth)
    (annotations : SameRawAnnotations.{u,v} entries)
    (binders : DefEqBinderAssumptions.{u,v} resolve anchor entries)
    (resources : DefEqReducingResources.{u,v} resolve anchor entries source catalog)
    {before : TcState .anon} {left right : KExpr .anon} {x y : AExpr β}
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (leftReads : readScopedExpr? resolve locals left = some x.erase)
    (leftTyped : ∃ type, TypingClaim.{u,v} entries context x type)
    (rightReads : readScopedExpr? resolve locals right = some y.erase)
    (rightTyped : ∃ type, TypingClaim.{u,v} entries context y type) :
    LazyStepPost.{u,v} resolve anchor entries source catalog locals context bounds x y
      ((RecM.defEqLazyDeltaStepWithLeftDelta left right).run (methodsN depth) before) := by
  unfold RecM.defEqLazyDeltaStepWithLeftDelta
  try simp only [ReaderT.run_bind]
  have unfolded := seams.deltaUnfoldOne left locals context bounds before x valid leftReads leftTyped
  cases runU : (RecM.deltaUnfoldOne left).run (methodsN depth) before with
  | error err s₁ =>
      rw [EStateM.run_bind_error runU]
      rw [runU] at unfolded
      exact unfolded
  | ok unfolded? s₁ =>
      rw [EStateM.run_bind_ok runU]
      rw [runU] at unfolded
      cases unfolded? with
      | none =>
          try dsimp only
          rw [pure_run]
          exact LazyPairInvariant.refl unfolded leftReads leftTyped rightReads rightTyped
      | some u =>
          obtain ⟨valid₁, U, uReads, claimXU, typesU⟩ := unfolded
          try dsimp only
          try simp only [ReaderT.run_bind]
          have reduced := whnfNoDeltaForDefEq_sound seams u locals context bounds s₁ U valid₁ uReads
            (leftTyped.imp fun _ => typesU _)
          cases runR : (RecM.whnfNoDeltaForDefEq u).run (methodsN depth) s₁ with
          | error err s₂ =>
              rw [EStateM.run_bind_error runR]
              rw [runR] at reduced
              exact reduced
          | ok r s₂ =>
              rw [EStateM.run_bind_ok runR]
              rw [runR] at reduced
              obtain ⟨valid₂, R, rReads, claimUR, typesR⟩ := reduced
              try dsimp only
              exact (finishDefEqLazyDeltaStep_sound recursive annotations binders resources valid₂ rReads
                (leftTyped.imp fun _ typed => typesR _ (typesU _ typed)) rightReads rightTyped).lift
                (claimXU.trans claimUR) (ConversionClaim.refl y)

/-- One-sided unfolding of the right operand. -/
theorem defEqLazyDeltaStepWithRightDelta_sound {depth : Nat}
    (recursive : MethodContracts.{u,v} resolve anchor entries source catalog (methodsN depth))
    (seams : DefEqReducingSeams.{u,v} resolve anchor entries source catalog depth)
    (annotations : SameRawAnnotations.{u,v} entries)
    (binders : DefEqBinderAssumptions.{u,v} resolve anchor entries)
    (resources : DefEqReducingResources.{u,v} resolve anchor entries source catalog)
    {before : TcState .anon} {left right : KExpr .anon} {x y : AExpr β}
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (leftReads : readScopedExpr? resolve locals left = some x.erase)
    (leftTyped : ∃ type, TypingClaim.{u,v} entries context x type)
    (rightReads : readScopedExpr? resolve locals right = some y.erase)
    (rightTyped : ∃ type, TypingClaim.{u,v} entries context y type) :
    LazyStepPost.{u,v} resolve anchor entries source catalog locals context bounds x y
      ((RecM.defEqLazyDeltaStepWithRightDelta left right).run (methodsN depth) before) := by
  unfold RecM.defEqLazyDeltaStepWithRightDelta
  try simp only [ReaderT.run_bind]
  have unfolded := seams.deltaUnfoldOne right locals context bounds before y valid rightReads rightTyped
  cases runU : (RecM.deltaUnfoldOne right).run (methodsN depth) before with
  | error err s₁ =>
      rw [EStateM.run_bind_error runU]
      rw [runU] at unfolded
      exact unfolded
  | ok unfolded? s₁ =>
      rw [EStateM.run_bind_ok runU]
      rw [runU] at unfolded
      cases unfolded? with
      | none =>
          try dsimp only
          rw [pure_run]
          exact LazyPairInvariant.refl unfolded leftReads leftTyped rightReads rightTyped
      | some u =>
          obtain ⟨valid₁, U, uReads, claimYU, typesU⟩ := unfolded
          try dsimp only
          try simp only [ReaderT.run_bind]
          have reduced := whnfNoDeltaForDefEq_sound seams u locals context bounds s₁ U valid₁ uReads
            (rightTyped.imp fun _ => typesU _)
          cases runR : (RecM.whnfNoDeltaForDefEq u).run (methodsN depth) s₁ with
          | error err s₂ =>
              rw [EStateM.run_bind_error runR]
              rw [runR] at reduced
              exact reduced
          | ok r s₂ =>
              rw [EStateM.run_bind_ok runR]
              rw [runR] at reduced
              obtain ⟨valid₂, R, rReads, claimUR, typesR⟩ := reduced
              try dsimp only
              exact (finishDefEqLazyDeltaStep_sound recursive annotations binders resources valid₂ leftReads
                leftTyped rReads (rightTyped.imp fun _ typed => typesR _ (typesU _ typed))).lift
                (ConversionClaim.refl x) (claimYU.trans claimUR)

/-- Two-sided unfolding after the same-head attempt misses. -/
theorem defEqLazyDeltaStepAfterSameHeadMiss_sound {depth : Nat}
    (recursive : MethodContracts.{u,v} resolve anchor entries source catalog (methodsN depth))
    (seams : DefEqReducingSeams.{u,v} resolve anchor entries source catalog depth)
    (annotations : SameRawAnnotations.{u,v} entries)
    (binders : DefEqBinderAssumptions.{u,v} resolve anchor entries)
    (resources : DefEqReducingResources.{u,v} resolve anchor entries source catalog)
    {before : TcState .anon} {left right : KExpr .anon} {x y : AExpr β}
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (leftReads : readScopedExpr? resolve locals left = some x.erase)
    (leftTyped : ∃ type, TypingClaim.{u,v} entries context x type)
    (rightReads : readScopedExpr? resolve locals right = some y.erase)
    (rightTyped : ∃ type, TypingClaim.{u,v} entries context y type) :
    LazyStepPost.{u,v} resolve anchor entries source catalog locals context bounds x y
      ((RecM.defEqLazyDeltaStepAfterSameHeadMiss left right).run (methodsN depth) before) := by
  unfold RecM.defEqLazyDeltaStepAfterSameHeadMiss
  try simp only [ReaderT.run_bind]
  have unfoldedA := seams.deltaUnfoldOne left locals context bounds before x valid leftReads leftTyped
  cases runA : (RecM.deltaUnfoldOne left).run (methodsN depth) before with
  | error err s₁ =>
      rw [EStateM.run_bind_error runA]
      rw [runA] at unfoldedA
      exact unfoldedA
  | ok ua? s₁ =>
      rw [EStateM.run_bind_ok runA]
      rw [runA] at unfoldedA
      have validA : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds s₁ := by
        cases ua? with
        | none => exact unfoldedA
        | some _ => exact unfoldedA.1
      try dsimp only
      try simp only [ReaderT.run_bind]
      have unfoldedB := seams.deltaUnfoldOne right locals context bounds s₁ y validA rightReads rightTyped
      cases runB : (RecM.deltaUnfoldOne right).run (methodsN depth) s₁ with
      | error err s₂ =>
          rw [EStateM.run_bind_error runB]
          rw [runB] at unfoldedB
          exact unfoldedB
      | ok ub? s₂ =>
          rw [EStateM.run_bind_ok runB]
          rw [runB] at unfoldedB
          try dsimp only
          cases ua? with
          | none =>
              cases ub? with
              | none =>
                  try dsimp only
                  rw [pure_run]
                  exact LazyPairInvariant.refl unfoldedB leftReads leftTyped rightReads rightTyped
              | some ub =>
                  obtain ⟨valid₂, U, uReads, claimYU, typesU⟩ := unfoldedB
                  try dsimp only
                  try simp only [ReaderT.run_bind]
                  have reduced := whnfNoDeltaForDefEq_sound seams ub locals context bounds s₂ U valid₂ uReads
                    (rightTyped.imp fun _ => typesU _)
                  cases runR : (RecM.whnfNoDeltaForDefEq ub).run (methodsN depth) s₂ with
                  | error err s₃ =>
                      rw [EStateM.run_bind_error runR]
                      rw [runR] at reduced
                      exact reduced
                  | ok r s₃ =>
                      rw [EStateM.run_bind_ok runR]
                      rw [runR] at reduced
                      obtain ⟨valid₃, R, rReads, claimUR, typesR⟩ := reduced
                      try dsimp only
                      exact (finishDefEqLazyDeltaStep_sound recursive annotations binders resources valid₃
                        leftReads leftTyped rReads
                        (rightTyped.imp fun _ typed => typesR _ (typesU _ typed))).lift
                        (ConversionClaim.refl x) (claimYU.trans claimUR)
          | some ua =>
              obtain ⟨_, UA, uaReads, claimXUA, typesUA⟩ := unfoldedA
              cases ub? with
              | none =>
                  try dsimp only
                  try simp only [ReaderT.run_bind]
                  have reduced := whnfNoDeltaForDefEq_sound seams ua locals context bounds s₂ UA unfoldedB
                    uaReads (leftTyped.imp fun _ => typesUA _)
                  cases runR : (RecM.whnfNoDeltaForDefEq ua).run (methodsN depth) s₂ with
                  | error err s₃ =>
                      rw [EStateM.run_bind_error runR]
                      rw [runR] at reduced
                      exact reduced
                  | ok r s₃ =>
                      rw [EStateM.run_bind_ok runR]
                      rw [runR] at reduced
                      obtain ⟨valid₃, R, rReads, claimUR, typesR⟩ := reduced
                      try dsimp only
                      exact (finishDefEqLazyDeltaStep_sound recursive annotations binders resources valid₃
                        rReads (leftTyped.imp fun _ typed => typesR _ (typesUA _ typed)) rightReads
                        rightTyped).lift (claimXUA.trans claimUR) (ConversionClaim.refl y)
              | some ub =>
                  obtain ⟨valid₂, UB, ubReads, claimYUB, typesUB⟩ := unfoldedB
                  try dsimp only
                  try simp only [ReaderT.run_bind]
                  have reducedA := whnfNoDeltaForDefEq_sound seams ua locals context bounds s₂ UA valid₂
                    uaReads (leftTyped.imp fun _ => typesUA _)
                  cases runRA : (RecM.whnfNoDeltaForDefEq ua).run (methodsN depth) s₂ with
                  | error err s₃ =>
                      rw [EStateM.run_bind_error runRA]
                      rw [runRA] at reducedA
                      exact reducedA
                  | ok ra s₃ =>
                      rw [EStateM.run_bind_ok runRA]
                      rw [runRA] at reducedA
                      obtain ⟨valid₃, RA, raReads, claimRA, typesRA⟩ := reducedA
                      try dsimp only
                      try simp only [ReaderT.run_bind]
                      have reducedB := whnfNoDeltaForDefEq_sound seams ub locals context bounds s₃ UB valid₃
                        ubReads (rightTyped.imp fun _ => typesUB _)
                      cases runRB : (RecM.whnfNoDeltaForDefEq ub).run (methodsN depth) s₃ with
                      | error err s₄ =>
                          rw [EStateM.run_bind_error runRB]
                          rw [runRB] at reducedB
                          exact reducedB
                      | ok rb s₄ =>
                          rw [EStateM.run_bind_ok runRB]
                          rw [runRB] at reducedB
                          obtain ⟨valid₄, RB, rbReads, claimRB, typesRB⟩ := reducedB
                          try dsimp only
                          exact (finishDefEqLazyDeltaStep_sound recursive annotations binders resources
                            valid₄ raReads (leftTyped.imp fun _ typed => typesRA _ (typesUA _ typed))
                            rbReads (rightTyped.imp fun _ typed => typesRB _ (typesUB _ typed))).lift
                            (claimXUA.trans claimRA) (claimYUB.trans claimRB)

/-- Equal rank: the guarded same-head attempt, then two-sided unfolding. -/
theorem defEqLazyDeltaStepWithEqualRank_sound {depth : Nat}
    (recursive : MethodContracts.{u,v} resolve anchor entries source catalog (methodsN depth))
    (seams : DefEqReducingSeams.{u,v} resolve anchor entries source catalog depth)
    (annotations : SameRawAnnotations.{u,v} entries)
    (binders : DefEqBinderAssumptions.{u,v} resolve anchor entries)
    (resources : DefEqReducingResources.{u,v} resolve anchor entries source catalog)
    {before : TcState .anon} {left right : KExpr .anon} {x y : AExpr β}
    (aHead bHead : Option (KId .anon))
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (leftReads : readScopedExpr? resolve locals left = some x.erase)
    (leftTyped : ∃ type, TypingClaim.{u,v} entries context x type)
    (rightReads : readScopedExpr? resolve locals right = some y.erase)
    (rightTyped : ∃ type, TypingClaim.{u,v} entries context y type) :
    LazyStepPost.{u,v} resolve anchor entries source catalog locals context bounds x y
      ((RecM.defEqLazyDeltaStepWithEqualRank left right aHead bHead).run (methodsN depth) before) := by
  have miss : ∀ state,
      CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds state →
      LazyStepPost.{u,v} resolve anchor entries source catalog locals context bounds x y
        ((RecM.defEqLazyDeltaStepAfterSameHeadMiss left right).run (methodsN depth) state) :=
    fun _ valid' => defEqLazyDeltaStepAfterSameHeadMiss_sound recursive seams annotations binders resources
      valid' leftReads leftTyped rightReads rightTyped
  unfold RecM.defEqLazyDeltaStepWithEqualRank
  try dsimp only
  cases aHead with
  | none => exact miss before valid
  | some ah =>
  cases bHead with
  | none => exact miss before valid
  | some bh =>
  try dsimp only
  refine RecM.ite_post (fun _ => ?_) fun _ => miss before valid
  try simp only [ReaderT.run_bind]
  have regular := isRegular_keeps (methods := methodsN depth) resources valid ah
  cases runR : (RecM.isRegular ah).run (methodsN depth) before with
  | error err s₁ =>
      rw [EStateM.run_bind_error runR]
      rw [runR] at regular
      exact regular
  | ok isRegular s₁ =>
      rw [EStateM.run_bind_ok runR]
      rw [runR] at regular
      try dsimp only
      try simp only [ReaderT.run_bind]
      have cached := trySameHeadSpineCached_sound recursive seams resources (!isRegular) left right locals
        context bounds s₁ x y regular leftReads leftTyped rightReads rightTyped
      cases runC : (RecM.trySameHeadSpineCached (!isRegular) left right).run (methodsN depth) s₁ with
      | error err s₂ =>
          rw [EStateM.run_bind_error runC]
          rw [runC] at cached
          exact cached
      | ok answer? s₂ =>
          rw [EStateM.run_bind_ok runC]
          rw [runC] at cached
          cases answer? with
          | none =>
              try dsimp only
              exact miss s₂ cached
          | some answer =>
              try dsimp only
              rw [pure_run]
              cases answer with
              | false => exact cached
              | true => exact cached

/-- Rank dispatch after the projection probe. -/
theorem defEqLazyDeltaStepAfterProjectionMiss_sound {depth : Nat}
    (recursive : MethodContracts.{u,v} resolve anchor entries source catalog (methodsN depth))
    (seams : DefEqReducingSeams.{u,v} resolve anchor entries source catalog depth)
    (annotations : SameRawAnnotations.{u,v} entries)
    (binders : DefEqBinderAssumptions.{u,v} resolve anchor entries)
    (resources : DefEqReducingResources.{u,v} resolve anchor entries source catalog)
    {before : TcState .anon} {left right : KExpr .anon} {x y : AExpr β}
    (aHead bHead : Option (KId .anon)) (aDelta bDelta : Bool)
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (leftReads : readScopedExpr? resolve locals left = some x.erase)
    (leftTyped : ∃ type, TypingClaim.{u,v} entries context x type)
    (rightReads : readScopedExpr? resolve locals right = some y.erase)
    (rightTyped : ∃ type, TypingClaim.{u,v} entries context y type) :
    LazyStepPost.{u,v} resolve anchor entries source catalog locals context bounds x y
      ((RecM.defEqLazyDeltaStepAfterProjectionMiss left right aHead bHead aDelta bDelta).run
        (methodsN depth) before) := by
  have leftDelta : ∀ state,
      CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds state →
      LazyStepPost.{u,v} resolve anchor entries source catalog locals context bounds x y
        ((RecM.defEqLazyDeltaStepWithLeftDelta left right).run (methodsN depth) state) :=
    fun _ valid' => defEqLazyDeltaStepWithLeftDelta_sound recursive seams annotations binders resources
      valid' leftReads leftTyped rightReads rightTyped
  have rightDelta : ∀ state,
      CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds state →
      LazyStepPost.{u,v} resolve anchor entries source catalog locals context bounds x y
        ((RecM.defEqLazyDeltaStepWithRightDelta left right).run (methodsN depth) state) :=
    fun _ valid' => defEqLazyDeltaStepWithRightDelta_sound recursive seams annotations binders resources
      valid' leftReads leftTyped rightReads rightTyped
  unfold RecM.defEqLazyDeltaStepAfterProjectionMiss
  try dsimp only
  refine RecM.ite_post (fun _ => ?_) fun _ => RecM.ite_post (fun _ => leftDelta before valid)
    fun _ => rightDelta before valid
  try simp only [ReaderT.run_bind]
  have rankA := rankDeltaHead_keeps (methods := methodsN depth) resources valid aHead
  cases runA : (RecM.rankDeltaHead aHead).run (methodsN depth) before with
  | error err s₁ =>
      rw [EStateM.run_bind_error runA]
      rw [runA] at rankA
      exact rankA
  | ok waW s₁ =>
      rw [EStateM.run_bind_ok runA]
      rw [runA] at rankA
      try dsimp only
      try simp only [ReaderT.run_bind]
      have rankB := rankDeltaHead_keeps (methods := methodsN depth) resources rankA bHead
      cases runB : (RecM.rankDeltaHead bHead).run (methodsN depth) s₁ with
      | error err s₂ =>
          rw [EStateM.run_bind_error runB]
          rw [runB] at rankB
          exact rankB
      | ok wbW s₂ =>
          rw [EStateM.run_bind_ok runB]
          rw [runB] at rankB
          try dsimp only
          refine RecM.ite_post (fun _ => ?_) fun _ => RecM.ite_post (fun _ => leftDelta s₂ rankB)
            fun _ => rightDelta s₂ rankB
          exact defEqLazyDeltaStepWithEqualRank_sound recursive seams annotations binders resources aHead
            bHead rankB leftReads leftTyped rightReads rightTyped

/-- The asymmetric projection-app probe before unfolding. -/
theorem defEqLazyDeltaStepAfterDeltaClassification_sound {depth : Nat}
    (recursive : MethodContracts.{u,v} resolve anchor entries source catalog (methodsN depth))
    (seams : DefEqReducingSeams.{u,v} resolve anchor entries source catalog depth)
    (annotations : SameRawAnnotations.{u,v} entries)
    (binders : DefEqBinderAssumptions.{u,v} resolve anchor entries)
    (resources : DefEqReducingResources.{u,v} resolve anchor entries source catalog)
    {before : TcState .anon} {left right : KExpr .anon} {x y : AExpr β}
    (aHead bHead : Option (KId .anon)) (aDelta bDelta : Bool)
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (leftReads : readScopedExpr? resolve locals left = some x.erase)
    (leftTyped : ∃ type, TypingClaim.{u,v} entries context x type)
    (rightReads : readScopedExpr? resolve locals right = some y.erase)
    (rightTyped : ∃ type, TypingClaim.{u,v} entries context y type) :
    LazyStepPost.{u,v} resolve anchor entries source catalog locals context bounds x y
      ((RecM.defEqLazyDeltaStepAfterDeltaClassification left right aHead bHead aDelta bDelta).run
        (methodsN depth) before) := by
  have miss : ∀ state,
      CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds state →
      LazyStepPost.{u,v} resolve anchor entries source catalog locals context bounds x y
        ((RecM.defEqLazyDeltaStepAfterProjectionMiss left right aHead bHead aDelta bDelta).run
          (methodsN depth) state) :=
    fun _ valid' => defEqLazyDeltaStepAfterProjectionMiss_sound recursive seams annotations binders
      resources aHead bHead aDelta bDelta valid' leftReads leftTyped rightReads rightTyped
  unfold RecM.defEqLazyDeltaStepAfterDeltaClassification
  try dsimp only
  refine RecM.ite_post (fun _ => ?_) fun _ => RecM.ite_post (fun _ => ?_) fun _ => miss before valid
  · simp only [ReaderT.run_bind]
    have probe := seams.unfoldProjApp right locals context bounds before y valid rightReads rightTyped
    cases runP : (RecM.tryUnfoldProjApp right).run (methodsN depth) before with
    | error err s₁ =>
        rw [EStateM.run_bind_error runP]
        rw [runP] at probe
        exact probe
    | ok reduced? s₁ =>
        rw [EStateM.run_bind_ok runP]
        rw [runP] at probe
        cases reduced? with
        | none =>
            try dsimp only
            try simp only [ReaderT.run_bind]
            try rw [EStateM.run_bind_ok (pure_run _ (methodsN depth) s₁)]
            try dsimp only
            exact miss s₁ probe
        | some reduced =>
            obtain ⟨valid₁, R, rReads, claimYR, typesR⟩ := probe
            try dsimp only
            rw [pure_run]
            exact ⟨valid₁, x, R, leftReads, leftTyped, rReads, rightTyped.imp fun _ => typesR _,
              ConversionClaim.refl x, claimYR⟩
  · simp only [ReaderT.run_bind]
    have probe := seams.unfoldProjApp left locals context bounds before x valid leftReads leftTyped
    cases runP : (RecM.tryUnfoldProjApp left).run (methodsN depth) before with
    | error err s₁ =>
        rw [EStateM.run_bind_error runP]
        rw [runP] at probe
        exact probe
    | ok reduced? s₁ =>
        rw [EStateM.run_bind_ok runP]
        rw [runP] at probe
        cases reduced? with
        | none =>
            try dsimp only
            try simp only [ReaderT.run_bind]
            try rw [EStateM.run_bind_ok (pure_run _ (methodsN depth) s₁)]
            try dsimp only
            exact miss s₁ probe
        | some reduced =>
            obtain ⟨valid₁, R, rReads, claimXR, typesR⟩ := probe
            try dsimp only
            rw [pure_run]
            exact ⟨valid₁, R, y, rReads, leftTyped.imp fun _ => typesR _, rightReads, rightTyped,
              claimXR, ConversionClaim.refl y⟩

/-- Delta classification of both heads: neither reducible stops the loop. -/
theorem defEqLazyDeltaStepAfterAcceleratorMiss_sound {depth : Nat}
    (recursive : MethodContracts.{u,v} resolve anchor entries source catalog (methodsN depth))
    (seams : DefEqReducingSeams.{u,v} resolve anchor entries source catalog depth)
    (annotations : SameRawAnnotations.{u,v} entries)
    (binders : DefEqBinderAssumptions.{u,v} resolve anchor entries)
    (resources : DefEqReducingResources.{u,v} resolve anchor entries source catalog)
    {before : TcState .anon} {left right : KExpr .anon} {x y : AExpr β}
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (leftReads : readScopedExpr? resolve locals left = some x.erase)
    (leftTyped : ∃ type, TypingClaim.{u,v} entries context x type)
    (rightReads : readScopedExpr? resolve locals right = some y.erase)
    (rightTyped : ∃ type, TypingClaim.{u,v} entries context y type) :
    LazyStepPost.{u,v} resolve anchor entries source catalog locals context bounds x y
      ((RecM.defEqLazyDeltaStepAfterAcceleratorMiss left right).run (methodsN depth) before) := by
  unfold RecM.defEqLazyDeltaStepAfterAcceleratorMiss
  try dsimp only
  try simp only [ReaderT.run_bind]
  have classA := classifyDeltaHead_keeps (methods := methodsN depth) resources valid left
  cases runA : (RecM.classifyDeltaHead left).run (methodsN depth) before with
  | error err s₁ =>
      rw [EStateM.run_bind_error runA]
      rw [runA] at classA
      exact classA
  | ok aDelta s₁ =>
      rw [EStateM.run_bind_ok runA]
      rw [runA] at classA
      try dsimp only
      try simp only [ReaderT.run_bind]
      have classB := classifyDeltaHead_keeps (methods := methodsN depth) resources classA right
      cases runB : (RecM.classifyDeltaHead right).run (methodsN depth) s₁ with
      | error err s₂ =>
          rw [EStateM.run_bind_error runB]
          rw [runB] at classB
          exact classB
      | ok bDelta s₂ =>
          rw [EStateM.run_bind_ok runB]
          rw [runB] at classB
          try dsimp only
          refine RecM.ite_post (fun _ => ?_) fun _ => ?_
          · rw [pure_run]
            exact LazyPairInvariant.refl classB leftReads leftTyped rightReads rightTyped
          · exact defEqLazyDeltaStepAfterDeltaClassification_sound recursive seams annotations binders
              resources _ _ aDelta bDelta classB leftReads leftTyped rightReads rightTyped

/-- An optional reduction of the left operand answered through the callback,
otherwise the continuation. -/
theorem LazyStepPost.optionalLeft {depth : Nat}
    (recursive : MethodContracts.{u,v} resolve anchor entries source catalog (methodsN depth))
    {probe : RecM .anon (Option (KExpr .anon))}
    {next : Option (KExpr .anon) → RecM .anon
      (RecM.BoundedStep (KExpr .anon × KExpr .anon) (LazyDeltaLoopResult .anon))}
    {before : TcState .anon} {right : KExpr .anon} {x y : AExpr β}
    (probeSound : OptionalReductionPost.{u,v} resolve anchor entries source catalog locals context bounds x
      (probe.run (methodsN depth) before))
    (answered : ∀ reduced, next (some reduced) = RecM.isDefEqCall reduced right >>= fun answer =>
      pure (RecM.BoundedStep.done (LazyDeltaLoopResult.answer answer)))
    (rightReads : readScopedExpr? resolve locals right = some y.erase)
    (rightTyped : ∃ type, TypingClaim.{u,v} entries context y type)
    (leftTyped : ∃ type, TypingClaim.{u,v} entries context x type)
    (restSound : ∀ state,
      CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds state →
      LazyStepPost.{u,v} resolve anchor entries source catalog locals context bounds x y
        ((next none).run (methodsN depth) state)) :
    LazyStepPost.{u,v} resolve anchor entries source catalog locals context bounds x y
      ((probe >>= next).run (methodsN depth) before) := by
  try simp only [ReaderT.run_bind]
  cases run : probe.run (methodsN depth) before with
  | error err after =>
      rw [EStateM.run_bind_error run]
      rw [run] at probeSound
      exact probeSound
  | ok reduced? after =>
      rw [EStateM.run_bind_ok run]
      rw [run] at probeSound
      cases reduced? with
      | none => exact restSound after probeSound
      | some reduced =>
          obtain ⟨valid, R, rReads, claim, types⟩ := probeSound
          rw [answered]
          exact LazyStepPost.ofCallLeft recursive.toDefEqContract valid claim rReads
            (leftTyped.imp fun _ => types _) rightReads rightTyped

/-- An optional reduction of the right operand answered through the callback,
otherwise the continuation. -/
theorem LazyStepPost.optionalRight {depth : Nat}
    (recursive : MethodContracts.{u,v} resolve anchor entries source catalog (methodsN depth))
    {probe : RecM .anon (Option (KExpr .anon))}
    {next : Option (KExpr .anon) → RecM .anon
      (RecM.BoundedStep (KExpr .anon × KExpr .anon) (LazyDeltaLoopResult .anon))}
    {before : TcState .anon} {left : KExpr .anon} {x y : AExpr β}
    (probeSound : OptionalReductionPost.{u,v} resolve anchor entries source catalog locals context bounds y
      (probe.run (methodsN depth) before))
    (answered : ∀ reduced, next (some reduced) = RecM.isDefEqCall left reduced >>= fun answer =>
      pure (RecM.BoundedStep.done (LazyDeltaLoopResult.answer answer)))
    (leftReads : readScopedExpr? resolve locals left = some x.erase)
    (leftTyped : ∃ type, TypingClaim.{u,v} entries context x type)
    (rightTyped : ∃ type, TypingClaim.{u,v} entries context y type)
    (restSound : ∀ state,
      CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds state →
      LazyStepPost.{u,v} resolve anchor entries source catalog locals context bounds x y
        ((next none).run (methodsN depth) state)) :
    LazyStepPost.{u,v} resolve anchor entries source catalog locals context bounds x y
      ((probe >>= next).run (methodsN depth) before) := by
  try simp only [ReaderT.run_bind]
  cases run : probe.run (methodsN depth) before with
  | error err after =>
      rw [EStateM.run_bind_error run]
      rw [run] at probeSound
      exact probeSound
  | ok reduced? after =>
      rw [EStateM.run_bind_ok run]
      rw [run] at probeSound
      cases reduced? with
      | none => exact restSound after probeSound
      | some reduced =>
          obtain ⟨valid, R, rReads, claim, types⟩ := probeSound
          rw [answered]
          exact LazyStepPost.ofCallRight recursive.toDefEqContract valid claim leftReads leftTyped rReads
            (rightTyped.imp fun _ => types _)

/-- The accelerators: native and Decidable reduction on either side. -/
theorem defEqLazyDeltaStepAfterNatMiss_sound {depth : Nat}
    (recursive : MethodContracts.{u,v} resolve anchor entries source catalog (methodsN depth))
    (seams : DefEqReducingSeams.{u,v} resolve anchor entries source catalog depth)
    (annotations : SameRawAnnotations.{u,v} entries)
    (binders : DefEqBinderAssumptions.{u,v} resolve anchor entries)
    (resources : DefEqReducingResources.{u,v} resolve anchor entries source catalog)
    {before : TcState .anon} {left right : KExpr .anon} {x y : AExpr β}
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (leftReads : readScopedExpr? resolve locals left = some x.erase)
    (leftTyped : ∃ type, TypingClaim.{u,v} entries context x type)
    (rightReads : readScopedExpr? resolve locals right = some y.erase)
    (rightTyped : ∃ type, TypingClaim.{u,v} entries context y type) :
    LazyStepPost.{u,v} resolve anchor entries source catalog locals context bounds x y
      ((RecM.defEqLazyDeltaStepAfterNatMiss left right).run (methodsN depth) before) := by
  unfold RecM.defEqLazyDeltaStepAfterNatMiss
  try dsimp only
  refine LazyStepPost.optionalLeft recursive
    (seams.reduceNative left locals context bounds before x valid leftReads leftTyped) (fun _ => rfl)
    rightReads rightTyped leftTyped fun s₁ valid₁ => ?_
  try dsimp only
  refine LazyStepPost.optionalRight recursive
    (seams.reduceNative right locals context bounds s₁ y valid₁ rightReads rightTyped) (fun _ => rfl)
    leftReads leftTyped rightTyped fun s₂ valid₂ => ?_
  try dsimp only
  refine LazyStepPost.optionalLeft recursive
    (seams.reduceDecidable left locals context bounds s₂ x valid₂ leftReads leftTyped) (fun _ => rfl)
    rightReads rightTyped leftTyped fun s₃ valid₃ => ?_
  try dsimp only
  refine LazyStepPost.optionalRight recursive
    (seams.reduceDecidable right locals context bounds s₃ y valid₃ rightReads rightTyped) (fun _ => rfl)
    leftReads leftTyped rightTyped fun s₄ valid₄ => ?_
  try dsimp only
  exact defEqLazyDeltaStepAfterAcceleratorMiss_sound recursive seams annotations binders resources valid₄
    leftReads leftTyped rightReads rightTyped

/-- The gated Nat reducers. -/
theorem defEqLazyDeltaStepAfterOffsetMiss_sound {depth : Nat}
    (recursive : MethodContracts.{u,v} resolve anchor entries source catalog (methodsN depth))
    (seams : DefEqReducingSeams.{u,v} resolve anchor entries source catalog depth)
    (annotations : SameRawAnnotations.{u,v} entries)
    (binders : DefEqBinderAssumptions.{u,v} resolve anchor entries)
    (resources : DefEqReducingResources.{u,v} resolve anchor entries source catalog)
    {before : TcState .anon} {left right : KExpr .anon} {x y : AExpr β}
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (leftReads : readScopedExpr? resolve locals left = some x.erase)
    (leftTyped : ∃ type, TypingClaim.{u,v} entries context x type)
    (rightReads : readScopedExpr? resolve locals right = some y.erase)
    (rightTyped : ∃ type, TypingClaim.{u,v} entries context y type) :
    LazyStepPost.{u,v} resolve anchor entries source catalog locals context bounds x y
      ((RecM.defEqLazyDeltaStepAfterOffsetMiss (left, right)).run (methodsN depth) before) := by
  have miss : ∀ state,
      CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds state →
      LazyStepPost.{u,v} resolve anchor entries source catalog locals context bounds x y
        ((RecM.defEqLazyDeltaStepAfterNatMiss left right).run (methodsN depth) state) :=
    fun _ valid' => defEqLazyDeltaStepAfterNatMiss_sound recursive seams annotations binders resources
      valid' leftReads leftTyped rightReads rightTyped
  unfold RecM.defEqLazyDeltaStepAfterOffsetMiss
  try dsimp only
  try simp only [ReaderT.run_bind]
  rw [EStateM.run_bind_ok (get_run (methodsN depth) before)]
  try dsimp only
  refine RecM.ite_post (fun _ => ?_) fun _ => miss before valid
  refine LazyStepPost.optionalLeft recursive
    (seams.reduceNat left locals context bounds before x valid leftReads leftTyped) (fun _ => rfl)
    rightReads rightTyped leftTyped fun s₁ valid₁ => ?_
  try dsimp only
  refine LazyStepPost.optionalRight recursive
    (seams.reduceNat right locals context bounds s₁ y valid₁ rightReads rightTyped) (fun _ => rfl)
    leftReads leftTyped rightTyped fun s₂ valid₂ => ?_
  try dsimp only
  exact miss s₂ valid₂

/-- One iteration: the Nat-offset probe, then the remaining branches. -/
theorem defEqLazyDeltaStep_sound {depth : Nat}
    (recursive : MethodContracts.{u,v} resolve anchor entries source catalog (methodsN depth))
    (seams : DefEqReducingSeams.{u,v} resolve anchor entries source catalog depth)
    (annotations : SameRawAnnotations.{u,v} entries)
    (binders : DefEqBinderAssumptions.{u,v} resolve anchor entries)
    (resources : DefEqReducingResources.{u,v} resolve anchor entries source catalog)
    {before : TcState .anon} {left right : KExpr .anon} {x y : AExpr β}
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (leftReads : readScopedExpr? resolve locals left = some x.erase)
    (leftTyped : ∃ type, TypingClaim.{u,v} entries context x type)
    (rightReads : readScopedExpr? resolve locals right = some y.erase)
    (rightTyped : ∃ type, TypingClaim.{u,v} entries context y type) :
    LazyStepPost.{u,v} resolve anchor entries source catalog locals context bounds x y
      ((RecM.defEqLazyDeltaStep (left, right)).run (methodsN depth) before) := by
  unfold RecM.defEqLazyDeltaStep
  try dsimp only
  try simp only [ReaderT.run_bind]
  have offset := seams.offset left right locals context bounds before x y valid leftReads leftTyped
    rightReads rightTyped
  cases runO : (RecM.tryDefEqOffset left right).run (methodsN depth) before with
  | error err s₁ =>
      rw [EStateM.run_bind_error runO]
      rw [runO] at offset
      exact offset
  | ok answer? s₁ =>
      rw [EStateM.run_bind_ok runO]
      rw [runO] at offset
      cases answer? with
      | none =>
          try dsimp only
          exact defEqLazyDeltaStepAfterOffsetMiss_sound recursive seams annotations binders resources offset
            leftReads leftTyped rightReads rightTyped
      | some answer =>
          try dsimp only
          rw [pure_run]
          cases answer with
          | false => exact offset
          | true => exact offset

end Iteration

/-! ### The loop and the lazy-delta pass -/

section Loop

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {anchor entries : Model.Environment β} {source : Ixon.Env}
  {catalog : List (SourceCacheRequest source)}

/-- The bounded lazy-delta loop from any loop state. -/
theorem runDefEqLazyDelta_sound {depth : Nat}
    (recursive : MethodContracts.{u,v} resolve anchor entries source catalog (methodsN depth))
    (seams : DefEqReducingSeams.{u,v} resolve anchor entries source catalog depth)
    (annotations : SameRawAnnotations.{u,v} entries)
    (binders : DefEqBinderAssumptions.{u,v} resolve anchor entries)
    (resources : DefEqReducingResources.{u,v} resolve anchor entries source catalog)
    {locals : List FVarId} {context : Model.Context β} {bounds : List VLevel} {before : TcState .anon}
    {left right : KExpr .anon} {a b : AExpr β}
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (leftReads : readScopedExpr? resolve locals left = some a.erase)
    (leftTyped : ∃ type, TypingClaim.{u,v} entries context a type)
    (rightReads : readScopedExpr? resolve locals right = some b.erase)
    (rightTyped : ∃ type, TypingClaim.{u,v} entries context b type) :
    LazyDeltaPost.{u,v} resolve anchor entries source catalog locals context bounds a b
      ((RecM.runDefEqLazyDelta left right).run (methodsN depth) before) := by
  unfold RecM.runDefEqLazyDelta
  refine runBoundedInvariant_sound
    (Inv := LazyPairInvariant.{u,v} resolve anchor entries source catalog locals context bounds a b)
    (Post := LazyDeltaPost.{u,v} resolve anchor entries source catalog locals context bounds a b)
    ?_ ?_ _ _ before (LazyPairInvariant.refl valid leftReads leftTyped rightReads rightTyped)
  · rintro ⟨x, y⟩ state ⟨valid', X, Y, xReads, xTyped, yReads, yTyped, claimX, claimY⟩
    have post := (defEqLazyDeltaStep_sound recursive seams annotations binders resources valid' xReads
      xTyped yReads yTyped).lift claimX claimY
    cases run : (RecM.defEqLazyDeltaStep (x, y)).run (methodsN depth) state with
    | error err after =>
        rw [run] at post
        exact post
    | ok next after =>
        rw [run] at post
        cases next with
        | next pair => exact post
        | done result => exact post
  · intro state before invariant
    exact invariant.1

/-- The lazy-delta pass: an answer, or the stopped continuation on the
final pair. -/
theorem isDefEqInnerAfterProofIrrelevance_sound {depth : Nat}
    (recursive : MethodContracts.{u,v} resolve anchor entries source catalog (methodsN depth))
    (seams : DefEqReducingSeams.{u,v} resolve anchor entries source catalog depth)
    (annotations : SameRawAnnotations.{u,v} entries)
    (binders : DefEqBinderAssumptions.{u,v} resolve anchor entries)
    (resources : DefEqReducingResources.{u,v} resolve anchor entries source catalog)
    (left right : KExpr .anon) :
    SoundConversion.{u,v} resolve anchor entries source catalog left right
      ((RecM.isDefEqInnerAfterProofIrrelevance left right).run (methodsN depth)) := by
  intro locals context bounds before a b valid leftReads leftTyped rightReads rightTyped
  unfold RecM.isDefEqInnerAfterProofIrrelevance
  try simp only [ReaderT.run_bind]
  have loop := runDefEqLazyDelta_sound recursive seams annotations binders resources valid leftReads
    leftTyped rightReads rightTyped
  cases run : (RecM.runDefEqLazyDelta left right).run (methodsN depth) before with
  | error err after =>
      rw [EStateM.run_bind_error run]
      rw [run] at loop
      exact loop
  | ok result after =>
      rw [EStateM.run_bind_ok run]
      rw [run] at loop
      cases result with
      | answer answer =>
          try dsimp only
          rw [pure_run]
          cases answer with
          | false => exact loop
          | true => exact loop
      | stopped x y =>
          obtain ⟨valid', X, Y, xReads, xTyped, yReads, yTyped, claimX, claimY⟩ := loop
          try dsimp only
          have stopped := isDefEqAfterLazyDeltaStopped_sound recursive seams annotations binders resources x y
            locals context bounds after X Y valid' xReads xTyped yReads yTyped
          cases runS : (RecM.isDefEqAfterLazyDeltaStopped x y).run (methodsN depth) after with
          | error err final =>
              rw [runS] at stopped
              exact stopped
          | ok answer final =>
              rw [runS] at stopped
              cases answer with
              | false => exact stopped
              | true => exact ⟨stopped.1, claimX.trans (stopped.2.trans claimY.symm)⟩

end Loop

/-! ### The assembled reducing tiers -/

section Assembly

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {anchor entries : Model.Environment β} {source : Ixon.Env}
  {catalog : List (SourceCacheRequest source)}

/-- The remaining recursive tiers after the quick structural probe: the eager
`Bool.true` shortcut, the vacuous string expansion, the structural-core and
no-delta passes, proof irrelevance, the lazy-delta loop, and the stopped
continuation through the final tier, under the smaller table's contracts,
the reducer seams, the annotation discipline, the binder premises, and the
finite resources. -/
theorem isDefEqInnerAfterQuick_sound {depth : Nat}
    (recursive : MethodContracts.{u,v} resolve anchor entries source catalog (methodsN depth))
    (seams : DefEqReducingSeams.{u,v} resolve anchor entries source catalog depth)
    (annotations : SameRawAnnotations.{u,v} entries)
    (binders : DefEqBinderAssumptions.{u,v} resolve anchor entries)
    (resources : DefEqReducingResources.{u,v} resolve anchor entries source catalog)
    (left right : KExpr .anon) :
    SoundConversion.{u,v} resolve anchor entries source catalog left right
      ((RecM.isDefEqInnerAfterQuick left right).run (methodsN depth)) :=
  isDefEqInnerAfterQuick_sound_of_tail seams
    (isDefEqInnerAfterBoolTrue_sound_of_tail
      (isDefEqInnerAfterStringExpansion_sound_of_tail recursive seams annotations binders resources
        (isDefEqInnerAfterCorePass_sound_of_tail recursive seams annotations binders resources
          (isDefEqInnerAfterNoDeltaPass_sound_of_tail recursive seams resources
            (isDefEqInnerAfterProofIrrelevance_sound recursive seams annotations binders resources)))))
    left right

/-- The direct tiers' seam record from the reducing seams: `inner` is
discharged, the other three fields are the model boundaries they were. -/
theorem DefEqSeamAssumptions.ofReducing {depth : Nat}
    (recursive : MethodContracts.{u,v} resolve anchor entries source catalog (methodsN depth))
    (seams : DefEqReducingSeams.{u,v} resolve anchor entries source catalog depth)
    (transport : DefEqMemoTransport.{u,v} resolve anchor entries source catalog)
    (annotations : SameRawAnnotations.{u,v} entries)
    (binders : DefEqBinderAssumptions.{u,v} resolve anchor entries)
    (resources : DefEqReducingResources.{u,v} resolve anchor entries source catalog) :
    DefEqSeamAssumptions.{u,v} resolve anchor entries source catalog depth where
  inner := isDefEqInnerAfterQuick_sound recursive seams annotations binders resources
  transport := transport
  sameRawAnnotations := annotations
  binders := binders

/-- The `StepContracts.isDefEq` field modulo the reducer seams, the memo
transport, the annotation discipline, the binder premises, and the finite
resources. The seams may depend on the smaller table's contracts, as the
reduction package's `StepContracts` fields do. -/
theorem StepContracts.isDefEq_of_reducing_tiers {depth : Nat}
    (seams : MethodContracts.{u,v} resolve anchor entries source catalog (methodsN depth) →
      DefEqReducingSeams.{u,v} resolve anchor entries source catalog depth)
    (transport : DefEqMemoTransport.{u,v} resolve anchor entries source catalog)
    (annotations : SameRawAnnotations.{u,v} entries)
    (binders : DefEqBinderAssumptions.{u,v} resolve anchor entries)
    (resources : DefEqReducingResources.{u,v} resolve anchor entries source catalog) :
    MethodContracts.{u,v} resolve anchor entries source catalog (methodsN depth) →
    ∀ left right, SoundConversion.{u,v} resolve anchor entries source catalog left right
      ((RecM.isDefEq left right).run (methodsN depth)) :=
  fun recursive => StepContracts.isDefEq_of_direct_tiers
    (DefEqSeamAssumptions.ofReducing recursive (seams recursive) transport annotations binders resources)
    resources.tiers recursive

end Assembly

end Ix.Kernel.Consistency
