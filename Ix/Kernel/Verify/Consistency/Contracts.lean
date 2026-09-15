/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.Invariant

/-!
# Method soundness contracts and their induction

The production checker is a recursive knot. Every table `methodsN (n + 1)`
installs the six one-layer bodies with their recursive callbacks bound to
`methodsN n`; reduction calls conversion and inference, conversion calls
reduction and inference, and inference calls both. Their soundness is
therefore one mutual statement proved by induction on the depth, exactly as
`MethodsLocalState.methodsN` closes the structural contract.

This module states that mutual statement over the checker state invariant. A
reduction call from an invariant state on a readable term whose annotated
reading is typed returns an invariant state and a readable result convertible
to the source that retains every type of the source. A conversion call
answering `true` on two such operands establishes conversion of their
annotated readings. Full-mode inference returns a typed annotated reading of
the source and its type; inference-only mode returns a type of an annotated
reading the caller has already checked, which is how production uses that
mode. Every outcome, including every error, preserves the invariant. The
contracts are bundled per table in the layout of `MethodsLocalState`, the
exhausted table satisfies them because it fails without touching the state,
and the successor step unfolds `methodsN (n + 1)` to its bodies. The one-layer
obligations remain `StepContracts`; discharging them for the reduction,
conversion, and inference bodies is the remaining conversion and reduction
work.

Two instances show the shape composes. The hash-equality fast path of
conversion is sound under pairwise address faithfulness and agreement of the
binder annotations of the two readings, since the model interprets binder
conditions. Closed sort inference is the full-mode inference clause restated
from `CheckerInvariant.inferSort`. The contracts carry no collision, size, or
annotation resources of their own; those remain per-call premises, each an
instance of `RunAssumptions`. Matching a memo hit to a caller's annotated
reading needs the memo semantics of the invariant to record that annotation,
which they do not yet.
-/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

section Postconditions

variable {β : Type u} (resolve : Address → Option (ConstRef β))
  (anchor entries : Model.Environment β) (source : Ixon.Env)
  (catalog : List (SourceCacheRequest source)) (locals : List FVarId)
  (context : Model.Context β) (bounds : List VLevel)

/-- One reduction outcome at an annotated reading of the source: the invariant
holds afterwards, and a successful result has an annotated reading that is
convertible to the source and retains every type of the source. -/
def ReductionPost (term : AExpr β) :
    EStateM.Result (TcError .anon) (TcState .anon) (KExpr .anon) → Prop
  | .ok result after =>
      CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds after ∧
      ∃ target : AExpr β, readScopedExpr? resolve locals result = some target.erase ∧
        ConversionClaim.{u,v} entries context term target ∧
        ∀ type, TypingClaim.{u,v} entries context term type →
          TypingClaim.{u,v} entries context target type
  | .error _ after =>
      CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds after

/-- One conversion outcome at annotated readings of the two operands: the
invariant holds afterwards, and the answer `true` establishes conversion. -/
def ConversionPost (left right : AExpr β) :
    EStateM.Result (TcError .anon) (TcState .anon) Bool → Prop
  | .ok true after =>
      CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds after ∧
      ConversionClaim.{u,v} entries context left right
  | .ok false after =>
      CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds after
  | .error _ after =>
      CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds after

/-- One full-mode inference outcome: the invariant holds afterwards, and a
successful result is a typed annotated reading of the source and its type. -/
def FullInferencePost (input : KExpr .anon) :
    EStateM.Result (TcError .anon) (TcState .anon) (KExpr .anon) → Prop
  | .ok result after =>
      CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds after ∧
      ScopedModelTyping.{u,v} resolve entries locals context input result
  | .error _ after =>
      CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds after

/-- One inference-only outcome at an already checked annotated reading of the
source: the invariant holds afterwards, and a successful result reads to a
type of that same annotated term. -/
def InferenceOnlyPost (term : AExpr β) :
    EStateM.Result (TcError .anon) (TcState .anon) (KExpr .anon) → Prop
  | .ok result after =>
      CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds after ∧
      ∃ type : AExpr β, readScopedExpr? resolve locals result = some type.erase ∧
        TypingClaim.{u,v} entries context term type
  | .error _ after =>
      CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds after

end Postconditions

section Contracts

variable {β : Type u} (resolve : Address → Option (ConstRef β))
  (anchor entries : Model.Environment β) (source : Ixon.Env)
  (catalog : List (SourceCacheRequest source))

/-- A reduction call is sound in every scope: from an invariant state and a
readable source whose annotated reading is typed, its outcome satisfies
`ReductionPost` at that reading. -/
def SoundReduction (input : KExpr .anon) (action : TcM .anon (KExpr .anon)) : Prop :=
  ∀ (locals : List FVarId) (context : Model.Context β) (bounds : List VLevel)
    (before : TcState .anon) (term : AExpr β),
    CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before →
    readScopedExpr? resolve locals input = some term.erase →
    (∃ type, TypingClaim.{u,v} entries context term type) →
    ReductionPost.{u,v} resolve anchor entries source catalog locals context bounds term (action before)

/-- A conversion call is sound in every scope: from an invariant state and two
readable operands whose annotated readings are typed, its outcome satisfies
`ConversionPost` at those readings. -/
def SoundConversion (left right : KExpr .anon) (action : TcM .anon Bool) : Prop :=
  ∀ (locals : List FVarId) (context : Model.Context β) (bounds : List VLevel)
    (before : TcState .anon) (a b : AExpr β),
    CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before →
    readScopedExpr? resolve locals left = some a.erase →
    (∃ type, TypingClaim.{u,v} entries context a type) →
    readScopedExpr? resolve locals right = some b.erase →
    (∃ type, TypingClaim.{u,v} entries context b type) →
    ConversionPost.{u,v} resolve anchor entries source catalog locals context bounds a b (action before)

/-- An inference call is sound in every scope under both checking policies.
Full mode needs only a readable source; inference-only mode is given an
already checked annotated reading of the source. -/
structure SoundInference (input : KExpr .anon) (action : TcM .anon (KExpr .anon)) : Prop where
  full : ∀ (locals : List FVarId) (context : Model.Context β) (bounds : List VLevel)
    (before : TcState .anon) (reading : VExpr β),
    CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before →
    before.inferOnly = false →
    readScopedExpr? resolve locals input = some reading →
    FullInferencePost.{u,v} resolve anchor entries source catalog locals context bounds input
      (action before)
  only : ∀ (locals : List FVarId) (context : Model.Context β) (bounds : List VLevel)
    (before : TcState .anon) (term type : AExpr β),
    CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before →
    before.inferOnly = true →
    readScopedExpr? resolve locals input = some term.erase →
    TypingClaim.{u,v} entries context term type →
    InferenceOnlyPost.{u,v} resolve anchor entries source catalog locals context bounds term
      (action before)

/-- The reduction contract of a method table, one clause per reduction field. -/
structure WhnfContract (methods : Methods .anon) : Prop where
  whnf : ∀ term, SoundReduction.{u,v} resolve anchor entries source catalog term (methods.whnf term)
  whnfCore : ∀ term,
    SoundReduction.{u,v} resolve anchor entries source catalog term (methods.whnfCore term)
  whnfMode : ∀ term mode,
    SoundReduction.{u,v} resolve anchor entries source catalog term (methods.whnfMode term mode)
  whnfCoreFlags : ∀ term flags,
    SoundReduction.{u,v} resolve anchor entries source catalog term (methods.whnfCoreFlags term flags)

/-- The conversion contract of a method table. -/
structure DefEqContract (methods : Methods .anon) : Prop where
  isDefEq : ∀ left right,
    SoundConversion.{u,v} resolve anchor entries source catalog left right (methods.isDefEq left right)

/-- The inference contract of a method table. -/
structure InferContract (methods : Methods .anon) : Prop where
  infer : ∀ term, SoundInference.{u,v} resolve anchor entries source catalog term (methods.infer term)

/-- The six method contracts of one table, in the layout of `MethodsLocalState`. -/
structure MethodContracts (methods : Methods .anon) : Prop extends
    WhnfContract.{u,v} resolve anchor entries source catalog methods,
    DefEqContract.{u,v} resolve anchor entries source catalog methods,
    InferContract.{u,v} resolve anchor entries source catalog methods

/-- The one-layer obligations at one depth: each production body that
`methodsN (depth + 1)` installs satisfies its contract whenever its recursive
callbacks `methodsN depth` satisfy theirs. Discharging these fields is the
conversion and reduction work. -/
structure StepContracts (depth : Nat) : Prop where
  whnf : MethodContracts.{u,v} resolve anchor entries source catalog (methodsN depth) →
    ∀ term, SoundReduction.{u,v} resolve anchor entries source catalog term
      ((RecM.whnf term).run (methodsN depth))
  whnfCore : MethodContracts.{u,v} resolve anchor entries source catalog (methodsN depth) →
    ∀ term, SoundReduction.{u,v} resolve anchor entries source catalog term
      ((RecM.whnfCore term).run (methodsN depth))
  whnfMode : MethodContracts.{u,v} resolve anchor entries source catalog (methodsN depth) →
    ∀ term mode, SoundReduction.{u,v} resolve anchor entries source catalog term
      ((RecM.whnfWithNatSuccMode term mode).run (methodsN depth))
  whnfCoreFlags : MethodContracts.{u,v} resolve anchor entries source catalog (methodsN depth) →
    ∀ term flags, SoundReduction.{u,v} resolve anchor entries source catalog term
      ((RecM.whnfCoreWithFlags term flags).run (methodsN depth))
  infer : MethodContracts.{u,v} resolve anchor entries source catalog (methodsN depth) →
    ∀ term, SoundInference.{u,v} resolve anchor entries source catalog term
      ((RecM.infer term).run (methodsN depth))
  isDefEq : MethodContracts.{u,v} resolve anchor entries source catalog (methodsN depth) →
    ∀ left right, SoundConversion.{u,v} resolve anchor entries source catalog left right
      ((RecM.isDefEq left right).run (methodsN depth))

end Contracts

section Failure

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {anchor entries : Model.Environment β} {source : Ixon.Env}
  {catalog : List (SourceCacheRequest source)}

/-- A call that fails without touching the state is a sound reduction. -/
theorem SoundReduction.throw {input : KExpr .anon} {error : TcError .anon} :
    SoundReduction.{u,v} resolve anchor entries source catalog input (throw error) :=
  fun _ _ _ _ _ valid _ _ => valid

/-- A call that fails without touching the state is a sound conversion. -/
theorem SoundConversion.throw {left right : KExpr .anon} {error : TcError .anon} :
    SoundConversion.{u,v} resolve anchor entries source catalog left right (throw error) :=
  fun _ _ _ _ _ _ valid _ _ _ _ => valid

/-- A call that fails without touching the state is a sound inference. -/
theorem SoundInference.throw {input : KExpr .anon} {error : TcError .anon} :
    SoundInference.{u,v} resolve anchor entries source catalog input (throw error) where
  full := fun _ _ _ _ _ valid _ _ => valid
  only := fun _ _ _ _ _ _ valid _ _ _ => valid

end Failure

namespace MethodContracts

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {anchor entries : Model.Environment β} {source : Ixon.Env}
  {catalog : List (SourceCacheRequest source)}

/-- The exhausted table fails every call without touching the state. -/
theorem zero :
    MethodContracts.{u,v} resolve anchor entries source catalog (_root_.Ix.Kernel.methodsN 0) where
  whnf := fun _ => SoundReduction.throw
  whnfCore := fun _ => SoundReduction.throw
  whnfMode := fun _ _ => SoundReduction.throw
  whnfCoreFlags := fun _ _ => SoundReduction.throw
  isDefEq := fun _ _ => SoundConversion.throw
  infer := fun _ => SoundInference.throw

/-- One induction step: `methodsN (depth + 1)` installs exactly the bodies
whose contracts `StepContracts depth` supplies from the smaller table's. -/
theorem succ {depth : Nat}
    (recursive : MethodContracts.{u,v} resolve anchor entries source catalog
      (_root_.Ix.Kernel.methodsN depth))
    (step : StepContracts.{u,v} resolve anchor entries source catalog depth) :
    MethodContracts.{u,v} resolve anchor entries source catalog
      (_root_.Ix.Kernel.methodsN (depth + 1)) where
  whnf := step.whnf recursive
  whnfCore := step.whnfCore recursive
  whnfMode := step.whnfMode recursive
  whnfCoreFlags := step.whnfCoreFlags recursive
  isDefEq := step.isDefEq recursive
  infer := step.infer recursive

/-- Every finite production table satisfies the contracts once every one-layer
obligation is discharged. -/
theorem methodsN (steps : ∀ depth, StepContracts.{u,v} resolve anchor entries source catalog depth) :
    ∀ depth, MethodContracts.{u,v} resolve anchor entries source catalog
      (_root_.Ix.Kernel.methodsN depth)
  | 0 => zero
  | depth + 1 => (methodsN steps depth).succ (steps depth)

end MethodContracts

section Instances

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {anchor entries : Model.Environment β} {source : Ixon.Env}
  {catalog : List (SourceCacheRequest source)} {locals : List FVarId}
  {context : Model.Context β} {bounds : List VLevel}

/-- The hash-equality fast path of conversion. Address faithfulness identifies
the two readings and agreement of their binder annotations identifies the
annotated terms, so the answer `true` is reflexive conversion after only the
statistics update. -/
theorem DefEqContract.hashPath {left right : KExpr .anon} {a b : AExpr β}
    {methods : Methods .anon} {before after : TcState .anon}
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (faithful : left.AddrFaithful right) (conditions : a.annotations = b.annotations)
    (equal : (left.addr == right.addr) = true)
    (leftReads : readScopedExpr? resolve locals left = some a.erase)
    (rightReads : readScopedExpr? resolve locals right = some b.erase)
    (accepted : RecM.isDefEq left right methods before = .ok true after) :
    ConversionPost.{u,v} resolve anchor entries source catalog locals context bounds a b
      (.ok true after) := by
  have sameReading := beq_readScopedExpr? (resolve := resolve) (locals := locals) (depth := 0)
    faithful (by rw [KExpr.beq_def]; exact equal)
  have erased : a.erase = b.erase :=
    Option.some.inj (leftReads.symm.trans (sameReading.trans rightReads))
  cases AExpr.eq_of_erase_annotations erased conditions
  refine And.intro ?_ (ConversionClaim.refl a)
  rw [isDefEq_hash_state equal] at accepted
  split at accepted <;> cases accepted
  · exact valid.ofMaps ⟨Nat.le_refl _, .refl _, rfl⟩ rfl rfl valid.coherent rfl rfl
      (fun partition => by cases partition <;> rfl) (fun partition => by cases partition <;> rfl)
      rfl rfl rfl
  · exact valid

/-- Closed sort inference is the full-mode inference clause at a sort:
`CheckerInvariant.inferSort` returns the invariant and the typed reading. -/
theorem InferContract.sortPath {level : KUniv .anon} {fuel : Nat} {result : KExpr .anon}
    {before after : TcState .anon}
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (member : SourceCacheRequest.sort level ∈ catalog)
    (keyData : SourceCacheKeyData catalog (KExpr.mkSort level))
    (faithful : KExpr.KeyCollisionFree fun term => before.env.intern.ExprSupport term ∨
      term = KExpr.mkSort (KUniv.mkSucc level))
    (accepted : RecM.infer (KExpr.mkSort level) (methodsN fuel) before = .ok result after) :
    FullInferencePost.{u,v} resolve anchor entries source catalog locals context bounds
      (KExpr.mkSort level) (.ok result after) := by
  obtain ⟨preserved, _, typed⟩ := valid.inferSort member keyData faithful accepted
  exact And.intro preserved typed

end Instances

end Ix.Kernel.Consistency
