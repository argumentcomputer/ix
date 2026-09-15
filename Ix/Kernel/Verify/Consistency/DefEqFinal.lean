/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.DefEqReducing

/-!
# The final DefEq tiers under the contracts

After lazy delta stops, production runs post-delta structural congruence, a
second structural pass through `whnfCore`, the application-spine comparison,
and the final WHNF tier: the constructor-directed structural prefix, Nat
bridging, lambda eta, string expansion, structure eta, unit-like types, and
proof irrelevance. This module proves each tier sound against the checker
invariant with the recursive callbacks abstracted by the smaller table's
contracts and the reducer seams of `DefEqReducingSeams`:

* the structural prefix decides sorts by universe equality, constants by the
  universe gate, applications by the recursive callback on both parts, and
  matching binders by the common-local comparison; legacy variables and
  string literals have no reading, so their branches are vacuous, and the
  let branch is the `whnfLet` seam;
* lambda eta infers and normalizes the non-lambda operand's type through the
  smaller table and the reducer seam, converts the operand to the exposed
  dependent function type, and compares the constructed expansion through the
  `compareEta` seam; `ConversionClaim.eta` is the seam implementer's tool;
* the string, Nat, structure-eta, and unit-like phases are the corresponding
  seams, and the last fallback is proof irrelevance;
* post-delta congruence compares constants by the universe gate and
  projections through the projection-delta seam; the spine comparison
  composes the head callback with the argument loop.

Every branch that answers by address equality uses the hash path under
address faithfulness and the annotation discipline.
-/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

/-! ### Branch combinators on outcomes -/

section Branches

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {anchor entries : Model.Environment β} {source : Ixon.Env}
  {catalog : List (SourceCacheRequest source)} {locals : List FVarId}
  {context : Model.Context β} {bounds : List VLevel} {methods : Methods .anon}
  {before : TcState .anon} {a b : AExpr β}

theorem ConversionPost.ite {c : Prop} [Decidable c] {left right : RecM .anon Bool}
    (thenSound : c → ConversionPost.{u,v} resolve anchor entries source catalog locals context bounds
      a b (left.run methods before))
    (elseSound : ¬ c → ConversionPost.{u,v} resolve anchor entries source catalog locals context bounds
      a b (right.run methods before)) :
    ConversionPost.{u,v} resolve anchor entries source catalog locals context bounds a b
      ((if c then left else right).run methods before) := by
  by_cases h : c
  · rw [if_pos h]
    exact thenSound h
  · rw [if_neg h]
    exact elseSound h

theorem OptionalConversionPost.ite {c : Prop} [Decidable c] {left right : RecM .anon (Option Bool)}
    (thenSound : c → OptionalConversionPost.{u,v} resolve anchor entries source catalog locals context
      bounds a b (left.run methods before))
    (elseSound : ¬ c → OptionalConversionPost.{u,v} resolve anchor entries source catalog locals context
      bounds a b (right.run methods before)) :
    OptionalConversionPost.{u,v} resolve anchor entries source catalog locals context bounds a b
      ((if c then left else right).run methods before) := by
  by_cases h : c
  · rw [if_pos h]
    exact thenSound h
  · rw [if_neg h]
    exact elseSound h

theorem ConversionPost.pureTrue
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (claim : ConversionClaim.{u,v} entries context a b) :
    ConversionPost.{u,v} resolve anchor entries source catalog locals context bounds a b
      ((pure true : RecM .anon Bool).run methods before) := by
  rw [pure_run]
  exact ⟨valid, claim⟩

theorem ConversionPost.pureFalse
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before) :
    ConversionPost.{u,v} resolve anchor entries source catalog locals context bounds a b
      ((pure false : RecM .anon Bool).run methods before) := by
  rw [pure_run]
  exact valid

theorem OptionalConversionPost.pureNone
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before) :
    OptionalConversionPost.{u,v} resolve anchor entries source catalog locals context bounds a b
      ((pure none : RecM .anon (Option Bool)).run methods before) := by
  rw [pure_run]
  exact valid

theorem OptionalConversionPost.pureSome
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (answer : Bool) (claim : answer = true → ConversionClaim.{u,v} entries context a b) :
    OptionalConversionPost.{u,v} resolve anchor entries source catalog locals context bounds a b
      ((pure (some answer) : RecM .anon (Option Bool)).run methods before) := by
  rw [pure_run]
  cases answer with
  | true => exact ⟨valid, claim rfl⟩
  | false => exact valid

/-- A terminal optional answer is a conversion answer. -/
theorem OptionalConversionPost.answer {answer : Bool} {after : TcState .anon}
    (post : OptionalConversionPost.{u,v} resolve anchor entries source catalog locals context bounds a b
      (.ok (some answer) after)) :
    ConversionPost.{u,v} resolve anchor entries source catalog locals context bounds a b
      (.ok answer after) := by
  cases answer <;> exact post

/-- The production shape `match ← probe with | some answer => return answer | none => rest`. -/
theorem ConversionPost.optionalThen {probe : RecM .anon (Option Bool)} {rest : RecM .anon Bool}
    (probeSound : OptionalConversionPost.{u,v} resolve anchor entries source catalog locals context bounds
      a b (probe.run methods before))
    (restSound : ∀ state,
      CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds state →
      ConversionPost.{u,v} resolve anchor entries source catalog locals context bounds a b
        (rest.run methods state)) :
    ConversionPost.{u,v} resolve anchor entries source catalog locals context bounds a b
      ((probe >>= fun answer? => match answer? with
        | some answer => pure answer
        | none => rest).run methods before) := by
  simp only [ReaderT.run_bind]
  cases run : probe.run methods before with
  | error err after =>
      rw [EStateM.run_bind_error run]
      rw [run] at probeSound
      exact probeSound
  | ok answer? after =>
      rw [EStateM.run_bind_ok run]
      rw [run] at probeSound
      cases answer? with
      | none => exact restSound after probeSound
      | some answer =>
          try dsimp only
          rw [pure_run]
          exact probeSound.answer

end Branches

/-! ### The constructor-directed structural prefix -/

section Structural

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {anchor entries : Model.Environment β} {source : Ixon.Env}
  {catalog : List (SourceCacheRequest source)}

/-- The short-circuiting application branch: both parts through the recursive callback. -/
theorem tryDefEqWhnfApp_sound {methods : Methods .anon}
    (recursive : DefEqContract.{u,v} resolve anchor entries source catalog methods)
    (appHereditary : ∀ (context : Model.Context β) (fn arg type : AExpr β),
      TypingClaim.{u,v} entries context (.app fn arg) type →
      (∃ type, TypingClaim.{u,v} entries context fn type) ∧
      (∃ type, TypingClaim.{u,v} entries context arg type))
    {locals : List FVarId} {context : Model.Context β} {bounds : List VLevel} {before : TcState .anon}
    {f1 a1 f2 a2 : KExpr .anon} {info1 info2 : ExprInfo .anon} {a b : AExpr β}
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (leftReads : readScopedExpr? resolve locals (.app f1 a1 info1) = some a.erase)
    (leftTyped : ∃ type, TypingClaim.{u,v} entries context a type)
    (rightReads : readScopedExpr? resolve locals (.app f2 a2 info2) = some b.erase)
    (rightTyped : ∃ type, TypingClaim.{u,v} entries context b type) :
    OptionalConversionPost.{u,v} resolve anchor entries source catalog locals context bounds a b
      ((RecM.tryDefEqWhnfApp f1 a1 f2 a2).run methods before) := by
  obtain ⟨F1, A1, aEq, f1Reads, a1Reads⟩ := readScopedExpr?_app_annotated leftReads
  obtain ⟨F2, A2, bEq, f2Reads, a2Reads⟩ := readScopedExpr?_app_annotated rightReads
  subst aEq bEq
  obtain ⟨T1, typed1⟩ := leftTyped
  obtain ⟨T2, typed2⟩ := rightTyped
  obtain ⟨f1Typed, a1Typed⟩ := appHereditary context F1 A1 T1 typed1
  obtain ⟨f2Typed, a2Typed⟩ := appHereditary context F2 A2 T2 typed2
  unfold RecM.tryDefEqWhnfApp
  simp only [ReaderT.run_bind, isDefEqCall_run]
  have heads := recursive.isDefEq f1 f2 locals context bounds before F1 F2 valid f1Reads f1Typed f2Reads
    f2Typed
  cases runF : methods.isDefEq f1 f2 before with
  | error err s₁ =>
      rw [EStateM.run_bind_error runF]
      rw [runF] at heads
      exact heads
  | ok headAnswer s₁ =>
      rw [EStateM.run_bind_ok runF]
      rw [runF] at heads
      cases headAnswer with
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact OptionalConversionPost.pureNone heads
      | true =>
          obtain ⟨valid₁, headClaim⟩ := heads
          simp only [↓reduceIte]
          simp only [ReaderT.run_bind, isDefEqCall_run]
          have args := recursive.isDefEq a1 a2 locals context bounds s₁ A1 A2 valid₁ a1Reads a1Typed
            a2Reads a2Typed
          cases runA : methods.isDefEq a1 a2 s₁ with
          | error err s₂ =>
              rw [EStateM.run_bind_error runA]
              rw [runA] at args
              exact args
          | ok argAnswer s₂ =>
              rw [EStateM.run_bind_ok runA]
              rw [runA] at args
              cases argAnswer with
              | false =>
                  simp only [Bool.false_eq_true, ↓reduceIte]
                  exact OptionalConversionPost.pureNone args
              | true =>
                  simp only [↓reduceIte]
                  exact OptionalConversionPost.pureSome args.1 true
                    (fun _ => ConversionClaim.app headClaim args.2)

/-- The constructor-directed prefix of the final tier. -/
theorem tryDefEqWhnfStructural_sound {depth : Nat}
    (recursive : MethodContracts.{u,v} resolve anchor entries source catalog (methodsN depth))
    (seams : DefEqReducingSeams.{u,v} resolve anchor entries source catalog depth)
    (binders : DefEqBinderAssumptions.{u,v} resolve anchor entries)
    (resources : DefEqReducingResources.{u,v} resolve anchor entries source catalog)
    (left right : KExpr .anon) :
    SoundOptionalConversion.{u,v} resolve anchor entries source catalog left right
      ((RecM.tryDefEqWhnfStructural left right).run (methodsN depth)) := by
  intro locals context bounds before a b valid leftReads leftTyped rightReads rightTyped
  unfold RecM.tryDefEqWhnfStructural
  split
  · rename_i u1 info1 u2 info2
    rw [pure_run]
    cases accepted : univEq u1 u2
    · exact valid
    · obtain ⟨faithful, boundU, boundV⟩ := resources.tiers.sorts u1 u2 info1 info2 trivial trivial
      have aEq := readScopedExpr?_sort_annotated leftReads
      have bEq := readScopedExpr?_sort_annotated rightReads
      subst aEq bEq
      exact ⟨valid, ConversionClaim.sort
        (Theory.VLevel.equiv_def.mp (univEq_sound faithful boundU boundV accepted))⟩
  · rw [readScopedExpr?_var_none] at leftReads
    cases leftReads
  · rename_i id1 us1 info1 id2 us2 info2
    refine OptionalConversionPost.ite ?_ ?_
    · intro gate
      simp only [Bool.and_eq_true, beq_iff_eq] at gate
      exact OptionalConversionPost.pureSome valid true fun _ =>
        ConversionClaim.constInstances leftReads rightReads gate.1 gate.2
          (fun u _ v _ => resources.tiers.sorts u v info1 info2 trivial trivial)
    · intro _
      exact OptionalConversionPost.pureNone valid
  · rename_i f1 a1 info1 f2 a2 info2
    have post := tryDefEqWhnfApp_sound recursive.toDefEqContract seams.appHereditary
      (info1 := info1) (info2 := info2) valid leftReads leftTyped rightReads rightTyped
    exact post
  · rename_i name1 bi1 ty1 body1 info1 name2 bi2 ty2 body2 info2
    have quick := quickDefEq_sound recursive.toDefEqContract (MethodsLocalState.methodsN depth) binders
      resources.tiers valid trivial trivial leftReads leftTyped rightReads rightTyped
    rw [quickDefEq_eq] at quick
    dsimp only at quick
    simp only [ReaderT.run_bind]
    cases run : (RecM.quickBinder name1 bi1 ty1 body1 ty2 body2).run (methodsN depth) before with
    | error err after =>
        rw [EStateM.run_bind_error run]
        rw [run] at quick
        exact quick
    | ok answer after =>
        rw [EStateM.run_bind_ok run]
        rw [run] at quick
        cases answer with
        | true =>
            simp only [↓reduceIte]
            exact OptionalConversionPost.pureSome quick.1 true fun _ => quick.2
        | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact OptionalConversionPost.pureNone quick
  · rename_i name1 bi1 ty1 body1 info1 name2 bi2 ty2 body2 info2
    have quick := quickDefEq_sound recursive.toDefEqContract (MethodsLocalState.methodsN depth) binders
      resources.tiers valid trivial trivial leftReads leftTyped rightReads rightTyped
    rw [quickDefEq_eq] at quick
    dsimp only at quick
    simp only [ReaderT.run_bind]
    cases run : (RecM.quickBinder name1 bi1 ty1 body1 ty2 body2).run (methodsN depth) before with
    | error err after =>
        rw [EStateM.run_bind_error run]
        rw [run] at quick
        exact quick
    | ok answer after =>
        rw [EStateM.run_bind_ok run]
        rw [run] at quick
        cases answer with
        | true =>
            simp only [↓reduceIte]
            exact OptionalConversionPost.pureSome quick.1 true fun _ => quick.2
        | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact OptionalConversionPost.pureNone quick
  · rename_i name1 ty1 v1 body1 nonDep1 info1 name2 ty2 v2 body2 nonDep2 info2
    have post := seams.whnfLet name1 ty1 v1 body1 ty2 v2 body2 nonDep1 nonDep2 info1 info2 locals context
      bounds before a b valid leftReads leftTyped rightReads rightTyped
    exact post
  · rename_i v1 blob1 info1 v2 blob2 info2
    rw [pure_run]
    cases equal : v1 == v2
    · exact valid
    · have aEq := readScopedExpr?_nat_annotated leftReads
      have bEq := readScopedExpr?_nat_annotated rightReads
      subst aEq bEq
      rw [beq_iff_eq] at equal
      subst equal
      exact ⟨valid, ConversionClaim.refl _⟩
  · rw [readScopedExpr?_str_none] at leftReads
    cases leftReads
  · exact OptionalConversionPost.pureNone valid

end Structural

/-! ### Lambda eta -/

section Eta

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {anchor entries : Model.Environment β} {source : Ixon.Env}
  {catalog : List (SourceCacheRequest source)}

set_option maxHeartbeats 1000000 in
/-- After the syntactic guard: the non-lambda operand's type is inferred and
normalized to a dependent function type, and the constructed expansion is
compared through the seam. -/
theorem tryEtaExpansionAfterGuard_sound {depth : Nat}
    (recursive : MethodContracts.{u,v} resolve anchor entries source catalog (methodsN depth))
    (seams : DefEqReducingSeams.{u,v} resolve anchor entries source catalog depth)
    (t s : KExpr .anon) :
    SoundConversion.{u,v} resolve anchor entries source catalog t s
      ((RecM.tryEtaExpansionAfterGuard t s).run (methodsN depth)) := by
  intro locals context bounds before T S valid tReads tTyped sReads sTyped
  obtain ⟨Ts, typedS⟩ := sTyped
  unfold RecM.tryEtaExpansionAfterGuard
  simp only [ReaderT.run_bind]
  have probe := tryInferOnly_sound (methods := methodsN depth) recursive.toInferContract valid sReads typedS
  cases runI : (RecM.try? (RecM.inferOnlyCall s)).run (methodsN depth) before with
  | error err s₁ =>
      rw [EStateM.run_bind_error runI]
      rw [runI] at probe
      exact probe
  | ok type? s₁ =>
      rw [EStateM.run_bind_ok runI]
      rw [runI] at probe
      cases type? with
      | none =>
          try dsimp only
          exact ConversionPost.pureFalse probe
      | some sType =>
          obtain ⟨valid₁, Sty, styReads, typedSty⟩ := probe
          obtain ⟨level, formedSty⟩ := seams.typeFormation context S Sty typedSty
          try dsimp only
          simp only [ReaderT.run_bind]
          have reduced := seams.whnf sType locals context bounds s₁ Sty valid₁ styReads ⟨_, formedSty⟩
          cases runW : (RecM.whnf sType).run (methodsN depth) s₁ with
          | error err s₂ =>
              have caught : (RecM.try? (RecM.whnf sType)).run (methodsN depth) s₁ = .ok none s₂ := by
                rw [try?_run, runW]
              rw [EStateM.run_bind_ok caught]
              rw [runW] at reduced
              try dsimp only
              exact ConversionPost.pureFalse reduced
          | ok w s₂ =>
              have caught : (RecM.try? (RecM.whnf sType)).run (methodsN depth) s₁ = .ok (some w) s₂ := by
                rw [try?_run, runW]
              rw [EStateM.run_bind_ok caught]
              rw [runW] at reduced
              obtain ⟨valid₂, W, wReads, claimW, typesW⟩ := reduced
              try dsimp only
              split
              · rename_i name bi ty body info
                obtain ⟨condition, A, B, wEq, tyReads, _⟩ := readScopedExpr?_all_annotated wReads
                subst wEq
                have branch : ConversionPost.{u,v} resolve anchor entries source catalog locals context
                    bounds T S ((RecM.compareEtaExpansion t s name bi ty).run (methodsN depth) s₂) :=
                  seams.compareEta t s name bi ty locals context bounds s₂ T S A B condition valid₂
                    tReads tTyped sReads tyReads
                    (TypingClaim.conv typedSty (typesW _ formedSty) claimW)
                exact branch
              · exact ConversionPost.pureFalse valid₂

/-- Lambda eta: a lambda against a non-lambda. -/
theorem tryEtaExpansion_sound {depth : Nat}
    (recursive : MethodContracts.{u,v} resolve anchor entries source catalog (methodsN depth))
    (seams : DefEqReducingSeams.{u,v} resolve anchor entries source catalog depth)
    (t s : KExpr .anon) :
    SoundConversion.{u,v} resolve anchor entries source catalog t s
      ((RecM.tryEtaExpansion t s).run (methodsN depth)) := by
  intro locals context bounds before T S valid tReads tTyped sReads sTyped
  unfold RecM.tryEtaExpansion
  try dsimp only
  refine ConversionPost.ite (fun _ => ConversionPost.pureFalse valid) fun _ => ?_
  exact tryEtaExpansionAfterGuard_sound recursive seams t s locals context bounds before T S valid tReads
    tTyped sReads sTyped

/-- Both eta directions after the outer guard. -/
theorem tryDefEqWhnfEtaAfterGuard_sound {depth : Nat}
    (recursive : MethodContracts.{u,v} resolve anchor entries source catalog (methodsN depth))
    (seams : DefEqReducingSeams.{u,v} resolve anchor entries source catalog depth)
    (left right : KExpr .anon) :
    SoundOptionalConversion.{u,v} resolve anchor entries source catalog left right
      ((RecM.tryDefEqWhnfEtaAfterGuard left right).run (methodsN depth)) := by
  intro locals context bounds before a b valid leftReads leftTyped rightReads rightTyped
  unfold RecM.tryDefEqWhnfEtaAfterGuard
  simp only [ReaderT.run_bind]
  have first := tryEtaExpansion_sound recursive seams left right locals context bounds before a b valid
    leftReads leftTyped rightReads rightTyped
  cases run₁ : (RecM.tryEtaExpansion left right).run (methodsN depth) before with
  | error err s₁ =>
      rw [EStateM.run_bind_error run₁]
      rw [run₁] at first
      exact first
  | ok answer s₁ =>
      rw [EStateM.run_bind_ok run₁]
      rw [run₁] at first
      cases answer with
      | true =>
          simp only [↓reduceIte]
          exact OptionalConversionPost.pureSome first.1 true fun _ => first.2
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          simp only [ReaderT.run_bind]
          have second := tryEtaExpansion_sound recursive seams right left locals context bounds s₁ b a first
            rightReads rightTyped leftReads leftTyped
          cases run₂ : (RecM.tryEtaExpansion right left).run (methodsN depth) s₁ with
          | error err s₂ =>
              rw [EStateM.run_bind_error run₂]
              rw [run₂] at second
              exact second
          | ok answer s₂ =>
              rw [EStateM.run_bind_ok run₂]
              rw [run₂] at second
              cases answer with
              | true =>
                  simp only [↓reduceIte]
                  exact OptionalConversionPost.pureSome second.1 true fun _ => second.2.symm
              | false =>
                  simp only [Bool.false_eq_true, ↓reduceIte]
                  exact OptionalConversionPost.pureNone second

/-- The lambda-eta phase: the guard only selects the ordered attempts. -/
theorem tryDefEqWhnfEta_sound {depth : Nat}
    (recursive : MethodContracts.{u,v} resolve anchor entries source catalog (methodsN depth))
    (seams : DefEqReducingSeams.{u,v} resolve anchor entries source catalog depth)
    (left right : KExpr .anon) :
    SoundOptionalConversion.{u,v} resolve anchor entries source catalog left right
      ((RecM.tryDefEqWhnfEta left right).run (methodsN depth)) := by
  intro locals context bounds before a b valid leftReads leftTyped rightReads rightTyped
  unfold RecM.tryDefEqWhnfEta
  try dsimp only
  refine OptionalConversionPost.ite (fun _ => ?_) fun _ => OptionalConversionPost.pureNone valid
  exact tryDefEqWhnfEtaAfterGuard_sound recursive seams left right locals context bounds before a b valid
    leftReads leftTyped rightReads rightTyped

/-- String expansion is never reached on readable operands. -/
theorem tryDefEqWhnfString_sound {methods : Methods .anon} (left right : KExpr .anon) :
    SoundOptionalConversion.{u,v} resolve anchor entries source catalog left right
      ((RecM.tryDefEqWhnfString left right).run methods) := by
  intro locals context bounds before a b valid leftReads leftTyped rightReads rightTyped
  unfold RecM.tryDefEqWhnfString
  rw [hasStringLiteralPair_eq_false leftReads rightReads]
  simp only [Bool.false_eq_true, ↓reduceIte]
  exact OptionalConversionPost.pureNone valid

end Eta

/-! ### The final tier assembled -/

section Final

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {anchor entries : Model.Environment β} {source : Ixon.Env}
  {catalog : List (SourceCacheRequest source)}

/-- Unit-like types, then proof irrelevance. -/
theorem isDefEqWhnfAfterStructEta_sound {depth : Nat}
    (recursive : MethodContracts.{u,v} resolve anchor entries source catalog (methodsN depth))
    (seams : DefEqReducingSeams.{u,v} resolve anchor entries source catalog depth)
    (resources : DefEqReducingResources.{u,v} resolve anchor entries source catalog)
    (left right : KExpr .anon) :
    SoundConversion.{u,v} resolve anchor entries source catalog left right
      ((RecM.isDefEqWhnfAfterStructEta left right).run (methodsN depth)) := by
  intro locals context bounds before a b valid leftReads leftTyped rightReads rightTyped
  unfold RecM.isDefEqWhnfAfterStructEta
  simp only [ReaderT.run_bind]
  have unit := seams.unit left right locals context bounds before a b valid leftReads leftTyped rightReads
    rightTyped
  cases run : (RecM.tryDefEqUnit left right).run (methodsN depth) before with
  | error err s₁ =>
      rw [EStateM.run_bind_error run]
      rw [run] at unit
      exact unit
  | ok answer s₁ =>
      rw [EStateM.run_bind_ok run]
      rw [run] at unit
      cases answer with
      | true =>
          simp only [↓reduceIte]
          exact ConversionPost.pureTrue unit.1 unit.2
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          unfold RecM.isDefEqWhnfAfterUnit
          exact tryProofIrrel_sound recursive seams resources left right locals context bounds s₁ a b unit
            leftReads leftTyped rightReads rightTyped

/-- Structure eta, then the unit-like and proof-irrelevance fallbacks. -/
theorem isDefEqWhnfAfterString_sound {depth : Nat}
    (recursive : MethodContracts.{u,v} resolve anchor entries source catalog (methodsN depth))
    (seams : DefEqReducingSeams.{u,v} resolve anchor entries source catalog depth)
    (resources : DefEqReducingResources.{u,v} resolve anchor entries source catalog)
    (left right : KExpr .anon) :
    SoundConversion.{u,v} resolve anchor entries source catalog left right
      ((RecM.isDefEqWhnfAfterString left right).run (methodsN depth)) := by
  intro locals context bounds before a b valid leftReads leftTyped rightReads rightTyped
  unfold RecM.isDefEqWhnfAfterString
  exact ConversionPost.optionalThen
    (seams.structEta left right locals context bounds before a b valid leftReads leftTyped rightReads
      rightTyped)
    (fun state valid' => isDefEqWhnfAfterStructEta_sound recursive seams resources left right locals context
      bounds state a b valid' leftReads leftTyped rightReads rightTyped)

/-- String expansion (vacuous), then the remaining fallbacks. -/
theorem isDefEqWhnfAfterEta_sound {depth : Nat}
    (recursive : MethodContracts.{u,v} resolve anchor entries source catalog (methodsN depth))
    (seams : DefEqReducingSeams.{u,v} resolve anchor entries source catalog depth)
    (resources : DefEqReducingResources.{u,v} resolve anchor entries source catalog)
    (left right : KExpr .anon) :
    SoundConversion.{u,v} resolve anchor entries source catalog left right
      ((RecM.isDefEqWhnfAfterEta left right).run (methodsN depth)) := by
  intro locals context bounds before a b valid leftReads leftTyped rightReads rightTyped
  unfold RecM.isDefEqWhnfAfterEta
  exact ConversionPost.optionalThen
    (tryDefEqWhnfString_sound left right locals context bounds before a b valid leftReads leftTyped
      rightReads rightTyped)
    (fun state valid' => isDefEqWhnfAfterString_sound recursive seams resources left right locals context
      bounds state a b valid' leftReads leftTyped rightReads rightTyped)

/-- Lambda eta, then the remaining fallbacks. -/
theorem isDefEqWhnfAfterNat_sound {depth : Nat}
    (recursive : MethodContracts.{u,v} resolve anchor entries source catalog (methodsN depth))
    (seams : DefEqReducingSeams.{u,v} resolve anchor entries source catalog depth)
    (resources : DefEqReducingResources.{u,v} resolve anchor entries source catalog)
    (left right : KExpr .anon) :
    SoundConversion.{u,v} resolve anchor entries source catalog left right
      ((RecM.isDefEqWhnfAfterNat left right).run (methodsN depth)) := by
  intro locals context bounds before a b valid leftReads leftTyped rightReads rightTyped
  unfold RecM.isDefEqWhnfAfterNat
  exact ConversionPost.optionalThen
    (tryDefEqWhnfEta_sound recursive seams left right locals context bounds before a b valid leftReads
      leftTyped rightReads rightTyped)
    (fun state valid' => isDefEqWhnfAfterEta_sound recursive seams resources left right locals context
      bounds state a b valid' leftReads leftTyped rightReads rightTyped)

/-- Nat bridging, then the remaining fallbacks. -/
theorem isDefEqWhnfAfterStructural_sound {depth : Nat}
    (recursive : MethodContracts.{u,v} resolve anchor entries source catalog (methodsN depth))
    (seams : DefEqReducingSeams.{u,v} resolve anchor entries source catalog depth)
    (resources : DefEqReducingResources.{u,v} resolve anchor entries source catalog)
    (left right : KExpr .anon) :
    SoundConversion.{u,v} resolve anchor entries source catalog left right
      ((RecM.isDefEqWhnfAfterStructural left right).run (methodsN depth)) := by
  intro locals context bounds before a b valid leftReads leftTyped rightReads rightTyped
  unfold RecM.isDefEqWhnfAfterStructural
  exact ConversionPost.optionalThen
    (seams.whnfNat left right locals context bounds before a b valid leftReads leftTyped rightReads
      rightTyped)
    (fun state valid' => isDefEqWhnfAfterNat_sound recursive seams resources left right locals context
      bounds state a b valid' leftReads leftTyped rightReads rightTyped)

/-- Tier 5: the structural prefix, then the ordered fallbacks. -/
theorem isDefEqWhnf_sound {depth : Nat}
    (recursive : MethodContracts.{u,v} resolve anchor entries source catalog (methodsN depth))
    (seams : DefEqReducingSeams.{u,v} resolve anchor entries source catalog depth)
    (binders : DefEqBinderAssumptions.{u,v} resolve anchor entries)
    (resources : DefEqReducingResources.{u,v} resolve anchor entries source catalog)
    (left right : KExpr .anon) :
    SoundConversion.{u,v} resolve anchor entries source catalog left right
      ((RecM.isDefEqWhnf left right).run (methodsN depth)) := by
  intro locals context bounds before a b valid leftReads leftTyped rightReads rightTyped
  unfold RecM.isDefEqWhnf
  exact ConversionPost.optionalThen
    (tryDefEqWhnfStructural_sound recursive seams binders resources left right locals context bounds before
      a b valid leftReads leftTyped rightReads rightTyped)
    (fun state valid' => isDefEqWhnfAfterStructural_sound recursive seams resources left right locals
      context bounds state a b valid' leftReads leftTyped rightReads rightTyped)

end Final

/-! ### The stopped continuation -/

section Stopped

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {anchor entries : Model.Environment β} {source : Ixon.Env}
  {catalog : List (SourceCacheRequest source)}

/-- Post-delta structural congruence: constants by the universe gate,
projections through the projection-delta seam; legacy variables have no
reading. -/
theorem tryStructuralCongruence_sound {depth : Nat}
    (seams : DefEqReducingSeams.{u,v} resolve anchor entries source catalog depth)
    (resources : DefEqReducingResources.{u,v} resolve anchor entries source catalog)
    (left right : KExpr .anon) :
    SoundConversion.{u,v} resolve anchor entries source catalog left right
      ((RecM.tryStructuralCongruence left right).run (methodsN depth)) := by
  intro locals context bounds before a b valid leftReads leftTyped rightReads rightTyped
  unfold RecM.tryStructuralCongruence
  split
  · rename_i id1 us1 info1 id2 us2 info2
    rw [pure_run]
    cases gate : (id1.addr == id2.addr && RecM.sameDefEqUniverses us1 us2)
    · exact valid
    · simp only [Bool.and_eq_true, beq_iff_eq] at gate
      exact ⟨valid, ConversionClaim.constInstances leftReads rightReads gate.1 gate.2
        (fun u _ v _ => resources.tiers.sorts u v info1 info2 trivial trivial)⟩
  · rw [readScopedExpr?_var_none] at leftReads
    cases leftReads
  · rename_i id1 f1 v1 info1 id2 f2 v2 info2
    refine ConversionPost.ite (fun _ => ConversionPost.pureFalse valid) fun mismatch => ?_
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Classical.not_not] at mismatch
    obtain ⟨sameHead, sameField⟩ := mismatch
    subst sameField
    obtain ⟨ref, va, resolved, aEq, vaReads⟩ := readScopedExpr?_prj_annotated leftReads
    obtain ⟨ref', vb, resolved', bEq, vbReads⟩ := readScopedExpr?_prj_annotated rightReads
    have resolvedAt : resolve id2.addr = some ref := by rw [← sameHead]; exact resolved
    cases Option.some.inj (resolvedAt.symm.trans resolved')
    have rightReads' : readScopedExpr? resolve locals (.prj id1 f1 v2 info2) = some b.erase := by
      rw [bEq]
      simp [readScopedExpr?, resolved, vbReads, AExpr.erase]
    exact seams.projectionDelta id1 f1 v1 v2 info1 info2 locals context bounds before a b valid leftReads
      leftTyped rightReads' rightTyped
  · exact ConversionPost.pureFalse valid

/-- The application-spine comparison: equal spine sizes, the heads through
the recursive callback, then the argument loop. -/
theorem tryDefEqApp_sound {depth : Nat}
    (recursive : MethodContracts.{u,v} resolve anchor entries source catalog (methodsN depth))
    (seams : DefEqReducingSeams.{u,v} resolve anchor entries source catalog depth)
    (left right : KExpr .anon) :
    SoundConversion.{u,v} resolve anchor entries source catalog left right
      ((RecM.tryDefEqApp left right).run (methodsN depth)) := by
  intro locals context bounds before a b valid leftReads leftTyped rightReads rightTyped
  unfold RecM.tryDefEqApp
  try dsimp only
  refine ConversionPost.ite (fun _ => ConversionPost.pureFalse valid) fun _ => ?_
  rcases spineA : left.collectSpine with ⟨aHead, aArgs⟩
  rcases spineB : right.collectSpine with ⟨bHead, bArgs⟩
  try dsimp only
  refine ConversionPost.ite (fun _ => ConversionPost.pureFalse valid) fun sizes => ?_
  have sizes' : aArgs.size = bArgs.size := by simpa using sizes
  obtain ⟨aEq, bEq, aHeadReads, bHeadReads, aHeadTyped, bHeadTyped, lengths, readings⟩ :=
    spine_parts seams.appHereditary leftReads leftTyped rightReads rightTyped
      (by rw [spineA, spineB]; exact sizes')
  rw [spineA] at aHeadReads readings
  rw [spineB] at bHeadReads readings
  dsimp only at aHeadReads bHeadReads readings
  simp only [ReaderT.run_bind, isDefEqCall_run]
  have heads := recursive.isDefEq aHead bHead locals context bounds before _ _ valid aHeadReads aHeadTyped
    bHeadReads bHeadTyped
  cases runH : (methodsN depth).isDefEq aHead bHead before with
  | error err s₁ =>
      rw [EStateM.run_bind_error runH]
      rw [runH] at heads
      exact heads
  | ok answer s₁ =>
      rw [EStateM.run_bind_ok runH]
      rw [runH] at heads
      cases answer with
      | false =>
          simp only [Bool.not_false, ↓reduceIte]
          exact ConversionPost.pureFalse heads
      | true =>
          obtain ⟨valid₁, headClaim⟩ := heads
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          have spine := allDefEqSpineArgs_sound recursive.toDefEqContract (pairs := aArgs.zip bArgs)
            (by rw [Array.toList_zip]; exact readings) valid₁
          cases runS : (RecM.allDefEqSpineArgs (aArgs.zip bArgs)).run (methodsN depth) s₁ with
          | error err s₂ =>
              rw [runS] at spine
              exact spine
          | ok answer s₂ =>
              rw [runS] at spine
              cases answer with
              | false => exact spine
              | true =>
                  obtain ⟨valid₂, claims⟩ := spine
                  refine ⟨valid₂, ?_⟩
                  rw [aEq, bEq]
                  exact ConversionClaim.appN headClaim lengths claims

/-- After lazy delta stops: structural congruence, the second structural
pass, the address and quick checks, the spine comparison, and the final tier. -/
theorem isDefEqAfterLazyDeltaStopped_sound {depth : Nat}
    (recursive : MethodContracts.{u,v} resolve anchor entries source catalog (methodsN depth))
    (seams : DefEqReducingSeams.{u,v} resolve anchor entries source catalog depth)
    (annotations : SameRawAnnotations.{u,v} entries)
    (binders : DefEqBinderAssumptions.{u,v} resolve anchor entries)
    (resources : DefEqReducingResources.{u,v} resolve anchor entries source catalog)
    (left right : KExpr .anon) :
    SoundConversion.{u,v} resolve anchor entries source catalog left right
      ((RecM.isDefEqAfterLazyDeltaStopped left right).run (methodsN depth)) := by
  intro locals context bounds before a b valid leftReads leftTyped rightReads rightTyped
  unfold RecM.isDefEqAfterLazyDeltaStopped
  simp only [ReaderT.run_bind]
  have congruence := tryStructuralCongruence_sound seams resources left right locals context bounds before
    a b valid leftReads leftTyped rightReads rightTyped
  cases runC : (RecM.tryStructuralCongruence left right).run (methodsN depth) before with
  | error err s₁ =>
      rw [EStateM.run_bind_error runC]
      rw [runC] at congruence
      exact congruence
  | ok answer s₁ =>
      rw [EStateM.run_bind_ok runC]
      rw [runC] at congruence
      cases answer with
      | true =>
          simp only [↓reduceIte]
          exact ConversionPost.pureTrue congruence.1 congruence.2
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          simp only [ReaderT.run_bind]
          have reducedA := seams.whnfCore left locals context bounds s₁ a congruence leftReads leftTyped
          cases runA : (RecM.whnfCore left).run (methodsN depth) s₁ with
          | error err s₂ =>
              rw [EStateM.run_bind_error runA]
              rw [runA] at reducedA
              exact reducedA
          | ok ca s₂ =>
              rw [EStateM.run_bind_ok runA]
              rw [runA] at reducedA
              obtain ⟨valid₂, Ca, caReads, claimA, typesA⟩ := reducedA
              have caTyped : ∃ type, TypingClaim.{u,v} entries context Ca type :=
                leftTyped.imp fun _ => typesA _
              have reducedB := seams.whnfCore right locals context bounds s₂ b valid₂ rightReads rightTyped
              cases runB : (RecM.whnfCore right).run (methodsN depth) s₂ with
              | error err s₃ =>
                  rw [EStateM.run_bind_error runB]
                  rw [runB] at reducedB
                  exact reducedB
              | ok cb s₃ =>
                  rw [EStateM.run_bind_ok runB]
                  rw [runB] at reducedB
                  obtain ⟨valid₃, Cb, cbReads, claimB, typesB⟩ := reducedB
                  have cbTyped : ∃ type, TypingClaim.{u,v} entries context Cb type :=
                    rightTyped.imp fun _ => typesB _
                  have lift : ∀ {result : EStateM.Result (TcError .anon) (TcState .anon) Bool},
                      ConversionPost.{u,v} resolve anchor entries source catalog locals context bounds
                        Ca Cb result →
                      ConversionPost.{u,v} resolve anchor entries source catalog locals context bounds
                        a b result := by
                    intro result post
                    cases result with
                    | error err after => exact post
                    | ok answer after =>
                        cases answer with
                        | false => exact post
                        | true => exact ⟨post.1, claimA.trans (post.2.trans claimB.symm)⟩
                  try dsimp only
                  refine ConversionPost.ite (fun _ => ?_) fun _ => ?_
                  · simp only [isDefEqCall_run]
                    have conv := recursive.isDefEq ca cb locals context bounds s₃ Ca Cb valid₃ caReads
                      caTyped cbReads cbTyped
                    cases runD : (methodsN depth).isDefEq ca cb s₃ with
                    | error err s₄ =>
                        rw [runD] at conv
                        exact lift conv
                    | ok answer s₄ =>
                        rw [runD] at conv
                        exact lift conv
                  · refine ConversionPost.ite (fun same => ?_) fun _ => ?_
                    · exact ConversionPost.pureTrue valid₃ (claimA.trans ((ConversionClaim.ofAddrEq
                        (resources.tiers.faithful ca cb trivial trivial) annotations same caReads caTyped
                        cbReads cbTyped).trans claimB.symm))
                    · simp only [ReaderT.run_bind]
                      have quick := quickDefEq_sound recursive.toDefEqContract
                        (MethodsLocalState.methodsN depth) binders resources.tiers valid₃ trivial trivial
                        caReads caTyped cbReads cbTyped
                      cases runQ : (RecM.quickDefEq ca cb).run (methodsN depth) s₃ with
                      | error err s₄ =>
                          rw [EStateM.run_bind_error runQ]
                          rw [runQ] at quick
                          exact quick
                      | ok answer s₄ =>
                          rw [EStateM.run_bind_ok runQ]
                          rw [runQ] at quick
                          cases answer with
                          | true =>
                              simp only [↓reduceIte]
                              exact ConversionPost.pureTrue quick.1
                                (claimA.trans (quick.2.trans claimB.symm))
                          | false =>
                              simp only [Bool.false_eq_true, ↓reduceIte]
                              simp only [ReaderT.run_bind]
                              have app := tryDefEqApp_sound recursive seams ca cb locals context bounds s₄
                                Ca Cb quick caReads caTyped cbReads cbTyped
                              cases runP : (RecM.tryDefEqApp ca cb).run (methodsN depth) s₄ with
                              | error err s₅ =>
                                  rw [EStateM.run_bind_error runP]
                                  rw [runP] at app
                                  exact app
                              | ok answer s₅ =>
                                  rw [EStateM.run_bind_ok runP]
                                  rw [runP] at app
                                  cases answer with
                                  | true =>
                                      simp only [↓reduceIte]
                                      exact ConversionPost.pureTrue app.1
                                        (claimA.trans (app.2.trans claimB.symm))
                                  | false =>
                                      simp only [Bool.false_eq_true, ↓reduceIte]
                                      exact lift (isDefEqWhnf_sound recursive seams binders resources ca cb
                                        locals context bounds s₅ Ca Cb app caReads caTyped cbReads cbTyped)

end Stopped

end Ix.Kernel.Consistency
