/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certified.Checker

namespace Ix.Theory.Certified

open Model

universe u v
variable {β : Type u} [DecidableEq β]

structure InferenceWitness (β : Type u) where
  annotations : AnnotationTree
  type : AExpr β
  typing : TypingWitness β

structure InferenceResult (entries : Environment β) (n : Nat) (Γ : Context β)
    (source : VExpr β) where
  reading : Reading n Γ.length source
  type : AExpr β
  typeScope : type.Scope n Γ.length
  sound : TypingClaim.{u,v} entries Γ reading.val type

/-- Witness-directed inference. An unchecked type suggestion is accepted only
after the complete recursive typing validator establishes its meaning. -/
def inferCertified (fuel n : Nat) (entries : Environment β) (Γ : Context β)
    (source : VExpr β) (witness : InferenceWitness β) :
    Option (InferenceResult.{u,v} entries n Γ source) := do
  let reading ← readAnnotations? n Γ.length source witness.annotations
  if hs : witness.type.Scope n Γ.length then do
    let h ← verifyType.{u,v} fuel n entries Γ reading.val witness.type witness.typing
    return ⟨reading, witness.type, hs, h.down⟩
  else none

/-- The permitted head forms, including a stuck application spine. Definitions
with bodies must be unfolded; unsupported literals and projections fail. -/
def whnfShape (entries : Environment β) : AExpr β → Bool
  | .bvar _ | .sort _ | .lam .. | .forallE .. => true
  | .const r _ => (entries r).any (fun entry => entry.body.isNone)
  | .app (.lam ..) _ => false
  | .app f _ => whnfShape entries f
  | .natLit _ | .proj .. => false

structure WhnfWitness (β : Type u) where
  source : InferenceWitness β
  result : AExpr β
  resultTyping : TypingWitness β
  conversion : ConversionWitness β

structure WhnfResult (entries : Environment β) (n : Nat) (Γ : Context β)
    (source : VExpr β) where
  input : InferenceResult.{u,v} entries n Γ source
  result : AExpr β
  resultScope : result.Scope n Γ.length
  resultShape : whnfShape entries result = true
  resultTyping : TypingClaim.{u,v} entries Γ result input.type
  equal : ConversionClaim.{u,v} entries Γ input.reading.val result

/-- Conservative validation rechecks both endpoints and all conversion
premises, including every actual beta domain. It establishes hereditary
validity for its result and does not consume an unchecked inference invariant. -/
def whnfCertified (fuel n : Nat) (entries : Environment β) (Γ : Context β)
    (source : VExpr β) (witness : WhnfWitness β) :
    Option (WhnfResult.{u,v} entries n Γ source) := do
  let input ← inferCertified fuel n entries Γ source witness.source
  if hs : witness.result.Scope n Γ.length then
    if hw : whnfShape entries witness.result = true then do
      let ht ← verifyType.{u,v} fuel n entries Γ witness.result input.type witness.resultTyping
      let he ← verifyConversion.{u,v} fuel n entries Γ input.reading.val witness.result
        witness.conversion
      return ⟨input, witness.result, hs, hw, ht.down, he.down⟩
    else none
  else none

theorem inferCertified_sound {fuel n : Nat} {entries : Environment β}
    {Γ : Context β} {source : VExpr β} {witness : InferenceWitness β}
    {result : InferenceResult.{u,v} entries n Γ source}
    (_ : inferCertified fuel n entries Γ source witness = some result) :
    result.reading.val.erase = source ∧ result.type.Scope n Γ.length ∧
      TypingClaim.{u,v} entries Γ result.reading.val result.type :=
  ⟨result.reading.property.1, result.typeScope, result.sound⟩

theorem whnfCertified_sound {fuel n : Nat} {entries : Environment β}
    {Γ : Context β} {source : VExpr β} {witness : WhnfWitness β}
    {result : WhnfResult.{u,v} entries n Γ source}
    (_ : whnfCertified fuel n entries Γ source witness = some result)
    (V : Type v) [SetTheory V] (constants : Assignment β V)
    (hM : Realizes constants entries) (levels : List Nat) (env : Nat → V)
    (hΓ : Γ.Valid constants levels env) :
    result.input.reading.val.erase = source ∧ whnfShape entries result.result = true ∧
      WellDenoted constants levels env result.input.reading.val ∧
      WellDenoted constants levels env result.result ∧
      interp constants levels env result.input.reading.val =
        interp constants levels env result.result :=
  ⟨result.input.reading.property.1, result.resultShape,
    (result.input.sound V constants hM levels env hΓ).1,
    (result.resultTyping V constants hM levels env hΓ).1,
    result.equal V constants hM levels env hΓ⟩

end Ix.Theory.Certified
