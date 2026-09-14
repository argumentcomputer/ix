/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Certified.ClaimMeaning

namespace Ix.Certified

def Selected {α : Type _} (expected : Option α) (actual : α) : Prop :=
  match expected with
  | none => True
  | some value => value = actual

instance {α : Type _} [DecidableEq α] (expected : Option α) (actual : α) :
    Decidable (Selected expected actual) := by
  unfold Selected
  split <;> infer_instance

/-- The structural reveal protocol commits to the exact serialized raw
expression, including its original table indices and sharing references. -/
def expressionAddress (expression : Ixon.Expr) : Address :=
  Address.blake3 (Ixon.runPut (Ixon.putExpr expression))

def ConstructorMatches (expected : Ix.RevealConstructorInfo) (actual : Ixon.Constructor) : Prop :=
  Selected expected.isUnsafe actual.isUnsafe ∧ Selected expected.lvls actual.lvls ∧
    Selected expected.cidx actual.cidx ∧ Selected expected.params actual.params ∧
    Selected expected.fields actual.fields ∧ Selected expected.typ (expressionAddress actual.typ)

instance (expected : Ix.RevealConstructorInfo) (actual : Ixon.Constructor) :
    Decidable (ConstructorMatches expected actual) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

def ConstructorsMatch (expected : Option (Array (UInt64 × Ix.RevealConstructorInfo)))
    (actual : Array Ixon.Constructor) : Prop :=
  match expected with
  | none => True
  | some constructors => ∀ pair ∈ constructors.toList,
    match actual[pair.1.toNat]? with
    | none => False
    | some constructor => ConstructorMatches pair.2 constructor

instance (expected : Option (Array (UInt64 × Ix.RevealConstructorInfo))) (actual : Array Ixon.Constructor) :
    Decidable (ConstructorsMatch expected actual) := by
  unfold ConstructorsMatch
  split
  · infer_instance
  · apply @List.decidableBAll _ _ (fun pair => by split <;> infer_instance)

def RulesMatch (expected : Option (Array Ix.RevealRecursorRule)) (actual : Array Ixon.RecursorRule) : Prop :=
  match expected with
  | none => True
  | some rules => ∀ rule ∈ rules.toList,
    match actual[rule.ruleIdx.toNat]? with
    | none => False
    | some actual => rule.fields = actual.fields ∧ rule.rhs = expressionAddress actual.rhs

instance (expected : Option (Array Ix.RevealRecursorRule)) (actual : Array Ixon.RecursorRule) :
    Decidable (RulesMatch expected actual) := by
  unfold RulesMatch
  split
  · infer_instance
  · apply @List.decidableBAll _ _ (fun rule => by split <;> infer_instance)

def MutMatches (expected : Ix.RevealMutConstInfo) (actual : Ixon.MutConst) : Prop :=
  match expected, actual with
  | .defn kind safety levels type value, .defn actual =>
    Selected kind actual.kind ∧ Selected safety actual.safety ∧ Selected levels actual.lvls ∧
      Selected type (expressionAddress actual.typ) ∧ Selected value (expressionAddress actual.value)
  | .indc safety levels params indices type ctors, .indc actual =>
    Selected safety actual.isUnsafe ∧ Selected levels actual.lvls ∧ Selected params actual.params ∧
      Selected indices actual.indices ∧ Selected type (expressionAddress actual.typ) ∧ ConstructorsMatch ctors actual.ctors
  | .recr k safety levels params indices motives minors type rules, .recr actual =>
    Selected k actual.k ∧ Selected safety actual.isUnsafe ∧ Selected levels actual.lvls ∧
      Selected params actual.params ∧ Selected indices actual.indices ∧ Selected motives actual.motives ∧
      Selected minors actual.minors ∧ Selected type (expressionAddress actual.typ) ∧ RulesMatch rules actual.rules
  | _, _ => False

instance (expected : Ix.RevealMutConstInfo) (actual : Ixon.MutConst) : Decidable (MutMatches expected actual) := by
  unfold MutMatches
  cases expected <;> cases actual <;> infer_instance

def ComponentsMatch (expected : Array (UInt64 × Ix.RevealMutConstInfo)) (actual : Array Ixon.MutConst) : Prop :=
  ∀ pair ∈ expected.toList, match actual[pair.1.toNat]? with
    | none => False
    | some member => MutMatches pair.2 member

instance (expected : Array (UInt64 × Ix.RevealMutConstInfo)) (actual : Array Ixon.MutConst) :
    Decidable (ComponentsMatch expected actual) := by
  unfold ComponentsMatch
  apply @List.decidableBAll _ _ (fun pair => by split <;> infer_instance)

def RevealMatches (expected : Ix.RevealConstantInfo) (actual : Ixon.ConstantInfo) : Prop :=
  match expected, actual with
  | .defn kind safety levels type value, .defn actual =>
    Selected kind actual.kind ∧ Selected safety actual.safety ∧ Selected levels actual.lvls ∧
      Selected type (expressionAddress actual.typ) ∧ Selected value (expressionAddress actual.value)
  | .recr k safety levels params indices motives minors type rules, .recr actual =>
    Selected k actual.k ∧ Selected safety actual.isUnsafe ∧ Selected levels actual.lvls ∧
      Selected params actual.params ∧ Selected indices actual.indices ∧ Selected motives actual.motives ∧
      Selected minors actual.minors ∧ Selected type (expressionAddress actual.typ) ∧ RulesMatch rules actual.rules
  | .axio safety levels type, .axio actual =>
    Selected safety actual.isUnsafe ∧ Selected levels actual.lvls ∧ Selected type (expressionAddress actual.typ)
  | .quot kind levels type, .quot actual =>
    Selected kind actual.kind ∧ Selected levels actual.lvls ∧ Selected type (expressionAddress actual.typ)
  | .cPrj index constructor block, .cPrj actual =>
    Selected index actual.idx ∧ Selected constructor actual.cidx ∧ Selected block actual.block
  | .iPrj index block, .iPrj actual | .rPrj index block, .rPrj actual | .dPrj index block, .dPrj actual =>
    Selected index actual.idx ∧ Selected block actual.block
  | .muts components, .muts actual => ComponentsMatch components actual
  | _, _ => False

instance (expected : Ix.RevealConstantInfo) (actual : Ixon.ConstantInfo) : Decidable (RevealMatches expected actual) := by
  unfold RevealMatches
  cases expected <;> cases actual <;> infer_instance

structure RevealWitness where
  opening : Ixon.Comm

structure RevealReceipt (source : Ixon.Env) (commitment : Address) (info : Ix.RevealConstantInfo)
    (witness : RevealWitness) where
  secretSize : witness.opening.secret.hash.size = 32
  payloadSize : witness.opening.payload.hash.size = 32
  bound : witness.opening.commit = commitment
  object : SourceObject source
  payload : object.address = witness.opening.payload
  fields : RevealMatches info object.decoded.val.info

def checkReveal? (source : Ixon.Env) (commitment : Address) (info : Ix.RevealConstantInfo)
    (witness : RevealWitness) : Read source (RevealReceipt source commitment info witness) :=
  if hs : witness.opening.secret.hash.size = 32 then
    if hp : witness.opening.payload.hash.size = 32 then
      if hb : witness.opening.commit = commitment then do
        let object ← readObject? source witness.opening.payload
        if ha : object.address = witness.opening.payload then
          if hf : RevealMatches info object.decoded.val.info then
            return ⟨hs, hp, hb, object, ha, hf⟩
          else failure
        else failure
      else failure
    else failure
  else failure

def RevealMeaning (source : Ixon.Env) (commitment : Address) (info : Ix.RevealConstantInfo) : Prop :=
  ∃ opening : Ixon.Comm, opening.secret.hash.size = 32 ∧ opening.payload.hash.size = 32 ∧
    opening.commit = commitment ∧ ∃ bytes object, ObjectBytes source opening.payload bytes object ∧
      RevealMatches info object.info

theorem RevealReceipt.meaning (receipt : RevealReceipt source commitment info witness) :
    RevealMeaning source commitment info := by
  refine ⟨witness.opening, receipt.secretSize, receipt.payloadSize, receipt.bound,
    receipt.object.bytes, receipt.object.decoded.val, ?_, receipt.fields⟩
  rw [← receipt.payload]
  exact ⟨receipt.object.fromSource, receipt.object.decoded.property⟩

end Ix.Certified
