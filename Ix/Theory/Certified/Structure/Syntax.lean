/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certified.Ordinary.Checked
import Ix.Theory.Model.TelescopeSemantics

namespace Ix.Theory.Certified.Structure

open Model

universe u v
variable {β : Type u}

structure Field (β : Type u) where
  domain : AExpr β
  level : VLevel
deriving DecidableEq

/-- A single nonrecursive constructor with dependent fields. The additional
field sorts license projections out of a proof-valued structure. -/
structure Description (β : Type u) where
  universes : Nat
  parameters : List (AExpr β)
  fields : List (Field β)
  level : VLevel
deriving DecidableEq

def Description.constructor (d : Description β) : Ordinary.Constructor β :=
  ⟨d.fields.map Field.domain, [], []⟩

def Description.ordinary (d : Description β) : Ordinary.Shape β :=
  ⟨d.universes, d.parameters, [], d.level, [d.constructor]⟩

def projections (source : β) (count : Nat) : List (AExpr β) :=
  (List.range count).map fun i => .proj (.member source 0) i (.bvar 0)

/-- Insert the major premise below preceding fields, then substitute their
actual projections in outermost-first order. -/
def fieldResult (source : β) (index : Nat) (field : Field β) : AExpr β :=
  (field.domain.liftN 1 index).instRev (projections source index)

def Description.projectionDomains (d : Description β) (source : β) : List (AExpr β) :=
  d.parameters ++ [d.ordinary.familyApp source 0 []]

def Description.projection (d : Description β) (source : β) (i : Nat) (field : Field β) : AExpr β :=
  .lamN (zeroCondition field.level) (d.projectionDomains source) (.proj (.member source 0) i (.bvar 0))

def Description.projectionType (d : Description β) (source : β) (i : Nat) (field : Field β) : AExpr β :=
  .forallN (zeroCondition field.level) (d.projectionDomains source) (fieldResult source i field)

def Description.facts (d : Description β) (source : β) : List (ConstantFact β) :=
  d.fields.zipIdx.map fun (field, i) => .typed (d.projection source i field) (d.projectionType source i field)

def Description.etaLhs (d : Description β) (source : β) : AExpr β :=
  .lamN (zeroCondition d.level) (d.projectionDomains source)
    (.appN (.const (.ctor source 0 0) (VLevel.params d.universes))
      (Ordinary.parameterVars 1 d.parameters.length ++ projections source d.fields.length))

def Description.etaRhs (d : Description β) (source : β) : AExpr β :=
  .lamN (zeroCondition d.level) (d.projectionDomains source) (.bvar 0)

def Description.iotaLhs (d : Description β) (source : β) (i : Nat) (field : Field β) : AExpr β :=
  .lamN (zeroCondition field.level) (d.parameters ++ d.constructor.fields)
    (.proj (.member source 0) i (.appN (.const (.ctor source 0 0) (VLevel.params d.universes))
      (Ordinary.parameterVars 0 (d.parameters.length + d.fields.length))))

def Description.iotaRhs (d : Description β) (i : Nat) (field : Field β) : AExpr β :=
  .lamN (zeroCondition field.level) (d.parameters ++ d.constructor.fields)
    (.bvar (d.fields.length - 1 - i))

def Description.equations (d : Description β) (source : β) : List (ConstantEquation β) :=
  ⟨d.etaLhs source, d.etaRhs source⟩ :: d.fields.zipIdx.map fun (field, i) =>
    ⟨d.iotaLhs source i field, d.iotaRhs i field⟩

inductive FieldsFormed (entries : Environment β) (w : VLevel) : Context β → List (Field β) → Prop
  | nil {Γ} : FieldsFormed entries w Γ []
  | cons {Γ field rest}
      (domain : TypingClaim.{u,v} entries Γ field.domain (.sort field.level))
      (proofField : ∀ levels, w.eval levels = 0 → field.level.eval levels = 0)
      (tail : FieldsFormed entries w (Γ.push field.domain) rest) :
      FieldsFormed entries w Γ (field :: rest)

theorem FieldsFormed.formed {entries : Environment β} {w : VLevel} {Γ : Context β}
    {fields : List (Field β)} (h : FieldsFormed.{u,v} entries w Γ fields) :
    Telescope.Formed.{u,v} entries Γ (fields.map Field.domain) := by
  induction h with
  | nil => exact .nil
  | cons hA _ _ ih => exact .cons _ hA ih

theorem FieldsFormed.prop {entries : Environment β} {w : VLevel} {Γ : Context β}
    {fields : List (Field β)} (h : FieldsFormed.{u,v} entries w Γ fields) :
    TelescopeProp.{u,v} entries Γ (fields.map Field.domain) w := by
  induction h with
  | nil => exact TelescopeProp.nil entries _ w
  | cons hA hz _ ih => exact TelescopeProp.cons hA hz ih

def checkFields [DecidableEq β] (fuel n : Nat) (entries : Environment β) (w : VLevel) :
    (Γ : Context β) → (fields : List (Field β)) → List (TypingWitness β) →
      Option (CheckedClaim.{u} (FieldsFormed.{u,v} entries w Γ fields))
  | _, [], [] => some ⟨.nil⟩
  | Γ, field :: fields, witness :: witnesses =>
    if hz : checkZeroImplies w field.level = true then do
      let hA ← verifyType.{u,v} fuel n entries Γ field.domain (.sort field.level) witness
      let rest ← checkFields fuel n entries w (Γ.push field.domain) fields witnesses
      return ⟨.cons hA.down (checkZeroImplies_sound hz) rest.down⟩
    else none
  | _, _, _ => none

end Ix.Theory.Certified.Structure
