/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certificate.Suggest
import Ix.Theory.Certified.Standard.Checked

namespace Ix.Theory.Certificate.Standard

open Model Certified Certified.Standard Certified.Basis

universe u
variable {β : Type u} [DecidableEq β]
variable [Hints β]

def recursorFor? (store : Store β) (n : Nat) (type : AExpr β) : Option (ConstRef β) :=
  (store.dom.find? fun source => match store.blocks source with
    | some ⟨[.recursor m _ _ _ _ raw _ _ .safe]⟩ => m == n && raw == type.erase
    | _ => false).map (.member · 0)

/-- Recover only known standard schemas, then require exact source erasure.
All prerequisite interfaces are checked again by standard admission. -/
def spec? (store : Store β) (type : VExpr β) : Option (Spec β) := do
  let spec ← match type with
    | .forallE (.sort .zero) (.forallE (.sort .zero) (.forallE premise result)) => do
      let .const iff [] := premise.appHead | none
      let .const eq [.succ .zero] := result.appHead | none
      let .member isource 0 := iff | none
      let .member esource 0 := eq | none
      let ei := ConstRef.ctor esource 0 0
      let ii := ConstRef.ctor isource 0 0
      let er ← recursorFor? store 2 (Equality.recType eq ei)
      let ir ← recursorFor? store 1 (Iff.recType iff ii)
      return Spec.propext eq ei er iff ii ir
    | .forallE (.sort (.param 0)) (.forallE premise (.bvar 1)) => do
      let .const ne [.param 0] := premise.appHead | none
      let .member source 0 := ne | none
      let ctor := ConstRef.ctor source 0 0
      let recursor ← recursorFor? store 1 (Nonempty.recType ne ctor)
      return Spec.choice ne ctor recursor
    | _ => none
  if spec.type.erase = type then some spec else none

def witness? (fuel : Nat) (store : Store β) (entries : Environment β)
    (ref : ConstRef β) (source : Const β) : Option (Witness β) := do
  let .axiom _ type .safe := source | none
  let spec ← spec? store type
  if spec.source != source then none else do
    let inferred ← inferAnnotated? fuel spec.universes entries [] spec.type
    let .sort level := inferred.type | none
    return ⟨ref, spec, level, inferred.witness⟩

end Ix.Theory.Certificate.Standard
