/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certified.Basis.Equality
import Ix.Theory.Quot

namespace Ix.Theory.Certified.Quotient

open Model

universe u
variable {β : Type u}

/-- The five quotient declarations are realized together. References may be
members of different authenticated blocks. Equality must already be admitted. -/
structure Refs (β : Type u) extends Store.QuotRefs β where
  eqRefl : ConstRef β
  eqRec : ConstRef β
  sound : ConstRef β
  deriving DecidableEq

inductive Kind where
  | type | ctor | lift | ind | sound
  deriving DecidableEq

def kinds : List Kind := [.type, .ctor, .lift, .ind, .sound]

def Refs.ref (refs : Refs β) : Kind → ConstRef β
  | .type => refs.type
  | .ctor => refs.ctor
  | .lift => refs.lift
  | .ind => refs.ind
  | .sound => refs.sound

def Kind.universes : Kind → Nat
  | .lift => 2
  | _ => 1

def relationType : AExpr β :=
  .forallE .never (.bvar 0) (.forallE .never (.bvar 1) (.sort .zero))

def applied (refs : Refs β) (l : VLevel) (A R : AExpr β) : AExpr β :=
  .appN (.const refs.type [l]) [A, R]

def constructed (refs : Refs β) (l : VLevel) (A R a : AExpr β) : AExpr β :=
  .appN (.const refs.ctor [l]) [A, R, a]

def typeType : AExpr β :=
  .forallE .never (.sort (.param 0)) (.forallE .never relationType (.sort (.param 0)))

def ctorType (refs : Refs β) : AExpr β :=
  .forallE (.param 0) (.sort (.param 0)) <|
  .forallE (.param 0) relationType <|
  .forallE (.param 0) (.bvar 1) <|
    applied refs (.param 0) (.bvar 2) (.bvar 1)

/-- In the context `A, R, B, f`, invariance of `f` under `R`. -/
def invariantType (refs : Refs β) : AExpr β :=
  .forallE .always (.bvar 3) <|
  .forallE .always (.bvar 4) <|
  .forallE .always (.appN (.bvar 4) [.bvar 1, .bvar 0]) <|
    Basis.Equality.applied refs.eq (.param 1) (.bvar 4)
      (.app (.bvar 3) (.bvar 2)) (.app (.bvar 3) (.bvar 1))

def liftPrefix (refs : Refs β) : List (AExpr β) :=
  [.sort (.param 0), relationType, .sort (.param 1),
    .forallE (.param 1) (.bvar 2) (.bvar 1), invariantType refs]

def liftType (refs : Refs β) : AExpr β :=
  .forallN (.param 1) (liftPrefix refs) <|
    .forallE (.param 1) (applied refs (.param 0) (.bvar 4) (.bvar 3)) (.bvar 3)

def indPrefix (refs : Refs β) : List (AExpr β) :=
  [.sort (.param 0), relationType,
    .forallE .never (applied refs (.param 0) (.bvar 1) (.bvar 0)) (.sort .zero),
    .forallE .always (.bvar 2)
      (.app (.bvar 1) (constructed refs (.param 0) (.bvar 3) (.bvar 2) (.bvar 0)))]

def indType (refs : Refs β) : AExpr β :=
  .forallN .always (indPrefix refs) <|
    .forallE .always (applied refs (.param 0) (.bvar 3) (.bvar 2)) (.app (.bvar 2) (.bvar 0))

def soundType (refs : Refs β) : AExpr β :=
  .forallE .always (.sort (.param 0)) <|
  .forallE .always relationType <|
  .forallE .always (.bvar 1) <|
  .forallE .always (.bvar 2) <|
  .forallE .always (.appN (.bvar 2) [.bvar 1, .bvar 0]) <|
    Basis.Equality.applied refs.eq (.param 0)
      (applied refs (.param 0) (.bvar 4) (.bvar 3))
      (constructed refs (.param 0) (.bvar 4) (.bvar 3) (.bvar 2))
      (constructed refs (.param 0) (.bvar 4) (.bvar 3) (.bvar 1))

def Refs.entryType (refs : Refs β) : Kind → AExpr β
  | .type => typeType
  | .ctor => ctorType refs
  | .lift => liftType refs
  | .ind => indType refs
  | .sound => soundType refs

def Refs.source (refs : Refs β) : Kind → Const β
  | .type => .quot .type 1 typeType.erase
  | .ctor => .quot .ctor 1 (ctorType refs).erase
  | .lift => .quot .lift 2 (liftType refs).erase
  | .ind => .quot .ind 1 (indType refs).erase
  | .sound => .axiom 1 (soundType refs).erase .safe

def liftRuleBinders (refs : Refs β) : List (AExpr β) := liftPrefix refs ++ [.bvar 4]
def liftRuleType (refs : Refs β) : AExpr β := .forallN (.param 1) (liftRuleBinders refs) (.bvar 3)
def liftRuleLhs (refs : Refs β) : AExpr β :=
  .lamN (.param 1) (liftRuleBinders refs) <|
    .appN (.const refs.lift [.param 0, .param 1])
      [.bvar 5, .bvar 4, .bvar 3, .bvar 2, .bvar 1,
        constructed refs (.param 0) (.bvar 5) (.bvar 4) (.bvar 0)]
def liftRuleRhs (refs : Refs β) : AExpr β :=
  .lamN (.param 1) (liftRuleBinders refs) (.app (.bvar 2) (.bvar 0))

def indRuleBinders (refs : Refs β) : List (AExpr β) := indPrefix refs ++ [.bvar 3]
def indRuleType (refs : Refs β) : AExpr β :=
  .forallN .always (indRuleBinders refs) <|
    .app (.bvar 2) (constructed refs (.param 0) (.bvar 4) (.bvar 3) (.bvar 0))
def indRuleLhs (refs : Refs β) : AExpr β :=
  .lamN .always (indRuleBinders refs) <|
    .appN (.const refs.ind [.param 0]) [.bvar 4, .bvar 3, .bvar 2, .bvar 1,
      constructed refs (.param 0) (.bvar 4) (.bvar 3) (.bvar 0)]
def indRuleRhs (refs : Refs β) : AExpr β :=
  .lamN .always (indRuleBinders refs) (.app (.bvar 1) (.bvar 0))

def Refs.equations (refs : Refs β) : Kind → List (ConstantEquation β)
  | .lift => [⟨liftRuleLhs refs, liftRuleRhs refs⟩]
  | .ind => [⟨indRuleLhs refs, indRuleRhs refs⟩]
  | _ => []

def Refs.entry (refs : Refs β) (kind : Kind) : ConstantEntry β :=
  ⟨kind.universes, refs.entryType kind, none, refs.equations kind, []⟩

theorem typeType_erase : (typeType : AExpr β).erase = Store.Quotient.typeType := rfl
theorem ctorType_erase (refs : Refs β) : (ctorType refs).erase = Store.Quotient.ctorType refs.toQuotRefs := rfl
theorem liftType_erase (refs : Refs β) : (liftType refs).erase = Store.Quotient.liftType refs.toQuotRefs := rfl
theorem indType_erase (refs : Refs β) : (indType refs).erase = Store.Quotient.indType refs.toQuotRefs := rfl

end Ix.Theory.Certified.Quotient
