/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certified

open Ix.Theory

/-! Structural and universe-validation regressions. These do not yet exercise
proof acceptance; that gate will add its own corpus when implemented. -/

namespace Tests.Theory.Certified

open Ix.Theory.Certified Ix.Theory.Model

#guard (PropWhen.ofList [2, 0, 2]).toRaw == some [0, 2]
#guard PropWhen.fromRaw? 2 (some [0, 1]) |>.isSome
#guard PropWhen.fromRaw? 2 (some [1, 0]) |>.isNone
#guard PropWhen.fromRaw? 1 (some [0, 0]) |>.isNone
#guard PropWhen.fromRaw? 1 (some [1]) |>.isNone
#guard validateZero? 1 (.param 0) (some [0]) |>.isSome
#guard validateZero? 1 (.param 0) none |>.isNone
#guard validateZero? 1 (.param 0) (some []) |>.isNone
#guard validateZero? 0 (.succ (.param 0)) none |>.isNone
#guard validateZero? 0 (.imax (.param 0) .zero) (some []) |>.isNone
#guard validateZero? 2 (.imax (.param 0) (.param 1)) (some [1]) |>.isSome
#guard (zeroCondition (.imax (.param 0) (.param 1))).holds ([5, 0].getD · 0)
#guard !(zeroCondition (.imax (.param 0) (.param 1))).holds ([0, 5].getD · 0)
#guard (instCondition [.succ .zero] (.param 0)).toRaw == none
#guard (instCondition [.zero] (.param 0)).toRaw == some []

-- Equal zero conditions do not imply equal universes.
example : zeroCondition (.succ .zero) = zeroCondition (.succ (.succ .zero)) := rfl
example : VLevel.eval [] (.succ .zero) ≠ VLevel.eval [] (.succ (.succ .zero)) := by decide

def identity : VExpr Nat := .lam (.sort (.param 0)) (.lam (.bvar 0) (.bvar 0))
def identityAnnotations : AnnotationTree :=
  .lam (some [0]) .leaf (.lam (some [0]) .leaf .leaf)

#guard readAnnotations? 1 0 identity identityAnnotations |>.isSome
#guard ((readAnnotations? 1 0 identity identityAnnotations).map (·.val.erase)) == some identity
#guard readAnnotations? 0 0 identity identityAnnotations |>.isNone
#guard readAnnotations? 1 0 identity .leaf |>.isNone
-- The same source node at two context depths is checked separately.
#guard readAnnotations? 0 1 (VExpr.bvar (β := Nat) 0) .leaf |>.isSome
#guard readAnnotations? 0 0 (VExpr.bvar (β := Nat) 0) .leaf |>.isNone

def primitives : PrimitiveSignature Nat := ⟨.member 10 0, .member 11 0, by decide, none⟩

def primitiveStore (falseDecl recDecl : Const Nat) : Store Nat where
  dom := [10, 11]
  nodup := by decide
  blocks b := if b = 10 then some ⟨[falseDecl]⟩ else if b = 11 then some ⟨[recDecl]⟩ else none
  mem_dom b := by
    by_cases h : b = 10 <;> by_cases h' : b = 11 <;> simp_all

#guard primitives.validate (primitiveStore PrimitiveSignature.falseDeclaration
  primitives.falseElimDeclaration)
#guard !primitives.validate (primitiveStore (.axiom 0 (.sort .zero) .safe)
  primitives.falseElimDeclaration)
#guard !primitives.validate (primitiveStore PrimitiveSignature.falseDeclaration
  (.recursor 0 0 0 1 0 primitives.falseElimType [] false .safe))
#guard !primitives.validate (primitiveStore PrimitiveSignature.falseDeclaration
  (.recursor 1 0 0 1 0 primitives.falseElimType [] true .safe))
#guard !primitives.validate (primitiveStore
  (.induct 0 0 0 (.sort .zero) [⟨0, 0, 0, primitives.falseExpr, .safe⟩] .safe)
  primitives.falseElimDeclaration)

#guard readDefinition? (Const.axiom 0 primitives.falseExpr .safe) .leaf .leaf |>.isNone
#guard readDefinition? (Const.axiom (β := Nat) 0 (.forallE (.sort .zero) (.bvar 0)) .safe)
  .leaf .leaf |>.isNone
#guard readDefinition? (Const.defn 0 .opaque primitives.falseExpr (.sort .zero) .unsafe)
  .leaf .leaf |>.isNone

end Tests.Theory.Certified
