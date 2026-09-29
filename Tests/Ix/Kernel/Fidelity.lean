/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Tests.Ix.Kernel.Fixtures
import Tests.Ix.Kernel.Inductives
import Tests.Ix.Kernel.Structures
import Tests.Ix.Kernel.Literals
import Tests.Ix.Kernel.Quotients
import Tests.Ix.Kernel.Axioms

/-! # Exact input fidelity through all admission routes

Inspect the returned environment through its public lookup view. This
catches changed source types, bodies, universe counts, and member or
constructor positions independently of whether checking still succeeds.
-/

open Ix.Kernel Ix.Kernel.Model
namespace Tests.Ix.Kernel.Fidelity

def readsMember (env : Env String) (source : String) (index : Nat) (c : Const String) : Bool :=
  match env.toEnvironment (.member source index) with
  | none => false
  | some entry =>
    decide (entry.universes = c.uvars ∧ entry.type.erase = c.type) &&
      (match c with
       | .defn _ _ _ body _ => decide (entry.body.map AExpr.erase = some body)
       | _ => entry.body.isNone) &&
      (match c with
       | .induct _ _ _ _ ctors _ => ctors.zipIdx.all fun (ctor, j) =>
           match env.toEnvironment (.ctor source index j) with
           | none => false
           | some ce => decide (ce.universes = ctor.uvars ∧ ce.type.erase = ctor.type) && ce.body.isNone
       | _ => true)

def faithful (decls : List (Decl String)) : Bool :=
  match check.{0,1} {} decls with
  | .error _ => false
  | .ok env => decls.all fun d =>
      d.block.members.zipIdx.all fun (c, i) => readsMember env d.address i c

#guard faithful Fixtures.accepted
#guard faithful (Inductives.accepted ++ [Inductives.oneDecl, Inductives.nilNat, Inductives.reflOne])
#guard faithful (Structures.accepted ++ [Structures.fstDecl, Structures.propertyDecl])
#guard faithful [Literals.natDecl, Literals.three]
#guard faithful (Quotients.primitives ++ [Quotients.liftMk])
#guard faithful [Axioms.eqDecl, Axioms.iffDecl, Axioms.propextDecl]
#guard faithful [Axioms.nonemptyDecl, Axioms.choiceDecl, Axioms.pick]

/-- Raw scope alone does not check binder-condition universe indices. -/
def badCondition : AExpr Nat :=
  .lam (.param 17) (.sort (.succ .zero)) (.bvar 0)
example : badCondition.erase.LevelWF 0 ∧ badCondition.erase.ClosedN 0 := by
  simp [badCondition, AExpr.erase, VExpr.LevelWF, VExpr.ClosedN, VLevel.WF]
#guard !decide (badCondition.Scope 0 0)

-- The public contracts compose without assuming anything about a model.
example {cfg : Config} {before after : Env Nat} {decls : List (Decl Nat)}
    (accepted : checkDecls.{0,1} cfg before decls = .ok after)
    {r : ConstRef Nat} {entry : ConstantEntry Nat} (old : before.toEnvironment r = some entry) :
    after.toEnvironment r = some entry := checkDecls_preserves accepted r entry old

example {cfg : Config} {after : Env Nat} {decls : List (Decl Nat)}
    (accepted : check.{0,1} cfg decls = .ok after) {d : Decl Nat} (member : d ∈ decls) :
    d.block.Installed d.address after.toEnvironment := check_installed accepted d member

end Tests.Ix.Kernel.Fidelity
