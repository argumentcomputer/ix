/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Infer

/-! # Conversion of long application spines

Neutral applications compare their heads and arguments without re-entering
normalization for every partial application. The long-spine guard exercises a
fuel limit that the former prefix-by-prefix search exhausted. The arguments
are syntactically different but convert by universe commutativity.
-/

open Ix.Kernel Ix.Kernel.Model

namespace Tests.Ix.Kernel.ConversionSpines

def maxUV : VLevel := .max (.param 0) (.param 1)
def maxVU : VLevel := .max (.param 1) (.param 0)

def applied (n : Nat) (arg : AExpr Nat) : AExpr Nat :=
  (List.replicate n arg).foldl AExpr.app (.bvar 0)

def functionType (n : Nat) : AExpr Nat :=
  (List.range n).foldl (fun acc _ => .forallE .never (.sort (.succ maxUV)) acc)
    (.sort (.succ maxUV))

def converts (fuel n : Nat) (a b : AExpr Nat) : Bool :=
  (isDefEq.{0,1} fuel (fun _ => none) [functionType n] (applied n a) (applied n b)).isOk

-- These probes use actual well-typed open terms, not malformed spines.
#guard (inferA.{0,1} 1000 (fun _ => none) [functionType 4] (applied 4 (.sort maxUV))).isOk
#guard (inferA.{0,1} 1000 (fun _ => none) [functionType 4] (applied 4 (.sort maxVU))).isOk
#guard converts 160 128 (.sort maxUV) (.sort maxVU)
#guard !converts 16 128 (.sort maxUV) (.sort maxVU)
#guard !converts 160 8 (.sort maxUV) (.sort (.succ maxUV))

-- Arguments still receive full reduction and conversion.
def betaArg : AExpr Nat :=
  .app (.lam .never (.sort (.succ maxVU)) (.bvar 0)) (.sort maxVU)

#guard (inferA.{0,1} 1000 (fun _ => none) [] betaArg).isOk
#guard converts 160 8 (.sort maxUV) betaArg

-- A spine walk spends work even when all of its leaf comparisons are reflexive.
#guard match appCongrC.{0,1} 160 (fun _ => none) [functionType 8]
    (applied 8 (.sort maxUV)) (applied 8 (.sort maxUV)) (Cache.empty (fun _ => 0) 0) with
  | (.error .exhausted, _) => true
  | _ => false

-- Checking whether a head can unfold must respect both body availability and
-- the universe arity; the implementation agrees with deltaHead by theorem.
def deltaEnv : Environment Nat := fun
  | .member 0 0 => some ⟨1, .sort (.succ (.param 0)), some (.sort (.param 0)), [], []⟩
  | .member 1 0 => some ⟨1, .sort (.succ (.param 0)), none, [], []⟩
  | _ => none

#guard hasDeltaHead deltaEnv (.app (.const (.member 0 0) [.zero]) (.sort .zero))
#guard !hasDeltaHead deltaEnv (.const (.member 0 0) [])
#guard !hasDeltaHead deltaEnv (.const (.member 1 0) [.zero])
#guard !hasDeltaHead deltaEnv (.const (.member 2 0) [.zero])
#guard !hasDeltaHead deltaEnv (.app (.bvar 0) (.sort .zero))

def type0 : AExpr Nat := .sort (.succ .zero)
def prop : AExpr Nat := .sort .zero
def propToProp : AExpr Nat := .forallE .never prop prop
def propBeta : AExpr Nat := .app (.lam .never type0 (.bvar 0)) prop

/-- Delay an identity function's argument behind `n` lets. -/
def delayedIdentity : Nat → Nat → AExpr Nat
  | 0, depth => .bvar depth
  | n + 1, depth => .letE type0 prop (delayedIdentity n (depth + 1))

def functionEnv (body : AExpr Nat) : Environment Nat := fun
  | .member 0 0 => some ⟨0, .forallE .never type0 type0, some (.lam .never type0 body), [], []⟩
  | _ => none

def functionApp (arg : AExpr Nat) : AExpr Nat := .app (.const (.member 0 0) []) arg

-- Congruence succeeds before unfolding a long definition, even though its
-- arguments require reduction and cannot be compared by quickConv.
#guard (inferA.{0,1} 1000 (fun _ => none) [] (.lam .never type0 (delayedIdentity 64 0))).isOk
#guard (isDefEq.{0,1} 32 (functionEnv (delayedIdentity 64 0)) []
  (functionApp prop) (functionApp propBeta)).isOk

-- A failed argument comparison must not poison conversion of a function
-- that ignores the argument: full delta reduction still proves equality.
#guard !(isDefEq.{0,1} 64 (fun _ => none) [] prop propToProp).isOk
#guard (inferA.{0,1} 64 (functionEnv prop) [] (functionApp propToProp)).isOk
#guard (isDefEq.{0,1} 64 (functionEnv prop) []
  (functionApp prop) (functionApp propToProp)).isOk

-- A locally exhausted attempt restores the unused enclosing budget and
-- remains an exhausted result; a later fallback still has work available.
#guard match KM.speculate (entries := (fun _ => none : Environment Nat)) (Γ := []) 256
    (KM.tick.{0,1} >>= fun _ => KM.tick) (Cache.empty (fun _ => 0) 4) with
  | (.error .exhausted, cache) => cache.budget == 3
  | _ => false

/-- Compare the fast public step with its original recursive implementation,
including exact low-fuel failures. -/
def originalStepResult (fuel : Nat) (entries : Environment Nat) (e : AExpr Nat) :
    Search (AExpr Nat) :=
  (KM.run (fun _ => 0) (fuel * workPerFuel) (stepC.{0,1} fuel entries [] e)).map (·.result)

def stepAgrees (entries : Environment Nat) (e : AExpr Nat) : Bool :=
  (List.range 16).all fun fuel =>
    match (step.{0,1} fuel entries [] e).map (·.result), originalStepResult fuel entries e with
    | .ok a, .ok b => decide (a = b)
    | .error a, .error b => decide (a = b)
    | _, _ => false

def neutralHeads : List (AExpr Nat) := [
  .bvar 0, prop, .forallE .never type0 type0, .natLit (.member 3 0) 0,
  .const (.member 0 0) [], .const (.member 1 0) [.zero], .const (.member 2 0) []]

-- Missing constants and wrong universe arities remain reduction failures;
-- only the existing type checker decides whether those inputs are malformed.
#guard neutralHeads.all fun head => stepAgrees deltaEnv (AExpr.appN head (List.replicate 8 prop))
#guard match step.{0,1} 8 deltaEnv [] (applied 8 prop) with
  | .error .exhausted => true
  | _ => false
#guard match step.{0,1} 9 deltaEnv [] (applied 8 prop) with
  | .error .noMatch => true
  | _ => false

-- Active heads retain their old beta, zeta, delta and projection paths.
def identity : AExpr Nat := .lam .never type0 (.bvar 0)
def letHead : AExpr Nat := .letE type0 prop identity
#guard stepAgrees (fun _ => none) (.app identity prop)
#guard stepAgrees (fun _ => none) (.app letHead prop)
#guard stepAgrees (functionEnv (.bvar 0)) (functionApp prop)
#guard stepAgrees (fun _ => none) (.app (.proj (.member 0 0) 0 (.bvar 0)) prop)
#guard (whnf.{0,1} 64 (fun _ => none) [] (.app letHead prop)).result = prop
#guard (whnf.{0,1} 64 (functionEnv (.bvar 0)) [] (functionApp prop)).result = prop

def factsEnv (facts : List (ConstantFact Nat)) : Environment Nat := fun _ =>
  some ⟨0, type0, none, [], facts⟩

def reductionFacts : List (ConstantFact Nat) := [
  .natOp .add, .natTest .beq (.member 1 0) (.member 2 0), .recursor 0 1 0 [],
  .quotientLift (.member 1 0) (.member 2 0), .quotient .ind]

-- Any potentially active rule keeps the full strategy, regardless of where
-- its fact occurs. Former/constructor and typed facts alone remain neutral.
#guard reductionFacts.all fun fact =>
  (neutralSpineDepth (factsEnv [.typed prop type0, fact]) (functionApp prop) 0).isNone
#guard neutralSpineDepth (factsEnv [
    .natural (.member 1 0) (.member 2 0), .«structure» 0 0,
    .typed prop type0, .quotient .type, .quotient .ctor]) (functionApp prop) 0 = some 1

-- A native literal operation is not mistaken for an inert constant even
-- when it has no delta body.
def addApp : AExpr Nat :=
  .app (.app (.const (.member 0 0) []) (.natLit (.member 3 0) 20)) (.natLit (.member 3 0) 22)
#guard stepAgrees (factsEnv [.natOp .add]) addApp
#guard (whnf.{0,1} 64 (factsEnv [.natOp .add]) [] addApp).result = .natLit (.member 3 0) 42

end Tests.Ix.Kernel.ConversionSpines
