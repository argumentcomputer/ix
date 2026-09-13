/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.LookupCoordinates

/-! Checked degree-two logUp evaluation. Every external node and coordinate
read is optional. Group zero has the native normalization to one; groups above
eight are rejected. The returned list retains both coordinates in native order.
Prefix and suffix scans include multiplication by one at their endpoints;
ring reflection relates these to the native seeded scans. -/

namespace Aiur.NativeAIR.LogUp

def product [OfNat R 1] [Mul R] (values : List R) : R := values.foldr (· * ·) 1
def sum [OfNat R 0] [Add R] (values : List R) : R := values.foldr (· + ·) 0

/-- Denominator-cleared weighted numerator, defined without division. -/
def numerator [OfNat R 0] [OfNat R 1] [Add R] [Mul R] : List (R × R) → R
  | [] => 0
  | (weight, message) :: rest =>
    weight * product (rest.map Prod.snd) + message * numerator rest

def prefixSuffixTerms [OfNat R 1] [Mul R] (initial : R) (entries : List (R × R)) : List R :=
  let messages := entries.map Prod.snd
  let prefixes := messages.scanl (· * ·) initial
  let suffixes := (messages.scanr (· * ·) 1).tail
  (entries.zip (prefixes.zip suffixes)).map fun (entry, before, after) => before * after * entry.1

def groupEquation [OfNat R 0] [OfNat R 1] [Add R] [Sub R] [Mul R]
    (entries : List (R × R)) (difference : R) : R :=
  match entries with
  | [] => difference
  | [(weight, message)] => message * difference - weight
  | _ => (entries.map Prod.snd).foldl (· * ·) 1 * difference -
      (prefixSuffixTerms 1 entries).foldl (· + ·) 0

section Evaluation

variable {W : Type u} [OfNat W 0] [OfNat W 1] [OfNat W 7] [Add W] [Sub W] [Mul W]

def fingerprint (gamma : Coordinates W) (args : List W) : Coordinates W :=
  args.foldr (fun arg acc => acc * gamma + Coordinates.ofBase arg) 0

def compress (beta gamma : Coordinates W) (lookups : List (W × List W)) :
    List (Coordinates W × Coordinates W) :=
  lookups.map fun (multiplicity, args) =>
    (Coordinates.ofBase multiplicity, fingerprint gamma args + beta)

def groupCount (groupSize lookupCount : Nat) : Nat :=
  max 1 ((lookupCount + max groupSize 1 - 1) / max groupSize 1)

def chunk (groupSize index : Nat) (lookups : List α) : List α :=
  (lookups.drop (index * max groupSize 1)).take (max groupSize 1)

def step (beta gamma injection next : Coordinates W) (stageCurrent : Array W)
    (lookups : List (W × List W)) (groupSize index : Nat) : Option (Coordinates W) := do
  let source ← Coordinates.read stageCurrent index
  let target ← if index + 1 < groupCount groupSize lookups.length then Coordinates.read stageCurrent (index + 1)
    else some (next + injection)
  return groupEquation (compress beta gamma (chunk groupSize index lookups)) (target - source)

def equations (lookups : List (W × List W)) (stageCurrent stageNext publics deltaScaled : Array W)
    (isLast : W) (groupSize : Nat) : Option (List (Coordinates W)) := do
  if 8 < groupSize then none else do
    let beta ← Coordinates.read publics 0
    let gamma ← Coordinates.read publics 1
    let delta ← Coordinates.read deltaScaled 0
    let injection := delta.scale isLast
    let next ← Coordinates.read stageNext 0
    let groups := groupCount groupSize lookups.length
    (List.range groups).mapM (step beta gamma injection next stageCurrent lookups groupSize)

def constraintValues (lookups : List Lookup) (nodeValues stageCurrent stageNext publics deltaScaled : Array W)
    (isLast : W) (groupSize : Nat) : Option (List W) := do
  let values ← lookups.mapM (readLookup nodeValues)
  return Coordinates.flatten (← equations values stageCurrent stageNext publics deltaScaled isLast groupSize)

end Evaluation
end Aiur.NativeAIR.LogUp
