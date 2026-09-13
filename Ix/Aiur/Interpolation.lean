/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Polynomial
import Ix.Aiur.LogUp

/-! Coefficients and evaluation of the native FRI row interpolant.
The evaluator preserves the native early return at a node. Elsewhere it
checks every inverse; the domain proofs establish that these checks succeed.
-/

namespace Aiur.NativeAIR.Interpolation

def derivativeValue [OfNat R 0] [Add R] [Mul R] (point : R) : List R → R
  | [] => 0
  | _ :: rest => Quotient.horner point rest + point * derivativeValue point rest

def combine [OfNat R 0] [Add R] [Mul R] (vanishing : List R) (scale : R) :
    List (R × R) → List R
  | [] => []
  | (root, value) :: rest =>
    Polynomial.add (Polynomial.scale (value * (root * scale)) (Polynomial.divide root vanishing))
      (combine vanishing scale rest)

def coefficients [OfNat R 0] [OfNat R 1] [Add R] [Sub R] [Mul R]
    (samples : List (R × R)) (scale : R) : List R :=
  combine (Polynomial.fromRoots (samples.map Prod.fst)) scale samples

open ProofCodec (Extension)

def weightedSum (scale point : Extension) : List (Extension × Extension) → Option Extension
  | [] => some 0
  | (root, value) :: rest => do
    let inverse ← (point - root).tryInverse
    let tail ← weightedSum scale point rest
    return value * (root * scale) * inverse + tail

def evaluate (scale point : Extension) (samples : List (Extension × Extension)) : Option Extension :=
  match samples.find? (fun sample => point == sample.1) with
  | some sample => some sample.2
  | none => do
    let sum ← weightedSum scale point samples
    return sum * LogUp.product (samples.map (fun sample => point - sample.1))

def foldSamples (parent arity : Domain.Subgroup) (index : Nat) (values : List Extension) :
    List (Extension × Extension) :=
  ((Polynomial.foldingNodes parent arity index).map Extension.ofBase).zip values

def foldScale (parent arity : Domain.Subgroup) (index : Nat) : G :=
  (G.ofNat (Domain.size arity) * (FriDomain.foldNode parent arity index 0).pow (Domain.size arity)).inverse

def foldRow (parent arity : Domain.Subgroup) (index : Nat) (values : List Extension)
    (point : Extension) : Option Extension :=
  if arity.val > parent.val || index ≥ 2^(parent.val - arity.val) || values.length != Domain.size arity then none
  else evaluate (Extension.ofBase (foldScale parent arity index)) point (foldSamples parent arity index values)

end Aiur.NativeAIR.Interpolation
