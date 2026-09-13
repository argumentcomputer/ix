/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Quotient
import Ix.Aiur.FriDomain

/-! Coefficients in the native verifier's ascending-power convention.
Trailing zeros are permitted. Synthetic division lowers the coefficient
length without assuming an evaluation point is a root.
-/

namespace Aiur.NativeAIR.Polynomial

def IsZero [OfNat R 0] (coefficients : List R) : Prop :=
  ∀ coefficient ∈ coefficients, coefficient = 0

def Monic [OfNat R 1] (coefficients : List R) : Prop :=
  ∃ initial, coefficients = initial ++ [1]

def add [Add R] : List R → List R → List R
  | [], right => right
  | left, [] => left
  | first :: left, second :: right => (first + second) :: add left right

def sub [OfNat R 0] [Sub R] : List R → List R → List R
  | [], right => right.map (0 - ·)
  | left, [] => left
  | first :: left, second :: right => (first - second) :: sub left right

def scale [Mul R] (scalar : R) (coefficients : List R) : List R :=
  coefficients.map (scalar * ·)

def mulLinear [OfNat R 0] [Sub R] [Mul R] (root : R) (coefficients : List R) : List R :=
  sub (0 :: coefficients) (scale root coefficients)

def fromRoots [OfNat R 0] [OfNat R 1] [Sub R] [Mul R] (roots : List R) : List R :=
  roots.foldr mulLinear [1]

def powerMinus [OfNat R 0] [OfNat R 1] [Sub R] (degree : Nat) (constant : R) : List R :=
  sub (List.replicate degree 0 ++ [1]) [constant]

def divide [OfNat R 0] [Add R] [Mul R] (point : R) : List R → List R
  | [] => []
  | [_] => []
  | _ :: next :: rest => Quotient.horner point (next :: rest) :: divide point (next :: rest)

def foldingNodes (parent arity : Domain.Subgroup) (index : Nat) : List G :=
  (List.range (Domain.size arity)).map (FriDomain.foldNode parent arity index)

end Aiur.NativeAIR.Polynomial
