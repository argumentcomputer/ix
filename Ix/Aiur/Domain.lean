/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Extension

/-! Natural trace domains and the pinned Goldilocks two-adic generators.
The checked out-of-domain selector evaluator rejects every division pole.
-/

namespace Aiur.NativeAIR.Domain

def generators : Array G := #[
  0x0000000000000001, 0xffffffff00000000, 0x0001000000000000,
  0xfffffffeff000001, 0xefffffff00000001, 0x00003fffffffc000,
  0x0000008000000000, 0xf80007ff08000001, 0xbf79143ce60ca966,
  0x1905d02a5c411f4e, 0x9d8f2ad78bfed972, 0x0653b4801da1c8cf,
  0xf2c35199959dfcb6, 0x1544ef2335d17997, 0xe0ee099310bba1e2,
  0xf6b2cffe2306baac, 0x54df9630bf79450e, 0xabd0a6e8aa3d8a0e,
  0x81281a7b05f9beac, 0xfbd41c6b8caa3302, 0x30ba2ecd5e93e76d,
  0xf502aef532322654, 0x4b2a18ade67246b5, 0xea9d5a1336fbc98b,
  0x86cdcc31c307e171, 0x4bbaf5976ecfefd8, 0xed41d05b78d6e286,
  0x10d78dd8915a171d, 0x59049500004a4485, 0xdfa8c93ba46d2666,
  0x7e9bd009b86a0845, 0x400a7f755588e659, 0x185629dcda58878c]

theorem generators_size : generators.size = 33 := rfl

abbrev Subgroup := Fin 33

def ofLogSize (bits : Nat) : Option Subgroup :=
  if bounded : bits < 33 then some ⟨bits, bounded⟩ else none

def size (domain : Subgroup) : Nat := 2 ^ domain.val

def generator (domain : Subgroup) : G :=
  generators[domain.val]'(by simpa only [generators_size] using domain.isLt)

def point (domain : Subgroup) (index : Fin (size domain)) : G :=
  (generator domain).pow index.val

def lastPoint (domain : Subgroup) : G := (generator domain).inverse

def normalizer (domain : Subgroup) : G := G.ofNat (size domain) * generator domain

structure Selectors (W : Type) where
  isFirst : W
  isLast : W
  isTransition : W
  invVanishing : W
  deriving DecidableEq, Repr

open ProofCodec (Extension)

def vanishing (domain : Subgroup) (value : Extension) : Extension :=
  value.power (size domain) - 1

def selectors (domain : Subgroup) (value : Extension) : Option (Selectors Extension) := do
  let z := vanishing domain value
  let lastDenominator := value - Extension.ofBase (lastPoint domain)
  let firstInverse ← (value - 1).tryInverse
  let lastInverse ← lastDenominator.tryInverse
  let vanishingInverse ← z.tryInverse
  return ⟨z * firstInverse, z * lastInverse, lastDenominator, vanishingInverse⟩

end Aiur.NativeAIR.Domain
