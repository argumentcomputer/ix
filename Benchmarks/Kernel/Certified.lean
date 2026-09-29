/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Tests.Ix.Kernel.Structures
import Tests.Ix.Kernel.Literals
import Tests.Ix.Kernel.Quotients

/-! # Native certified-kernel scaling probes

Input construction and validation precede the timer. Each action reads its
input from an IO reference within the timed region, so the native compiler
cannot precompute a captured pure result. The driver runs one action per
process; `scripts/bench-certified-kernel.py` handles warmup, repetitions,
revision metadata, and process peak RSS. These probes exercise Ix.Kernel,
not the Rust checker or Ix.Tc.
-/

namespace Benchmarks.Kernel.Certified

open Ix.Kernel Ix.Kernel.Model

def prop {β : Type} : VExpr β := .sort .zero
def type0 {β : Type} : VExpr β := .sort (.succ .zero)

def simpleDecl {β : Type} (key : β) : Decl β :=
  ⟨key, ⟨[.defn 0 .definition type0 prop .safe]⟩⟩

def nestedLambda : Nat → VExpr Nat
  | 0 => prop
  | n + 1 => .lam prop (nestedLambda n)

def nestedType : Nat → VExpr Nat
  | 0 => type0
  | n + 1 => .forallE prop (nestedType n)

def betaTerm : Nat → VExpr Nat
  | 0 => prop
  | n + 1 => .app (.lam type0 (.bvar 0)) (betaTerm n)

def arityType : Nat → AExpr Nat
  | 0 => .sort (.succ .zero)
  | n + 1 => .forallE .never (.sort (.succ .zero)) (arityType n)

/-- Deterministic full-width keys. Construction is outside the timed region. -/
def address (n : Nat) : Address :=
  ⟨ByteArray.mk (Array.ofFn fun (i : Fin 32) => UInt8.ofNat (n / 256 ^ i.val))⟩

def repeated (n : Nat) (d : Decl String) : List (Decl String) :=
  (List.range n).map fun i => { d with address := s!"sample-{i}" }

def checkAction {β : Type} [DecidableEq β] (fuel : Nat) (ds : List (Decl β)) : IO (IO Nat) := do
  let input ← IO.mkRef ds
  return do
    let ds ← input.get
    match check.{0,1} {fuel} ds with
    | .ok env =>
      let sink ← IO.mkRef env
      return (← sink.get).entries.length
    | .error e => throw (IO.userError s!"fixture did not accept: {repr e}")

def prepare (kind : String) (size fuel : Nat) : IO (IO Nat) := do
  match kind with
  | "env" => checkAction fuel ((List.range size).map simpleDecl)
  | "address" => checkAction fuel ((List.range size).map fun n => simpleDecl (address n))
  | "references" =>
    let ds := (List.range size).map fun n =>
      (⟨n + 1, ⟨[.defn 0 .definition type0 (.const (.member 0 0) []) .safe]⟩⟩ : Decl Nat)
    checkAction fuel (simpleDecl 0 :: ds)
  | "binders" =>
    checkAction fuel [⟨0, ⟨[.defn 0 .definition (nestedType size) (nestedLambda size) .safe]⟩⟩]
  | "beta" => checkAction fuel [⟨0, ⟨[.defn 0 .definition type0 (betaTerm size) .safe]⟩⟩]
  | "context" =>
    let input ← IO.mkRef (List.range size)
    return do
      let indices ← input.get
      let ctx : Context Nat := indices.foldl (fun ctx _ => ctx.push (.sort .zero)) []
      let sink ← IO.mkRef ctx
      return (← sink.get).length
  | "spine" =>
    let e := AExpr.appN (.bvar 0) (List.replicate size (.sort .zero))
    let ctx := [arityType size]
    unless (inferA.{0,1} fuel (fun _ => none) ctx e).isSome do
      throw (IO.userError "stuck-spine input failed its typing precheck")
    let input ← IO.mkRef (ctx, e)
    return do
      let (ctx, e) ← input.get
      let sink ← IO.mkRef (whnf.{0,1} fuel (fun _ => none) ctx e).result
      unless decide ((← sink.get) = e) do
        throw (IO.userError "stuck-spine reduction changed its input")
      return size
  | "ordinary" =>
    let ds := [Tests.Ix.Kernel.Literals.natDecl, Tests.Ix.Kernel.Literals.eqDecl,
      Tests.Ix.Kernel.Literals.addDecl]
    checkAction fuel (ds ++ repeated size Tests.Ix.Kernel.Literals.twoPlusTwo)
  | "structure" =>
    let ds := [Tests.Ix.Kernel.Structures.prodDecl, Tests.Ix.Kernel.Structures.eqDecl]
    let samples := (List.range size).map fun i =>
      { (if i % 2 == 0 then Tests.Ix.Kernel.Structures.fstMk
          else Tests.Ix.Kernel.Structures.etaProd) with address := s!"sample-{i}" }
    checkAction fuel (ds ++ samples)
  | "quotient" =>
    checkAction fuel (Tests.Ix.Kernel.Quotients.primitives ++
      repeated size Tests.Ix.Kernel.Quotients.liftMk)
  | _ => throw (IO.userError s!"unknown probe: {kind}")

def run (kind : String) (size fuel : Nat) : IO Unit := do
  let action ← prepare kind size fuel
  let start ← IO.monoNanosNow
  let checksum ← action
  let stop ← IO.monoNanosNow
  IO.println s!"{kind}\t{size}\t{fuel}\t{stop - start}\t{checksum}\t{Lean.versionString}"

end Benchmarks.Kernel.Certified

def main (args : List String) : IO Unit := do
  match args with
  | [kind, size] =>
    let some size := size.toNat? | throw (IO.userError "size must be a natural number")
    Benchmarks.Kernel.Certified.run kind size 100000
  | [kind, size, fuel] =>
    let some size := size.toNat? | throw (IO.userError "size must be a natural number")
    let some fuel := fuel.toNat? | throw (IO.userError "fuel must be a natural number")
    Benchmarks.Kernel.Certified.run kind size fuel
  | _ => throw (IO.userError
    "usage: bench-certified-kernel env|address|references|binders|beta|context|spine|ordinary|structure|quotient SIZE [FUEL]")
