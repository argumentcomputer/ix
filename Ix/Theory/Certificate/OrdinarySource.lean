/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certificate.Ordinary

/-! Untrusted recovery of ordinary descriptions from exact source declarations.
Every removed context slot is checked by lifting back, and the completed
description must reproduce all original source metadata and expressions. -/

namespace Ix.Theory.Certificate.Ordinary

open Model Certified Certified.Ordinary

universe u
variable {β : Type u} [DecidableEq β]
variable [Hints β]

def telescope : VExpr β → List (VExpr β) × VExpr β
  | .forallE A B => let (tail, result) := telescope B; (A :: tail, result)
  | e => ([], e)

def sourceDomains? (fuel n : Nat) (entries : Environment β) :
    Context β → List (VExpr β) → Option (List (AExpr β))
  | _, [] => some []
  | Γ, A :: rest => do
    let typed ← inferSource? fuel n entries Γ A
    let .sort _ := typed.type | none
    let tail ← sourceDomains? fuel n entries (Γ.push typed.expression) rest
    return typed.expression :: tail

def removeVariables? (count : Nat) (e : VExpr β) : Option (VExpr β) :=
  let candidate := e.unliftN count 0
  if candidate.liftN count = e then some candidate else none

def sourceIndices? (fuel : Nat) (entries : Environment β) (shape : Shape β)
    (source : β) (Γ : Context β) (offset : Nat) (result : VExpr β) :
    Option (List (AExpr β)) := do
  if result.appHead != .const (.member source 0) (VLevel.params shape.universes) then none else do
    let args := result.appArgs []
    if args.length != shape.parameters.length + shape.indices.length then none else do
      if args.take shape.parameters.length != VExpr.bvarRevRange offset shape.parameters.length then
        none
      else
        (args.drop shape.parameters.length).mapM fun index => do
          return (← inferSource? fuel shape.universes entries Γ index).expression

def sourceRecursive? (fuel : Nat) (entries : Environment β) (shape : Shape β)
    (source : β) (fields : List (AExpr β)) (previous : Nat) (raw : VExpr β) :
    Option (RecursiveField β) := do
  let raw ← removeVariables? previous raw
  let (domains, result) := telescope raw
  let Γ := Telescope.context shape.parameterContext fields
  let domains ← sourceDomains? fuel shape.universes entries Γ domains
  let indices ← sourceIndices? fuel entries shape source (Telescope.context Γ domains)
    (fields.length + domains.length) result
  return ⟨domains, indices⟩

def sourceConstructor? (fuel : Nat) (entries : Environment β) (shape : Shape β)
    (source : β) (raw : Ctor β) : Option (Constructor β) := do
  let (binders, result) := telescope raw.type
  if binders.take shape.parameters.length != shape.parameters.map AExpr.erase then none else do
    let fields := binders.drop shape.parameters.length
    let ordinary := fields.takeWhile fun A => !A.refs.contains (.member source 0)
    let recursive := fields.drop ordinary.length
    let fields ← sourceDomains? fuel shape.universes entries shape.parameterContext ordinary
    let recursive ← recursive.zipIdx.mapM fun (raw, previous) =>
      sourceRecursive? fuel entries shape source fields previous raw
    let result ← removeVariables? recursive.length result
    let indices ← sourceIndices? fuel entries shape source
      (Telescope.context shape.parameterContext fields) fields.length result
    return ⟨fields, recursive, indices⟩

def description? (fuel : Nat) (entries : Environment β) (source : β) (raw : Const β) :
    Option (Shape β) := do
  let .induct n p i type constructors .safe := raw | none
  let (binders, result) := telescope type
  let .sort level := result | none
  if binders.length != p + i then none else do
    let parameters ← sourceDomains? fuel n entries [] (binders.take p)
    let indices ← sourceDomains? fuel n entries (Telescope.context [] parameters) (binders.drop p)
    let shape : Shape β := ⟨n, parameters, indices, level, []⟩
    let constructors ← constructors.mapM (sourceConstructor? fuel entries shape source)
    let shape := { shape with constructors }
    if shape.source source = raw then some shape else none

def sourceBlock? (fuel : Nat) (entries : Environment β) (store : Store β)
    (source recursor : β) : Option (BlockWitness β) := do
  let ⟨[raw]⟩ ← store.blocks source | none
  let shape ← description? fuel entries source raw
  if shape.RecursorSourceMatches store source recursor .small then
    block? fuel entries shape source recursor .small
  else if shape.RecursorSourceMatches store source recursor .large then
    block? fuel entries shape source recursor .large
  else none

end Ix.Theory.Certificate.Ordinary
