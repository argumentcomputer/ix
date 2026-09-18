/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Annotate
import Ix.Kernel.Certified.Ordinary.Shape
import Ix.Kernel.Inductive.Levels

/-! # Reading an ordinary block

An unverified reader from a stored block (an inductive member followed by its
recursor) to the `Shape` that generates it. Nothing depends on the reader
being right: the checker regenerates the block from the shape and compares
it with the stored one exactly, so a misreading is rejected, never accepted.
Regimes inside the read telescopes come from `annotate`; the regimes of the
generated binders are fixed by the shape. -/

namespace Ix.Kernel.Certified.Ordinary

open Model Inductive

universe u v

variable {β : Type u} [DecidableEq β]

/-- Annotate a raw telescope, each domain in the context of its predecessors. -/
def annotateTelescope (fuel : Nat) (entries : Environment β) :
    Context β → List (VExpr β) → Option (List (AExpr β))
  | _, [] => some []
  | Γ, D :: rest => do
    let D' ← (annotate.{u,v} fuel entries Γ D).toOption
    let rest' ← annotateTelescope fuel entries (Γ.push D') rest
    return D' :: rest'

/-- Split exactly `n` leading binders off a raw type. -/
def splitN : Nat → VExpr β → Option (List (VExpr β) × VExpr β)
  | 0, e => some ([], e)
  | n + 1, .forallE D B => do
    let (ds, b) ← splitN n B
    return (D :: ds, b)
  | _ + 1, _ => none

/-- Peel binders until the body is an application of the family, returning the
domains and the family's arguments. -/
def peelToFamily (family : ConstRef β) : VExpr β → Option (List (VExpr β) × List (VExpr β))
  | .forallE D B => do
    let (ds, args) ← peelToFamily family B
    return (D :: ds, args)
  | e =>
    match e.appHead with
    | .const r _ => if r = family then some ([], e.appArgs []) else none
    | _ => none

/-- Read a constructor's fields: ordinary fields first, then recursive fields
whose raw types are lowered over the earlier recursive fields. -/
def readFields (fuel : Nat) (entries : Environment β) (family : ConstRef β) (nparams : Nat) :
    Context β → List (VExpr β) → Nat → Option (List (AExpr β) × List (RecursiveField β))
  | _, [], _ => some ([], [])
  | Γc, F :: raw, nrec =>
    match peelToFamily family (F.unliftN nrec 0) with
    | some (rawDomains, args) => do
      let domains ← annotateTelescope.{u,v} fuel entries Γc rawDomains
      let indices ← (args.drop nparams).mapM fun a => (annotate.{u,v} fuel entries (Telescope.context Γc domains) a).toOption
      let rest ← readFields fuel entries family nparams Γc raw (nrec + 1)
      match rest with
      | (ordinary, recursive) =>
        if ordinary.isEmpty then return ([], ⟨domains, indices⟩ :: recursive) else none
    | none =>
      if nrec ≠ 0 then none else do
        let D ← (annotate.{u,v} fuel entries Γc F).toOption
        let rest ← readFields fuel entries family nparams (Γc.push D) raw 0
        match rest with
        | (ordinary, recursive) => return (D :: ordinary, recursive)

/-- Read one constructor from its stored declaration. -/
def readConstructor (fuel : Nat) (entries : Environment β) (family : ConstRef β) (nparams : Nat)
    (Γp : Context β) (ctor : Ctor β) : Option (Constructor β) := do
  let (_, rest) ← splitN nparams ctor.type
  let (rawFields, result) ← splitN ctor.nfields rest
  let read ← readFields.{u,v} fuel entries family nparams Γp rawFields 0
  match read with
  | (fields, recursive) =>
    let Γc := Telescope.context Γp fields
    let (_, args) ← peelToFamily family (result.unliftN recursive.length 0)
    let indices ← (args.drop nparams).mapM fun a => (annotate.{u,v} fuel entries Γc a).toOption
    return ⟨fields, recursive, indices⟩

/-- What the reader recovers from a block. -/
structure Reading (β : Type u) where
  shape : Shape β
  mode : ElimMode
  k : Bool

/-- Read a block holding one inductive member and its recursor. -/
def readBlock (fuel : Nat) (entries : Environment β) (source : β) (block : Block β) :
    Option (Reading β) :=
  match block.members with
  | [.induct uvars nparams nindices type ctors .safe, .recursor ruvars _ _ _ _ _ _ k .safe] => do
    let (rawParams, rest) ← splitN nparams type
    let (rawIndices, body) ← splitN nindices rest
    match body with
    | .sort level =>
      let parameters ← annotateTelescope.{u,v} fuel entries [] rawParams
      let Γp := Telescope.context [] parameters
      let indices ← annotateTelescope.{u,v} fuel entries Γp rawIndices
      let constructors ← ctors.mapM (readConstructor.{u,v} fuel entries (.member source 0) nparams Γp)
      let shape : Shape β := ⟨uvars, parameters, indices, level, constructors⟩
      if ruvars = uvars + 1 then return ⟨shape, .large, k⟩
      else if ruvars = uvars then return ⟨shape, .small, k⟩
      else none
    | _ => none
  | _ => none

end Ix.Kernel.Certified.Ordinary
