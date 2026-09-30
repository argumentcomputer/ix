/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Certified.Ordinary.Read

/-! # Constructors with ordinary fields after recursive ones

Lean orders a constructor's fields as declared; the ordinary shape class needs
the ordinary fields first. When no ordinary field depends on a recursive one,
the declared constructor is the ordinary one with its fields permuted. This
file reads such a block into its canonical (ordinary-first) shape, recording
each declared field's canonical position; `Ix.Kernel.Check` admits the
canonical block and values the supplied constructors and recursor by closed
wrapper terms over it (`Ix.Kernel.Revalue`).

Nothing here is trusted: every term built from this reading is checked by
inference and conversion before it is used. -/

namespace Ix.Kernel.Certified.Ordinary

open Model Inductive

universe u v

variable {β : Type u} [DecidableEq β]

/-- Rename the variables of a raw term above `depth` binders by `f`; `none` if
some variable has no image. -/
def renameVars (f : Nat → Option Nat) : Nat → VExpr β → Option (VExpr β)
  | depth, .bvar i =>
    if i < depth then some (.bvar i) else (f (i - depth)).map fun j => .bvar (j + depth)
  | _, .sort l => some (.sort l)
  | _, .const r ls => some (.const r ls)
  | depth, .app fn a => return .app (← renameVars f depth fn) (← renameVars f depth a)
  | depth, .lam D b => return .lam (← renameVars f depth D) (← renameVars f (depth + 1) b)
  | depth, .forallE D B => return .forallE (← renameVars f depth D) (← renameVars f (depth + 1) B)
  | depth, .letE t w b =>
    return .letE (← renameVars f depth t) (← renameVars f depth w) (← renameVars f (depth + 1) b)
  | depth, .proj r i x => return .proj r i (← renameVars f depth x)
  | _, .natLit r n => some (.natLit r n)

/-- The canonical position of each declared field: ordinary fields first, in
declared order, then recursive fields. -/
def canonicalPositions (recursive : List Bool) : List Nat :=
  let a := recursive.count false
  (recursive.foldl (fun (acc : List Nat × Nat × Nat) isRec =>
    let (out, ordinary, recs) := acc
    if isRec then (out ++ [a + recs], ordinary, recs + 1) else (out ++ [ordinary], ordinary + 1, recs))
    ([], 0, 0)).1

/-- The variable map from the context of the declared field at `k` into a
canonical context with `m` ordinary fields: a declared field maps to its
ordinary position; a recursive one has no image; parameters follow. -/
def fieldRenaming (recursive : List Bool) (positions : List Nat) (k m : Nat) (j : Nat) :
    Option Nat :=
  if j < k then
    let d := k - 1 - j
    if recursive.getD d false then none else some (m - 1 - positions.getD d 0)
  else some (j - k + m)

/-- Read a constructor whose ordinary fields may follow recursive ones, into
its canonical constructor and each declared field's canonical position. -/
def readInterleavedConstructor (fuel : Nat) (entries : Environment β) (family : ConstRef β)
    (nparams : Nat) (Γp : Context β) (ctor : Ctor β) : Search (Constructor β × List Nat) := do
  let (_, rest) ← splitN nparams ctor.type
  let (rawFields, result) ← splitN ctor.nfields rest
  let recursive := rawFields.map fun F => (peelToFamily family F).isSome
  let positions := canonicalPositions recursive
  let a := recursive.count false
  let n := rawFields.length
  -- Ordinary fields, each renamed into the context of the ordinary ones before it.
  let mut fields : List (AExpr β) := []
  for (F, k) in rawFields.zipIdx do
    if !recursive.getD k false then
      let some F' := renameVars (fieldRenaming recursive positions k fields.length) 0 F
        | throw (.unsupported "an ordinary field depends on a recursive field")
      let D ← annotate.{u,v} fuel entries (Telescope.context Γp fields) F'
      fields := fields ++ [D]
  let Γc := Telescope.context Γp fields
  -- Recursive fields, in the context of all ordinary fields.
  let mut recs : List (RecursiveField β) := []
  for (F, k) in rawFields.zipIdx do
    if recursive.getD k false then
      let some F' := renameVars (fieldRenaming recursive positions k a) 0 F
        | throw (.unsupported "a recursive field depends on a recursive field")
      let some (rawDomains, args) := peelToFamily family F' | throw .noMatch
      let domains ← annotateTelescope.{u,v} fuel entries Γc rawDomains
      let indices ← (args.drop nparams).mapM fun x =>
        annotate.{u,v} fuel entries (Telescope.context Γc domains) x
      recs := recs ++ [⟨domains, indices⟩]
  let some result' := renameVars (fieldRenaming recursive positions n a) 0 result
    | throw (.unsupported "the constructor's indices depend on a recursive field")
  let some (_, args) := peelToFamily family result' | throw .noMatch
  let indices ← (args.drop nparams).mapM fun x => annotate.{u,v} fuel entries Γc x
  return (⟨fields, recs, indices⟩, positions)

/-- A block read with interleaved fields: the canonical reading, and each
constructor's canonical positions. -/
structure InterleavedReading (β : Type u) where
  reading : Reading β
  positions : List (List Nat)

/-- Read a family and recursor pair whose constructors may interleave ordinary
and recursive fields. -/
def readInterleavedBlock (fuel : Nat) (entries : Environment β) (source : β) (block : Block β) :
    Search (InterleavedReading β) :=
  match block.members with
  | [.induct uvars nparams nindices type ctors .safe, .recursor ruvars _ _ _ _ _ _ k .safe] => do
    let (rawParams, rest) ← splitN nparams type
    let (rawIndices, body) ← splitN nindices rest
    match body with
    | .sort level =>
      let parameters ← annotateTelescope.{u,v} fuel entries [] rawParams
      let Γp := Telescope.context [] parameters
      let indices ← annotateTelescope.{u,v} fuel entries Γp rawIndices
      let read ← ctors.mapM
        (readInterleavedConstructor.{u,v} fuel entries (.member source 0) nparams Γp)
      let shape : Shape β := ⟨uvars, parameters, indices, level, read.map (·.1)⟩
      let mode? : Option ElimMode :=
        if ruvars = uvars + 1 then some .large else if ruvars = uvars then some .small else none
      match mode? with
      | some mode => return ⟨⟨shape, mode, k⟩, read.map (·.2)⟩
      | none => throw .noMatch
    | _ => throw .noMatch
  | _ => throw .noMatch

/-! ## Wrapper terms and declared rules

Built from the supplied types and checked by the kernel before use; a wrong
term only declines. -/

/-- Peel `n` Π binders off an annotated type. -/
def peelPis : Nat → AExpr β → Option (List (PropWhen × AExpr β) × AExpr β)
  | 0, e => some ([], e)
  | n + 1, .forallE p D B => do
    let (bs, r) ← peelPis n B
    return ((p, D) :: bs, r)
  | _ + 1, _ => none

def lamsOf (bs : List (PropWhen × AExpr β)) (body : AExpr β) : AExpr β :=
  bs.foldr (fun (p, D) b => .lam p D b) body

def pisOf (bs : List (PropWhen × AExpr β)) (body : AExpr β) : AExpr β :=
  bs.foldr (fun (p, D) b => .forallE p D b) body

/-- The supplied constructor `i`, valued by the canonical one: the declared
fields passed in canonical order. -/
def ctorWrapper (source : β) (i universes nparams : Nat) (positions : List Nat)
    (type : AExpr β) : Option (AExpr β) := do
  let n := positions.length
  let (bs, _) ← peelPis (nparams + n) type
  let fieldArgs ← (List.range n).mapM fun c =>
    (positions.findIdx? (· == c)).map fun d => AExpr.bvar (n - 1 - d)
  return lamsOf bs (.appN (.const (.ctor source 0 i) (VLevel.params universes))
    (parameterVars n nparams ++ fieldArgs))

/-- The supplied recursor, valued by the canonical one: each minor premise
adapted to take the canonical fields and pass them in declared order.
`canonical` is the canonical recursor's type; `ctors` gives each
constructor's recursive-field count and canonical positions. -/
def recWrapper (recursor : ConstRef β) (ruvars nparams nminors nindices : Nat)
    (canonical : AExpr β) (ctors : List (Nat × List Nat)) (type : AExpr β) : Option (AExpr β) := do
  let m := nparams + 1 + nminors + nindices + 1
  let (bs, _) ← peelPis m type
  let var (t : Nat) : AExpr β := .bvar (m - 1 - t)
  -- The canonical minor premise types, in the wrapper body's context.
  let mut cursor := canonical
  for t in List.range (nparams + 1) do
    match cursor with
    | .forallE _ _ B => cursor := B.inst (var t)
    | _ => none
  let mut minors : List (AExpr β) := []
  for ((b, positions), i) in ctors.zipIdx do
    match cursor with
    | .forallE _ D B =>
      let n := positions.length
      let (mbs, _) ← peelPis (n + b) D
      let fieldArgs := positions.map fun c => AExpr.bvar (n + b - 1 - c)
      let ihArgs := (List.range b).map fun r => AExpr.bvar (b - 1 - r)
      let minor := AExpr.bvar (m - 1 - (nparams + 1 + i) + n + b)
      minors := minors ++ [lamsOf mbs (.appN minor (fieldArgs ++ ihArgs))]
      cursor := B.inst (var (nparams + 1 + i))
    | _ => none
  let leading := (List.range (nparams + 1)).map var
  let trailing := (List.range (nindices + 1)).map fun t => var (nparams + 1 + nminors + t)
  return lamsOf bs (.appN (.const recursor (VLevel.params ruvars)) (leading ++ minors ++ trailing))

/-- The rule of constructor `i` in declared field order: the equation between
the recursor at the constructor and the supplied right side, and the rule's
type. -/
def declaredRule (source : β) (recursor : ConstRef β) (mode : ElimMode)
    (universes ruvars nparams nminors : Nat) (i : Nat) (recType ctorType : AExpr β)
    (nfields : Nat) (rhs : AExpr β) : Option (ConstantEquation β × AExpr β) := do
  let pv := zeroCondition mode.motiveLevel
  let sl := mode.sourceLevels universes
  let (leading, _) ← peelPis (nparams + 1 + nminors) recType
  let (cbs, result) ← peelPis (nparams + nfields) ctorType
  let fieldBinders := (cbs.drop nparams).zipIdx.map fun ((_, D), k) =>
    (pv, (D.instL sl).liftN (1 + nminors) k)
  let indices := ((Ix.Kernel.spine result []).2.drop nparams).map fun e =>
    (e.instL sl).liftN (1 + nminors) nfields
  let major := AExpr.appN (.const (.ctor source 0 i) sl)
    (parameterVars (1 + nminors + nfields) nparams ++ parameterVars 0 nfields)
  let binders := leading.map (fun (_, D) => (pv, D)) ++ fieldBinders
  let lhsBody := AExpr.appN (.const recursor (VLevel.params ruvars))
    (parameterVars nfields (nparams + 1 + nminors) ++ indices ++ [major])
  return (⟨lamsOf binders lhsBody, rhs⟩, pisOf binders (.appN (.bvar (nminors + nfields)) (indices ++ [major])))

end Ix.Kernel.Certified.Ordinary
