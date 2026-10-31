module

public import IxC.Kernel.Core

@[expose] public section

/-!
# The units check (S1)

The fold's input is a sequence of **units**: one record's lowering. A mutual
or nested block's record lowers to the in-process modeller's generated
records (every name they declare derived, `.aux`, over the block's type
keys; `Frontend.InModel.generate`) followed by the block's `indDecl`; every
other record lowers to one declaration. `unitsOf` recovers them from the
fold's input: a maximal run of generated records, closed by the next
declaration.

**The check** (`checkUnits`, run by the fold after it accepts,
`Cached.checkDecls`): no unit holds the fold's own `basisDecl` (no frontend
emits one), every unit is closed by a declaration that is not generated and
declares every base its generated records declare, no unit past the front (the first `preludeSize` declarations, the
prelude's) declares a prelude role, and no two units declare a common base
(`Key.base`). It is a
decided property of the fold's anonymous input, read by the verifier. What it
gives the proofs (`Verify/Rename/UnionUnits.lean`): the input after the
prelude's front is a list of well formed units (`UnitsOk`), as the union of
two accepted lists (`Cached.AcceptsRef.union`) takes it. A stream that
satisfies it on a valid input loses nothing: a record's lowering declares the
record's own keys, records are distinct, and the front holds the prelude's
declarations once. What it rules out is an input the union's statement does
not cover: a generated record separated from its block (a reorder that split
a unit), or a base declared by two records.
-/

namespace Ix.Kernel

variable {md : Mode}

/-- A derived key. -/
def Key.isAux : Key md → Bool
  | .aux _ _ => true
  | _ => false

/-- **A generated record** (the modeller's): it declares names, all of them
derived. -/
def Declaration.isGenerated (d : Declaration md) : Bool :=
  !d.names.isEmpty && d.names.all Key.isAux

/-- The fold's own record for a pinned basis block. -/
def Declaration.isBasis : Declaration md → Bool
  | .basisDecl _ => true
  | _ => false

/-- `unitsOf`, with the open run of generated records (reversed). -/
def unitsGo : List (Declaration md) → List (Declaration md) → List (List (Declaration md))
  | acc, [] => if acc.isEmpty then [] else [acc.reverse]
  | acc, d :: ds =>
    if d.isGenerated then unitsGo (d :: acc) ds else (d :: acc).reverse :: unitsGo [] ds

/-- **The units of a list**: maximal runs of generated records, each closed by
the next declaration (a trailing run is a unit of its own). -/
def unitsOf (ds : List (Declaration md)) : List (List (Declaration md)) := unitsGo [] ds

/-- The bases a unit declares. -/
def unitBases (u : List (Declaration md)) : List (Key md) :=
  (u.flatMap Declaration.names).map Key.base

/-- A unit's generated records (all but its last declaration) and its closing
declaration (its last). -/
def unitSplit : List (Declaration md) → Option (List (Declaration md) × Declaration md)
  | [] => none
  | [d] => some ([], d)
  | d :: ds => (unitSplit ds).map fun p => (d :: p.1, p.2)

/-- The bases a unit's generated records declare. -/
def genBases (u : List (Declaration md)) : List (Key md) :=
  match unitSplit u with
  | some (gs, _) => (gs.flatMap Declaration.names).map Key.base
  | none => []

/-- The bases a unit's closing declaration declares. -/
def closerBases (u : List (Declaration md)) : List (Key md) :=
  match unitSplit u with
  | some (_, c) => c.names.map Key.base
  | none => []

/-- **A unit's shape**: it is closed by a declaration that is not generated,
and every base its generated records declare, the closing declaration
declares (a block's model records are over the block's own keys). -/
def unitShapeOk (u : List (Declaration md)) : Bool :=
  (match unitSplit u with
   | some (_, c) => !c.isGenerated
   | none => true) && (genBases u).all (closerBases u).contains

/-- The message of a unit at position `i` whose shape fails. -/
def unitShapeMsg (u : List (Declaration md)) (i : Nat) : Msg md :=
  match (genBases u).find? (fun j => !(closerBases u).contains j) with
  | some j =>
    msg!"units: a generated record of the unit at position {i} declares {j}, which the unit's closing declaration does not"
  | none => msg!"units: the generated records at position {i} are not closed by a block"

/-- **The units check** from `seen` (every base declared by an earlier unit, at
that unit's position), over units starting at position `i`. -/
def checkUnitsGo (seen : Std.HashMap (Key md) Nat) :
    List (List (Declaration md)) → Nat → Except (CheckError md × Nat) Unit
  | [], _ => pure ()
  | u :: us, i =>
    if u.any Declaration.isBasis then
      throw (.notImplemented msg!"units: a basis record (the fold's own) at position {i}", i)
    else if !unitShapeOk u then
      throw (.notImplemented (unitShapeMsg u i), i)
    else
      match (if preludeSize ≤ i then (unitBases u).find? Key.isPreludeRole else none) with
      | some j =>
        throw (.notImplemented
          msg!"units: {j}, a prelude role, is declared past the front, by the unit at position {i}", i)
      | none =>
        match (unitBases u).find? seen.contains with
        | some j =>
          throw (.notImplemented
            msg!"units: {j} is declared by the unit at position {i} and by the unit at position {seen.getD j 0}",
            i)
        | none => checkUnitsGo ((unitBases u).foldl (fun m j => m.insert j i) seen) us (i + u.length)

/-- **The units check** of the fold's input: no unit holds a basis record, and
no two units declare a common base. -/
def checkUnits (ds : Array (Declaration md)) : Except (CheckError md × Nat) Unit :=
  checkUnitsGo {} (unitsOf ds.toList) 0

end Ix.Kernel
