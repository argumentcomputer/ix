module
public import Ix.MultiStark.Verify.Ood.Basic

/-! Direct grouped logUp equations. Products excluding one message are
evaluated literally (groups have at most eight members), independently of
the native evaluator's prefix/suffix optimization. -/

public section
@[expose] section

namespace MultiStark.Verify.Ood

open Arithmetic (Coordinates)

def readCoordinates (row : Array Ext) (offset : Nat) : Except Error Coordinates :=
  return ⟨← getAt row offset, ← getAt row (offset + 1)⟩

def lookupMessage (computed : Array Ext) (beta gamma : Coordinates) (lookup : Lookup) :
    Except Error Coordinates := do
  let values ← readRefs computed lookup.args.toList
  let fingerprint := values.foldr (fun value acc => (acc.mul gamma).add (Coordinates.embed value)) Coordinates.zero
  return beta.add fingerprint

def lookupEntries (computed : Array Ext) (beta gamma : Coordinates) :
    List Lookup → Except Error (List (Coordinates × Ext))
  | [] => .ok []
  | lookup :: lookups => do
    let message ← lookupMessage computed beta gamma lookup
    let multiplicity ← getAt computed lookup.multiplicity
    let rest ← lookupEntries computed beta gamma lookups
    return (message, multiplicity) :: rest

/-- Defining grouped logUp polynomial, with literal products of all messages
except the selected one. Groups are bounded by key admission (at most eight).
The multiplication/subtraction order is deterministic even before any field
algebra laws are used in a higher-level cryptographic argument. -/
def groupPolynomial (entries : List (Coordinates × Ext)) (delta : Coordinates) : Coordinates :=
  let messages := entries.map Prod.fst
  let product := messages.foldl Coordinates.mul Coordinates.one
  entries.zipIdx.foldl (fun result (entry, index) =>
    let others := (messages.take index ++ messages.drop (index + 1)).foldl Coordinates.mul Coordinates.one
    result.sub (others.scale entry.2)) (product.mul delta)

def groupEquation (computed : Array Ext) (group : Array Lookup) (beta gamma delta : Coordinates) :
    Except Error Coordinates := do
  return groupPolynomial (← lookupEntries computed beta gamma group.toList) delta

def lookupTarget (view : View) (injection : Coordinates) (group : Nat) : Except Error Coordinates :=
  if group + 1 < view.values.circuit.lookupGroups then
    readCoordinates view.values.stage2.1 (2 * (group + 1))
  else (readCoordinates view.values.stage2.2 0).map (·.add injection)

def lookupGroupsFrom (view : View) (computed : Array Ext) (beta gamma injection : Coordinates) :
    Nat → Nat → Except Error (List Ext)
  | _, 0 => .ok []
  | group, remaining + 1 => do
    let source ← readCoordinates view.values.stage2.1 (2 * group)
    let target ← lookupTarget view injection group
    let groupSize := max 1 view.values.circuit.lookupGroupSize
    let chunk := view.values.circuit.lookups.extract (group * groupSize) ((group + 1) * groupSize)
    let equation ← groupEquation computed chunk beta gamma (target.sub source)
    let rest ← lookupGroupsFrom view computed beta gamma injection (group + 1) remaining
    return equation.c0 :: equation.c1 :: rest

def lookupValues (view : View) (computed : Array Ext) : Except Error (Array Ext) := do
  let circuit := view.values.circuit
  ensure (view.values.stage2.1.size == circuit.stage2Width &&
      view.values.stage2.2.size == circuit.stage2Width) .width
  let beta ← readCoordinates view.publics 0
  let gamma ← readCoordinates view.publics 2
  let initial ← readCoordinates view.publics 4
  let final ← readCoordinates view.publics 6
  let injection := ((final.sub initial).scale view.selectors.injectionNorm).scale view.selectors.last
  return (← lookupGroupsFrom view computed beta gamma injection 0 circuit.lookupGroups).toArray

end MultiStark.Verify.Ood
