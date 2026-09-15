import Compilatrix.Aiur.Wire.Codec
import Ix.Aiur.Compiler.CallOrder

/-! Invoke the pinned static-component checker after a resource preflight.
The retained result is the upstream Boolean check, not a checker-to-AIR or
bytecode semantic theorem. Empty components select the ranked fallback.

The upstream unit-counter analysis allocates from input/output counts. These
counts must be bounded separately from their compact wire representation. -/

namespace Compilatrix.Aiur.Wire

open _root_.Aiur.Bytecode
open Compilatrix.Ixon

structure CheckLimits where
  maxFunctions : Nat := 1024
  maxDepth : Nat := 128
  maxValues : Nat := 65536
  maxCandidates : Nat := 4096
  maxWork : Nat := 10000000
  deriving Repr, Inhabited

structure CheckCost where
  nodes : Nat := 0
  produced : Nat := 0
  returns : Nat := 0
  selfCalls : Nat := 0

def CheckCost.add (left right : CheckCost) : CheckCost :=
  ⟨left.nodes + right.nodes, left.produced + right.produced,
    max left.returns right.returns, left.selfCalls + right.selfCalls⟩

def blockCost (self : Nat) : Nat → Block → Option CheckCost
  | 0, _ => none
  | depth + 1, block => do
    let own := block.ops.foldl (fun cost op => cost.add
      ⟨1, UnitCounter.outputCount op, 0, match op with
        | .call callee _ _ false => if callee == self then 1 else 0
        | _ => 0⟩) { nodes := 1 }
    match block.ctrl with
    | .return _ values | .yield _ values => return own.add { returns := values.size }
    | .match _ cases fallback =>
      let branches ← cases.foldlM (fun cost branch => do
        return cost.add (← blockCost self depth branch.2)) own
      match fallback with
      | none => return branches
      | some block => return branches.add (← blockCost self depth block)
    | .matchContinue _ cases fallback _ _ _ continuation =>
      let branches ← cases.foldlM (fun cost branch => do
        return cost.add (← blockCost self depth branch.2)) own
      let branches ← match fallback with
        | none => pure branches
        | some block => do return branches.add (← blockCost self depth block)
      return branches.add (← blockCost self depth continuation)

/-- Conservative admission score, not a machine-time theorem. It counts
candidate scans and declared allocation sizes even when a check could exit
early. Consumer limits never alter the wire bytes or content root. -/
def componentCheckFits (limits : CheckLimits) (value : Toplevel) : Bool := Id.run do
  if value.callComponents.isEmpty then return true
  if value.functions.size > limits.maxFunctions then return false
  let mut work := 0
  for i in [:value.functions.size] do
    let fn := value.functions[i]!
    let some cost := blockCost i limits.maxDepth fn.body | return false
    let values := fn.layout.inputSize + cost.produced + 1
    let candidates := fn.layout.inputSize + cost.returns
    if values > limits.maxValues || candidates > limits.maxCandidates then return false
    work := work + cost.nodes * (1 + cost.selfCalls * 2 * candidates * values)
    if work > limits.maxWork then return false
  return true

def componentsValid (value : Toplevel) : Bool :=
  value.callComponents.isEmpty || value.validCallComponents

structure ComponentChecked (limits : CheckLimits) (value : Toplevel) : Type where
  bounded : componentCheckFits limits value = true
  accepted : componentsValid value = true

def checkComponents (limits : CheckLimits) (value : Toplevel) :
    Except String (ComponentChecked limits value) := do
  if bounded : componentCheckFits limits value then
    if accepted : componentsValid value then return ⟨bounded, accepted⟩
    else throw "Aiur bytecode: invalid static call components"
  else throw "Aiur bytecode: component analysis resource limit"

structure Ingress (limits : Limits) (checkLimits : CheckLimits)
    (bytes : ByteArray) (root : Address) extends Addressed limits bytes root where
  checked : ComponentChecked checkLimits value

def ingest (limits : Limits) (checkLimits : CheckLimits) (bytes : ByteArray) (root : Address) :
    Except String (Ingress limits checkLimits bytes root) := do
  let addressed ← decodeAddressed limits bytes root
  let checked ← checkComponents checkLimits addressed.value
  return { toAddressed := addressed, checked }

end Compilatrix.Aiur.Wire
