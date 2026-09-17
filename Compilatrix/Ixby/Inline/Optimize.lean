import Compilatrix.Ixby.Inline.Check

/-! Optional, deterministic candidate production. A selected image always
includes complete-image evidence from the independent checker. Disabled,
unsupported, exhausted, and rejected attempts retain the admitted original. -/

namespace Compilatrix.Ixby.Inline

open Ix.Ixby

structure Policy where
  version : Nat := 1
  enabled : Bool := true
  protectedPrefix : Nat := 0
  maxWork : Nat := 1000000
  deriving BEq, Repr

inductive Status where
  | optimized (sites : Nat)
  | disabled
  | unsupportedVersion (version : Nat)
  | workLimit (needed allowed : Nat)
  | unchanged
  | rejected (reason : String)
  deriving BEq, Repr

private def operandWork : Instr → Nat
  | .letOp (.primitive _ args) _ | .letOp (.construct _ args) _ |
      .letOp (.closure _ args) _ | .letOp (.call _ args) _ |
      .letOp (.callSelf args) _ | .tailCall _ args | .tailCallSelf args => args.length
  | .letOp (.apply _ args) _ | .tailApply _ args => args.length + 1
  | .caseCtor _ alternatives => alternatives.length + 1
  | _ => 1

/-- Structural scan budget, measured in declarations, blocks, and operands.
It is independent of concrete input values and guest transition counts. -/
def work (program : Program) : Nat :=
  program.functions.foldl (fun total function =>
    function.blocks.foldl (fun total block => total + 1 + operandWork block.instruction) (total + 1)) 0

private def candidateBlock (limits : Limits) (source : Program) (block : Block) : Block × Nat :=
  match block.instruction with
  | .letOp (.call callee args) next =>
    match recognize source callee with
    | none => (block, 0)
    | some leaf =>
      if args.length = leaf.arity ∧ operandsBound block.locals args ∧ leaf.arity + 1 ≤ limits.locals then
        match leaf.operation.substitute args with
        | none => (block, 0)
        | some replacement => ({ block with instruction := .letOp replacement.toOp next }, 1)
      else (block, 0)
  | _ => (block, 0)

/-- This producer is not a proof oracle. `check` accepts its result only after
independently inspecting the original and candidate at every program position. -/
def candidate (limits : Limits) (source : Program) (protectedPrefix : Nat) : Program × Nat := Id.run do
  let mut functions := source.functions
  let mut sites := 0
  for index in [protectedPrefix:source.functions.size] do
    let original := source.functions[index]!
    let mut blocks := original.blocks
    for block in [:original.blocks.size] do
      let (replacement, count) := candidateBlock limits source original.blocks[block]!
      blocks := blocks.set! block replacement
      sites := sites + count
    functions := functions.set! index { original with blocks }
  return ({ source with functions }, sites)

structure Outcome (limits : Limits) (source : Program) (protectedPrefix : Nat) where
  program : Program
  certificate : Certificate limits source program protectedPrefix
  status : Status

/-- Select only a checked candidate. An admitted original is the fallback even
when an external or future producer proposes an invalid rewrite. `sites` is a
diagnostic count and contributes no premise to the certificate. -/
def selectCandidate {limits source protectedPrefix}
    (original : Certificate limits source source protectedPrefix)
    (program : Program) (sites : Nat) : Outcome limits source protectedPrefix :=
  match check limits source program protectedPrefix with
  | .error reason => ⟨source, original, .rejected reason⟩
  | .ok certificate => ⟨program, certificate, .optimized sites⟩

/-- Invalid original programs remain errors. Every optional optimization failure
returns the original image with its checked reflexive certificate. -/
def optimize (limits : Limits) (source : Program) (policy : Policy := {}) :
    Except String (Outcome limits source policy.protectedPrefix) := do
  let original ← check limits source source policy.protectedPrefix
  let unchanged (status : Status) : Outcome limits source policy.protectedPrefix :=
    ⟨source, original, status⟩
  if !policy.enabled then return unchanged .disabled
  if policy.version != 1 then return unchanged (.unsupportedVersion policy.version)
  let needed := work source
  if needed > policy.maxWork then return unchanged (.workLimit needed policy.maxWork)
  let (program, sites) := candidate limits source policy.protectedPrefix
  if sites == 0 then return unchanged .unchanged
  return selectCandidate original program sites

end Compilatrix.Ixby.Inline
