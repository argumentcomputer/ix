import Ix.Compiler.IxIR2.Validate
import Ix.Compiler.Ixon.Hash

/-! Bounded proposals for a borrowed ABI. Summaries are claims, not facts:
the checker reconstructs every variant from the exact baseline and validates
the complete program, including all owned wrappers and their call sites.
The first version borrows one shared parameter and rejects credit effects
and recursive calls. It leaves constructor-field retains intact. -/

namespace Ix.Compiler.IxIR2.Borrow

open Ix.Compiler.Ixon (Address)

structure Summary where
  owner : Address
  borrowed : Address
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr

structure Limits where
  maxCandidates : Nat := 32
  maxRounds : Nat := 16
  maxAttempts : Nat := 256
  validator : Validate.Limits := Validate.defaultLimits
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr

inductive Error where
  | limit
  | missingOwner (owner : Address)
  | signature (owner : Address)
  | unsupported (owner : Address)
  | duplicateSummary
  | validation (error : Validate.Error)
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr

/-- This is an internal label, not a persistent IxIR₂ content address.
Collisions are rejected by whole-program validation. -/
def borrowedAddress (owner : Address) : Address :=
  Address.blake3 ("compilatrix/borrowed-entry/1\x00".toUTF8 ++ owner.hash)

def eligible (definition : Function) : Bool :=
  definition.signature.params == #[{ world := .shared, passing := .owned }] &&
    definition.signature.result == .shared

def borrowedAt? (summaries : List Summary) (owner : Address) : Option Address :=
  (summaries.find? fun summary => summary.owner == owner).map (·.borrowed)

private def loanAtom (loans : Array Bool) : Atom → Bool
  | .reg id => loans[id]?.getD false
  | .lit _ | .erased => false

private def borrowedCap : ValueCap → ValueCap
  | .owned .shared => .borrowed .shared .caller
  | cap => cap

/-- Replace root retains by non-consuming moves so result-register numbering
does not change. Releases have no result and can simply be removed. Fetches
produce field views, whose later retains remain real ownership operations. -/
def rewriteBlock (owner : Address) (summaries : List Summary) (block : Block) :
    Except Error Block := do
  if !block.creditParams.isEmpty then throw (.unsupported owner)
  let mut loans := block.valueParams.map (· == .owned .shared)
  let mut instructions := #[]
  for instruction in block.instructions do
    match instruction with
    | .retainShared atom =>
        let loan := loanAtom loans atom
        instructions := instructions.push (if loan then .move atom else instruction)
        loans := loans.push loan
    | .move atom =>
        instructions := instructions.push instruction
        loans := loans.push (loanAtom loans atom)
    | .releaseShared atom =>
        if !loanAtom loans atom then instructions := instructions.push instruction
    | .call target args =>
        instructions := instructions.push (.call ((borrowedAt? summaries target).getD target) args)
        loans := loans.push false
    | .alloc .. | .fetch .. | .papp .. | .apply .. =>
        instructions := instructions.push instruction
        loans := loans.push false
    | .dropUnique .. | .freeUnique .. =>
        instructions := instructions.push instruction
    | .allocWith .. | .discardCredit .. | .takeUnique .. | .resetShared .. |
        .callSelf .. | .extern .. => throw (.unsupported owner)
  let terminator ← match block.terminator with
    | .tailCall target args =>
        pure (.tailCall ((borrowedAt? summaries target).getD target) args)
    | .tailCallSelf .. | .branchCredit .. => throw (.unsupported owner)
    | terminator => pure terminator
  return { block with valueParams := block.valueParams.map borrowedCap
                      instructions, terminator }

def rewriteFunction (owner : Address) (summaries : List Summary)
    (definition : Function) : Except Error Function := do
  if !eligible definition then throw (.signature owner)
  let blocks ← definition.blocks.mapM (rewriteBlock owner summaries)
  return {
    signature := { definition.signature with
      params := #[{ world := .shared, passing := .borrowed }], papSafe := false }
    blocks }

/-- Dynamic/PAP entry still owns its argument. Its wrapper keeps the lender
alive during the borrowed call and performs the final release on return. -/
def ownedWrapper (borrowed : Address) (definition : Function) : Function :=
  { signature := definition.signature
    blocks := #[{
      valueParams := #[.owned .shared], creditParams := #[]
      instructions := #[.call borrowed #[.reg 0], .releaseShared (.reg 0)]
      terminator := .ret (.reg 1) }] }

def rebuild (limits : Limits) (baseline : Program) (summaries : List Summary) :
    Except Error Program := do
  if summaries.length > limits.maxCandidates then throw .limit
  if summaries.any fun summary =>
      (summaries.filter fun other => other.owner == summary.owner).length != 1 then
    throw .duplicateSummary
  let mut variants := []
  for summary in summaries do
    let some (_, .fn definition) := baseline.declarations.find? (fun entry => entry.1 == summary.owner)
      | throw (.missingOwner summary.owner)
    variants := variants ++ [(summary.borrowed, .fn (← rewriteFunction summary.owner summaries definition))]
  let declarations := baseline.declarations.map fun (owner, declaration) =>
    match borrowedAt? summaries owner, declaration with
    | some borrowed, .fn definition => (owner, .fn (ownedWrapper borrowed definition))
    | _, _ => (owner, declaration)
  return { baseline with declarations := declarations ++ variants }

structure Checked (limits : Limits) (context : Validate.Context) (baseline : Program) where
  summaries : List Summary
  program : Program
  produced : rebuild limits baseline summaries = .ok program
  baselineChecked : Validate.Checked limits.validator context baseline
  checked : Validate.Checked limits.validator context program

def check (limits : Limits) (context : Validate.Context) (baseline : Program)
    (summaries : List Summary) : Except Error (Checked limits context baseline) := do
  let baselineChecked ← match h : Validate.validateWith limits.validator context baseline with
    | .error error => .error (.validation error)
    | .ok stats => pure (Validate.Checked.mk stats h)
  match h : rebuild limits baseline summaries with
  | .error error => .error error
  | .ok program =>
      match checked : Validate.validateWith limits.validator context program with
      | .error error => .error (.validation error)
      | .ok stats => return {
          summaries, program, produced := h, baselineChecked
          checked := ⟨stats, checked⟩ }

structure Inference where
  summaries : List Summary := []
  attempts : Nat := 0
  rounds : Nat := 0
  rejected : Nat := 0
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr

/-- Bounded dependency iteration. Each new claim is checked with all earlier
claims. A failed attempt does not evict the last checked set. This version
does not infer cyclic SCCs; a cycle without an accepted seed is left owned. -/
def infer (limits : Limits) (context : Validate.Context) (baseline : Program) :
    Inference := Id.run do
  let candidates := baseline.declarations.filterMap fun
    | (owner, .fn definition) => if eligible definition then some owner else none
    | _ => none
  if candidates.length > limits.maxCandidates then return {}
  let mut state : Inference := {}
  for _ in [:limits.maxRounds] do
    let before := state.summaries.length
    state := { state with rounds := state.rounds + 1 }
    for owner in candidates do
      if state.attempts < limits.maxAttempts && (borrowedAt? state.summaries owner).isNone then
        let proposed := state.summaries ++ [{ owner, borrowed := borrowedAddress owner }]
        state := { state with attempts := state.attempts + 1 }
        match check limits context baseline proposed with
        | .ok _ => state := { state with summaries := proposed }
        | .error _ => state := { state with rejected := state.rejected + 1 }
    if state.summaries.length == before || state.attempts == limits.maxAttempts then break
  return state

theorem Checked.valid {limits context baseline} (result : Checked limits context baseline) :
    Validate.ValidWith limits.validator context result.program :=
  ⟨result.checked.stats, result.checked.accepted⟩

theorem Checked.exactRewrite {limits context baseline} (result : Checked limits context baseline) :
    rebuild limits baseline result.summaries = .ok result.program := result.produced

end Ix.Compiler.IxIR2.Borrow
