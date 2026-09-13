import Compilatrix.Modular.Basic

/-! Exact source-address evidence can be retained independently of a unit's
current imported context. Dependency and usage checks still run in that
context. No hash comparison substitutes for equality of source constants. -/

namespace Compilatrix.Modular

open Ixon (Address Constant)

def constantDependencies (constant : Constant) : List Address :=
  constant.refs.toList ++ match constant.info with
    | .cPrj projection => [projection.block]
    | .rPrj projection => [projection.block]
    | .iPrj projection => [projection.block]
    | .dPrj projection => [projection.block]
    | _ => []

/-- Successful canonical validation, including the address boundary's own
wire, sharing, and work checks, for every complete owned constant. -/
abbrev AddressEvidence (constants : SourceEntries) : Prop :=
  ∀ entry ∈ constants, entry.2.addressChecked = .ok entry.1

namespace SourceCheck

private def address (entry : Address × Constant) :
    Except String (PLift (entry.2.addressChecked = .ok entry.1)) :=
  match entry.2.addressChecked with
  | .error error => .error (reprStr error)
  | .ok actual =>
      if same : actual = entry.1 then
        .ok ⟨congrArg Except.ok same⟩
      else .error "source address does not match its exact canonical constant"

private theorem address_of_evidence (entry : Address × Constant)
    (evidence : entry.2.addressChecked = .ok entry.1) :
    address entry = .ok ⟨evidence⟩ := by
  unfold address
  generalize checked : entry.2.addressChecked = result at *
  cases result with
  | error error => cases evidence
  | ok actual => cases evidence; simp

private def context (policy : Policy) (source : Ixon.Eval.EvalCtx)
    (constant : Constant) : Except String Unit := do
  for dependency in constantDependencies constant do
    ensure ((source.resolve dependency).isSome || (source.blobs dependency).isSome)
      "source reference is absent from the declared dependency closure"
  match Ixon.UsageCheck.checkConstant source.resolve constant policy.checkFuel with
  | .ok _ => pure ()
  | .error error => throw s!"unit usage check: {repr error}"

/-- The original per-entry order: canonical address, dependency resolution,
usage, then the next entry. Successful facts are erased proof fields. -/
def check (policy : Policy) (source : Ixon.Eval.EvalCtx) :
    (constants : SourceEntries) → Except String (PLift (AddressEvidence constants))
  | [] => .ok ⟨by intro entry member; cases member⟩
  | entry :: rest => do
      let first ← address entry
      context policy source entry.2
      let tail ← check policy source rest
      return ⟨by
        intro found member
        rcases List.mem_cons.mp member with same | later
        · subst found; exact first.down
        · exact tail.down found later⟩

/-- Reuse only the exact canonical-address facts. Current dependency and
usage validation remains in the same order. -/
def checkKnown (policy : Policy) (source : Ixon.Eval.EvalCtx) :
    (constants : SourceEntries) → AddressEvidence constants →
      Except String (PLift (AddressEvidence constants))
  | [], evidence => .ok ⟨evidence⟩
  | entry :: rest, evidence => do
      context policy source entry.2
      let _ ← checkKnown policy source rest (fun found member =>
        evidence found (List.mem_cons_of_mem entry member))
      return ⟨evidence⟩

theorem checkKnown_eq (policy : Policy) (source : Ixon.Eval.EvalCtx)
    (constants : SourceEntries) (evidence : AddressEvidence constants) :
    checkKnown policy source constants evidence = check policy source constants := by
  induction constants with
  | nil => rfl
  | cons entry rest ih =>
      simp only [checkKnown, check, address_of_evidence entry (evidence entry (by simp))]
      rw [ih]
      rfl

/-- Attach the exact result of a completed computation without rerunning it. -/
def attachResult (result : Except String α) :
    Except String { value : α // result = .ok value } :=
  match result with
  | .error error => .error error
  | .ok value => .ok ⟨value, rfl⟩

theorem attachResult_map (result : Except String α) :
    (attachResult result).map (·.val) = result := by
  cases result <;> rfl

private theorem map_map (result : Except String α) (first : α → β) (second : β → γ) :
    (result.map first).map second = result.map (fun value => second (first value)) := by
  cases result <;> rfl

/-- Every successful implementation returns a witness for the unchanged
fresh check, even when an earlier canonical-address result is reused. -/
def run (policy : Policy) (source : Ixon.Eval.EvalCtx) (constants : SourceEntries)
    (known : Option (PLift (AddressEvidence constants)) := none) :
    Except String { evidence : PLift (AddressEvidence constants) //
      check policy source constants = .ok evidence } :=
  let selected := match known with
    | none => check policy source constants
    | some evidence => checkKnown policy source constants evidence.down
  have equal : selected = check policy source constants := by
    cases known with
    | none => rfl
    | some evidence => exact checkKnown_eq policy source constants evidence.down
  (attachResult selected).map fun result => ⟨result.val, equal.symm.trans result.property⟩

theorem run_eq (policy : Policy) (source : Ixon.Eval.EvalCtx) (constants : SourceEntries)
    (known : Option (PLift (AddressEvidence constants))) :
    (run policy source constants known).map (·.val) = check policy source constants := by
  unfold run
  rw [map_map]
  change (attachResult _).map (·.val) = _
  rw [attachResult_map]
  cases known with
  | none => rfl
  | some evidence => exact checkKnown_eq policy source constants evidence.down

end SourceCheck

end Compilatrix.Modular
