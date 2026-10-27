import Ix.Cert.RoleClosurePrepare

/-! # The role table's certificates check on their own closure (Route A, B6b)

The default role table (`IxC/Kernel/Ixon/RoleData.lean`) is the verifier's pinned
configuration. For each well-founded `Nat` operation (`Ix.Kernel.natDivModNames`)
its proof evidence must pass the fold's gate (`Ix.Kernel.checkDivModEvidence`,
reached from `checkDecl`'s definition arm) in the environment that holds the
operation's dependency closure. `kernel-pin-gen` pins that closure in RoleData
(`closure`, with the blobs its literals reference and its definitions' hints), so
the statement is closed: `RoleEvidenceChecks` mentions no input.

* `prepareClosure`: the Ixon entry's reading (`Admission.readStream`) of the
  closure records under a table, behind a prelude, with the prelude in front
  (`preparePrelude`): the evidence and the declarations the fold runs over;
* `RoleEvidenceChecks`: on the default table and its committed prelude and
  closure, the declarations include a definition of every well-founded operation,
  and the pure fold accepts them at some fuel (`Cached.AcceptsRef`), so every
  operation's gate passed; and every committed prelude and evidence row is stored at
  the admission hash of its bytes (`FallbackHashed`);
* `roleEvidenceCheck`: the same with the executed fold and hashes, decided;
  `roleEvidenceChecks_of_check` gives `RoleEvidenceChecks` from it, through the
  fold's refinement (`Cached.checkDecls_refines_ref`).

`kernel-pin-gen` runs `closureCheck` on the closure before writing it, and
`cert-statement` checks `roleEvidenceCheck` on the committed file at every
regeneration. Replaced by CQX.7 (the compiler binds its own compiled
certificate theorems). -/

namespace Ix.Cert.RoleClosure

open Ix.Kernel Ix.Kernel.Reader

/-- **A passing check is a reference accept** of what it prepared, defining
every well-founded operation, through the fold's refinement
(`Cached.checkDecls_refines_ref`; the set theory is a hypothesis of that walk,
not of the statement's meaning). -/
theorem checks_of_closureCheck (V : Type w) [SetTheory V]
    (prepared : Except String (Evidences .anon × List (Declaration .anon))) (h : closureCheck prepared = true) :
    ∃ ev ds env, prepared = .ok (ev, ds) ∧ DefinesAll ds ∧ Cached.AcceptsRef .verified ev ds env := by
  cases prepared with
  | error e => cases h
  | ok pair =>
    obtain ⟨ev, ds⟩ := pair
    simp only [closureCheck, Bool.and_eq_true] at h
    obtain ⟨defines, accepted⟩ := h
    cases run : Cached.checkDecls .verified ev ds.toArray with
    | error e => rw [run] at accepted; cases accepted
    | ok env =>
      have ref := Cached.checkDecls_refines_ref V rfl run
      rw [List.toList_toArray] at ref
      exact ⟨ev, ds, env, rfl, (definesAll_iff ds).1 defines, ref⟩

/-! ## The committed closure -/

/-- The committed closure records, decoded canonically. -/
def closureRecords : Except String (Array (Address × Ixon.Constant)) :=
  decodeCommitted "closure" RoleData.closure

/-- The blobs the committed closure's literals reference. -/
def closureBlobs : Except String (List (Address × ByteArray)) :=
  RoleData.closureBlobs.toList.mapM fun (hex, bytes) => do
    let some a := addressOfHex hex | throw s!"closure blob: bad address {hex}"
    let some b := bytesOfHex bytes | throw s!"closure blob: bad bytes at {hex}"
    pure (a, b)

/-- The committed closure's hints. -/
def closureHints : Except String (Array (Address × ReducibilityHint)) :=
  RoleData.closureHints.mapM fun (hex, s) => do
    let some a := addressOfHex hex | throw s!"closure hint: bad address {hex}"
    let some h := hintOfString s | throw s!"closure hint: bad hint {s} at {hex}"
    pure (a, h)

/-- The committed closure, prepared under the default table behind its
committed prelude. -/
def preparedDefault : Except String (Evidences .anon × List (Declaration .anon)) := do
  let t ← defaultTable
  let pre ← preludeFor t
  prepareClosure t pre (← closureRecords) (← closureBlobs) (← closureHints)

/-- **The committed fallback sits at its hashes**: every committed prelude and evidence
row (`RoleData.prelude`, `RoleData.evidence`: the records the reader's store falls back
on behind a stream's own) is stored at the admission hash of its bytes. Reading the
committed file does not recompute these addresses (`decodeCommitted`), and the reader keys
an address by the role bound to the reference it resolves to, so a fallback record under
another address than its hash could lend a role to a stream record of the same
constant. This is the run-time form of the fact `Tests/Ix/Kernel/Authentication.lean`
guards; the kernel cannot decide it on the committed hex strings, which it expands
quadratically. -/
def FallbackHashed : Prop :=
  ∀ row ∈ (RoleData.prelude ++ RoleData.evidence).toList,
    (bytesOfHex row.2).map Address.admissionHash = addressOfHex row.1

/-- `FallbackHashed`, decided. -/
def fallbackHashed : Bool :=
  (RoleData.prelude ++ RoleData.evidence).all fun row =>
    (bytesOfHex row.2).map Address.admissionHash == addressOfHex row.1

theorem fallbackHashed_iff : fallbackHashed = true ↔ FallbackHashed := by
  unfold fallbackHashed FallbackHashed
  rw [Array.all_eq_true_iff_forall_mem]
  simp only [beq_iff_eq, Array.mem_toList_iff]

/-- **The shipped role table's certificates check, and its committed fallback sits at
its hashes**: the committed closure, prepared under the default table behind its
committed prelude, defines every well-founded `Nat` operation, and the pure fold accepts
it at some fuel under the table's evidence. The fold reaches each operation's definition
with its dependency closure installed and runs its evidence gate there
(`checkDivModEvidence`), so every gate passed. And every committed prelude and evidence
row is stored at the admission hash of its bytes (`FallbackHashed`). A closed
proposition about `IxC/Kernel/Ixon/RoleData.lean`, the verifier's pinned configuration:
it mentions no input. -/
def RoleEvidenceChecks : Prop :=
  (∃ ev ds env, preparedDefault = .ok (ev, ds) ∧ DefinesAll ds ∧ Cached.AcceptsRef .verified ev ds env) ∧
    FallbackHashed

/-- `RoleEvidenceChecks`, with the executed fold and the executed hashes, decided. -/
def roleEvidenceCheck : Bool := closureCheck preparedDefault && fallbackHashed

/-- **The executed check gives `RoleEvidenceChecks`**, through the fold's
refinement (the set theory is a hypothesis of that walk, not of the
statement's meaning). -/
theorem roleEvidenceChecks_of_check (V : Type w) [SetTheory V] (h : roleEvidenceCheck = true) :
    RoleEvidenceChecks := by
  unfold roleEvidenceCheck at h
  obtain ⟨closure, hashed⟩ := Bool.and_eq_true_iff.mp h
  exact ⟨checks_of_closureCheck V preparedDefault closure, fallbackHashed_iff.mp hashed⟩

end Ix.Cert.RoleClosure
