import Ix.Cert.RoleClosurePrepare
import Ix.Cert.PreludeAgree

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

/-- **The default role table's binding admits under the admission hash**: its committed
section is stored at the admission hash of its bytes, decodes canonically and is well
formed (`Admission.admitBinding`). This is the run-time form of the table row of the fact
`Tests/Ix/Kernel/Authentication.lean` guards; the kernel cannot hash the committed hex. -/
def DefaultAdmits : Prop :=
  ∃ binding t, Admission.defaultBinding = .ok binding ∧
    Admission.admitBinding Address.admissionHash binding = .ok t

/-- Whether a binding source yields a binding that admits under the admission hash. -/
def admitsOf (e : Except String Admission.Binding) : Bool :=
  match e with
  | .ok binding => (Admission.admitBinding Address.admissionHash binding).isOk
  | .error _ => false

theorem admitsOf_sound {e : Except String Admission.Binding} (h : admitsOf e = true) :
    ∃ binding t, e = .ok binding ∧ Admission.admitBinding Address.admissionHash binding = .ok t := by
  cases e with
  | error _ => cases h
  | ok binding =>
    cases ha : Admission.admitBinding Address.admissionHash binding with
    | error _ => simp [admitsOf, ha, Except.isOk, Except.toBool] at h
    | ok t => exact ⟨binding, t, rfl, ha⟩

/-- `DefaultAdmits`, decided. -/
def defaultAdmits : Bool := admitsOf Admission.defaultBinding

/-- The decision is sound, through `admitsOf_sound`: no proof step evaluates the committed
binding. -/
theorem defaultAdmits_sound (h : defaultAdmits = true) : DefaultAdmits :=
  admitsOf_sound h

/-- **The committed prelude reads alike at both modes**: under the default table it reads in
Source and in anonymous mode, and the two readings agree with names erased
(`PreludeAgree.preludeAgreeB`, a check on the two concrete readings). The agreement lifts to
every renaming (`PreludeAgree.preludeAgree_decls`, `PreludeAgree.preludeAgree_state`). -/
def PreludeAgrees : Prop :=
  ∃ t preS preA, defaultTable = .ok t ∧ preludeFor (md := .source) t = .ok preS ∧
    preludeFor (md := .anon) t = .ok preA ∧ PreludeAgree.preludeAgreeB preS preA = true

/-- Whether two prelude readings agree, names erased. -/
def agreesOfReadings (s : Except String (Prelude .source)) (a : Except String (Prelude .anon)) : Bool :=
  match s, a with
  | .ok preS, .ok preA => PreludeAgree.preludeAgreeB preS preA
  | _, _ => false

theorem agreesOfReadings_sound {s : Except String (Prelude .source)} {a : Except String (Prelude .anon)}
    (h : agreesOfReadings s a = true) :
    ∃ preS preA, s = .ok preS ∧ a = .ok preA ∧ PreludeAgree.preludeAgreeB preS preA = true := by
  cases s with
  | error _ => cases h
  | ok preS =>
    cases a with
    | error _ => cases h
    | ok preA => exact ⟨preS, preA, rfl, rfl, h⟩

/-- Whether a table source's prelude reads alike at both modes. -/
def preludeAgreesOf (table : Except String RoleTable) : Bool :=
  match table with
  | .ok t => agreesOfReadings (preludeFor (md := .source) t) (preludeFor (md := .anon) t)
  | .error _ => false

/-- The decision is sound. No proof step simplifies the prelude readings: simplifying
through them makes Lean evaluate the committed prelude. -/
theorem preludeAgreesOf_sound {e : Except String RoleTable} (h : preludeAgreesOf e = true) :
    ∃ t preS preA, e = .ok t ∧ preludeFor (md := .source) t = .ok preS ∧
      preludeFor (md := .anon) t = .ok preA ∧ PreludeAgree.preludeAgreeB preS preA = true := by
  cases e with
  | error _ => cases h
  | ok t =>
    obtain ⟨preS, preA, hS, hA, agree⟩ := agreesOfReadings_sound (s := preludeFor (md := .source) t)
      (a := preludeFor (md := .anon) t) h
    exact ⟨t, preS, preA, rfl, hS, hA, agree⟩

/-- `PreludeAgrees`, decided. -/
def preludeAgrees : Bool := preludeAgreesOf defaultTable

/-- The decision is sound, through `preludeAgreesOf_sound`: no proof step evaluates the
committed prelude. -/
theorem preludeAgrees_sound (h : preludeAgrees = true) : PreludeAgrees :=
  preludeAgreesOf_sound h

/-- **The shipped role table's certificates check, and its committed fallback sits at
its hashes**: the committed closure, prepared under the default table behind its
committed prelude, defines every well-founded `Nat` operation, and the pure fold accepts
it at some fuel under the table's evidence. The fold reaches each operation's definition
with its dependency closure installed and runs its evidence gate there
(`checkDivModEvidence`), so every gate passed. And every committed prelude and evidence
row is stored at the admission hash of its bytes (`FallbackHashed`), and the default binding
admits under the admission hash (`DefaultAdmits`), and the committed prelude reads alike at
both modes (`PreludeAgrees`). A closed proposition about `IxC/Kernel/Ixon/RoleData.lean`, the verifier's pinned configuration:
it mentions no input. -/
def RoleEvidenceChecks : Prop :=
  (∃ ev ds env, preparedDefault = .ok (ev, ds) ∧ DefinesAll ds ∧ Cached.AcceptsRef .verified ev ds env) ∧
    FallbackHashed ∧ DefaultAdmits ∧ PreludeAgrees

/-- `RoleEvidenceChecks`, with the executed fold and the executed hashes, decided. -/
def roleEvidenceCheck : Bool :=
  closureCheck preparedDefault && fallbackHashed && defaultAdmits && preludeAgrees

/-- **The executed check gives `RoleEvidenceChecks`**, through the fold's
refinement (the set theory is a hypothesis of that walk, not of the
statement's meaning). -/
theorem roleEvidenceChecks_of_check (V : Type w) [SetTheory V] (h : roleEvidenceCheck = true) :
    RoleEvidenceChecks := by
  unfold roleEvidenceCheck at h
  obtain ⟨h₁, agrees⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨h₂, admits⟩ := Bool.and_eq_true_iff.mp h₁
  obtain ⟨closure, hashed⟩ := Bool.and_eq_true_iff.mp h₂
  exact ⟨checks_of_closureCheck V preparedDefault closure, fallbackHashed_iff.mp hashed,
    defaultAdmits_sound admits, preludeAgrees_sound agrees⟩

end Ix.Cert.RoleClosure
