import IxAI.Store

/-!
# Tasks and the rewarder

A task fixes its target independently of the candidate: the target statement and its address,
an interface carved from a certified root, and an assumption policy. The rewarder runs the kernel
on the candidate against that interface. The theorems below say what an `accepted` verdict
guarantees, whatever the candidate model did.
-/

namespace IxAI

structure Policy where
  allowedAxioms : List String
  deriving Repr

/-- The toy logic has no counterpart of Lean's `propext`, `Classical.choice` and `Quot.sound`,
so the standard policy admits no axioms. -/
def Policy.standard : Policy := ⟨[]⟩

structure Task where
  id : String
  /-- In Ix this is the address of the elaboration-certified target statement. -/
  target : Address
  targetStmt : Stmt
  interface : Interface
  policy : Policy

structure Candidate where
  name : String
  stmt : Stmt
  proof : Proof
  deriving Repr

inductive Verdict where
  | accepted
  | wrongTarget (got expected : Address)
  | illTyped (msg : String)
  | hole
  | policyViolation (axioms : List String)
  /-- An exhausted budget is an unknown result. It must never become a negative label. -/
  | timeout
  deriving Repr, DecidableEq

def Verdict.isAccepted : Verdict → Bool
  | .accepted => true
  | _ => false

def reward (t : Task) (c : Candidate) : Verdict :=
  if Address.ofStmt c.stmt ≠ t.target ∨ c.stmt ≠ t.targetStmt then
    .wrongTarget (Address.ofStmt c.stmt) t.target
  else if c.proof.hasHole then .hole
  else
    match infer t.interface [] c.proof with
    | .error e => .illTyped e
    | .ok s =>
      if s ≠ c.stmt then .illTyped s!"proof establishes {s}"
      else if (c.proof.footprint t.interface).all (t.policy.allowedAxioms.contains ·) then
        .accepted
      else .policyViolation (c.proof.footprint t.interface).eraseDups

/-- An accepted candidate proves exactly the fixed target, with no holes, by a proof the kernel
accepts against the task interface, using only allowed axioms. A model cannot earn reward by
weakening or restating the target. -/
theorem reward_accepted {t : Task} {c : Candidate} (h : reward t c = .accepted) :
    c.stmt = t.targetStmt ∧ Address.ofStmt c.stmt = t.target ∧ c.proof.hasHole = false ∧
      infer t.interface [] c.proof = .ok c.stmt ∧
      (c.proof.footprint t.interface).all (t.policy.allowedAxioms.contains ·) = true := by
  unfold reward at h
  split at h
  · cases h
  rename_i h1
  split at h
  · cases h
  rename_i h2
  split at h
  · cases h
  rename_i s hinf
  split at h
  · cases h
  rename_i h3
  split at h
  · rename_i h4
    simp only [not_or, Decidable.not_not] at h1
    simp only [Decidable.not_not] at h3
    subst h3
    exact ⟨h1.2, h1.1, by simpa using h2, hinf, h4⟩
  · cases h

/-! ## Task environments carved from a store -/

/-- The environment for "prove `target` again": the dependency closure of its reference proof,
minus the target itself and anything with the same statement. Only interfaces are exposed. -/
def mkTask (s : Store) (target : Entry) (policy : Policy) : Task :=
  let keep := s.closure target.deps
  { id := target.name
    target := target.stmtAddr
    targetStmt := target.stmt
    interface := (s.entries.filter fun e =>
        keep.contains e.addr && e.addr != target.addr && e.stmtAddr != target.stmtAddr).map
      Entry.toIface
    policy }

/-- A task environment never offers the target, or a renamed copy of it, as a citable lemma. -/
theorem mkTask_excludes_target (s : Store) (target : Entry) (policy : Policy) :
    ∀ i ∈ (mkTask s target policy).interface,
      i.addr ≠ target.addr ∧ Address.ofStmt i.stmt ≠ target.stmtAddr := by
  intro i hi
  simp only [mkTask, List.mem_map] at hi
  obtain ⟨e, he, rfl⟩ := hi
  rw [List.mem_filter] at he
  have h := he.2
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  exact ⟨h.1.2, h.2⟩

/-- How large the sandbox's view is, compared with the store it came from. -/
def Task.interfaceSize (t : Task) : Nat := t.interface.length

end IxAI
