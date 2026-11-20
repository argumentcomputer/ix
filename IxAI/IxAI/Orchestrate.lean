import IxAI.Task
import IxAI.Cert

/-!
# Interface-first orchestration

A project fixes its reviewed statements first (the spec), as the FLT repository does with
`Theorems/` and `P2M/Sol/`. Work is delegated per statement. A worker's result is accepted only if
it proves the exact spec statement under the project policy, against everything accepted so far.
Accepted results go into the project store, from which certificates are promoted for consumers in
other trust domains.
-/

namespace IxAI

structure Goal where
  name : String
  stmt : Stmt
  deriving Repr, Inhabited

inductive Outcome where
  | accepted (addr : Address)
  | rejected (v : Verdict)
  | unknownGoal
  | alreadyProved (by_ : String)
  /-- A helper lemma whose statement is already in the store: reuse the existing constant. -/
  | deduplicated (existing : String)
  deriving Repr

structure LogEntry where
  worker : String
  goal : String
  candidate : String
  outcome : Outcome
  deriving Repr

structure Project where
  name : String
  spec : List Goal
  policy : Policy
  store : Store := {}
  log : List LogEntry := []

namespace Project

def goalFor? (p : Project) (name : String) : Option Goal := p.spec.find? (·.name == name)

def isProved (p : Project) (g : Goal) : Bool := (p.store.findByStmt? (Address.ofStmt g.stmt)).isSome

def openGoals (p : Project) : List Goal := p.spec.filter (!p.isProved ·)

/-- Proved spec goals out of the total. With certificates this is a checkable claim rather than
a dashboard figure. -/
def progress (p : Project) : Nat × Nat := (p.spec.countP p.isProved, p.spec.length)

/-- Spec statements that are the same up to naming: worth catching before delegating. -/
def specDuplicates (p : Project) : List (String × String) :=
  p.spec.flatMap fun g =>
    (p.spec.filter fun h => h.name != g.name && h.name > g.name &&
      Address.ofStmt h.stmt == Address.ofStmt g.stmt).map (g.name, ·.name)

private def record (p : Project) (w g c : String) (o : Outcome) : Project × Outcome :=
  ({ p with log := p.log ++ [⟨w, g, c, o⟩] }, o)

/-- A worker submits a candidate for one named goal. -/
def submit (p : Project) (worker goalName : String) (c : Candidate) : Project × Outcome :=
  match p.goalFor? goalName with
  | none => record p worker goalName c.name .unknownGoal
  | some g =>
    match p.store.findByStmt? (Address.ofStmt g.stmt) with
    | some e => record p worker goalName c.name (.alreadyProved e.name)
    | none =>
      let task : Task :=
        { id := g.name, target := Address.ofStmt g.stmt, targetStmt := g.stmt
          interface := p.store.interface, policy := p.policy }
      match reward task c with
      | .accepted =>
        match p.store.admit ⟨c.name, c.stmt, c.proof, []⟩ with
        | .ok s' =>
          let p' := { p with store := s' }
          record p' worker goalName c.name (.accepted (Entry.addr ⟨c.name, c.stmt, c.proof, []⟩))
        | .error msg => record p worker goalName c.name (.rejected (.illTyped msg))
      | v => record p worker goalName c.name (.rejected v)

/-- Helper lemmas outside the spec. A statement already in the store is not added again under a
new name: content addressing turns agents' duplicated lemmas into reuse. -/
def submitHelper (p : Project) (worker : String) (c : Candidate) : Project × Outcome :=
  match p.store.findByStmt? (Address.ofStmt c.stmt) with
  | some e => record p worker "(helper)" c.name (.deduplicated e.name)
  | none =>
    let task : Task :=
      { id := c.name, target := Address.ofStmt c.stmt, targetStmt := c.stmt
        interface := p.store.interface, policy := p.policy }
    match reward task c with
    | .accepted =>
      match p.store.admit ⟨c.name, c.stmt, c.proof, []⟩ with
      | .ok s' => record { p with store := s' } worker "(helper)" c.name
          (.accepted (Entry.addr ⟨c.name, c.stmt, c.proof, []⟩))
      | .error msg => record p worker "(helper)" c.name (.rejected (.illTyped msg))
    | v => record p worker "(helper)" c.name (.rejected v)

/-- The claim a consumer checks for one goal. -/
def claimFor (p : Project) (g : Goal) : Claim :=
  ⟨p.store.root, Address.ofStmt g.stmt, p.policy.allowedAxioms⟩

/-- Promotion: produce a certificate once, for consumers outside the project. -/
def certify (p : Project) (ps : ProofSystem) (g : Goal) : Option ps.Cert :=
  ps.prove p.store (p.claimFor g)

end Project

end IxAI
