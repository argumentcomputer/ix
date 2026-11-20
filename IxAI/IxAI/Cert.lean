import IxAI.Store

/-!
# Claims, certificates and light clients

`Holds` is the shape of the statement an Ix certificate establishes: some store with this root
checks, and proves the statement at this address using only allowed axioms. Ix's version is
`IxVM.consistent` plus STARK/PLONK soundness, with a BLAKE3-collision escape.

`ProofSystem` abstracts the prover and verifier. `mock` carries the whole store as its witness and
rechecks it, so its soundness is a theorem here but it is not succinct. A real Ix system has the
same interface with a fixed-size certificate (864 B at the PLONK terminal) whose soundness rests
on the IxVM theorem and cryptographic assumptions. Everything above this file only uses
`ProofSystem.Sound`, so swapping the mock for Ix changes cost, not the pipeline's guarantees.
-/

namespace IxAI

structure Claim where
  root : Digest
  stmtAddr : Address
  allowedAxioms : List String
  deriving Repr

def Holds (c : Claim) : Prop :=
  ∃ s : Store, s.root = c.root ∧ s.checkAll = true ∧ s.provesWithin c.stmtAddr c.allowedAxioms = true

structure ProofSystem where
  Cert : Type
  prove : Store → Claim → Option Cert
  verify : Claim → Cert → Bool
  /-- Bytes a verifier must receive. -/
  size : Cert → Nat

def ProofSystem.Sound (ps : ProofSystem) : Prop :=
  ∀ c cert, ps.verify c cert = true → Holds c

structure MockCert where
  witness : Store

def mockVerify (c : Claim) (cert : MockCert) : Bool :=
  cert.witness.root == c.root && cert.witness.checkAll &&
    cert.witness.provesWithin c.stmtAddr c.allowedAxioms

def mock : ProofSystem where
  Cert := MockCert
  prove s c := if mockVerify c ⟨s⟩ then some ⟨s⟩ else none
  verify := mockVerify
  size cert := 64 * cert.witness.entries.length

theorem mock_sound : mock.Sound := by
  intro c cert h
  simp only [mock, mockVerify, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨cert.witness, h.1.1, h.1.2, h.2⟩

/-- What a light client does: from the statement alone (which it can elaborate locally because
statements are small) compute the address, then verify. It never sees the proof or the store. -/
def lightClientAccepts (ps : ProofSystem) (root : Digest) (stmt : Stmt) (allowed : List String)
    (cert : ps.Cert) : Bool :=
  ps.verify ⟨root, Address.ofStmt stmt, allowed⟩ cert

theorem lightClient_sound {ps : ProofSystem} (hs : ps.Sound) {root stmt allowed cert}
    (h : lightClientAccepts ps root stmt allowed cert = true) :
    Holds ⟨root, Address.ofStmt stmt, allowed⟩ :=
  hs _ _ h

/-- A consumer that does not trust the producer and has no certificate must recheck the store. -/
def fullRecheckAccepts (s : Store) (stmt : Stmt) (allowed : List String) : Bool :=
  s.checkAll && s.provesWithin (Address.ofStmt stmt) allowed

end IxAI
