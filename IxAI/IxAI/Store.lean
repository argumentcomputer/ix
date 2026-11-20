import IxAI.Kernel
import IxAICommon.Merkle

/-!
# Truth Mines store

An append-only store of checked constants with a Merkle root. Each entry was checked against the
interface of the entries before it, so any prefix is itself a checked store, and so is any
dependency-closed subset (see `Task.lean`).
-/

namespace IxAI

structure Entry where
  /-- Display name. Not part of any address. -/
  name : String
  stmt : Stmt
  proof : Proof
  /-- Axiom footprint, computed at admission and rechecked by `checkEntry`. -/
  axioms : List String := []
  deriving Repr, Inhabited

def Entry.addr (e : Entry) : Address := digestOf "const" (e.stmt, e.proof)

def Entry.stmtAddr (e : Entry) : Address := Address.ofStmt e.stmt

def Entry.deps (e : Entry) : List Address := e.proof.cites

def Entry.toIface (e : Entry) : IfaceEntry := ⟨e.addr, e.stmt, e.axioms⟩

def okB : Except String Unit → Bool
  | .ok _ => true
  | .error _ => false

def checkEntry (I : Interface) (e : Entry) : Except String Unit := do
  if e.proof.hasHole then throw "proof contains a hole"
  let s ← infer I [] e.proof
  unless s = e.stmt do throw s!"proof establishes {s}, not {e.stmt}"
  unless e.axioms = e.proof.footprint I do throw "recorded axiom footprint is wrong"

structure Store where
  entries : List Entry := []
  deriving Repr

namespace Store

def interface (s : Store) : Interface := s.entries.map Entry.toIface

def root (s : Store) : Digest := merkleRootV2 (s.entries.map (·.addr))

def find? (s : Store) (a : Address) : Option Entry := s.entries.find? (·.addr == a)

def findByStmt? (s : Store) (a : Address) : Option Entry := s.entries.find? (·.stmtAddr == a)

/-- Admit a new constant. Rejects ill-typed proofs and proof holes; axioms are recorded, not
judged. Judging axioms is the consumer's assumption policy. -/
def admit (s : Store) (e : Entry) : Except String Store := do
  let e := { e with axioms := (e.proof.footprint s.interface).eraseDups }
  checkEntry s.interface e
  if s.entries.any (·.addr == e.addr) then throw s!"{e.name} is already present"
  pure { entries := s.entries ++ [e] }

/-- Full recheck from scratch: what every consumer does today without certificates. -/
def checkAll (s : Store) : Bool := go [] s.entries
where
  go (pre : List Entry) : List Entry → Bool
    | [] => true
    | e :: rest => okB (checkEntry (pre.map Entry.toIface) e) && go (pre ++ [e]) rest

def membership? (s : Store) (a : Address) : Option MerklePathV2 :=
  (s.entries.findIdx? (·.addr == a)).map (merklePathV2 (s.entries.map (·.addr)))

/-- Does the store contain a checked proof of statement `a` whose axioms are all allowed? -/
def provesWithin (s : Store) (a : Address) (allowed : List String) : Bool :=
  s.entries.any fun e => e.stmtAddr == a && e.axioms.all (allowed.contains ·)

/-- Transitive dependency closure, by fixpoint iteration bounded by the store size. -/
def closure (s : Store) (start : List Address) : List Address :=
  (List.range (s.entries.length + 1)).foldl (fun acc _ => step acc) start.eraseDups
where
  step (acc : List Address) : List Address :=
    (acc ++ acc.flatMap fun a => ((s.find? a).map Entry.deps).getD []).eraseDups

end Store

end IxAI
