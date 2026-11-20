import IxAI.Stmt

/-!
# A toy kernel over content-addressed statements

Ix checks Ixon terms with a verified kernel. This mock replaces the type theory with a small
propositional natural-deduction calculus so the pipeline around it can be exercised:

* Statements (`IxAI.Stmt`) and proofs are plain syntax with no names, so a constant's address depends only on
  its content. Renaming a declaration never changes its address, which mirrors Ixon's
  alpha-invariant addressing.
* The checker reads only an `Interface`: the statements and axiom footprints of the constants a
  proof cites. Proof bodies of dependencies are never consulted, as in a kernel that does not
  unfold theorems.
-/

namespace IxAI

/-- A content address: the BLAKE3 digest of a canonical encoding under a domain tag. -/
abbrev Address := Digest

/-- The address of a statement, separated by a domain tag from constant addresses. -/
def Address.ofStmt (s : Stmt) : Address := digestOf "stmt" s

/-- Proof terms. `ax` and `hole` assert a statement without justification; the checker accepts
them as well-typed, and the assumption policy decides whether they are admissible. -/
inductive Proof where
  | triv
  | hyp (i : Nat)
  | lam (a : Stmt) (body : Proof)
  | app (f x : Proof)
  | pair (p q : Proof)
  | fst (p : Proof)
  | snd (p : Proof)
  | cite (c : Address)
  | ax (name : String) (s : Stmt)
  | hole (s : Stmt)
  deriving DecidableEq, Hashable, Repr, Inhabited

def Proof.encode (b : ByteArray) : Proof → ByteArray
  | .triv => b.push 0
  | .hyp i => Enc.enc (b.push 1) i
  | .lam a p => p.encode (Enc.enc (b.push 2) a)
  | .app f x => x.encode (f.encode (b.push 3))
  | .pair p q => q.encode (p.encode (b.push 4))
  | .fst p => p.encode (b.push 5)
  | .snd p => p.encode (b.push 6)
  | .cite c => Enc.enc (b.push 7) c
  | .ax n s => Enc.enc (Enc.enc (b.push 8) n) s
  | .hole s => Enc.enc (b.push 9) s

instance : Enc Proof := ⟨Proof.encode⟩

/-- What a checker needs to know about a dependency: its statement and the axioms it rests on.
Never its proof. -/
structure IfaceEntry where
  addr : Address
  stmt : Stmt
  axioms : List String
  deriving Repr

abbrev Interface := List IfaceEntry

def Interface.lookup (I : Interface) (c : Address) : Option IfaceEntry :=
  I.find? (·.addr == c)

def infer (I : Interface) (ctx : List Stmt) : Proof → Except String Stmt
  | .triv => pure .top
  | .hyp i =>
    match ctx[i]? with
    | some s => pure s
    | none => throw s!"unbound hypothesis {i}"
  | .lam a body => do
    let b ← infer I (a :: ctx) body
    pure (.imp a b)
  | .app f x => do
    let tf ← infer I ctx f
    let tx ← infer I ctx x
    match tf with
    | .imp a b => if a = tx then pure b else throw s!"argument proves {tx}, expected {a}"
    | s => throw s!"applied a proof of {s}, which is not an implication"
  | .pair p q => do
    let a ← infer I ctx p
    let b ← infer I ctx q
    pure (.and a b)
  | .fst p => do
    match ← infer I ctx p with
    | .and a _ => pure a
    | s => throw s!"fst of {s}"
  | .snd p => do
    match ← infer I ctx p with
    | .and _ b => pure b
    | s => throw s!"snd of {s}"
  | .cite c =>
    match I.lookup c with
    | some e => pure e.stmt
    | none => throw s!"cites {c}, which is not in the interface"
  | .ax _ s => pure s
  | .hole s => pure s

def Proof.hasHole : Proof → Bool
  | .hole _ => true
  | .lam _ p | .fst p | .snd p => p.hasHole
  | .app p q | .pair p q => p.hasHole || q.hasHole
  | _ => false

/-- Constants this proof cites directly. -/
def Proof.cites : Proof → List Address
  | .cite c => [c]
  | .lam _ p | .fst p | .snd p => p.cites
  | .app p q | .pair p q => p.cites ++ q.cites
  | _ => []

/-- An axiom is identified by its name *and* its statement's address. Policies list these
identities, so an allowed axiom name cannot be reused to assert a different statement; Ix names
axioms by constant address for the same reason. -/
def axiomId (name : String) (s : Stmt) : String := s!"{name}:{(Address.ofStmt s).short}"

/-- Axioms the proof rests on: its own `ax` uses plus the recorded footprints of what it cites.
Ix claims carry the same information as the axioms beyond the standard ones. -/
def Proof.footprint (I : Interface) : Proof → List String
  | .ax n s => [axiomId n s]
  | .cite c => ((I.lookup c).map (·.axioms)).getD []
  | .lam _ p | .fst p | .snd p => p.footprint I
  | .app p q | .pair p q => p.footprint I ++ q.footprint I
  | _ => []

end IxAI
