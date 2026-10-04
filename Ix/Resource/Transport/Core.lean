module
public import Ix.Resource.Check

/-! Authenticated nominal metadata for source-contract typing. The addressed
adapter constructs this sidecar from the canonical input bytes. It is not
provided by the resource profile. Erased canonical-family validation remains
a separate prerequisite of combined admission. -/
@[expose] public section
namespace Ix.Resource.Transport
open Ixon

inductive Kind where
  | definition | theorem | opaqueDecl | inductiveType | constructor | recursor | quotient
  | axiomDecl (standard : Bool)
  deriving BEq, Repr, Inhabited

structure Constructor where
  index : UInt64
  family : UInt64
  position : Nat
  params : Nat
  fields : Nat
  deriving BEq, Repr, Inhabited

structure Inductive where
  index : UInt64
  params : Nat
  indices : Nat
  constructors : Array UInt64
  deriving BEq, Repr, Inhabited

structure Rule where
  fields : Nat
  rhs : Ixon.Expr
  deriving BEq, Repr, Inhabited

structure Recursor where
  index : UInt64
  family : UInt64
  k : Bool
  params : Nat
  motives : Nat
  minors : Nat
  indices : Nat
  rules : Array Rule
  deriving BEq, Repr, Inhabited

def Recursor.major (r : Recursor) : Nat := r.params + r.motives + r.minors + r.indices

structure Metadata where
  universes : Array Ixon.Univ := #[]
  levelArities : Array Nat := #[]
  /-- Relevance includes the complete runtime dependency graph and overlays. -/
  resourceSensitive : Array Bool := #[]
  /-- Canonical builtin identities, independent of profile literal hints. -/
  natType : Option Ixon.Expr := none
  stringType : Option Ixon.Expr := none
  eqType : Option UInt64 := none
  kinds : Array Kind := #[]
  /-- Unsafe inductives bypass erased positivity validation. -/
  unsafePrimitives : Array Nat := #[]
  inductives : Array Inductive := #[]
  constructors : Array Constructor := #[]
  recursors : Array Recursor := #[]
  /-- Decoded natural payloads, indexed as in Program's blob table. -/
  naturals : Array (UInt64 × Nat) := #[]
  deriving BEq, Repr, Inhabited

structure Failure where
  declaration : Option Nat := none
  error : Resource.Error
  deriving Repr

def Metadata.constructor? (m : Metadata) (i : UInt64) : Option Constructor :=
  m.constructors.find? (·.index == i)
def Metadata.inductive? (m : Metadata) (i : UInt64) : Option Inductive :=
  m.inductives.find? (·.index == i)
def Metadata.recursor? (m : Metadata) (i : UInt64) : Option Recursor :=
  m.recursors.find? (·.index == i)
def Metadata.natural? (m : Metadata) (i : UInt64) : Option Nat :=
  (m.naturals.find? (·.1 == i)).map (·.2)

/-- The logical judgment never consumes a profile-rewritten source type. -/
def sourceProgram (m : Metadata) (p : Program) : Program :=
  { p with interfaces := #[], natType := m.natType, stringType := m.stringType }
end Ix.Resource.Transport
end
