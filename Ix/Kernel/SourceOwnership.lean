module

public import Ix.Kernel.Ingress

/-!
Finite source-header ownership checks for the verified lazy loader.
The checker does not convert expressions or inspect a kernel environment.
-/

public section
@[expose] section

namespace Ix.Kernel

/-- The finite projection keys contributed by one source member. -/
def memberProjectionIds (block : Address) (idx : UInt64) : Ixon.MutConst → Array (KId .anon)
  | .defn _ => #[⟨defnProjAddr block idx, ()⟩]
  | .recr _ => #[⟨recrProjAddr block idx, ()⟩]
  | .indc ind => #[⟨indcProjAddr block idx, ()⟩] ++
      (anonCtorAddrs block idx ind).map (⟨·, ()⟩)

/-- Enumerate actual source projection keys, including constructors. -/
def blockProjectionIds (block : Address) (constant : Ixon.Constant) : Array (KId .anon) :=
  match constant.info with
  | .muts members => (Array.range members.size).flatMap fun idx =>
      memberProjectionIds block idx.toUInt64 members[idx]!
  | _ => #[]

/-- Address data for a verified source header. Repeated keys within one block
are permitted; only different owners or a standalone/projection overlap reject. -/
structure OwnershipRow where
  addr : Address
  projections : Array (KId .anon)
  standalone : Bool

def ownershipRow (addr : Address) (constant : Ixon.Constant) : OwnershipRow :=
  ⟨addr, blockProjectionIds addr constant, (ingressBlockAddr? addr constant.info).isNone⟩

/-- Only verified, parsed constants can be used by the production loader. -/
def sourceOwnershipRows (source : Ixon.Env) : List OwnershipRow :=
  source.consts.toList.filterMap fun (addr, _) =>
    match getConstVerified source addr true with
    | .ok (some constant) => some (ownershipRow addr constant)
    | _ => none

/-- A finite comparison of source projection ownership and standalone keys. -/
def ownershipRowsCheck (rows : List OwnershipRow) : Bool :=
  rows.all fun left => rows.all fun right =>
    (left.projections.all fun id => !right.projections.contains id || left.addr == right.addr) &&
    (!left.standalone || !right.projections.contains ⟨left.addr, ()⟩)

/-- Optional source-only preflight for the ownership preservation theorems.
Failure reports conflicting ownership; it does not change loader behavior. -/
def sourceOwnershipCheck (source : Ixon.Env) : Bool :=
  ownershipRowsCheck (sourceOwnershipRows source)

end Ix.Kernel

end
end
