import Ix.Cert.SourceContext.Maps
import Ix.Cert.RecursorSupport

namespace Ix.Cert.SourceContext
open Ix.Kernel Ix.Kernel.Reader

def sameEntry (a b : RecEntry) : Bool := RecursorSupport.entryEq (some a) (some b)
def sameShape (a b : BlockShape) : Bool := a.order == b.order && a.recs == b.recs
private theorem sameEntry_iff (a b : RecEntry) : sameEntry a b = true ↔ a = b := by
  rw [sameEntry,RecursorSupport.entryEq_iff]
  simp only [Option.some.injEq]
  constructor
  · rintro ⟨e,rfl,rfl⟩; rfl
  · intro same; exact ⟨a,rfl,same.symm⟩
private theorem sameShape_iff (a b : BlockShape) : sameShape a b = true ↔ a = b := by
  cases a; cases b
  simp [sameShape]

/-- Every actual finite table is compared in both directions. Required-family
presence is checked separately from equality, so none/none is not a witness. -/
def checkTables (a b : Ctx .anon) : Bool :=
  Maps.check sameEntry a.index.recs b.index.recs &&
  Maps.check sameShape a.index.blocks b.index.blocks &&
  Maps.check (· == ·) a.roles.names b.roles.names &&
  Maps.check (· == ·) a.keys.byAddress b.keys.byAddress &&
  Maps.check (· == ·) a.keys.address b.keys.address

structure Tables (a b : Ctx .anon) : Prop where
  recs : Maps.Agrees a.index.recs b.index.recs
  blocks : Maps.Agrees a.index.blocks b.index.blocks
  roles : Maps.Agrees a.roles.names b.roles.names
  addressKeys : Maps.Agrees a.keys.byAddress b.keys.byAddress
  memberAddresses : Maps.Agrees a.keys.address b.keys.address

theorem checkTables_sound {a b : Ctx .anon} (accepted : checkTables a b = true) : Tables a b := by
  simp only [checkTables,Bool.and_eq_true_iff] at accepted
  obtain ⟨⟨⟨⟨recs,blocks⟩,roles⟩,keys⟩,addresses⟩ := accepted
  exact ⟨Maps.check_sound (fun x y h => (sameEntry_iff x y).mp h) recs,
    Maps.check_sound (fun x y h => (sameShape_iff x y).mp h) blocks,
    Maps.check_sound (fun _ _ h => beq_iff_eq.mp h) roles,
    Maps.check_sound (fun _ _ h => beq_iff_eq.mp h) keys,
    Maps.check_sound (fun _ _ h => beq_iff_eq.mp h) addresses⟩

theorem checkTables_complete {a b : Ctx .anon} (same : Tables a b) : checkTables a b = true := by
  simp only [checkTables,
    Maps.check_complete (fun x => (sameEntry_iff x x).mpr rfl) same.recs,
    Maps.check_complete (fun x => (sameShape_iff x x).mpr rfl) same.blocks,
    Maps.check_complete (fun _ => BEq.rfl) same.roles,
    Maps.check_complete (fun _ => BEq.rfl) same.addressKeys,
    Maps.check_complete (fun _ => BEq.rfl) same.memberAddresses,Bool.and_self]

structure Agrees (a b : Ctx .anon) : Prop extends Tables a b where
  store : a.store = b.store
  blob : a.blob = b.blob
  hint : a.hint = b.hint
  reconstruct : a.reconstruct = b.reconstruct

/-- Agreement of all finite domains (and absence outside them) is available
from Maps.domain_iff/none_outside, instantiated at these actual maps. -/
theorem Tables.domains {a b : Ctx .anon} (same : Tables a b) :
    (∀ r, r ∈ Maps.domain a.index.recs ↔ r ∈ Maps.domain b.index.recs) ∧
    (∀ k, k ∈ Maps.domain a.index.blocks ↔ k ∈ Maps.domain b.index.blocks) ∧
    (∀ r, r ∈ Maps.domain a.roles.names ↔ r ∈ Maps.domain b.roles.names) ∧
    (∀ k, k ∈ Maps.domain a.keys.byAddress ↔ k ∈ Maps.domain b.keys.byAddress) ∧
    (∀ r, r ∈ Maps.domain a.keys.address ↔ r ∈ Maps.domain b.keys.address) :=
  ⟨Maps.agreed_domains same.recs,Maps.agreed_domains same.blocks,
    Maps.agreed_domains same.roles,Maps.agreed_domains same.addressKeys,
    Maps.agreed_domains same.memberAddresses⟩

/-- These equalities cover arbitrary addresses/references, including failures.
They are transport facts; equality of two failures does not supply totality. -/
theorem Agrees.keyAt {a b : Ctx .anon} (same : Agrees a b) (address : Address) :
    a.keyAt address = b.keyAt address := by
  unfold Ctx.keyAt
  rw [same.addressKeys address]
  cases cached : b.keys.byAddress[address]? with
  | some key => rfl
  | none =>
    rw [same.store]
    cases resolved : resolve b.store address with
    | none => rfl
    | some ref => dsimp only; rw [same.roles ref]

theorem Agrees.addressOf {a b : Ctx .anon} (same : Agrees a b) (ref : ConstRef Address) :
    a.addressOf ref = b.addressOf ref := by
  unfold Ctx.addressOf
  rw [same.memberAddresses ref]
  cases cached : b.keys.address[ref]? with
  | some address => rfl
  | none => rw [same.store,same.reconstruct]

theorem Agrees.memberKey {a b : Ctx .anon} (same : Agrees a b) (ref : ConstRef Address) :
    a.memberKey ref = b.memberKey ref := by
  unfold Ctx.memberKey
  rw [same.roles ref]
  cases bound : b.roles.names[ref]? with
  | some key => rfl
  | none =>
    rw [same.addressOf ref]
    have keys : ∀ address : Address, a.keys.byAddress[address]? = b.keys.byAddress[address]? := same.addressKeys
    simp only [keys]

end Ix.Cert.SourceContext
