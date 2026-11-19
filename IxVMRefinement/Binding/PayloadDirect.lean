import IxVMRefinement.Binding.StoreClausesWalk

/-! # The payload's facts, split at the last step of the reach

An address the payload of group `g` reaches (`PayReach`) is named directly by a family check of a
block the group reaches (`PayDirect`: the family record, an advice record or a container
recursor), or is reached by one step from an address the payload reaches (`PayStep`: an
uncovered used reference, or the block of a projection record) (`payReach_cases`). The payload's
facts (`PayloadFacts`) follow from the same facts at the two kinds of address
(`PayloadFactsOn`, `payloadFacts_of_on`): the direct addresses are what the family checks load
and check themselves; the stepped ones are what those checks admit of their records'
references. -/

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing

section Split

variable {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {Pay : PayloadRel}

/-- **An address the payload of group `g` names directly**: the family check of a block the
group reaches, by its walk or through its payload, names it. -/
def PayDirect (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (Pay : PayloadRel) (g : Nat)
    (a : _root_.Address) : Prop :=
  ∃ B, (GroupReach t E₀ g B ∨ PayReach t E₀ Pay g B) ∧ Pay g B a

/-- **An address the payload of group `g` reaches by a step**: an uncovered used reference (not
already stored before the group), or the block of a projection record, of an address the payload
reaches. -/
def PayStep (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (Pay : PayloadRel) (g : Nat)
    (x : _root_.Address) : Prop :=
  ∃ a, PayReach t E₀ Pay g a ∧
    ((UsedRef E₀ a x ∧ ¬ AlreadyStoredRole t g x) ∨
      ∃ c, recordOf E₀ a = some c ∧ IsProj c ∧ x = Ix.Cert.ownerOf a c)

/-- **An address the payload reaches is named directly or reached by a step.** -/
theorem payReach_cases {g : Nat} {a : _root_.Address} (h : PayReach t E₀ Pay g a) :
    PayDirect t E₀ Pay g a ∨ PayStep t E₀ Pay g a := by
  cases h with
  | payload hB hp => exact Or.inl ⟨_, Or.inl hB, hp⟩
  | payloadOf hB hp => exact Or.inl ⟨_, Or.inr hB, hp⟩
  | ref ha hu hnc => exact Or.inr ⟨_, ha, Or.inl ⟨hu, hnc⟩⟩
  | owner ha hc hp => exact Or.inr ⟨_, ha, Or.inr ⟨_, hc, hp, rfl⟩⟩

theorem PayDirect.reach {g : Nat} {a : _root_.Address} (h : PayDirect t E₀ Pay g a) :
    PayReach t E₀ Pay g a := by
  obtain ⟨B, hB | hB, hp⟩ := h
  · exact PayReach.payload hB hp
  · exact PayReach.payloadOf hB hp

theorem PayStep.reach {g : Nat} {x : _root_.Address} (h : PayStep t E₀ Pay g x) :
    PayReach t E₀ Pay g x := by
  obtain ⟨a, ha, ⟨hu, hnc⟩ | ⟨c, hc, hp, rfl⟩⟩ := h
  · exact PayReach.ref ha hu hnc
  · exact PayReach.owner ha hc hp

/-- **The payload's facts at the addresses `S` selects** (the fields of `PayloadFacts`, with
`S g a` in place of `PayReach t E₀ Pay g a`). -/
structure PayloadFactsOn (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (Pay : PayloadRel)
    (S : Nat → _root_.Address → Prop) : Prop where
  record : ∀ g a, S g a → ∃ c, recordOf E₀ a = some c
  blockMembers : ∀ g B c ms, S g B → recordOf E₀ B = some c → c.info = .muts ms →
    ∀ i m, ms[i]? = some m →
      recordOf E₀ (memberAddr B i m) = some (memberProjection B i m) ∧
      ∀ ind j, m = .indc ind → j < ind.ctors.size →
        recordOf E₀ (ctorAddr B i j) = some (constructorProjection B i j)
  projMember : ∀ g a c, S g a → recordOf E₀ a = some c → IsProj c →
    ∃ cb, recordOf E₀ (Ix.Cert.ownerOf a c) = some cb ∧ ConstAddrOf (Ix.Cert.ownerOf a c) cb a
  logic : ∀ g a c, S g a → recordOf E₀ a = some c → InLogic c
  notAxiomLike : ∀ g a c, S g a →
    New (groupStore t E₀ Pay g) (groupStore t E₀ Pay (g + 1)) a → recordOf E₀ a = some c →
    ¬ IsAxiomLike c

/-- **The payload's facts from the facts at the direct addresses and at the stepped ones.** -/
theorem payloadFacts_of_on (hd : PayloadFactsOn t E₀ Pay (PayDirect t E₀ Pay))
    (hs : PayloadFactsOn t E₀ Pay (PayStep t E₀ Pay)) : PayloadFacts t E₀ Pay where
  record := fun g a h => (payReach_cases h).elim (hd.record g a) (hs.record g a)
  blockMembers := fun g B c ms h =>
    (payReach_cases h).elim (hd.blockMembers g B c ms) (hs.blockMembers g B c ms)
  projMember := fun g a c h =>
    (payReach_cases h).elim (hd.projMember g a c) (hs.projMember g a c)
  logic := fun g a c h => (payReach_cases h).elim (hd.logic g a c) (hs.logic g a c)
  notAxiomLike := fun g a c h =>
    (payReach_cases h).elim (hd.notAxiomLike g a c) (hs.notAxiomLike g a c)

end Split

end IxVM.Refinement.Binding
