import IxVMRefinement.Assembly.TypingDefnStep
import IxVMRefinement.Claim.RoleTable

/-! # The key of an address a valid table's environment does not store is free

A unit's step stores its constants at the keys of the record's constant addresses, and the
declaration judgment refuses three lists of keys (`Decl.KeyFree`): the reserved basis names,
the accelerated `Nat` operations and the division certificates' names. Every key of those lists
is the key of a role whose constant a valid table's environment stores: a walked role
(`covered_stored`) or a role of the quotient package (`standing_stored`). So the key of an
address that the environment does not store is free, whether or not the table binds a role to
the address (`keyFree_of_not_stored`; `keyFree_keyOf_of_unbound` is the unbound case).

The skeleton asks a unit's step only at environments that extend the witness's and store none
of the record's constant addresses (`UnitStep`), so the witness's environment stores none of
them, and their keys are free.
-/

universe u

namespace IxVM.Refinement.Typing

open IxVM.Consistency

/-- A role whose constant a valid table's environment stores at the role's key, by
`covered_stored` or `standing_stored`. -/
private def roleStored (r : Ix.Kernel.Role) : Bool :=
  walkedRole r || decide (r ∈ standingRoles)

private def storedRoleKey : Ix.Kernel.Key .anon → Bool
  | .role r => roleStored r
  | _ => false

private theorem contains_role_false :
    ∀ (L : List (Ix.Kernel.Key .anon)), L.all storedRoleKey = true →
      ∀ {r : Ix.Kernel.Role}, roleStored r = false → L.contains (.role r) = false
  | [], _, _, _ => rfl
  | x :: xs, hall, r, hr => by
    simp only [List.all_cons, Bool.and_eq_true] at hall
    simp only [List.contains, List.elem]
    cases hbeq : ((Ix.Kernel.Key.role r : Ix.Kernel.Key .anon) == x) with
    | true =>
      have hk : (Ix.Kernel.Key.role r : Ix.Kernel.Key .anon) = x := beq_iff_eq.mp hbeq
      subst hk
      have h1 : roleStored r = true := hall.1
      rw [hr] at h1
      cases h1
    | false => exact contains_role_false xs hall.2 hr

set_option maxRecDepth 100000 in
private theorem reservedBasisNames_stored :
    (Ix.Kernel.reservedBasisNames : List (Ix.Kernel.Key .anon)).all storedRoleKey = true := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem natOpNames_stored :
    (Ix.Kernel.natOpNames : List (Ix.Kernel.Key .anon)).all storedRoleKey = true := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem natDivModNames_stored :
    (Ix.Kernel.natDivModNames : List (Ix.Kernel.Key .anon)).all storedRoleKey = true := by
  decide +kernel

/-- **The key of an address that a valid table's environment does not store is free**
(module docstring). -/
theorem keyFree_of_not_stored {t : Ix.Kernel.RoleTable} {R : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} (hshape : TableShape.{u} t (fun _ => True) R envT)
    (ht : t.check = .ok ()) {a : _root_.Address} (hns : ¬ StoredAt t envT a) :
    Decl.KeyFree (keyOf t a) := by
  have htwf : t.wf = true := by
    unfold Ix.Kernel.RoleTable.wf
    rw [ht]
    rfl
  rcases keyOf_cases t a with ⟨hk, -⟩ | ⟨r, hr, hk⟩
  · rw [hk]
    exact keyFree_id a
  · have ha : t.addressOf? r = some a := Claim.addressOf_eq_some_of_mem_bound ht hr
    rw [hk]
    cases hb : roleStored r with
    | false =>
      exact ⟨contains_role_false _ reservedBasisNames_stored hb,
        contains_role_false _ natOpNames_stored hb,
        contains_role_false _ natDivModNames_stored hb⟩
    | true =>
      unfold roleStored at hb
      cases hw : walkedRole r with
      | true =>
        have hcov : Covered t a := ⟨r, ha, hw⟩
        exact absurd (covered_stored hshape htwf hcov) hns
      | false =>
        rw [hw] at hb
        have hs : decide (r ∈ standingRoles) = true := hb
        exact absurd (standing_stored hshape htwf (of_decide_eq_true hs) ha) hns

end IxVM.Refinement.Typing
