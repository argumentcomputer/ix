import IxVMRefinement.Assembly.PointTable

/-! # Literal-function keys are already stored before a typing install

The full table shape used by a typing unit keeps the literal-function roles. A fresh block
member therefore cannot acquire one of these keys. This argument is specific to the typing
prefix; a partially admitted binding prefix does not supply the full table shape.
-/

namespace IxVM.Refinement.Typing

open IxVM.Consistency

universe u

/-- A fresh input address is distinct from every role that the full table already stores. -/
theorem fresh_key_ne_storedRole {t : Ix.Kernel.RoleTable} (hwf : t.wf = true)
    {R : Ixon.Env} {envT env : Ix.Kernel.Env .anon}
    (shape : TableShape.{u} t (fun _ => True) R envT)
    (prefixExtension : ∀ ci ∈ envT.consts, ci ∈ env.consts)
    (distinct : (env.consts.map (·.name)).Nodup)
    {address : _root_.Address} (fresh : env.find? (Core.keyOf t address) = none)
    {role : Ix.Kernel.Role} (stored : StoredRole role) :
    Core.keyOf t address ≠ .role role := by
  intro equal
  have bound := Core.addressOf_of_keyOf hwf equal
  obtain ⟨constant, found⟩ := storedRole_find shape stored bound
  have foundHere := find_of_ext prefixExtension distinct found
  rw [← equal, fresh] at foundHere
  cases foundHere

/-- The four literal-function names needed by alias constructor classification are excluded
by actual full-table storage and the freshness supplied to a typing unit. -/
theorem alias_literal_keys_distinct {t : Ix.Kernel.RoleTable} (hwf : t.wf = true)
    {R : Ixon.Env} {envT env : Ix.Kernel.Env .anon}
    (shape : TableShape.{u} t (fun _ => True) R envT)
    (prefixExtension : ∀ ci ∈ envT.consts, ci ∈ env.consts)
    (distinct : (env.consts.map (·.name)).Nodup)
    {address : _root_.Address} (fresh : env.find? (Core.keyOf t address) = none) :
    Core.keyOf t address ≠ Ix.Kernel.stringOfListName ∧
    Core.keyOf t address ≠ Ix.Kernel.listNilName ∧
    Core.keyOf t address ≠ Ix.Kernel.listConsName ∧
    Core.keyOf t address ≠ Ix.Kernel.charOfNatName := by
  exact ⟨fresh_key_ne_storedRole hwf shape prefixExtension distinct fresh (by decide +kernel),
    fresh_key_ne_storedRole hwf shape prefixExtension distinct fresh (by decide +kernel),
    fresh_key_ne_storedRole hwf shape prefixExtension distinct fresh (by decide +kernel),
    fresh_key_ne_storedRole hwf shape prefixExtension distinct fresh (by decide +kernel)⟩

end IxVM.Refinement.Typing
