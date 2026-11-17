import IxVMRefinement.Binding.Carried

/-! # The steps inside one group of the binding fold: interfaces

`StepCore` at group `g` is taken in three parts: the closure of `g` (every new record that is
no role unit, installed in rank order), the role unit of `g` by kind (none, an operation, a
standard axiom), and the raise of the prefix invariant to the next group's top limit
(`Raise.lean`). This file states what one closure unit's step must give (`BUnitStep`) and what
the fold reads of a group's admission beyond `Admits` (`AdmitsReads`).

`BUnitStep` differs from the typing skeleton's `UnitStep` in what it says of the record store:
the binding invariant quantifies over every record store for the fold's store `R` (`BFacts`), and
one environment must serve every such store. So the new constants are chosen once, and the
prefix invariant and the projection guard are carried to every store for `R` and every limit,
the extra clause to every store for `R`. This is the form `Decl.walkedConst_step` gives (its
transport is for every store at which the record reloads, and every limit).

`AdmitsReads` is what the closure needs to read the new records over the fold's own store:
every blob the run loaded is held (the reload of a record at a store for `R` asks for the run's
blobs), and a reading over the run's records of a constant address of a new unit is a reading
over `R'` (locality of the reader: the walk loads the records a reading looks up).
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing

/-- **The step of one closure unit, in the binding fold** (module docstring). At every
environment that extends `envT`, has distinct names, satisfies the prefix invariant at the check's
limit `n`, the guard at every limit and the extra clause `Y` for every record store for `R`,
stores every used reference of the record that is not its own constant address (unless the
reference is no in-logic constant address of the run's store), and stores none of the record's
constant addresses: there are fresh constants `new` with distinct names, none at an operation's
key, such that for every record store for `R`, the prefix invariant at every limit is carried to
`new ++ env` given the guard there, the guard at every limit holds there, and so does `Y`; at
each constant address of the record `new` holds a constant at that address's key that stores a
reading of the address over the run's records; and every other constant of `new` is at a
derived key. -/
def BUnitStep (Y : Ixon.Env → Ix.Kernel.Env .anon → Prop) (t : Ix.Kernel.RoleTable)
    (R : Ixon.Env) (envT : Ix.Kernel.Env .anon) (E₀ : Ixon.Env) (n : Nat)
    (A : _root_.Address) (c : Ixon.Constant) : Prop :=
  ∀ env : Ix.Kernel.Env .anon,
    (∀ ci ∈ envT.consts, ci ∈ env.consts) → (env.consts.map (·.name)).Nodup →
    (∀ E, RecordsFor R E → Decl.PrefixInv.{u} E t (some n) env) →
    (∀ E, RecordsFor R E → ∀ lim, GuardAt E t lim env) →
    (∀ E, RecordsFor R E → Y E env) →
    (∀ x, UsedRef E₀ A x →
      (env.find? (keyOf t x)).isSome = true ∨ ConstAddrOf A c x ∨ ¬ NeedOk E₀ x) →
    (∀ x, ConstAddrOf A c x → env.find? (keyOf t x) = none) →
    ∃ new : List (Ix.Kernel.ConstantInfo .anon),
      (new.map (·.name)).Nodup ∧ (∀ ci ∈ new, env.find? ci.name = none) ∧
      (∀ E, RecordsFor R E → ∀ lim, Decl.PrefixInv.{u} E t lim env →
        GuardAt E t lim ⟨new ++ env.consts⟩ → Decl.PrefixInv.{u} E t lim ⟨new ++ env.consts⟩) ∧
      (∀ E, RecordsFor R E → ∀ lim, GuardAt E t lim ⟨new ++ env.consts⟩) ∧
      (∀ E, RecordsFor R E → Y E ⟨new ++ env.consts⟩) ∧
      (∀ ci ∈ new, ci.name ∉ RoleOps.opNames) ∧
      (∀ x, ConstAddrOf A c x →
        ∃ ci ∈ new, ∃ ci₀, ci.name = keyOf t x ∧ Reads t E₀ x ci₀ ∧ StoredAs ci ci₀) ∧
      ∀ ci ∈ new, (∃ x, ConstAddrOf A c x ∧ ci.name = keyOf t x) ∨ ∃ k s, ci.name = .aux k s

/-- **What the closure reads of a group's admission beyond `Admits`** (module docstring):
`R'` holds every blob the run loaded, and a reading over the run's records of a constant
address of a new record is a reading over `R'`. -/
structure AdmitsReads (ρ : BRun) (t : Ix.Kernel.RoleTable) (R R' : Ixon.Env) : Prop where
  blobs : ∀ x b, ρ.E₀.blobs.get? x = some b → R'.blobs.get? x = some b
  reads : ∀ A c x ci₀, New R R' A → recordOf R' A = some c → ConstAddrOf A c x →
    Reads t ρ.E₀ x ci₀ → Reads t R' x ci₀

end IxVM.Refinement.Binding
