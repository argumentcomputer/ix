import IxVMRefinement.Assembly.TypingStore
import IxVMRefinement.Decl.PrefixInv

/-! # What the typing statement's proof continues from

`Facts t G R env` is the internal part of a table witness (`IxVM.Consistency.TableWitness`):
what a typing run's proof reads of the witness's environment `env` beyond the public shape.

* `inv`: the standing invariant of a prefix (`Decl.PrefixInv`) holds of `env` for every
  record store for `R` (`RecordsFor`) and every group limit within `G` (`LimWithin`). The
  store is universally quantified because the witness is built over one run's records and
  read over another's; the limit because a typing run reads the table at its own limit.
* `whole`: a block is stored whole. If `env` stores the key of a projection record's
  address, it stores the key of every member and constructor address of that record's
  block. The block is read off the store, so the clause speaks of the record the store holds
  at the address and of the block it names.

It mentions no run, no call, and no collision. `FactsWith X` adds one more clause `X`, for
what is not settled here (the registry of native families a later recursor is installed
against); the typing skeleton is stated over `FactsWith X` for every `X`.

`facts_empty`: `Facts` holds of the empty environment on the empty group set, for every
well-formed table and every store. It says nothing about the table: no role is in force.

`fabricated_basis` is one closed fact about the group schedule: the roles of the first six
groups whose constants the checker builds are among the nineteen pinned basis roles.
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Typing

open IxVM.Consistency

/-- **The limit is within the groups `G`**: every role in force at `lim` (bound, and of a
group below the limit when there is one) is of a group of `G`. On every group, every limit is
within. -/
def LimWithin (G : Nat → Prop) (t : Ix.Kernel.RoleTable) (lim : Option Nat) : Prop :=
  ∀ r : Ix.Kernel.Role, (t.addressOf? r).isSome = true →
    (∀ n, lim = some n → Ix.SpecDigest.groupOf r < n) → G (Ix.SpecDigest.groupOf r)

theorem limWithin_all (t : Ix.Kernel.RoleTable) (lim : Option Nat) :
    LimWithin (fun _ => True) t lim :=
  fun _ _ _ => trivial

/-- **The block `ms` at `B` is stored**: the key of every member's address and of every
constructor's address is stored. -/
def BlockStored (t : Ix.Kernel.RoleTable) (env : Ix.Kernel.Env .anon) (B : _root_.Address)
    (ms : Array Ixon.MutConst) : Prop :=
  ∀ i m, ms[i]? = some m →
    (env.find? (keyOf t (memberAddr B i m))).isSome = true ∧
    ∀ ind j, m = .indc ind → j < ind.ctors.size →
      (env.find? (keyOf t (ctorAddr B i j))).isSome = true

/-- **What the typing statement's proof continues from** (module docstring). -/
structure Facts (t : Ix.Kernel.RoleTable) (G : Nat → Prop) (R : Ixon.Env)
    (env : Ix.Kernel.Env .anon) : Prop where
  /-- The prefix invariant, for every record store for `R` and every limit within `G`. -/
  inv : ∀ E, RecordsFor R E → ∀ lim, LimWithin G t lim → Decl.PrefixInv.{u} E t lim env
  /-- A block is stored whole. -/
  whole : ∀ E, RecordsFor R E →
    ∀ (a B : _root_.Address) (c cb : Ixon.Constant) (ms : Array Ixon.MutConst),
      (env.find? (keyOf t a)).isSome = true → Ix.Cert.recordAt E a = some c →
      Ix.Cert.ownerOf a c = B → B ≠ a → Ix.Cert.recordAt E B = some cb → cb.info = .muts ms →
      BlockStored t env B ms

/-- `Facts` with one more clause. -/
def FactsWith
    (X : Ix.Kernel.RoleTable → (Nat → Prop) → Ixon.Env → Ix.Kernel.Env .anon → Prop)
    (t : Ix.Kernel.RoleTable) (G : Nat → Prop) (R : Ixon.Env) (env : Ix.Kernel.Env .anon) :
    Prop :=
  Facts.{u} t G R env ∧ X t G R env

/-- **`Facts` holds of the empty environment on the empty group set.** -/
theorem facts_empty {t : Ix.Kernel.RoleTable} (htwf : t.wf = true) (R : Ixon.Env) :
    Facts.{u} t (fun _ => False) R Ix.Kernel.Env.empty where
  inv := by
    intro E hrf lim hlim
    have hnf : ∀ r, ¬ (⟨E, Ix.Kernel.Env.empty, t, lim⟩ : Core.Ctx).inForce r :=
      fun r hf => hlim r hf.1 hf.2
    exact {
      decl := Decl.FullDeclInv.empty
      store := Decl.foldStoreInv_empty
      unresolved := rfl
      tableWf := htwf
      companions := Decl.coreCompanions_of_empty (c := ⟨E, Ix.Kernel.Env.empty, t, lim⟩)
        (fun _ => rfl) hnf
      loads := Decl.storedLoads_of_empty (c := ⟨E, Ix.Kernel.Env.empty, t, lim⟩) hrf.1
        (fun _ => rfl) hnf
      etaStable := Decl.etaStable_empty }
  whole := by
    intro E _ a B c cb ms hst
    have hf : (Ix.Kernel.Env.empty (md := .anon)).find? (keyOf t a) = none := rfl
    rw [hf] at hst
    simp at hst

set_option maxRecDepth 8192 in
/-- **The roles of the first six groups whose constants the checker builds are pinned basis
roles** (decided over the roles). So at a limit within those groups the closing clause of the
load contract about such roles asks only for constants the pinned basis holds. -/
theorem fabricated_basis (r : Ix.Kernel.Role) :
    Core.fabricatedRole r = true → Ix.SpecDigest.groupOf r < 6 →
      r ∈ TableInhabit.basisRoleOrder := by
  cases r <;> decide +kernel

end IxVM.Refinement.Typing
