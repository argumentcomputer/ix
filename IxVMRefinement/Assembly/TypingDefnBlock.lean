import IxVMRefinement.Assembly.TypingDefnStep

/-! # Blocks of definitions

A unit is one record; a block of definitions is one unit (`DefnBlock`: every member is a
definition, theorem or opaque constant), and its step installs the block's members one at a
time, in the members' index order. This module holds what that step reads of the block beside
the members' checks:

* distinct members of a block the run's store holds have distinct constant addresses
  (`memberAddr_inj`: their projection records differ in the index), and keys identify
  addresses, so a member's key is fresh at the prefix that holds the members before it;
* the references the block uses, stored at the step's environment, are stored at every longer
  prefix (`usedRefsStored_append`).

The step itself is `valueUnitStep_defnBlock` (`Assembly/ValueUnitStep.lean`), stated once for
the typing fold and the binding fold. `MembersDone` is the state of the step for an arbitrary
clause after the first members (`unitStep_defnBlockJ`, `Assembly/LateValueStep.lean`).
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Typing

open IxVM.Consistency
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open Ix.Kernel (ConstantInfo)

/-- **A block of definitions**: every member is a definition. -/
def DefnBlock (ms : Array Ixon.MutConst) : Prop :=
  ∀ (i : Nat) (m : Ixon.MutConst), ms[i]? = some m → ∃ d : Ixon.Definition, m = .defn d

private theorem toUInt64_toNat_b {n : Nat} (hn : n < UInt64.size) : n.toUInt64.toNat = n := by
  change (UInt64.ofNat n).toNat = n
  rw [UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt hn

/-- Two definition members' projection records of one block are equal only at one index. -/
theorem memberIdx_eq {B : _root_.Address} {i j : Nat} {di dj : Ixon.Definition}
    (hi : i < UInt64.size) (hj : j < UInt64.size)
    (h : memberProjection B i (.defn di) = memberProjection B j (.defn dj)) : i = j := by
  have h1 : (memberProjection B i (.defn di)).info = .dPrj ⟨i.toUInt64, B⟩ := rfl
  have h2 : (memberProjection B j (.defn dj)).info = .dPrj ⟨j.toUInt64, B⟩ := rfl
  rw [h, h2] at h1
  injection h1 with h3
  injection h3 with h4
  have h5 := congrArg UInt64.toNat h4
  rw [toUInt64_toNat_b hj, toUInt64_toNat_b hi] at h5
  exact h5.symm

/-- **Distinct definition members of a block the store holds have distinct constant
addresses**: the store holds each member's projection record at its address. -/
theorem memberAddr_inj {E₀ : Ixon.Env} {B : _root_.Address} {i j : Nat}
    {di dj : Ixon.Definition} (hi : i < UInt64.size) (hj : j < UInt64.size)
    (hri : Ix.Cert.recordAt E₀ (memberAddr B i (.defn di)) =
      some (memberProjection B i (.defn di)))
    (hrj : Ix.Cert.recordAt E₀ (memberAddr B j (.defn dj)) =
      some (memberProjection B j (.defn dj)))
    (h : memberAddr B i (.defn di) = memberAddr B j (.defn dj)) : i = j := by
  rw [h, hrj] at hri
  exact memberIdx_eq hi hj (Option.some.inj hri).symm

/-- The references a record uses, stored at an environment, are stored at every longer
prefix. -/
theorem usedRefsStored_append {t : Ix.Kernel.RoleTable} {env : Ix.Kernel.Env .anon}
    {c : Ixon.Constant} (h : Decl.UsedRefsStored t env c) :
    ∀ acc : List (ConstantInfo .anon), Decl.UsedRefsStored t ⟨acc ++ env.consts⟩ c := by
  intro acc
  induction acc with
  | nil => exact h
  | cons cn acc ih => exact LoadedReads.usedRefsStored_cons cn ih

/-- **The members `0, …, m - 1` installed**, in index order, at the front of `env`: the
installed constants `acc` have distinct fresh keys, the prefix keeps the invariant and the
extra clause, each of the members has a constant storing a reading of its address, and each
installed constant is at the key of one of them. -/
structure MembersDone (X : Ix.Kernel.Env .anon → Prop) (t : Ix.Kernel.RoleTable)
    (E₀ E : Ixon.Env) (lim : Option Nat) (env : Ix.Kernel.Env .anon) (B : _root_.Address)
    (ms : Array Ixon.MutConst) (m : Nat) (acc : List (ConstantInfo .anon)) : Prop where
  nodup : (acc.map (·.name)).Nodup
  fresh : ∀ ci ∈ acc, env.find? ci.name = none
  inv : Decl.PrefixInv.{u} E t lim ⟨acc ++ env.consts⟩
  extra : X ⟨acc ++ env.consts⟩
  done : ∀ i mi, i < m → ms[i]? = some mi → ∃ ci ∈ acc, ∃ ci₀,
    ci.name = keyOf t (memberAddr B i mi) ∧ Reads t E₀ (memberAddr B i mi) ci₀ ∧
      StoredAs ci ci₀
  named : ∀ ci ∈ acc, ∃ i mi, i < m ∧ ms[i]? = some mi ∧ ci.name = keyOf t (memberAddr B i mi)

end IxVM.Refinement.Typing
