import IxVMRefinement.Binding.FoldClauseOver
import IxVMRefinement.Binding.NoneFacts
import IxVMRefinement.Binding.ObservedRun

/-! # The binding fold over the fold's clause: the invariant and the steps' interfaces

The binding fold's boundary invariant, restated with the fold's clause in the form that has one
registry before the store (`FoldClauseOver`), and the interfaces of the steps inside one group.

* `BoundaryFacts t G R env`: what the invariant holds beside the public shape and the clause:
  blocks stored whole, the stored operations pinned and of admitted groups, the stored shapes.
  The prefix invariant is not a field: it is read off the clause (`BndOver.inv`). No guard at a
  limit is a field either: the clause's load contract holds the firing of every stored
  projection table, and that names no limit.
* `BndOver L t G R env`: the boundary invariant: `TableShape`, `FoldClauseOver L`,
  `BoundaryFacts`. `OverW L` is the internal part of the table witness it gives.
* `OverUnitStep L t G R envT E₀ A c`: **the step of one closure unit**. From the clause at one
  registry, at every record store for `R` and every carried limit within `G`, to the clause at
  one registry at the grown environment, at every such store and limit. It names no limit: the
  check of a unit of group `g` runs at the group's validation limit, which is one of them. It
  asks nothing about the circuit's dispatch at a store other than the one a run is good for.
* `ClosureStepOver`: the closure of a group.
* `RoleFreeShapes L ρ t g`: **what a group with no role unit owes beyond its closure**: the
  stored shapes below `g + 1`. It is asked only where no role of the group is an operation or a
  standard axiom (the premise is part of the statement), and it has the run: the admission of
  the group, with the validation of each of its roles and the run's records, and the admission's
  reading clause.
* `BeforeRaise L t g R env`: the invariant on the groups up to `g` with the clause still at
  the limits within the groups below `g`, and what the raise past `g` needs of the environment.
* `RoleUnitStepOver P L ρ t g`: **the step of a group whose one role is a role unit**, with the
  admission's reading clause (a reading of the unit's record over the grown store needs the
  run's blobs there), ending before the raise.
* `GroupStepOver L ρ t g`: the step of a group.
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open Ix.Kernel.Semantics (NativeFam)

/-! ## The invariant -/

/-- **What the boundary invariant holds beside the public shape and the fold's clause** (module
docstring). -/
structure BoundaryFacts (t : Ix.Kernel.RoleTable) (G : Nat → Prop) (R : Ixon.Env)
    (env : Ix.Kernel.Env .anon) : Prop where
  /-- A block is stored whole. -/
  whole : ∀ E, RecordsFor R E →
    ∀ (a B : _root_.Address) (c cb : Ixon.Constant) (ms : Array Ixon.MutConst),
      (env.find? (keyOf t a)).isSome = true → Ix.Cert.recordAt E a = some c →
      Ix.Cert.ownerOf a c = B → B ≠ a → Ix.Cert.recordAt E B = some cb → cb.info = .muts ms →
      BlockStored t env B ms
  /-- Every stored operation is stored as pinned. -/
  opsPinned : RoleOps.OpsPinned env
  /-- An operation is stored only once its group is admitted. -/
  opsAdmitted : ∀ r ∈ RoleOps.opRoles, (env.find? (Ix.Kernel.Key.role r)).isSome = true →
    G (Ix.SpecDigest.groupOf r)
  /-- The stored shapes later groups read. -/
  shapes : Shapes G env

/-- **The boundary invariant over the fold's clause** on the admitted groups `G`: the public
shape, the clause at every record store for `R` and every carried limit within `G` with one
registry, and the facts beside them. -/
structure BndOver (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop)
    (t : Ix.Kernel.RoleTable) (G : Nat → Prop) (R : Ixon.Env) (env : Ix.Kernel.Env .anon) :
    Prop where
  shape : TableShape.{u} t G R env
  clause : FoldClauseOver.{u} L t G R env
  facts : BoundaryFacts t G R env

/-- **The internal part of the table witness the two halves share**: the facts beside the
clause, and the clause. -/
abbrev OverW (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop) (t : Ix.Kernel.RoleTable)
    (G : Nat → Prop) (R : Ixon.Env) (env : Ix.Kernel.Env .anon) : Prop :=
  BoundaryFacts t G R env ∧ FoldClauseOver.{u} L t G R env

section Invariant

variable {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop} {t : Ix.Kernel.RoleTable}
  {G : Nat → Prop} {R : Ixon.Env} {env : Ix.Kernel.Env .anon}

/-- **The prefix invariant at every record store and every carried limit within the groups**,
read off the clause. -/
theorem BndOver.inv (h : BndOver.{u} L t G R env) {E : Ixon.Env} (hE : RecordsFor R E)
    {lim : Option Nat} (hc : Carried lim) (hl : LimWithin G t lim) :
    Decl.PrefixInv.{u} E t lim env := by
  obtain ⟨Reg, hR⟩ := h.clause
  exact (hR E hE lim hc hl).prefixInv

/-- The invariant with the clause as its extra part gives the invariant over the clause. -/
theorem BndOver.of_bnd (h : Bnd.{u} (FoldClauseOver.{u} L) t G R env) :
    BndOver.{u} L t G R env :=
  ⟨h.shape, h.extra, ⟨h.facts.whole, h.facts.opsPinned, h.facts.opsAdmitted, h.facts.shapes⟩⟩

theorem BndOver.witness (h : BndOver.{u} L t G R env) :
    TableWitness.{u} (OverW.{u} L) t G R env :=
  ⟨h.shape, h.facts, h.clause⟩

theorem BndOver.of_witness (h : TableWitness.{u} (OverW.{u} L) t G R env) :
    BndOver.{u} L t G R env :=
  ⟨h.shape, h.facts.2, h.facts.1⟩

/-- **The invariant depends on the store only through its entries.** -/
theorem bndOver_storeCongr {R' : Ixon.Env} (hc : ∀ a, R.consts.get? a = R'.consts.get? a)
    (hb : ∀ a, R.blobs.get? a = R'.blobs.get? a) (h : BndOver.{u} L t G R env) :
    BndOver.{u} L t G R' env := by
  have hback : ∀ E, RecordsFor R' E → RecordsFor R E := fun E hE =>
    recordsFor_storeCongr (fun a => (hc a).symm) (fun a => (hb a).symm) hE
  obtain ⟨Reg, hR⟩ := h.clause
  exact ⟨tableShape_storeCongr hc hb h.shape, ⟨Reg, fun E hE => hR E (hback E hE)⟩,
    ⟨fun E hE => h.facts.whole E (hback E hE), h.facts.opsPinned, h.facts.opsAdmitted,
      h.facts.shapes⟩⟩

end Invariant

/-! ## The step of one closure unit -/

/-- **The step of one closure unit, over the fold's clause** (module docstring). At every
environment that extends `envT`, has distinct names, satisfies the clause with one registry
`Reg` at every record store for `R` and every carried limit within `G`, stores every used
reference of the record that is not its own constant address (unless the reference is no
in-logic constant address of the run's store), and stores none of the record's constant
addresses: there are fresh constants `new` with distinct names, none at an operation's key, and
one registry `Reg'`, such that the clause holds with `Reg'` at `new ++ env`, at every record
store for `R` and every carried limit within `G`; at each constant address of the record `new`
holds a constant at that address's key that stores a reading of the address over the run's
records; and every other constant of `new` is at a derived key. -/
def OverUnitStep (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop) (t : Ix.Kernel.RoleTable)
    (G : Nat → Prop) (R : Ixon.Env) (envT : Ix.Kernel.Env .anon) (E₀ : Ixon.Env)
    (A : _root_.Address) (c : Ixon.Constant) : Prop :=
  ∀ (env : Ix.Kernel.Env .anon) (Reg : NativeFam .anon → Prop),
    (∀ ci ∈ envT.consts, ci ∈ env.consts) → (env.consts.map (·.name)).Nodup →
    (∀ E, RecordsFor R E → ∀ lim, Carried lim → LimWithin G t lim →
      FoldClauseWith.{u} L t E lim env Reg) →
    (∀ x, UsedRef E₀ A x →
      (env.find? (keyOf t x)).isSome = true ∨ ConstAddrOf A c x ∨ ¬ NeedOk E₀ x) →
    (∀ x, ConstAddrOf A c x → env.find? (keyOf t x) = none) →
    ∃ (new : List (Ix.Kernel.ConstantInfo .anon)) (Reg' : NativeFam .anon → Prop),
      (new.map (·.name)).Nodup ∧ (∀ ci ∈ new, env.find? ci.name = none) ∧
      (∀ E, RecordsFor R E → ∀ lim, Carried lim → LimWithin G t lim →
        FoldClauseWith.{u} L t E lim ⟨new ++ env.consts⟩ Reg') ∧
      (∀ ci ∈ new, ci.name ∉ RoleOps.opNames) ∧
      (∀ x, ConstAddrOf A c x →
        ∃ ci ∈ new, ∃ ci₀, ci.name = keyOf t x ∧ Reads t E₀ x ci₀ ∧ StoredAs ci ci₀) ∧
      (∀ ci ∈ new, (∃ x, ConstAddrOf A c x ∧ ci.name = keyOf t x) ∨ ∃ k s, ci.name = .aux k s) ∧
      Ix.Kernel.EnvExt env ⟨new ++ env.consts⟩

/-! ## The parts of a group's step -/

/-- **The closure of group `g`**: from the invariant below `g` at `R`, `env`, the admission of
`g` and its reading clause, a store `R₁` between `R` and `R'` that lacks only role-unit records
and holds every blob of `R'`, and a grown environment with the invariant below `g` at `R₁` and
the group's roles that are no role unit stored as their records declare them. -/
def ClosureStepOver (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop) (ρ : BRun)
    (t : Ix.Kernel.RoleTable) (g : Nat) : Prop :=
  ∀ (R R' : Ixon.Env) (env : Ix.Kernel.Env .anon),
    BndOver.{u} L t (· < g) R env → Admits ρ t g R R' → AdmitsReads ρ t R R' →
    ∃ (R₁ : Ixon.Env) (env₁ : Ix.Kernel.Env .anon),
      StoreLe R R₁ ∧ StoreLe R₁ R' ∧
      (∀ x b, R'.blobs.get? x = some b → R₁.blobs.get? x = some b) ∧
      (∀ a, (R'.consts.get? a).isSome = true → R₁.consts.get? a = none → RoleUnitAt t g a) ∧
      (∀ ci ∈ env.consts, ci ∈ env₁.consts) ∧
      BndOver.{u} L t (· < g) R₁ env₁ ∧ GroupKept t g R₁ env₁ ∧
      (∀ x c, recordOf R₁ x = some c → (∀ ms, c.info ≠ .muts ms) →
        (env₁.find? (keyOf t x)).isSome = true)

/-- **The stored shapes after the closure of a group with no role unit** (module docstring).
Where no role of `g` is an operation or a standard axiom: from the admission of `g` by the run
(with the validation of each role of `g` and `R' ⊆ ρ.E₀`), its reading clause, a store `R₁`
within `R'` and an environment with the invariant below `g`, the group's roles stored as
their records declare them, and every non-block record of `R'` stored, the stored shapes
below `g + 1`. -/
def RoleFreeShapes (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop) (ρ : BRun)
    (t : Ix.Kernel.RoleTable) (g : Nat) : Prop :=
  (∀ r ∈ roleGroup g, ¬ (r ∈ RoleOps.opRoles ∨ r ∈ standardAxioms)) →
  ∀ (R R₁ R' : Ixon.Env) (env₁ : Ix.Kernel.Env .anon),
    Admits ρ t g R R' → AdmitsReads ρ t R R' → StoreLe R₁ R' →
    BndOver.{u} L t (· < g) R₁ env₁ → GroupKept t g R₁ env₁ →
    (∀ x c, recordOf R' x = some c → (∀ ms, c.info ≠ .muts ms) →
      (env₁.find? (keyOf t x)).isSome = true) →
      Shapes (· < g + 1) env₁

/-- **The invariant on the groups up to `g`, before the raise past `g`**: the public shape and
the facts beside the clause on the groups below `g + 1`, the clause at the limits within the
groups below `g`, and what the raise past `g` needs of the environment. -/
structure BeforeRaise (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop)
    (t : Ix.Kernel.RoleTable) (g : Nat) (R : Ixon.Env) (env : Ix.Kernel.Env .anon) : Prop where
  shape : TableShape.{u} t (· < g + 1) R env
  clause : FoldClauseOver.{u} L t (· < g) R env
  facts : BoundaryFacts t (· < g + 1) R env
  raise : RaiseAt t env g

/-- **The step of a group whose one role is a role unit** (module docstring); `P` is membership
in the operations or in the standard axioms. From the admission of `g` and its reading clause,
the invariant below `g` at the closure's store and environment, and the record added at the
role's address: a grown environment at the invariant before the raise past `g`. -/
def RoleUnitStepOver (P : Ix.Kernel.Role → Prop)
    (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop) (ρ : BRun) (t : Ix.Kernel.RoleTable)
    (g : Nat) : Prop :=
  ∀ (r : Ix.Kernel.Role) (a : _root_.Address) (R R₁ R' : Ixon.Env) (env₁ : Ix.Kernel.Env .anon),
    roleGroup g = [r] → P r → t.addressOf? r = some a → Admits ρ t g R R' →
    AdmitsReads ρ t R R' → BndOver.{u} L t (· < g) R₁ env₁ → AddsAt R₁ R' a →
    ∃ env' : Ix.Kernel.Env .anon, (∀ ci ∈ env₁.consts, ci ∈ env'.consts) ∧
      BeforeRaise.{u} L t g R' env'

/-- **The step of group `g`**: from the invariant below `g`, the admission of `g` and its
reading clause, the invariant below `g + 1` at the grown store and an environment that extends
the earlier one. -/
def GroupStepOver (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop) (ρ : BRun)
    (t : Ix.Kernel.RoleTable) (g : Nat) : Prop :=
  ∀ (R R' : Ixon.Env) (env : Ix.Kernel.Env .anon),
    BndOver.{u} L t (· < g) R env → Admits ρ t g R R' → AdmitsReads ρ t R R' →
      ∃ env' : Ix.Kernel.Env .anon, (∀ ci ∈ env.consts, ci ∈ env'.consts) ∧
        BndOver.{u} L t (· < g + 1) R' env'

end IxVM.Refinement.Binding
