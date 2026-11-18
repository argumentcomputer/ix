import IxVMRefinement.Assembly.TypingSkeleton
import IxVMRefinement.RoleOps.All
import IxVMRefinement.RoleOps.Schedule
import IxVMRefinement.RoleVal.GroupAdmit

/-! # The binding fold: the boundary invariant, one group's admission, and the step

The proof of the binding half (`IxVM.Consistency.BindingSpecOn`) folds over the validation
groups in order. Before group `g` the groups below it have been admitted; their records are
in a store `R` and their constants in an environment `env`. This file states what holds there,
what a run's admission of one group establishes, and the step from one to the next.

* `Carried lim`: a limit a role context carries. A validation of group `h` runs under
  `Mk(tbl, groupValLimit h, _)`, a typing claim that validates its table under
  `Mk(tbl, 77, _)`, one that assumes it under `Assumed` (no limit). No context carries the
  limits 34 to 40 or 42 to 45: the well-founded block is validated at 33 and the literal
  support at 41.
* `BFacts t G R env`: the internal part of the invariant. The prefix invariant at every
  carried limit within `G` and every record store for `R` (`inv`); blocks stored whole
  (`whole`); every stored operation stored as
  pinned (`opsPinned`) and only for an admitted group (`opsAdmitted`); and the stored shapes the
  later groups read (`shapes`: `Bool` and its constructors for the operations, the seven
  literal-support types for the literal rule, `Iff` and `Nonempty` for the standard axioms).
* `Bnd X t G R env`: the boundary invariant: `TableShape` on `G`, `BFacts`, and an extra
  clause `X` (the registry of native families a later recursor is installed against; the
  typing statement's proof is stated over `FactsWith X`).
* `BRun`: what the fold reads of a binding run: the records it loaded, a rank per group, and
  two abstract predicates, the check of a record at a limit and the validation of a role in its
  group. The claim layer instantiates them.
* `Admits ρ t g R R'`: what the run's admission of group `g` establishes about the store: `R'`
  is `R` and the records walked for `g`, all loaded by the run, with the store clauses of
  `TableShape`; every new record is reached through used references of smaller rank or stored
  ones; every new unit is checked at `groupValLimit g`; the group's roles are validated and
  their kept records are in `R'`; no new record is an operation's other than the group's
  own; and `R'` holds the records the proofs in the evidence of the group's roles use.
* `StepCore X ρ t G g`: the step on any needs-closed `G` holding the group of every bound role
  in force at `groupValLimit g`: from `Bnd` on `G` and `Admits` to `Bnd` on `G` and `g`.
  `StepInstance` is one step taken at concrete data, for non-vacuity.

The firing of the stored projection tables is inside the prefix invariant's load contract and
names no limit (`Core.ProjTablesFire`), so the invariant is carried at the carried limits only
and a limit is lowered with no further input (`Raise.lean`).
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)

/-! ## Limits -/

/-- The validation limit of group `g` (`KernelRoles::group_validation_limit`). -/
abbrev valLimit (g : Nat) : Nat := RoleVal.groupValLimit g

/-- **A limit a role context carries**: none (an assuming context), the group count (a
validating typing claim), or the validation limit of a group. -/
def Carried (lim : Option Nat) : Prop :=
  lim = none ∨ lim = some 77 ∨ ∃ h, lim = some (RoleVal.groupValLimit h)

theorem carried_valLimit (g : Nat) : Carried (some (valLimit g)) :=
  Or.inr (Or.inr ⟨g, rfl⟩)

/-- A group's validation limit is at most the group. -/
theorem valLimit_le (g : Nat) : valLimit g ≤ g := by
  show RoleVal.groupValLimit g ≤ g
  unfold RoleVal.groupValLimit
  split
  · exact Nat.le_refl g
  · split
    · omega
    · split <;> omega

/-- **The roles in force at a group's validation limit are of earlier groups**: the limit is
within the groups below `g`. -/
theorem limWithin_below (t : Ix.Kernel.RoleTable) (g : Nat) :
    LimWithin (· < g) t (some (valLimit g)) :=
  fun _ _ hr => Nat.lt_of_lt_of_le (hr _ rfl) (valLimit_le g)

/-! ## The roles that resolve -/

section RoleRes

/-- **Every fabricated role in force resolves**: the `roleRes` field of
`Core.ScopedLoadFacts`, stated alone. -/
def RoleResAt (c : Core.ScopedCtx) : Prop :=
  ∀ (r : Ix.Kernel.Role) (a : _root_.Address), c.inForce r → Core.fabricatedRole r = true →
    c.t.addressOf? r = some a → c.κ a ≠ Core.unresolvedKey

theorem roleResAt_of_loads {c : Core.ScopedCtx} (h : Core.ScopedLoadFacts c) : RoleResAt c :=
  h.roleRes

end RoleRes

/-! ## Stored shapes -/

/-- **`Iff` is stored as the `propext` check reads it**: for every axiom value named and shaped
as the `propext` pin, `stdAxiomOk` holds (its environment part: the pinned `Eq`, and `Iff`,
`Iff.intro`, `Iff.rec` matching their pins). -/
def IffPinned (env : Ix.Kernel.Env .anon) : Prop :=
  ∀ cvA : Ix.Kernel.ConstantVal .anon, cvA.name = Ix.Kernel.propextName →
    Ix.Kernel.ConstantVal.matchesPin cvA Ix.Kernel.propextA = true →
    Ix.Kernel.stdAxiomOk env cvA = true

/-- **`Nonempty` is stored as the `Classical.choice` check reads it**. -/
def NonemptyPinned (env : Ix.Kernel.Env .anon) : Prop :=
  ∀ cvA : Ix.Kernel.ConstantVal .anon, cvA.name = Ix.Kernel.choiceName →
    Ix.Kernel.ConstantVal.matchesPin cvA Ix.Kernel.choiceA = true →
    Ix.Kernel.stdAxiomOk env cvA = true

/-- **The stored shapes later groups read**, at the admitted groups `G`: `Bool` and its
constructors (the comparisons' and well-founded operations' guards), the seven types of the
literal support (`strLitSupported`, once all five literal groups are in), `Iff` and `Nonempty`
(the standard axioms' check). -/
structure Shapes (G : Nat → Prop) (env : Ix.Kernel.Env .anon) : Prop where
  bool : G (Ix.SpecDigest.groupOf .bool) →
    RoleOps.BoolPinned env ∧ RoleOps.BoolCtorsStored env ∧ RoleOps.BoolCtorsTyped env
  char : G (Ix.SpecDigest.groupOf .char) → Ix.Kernel.charTyOk (env.find? Ix.Kernel.charName) = true
  string : G (Ix.SpecDigest.groupOf .string) →
    Ix.Kernel.stringTyOk (env.find? Ix.Kernel.stringName) = true
  list : G (Ix.SpecDigest.groupOf .list) →
    Ix.Kernel.listTyOk (env.find? Ix.Kernel.listName) = true ∧
    Ix.Kernel.listNilTyOk (env.find? Ix.Kernel.listNilName) = true ∧
    Ix.Kernel.listConsTyOk (env.find? Ix.Kernel.listConsName) = true
  charOfNat : G (Ix.SpecDigest.groupOf .charOfNat) →
    Ix.Kernel.charOfNatTyOk (env.find? Ix.Kernel.charOfNatName) = true
  stringOfList : G (Ix.SpecDigest.groupOf .stringOfList) →
    Ix.Kernel.stringOfListTyOk (env.find? Ix.Kernel.stringOfListName) = true
  iff : G (Ix.SpecDigest.groupOf .iff) → IffPinned env
  nonempty : G (Ix.SpecDigest.groupOf .nonempty) → NonemptyPinned env

/-! ## The boundary invariant -/

/-- **The internal part of the boundary invariant** on the admitted groups `G` (module
docstring). -/
structure BFacts (t : Ix.Kernel.RoleTable) (G : Nat → Prop) (R : Ixon.Env)
    (env : Ix.Kernel.Env .anon) : Prop where
  /-- The prefix invariant at every carried limit within `G`, for every record store for `R`. -/
  inv : ∀ E, RecordsFor R E → ∀ lim, Carried lim → LimWithin G t lim →
    Decl.PrefixInv.{u} E t lim env
  /-- A block is stored whole (`Typing.Facts.whole`). -/
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

/-- **The boundary invariant** on the admitted groups `G`: the public shape, the internal
part, and the extra clause `X`. -/
structure Bnd (X : Ix.Kernel.RoleTable → (Nat → Prop) → Ixon.Env → Ix.Kernel.Env .anon → Prop)
    (t : Ix.Kernel.RoleTable) (G : Nat → Prop) (R : Ixon.Env) (env : Ix.Kernel.Env .anon) :
    Prop where
  shape : TableShape.{u} t G R env
  facts : BFacts.{u} t G R env
  extra : X t G R env

/-- `Bnd` depends on the group set only extensionally. -/
theorem Bnd.congr {X : Ix.Kernel.RoleTable → (Nat → Prop) → Ixon.Env → Ix.Kernel.Env .anon → Prop}
    {t : Ix.Kernel.RoleTable} {G G' : Nat → Prop} {R : Ixon.Env} {env : Ix.Kernel.Env .anon}
    (hG : ∀ k, G k ↔ G' k) (h : Bnd.{u} X t G R env) : Bnd.{u} X t G' R env := by
  have e : G = G' := funext fun k => propext (hG k)
  subst e
  exact h

/-! ## A binding run, as the fold reads it -/

/-- **What the fold reads of a binding run**: the records it loaded, a rank of the records
walked for each group, whether the unit at an address was checked under a role context at a
limit, and whether a role was validated in a group's validation. The claim layer instantiates
`checked` with the circuit's check (`Typing.CheckedAtFullAt` at the binding address, or the
block form) and `validated` with `RoleVal.RoleValidatedAt` and the facts the validation of
the role's kind refines to. -/
structure BRun where
  E₀ : Ixon.Env
  rank : Nat → _root_.Address → Nat
  checked : _root_.Address → Nat → Prop
  validated : Nat → Ix.Kernel.Role → Prop

/-- **A record new in `R'`**: `R'` holds a record at `a` and `R` holds none. -/
def New (R R' : Ixon.Env) (a : _root_.Address) : Prop :=
  (recordOf R' a).isSome = true ∧ recordOf R a = none

/-- **The record of a role unit of group `g`**: the record bound to one of the group's
operations or standard axioms. It is installed after the group's closure. -/
def RoleUnitAt (t : Ix.Kernel.RoleTable) (g : Nat) (a : _root_.Address) : Prop :=
  ∃ r ∈ roleGroup g, t.addressOf? r = some a ∧ (r ∈ RoleOps.opRoles ∨ r ∈ standardAxioms)

/-- **An axiom or quotient record.** -/
def IsAxiomLike (c : Ixon.Constant) : Prop :=
  (∃ ax, c.info = .axio ax) ∨ ∃ q, c.info = .quot q

/-- **What the run's admission of group `g` establishes about the store**, from `R` (the
groups admitted before) to `R'` (module docstring). The new records are those the walk of the
group's roots reached and `R` did not hold, the projection records of new blocks, and the
record of the group's standard axiom. -/
structure Admits (ρ : BRun) (t : Ix.Kernel.RoleTable) (g : Nat) (R R' : Ixon.Env) : Prop where
  /-- `R'` holds what `R` holds. -/
  mono : ∀ a lc, R.consts.get? a = some lc → R'.consts.get? a = some lc
  monoBlobs : ∀ a b, R.blobs.get? a = some b → R'.blobs.get? a = some b
  /-- `R'` holds records and blobs the run loaded. -/
  loaded : ∀ a lc, R'.consts.get? a = some lc → ρ.E₀.consts.get? a = some lc
  loadedBlobs : ∀ a b, R'.blobs.get? a = some b → ρ.E₀.blobs.get? a = some b
  /-- The store clauses of `TableShape` for `R'`. -/
  hashed : EnvSelfHashed R'
  usedClosed : UsedClosed R'
  committed : AgreesCommitted R'
  zeroFree : R'.consts.get? Ix.HostAdmission.Merkle.padding = none ∧
    R'.blobs.get? Ix.HostAdmission.Merkle.padding = none
  /-- A reference a new record uses is new at a smaller rank, or held by `R`. -/
  rankUsed : ∀ a x, New R R' a → UsedRef R' a x →
    (New R R' x ∧ ρ.rank g x < ρ.rank g a) ∨ (recordOf R x).isSome = true
  /-- A new projection record's block is new at a smaller rank, or held by `R`. -/
  rankOwner : ∀ a c, New R R' a → recordOf R' a = some c → IsProj c →
    (New R R' (Ix.Cert.ownerOf a c) ∧ ρ.rank g (Ix.Cert.ownerOf a c) < ρ.rank g a) ∨
      (recordOf R (Ix.Cert.ownerOf a c)).isSome = true
  /-- A new projection record is at a member's or a constructor's address of its block. -/
  projMember : ∀ a c, New R R' a → recordOf R' a = some c → IsProj c →
    ∃ cb, recordOf R' (Ix.Cert.ownerOf a c) = some cb ∧ ConstAddrOf (Ix.Cert.ownerOf a c) cb a
  /-- A new axiom or quotient record is the record of a standard axiom of the group. -/
  standing : ∀ a c, New R R' a → recordOf R' a = some c → IsAxiomLike c →
    ∃ r ∈ roleGroup g, r ∈ standardAxioms ∧ t.addressOf? r = some a
  /-- A new record is in Lean's logic. -/
  logic : ∀ a c, New R R' a → recordOf R' a = some c → InLogic c
  /-- Every new unit (definition, recursor or block) was checked at the group's limit. -/
  checked : ∀ a c, New R R' a → recordOf R' a = some c → UnitKind c →
    ρ.checked a (valLimit g)
  /-- Every role of the group was validated. -/
  validated : ∀ r ∈ roleGroup g, ρ.validated g r
  /-- The record of every kept or prelude role of the group is held by `R'`. -/
  kept : ∀ r ∈ roleGroup g, (keptRole r ∨ r ∈ preludeRoles) → ∀ a, t.addressOf? r = some a →
    (recordOf R' a).isSome = true
  /-- No new record is an operation's, other than the group's own. -/
  opsOwn : ∀ a r, New R R' a → t.addressOf? r = some a → r ∈ RoleOps.opRoles → r ∈ roleGroup g
  /-- No new record uses the record of a role unit of the group: the walk refuses an
  operation's own address (`assert_op_reached_in_order`, `op_order_scan`) and an axiom whose
  role is not in force (`check_const`'s axiom arm). So the role units come last. -/
  unitsLast : ∀ x a, New R R' x → UsedRef R' x a → ¬ RoleUnitAt t g a
  /-- The record at every used reference of a proof in the evidence of a role of the group,
  other than the role's own record, is held by `R'`: the validation walks them (a certificate's
  references by `walk_refs_except`, an equation theorem with its closure). -/
  evidenceRefs : ∀ r ∈ roleGroup g, ∀ (arr : Array (Ix.Kernel.Evidence _root_.Address))
    (thm x : _root_.Address), (r, arr) ∈ t.evidence.toList →
    Ix.Kernel.Evidence.proof thm ∈ arr.toList → UsedRef ρ.E₀ thm x →
    t.addressOf? r ≠ some x → (recordOf R' x).isSome = true

/-! ## The step -/

/-- **The step of group `g` on the admitted groups `G`** (module docstring). The premises on
`G`: the roles of `g` are bound, `G` holds the groups `g` needs, and `G` holds the group of every
bound role in force at `g`'s validation limit. -/
def StepCore (X : Ix.Kernel.RoleTable → (Nat → Prop) → Ixon.Env → Ix.Kernel.Env .anon → Prop)
    (ρ : BRun) (t : Ix.Kernel.RoleTable) (G : Nat → Prop) (g : Nat) : Prop :=
  ∀ (R R' : Ixon.Env) (env : Ix.Kernel.Env .anon),
    (∀ r ∈ roleGroup g, (t.addressOf? r).isSome = true) →
    (∀ r ∈ groupNeeded g, G (Ix.SpecDigest.groupOf r)) →
    LimWithin G t (some (valLimit g)) →
    Bnd.{u} X t G R env → Admits ρ t g R R' →
      ∃ env' : Ix.Kernel.Env .anon, (∀ ci ∈ env.consts, ci ∈ env'.consts) ∧
        Bnd.{u} X t (fun k => G k ∨ k = g) R' env'

/-- **One step taken at concrete data**: the premises of `StepCore` and its conclusion hold
at `R`, `R'`, `env`, `env'`. An inhabitant shows the step's interface is satisfiable there. -/
structure StepInstance
    (X : Ix.Kernel.RoleTable → (Nat → Prop) → Ixon.Env → Ix.Kernel.Env .anon → Prop)
    (ρ : BRun) (t : Ix.Kernel.RoleTable) (G : Nat → Prop) (g : Nat) (R R' : Ixon.Env)
    (env env' : Ix.Kernel.Env .anon) : Prop where
  bound : ∀ r ∈ roleGroup g, (t.addressOf? r).isSome = true
  needs : ∀ r ∈ groupNeeded g, G (Ix.SpecDigest.groupOf r)
  limWithin : LimWithin G t (some (valLimit g))
  pre : Bnd.{u} X t G R env
  admits : Admits ρ t g R R'
  ext : ∀ ci ∈ env.consts, ci ∈ env'.consts
  post : Bnd.{u} X t (fun k => G k ∨ k = g) R' env'

/-- **The internal part of the witness the public statement's `GroupStep` reads**: `BFacts`
and the extra clause. A table witness for it is the boundary invariant. -/
abbrev BW (X : Ix.Kernel.RoleTable → (Nat → Prop) → Ixon.Env → Ix.Kernel.Env .anon → Prop)
    (t : Ix.Kernel.RoleTable) (G : Nat → Prop) (R : Ixon.Env) (env : Ix.Kernel.Env .anon) :
    Prop :=
  BFacts.{u} t G R env ∧ X t G R env

theorem Bnd.witness {X : Ix.Kernel.RoleTable → (Nat → Prop) → Ixon.Env → Ix.Kernel.Env .anon → Prop}
    {t : Ix.Kernel.RoleTable} {G : Nat → Prop} {R : Ixon.Env} {env : Ix.Kernel.Env .anon}
    (h : Bnd.{u} X t G R env) : TableWitness.{u} (BW.{u} X) t G R env :=
  ⟨h.shape, h.facts, h.extra⟩

theorem Bnd.of_witness
    {X : Ix.Kernel.RoleTable → (Nat → Prop) → Ixon.Env → Ix.Kernel.Env .anon → Prop}
    {t : Ix.Kernel.RoleTable} {G : Nat → Prop} {R : Ixon.Env} {env : Ix.Kernel.Env .anon}
    (h : TableWitness.{u} (BW.{u} X) t G R env) : Bnd.{u} X t G R env :=
  ⟨h.shape, h.facts.1, h.facts.2⟩

/-- **`GroupStep` is `StepCore` below `g` with every role bound**: the public statement's step
(`IxVM.Consistency.GroupStep`), for the internal part `BW X` and the admission `Admits ρ`, from
`StepCore` at every group. -/
theorem groupStep_of_stepCore
    {X : Ix.Kernel.RoleTable → (Nat → Prop) → Ixon.Env → Ix.Kernel.Env .anon → Prop}
    {ρ : BRun}
    (h : ∀ t g, AllBound t → g < Ix.SpecDigest.groups.length → StepCore.{u} X ρ t (· < g) g) :
    GroupStep.{u} (BW.{u} X) (Admits ρ) := by
  intro t g R R' env hg hall hw hadm
  obtain ⟨env', hext, hb⟩ := h t g hall hg R R' env (fun r _ => hall r)
    (fun r hr => groupNeeded_lt hr) (limWithin_below t g) (Bnd.of_witness hw) hadm
  exact ⟨env', hext, hb.witness⟩

end IxVM.Refinement.Binding
