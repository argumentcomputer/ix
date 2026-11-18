import IxVMRefinement.Binding.ClauseInvariant
import IxVMRefinement.TwinFamily.Target
import IxVMRefinement.Assembly.PointTable

/-! # The binding fold's family form: the step of a block with its family record

`OverUnitStep` (`Binding/ClauseInvariant.lean`) is the step of one closure unit: it is handed the
used references of one record stored and stores constants at that record's constant addresses.
A block that the circuit routes as modeled is checked together with its family record (a block
of recursors at another address, named by the claim's payload) against advice records that only
the payload names (`KernelModeled::check_family`). Its step is the analogue of the typing half's
`UnitStepFamily` at the binding fold's clause:

* `OverUnitStepFamily L t G R envT E₀ B cb rb crb adv`: from the clause at one registry at every
  record store for `R` and every carried limit within `G`, at an environment that stores what
  the block, its family record and its advice use and the advice's own constant addresses, and
  none of the two records' constant addresses: fresh constants keep the clause with a registry,
  store at each constant address of the block and of the family record a constant that stores
  its reading, install the family record (each recursor with its model companion,
  `FamilyInstalled`), and store nothing else outside derived keys. No name is an operation's.
* `OverUnitStepTwin L t G R envT E₀ A c rb crb`: the step of a second family record `A` of a
  block whose family record `rb` the environment holds installed, at the binding fold's clause
  (the analogue of the typing half's `UnitStepTwin`).

Neither names a limit: the family check of a unit of group `g` runs at the group's validation
limit, one of the carried limits. -/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open IxVM.Refinement.Typing.TwinFamily (FamilyInstalled)
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open Ix.Kernel.Semantics (NativeFam)

/-- **The step of a block with its family record, over the fold's clause** (module docstring).
`adv` is the advice of the block's family check. -/
def OverUnitStepFamily (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop)
    (t : Ix.Kernel.RoleTable) (G : Nat → Prop) (R : Ixon.Env) (envT : Ix.Kernel.Env .anon)
    (E₀ : Ixon.Env) (B : _root_.Address) (cb : Ixon.Constant) (rb : _root_.Address)
    (crb : Ixon.Constant) (adv : _root_.Address → Prop) : Prop :=
  ∀ (env : Ix.Kernel.Env .anon) (Reg : NativeFam .anon → Prop),
    (∀ ci ∈ envT.consts, ci ∈ env.consts) → (env.consts.map (·.name)).Nodup →
    (∀ E, RecordsFor R E → ∀ lim, Carried lim → LimWithin G t lim →
      FoldClauseWith.{u} L t E lim env Reg) →
    (∀ x, UsedRef E₀ B x ∨ UsedRef E₀ rb x →
      (env.find? (keyOf t x)).isSome = true ∨ FamAddr B cb rb crb x ∨ ¬ NeedOk E₀ x) →
    (∀ a, adv a → ∀ ca, recordOf E₀ a = some ca → ∀ x, ConstAddrOf a ca x →
      (env.find? (keyOf t x)).isSome = true) →
    (∀ a, adv a → ∀ x, UsedRef E₀ a x →
      (env.find? (keyOf t x)).isSome = true ∨ FamAddr B cb rb crb x ∨ ¬ NeedOk E₀ x) →
    (∀ x, FamAddr B cb rb crb x → env.find? (keyOf t x) = none) →
    ∃ (new : List (Ix.Kernel.ConstantInfo .anon)) (Reg' : NativeFam .anon → Prop),
      (new.map (·.name)).Nodup ∧ (∀ ci ∈ new, env.find? ci.name = none) ∧
      (∀ E, RecordsFor R E → ∀ lim, Carried lim → LimWithin G t lim →
        FoldClauseWith.{u} L t E lim ⟨new ++ env.consts⟩ Reg') ∧
      (∀ ci ∈ new, ci.name ∉ RoleOps.opNames) ∧
      (∀ x, FamAddr B cb rb crb x →
        ∃ ci ∈ new, ∃ ci₀, ci.name = keyOf t x ∧ Reads t E₀ x ci₀ ∧ StoredAs ci ci₀) ∧
      FamilyInstalled t ⟨new ++ env.consts⟩ rb crb ∧
      ∀ ci ∈ new, (∃ x, FamAddr B cb rb crb x ∧ ci.name = keyOf t x) ∨ ∃ k s, ci.name = .aux k s

/-- **The step of a second family record of a block, over the fold's clause** (module
docstring): `OverUnitStep` of the record at `A`, handed in addition the family record `rb` of its
block installed. -/
def OverUnitStepTwin (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop)
    (t : Ix.Kernel.RoleTable) (G : Nat → Prop) (R : Ixon.Env) (envT : Ix.Kernel.Env .anon)
    (E₀ : Ixon.Env) (A : _root_.Address) (c : Ixon.Constant) (rb : _root_.Address)
    (crb : Ixon.Constant) : Prop :=
  ∀ (env : Ix.Kernel.Env .anon) (Reg : NativeFam .anon → Prop),
    (∀ ci ∈ envT.consts, ci ∈ env.consts) → (env.consts.map (·.name)).Nodup →
    (∀ E, RecordsFor R E → ∀ lim, Carried lim → LimWithin G t lim →
      FoldClauseWith.{u} L t E lim env Reg) →
    (∀ x, UsedRef E₀ A x →
      (env.find? (keyOf t x)).isSome = true ∨ ConstAddrOf A c x ∨ ¬ NeedOk E₀ x) →
    FamilyInstalled t env rb crb →
    (∀ x, ConstAddrOf A c x → env.find? (keyOf t x) = none) →
    ∃ (new : List (Ix.Kernel.ConstantInfo .anon)) (Reg' : NativeFam .anon → Prop),
      (new.map (·.name)).Nodup ∧ (∀ ci ∈ new, env.find? ci.name = none) ∧
      (∀ E, RecordsFor R E → ∀ lim, Carried lim → LimWithin G t lim →
        FoldClauseWith.{u} L t E lim ⟨new ++ env.consts⟩ Reg') ∧
      (∀ ci ∈ new, ci.name ∉ RoleOps.opNames) ∧
      (∀ x, ConstAddrOf A c x →
        ∃ ci ∈ new, ∃ ci₀, ci.name = keyOf t x ∧ Reads t E₀ x ci₀ ∧ StoredAs ci ci₀) ∧
      ∀ ci ∈ new, (∃ x, ConstAddrOf A c x ∧ ci.name = keyOf t x) ∨ ∃ k s, ci.name = .aux k s

/-- **A family installed by a step stays installed in every later environment** with distinct
names: what the family step's conclusion gives the rest of the fold. -/
theorem familyInstalled_mono {t : Ix.Kernel.RoleTable} {env env' : Ix.Kernel.Env .anon}
    {rb : _root_.Address} {crb : Ixon.Constant}
    (hext : ∀ ci ∈ env.consts, ci ∈ env'.consts) (hnd : (env'.consts.map (·.name)).Nodup)
    (h : FamilyInstalled t env rb crb) : FamilyInstalled t env' rb crb := by
  intro x hx
  obtain ⟨⟨cv, mI, rP, rules, hf⟩, hm⟩ := h x hx
  exact ⟨⟨cv, mI, rP, rules, find_of_ext hext hnd hf⟩,
    Ix.Kernel.Model.HasModel.mono (fun hk => find_of_ext hext hnd hk) hm⟩

end IxVM.Refinement.Binding
