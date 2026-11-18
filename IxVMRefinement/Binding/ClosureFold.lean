import IxVMRefinement.Binding.FamilyWitness
import IxVMRefinement.Binding.WalkedStored

/-! # The closure of a group with its modeled blocks' families: the fold's statement

The closure of group `g` installs, in rank order, every record the group's admission adds that
is no role unit. Each record is installed by the step of its kind, at the closure's store `R₁`
(the group's store without the record of its role unit):

* a unit with no family record that is no twin, by its plain step (`OverUnitStep`): a value
  record, a block of definitions, a standalone recursor, a one-type native block;
* a block with a selected family record `famOf B`, together with that record, by the family step
  (`OverUnitStepFamily`), handed its family check's advice; the family record is no unit of its
  own (it is checked by the block's family check, the exemption of `FamilyAdmits.checked`);
* a second family record of a block (a twin), by the twin step (`OverUnitStepTwin`), handed the
  block's family record installed.

The statement is `ClosureFoldStatement`: from the three step premises, the closure of every group
in the family form, with the binding fold's invariant that the walked records are stored.

* `WalkedStored ρ t G R env` (`Binding/WalkedStored.lean`): every non-block record of `R` the run
  checked, in Lean's logic with its block, is stored at its key, and so is the record of every
  walked role of a group of `G`. The role unit of an operation reads it after the closure. It
  reads the run record, so it sits beside the boundary invariant, in and out.
* `ClosureStepOverFamilyW`: `ClosureStepOverFamily` with `WalkedStored` before and after.
* `ClosureStore t g R R' R₁`: the closure's store: between `R` and `R'`, every blob of `R'`, and
  lacking only records of the group's role units.
* `ClosureNeeds E₀ famOf adv A x`: what the step of the unit at `A` reads stored: the in-logic
  constant addresses its record uses; for a block with a family record, those its family record
  and its advice use, and the advice's constant addresses.
* `ClosureRunFacts ρ t g R R' famOf adv`: the facts about the run's stores and walk the fold reads
  beside the admission and the family checks.
* `ClosureFam calls ρ t g`: what the run gives at a group beside `Admits`, `AdmitsReads` and
  `FamilyAdmits`: the family checks at one binding (`GroupFamilyChecks`) and the run facts.
* `ClosureCtx`: what the fold hands a step: the invariant and the stored families before the
  group, the admission with its reading clause, the run's family checks and facts, and the
  closure's store.
* `ClosureUnitSteps`, `ClosureFamilySteps`, `ClosureTwinSteps`: the three step premises.
* `IsTwinShape c`: a non-empty block of recursors only. -/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open IxVM.Refinement.Typing.TwinFamily (FamilyInstalled)
open IxVM.Refinement.Binding.FamilyOf (FamilyOfBlock)
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open Ix.Kernel.Semantics (NativeFam)

/-- **The closure of group `g` with its families and the walked records stored**:
`ClosureStepOverFamily` with `WalkedStored` on the groups below `g` before the group and after
its closure. -/
def ClosureStepOverFamilyW (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop) (ρ : BRun)
    (t : Ix.Kernel.RoleTable) (g : Nat)
    (Fam : Ixon.Env → Ixon.Env → (_root_.Address → Option _root_.Address) →
      (_root_.Address → _root_.Address → Prop) → (_root_.Address → _root_.Address → Prop) →
      Prop) : Prop :=
  ∀ (R R' : Ixon.Env) (env : Ix.Kernel.Env .anon)
    (famOf₀ famOf : _root_.Address → Option _root_.Address)
    (adv cont : _root_.Address → _root_.Address → Prop),
    BndOver.{u} L t (· < g) R env → WalkedStored ρ t (· < g) R env →
    StoredFamilies t R env famOf₀ →
    Admits ρ t g R R' → AdmitsReads ρ t R R' →
    Fam R R' famOf adv cont → FamilyAdmits ρ t g R R' famOf adv cont →
    ∃ (R₁ : Ixon.Env) (env₁ : Ix.Kernel.Env .anon)
      (famOf₁ : _root_.Address → Option _root_.Address),
      StoreLe R R₁ ∧ StoreLe R₁ R' ∧
      (∀ x b, R'.blobs.get? x = some b → R₁.blobs.get? x = some b) ∧
      (∀ a, (R'.consts.get? a).isSome = true → R₁.consts.get? a = none → RoleUnitAt t g a) ∧
      (∀ ci ∈ env.consts, ci ∈ env₁.consts) ∧
      BndOver.{u} L t (· < g) R₁ env₁ ∧ GroupKept t g R₁ env₁ ∧
      StoredFamilies t R₁ env₁ famOf₁ ∧
      (∀ B rb, famOf₀ B = some rb → famOf₁ B = some rb) ∧
      (∀ B rb, famOf B = some rb → famOf₁ B = some rb) ∧
      WalkedStored ρ t (· < g) R₁ env₁

/-! ## The closure's store, the needs, the run's facts -/

/-- **The closure's store** `R₁` of group `g`: between `R` and `R'`, with every blob of `R'`,
lacking only records of the group's role units. -/
structure ClosureStore (t : Ix.Kernel.RoleTable) (g : Nat) (R R' R₁ : Ixon.Env) : Prop where
  le₁ : StoreLe R R₁
  le₂ : StoreLe R₁ R'
  blobs : ∀ x b, R'.blobs.get? x = some b → R₁.blobs.get? x = some b
  units : ∀ a, (R'.consts.get? a).isSome = true → R₁.consts.get? a = none → RoleUnitAt t g a

/-- **A non-empty block of recursors only**: the shape of a twin. -/
def IsTwinShape (c : Ixon.Constant) : Prop :=
  ∃ rs : Array Ixon.MutConst, c.info = .muts rs ∧ 0 < rs.size ∧
    ∀ m ∈ rs.toList, ∃ r, m = Ixon.MutConst.recr r

/-- **A new unit of the group that the plain step installs**: a record new in the group, a
definition, a recursor or a block, no record of a role unit of the group, with no selected family
record, claimed by no block as its family record, and of no twin's shape. -/
def PlainUnitAt (t : Ix.Kernel.RoleTable) (g : Nat) (R R' : Ixon.Env)
    (famOf : _root_.Address → Option _root_.Address) (A : _root_.Address) (c : Ixon.Constant) :
    Prop :=
  New R R' A ∧ recordOf R' A = some c ∧ UnitKind c ∧ ¬ RoleUnitAt t g A ∧ famOf A = none ∧
    (∀ B, famOf B ≠ some A) ∧ ¬ IsTwinShape c

/-- **What the step of the unit at `A` reads stored** (module docstring). -/
def ClosureNeeds (E₀ : Ixon.Env) (famOf : _root_.Address → Option _root_.Address)
    (adv : _root_.Address → _root_.Address → Prop) (A x : _root_.Address) : Prop :=
  (UsedRef E₀ A x ∧ NeedOk E₀ x) ∨
  (∃ rb, famOf A = some rb ∧ UsedRef E₀ rb x ∧ NeedOk E₀ x) ∨
  (∃ rb a ca, famOf A = some rb ∧ adv A a ∧ recordOf E₀ a = some ca ∧ ConstAddrOf a ca x) ∨
  (∃ rb a, famOf A = some rb ∧ adv A a ∧ UsedRef E₀ a x ∧ NeedOk E₀ x)

/-- **What the closure reads of the run's stores and walk at group `g`**, beside the admission
`Admits`, its reading clause `AdmitsReads`, the family checks and `FamilyAdmits`. Each field is a
fact about the run at the group (its producer is named in the lane's notes):

* `oldNeeds`: an address a new unit's step reads stored, held before the group, is a non-block
  record in Lean's logic with its block that the run checked at some limit, the address of a
  walked role of an earlier group, or an address with a reading over `R`;
* `famRefs`: an in-logic constant address a selected family record uses that is new in the group
  is a constant address of the block or of the record, or ranked below the block;
* `famNonempty`: a block with a selected family record has a member (so one block selects a
  record with a constant address, and no block selects a block that selects a family record);
* `advNotUnit`: no advice record of a new block's family check is the new record of the group's
  role unit;
* `noPinned`: no constant address of a new record is at the key of a pinned basis constant;
* `roleUnitForm`: a new record of a role unit of the group is an operation's definition or a
  standard axiom's record;
* `keptRoles`: the record of each kept or prelude role of the group that is no role unit is in
  the group's store, no block, in Lean's logic with its block, and, if held before the group,
  checked by the run at some limit;
* `routeNew`: at a store between `R` and `R'` lacking only role-unit records, a new block the
  store routes as modeled has a selected family record (a block held before the group keeps its
  route, `blockRoute_closureStore`);
* `readsDown`: at such a store, a reading of an address `R` holds is a reading over `R`;
* `notInert`, `needOk`: no reference a plain unit of the group (`PlainUnitAt`) uses is the
  address of an inert axiom, and every one is a reference a step needs stored (`NeedOk`);
* `literals`: the key of the member of a plain unit that is a block of one inductive type is none
  of the four literal functions' keys;
* `famNotInert`, `famNeedOk`: the same two facts of the references a new block with a selected
  family record uses. -/
structure ClosureRunFacts (ρ : BRun) (t : Ix.Kernel.RoleTable) (g : Nat) (R R' : Ixon.Env)
    (famOf : _root_.Address → Option _root_.Address)
    (adv : _root_.Address → _root_.Address → Prop) : Prop where
  /-- An address a new unit's step reads stored, held before the group, is one of: a non-block
  record in Lean's logic with its block that the run checked at some limit (producer: the walk's
  `KernelClaim::run_check` at the group that added it, or a check inside a family check,
  `KernelModeled::check_advice_record`, `check_container_rec`); the address of a walked role of
  an earlier group (producer: that role's validation, `KernelRoles::validate_role`); or an
  address with a reading over the store before the group, which the boundary stores
  (`ReadingOf.stored`; producer: the reading of a projection record from its block's check over
  the used-closed store, such as a constructor projection of an advice block that
  `KernelClaim::check_muts_all` checked inside an earlier family check). -/
  oldNeeds : ∀ A x, New R R' A → ClosureNeeds ρ.E₀ famOf adv A x →
    (recordOf R x).isSome = true →
    (∃ c n, recordOf R x = some c ∧ (∀ ms, c.info ≠ .muts ms) ∧ InLogic c ∧
      (∀ cb, recordOf R (Ix.Cert.ownerOf x c) = some cb → InLogic cb) ∧ ρ.checked x n) ∨
    (∃ r, walkedRole r = true ∧ Ix.SpecDigest.groupOf r < g ∧ t.addressOf? r = some x) ∨
    ∃ ci₀, IxVM.Consistency.Reads t R x ci₀
  famRefs : ∀ B rb x, famOf B = some rb → UsedRef ρ.E₀ rb x → NeedOk ρ.E₀ x → New R R' x →
    (∃ cb crb, recordOf R' B = some cb ∧ recordOf R' rb = some crb ∧ FamAddr B cb rb crb x) ∨
      ρ.rank g x < ρ.rank g B
  famNonempty : ∀ B rb, famOf B = some rb → ∃ cb ms, recordOf ρ.E₀ B = some cb ∧
    cb.info = .muts ms ∧ 0 < ms.size
  advNotUnit : ∀ B rb a, famOf B = some rb → adv B a → ¬ (RoleUnitAt t g a ∧ New R R' a)
  noPinned : ∀ A c x ci, New R R' A → recordOf R' A = some c → ConstAddrOf A c x →
    PinnedBasis ci → ci.name ≠ keyOf t x
  roleUnitForm : ∀ a c, RoleUnitAt t g a → New R R' a → recordOf R' a = some c →
    (∃ d, c.info = .defn d) ∨ ∃ ax, c.info = .axio ax
  keptRoles : ∀ r ∈ roleGroup g, (keptRole r ∨ r ∈ preludeRoles) →
    ¬ (r ∈ RoleOps.opRoles ∨ r ∈ standardAxioms) → ∀ a, t.addressOf? r = some a →
    ∃ c, recordOf R' a = some c ∧ (∀ ms, c.info ≠ .muts ms) ∧ InLogic c ∧
      (∀ cb, recordOf R' (Ix.Cert.ownerOf a c) = some cb → InLogic cb) ∧
      ((recordOf R a).isSome = true → ∃ n, ρ.checked a n)
  routeNew : ∀ R₁ B, ClosureStore t g R R' R₁ → New R R' B →
    Route.blockRoute R₁ B = some true → ∃ rb, famOf B = some rb
  readsDown : ∀ R₁ x ci₀, ClosureStore t g R R' R₁ → (recordOf R x).isSome = true →
    Reads t R₁ x ci₀ → Reads t R x ci₀
  /-- No reference a plain unit uses is an inert axiom's. Producer: the group's walk.
  `KernelRoles::assert_ref_allowed` admits a reference bound to an inert role whose group is at or
  above the group's validation limit (`Claim.refAllowed_inert`); such a reference is excluded by
  `check_const`'s axiom arm with the inert role's own validation. For the records of the
  group's payload (advice records, container recursors), the circuit asserts nothing of their
  references until the advice and container checks run the walk's reference assertions on them
  (`KernelClaim::assert_safe_used_refs`, `assert_not_block_ref`). -/
  notInert : ∀ A c x, PlainUnitAt t g R R' famOf A c → UsedRef ρ.E₀ A x → ¬ InertAt t x
  /-- Every reference a plain unit uses is one a step needs stored: a record of the run's store,
  no block, in Lean's logic with its block. Producer: the group's walk
  (`KernelClaim::assert_not_block_ref`, `assert_safe_used_refs`); for the records of the group's
  payload, the same assertions once the advice and container checks run them on their records'
  references. -/
  needOk : ∀ A c x, PlainUnitAt t g R R' famOf A c → UsedRef ρ.E₀ A x → NeedOk ρ.E₀ x
  /-- The key of the member of a plain unit that is a block of one inductive type is none of the
  keys of the four literal functions (`String.ofList`, `List.nil`, `List.cons`, `Char.ofNat`), which
  the step of a block whose former is declared at a definition reads apart. Producer: above
  group 45 the four roles' records are held before the group (`Admits.kept` at their groups) and
  the member's projection record is new, so the addresses and keys differ; at or below group 45,
  the four roles' validations (their records are no inductive projection), not proved. -/
  literals : ∀ A c ind, PlainUnitAt t g R R' famOf A c → c.info = .muts #[.indc ind] →
    keyOf t (memberAddr A 0 (.indc ind)) ≠ Ix.Kernel.stringOfListName ∧
    keyOf t (memberAddr A 0 (.indc ind)) ≠ Ix.Kernel.listNilName ∧
    keyOf t (memberAddr A 0 (.indc ind)) ≠ Ix.Kernel.listConsName ∧
    keyOf t (memberAddr A 0 (.indc ind)) ≠ Ix.Kernel.charOfNatName
  /-- No reference the block of a selected family record uses, the block new in the group, is an
  inert axiom's. Producer: the group's walk at the block, a new walked unit checked at the group's
  validation limit (`FamilyAdmits.checked`; the block is claimed by no block):
  `KernelRoles::assert_ref_allowed` admits a reference bound to an inert role whose group is at or
  above the group's validation limit (`Claim.refAllowed_inert`), and such a reference is excluded
  by `KernelCheck::check_const`'s axiom arm with the inert role's own validation, as for
  `notInert`. -/
  famNotInert : ∀ B rb x, famOf B = some rb → New R R' B → UsedRef ρ.E₀ B x → ¬ InertAt t x
  /-- Every reference the block of a selected family record uses, the block new in the group, is
  one a step needs stored: a record of the run's store, no block, in Lean's logic with its block.
  Producer: the group's walk at the block, a new walked unit checked at the group's validation
  limit (`KernelClaim::assert_not_block_ref`, `KernelClaim::assert_safe_used_refs`), as for
  `needOk`. -/
  famNeedOk : ∀ B rb x, famOf B = some rb → New R R' B → UsedRef ρ.E₀ B x → NeedOk ρ.E₀ x

/-- **What the run gives at group `g` beside the admission and `FamilyAdmits`**: the family
checks at one binding and the run facts. The family form's `Fam`. -/
def ClosureFam (calls : List (Call F)) (ρ : BRun) (t : Ix.Kernel.RoleTable) (g : Nat)
    (R R' : Ixon.Env) (famOf : _root_.Address → Option _root_.Address)
    (adv cont : _root_.Address → _root_.Address → Prop) : Prop :=
  (∃ bAddr, GroupFamilyChecks calls bAddr t ρ.E₀ g R R' famOf adv cont) ∧
    ClosureRunFacts ρ t g R R' famOf adv

/-! ## What the fold hands a step -/

/-- **What the closure fold hands a step** (module docstring): the invariant, the walked records
stored and the stored families before the group; the admission and its reading clause; the run's
family checks at the binding `bAddr`, its facts and `FamilyAdmits`; and the closure's store `R₁`,
closed under what its records use, lacking every role-unit record new in the group. -/
structure ClosureCtx (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop) (calls : List (Call F))
    (ρ : BRun) (t : Ix.Kernel.RoleTable) (g : Nat) (R R' R₁ : Ixon.Env)
    (env : Ix.Kernel.Env .anon) (famOf₀ famOf : _root_.Address → Option _root_.Address)
    (adv cont : _root_.Address → _root_.Address → Prop) (bAddr : _root_.Address) : Prop where
  bnd : BndOver.{u} L t (· < g) R env
  walked : WalkedStored ρ t (· < g) R env
  fams : StoredFamilies t R env famOf₀
  admits : Admits ρ t g R R'
  reads : AdmitsReads ρ t R R'
  checks : GroupFamilyChecks calls bAddr t ρ.E₀ g R R' famOf adv cont
  run : ClosureRunFacts ρ t g R R' famOf adv
  famAdmits : FamilyAdmits ρ t g R R' famOf adv cont
  store : ClosureStore t g R R' R₁
  closed : UsedClosed R₁
  noUnit : ∀ a, RoleUnitAt t g a → New R R' a → R₁.consts.get? a = none

/-! ## The three step premises -/

/-- **The plain step of a new unit**: at every context the fold hands, every environment
`envT` extending the witness's with distinct names, and every new unit of the closure's store
with a constant address, no family record, claimed by no block and of no twin's shape, whose
constant addresses `envT` does not store: its step over the fold's clause at `R₁`. -/
def ClosureUnitSteps (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop) (calls : List (Call F))
    (ρ : BRun) (t : Ix.Kernel.RoleTable) (g : Nat) : Prop :=
  ∀ (R R' R₁ : Ixon.Env) (env envT : Ix.Kernel.Env .anon)
    (famOf₀ famOf : _root_.Address → Option _root_.Address)
    (adv cont : _root_.Address → _root_.Address → Prop) (bAddr A : _root_.Address)
    (c : Ixon.Constant),
    ClosureCtx.{u} L calls ρ t g R R' R₁ env famOf₀ famOf adv cont bAddr →
    (∀ ci ∈ env.consts, ci ∈ envT.consts) → (envT.consts.map (·.name)).Nodup →
    New R R₁ A → recordOf R₁ A = some c → UnitKind c → (∃ x, ConstAddrOf A c x) →
    famOf A = none → (∀ B, famOf B ≠ some A) → ¬ IsTwinShape c →
    (∀ x, ConstAddrOf A c x → ¬ StoredAt t envT x) →
    OverUnitStep.{u} L t (· < g) R₁ envT ρ.E₀ A c

/-- **The family step of a new block with its selected family record**, handed the advice of
its family check. -/
def ClosureFamilySteps (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop)
    (calls : List (Call F)) (ρ : BRun) (t : Ix.Kernel.RoleTable) (g : Nat) : Prop :=
  ∀ (R R' R₁ : Ixon.Env) (env envT : Ix.Kernel.Env .anon)
    (famOf₀ famOf : _root_.Address → Option _root_.Address)
    (adv cont : _root_.Address → _root_.Address → Prop) (bAddr B rb : _root_.Address)
    (cb crb : Ixon.Constant),
    ClosureCtx.{u} L calls ρ t g R R' R₁ env famOf₀ famOf adv cont bAddr →
    (∀ ci ∈ env.consts, ci ∈ envT.consts) → (envT.consts.map (·.name)).Nodup →
    New R R₁ B → recordOf R₁ B = some cb → (∀ B', famOf B' ≠ some B) →
    famOf B = some rb → recordOf R₁ rb = some crb →
    (∀ x, FamAddr B cb rb crb x → ¬ StoredAt t envT x) →
    OverUnitStepFamily.{u} L t (· < g) R₁ envT ρ.E₀ B cb rb crb (adv B)

/-- **The twin step of a new second family record**: a new unit of a twin's shape with no family
record, claimed by no block, has a block `B` and a family record `rb` of `B` installed before it
(selected before the group, or selected in the group for a block ranked below it), and its step
handed `rb` installed. -/
def ClosureTwinSteps (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop)
    (calls : List (Call F)) (ρ : BRun) (t : Ix.Kernel.RoleTable) (g : Nat) : Prop :=
  ∀ (R R' R₁ : Ixon.Env) (env : Ix.Kernel.Env .anon)
    (famOf₀ famOf : _root_.Address → Option _root_.Address)
    (adv cont : _root_.Address → _root_.Address → Prop) (bAddr A : _root_.Address)
    (c : Ixon.Constant),
    ClosureCtx.{u} L calls ρ t g R R' R₁ env famOf₀ famOf adv cont bAddr →
    New R R₁ A → recordOf R₁ A = some c → IsTwinShape c → famOf A = none →
    (∀ B, famOf B ≠ some A) →
    ∃ (B rb : _root_.Address) (crb : Ixon.Constant), recordOf R₁ rb = some crb ∧
      (famOf₀ B = some rb ∨ (famOf B = some rb ∧ ρ.rank g B < ρ.rank g A)) ∧
      ∀ envT : Ix.Kernel.Env .anon, (∀ ci ∈ env.consts, ci ∈ envT.consts) →
        (envT.consts.map (·.name)).Nodup → (∀ x, ConstAddrOf A c x → ¬ StoredAt t envT x) →
        OverUnitStepTwin.{u} L t (· < g) R₁ envT ρ.E₀ A c rb crb

/-! ## The statement -/

/-- **The closure fold with the family form** (module docstring): at every run record, table
and group from 6 to 76 of a well-formed table binding every role, the three step premises give
the closure of the group in the family form, with the walked records stored. -/
def ClosureFoldStatement (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop) : Prop :=
  ∀ (calls : List (Call F)) (ρ : BRun) (t : Ix.Kernel.RoleTable) (g : Nat),
    6 ≤ g → g < 77 → AllBound t → t.check = .ok () →
    ClosureUnitSteps.{u} L calls ρ t g → ClosureFamilySteps.{u} L calls ρ t g →
    ClosureTwinSteps.{u} L calls ρ t g →
    ClosureStepOverFamilyW.{u} L ρ t g (ClosureFam calls ρ t g)

end IxVM.Refinement.Binding
