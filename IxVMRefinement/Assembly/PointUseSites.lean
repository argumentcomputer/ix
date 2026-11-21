import IxVMRefinement.Assembly.PointRecord
import IxVMRefinement.Core.AllSteps
import IxVMRefinement.Ingress.HashedBlock

/-! # The circuit's use sites at a block on the constructors-only route

The one-point install stores a modeled block's types at the empty capability record and no
projection table (`Decl.Point.PointBlock.former_caps`, `.former_noTable`). The load contract's
fields that would ask more of a stored family (`projTables`, `projTablesAt`, `unitLike`,
`unitLikeRaw`, `eta`, `etaIota`) are each reached only through a circuit observation that the
modeled branch never makes, or at a block shape a modeled block never has. This file gives the
facts about the circuit's dispatch functions that route them away:

* `nativeAt_of_projCtor`: `KernelModeled::proj_ctor` asserts `block_is_modeled = 0`, so an
  observed projection at a block makes it native (`NativeAt`);
* `modeledAt_of_multi`: at a block of two or more inductives no good run answers
  `block_is_modeled = 0` (`Specs.Callees.block_is_modeled`, through the registry at a prefix);
* `multi_not_zero`: nor `block_is_multi = 0`;
* `few_not_multi`: `FewInductives` fails there.

At a block of ONE inductive with a nested occurrence the same three facts need a specification of
`KernelModeled::ctors_nested` (its answer is a function of the stored records) and of
`KernelWhnf::struct_is_rec` at such a block; `NestedGate` names what the load contract reads of
them. It has no producer in the tree.
-/

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal IndCaps)

universe u

/-! ## The number of inductive members -/

/-- **The record at `B` is a block of two or more inductive types.** -/
def MultiAt (E : Ixon.Env) (B : _root_.Address) : Prop :=
  ∃ cb ms, Ix.Cert.recordAt E B = some cb ∧ cb.info = .muts ms ∧
    2 ≤ (ms.toList.filter Core.isIndc).length

/-- `FewInductives` fails at a block of two or more inductive types. -/
theorem few_not_multi {c : Core.Ctx} {B : _root_.Address} (hm : MultiAt c.E B)
    (hfew : Core.FewInductives c B) : False := by
  obtain ⟨cb, ms, hrec, hms, h2⟩ := hm
  have := hfew cb ms hrec hms
  omega

/-! ## Observations of the dispatch -/

/-- An observation of `block_is_modeled` with the run's goodness gives `NativeAt` when it answers
`0`. -/
theorem nativeAt_of_obs {c : Core.Ctx} {bq : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)} {b : Bytes.Address}
    (ev : ObsFn Core.W "KernelModeled::block_is_modeled" [bq] h (.field 0) h' cs)
    (hg : Core.Good c cs) (hb : Bytes.RepAddressRef Core.addrTy h b bq) :
    NativeAt c.E (Core.ixAddr b) :=
  ⟨bq, h, h', cs, b, ev, hg.1, hg.2, hb, rfl⟩

section Registry

variable {E : Ixon.Env} {t : Ix.Kernel.RoleTable} {lim : Option Nat} {env : Ix.Kernel.Env .anon}

/-- **At a block of two or more inductives no good run answers `block_is_modeled = 0`**: the
callee's specification, read through the registry at any prefix whose invariant holds (the
specification reads the store only, through the record-shape load fact). -/
theorem modeledAt_of_multi (hinv : Decl.PrefixInv.{u} E t lim env) {B : _root_.Address}
    (hm : MultiAt E B) : ModeledAt E B := by
  rintro ⟨bq, h, h', cs, bb, ev, hnc, hbd, hrep, hB⟩
  obtain ⟨cb, ms, hrec, hms, h2⟩ := hm
  have hspec := Core.Registry.spec _ (Core.scoped_steps _ hinv.scopedCoreFacts) _ _ _ _ _ _ ev
    (.callees .block_is_modeled) rfl
  have h1 := (hspec bq bb rfl ⟨hnc, hbd, fun _ _ => trivial⟩ hrep cb
    (by rw [hB]; exact hrec)).1 ⟨ms, hms, h2⟩
  exact absurd (Value.field.inj h1) (by decide)

/-- **At a block of two or more inductives no good run answers `block_is_multi = 0`.** -/
theorem multi_not_zero (hinv : Decl.PrefixInv.{u} E t lim env) {B : _root_.Address}
    (hm : MultiAt E B) {bq : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    {bb : Bytes.Address}
    (ev : ObsFn Core.W "KernelModeled::block_is_multi" [bq] h (.field 0) h' cs)
    (hnc : ¬ View.HashedCollision { env := E } [] cs) (hbd : Bounded cs)
    (hrep : Bytes.RepAddressRef Core.addrTy h bb bq) (hB : Core.ixAddr bb = B) : False := by
  obtain ⟨cb, ms, hrec, hms, h2⟩ := hm
  have hspec := Core.Registry.spec _ (Core.scoped_steps _ hinv.scopedCoreFacts) _ _ _ _ _ _ ev
    (.callees .block_is_multi) rfl
  have h1 := ((hspec bq bb rfl ⟨hnc, hbd, fun _ _ => trivial⟩ hrep).2 cb
    (by rw [hB]; exact hrec)).2 ⟨ms, hms, h2⟩
  exact absurd (Value.field.inj h1) (by decide)

end Registry

/-! ## A block of one inductive -/

/-- **What the load contract reads of a one-type block on the constructors-only route** (no
producer in the tree; module docstring). The block at `B` has the one member `ind`:

* `modeled`: no good run answers `block_is_modeled = 0` at `B` (the answer is `ctors_nested`'s,
  a function of the stored records, and the walked check observed `1`);
* `noUnit`: the member is no structure whose one constructor has no field (a nested occurrence
  is in a field: the constructor's return type names the block only at its head, and its index
  arguments not at all, `check_ctor_return_type`);
* `recursive`: where the member has one constructor, no good run answers `struct_is_rec ≠ 1` at the
  member's address (the field with the nested occurrence mentions the member). -/
structure NestedGate (E : Ixon.Env) (B : _root_.Address) (ind : Ixon.Inductive) : Prop where
  modeled : ModeledAt E B
  noUnit : ind.indices.toNat = 0 → ind.ctors.size = 1 →
    ∀ ct, ind.ctors[0]? = some ct → ct.fields.toNat ≠ 0
  recursive : ind.ctors.size = 1 →
    ∀ (sp v : SourceValue F) (h h' : Heap F) (cs : List (Call F)) (s : Bytes.Address),
      ObsFn Core.W "KernelWhnf::struct_is_rec" [sp] h v h' cs →
      ¬ View.HashedCollision { env := E } [] cs → Bounded cs →
      Bytes.RepAddressRef Core.addrTy h s sp → Core.ixAddr s = Core.iprjAddr B 0 → v = .field 1

/-- **The block's shape on the constructors-only route**: two or more inductive types, or one
inductive type with the facts `NestedGate` names. -/
def PointShape (E : Ixon.Env) (B : _root_.Address) (ms : Array Ixon.MutConst) : Prop :=
  2 ≤ (ms.toList.filter Core.isIndc).length ∨ ∃ ind : Ixon.Inductive, ms = #[.indc ind] ∧ NestedGate E B ind

/-- **The dispatch is the modeled branch in every good run**, at either shape. -/
theorem PointShape.modeledAt {E : Ixon.Env} {t : Ix.Kernel.RoleTable} {lim : Option Nat}
    {env : Ix.Kernel.Env .anon} (hinv : Decl.PrefixInv.{u} E t lim env) {B : _root_.Address}
    {cb : Ixon.Constant} {ms : Array Ixon.MutConst} (hrec : Ix.Cert.recordAt E B = some cb)
    (hms : cb.info = .muts ms) (hs : PointShape E B ms) : ModeledAt E B := by
  rcases hs with h2 | ⟨ind, -, hN⟩
  · exact modeledAt_of_multi hinv ⟨cb, ms, hrec, hms, h2⟩
  · exact hN.modeled

end IxVM.Refinement.Typing
