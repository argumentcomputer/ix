import IxVMRefinement.Decl.PointModel
import IxVMRefinement.Assembly.TypingSkeleton

/-! # The table facts of the constructors-only route

The one-point install (`Decl.Point.PointBlock`) asks two facts that no check of the block's arms
gives: the block's constants sit at input keys (`keyF`, `keyC`), and the kernel's `PUnit` pin is
stored in the prefix (`pin`). Both come from the witness's public shape (`TableShape`) and the
freshness the skeleton hands a unit's step:

* `punitPin_of_shape`: a valid table's environment holds the pinned `PUnit` block whole
  (`TableShape.pins`), so every extension with distinct names stores it, and the derivations the
  one-point model reads (`PUnitPin`) hold there;
* `key_of_fresh`: the key of an address the step's environment does not store is the address
  itself, or a role that the witness's environment need not store (`StoredRole` fails): a role
  that a model reads, a standard axiom or a prelude role is stored at its key by the witness's
  environment (`TableShape.kept`, `TableShape.preludeKept`), and the step's environment extends
  it;
* `key_id_of_fresh`: the input key, where no such unstored role is bound at the address.

The roles `TableShape` leaves unstored are the four inert axioms (`sorryAx`, `trustCompiler`,
`ofReduceBool`, `ofReduceNat`) and the two opaques their types mention (`reduceBool`,
`reduceNat`): a table may bind one of them to a block member's address, and nothing in the
public shape excludes it.
-/

namespace IxVM.Refinement.Typing

open IxVM.Consistency
open Ix.Kernel (ConstantInfo)
open IxVM.Refinement.Decl.Point (PUnitPin)

universe u

/-! ## Stored constants along an extension -/

/-- A constant the witness's environment finds is found by every extension with distinct
names. -/
theorem find_of_ext {envT env : Ix.Kernel.Env .anon} (hext : ∀ ci ∈ envT.consts, ci ∈ env.consts)
    (hnd : (env.consts.map (·.name)).Nodup) {k : Ix.Kernel.Key .anon} {ci : ConstantInfo .anon}
    (h : envT.find? k = some ci) : env.find? k = some ci := by
  have hm := hext ci (Ix.Kernel.Semantics.Env.find?_mem h)
  have hn := Ix.Kernel.Semantics.Env.find?_name h
  have hf := find_of_mem_nodup hnd hm
  rw [hn] at hf
  exact hf

/-! ## The `PUnit` pin -/

/-- **The `PUnit` pin is stored at every extension of a valid table's environment** with
distinct names: the pinned block is in the witness's environment (`TableShape.pins`). -/
theorem punitPin_of_shape {t : Ix.Kernel.RoleTable} {G : Nat → Prop} {R : Ixon.Env}
    {envT env : Ix.Kernel.Env .anon} (hshape : TableShape.{u} t G R envT)
    (hext : ∀ ci ∈ envT.consts, ci ∈ env.consts) (hnd : (env.consts.map (·.name)).Nodup) :
    PUnitPin env := by
  have hP : Ix.Kernel.punitA ∈ env.consts :=
    hext _ (hshape.pins .punitK _ List.mem_cons_self)
  have hU : Ix.Kernel.punitUnitA ∈ env.consts :=
    hext _ (hshape.pins .punitK _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have hfP := find_of_mem_nodup hnd hP
  have hfU := find_of_mem_nodup hnd hU
  have hnP : (Ix.Kernel.punitA : ConstantInfo .anon).name = Ix.Kernel.punitName := by
    decide +kernel
  have hnU : (Ix.Kernel.punitUnitA : ConstantInfo .anon).name = Ix.Kernel.punitUnitName := by
    decide +kernel
  rw [hnP] at hfP
  rw [hnU] at hfU
  exact Decl.Point.PUnitPin.of_stored (ciP := Ix.Kernel.punitA) (ciU := Ix.Kernel.punitUnitA)
    (p := Ix.Kernel.uN) (q := Ix.Kernel.uN) hfP (by decide +kernel) (by decide +kernel)
    (by decide +kernel) hfU (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! ## Input keys -/

/-- **A role a valid table's environment stores at its key**: a role a model reads, a standard
axiom (`keptRole`), or a prelude role. -/
def StoredRole (r : Ix.Kernel.Role) : Prop := keptRole r ∨ r ∈ preludeRoles

/-- A stored role bound by a valid table is stored by the witness's environment at its key. -/
theorem storedRole_find {t : Ix.Kernel.RoleTable} {R : Ixon.Env} {envT : Ix.Kernel.Env .anon}
    (hshape : TableShape.{u} t (fun _ => True) R envT) {r : Ix.Kernel.Role} (hr : StoredRole r)
    {a : _root_.Address} (ha : t.addressOf? r = some a) :
    ∃ ci, envT.find? (.role r) = some ci := by
  rcases hr with hk | hp
  · obtain ⟨ci, hf, -⟩ :=
      hshape.kept (Ix.SpecDigest.groupOf r) r a trivial (role_mem_roleGroup r) hk ha
    exact ⟨ci, hf⟩
  · obtain ⟨ci, hf, -⟩ :=
      hshape.preludeKept (Ix.SpecDigest.groupOf r) r a trivial (role_mem_roleGroup r) hp ha
    exact ⟨ci, hf⟩

/-- **The key of an address the step's environment does not store** is the address itself, or a
role that `TableShape` does not make the witness's environment store, bound at the address. -/
theorem key_of_fresh {t : Ix.Kernel.RoleTable} (htwf : t.wf = true) {R : Ixon.Env}
    {envT env : Ix.Kernel.Env .anon} (hshape : TableShape.{u} t (fun _ => True) R envT)
    (hext : ∀ ci ∈ envT.consts, ci ∈ env.consts) (hnd : (env.consts.map (·.name)).Nodup)
    {x : _root_.Address} (hfresh : env.find? (keyOf t x) = none) :
    keyOf t x = .id x ∨ ∃ r, ¬ StoredRole r ∧ t.addressOf? r = some x := by
  rcases keyOf_cases t x with ⟨h, -⟩ | ⟨r, -, h⟩
  · exact Or.inl h
  · have ha : t.addressOf? r = some x := Core.addressOf_of_keyOf htwf h
    by_cases hs : StoredRole r
    · exfalso
      obtain ⟨ci, hf⟩ := storedRole_find hshape hs ha
      have hf' := find_of_ext hext hnd hf
      rw [← h, hfresh] at hf'
      cases hf'
    · exact Or.inr ⟨r, hs, ha⟩

/-- **The input key**, where no role `TableShape` leaves unstored is bound at the address. -/
theorem key_id_of_fresh {t : Ix.Kernel.RoleTable} (htwf : t.wf = true) {R : Ixon.Env}
    {envT env : Ix.Kernel.Env .anon} (hshape : TableShape.{u} t (fun _ => True) R envT)
    (hext : ∀ ci ∈ envT.consts, ci ∈ env.consts) (hnd : (env.consts.map (·.name)).Nodup)
    {x : _root_.Address} (hfresh : env.find? (keyOf t x) = none)
    (hunb : ∀ r, ¬ StoredRole r → t.addressOf? r ≠ some x) : keyOf t x = .id x := by
  rcases key_of_fresh htwf hshape hext hnd hfresh with h | ⟨r, hs, ha⟩
  · exact h
  · exact absurd ha (hunb r hs)

/-- **Every role but six is stored** (decided over the roles): the roles that are neither kept
nor prelude roles are the four inert axioms and the two opaques `reduceBool`, `reduceNat`. -/
theorem storedRole_or_inert (r : Ix.Kernel.Role) :
    StoredRole r ∨ r ∈ [.sorryAx, .trustCompiler, .ofReduceBool, .ofReduceNat, .reduceBool,
      .reduceNat] := by
  unfold StoredRole keptRole modelRead
  cases r <;> decide +kernel

end IxVM.Refinement.Typing
