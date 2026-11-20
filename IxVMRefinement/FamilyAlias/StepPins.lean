import IxVMRefinement.FamilyAlias.StepFamily
import IxVMRefinement.FamilyAlias.EqPin
import IxVMRefinement.Assembly.TypingKeyFree

/-! # The pinned equality and key freedom at the family row's step

Two premises of `unitStepFamily_of_facts` that the row's own hypotheses give:

* `familyEqPin_of_shape` (`heqPin`): every environment the step is asked at extends the
  witness's, which holds the pinned `Eq` block whole (`TableShape.pins`); with distinct names it
  finds it (`eqPin_of_shape`);
* `familyKeyFree_of_shape` (`hkey`): the step is asked only where none of the family's
  addresses is stored, so the witness's environment stores none of them, and the key of an
  address a valid table's environment does not store is free (`keyFree_of_not_stored`: every
  reserved basis name, accelerated `Nat` operation and division certificate name is the key of a
  role whose constant that environment stores). -/

universe u

namespace IxVM.Refinement.Typing.FamilyAlias

open IxVM.Consistency
open Ix.Kernel (ConstantInfo)

/-- **`heqPin` of the family row's step**, from the table's shape. -/
theorem familyEqPin_of_shape {t : Ix.Kernel.RoleTable} {G : Nat → Prop} {R : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} (hshape : TableShape.{u} t G R envT) :
    ∀ env : Ix.Kernel.Env .anon,
      (∀ ci ∈ envT.consts, ci ∈ env.consts) → (env.consts.map (·.name)).Nodup →
      env.find? Ix.Kernel.eqName = some Ix.Kernel.eqA :=
  fun _ hext hnd => eqPin_of_shape hshape hext hnd

/-- **`hbasis` of the family row's step**, from the table's shape. -/
theorem familyBasisPins_of_shape {t : Ix.Kernel.RoleTable} {G : Nat → Prop} {R : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} (hshape : TableShape.{u} t G R envT) :
    ∀ env : Ix.Kernel.Env .anon,
      (∀ ci ∈ envT.consts, ci ∈ env.consts) → (env.consts.map (·.name)).Nodup →
      ∀ ci ∈ IxVM.Refinement.TableInhabit.basisEnv.consts, env.find? ci.name = some ci :=
  fun _ hext hnd => basisPins_of_shape hshape hext hnd

/-- **`hkey` of the family row's step**, from the table's shape and its check: an address that
an environment extending the witness's does not store is not stored by the witness's. -/
theorem familyKeyFree_of_shape {t : Ix.Kernel.RoleTable} {R : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} (hshape : TableShape.{u} t (fun _ => True) R envT)
    (ht : t.check = .ok ()) {A rb : _root_.Address} {c crb : Ixon.Constant} :
    ∀ env : Ix.Kernel.Env .anon, (∀ ci ∈ envT.consts, ci ∈ env.consts) →
      (∀ x, FamAddr A c rb crb x → env.find? (keyOf t x) = none) →
      ∀ x, FamAddr A c rb crb x → Decl.KeyFree (keyOf t x) := by
  intro env hext hfresh x hx
  refine keyFree_of_not_stored hshape ht (fun hst => ?_)
  obtain ⟨ci, hci, hname⟩ := hst
  have h1 := find_isSome_of_storedAt (t := t) (env := env) ⟨ci, hext ci hci, hname⟩
  rw [hfresh x hx] at h1
  exact Bool.false_ne_true h1

end IxVM.Refinement.Typing.FamilyAlias
