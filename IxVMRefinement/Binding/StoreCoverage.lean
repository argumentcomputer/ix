import IxVMRefinement.Binding.Glue
import IxVMRefinement.Binding.UnitDefn
import IxVMRefinement.Binding.FamilyAdmits

/-! # What the binding store covers

Two facts other parts of the proof read off the binding fold's stores, both consequences of the
admission of the groups (`Admits`, `AdmitsReads`) and of nothing else.

* `StoreCovered E₀ R'`: **the store after a group's admission agrees with the run's store and
  is closed under what its records name.** Its records are the run's records at the same
  addresses; its blobs are exactly the run's blobs; the block of every record, the record at
  every constant reference a record uses, and the projection records of every block's members
  and constructors are records of the store. `storeCovered_of_admits` derives it.

  The closure is under the references a record *uses* (`usedRefIdxs`: the entries of its
  reference table that an expression of the record names as a constant) and under literal
  blobs through the run's blobs. It is not under every entry of a record's reference table: an
  entry no expression names is not walked by a run, so nothing puts a record or a blob at it in
  the store.
* `WalkedCovered ρ t Rs famOf`: **every kept role's record and its closure is in the final
  store, loaded by the run, and each unit among the records admitted after the basis was checked
  by the run at the validation limit of the group that admitted it, or is the family record that
  group selected for a block new in it** (`famOf g`; checked by the block's family check).
  `walkedCovered_of_chain` derives it from the admission of each group and the store side of its
  family checks (`FamilyAdmits`). The admitting group of a role's record is the role's own group
  or an earlier one whose walk reached it first; an earlier group's limit is at most the role's
  own.
-/

set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing

/-- **The store `R'` agrees with the run's store `E₀` and is closed under what its records
name** (module docstring). -/
structure StoreCovered (E₀ R' : Ixon.Env) : Prop where
  /-- A record of the store is the run's record at its address. -/
  records : ∀ a c, recordOf R' a = some c → recordOf E₀ a = some c
  /-- The store's blobs are exactly the run's. -/
  blobs : ∀ x b, R'.blobs.get? x = some b ↔ E₀.blobs.get? x = some b
  /-- The block of a record is a record of the store. -/
  owner : ∀ a c, recordOf R' a = some c →
    (recordOf R' (Ix.Cert.ownerOf a c)).isSome = true
  /-- The record at every constant reference a record uses is a record of the store. -/
  usedRefs : ∀ a c, recordOf R' a = some c → ∀ i ∈ usedRefIdxs c, ∀ x, c.refs[i]? = some x →
    (recordOf R' x).isSome = true
  /-- The projection records of a block's members and constructors are records of the store. -/
  members : ∀ (B : _root_.Address) (c : Ixon.Constant) (ms : Array Ixon.MutConst),
    recordOf R' B = some c → c.info = .muts ms → ∀ (i : Nat) (m : Ixon.MutConst),
      ms[i]? = some m →
      recordOf R' (memberAddr B i m) = some (memberProjection B i m) ∧
      ∀ (ind : Ixon.Inductive), m = .indc ind → ∀ (j : Nat), j < ind.ctors.size →
        recordOf R' (ctorAddr B i j) = some (constructorProjection B i j)

/-- **The store after a group's admission is covered**, from the admission and its reading
clause. -/
theorem storeCovered_of_admits {ρ : BRun} {t : Ix.Kernel.RoleTable} {g : Nat}
    {R R' : Ixon.Env} (hadm : Admits ρ t g R R') (hrd : AdmitsReads ρ t R R') :
    StoreCovered ρ.E₀ R' where
  records := fun _ _ h => recordOf_of_loaded hadm.loaded h
  blobs := fun x b => ⟨hadm.loadedBlobs x b, hrd.blobs x b⟩
  owner := fun a c h => (hadm.usedClosed.1 a c h).1
  usedRefs := fun a c h => (hadm.usedClosed.1 a c h).2
  members := hadm.usedClosed.2

/-- **What the final store of a binding run covers** (module docstring); `famOf g` is the family
selection of group `g`. -/
structure WalkedCovered (ρ : BRun) (t : Ix.Kernel.RoleTable) (Rs : Nat → Ixon.Env)
    (famOf : Nat → _root_.Address → Option _root_.Address) : Prop where
  /-- The record of every kept or prelude role of a group from 6 on is in the final store. -/
  held : ∀ r, 6 ≤ Ix.SpecDigest.groupOf r → (keptRole r ∨ r ∈ preludeRoles) →
    ∀ a, t.addressOf? r = some a → (recordOf (Rs 77) a).isSome = true
  /-- The final store is closed under what its records use. -/
  closed : UsedClosed (Rs 77)
  /-- A record of the final store is the run's record at its address. -/
  loaded : ∀ a c, recordOf (Rs 77) a = some c → recordOf ρ.E₀ a = some c
  /-- A record of the final store that the basis store does not hold was admitted by a group,
  and if it is a unit the run checked it at that group's validation limit, or it is the family
  record the group selected for a block new in it. -/
  checked : ∀ a c, recordOf (Rs 77) a = some c → recordOf (Rs 6) a = none →
    ∃ g, 6 ≤ g ∧ g < 77 ∧ New (Rs g) (Rs (g + 1)) a ∧
      (UnitKind c → ρ.checked a (valLimit g) ∨ ∃ B, famOf g B = some a ∧ New (Rs g) (Rs (g + 1)) B)

section Chain

variable {ρ : BRun} {t : Ix.Kernel.RoleTable} {Rs : Nat → Ixon.Env}
  {famOf : Nat → _root_.Address → Option _root_.Address}

/-- A record of the store before a group is a record of every later store. -/
theorem recordOf_chain_mono
    (hadm : ∀ g, 6 ≤ g → g < 77 → Admits ρ t g (Rs g) (Rs (g + 1)))
    {a : _root_.Address} {c : Ixon.Constant} {m : Nat} (hm : 6 ≤ m)
    (h : recordOf (Rs m) a = some c) :
    ∀ n, m ≤ n → n ≤ 77 → recordOf (Rs n) a = some c := by
  intro n hmn
  induction n, hmn using Nat.le_induction with
  | base => exact fun _ => h
  | succ n hmn ih =>
    intro hn
    exact recordOf_of_loaded (hadm n (by omega) (by omega)).mono (ih (by omega))

/-- A record of a store past the basis that the basis store does not hold was admitted by an
earlier group, which checked it if it is a unit or selected it as the family record of a block
new in the group. -/
theorem admitted_of_chain
    (hadm : ∀ g, 6 ≤ g → g < 77 → Admits ρ t g (Rs g) (Rs (g + 1)))
    (hfam : ∀ g, 6 ≤ g → g < 77 → ∃ adv cont : _root_.Address → _root_.Address → Prop,
      FamilyAdmits ρ t g (Rs g) (Rs (g + 1)) (famOf g) adv cont)
    {a : _root_.Address} {c : Ixon.Constant} (h6 : recordOf (Rs 6) a = none) :
    ∀ n, 6 ≤ n → n ≤ 77 → recordOf (Rs n) a = some c →
      ∃ g, 6 ≤ g ∧ g < n ∧ New (Rs g) (Rs (g + 1)) a ∧
        (UnitKind c → ρ.checked a (valLimit g) ∨
          ∃ B, famOf g B = some a ∧ New (Rs g) (Rs (g + 1)) B) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    intro _ h
    rw [h6] at h
    cases h
  | succ n hn ih =>
    intro hn77 h
    cases hprev : recordOf (Rs n) a with
    | none =>
      have hnew : New (Rs n) (Rs (n + 1)) a := ⟨by rw [h]; rfl, hprev⟩
      obtain ⟨adv, cont, hF⟩ := hfam n hn (by omega)
      exact ⟨n, hn, Nat.lt_succ_self n, hnew, fun hu => hF.checked a c hnew h hu⟩
    | some c' =>
      have hup := recordOf_of_loaded (hadm n hn (by omega)).mono hprev
      have hcc : c' = c := Option.some.inj (hup.symm.trans h)
      rw [hcc] at hprev
      obtain ⟨g, hg6, hgn, hnew, hchk⟩ := ih (by omega) hprev
      exact ⟨g, hg6, Nat.lt_succ_of_lt hgn, hnew, hchk⟩

/-- **The final store of a binding run is covered**, from the admission of each group and the
store side of its family checks. -/
theorem walkedCovered_of_chain
    (hadm : ∀ g, 6 ≤ g → g < 77 → Admits ρ t g (Rs g) (Rs (g + 1)))
    (hfam : ∀ g, 6 ≤ g → g < 77 → ∃ adv cont : _root_.Address → _root_.Address → Prop,
      FamilyAdmits ρ t g (Rs g) (Rs (g + 1)) (famOf g) adv cont) :
    WalkedCovered ρ t Rs famOf where
  held := by
    intro r h6 hk a ha
    have hlt : Ix.SpecDigest.groupOf r < 77 := RoleVal.groupOf_lt_77 r
    have hheld := (hadm _ h6 hlt).kept r (role_mem_roleGroup r) hk a ha
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hheld
    rw [recordOf_chain_mono hadm (Nat.le_succ_of_le h6) hc 77 (by omega) (Nat.le_refl 77)]
    rfl
  closed := (hadm 76 (by omega) (by omega)).usedClosed
  loaded := fun _ _ h => recordOf_of_loaded (hadm 76 (by omega) (by omega)).loaded h
  checked := by
    intro a c h h6
    obtain ⟨g, hg6, hg, hnew, hchk⟩ :=
      admitted_of_chain hadm hfam h6 77 (by omega) (Nat.le_refl 77) h
    exact ⟨g, hg6, hg, hnew, hchk⟩

end Chain

end IxVM.Refinement.Binding
