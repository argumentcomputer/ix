import IxVMRefinement.Assembly.TypingDefnStep

/-! # The definition step at the real definition record

`DefInhabit.defRecord` is `def _ : Nat := Nat.zero` at an address the default table binds no
role to. This module meets every input of `unitStep_defn` that is about the record, the table
or the witness's environment there:

* the record is a definition in Lean's logic, its key is free, and the two references it
  uses (`Nat`, `Nat.zero`) are no inert axiom's (`defRecord_inLogic`, `defAddr_keyFree`,
  `defRecord_inert`);
* the cover clause holds where the run's store holds a record at those two addresses that a
  step may need (`defRecord_needOk`);
* at the environment of the kernel's pins (`TableInhabit.basisEnv`), the premises of
  `UnitStep` other than the prefix invariant and the extra clause hold: distinct names, both
  references stored, the record's key not stored (`def_unit_premises`).

`def_step_at_basis` is the step there. What it still takes: the run (a run store holding the
record and the two records it uses, a store the step runs against, the walk's check of the
record at the limit `n`), and `Decl.PrefixInv E committedDefaultRoleTable (some n) basisEnv`,
for which nothing produces the load contract, the companions or η stability at an
environment that stores inductive types and constructors.
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Typing

open IxVM.Consistency
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open IxVM.Refinement.RoleVal IxVM.Refinement.DefInhabit

theorem defRecord_inLogic : InLogic defRecord :=
  (rfl : Ix.Kernel.Reader.safetyDecline defDefn = none)

theorem defRecord_refs {x : _root_.Address} (hx : x ∈ defRecord.refs.toList) :
    x = natAddr ∨ x = zeroAddr := by
  have hx' : x ∈ [natAddr, zeroAddr] := hx
  rcases List.mem_cons.mp hx' with h | h
  · exact Or.inl h
  · rcases List.mem_cons.mp h with h' | h'
    · exact Or.inr h'
    · exact absurd h' List.not_mem_nil

theorem defRecord_inert : InertClause committedDefaultRoleTable defRecord := by
  intro i hi x hx
  rcases defRecord_refs (List.mem_of_getElem? hx) with rfl | rfl
  · exact (congrArg inertKey natKey).trans (by decide)
  · exact (congrArg inertKey zeroKey).trans (by decide)

theorem defAddr_keyFree : Decl.KeyFree (keyOf committedDefaultRoleTable defAddr) := by
  rw [defKey]
  exact keyFree_id defAddr

/-- The two references the record uses are none of its constant addresses. -/
theorem not_constAddr_def {x : _root_.Address} (hx : x = natAddr ∨ x = zeroAddr) :
    ¬ ConstAddrOf defAddr defRecord x := by
  rintro (⟨hxd, -⟩ | ⟨ms, i, m, hms, -, -⟩)
  · have h := congrArg (keyOf committedDefaultRoleTable) hxd
    rcases hx with rfl | rfl
    · rw [natKey, defKey] at h
      cases h
    · rw [zeroKey, defKey] at h
      cases h
  · have h : Ixon.ConstantInfo.defn defDefn = .muts ms := hms
    cases h

/-- **The cover clause's input at the record**, from records a step may need at `Nat` and
`Nat.zero` in the run's store. -/
theorem defRecord_needOk {E₀ : Ixon.Env} (hnat : NeedOk E₀ natAddr)
    (hzero : NeedOk E₀ zeroAddr) :
    ∀ i ∈ usedRefIdxs defRecord, ∀ x, defRecord.refs.toList[i]? = some x →
      inertKey (keyOf committedDefaultRoleTable x) = false →
        NeedOk E₀ x ∧ ¬ ConstAddrOf defAddr defRecord x := by
  intro i hi x hx _
  have hr := defRecord_refs (List.mem_of_getElem? hx)
  refine ⟨?_, not_constAddr_def hr⟩
  rcases hr with rfl | rfl
  · exact hnat
  · exact hzero

/-- **The premises of `UnitStep` at the environment of the pins**, other than the prefix
invariant and the extra clause, for the record: distinct names, every reference the record
uses stored, its constant address not stored. -/
theorem def_unit_premises {E₀ : Ixon.Env} (hc : recordOf E₀ defAddr = some defRecord) :
    (TableInhabit.basisEnv.consts.map (·.name)).Nodup ∧
    (∀ x, UsedRef E₀ defAddr x →
      (TableInhabit.basisEnv.find? (keyOf committedDefaultRoleTable x)).isSome = true) ∧
    (∀ x, ConstAddrOf defAddr defRecord x →
      TableInhabit.basisEnv.find? (keyOf committedDefaultRoleTable x) = none) := by
  refine ⟨TableInhabit.basisEnv_nodup, ?_, ?_⟩
  · intro x hx
    obtain ⟨c, i, hc', hi, hxi⟩ := hx
    rw [hc] at hc'
    obtain rfl := Option.some.inj hc'
    have hxl : defRecord.refs.toList[i]? = some x := by
      rw [Array.getElem?_toList]
      exact hxi
    rcases defRecord_refs (List.mem_of_getElem? hxl) with rfl | rfl
    · rw [natKey]
      obtain ⟨ci, hf, -⟩ := StoreInhabit.basisEnv_find (r := .nat) (by decide)
      exact Option.isSome_iff_exists.mpr ⟨ci, hf⟩
    · rw [zeroKey]
      obtain ⟨ci, hf, -⟩ := StoreInhabit.basisEnv_find (r := .natZero) (by decide)
      exact Option.isSome_iff_exists.mpr ⟨ci, hf⟩
  · intro x hx
    have hxd : x = defAddr := by
      rcases hx with ⟨hxd, -⟩ | ⟨ms, i, m, hms, -, -⟩
      · exact hxd
      · have h : Ixon.ConstantInfo.defn defDefn = .muts ms := hms
        cases h
    rw [hxd]
    apply find_none_of_not_storedAt
    rintro ⟨ci, hci, hname⟩
    rw [defKey] at hname
    have hk : ci.name ∈ TableInhabit.basisEnv.consts.map (·.name) :=
      List.mem_map.mpr ⟨ci, hci, rfl⟩
    have hn : TableInhabit.basisEnv.consts.map (·.name) =
        TableInhabit.basisRoleOrder.map Ix.Kernel.Key.role := rfl
    rw [hn, hname] at hk
    obtain ⟨r, -, hr⟩ := List.mem_map.mp hk
    have hr' : (Ix.Kernel.Key.role r : Ix.Kernel.Key .anon) = Ix.Kernel.Key.id defAddr := hr
    cases hr'

/-- **`UnitStep` at the real definition record**: every input of `unitStep_defn` about the
record and the table is met; what remains is the run (`hS`, `hst`, `hc`, `hchk`, and records
a step may need at `Nat` and `Nat.zero`). -/
theorem unitStep_def_record {X : Ix.Kernel.Env .anon → Prop} (hX : KeepsValues X)
    {calls : List (Call F)} {E₀ E : Ixon.Env} {envT : Ix.Kernel.Env .anon}
    {lim : Option Nat} {bAddr : _root_.Address} {n : Nat}
    (hS : LoadedReads.RunStore calls E₀) (hst : StepStore calls committedDefaultRoleTable E₀ E)
    (hc : recordOf E₀ defAddr = some defRecord)
    (hchk : CheckedAtFullAt calls bAddr committedDefaultRoleTable defAddr n)
    (hlim : lim = some n) (hnat : NeedOk E₀ natAddr) (hzero : NeedOk E₀ zeroAddr) :
    UnitStep.{u} X committedDefaultRoleTable envT E₀ E lim defAddr defRecord :=
  unitStep_defn committedDefaultRoleTable_check hS hst hc rfl defRecord_inLogic hchk hlim
    defAddr_keyFree defRecord_inert (coverAt_of_needOk hc (defRecord_needOk hnat hzero)) hX

/-- **The step of the real definition record at the environment of the pins**: from the run,
the prefix invariant there, and the extra clause there, the record's constant is installed,
storing its reading, and the invariant and the extra clause are kept. -/
theorem def_step_at_basis {X : Ix.Kernel.Env .anon → Prop} (hX : KeepsValues X)
    {calls : List (Call F)} {E₀ E : Ixon.Env} {bAddr : _root_.Address} {n : Nat}
    (hS : LoadedReads.RunStore calls E₀) (hst : StepStore calls committedDefaultRoleTable E₀ E)
    (hc : recordOf E₀ defAddr = some defRecord)
    (hchk : CheckedAtFullAt calls bAddr committedDefaultRoleTable defAddr n)
    (hnat : NeedOk E₀ natAddr) (hzero : NeedOk E₀ zeroAddr)
    (hinv : Decl.PrefixInv.{u} E committedDefaultRoleTable (some n) TableInhabit.basisEnv)
    (hXb : X TableInhabit.basisEnv) :
    ∃ new : List (Ix.Kernel.ConstantInfo .anon),
      (new.map (·.name)).Nodup ∧ (∀ ci ∈ new, TableInhabit.basisEnv.find? ci.name = none) ∧
      Decl.PrefixInv.{u} E committedDefaultRoleTable (some n)
        ⟨new ++ TableInhabit.basisEnv.consts⟩ ∧
      X ⟨new ++ TableInhabit.basisEnv.consts⟩ ∧
      (∀ x, ConstAddrOf defAddr defRecord x →
        ∃ ci ∈ new, ∃ ci₀, ci.name = keyOf committedDefaultRoleTable x ∧
          Reads committedDefaultRoleTable E₀ x ci₀ ∧ StoredAs ci ci₀) ∧
      ∀ ci ∈ new, (∃ x, ConstAddrOf defAddr defRecord x ∧
        ci.name = keyOf committedDefaultRoleTable x) ∨ ∃ k s, ci.name = .aux k s := by
  obtain ⟨hnd, hrefs, hfr⟩ := def_unit_premises hc
  exact unitStep_def_record (envT := TableInhabit.basisEnv) hX hS hst hc hchk rfl hnat hzero
    TableInhabit.basisEnv (fun _ h => h) hnd hinv hXb (fun x hx => Or.inl (hrefs x hx)) hfr

end IxVM.Refinement.Typing
