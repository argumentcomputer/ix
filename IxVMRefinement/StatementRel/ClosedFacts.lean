import IxVMRefinement.RoleVal.CommittedData
import Ix.Cert.FallbackStore
import Ix.IxVM.Consistency.TableValid

/-! # Closed facts the table-validity statement rests on

Facts about committed data that make the clauses of `TableShape` say what they are read to
say. Each is proved from the kernel-evaluated checks of the committed rows
(`IxVM.Refinement.RoleVal`) or decided here.

* `committedRows_hashed`: every committed prelude row is stored under the BLAKE3 hash of its
  bytes, so a byte string a run hashes at such an address that differs from the row is a
  collision with it.
* `committedPrelude_rows`: each of the 33 decoded committed prelude records is a row of
  `committedRows`, with its canonical bytes, which decode exactly to it. So `committedRows`
  is not empty and `AgreesCommitted` constrains a store at those 33 addresses.
* `defaultTable_prelude_rows`, `preludePinned_rows`: the default table, and so every table
  that pins the prelude, binds each of the 26 prelude roles at the address of a committed
  row. So `AgreesCommitted` constrains a store at every pinned address.
* `committedPrelude_owner`: the block of a committed projection record is a committed record.
* `defaultTable_allBound`: the default table binds every role.
-/

namespace IxVM.Refinement.ClosedFacts

open IxVM.Consistency
open IxVM.Refinement.RoleVal

/-- A row of the committed file whose address and bytes parse is a row of `committedRows`. -/
theorem mem_committedRows {row : String × String}
    (hrow : row ∈ Ix.Kernel.Reader.RoleData.prelude.toList) {a : _root_.Address}
    {bytes : ByteArray} (ha : Ix.Kernel.Reader.addressOfHex row.1 = some a)
    (hb : bytesOfHex row.2 = some bytes) : (a, bytes) ∈ committedRows := by
  unfold committedRows
  refine List.mem_filterMap.mpr ⟨row, hrow, ?_⟩
  exact (congrArg₂
    (fun (oa : Option _root_.Address) (ob : Option ByteArray) =>
      oa.bind fun a => ob.map fun bytes => (a, bytes)) ha hb).trans rfl

/-- A row of `committedRows` is a row of the committed file, parsed. -/
theorem committedRows_inv {p : _root_.Address × ByteArray} (hp : p ∈ committedRows) :
    ∃ row ∈ Ix.Kernel.Reader.RoleData.prelude.toList,
      Ix.Kernel.Reader.addressOfHex row.1 = some p.1 ∧ bytesOfHex row.2 = some p.2 := by
  unfold committedRows at hp
  obtain ⟨row, hrow, hdec⟩ := List.mem_filterMap.mp hp
  refine ⟨row, hrow, ?_⟩
  have hdec' : ((Ix.Kernel.Reader.addressOfHex row.1).bind fun a =>
      (bytesOfHex row.2).map fun bytes => (a, bytes)) = some p := hdec
  cases ha : Ix.Kernel.Reader.addressOfHex row.1 with
  | none =>
    rw [ha] at hdec'
    have e : (none : Option (_root_.Address × ByteArray)) = some p := hdec'
    cases e
  | some a =>
    cases hb : bytesOfHex row.2 with
    | none =>
      rw [ha, hb] at hdec'
      have e : (none : Option (_root_.Address × ByteArray)) = some p := hdec'
      cases e
    | some bytes =>
      rw [ha, hb] at hdec'
      have e : some (a, bytes) = some p := hdec'
      have e' : (a, bytes) = p := Option.some.inj e
      subst e'
      exact ⟨rfl, rfl⟩

/-- **Every committed prelude row is stored under the BLAKE3 hash of its bytes.** -/
theorem committedRows_hashed : ∀ p ∈ committedRows, Address.blake3Pure p.2 = p.1 := by
  intro p hp
  obtain ⟨row, hrow, ha, hb⟩ := committedRows_inv hp
  have hh := preludeRowsHashed row hrow
  rw [ha, hb] at hh
  have e : some (Address.admissionHash p.2) = some p.1 := hh
  rw [← Address.admissionHash_eq]
  exact Option.some.inj e

/-- There are 33 decoded committed prelude records. -/
theorem committedPrelude_length : committedPreludeList.length = 33 := rfl

/-- **Each decoded committed prelude record is a row of `committedRows`**, with its
canonical bytes, and those bytes decode exactly to it. -/
theorem committedPrelude_rows : ∀ e ∈ committedPreludeList,
    (e.1, Ixon.serConstant e.2) ∈ committedRows ∧
      Ixon.deConstantExact (Ixon.serConstant e.2) = .ok e.2 := by
  intro e he
  obtain ⟨row, hrow, ha, b, hb, hd⟩ :=
    Ix.Cert.FallbackStore.decoded_rows "prelude" Ix.Kernel.Reader.RoleData.prelude
      preludeRecords_eq e (show e ∈ committedPrelude.toList from he)
  obtain ⟨-, wire, encoded⟩ := Ixon.Verify.Canonical.deConstant_spec _ _ _ _ hd
  refine ⟨?_, Ixon.Verify.deConstantExact_serConstant e.2 wire⟩
  rw [encoded]
  exact mem_committedRows hrow ha hb

/-- The default table binds each prelude role at the address of a decoded committed prelude
record (decided). -/
theorem defaultTable_prelude_bool :
    preludeRoles.all (fun r =>
      (committedDefaultRoleTable.addressOf? r).any fun a =>
        committedPreludeList.any fun p => p.1 == a) = true := by
  decide +kernel

/-- **The default table binds each prelude role at the address of a committed row.** -/
theorem defaultTable_prelude_rows : ∀ r ∈ preludeRoles, ∃ a bytes,
    committedDefaultRoleTable.addressOf? r = some a ∧ (a, bytes) ∈ committedRows := by
  intro r hr
  have h0 : (committedDefaultRoleTable.addressOf? r).any
      (fun a => committedPreludeList.any fun p => p.1 == a) = true :=
    List.all_eq_true.mp defaultTable_prelude_bool r hr
  cases hadr : committedDefaultRoleTable.addressOf? r with
  | none =>
    rw [hadr] at h0
    have e : false = true := h0
    cases e
  | some a =>
    rw [hadr] at h0
    have h1 : (committedPreludeList.any fun p => p.1 == a) = true := h0
    obtain ⟨p, hp, hpa⟩ := List.any_eq_true.mp h1
    have e : p.1 = a := beq_iff_eq.mp hpa
    subst e
    exact ⟨p.1, Ixon.serConstant p.2, rfl, (committedPrelude_rows p hp).1⟩

/-- **A table that pins the prelude binds each prelude role at the address of a committed
row**, so `AgreesCommitted` constrains a store at every pinned address. -/
theorem preludePinned_rows {t : Ix.Kernel.RoleTable} (h : PreludePinned t) :
    ∀ r ∈ preludeRoles, ∃ a bytes, t.addressOf? r = some a ∧ (a, bytes) ∈ committedRows := by
  obtain ⟨b₀, t₀, hdef, hadm, hpin⟩ := h
  have ht₀ : t₀ = committedDefaultRoleTable := admitBinding_committedDefault hdef hadm
  intro r hr
  obtain ⟨a, bytes, ha, hrow⟩ := defaultTable_prelude_rows r hr
  refine ⟨a, bytes, ?_, hrow⟩
  rw [hpin r hr, ht₀]
  exact ha

/-- The block of each decoded committed prelude record is a decoded committed prelude record
(decided). -/
theorem committedPrelude_owner_bool :
    committedPreludeList.all (fun e =>
      committedPreludeList.any fun q => q.1 == Ix.Cert.ownerOf e.1 e.2) = true := by
  decide +kernel

/-- **The block of a committed projection record is a committed record.** -/
theorem committedPrelude_owner : ∀ e ∈ committedPreludeList,
    ∃ q ∈ committedPreludeList, q.1 = Ix.Cert.ownerOf e.1 e.2 := by
  intro e he
  have h0 : (committedPreludeList.any fun q => q.1 == Ix.Cert.ownerOf e.1 e.2) = true :=
    List.all_eq_true.mp committedPrelude_owner_bool e he
  obtain ⟨q, hq, hqe⟩ := List.any_eq_true.mp h0
  exact ⟨q, hq, beq_iff_eq.mp hqe⟩

set_option maxRecDepth 8192 in
/-- **The default table binds every role.** -/
theorem defaultTable_allBound : AllBound committedDefaultRoleTable := by
  intro r
  cases r <;> decide +kernel

end IxVM.Refinement.ClosedFacts
