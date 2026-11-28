import IxCC.Rt.Rc.Gen.Proof.LiveMemory

/-! # Fully scanned cells

The pipeline allocates cells of `n` scanned fields and no scalar word (`CellLayout.ofFields n tag`,
`1 ≤ n ≤ 254`) until scalar fields are produced: their class `fieldsClass n` (classes 2–44) and
bytes `classBytes (fieldsClass n)` (at most 2,048), which are the bounded route's `smallClass n` and
`cellBytes n` below 32 fields, and the general invariant's `classOf`/`cellBytesOf` of a constructor
without scalar fields. -/

set_option autoImplicit false
namespace IxCC.Rt.Rc.Gen
open IxCC.Rt.Rc.Procs

/-- The class of a cell of `n` scanned fields and no scalar word. -/
def fieldsClass (n : Nat) : Nat := (classFor (1 + n)).getD 0

theorem ofFields_cls_fields {n tag : Nat} (h : n ≤ maxFields) :
    (CellLayout.ofFields n tag).cls? = some (fieldsClass n) := by
  have hs := classFor_total (w := 1 + n) (by omega)
    (by rw [maxCellWords_eq]; unfold maxFields at h; omega)
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hs
  simp [CellLayout.cls?, CellLayout.words, CellLayout.ofFields, fieldsClass, hc]

theorem ofFields_ok_fields {n tag : Nat} (h0 : 0 < n) (h : n ≤ maxFields) (ht : tag ≤ maxTag) :
    (CellLayout.ofFields n tag).ok = true := by
  have hc := ofFields_cls_fields (tag := tag) h
  simp only [CellLayout.ok, hc, Option.isSome_some, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq]
  simp only [CellLayout.ofFields]
  -- one goal per `omega` call: on a conjunction, `omega` uses a choice principle
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;> omega

/-- The pipeline's layout of a constructor of `fields` scanned fields is valid, in class
`fieldsClass fields`. -/
theorem ofFields_layout {fields tag : Nat} (positive : 0 < fields) (small : fields ≤ maxFields)
    (tagBound : tag ≤ maxTag) :
    (CellLayout.ofFields fields tag).ok = true ∧
      (CellLayout.ofFields fields tag).cls? = some (fieldsClass fields) :=
  ⟨ofFields_ok_fields positive small tagBound, ofFields_cls_fields small⟩

theorem fieldsClass_small {n : Nat} (h : n < 32) : fieldsClass n = smallClass n := by
  simp [fieldsClass, classFor_smallClass h]

theorem fieldsBytes_small {n : Nat} (h : n < 32) : classBytes (fieldsClass n) = cellBytes n := by
  rw [fieldsClass_small h, classBytes,
    classWords_small (by unfold smallClass; omega)]
  simp only [smallClass, cellBytes]
  omega

/-- `classFor`'s answer is a class of the table whose words hold the request (`classFor_spec`
without minimality, proved without a choice principle). -/
theorem classFor_some {w c : Nat} (h : classFor w = some c) :
    1 ≤ c ∧ c ≤ maxClass ∧ w ≤ classWords c := by
  unfold classFor at h
  cases w with
  | zero => simp at h
  | succ k =>
    simp only [Nat.succ_ne_zero, ite_false] at h
    have hfit := List.find?_some h
    simp only [decide_eq_true_eq] at hfit
    obtain ⟨i, hi, rfl⟩ := List.mem_range'.mp (List.mem_of_find?_eq_some h)
    unfold maxClass at hi ⊢
    -- one goal per `omega` call: on a conjunction, `omega` uses a choice principle
    exact ⟨by omega, by omega, hfit⟩

/-- The class of a valid layout is a class of the table, and its bytes hold the header and the
fields (`classOf_spec` and `cellBytesOf_le` without a choice principle). -/
theorem layoutOf_class {c : Fir.CtorInfo} (h : (layoutOf c).ok = true) :
    1 ≤ classOf c ∧ classOf c ≤ maxClass ∧ 8 * (1 + c.nobj + c.nscalar) ≤ cellBytesOf c := by
  obtain ⟨cls, hc⟩ := CellLayout.ok_cls h
  have hcls : classOf c = cls := by simp [classOf, hc]
  obtain ⟨h1, hm, hw⟩ := classFor_some hc
  simp only [CellLayout.words, layoutOf] at hw
  simp only [cellBytesOf, hcls]
  exact ⟨h1, hm, by omega⟩

/-- A class `fieldsClass n` that exists holds the header and the `n` fields. -/
theorem fieldsClass_fit {n : Nat} (h : 1 ≤ fieldsClass n) : 1 + n ≤ classWords (fieldsClass n) := by
  unfold fieldsClass at h ⊢
  cases hc : classFor (1 + n) with
  | none => simp [hc] at h
  | some c => simpa [hc] using (classFor_some hc).2.2

/-- A slot of class `fieldsClass n` holds the header and the `n` fields. -/
theorem fieldsClass_slot {cls n : Nat} (h : cls = fieldsClass n) (h1 : 1 ≤ cls) :
    8 * (n + 1) ≤ 8 * classWords cls := by
  subst h
  have := fieldsClass_fit h1
  omega

set_option maxRecDepth 8000 in
/-- The class of a cell of at most 254 scanned fields is at most 44. -/
theorem fieldsClass_le : ∀ n < maxFields + 1, fieldsClass n ≤ 44 := by
  decide

set_option maxRecDepth 8000 in
/-- The table's facts at every field count the pipeline allocates. -/
theorem fieldsClass_table : ∀ n < maxFields + 1, 0 < n →
    2 ≤ fieldsClass n ∧ fieldsClass n ≤ 44 ∧ 1 + n ≤ classWords (fieldsClass n) ∧
      classWords (fieldsClass n) ≤ 256 := by
  decide

/-- The class of a fully scanned cell is one of classes 2–44 (at most `maxClass`), and its bytes
hold the header and the fields, at most 2,048 bytes. -/
theorem fieldsClass_spec {n : Nat} (h0 : 0 < n) (h : n ≤ maxFields) :
    2 ≤ fieldsClass n ∧ fieldsClass n ≤ maxClass ∧ 8 * (1 + n) ≤ classBytes (fieldsClass n) ∧
      classBytes (fieldsClass n) ≤ 2048 := by
  obtain ⟨h2, h44, hw, hm⟩ := fieldsClass_table n (by omega) h0
  refine ⟨h2, by unfold maxClass; omega, ?_, ?_⟩ <;> unfold classBytes <;> omega

theorem layoutOf_fields {c : Fir.CtorInfo} (hs : c.nscalar = 0) :
    layoutOf c = CellLayout.ofFields c.nobj c.tag := by
  simp [layoutOf, CellLayout.ofFields, hs]

theorem classOf_fields {c : Fir.CtorInfo} (hs : c.nscalar = 0) (h : c.nobj ≤ maxFields) :
    classOf c = fieldsClass c.nobj := by
  simp [classOf, layoutOf_fields hs, ofFields_cls_fields (tag := c.tag) h]

theorem cellBytesOf_fields {c : Fir.CtorInfo} (hs : c.nscalar = 0) (h : c.nobj ≤ maxFields) :
    cellBytesOf c = classBytes (fieldsClass c.nobj) := by
  simp [cellBytesOf, classOf_fields hs h, classBytes]

end IxCC.Rt.Rc.Gen
