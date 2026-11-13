import IxCC.Recheck.Rc.Produce

/-! # Policy selection's linear form equals its list form

`Own.Plain.enrichFirContracts`, which RC policy selection (`selectRcPolicyForSrc`) and the
contract-aware canonical map (`Program.canonicalForSrc`) run, reads a key's function from the key
index (`keyIndex`, built once) and merges contract lists in one pass (`mergeContracts`,
`keepContracts`). `enrichFirContracts_eq_list` proves it equal to the list form
`enrichFirContractsList` (a key's function by `P.funList.find?`, rebuilt per call, and merges
index by index), which was its definition until 2026-11-13: the index gives the first function,
in id order, under each key (`keyIndex_getElem?`), and each one-pass merge is the indexed one
(`mergeContracts_eq`, `keepContracts_eq`). -/

set_option autoImplicit false

namespace IxCC.Own.Plain

open IxCC.Ixon

/-- The one-pass merge is the indexed merge. -/
theorem mergeContracts_eq : ∀ (n : Nat) (xs ys : List V3.BinderContract),
    mergeContracts n xs ys =
      (List.range n).map fun i => mergeBinderContract (xs.getD i {}) (ys.getD i {})
  | 0, _, _ => rfl
  | n + 1, xs, ys => by
    rw [mergeContracts, List.range_succ_eq_map, List.map_cons, List.map_map, mergeContracts_eq n]
    congr 1
    · cases xs <;> cases ys <;> rfl
    · apply List.map_congr_left
      intro i _
      cases xs <;> cases ys <;> rfl

/-- The one-pass selection is the indexed selection. -/
theorem keepContracts_eq : ∀ (keep : List Bool) (base : List V3.BinderContract),
    keepContracts keep base =
      ((List.range keep.length).zip keep).filterMap fun (i, k) =>
        if k then some (base.getD i {}) else none
  | [], _ => rfl
  | k :: ks, base => by
    rw [keepContracts, List.length_cons, List.range_succ_eq_map, List.zip_cons_cons,
      List.filterMap_cons, List.zip_map_left, List.filterMap_map, keepContracts_eq ks base.tail]
    have htail : (((List.range ks.length).zip ks).filterMap fun (p : Nat × Bool) =>
          if p.2 then some (base.tail.getD p.1 {}) else none) =
        ((List.range ks.length).zip ks).filterMap
          ((fun (p : Nat × Bool) => if p.2 then some (base.getD p.1 {}) else none) ∘
            Prod.map Nat.succ id) := by
      congr 1
      funext p
      cases base <;> rfl
    cases k
    · simpa using htail
    · cases base <;> simpa using htail

/-- **The key index gives `funList.find?`'s answer**: the first function, in id order, under a
key. -/
theorem keyIndex_getElem? (P : Fir.Program) (k : Key.GKey) :
    (keyIndex P)[k]? = (P.funList.find? fun (_, fd) => decide (fd.key = k)).map (·.2) := by
  unfold keyIndex
  generalize P.funList = l
  induction l with
  | nil => simp
  | cons x l ih =>
    obtain ⟨i, fd⟩ := x
    rw [List.foldr_cons, Std.HashMap.getElem?_insert, List.find?_cons]
    by_cases h : fd.key = k
    · simp [h]
    · have hb : (fd.key == k) = false := by simpa using h
      simp [hb, h, ih]

/-- `progKeyContracts` through any lookup that gives `funList.find?`'s answer. -/
theorem progKeyContractsBy_eq (src : Src.Program) (P : Fir.Program)
    (look : Key.GKey → Option Fir.Fun)
    (hlook : ∀ k, look k = (P.funList.find? fun (_, fd) => decide (fd.key = k)).map (·.2)) :
    ∀ k, progKeyContractsBy src look k = progKeyContracts src P k
  | .spec g args => by
    simp only [progKeyContractsBy, progKeyContracts, progKeyContractsBy_eq src P look hlook g]
  | .worker g keep => by
    simp only [progKeyContractsBy, progKeyContracts, progKeyContractsBy_eq src P look hlook g,
      keepContracts_eq]
  | .const c p => by
    simp only [progKeyContractsBy, progKeyContracts, hlook]
    cases List.find? _ _ <;> simp [mergeContracts_eq]
  | .byName c p => by
    simp only [progKeyContractsBy, progKeyContracts, hlook]
    cases List.find? _ _ <;> simp [mergeContracts_eq]
  | .recStar c p => by
    simp only [progKeyContractsBy, progKeyContracts, hlook]
    cases List.find? _ _ <;> simp [mergeContracts_eq]
  | .wrapper h p => by
    simp only [progKeyContractsBy, progKeyContracts, hlook]
    cases List.find? _ _ <;> simp [mergeContracts_eq]
  | .lam g path => by
    simp only [progKeyContractsBy, progKeyContracts, hlook]
    cases List.find? _ _ <;> simp [mergeContracts_eq]
  | .dispatch n => by
    simp only [progKeyContractsBy, progKeyContracts, hlook]
    cases List.find? _ _ <;> simp [mergeContracts_eq]
  | .entry g n => by
    simp only [progKeyContractsBy, progKeyContracts, hlook]
    cases List.find? _ _ <;> simp [mergeContracts_eq]

/-- `progKeyResult` through any lookup that gives `funList.find?`'s answer. -/
theorem progKeyResultBy_eq (src : Src.Program) (P : Fir.Program)
    (look : Key.GKey → Option Fir.Fun)
    (hlook : ∀ k, look k = (P.funList.find? fun (_, fd) => decide (fd.key = k)).map (·.2)) :
    ∀ k, progKeyResultBy src look k = progKeyResult src P k
  | .spec g _ => by simp only [progKeyResultBy, progKeyResult, progKeyResultBy_eq src P look hlook g]
  | .worker g _ => by simp only [progKeyResultBy, progKeyResult, progKeyResultBy_eq src P look hlook g]
  | .lam g _ => by simp only [progKeyResultBy, progKeyResult, progKeyResultBy_eq src P look hlook g]
  | .const c p => by
    simp only [progKeyResultBy, progKeyResult, hlook]
    cases List.find? _ _ <;> rfl
  | .byName c p => by
    simp only [progKeyResultBy, progKeyResult, hlook]
    cases List.find? _ _ <;> rfl
  | .recStar c p => by
    simp only [progKeyResultBy, progKeyResult, hlook]
    cases List.find? _ _ <;> rfl
  | .wrapper h p => by
    simp only [progKeyResultBy, progKeyResult, hlook]
    cases List.find? _ _ <;> rfl
  | .dispatch n => by
    simp only [progKeyResultBy, progKeyResult, hlook]
    cases List.find? _ _ <;> rfl
  | .entry g n => by
    simp only [progKeyResultBy, progKeyResult, hlook]
    cases List.find? _ _ <;> rfl

/-- **Policy selection's linear form is its list form.** -/
theorem enrichFirContracts_eq_list (src : Src.Program) (P : Fir.Program) :
    enrichFirContracts src P = enrichFirContractsList src P := by
  have hc := progKeyContractsBy_eq src P (fun k => (keyIndex P)[k]?) (keyIndex_getElem? P)
  have hr := progKeyResultBy_eq src P (fun k => (keyIndex P)[k]?) (keyIndex_getElem? P)
  simp only [enrichFirContracts, enrichFirContractsList, hc, hr, mergeContracts_eq]

/-- RC policy selection, restated over the list form. -/
theorem selectRcPolicyForSrc_eq_list (src : Src.Program) (P : Fir.Program) :
    selectRcPolicyForSrc src P = selectRcPolicy (enrichFirContractsList src P) := by
  rw [selectRcPolicyForSrc, enrichFirContracts_eq_list]

end IxCC.Own.Plain
