import IxKernel.Ixon.Bounded.Constant
import IxKernel.Ixon.Verify.BoundedUniverse

namespace Ixon.Verify.BoundedConstant

open Ixon

@[simp] theorem univNodes_empty : Bounded.univNodes #[] = 0 := rfl

@[simp] theorem univNodes_singleton (u : Univ) : Bounded.univNodes #[u] = u.nodeCount := by
  simp [Bounded.univNodes]

@[simp] theorem univNodes_append (left right : Array Univ) :
    Bounded.univNodes (left ++ right) = Bounded.univNodes left + Bounded.univNodes right := by
  simp [Bounded.univNodes, List.sum_append]

theorem getArray_succ (decoder : GetM α) (count : Nat) :
    getArray decoder (count + 1) = do
      let value ← decoder
      let rest ← getArray decoder count
      return #[value] ++ rest :=
  Codec.ConstantTables.getMany_succ_head decoder count

theorem getArray_zero (decoder : GetM α) : getArray decoder 0 = pure #[] := by
  simp [getArray]

/-- The tail loop preserves the production table read, appends precisely
those entries to its accumulator, and spends their aggregate node count. -/
theorem getUnivArray_go_spec (count budget : Nat) (acc : Array Univ)
    (start finish : GetState) (values : Array Univ) (remaining : Nat)
    (h : Bounded.getUnivArrayLoop count budget acc start = .ok (values, remaining) finish) :
    ∃ added, getArray Ixon.getUniv count start = .ok added finish ∧
      values = acc ++ added ∧ remaining + Bounded.univNodes added = budget := by
  induction count generalizing budget acc start finish values remaining with
  | zero =>
    simp only [Bounded.getUnivArrayLoop, pure, EStateM.pure,
      EStateM.Result.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨⟨rfl, rfl⟩, rfl⟩
    exact ⟨#[], by simp [getArray_zero, pure, EStateM.pure], by simp, by simp⟩
  | succ count ih =>
    simp only [Bounded.getUnivArrayLoop, bind, EStateM.bind] at h
    cases read : Bounded.getUniv budget start with
    | error reason state => simp [read] at h
    | ok value state =>
      obtain ⟨value, restBudget⟩ := value
      simp only [read] at h
      obtain ⟨same, spent⟩ := BoundedUniverse.getUniv_spec budget _ _ _ _ read
      obtain ⟨added, readAdded, appended, spentAdded⟩ := ih _ _ _ _ _ _ h
      refine ⟨#[value] ++ added, ?_, ?_, ?_⟩
      · simp [getArray_succ, bind, EStateM.bind, same, readAdded, pure, EStateM.pure]
      · simpa using appended
      · simp only [univNodes_append, univNodes_singleton]
        omega

theorem getUnivArray_spec (count budget : Nat) (start finish : GetState)
    (values : Array Univ) (remaining : Nat)
    (h : Bounded.getUnivArray count budget start = .ok (values, remaining) finish) :
    getArray Ixon.getUniv count start = .ok values finish ∧
      remaining + Bounded.univNodes values = budget := by
  obtain ⟨added, read, appended, spent⟩ := getUnivArray_go_spec count budget #[] _ _ _ _ h
  simp only [Array.empty_append] at appended
  subst values
  exact ⟨read, spent⟩

/-- The expansion budget does not reject a successful production table read
whose aggregate universe size fits, for any existing accumulator. -/
theorem getUnivArray_go_complete (count budget : Nat) (acc : Array Univ)
    (start finish : GetState) (values : Array Univ)
    (h : getArray Ixon.getUniv count start = .ok values finish)
    (fits : Bounded.univNodes values ≤ budget) :
    Bounded.getUnivArrayLoop count budget acc start =
      .ok (acc ++ values, budget - Bounded.univNodes values) finish := by
  induction count generalizing budget acc start finish values with
  | zero =>
    simp only [getArray_zero, pure, EStateM.pure, EStateM.Result.ok.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    simp [Bounded.getUnivArrayLoop, pure, EStateM.pure]
  | succ count ih =>
    rw [getArray_succ] at h
    simp only [bind, EStateM.bind] at h
    cases readHead : Ixon.getUniv start with
    | error reason state => simp [readHead] at h
    | ok head headState =>
      simp only [readHead] at h
      cases readTail : getArray Ixon.getUniv count headState with
      | error reason state => simp [readTail] at h
      | ok tail tailState =>
        simp only [readTail, pure, EStateM.pure, EStateM.Result.ok.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        simp only [univNodes_append, univNodes_singleton] at fits
        have headFits : head.nodeCount ≤ budget := by omega
        have tailFits : Bounded.univNodes tail ≤ budget - head.nodeCount := by omega
        have boundedHead : Bounded.getUniv budget start =
            .ok (head, budget - head.nodeCount) headState :=
          BoundedUniverse.getUnivFuel_complete _ _ _ _ _ readHead headFits
        have boundedTail := ih (budget - head.nodeCount) (acc.push head) _ _ _ readTail tailFits
        simp [Bounded.getUnivArrayLoop, bind, EStateM.bind, boundedHead, boundedTail,
          Nat.sub_sub]

theorem getUnivArray_complete (count budget : Nat) (start finish : GetState)
    (values : Array Univ)
    (h : getArray Ixon.getUniv count start = .ok values finish)
    (fits : Bounded.univNodes values ≤ budget) :
    Bounded.getUnivArray count budget start =
      .ok (values, budget - Bounded.univNodes values) finish := by
  simpa [Bounded.getUnivArray] using getUnivArray_go_complete count budget #[] _ _ _ h fits

/-- A proof-only view of the shared prefix; the production grammar does not
allocate this tuple. -/
def getPrefix : GetM (ConstantInfo × Array Expr × Array Address × Nat) := do
  let info ← getConstantInfo
  let sharingCount ← getTagN 0
  let sharing ← getArray getExpr sharingCount.value.toNat
  let refsCount ← getTagN 0
  let refs ← getArray Serialize.get refsCount.value.toNat
  let univsCount ← getTagN 0
  return (info, sharing, refs, univsCount.value.toNat)

theorem getConstantWithUnivs_eq (readUnivs : Nat → GetM (Array Univ)) :
    getConstantWithUnivs readUnivs = do
      let (info, sharing, refs, count) ← getPrefix
      let univs ← readUnivs count
      return ⟨info, sharing, refs, univs⟩ := by
  unfold getConstantWithUnivs getPrefix
  simp

theorem getConstantWithUnivs_ok_iff (readUnivs : Nat → GetM (Array Univ))
    (start finish : GetState) (constant : Constant) :
    getConstantWithUnivs readUnivs start = .ok constant finish ↔
      ∃ count middle,
        getPrefix start = .ok (constant.info, constant.sharing, constant.refs, count) middle ∧
        readUnivs count middle = .ok constant.univs finish := by
  rw [getConstantWithUnivs_eq]
  constructor
  · intro h
    simp only [bind, EStateM.bind] at h
    cases prefixRead : getPrefix start with
    | error reason state => simp [prefixRead] at h
    | ok prefixValue middle =>
      obtain ⟨info, sharing, refs, count⟩ := prefixValue
      simp only [prefixRead] at h
      cases univsRead : readUnivs count middle with
      | error reason state => simp [univsRead] at h
      | ok univs state =>
        simp only [univsRead, pure, EStateM.pure, EStateM.Result.ok.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        exact ⟨count, middle, rfl, univsRead⟩
  · rintro ⟨count, middle, prefixRead, univsRead⟩
    simp [bind, EStateM.bind, prefixRead, univsRead, pure, EStateM.pure]

/-- Bounded record reads retain the production result and cursor while
enforcing one aggregate limit for the entire universe table. -/
theorem getConstant_spec (budget : Nat) (start finish : GetState) (constant : Constant)
    (h : Bounded.getConstant budget start = .ok constant finish) :
    Ixon.getConstant start = .ok constant finish ∧
      Bounded.univNodes constant.univs ≤ budget := by
  obtain ⟨count, middle, prefixRead, univsRead⟩ :=
    (getConstantWithUnivs_ok_iff _ start finish constant).mp h
  change (EStateM.map Prod.fst (Bounded.getUnivArray count budget)) middle = _ at univsRead
  cases read : Bounded.getUnivArray count budget middle with
  | error reason state => simp [EStateM.map, read] at univsRead
  | ok value state =>
    obtain ⟨univs, remaining⟩ := value
    simp only [EStateM.map, read, EStateM.Result.ok.injEq] at univsRead
    rcases univsRead with ⟨rfl, rfl⟩
    obtain ⟨same, spent⟩ := getUnivArray_spec count budget _ _ _ _ read
    refine ⟨?_, by omega⟩
    exact (getConstantWithUnivs_ok_iff _ start _ constant).mpr
      ⟨count, middle, prefixRead, same⟩

/-- A successful production record read remains accepted whenever the whole
universe table, rather than just each individual entry, fits the limit. -/
theorem getConstant_complete (budget : Nat) (start finish : GetState) (constant : Constant)
    (h : Ixon.getConstant start = .ok constant finish)
    (fits : Bounded.univNodes constant.univs ≤ budget) :
    Bounded.getConstant budget start = .ok constant finish := by
  obtain ⟨count, middle, prefixRead, univsRead⟩ :=
    (getConstantWithUnivs_ok_iff _ start finish constant).mp h
  have bounded := getUnivArray_complete count budget _ _ _ univsRead fits
  apply (getConstantWithUnivs_ok_iff _ start finish constant).mpr
  refine ⟨count, middle, prefixRead, ?_⟩
  change (EStateM.map Prod.fst (Bounded.getUnivArray count budget)) middle = _
  simp [EStateM.map, bounded]

theorem deConstant_spec (maxBytes maxUnivNodes : Nat) (bytes : ByteArray) (constant : Constant)
    (h : Bounded.deConstant maxBytes maxUnivNodes bytes = .ok constant) :
    bytes.size ≤ maxBytes ∧ Bounded.univNodes constant.univs ≤ maxUnivNodes ∧
      deConstantExact bytes = .ok constant := by
  unfold Bounded.deConstant at h
  split at h
  next bytesFit =>
    obtain ⟨finish, read, consumed⟩ := runGetExact_complete h
    obtain ⟨same, spent⟩ := getConstant_spec maxUnivNodes _ _ _ read
    refine ⟨bytesFit, spent, ?_⟩
    simp [deConstantExact, runGetExact, EStateM.run, same, consumed]
  next => cases h

theorem deConstant_complete (maxBytes maxUnivNodes : Nat) (bytes : ByteArray) (constant : Constant)
    (h : deConstantExact bytes = .ok constant)
    (bytesFit : bytes.size ≤ maxBytes) (nodesFit : Bounded.univNodes constant.univs ≤ maxUnivNodes) :
    Bounded.deConstant maxBytes maxUnivNodes bytes = .ok constant := by
  obtain ⟨finish, read, consumed⟩ := runGetExact_complete h
  have bounded := getConstant_complete maxUnivNodes _ _ _ read nodesFit
  simp [Bounded.deConstant, bytesFit, runGetExact, EStateM.run, bounded, consumed]

/-- The exact decoder's successful domain is precisely production decoding
intersected with its two stated limits. -/
theorem deConstant_ok_iff (maxBytes maxUnivNodes : Nat) (bytes : ByteArray) (constant : Constant) :
    Bounded.deConstant maxBytes maxUnivNodes bytes = .ok constant ↔
      bytes.size ≤ maxBytes ∧ Bounded.univNodes constant.univs ≤ maxUnivNodes ∧
        deConstantExact bytes = .ok constant :=
  ⟨deConstant_spec _ _ _ _, fun ⟨bytesFit, nodesFit, read⟩ =>
    deConstant_complete _ _ _ _ read bytesFit nodesFit⟩

theorem deConstant_serConstant (constant : Constant) (wf : constant.wireWF)
    (maxBytes maxUnivNodes : Nat) (bytesFit : (serConstant constant).size ≤ maxBytes)
    (nodesFit : Bounded.univNodes constant.univs ≤ maxUnivNodes) :
    Bounded.deConstant maxBytes maxUnivNodes (serConstant constant) = .ok constant :=
  deConstant_complete _ _ _ _ (deConstantExact_serConstant constant wf) bytesFit nodesFit

theorem deConstant_noTrailing (constant : Constant) (wf : constant.wireWF)
    (maxBytes maxUnivNodes : Nat) (suffix : ByteArray) (nonempty : suffix.size ≠ 0) :
    (Bounded.deConstant maxBytes maxUnivNodes (serConstant constant ++ suffix)).isOk = false := by
  cases read : Bounded.deConstant maxBytes maxUnivNodes (serConstant constant ++ suffix) with
  | error _ => rfl
  | ok value =>
    have same := (deConstant_spec _ _ _ _ read).2.2
    have rejected := deConstantExact_noTrailing constant wf suffix nonempty
    simp [same] at rejected
    cases rejected

end Ixon.Verify.BoundedConstant
