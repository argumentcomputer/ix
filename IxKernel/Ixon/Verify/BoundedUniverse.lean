import IxKernel.Ixon.Bounded.Universe
import IxKernel.Ixon.Verify.Framing

namespace Ixon.Verify.BoundedUniverse

open Ixon

@[simp] theorem nodeCount_addSucc (count : Nat) (base : Univ) :
    (base.addSucc count).nodeCount = base.nodeCount + count := by
  induction count with
  | zero => rfl
  | succ count ih => simp [Univ.addSucc, Univ.nodeCount, ih, Nat.add_assoc]

theorem nodeCount_pos (u : Univ) : 0 < u.nodeCount := by
  cases u <;> simp [Univ.nodeCount]

theorem nodeCount_succBase (u : Univ) :
    u.succBase.nodeCount + u.succCountNat = u.nodeCount := by
  induction u with
  | succ u ih => simp [Univ.succBase, Univ.succCountNat, Univ.nodeCount]; omega
  | zero => rfl
  | max _ _ => rfl
  | imax _ _ => rfl
  | var _ => rfl

/-- Successful bounded reads preserve the production value and exact state,
and spend precisely one unit for each expanded universe constructor. -/
theorem getUnivFuel_spec (fuel budget : Nat) (start finish : GetState)
    (u : Univ) (remaining : Nat)
    (h : Bounded.getUnivFuel fuel budget start = .ok (u, remaining) finish) :
    Ixon.getUnivFuel fuel start = .ok u finish ∧
      remaining + u.nodeCount = budget := by
  induction fuel generalizing budget start finish u remaining with
  | zero => cases h
  | succ fuel ih =>
    simp only [Bounded.getUnivFuel, bind, EStateM.bind] at h
    cases readTag : getTagN 2 start with
    | error reason state => simp [readTag] at h
    | ok tag state =>
      simp only [readTag] at h
      simp only [Ixon.getUnivFuel, bind, EStateM.bind, readTag]
      unfold Bounded.getUnivFromTag at h
      split at h
      next chargeFits =>
        split at h
        next flagZero =>
          split at h
          next sizeZero =>
            simp only [pure, EStateM.pure, EStateM.Result.ok.injEq,
              Prod.mk.injEq] at h
            rcases h with ⟨⟨rfl, rfl⟩, rfl⟩
            constructor
            · simp [Ixon.getUnivFromTag, flagZero, sizeZero,
                pure, EStateM.pure]
            · simp_all [Univ.nodeCount, Bounded.univTagCharge]
          next sizeNonzero =>
            simp only [bind, EStateM.bind] at h
            split at h
            next value childState childRead =>
              obtain ⟨base, left⟩ := value
              simp only [pure, EStateM.pure, EStateM.Result.ok.injEq,
                Prod.mk.injEq] at h
              rcases h with ⟨⟨rfl, rfl⟩, rfl⟩
              obtain ⟨same, spent⟩ := ih _ _ _ _ _ childRead
              constructor
              · simp [Ixon.getUnivFromTag, flagZero, sizeNonzero,
                  bind, EStateM.bind, same, pure, EStateM.pure]
              · simp_all [nodeCount_addSucc, Bounded.univTagCharge]
                omega
            next => cases h
        next flagMax =>
          simp only [bind, EStateM.bind] at h
          split at h
          next value leftState leftRead =>
            obtain ⟨left, leftBudget⟩ := value
            split at h
            next value rightState rightRead =>
              obtain ⟨right, rightBudget⟩ := value
              simp only [pure, EStateM.pure, EStateM.Result.ok.injEq,
                Prod.mk.injEq] at h
              rcases h with ⟨⟨rfl, rfl⟩, rfl⟩
              obtain ⟨sameLeft, spentLeft⟩ := ih _ _ _ _ _ leftRead
              obtain ⟨sameRight, spentRight⟩ := ih _ _ _ _ _ rightRead
              constructor
              · simp [Ixon.getUnivFromTag, flagMax, bind, EStateM.bind,
                  sameLeft, sameRight, pure, EStateM.pure]
              · simp_all [Univ.nodeCount, Bounded.univTagCharge]
                omega
            next => cases h
          next => cases h
        next flagIMax =>
          simp only [bind, EStateM.bind] at h
          split at h
          next value leftState leftRead =>
            obtain ⟨left, leftBudget⟩ := value
            split at h
            next value rightState rightRead =>
              obtain ⟨right, rightBudget⟩ := value
              simp only [pure, EStateM.pure, EStateM.Result.ok.injEq,
                Prod.mk.injEq] at h
              rcases h with ⟨⟨rfl, rfl⟩, rfl⟩
              obtain ⟨sameLeft, spentLeft⟩ := ih _ _ _ _ _ leftRead
              obtain ⟨sameRight, spentRight⟩ := ih _ _ _ _ _ rightRead
              constructor
              · simp [Ixon.getUnivFromTag, flagIMax, bind, EStateM.bind,
                  sameLeft, sameRight, pure, EStateM.pure]
              · simp_all [Univ.nodeCount, Bounded.univTagCharge]
                omega
            next => cases h
          next => cases h
        next flagVar =>
          simp only [pure, EStateM.pure, EStateM.Result.ok.injEq,
            Prod.mk.injEq] at h
          rcases h with ⟨⟨rfl, rfl⟩, rfl⟩
          constructor
          · simp [Ixon.getUnivFromTag, flagVar, pure, EStateM.pure]
          · simp_all [Univ.nodeCount, Bounded.univTagCharge]
        next => cases h
      next => cases h

/-- Every successful production read also succeeds with a sufficient node
budget. The budget cannot silently narrow coverage within its stated limit. -/
theorem getUnivFuel_complete (fuel budget : Nat) (start finish : GetState)
    (u : Univ)
    (h : Ixon.getUnivFuel fuel start = .ok u finish)
    (fits : u.nodeCount ≤ budget) :
    Bounded.getUnivFuel fuel budget start =
      .ok (u, budget - u.nodeCount) finish := by
  induction fuel generalizing budget start finish u with
  | zero => cases h
  | succ fuel ih =>
    simp only [Ixon.getUnivFuel, bind, EStateM.bind] at h
    cases readTag : getTagN 2 start with
    | error reason state => simp [readTag] at h
    | ok tag state =>
      simp only [readTag] at h
      simp only [Bounded.getUnivFuel, bind, EStateM.bind, readTag]
      by_cases flagZero : tag.flag = 0
      · simp only [Ixon.getUnivFromTag, flagZero] at h
        split at h
        next sizeZero =>
          have sizeEq : tag.value = 0 := by simpa using sizeZero
          simp only [pure, EStateM.pure, EStateM.Result.ok.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          have chargeFits : 1 ≤ budget := fits
          simp [Bounded.getUnivFromTag, Bounded.univTagCharge, flagZero,
            sizeEq, chargeFits, Univ.nodeCount, pure, EStateM.pure]
        next sizeNonzero =>
          have sizeNe : tag.value ≠ 0 := by simpa using sizeNonzero
          simp only [bind, EStateM.bind] at h
          split at h
          next base childState childRead =>
            simp only [pure, EStateM.pure, EStateM.Result.ok.injEq] at h
            rcases h with ⟨rfl, rfl⟩
            have chargeFits : tag.value.toNat ≤ budget := by
              simp only [nodeCount_addSucc] at fits
              omega
            have childFits : base.nodeCount ≤ budget - tag.value.toNat := by
              simp only [nodeCount_addSucc] at fits
              omega
            have child := ih (budget - tag.value.toNat) _ _ _ childRead childFits
            simp [Bounded.getUnivFromTag, Bounded.univTagCharge, flagZero,
              sizeNe, chargeFits, bind, EStateM.bind, child, pure, EStateM.pure] <;> omega
          next => cases h
      · by_cases flagMax : tag.flag = 1
        · simp only [Ixon.getUnivFromTag, flagMax] at h
          exact maxStep fuel ih budget state finish u tag flagMax h fits
        · by_cases flagIMax : tag.flag = 2
          · simp only [Ixon.getUnivFromTag, flagIMax] at h
            exact imaxStep fuel ih budget state finish u tag flagIMax h fits
          · by_cases flagVar : tag.flag = 3
            · simp only [Ixon.getUnivFromTag, flagVar] at h
              simp only [pure, EStateM.pure, EStateM.Result.ok.injEq] at h
              rcases h with ⟨rfl, rfl⟩
              have chargeFits : 1 ≤ budget := fits
              simp [Bounded.getUnivFromTag, Bounded.univTagCharge, flagVar,
                chargeFits, Univ.nodeCount, pure, EStateM.pure]
            · simp_all [Ixon.getUnivFromTag]
              cases h
where
  maxStep (fuel : Nat)
      (ih : ∀ (budget : Nat) (start finish : GetState) (u : Univ),
        Ixon.getUnivFuel fuel start = .ok u finish →
        u.nodeCount ≤ budget →
        Bounded.getUnivFuel fuel budget start = .ok (u, budget - u.nodeCount) finish)
      (budget : Nat) (state finish : GetState) (u : Univ) (tag : TagN)
      (flagMax : tag.flag = 1)
      (h : (do
        let left ← Ixon.getUnivFuel fuel
        let right ← Ixon.getUnivFuel fuel
        pure (Univ.max left right)) state = .ok u finish)
      (fits : u.nodeCount ≤ budget) :
      Bounded.getUnivFromTag (Bounded.getUnivFuel fuel) budget tag state =
        .ok (u, budget - u.nodeCount) finish := by
        simp only [bind, EStateM.bind] at h
        split at h
        next left leftState leftRead =>
          split at h
          next right rightState rightRead =>
            simp only [pure, EStateM.pure, EStateM.Result.ok.injEq] at h
            rcases h with ⟨rfl, rfl⟩
            have chargeFits : 1 ≤ budget := by simp only [Univ.nodeCount] at fits; omega
            have leftFits : left.nodeCount ≤ budget - 1 := by
              simp only [Univ.nodeCount] at fits
              omega
            have rightFits : right.nodeCount ≤ budget - 1 - left.nodeCount := by
              simp only [Univ.nodeCount] at fits
              omega
            have leftResult := ih (budget - 1) _ _ _ leftRead leftFits
            have rightResult := ih (budget - 1 - left.nodeCount) _ _ _ rightRead rightFits
            simp [Bounded.getUnivFromTag, Bounded.univTagCharge, flagMax,
              chargeFits, bind, EStateM.bind, leftResult, rightResult, pure,
              EStateM.pure, Univ.nodeCount] <;> omega
          next => cases h
        next => cases h
  imaxStep (fuel : Nat)
      (ih : ∀ (budget : Nat) (start finish : GetState) (u : Univ),
        Ixon.getUnivFuel fuel start = .ok u finish →
        u.nodeCount ≤ budget →
        Bounded.getUnivFuel fuel budget start = .ok (u, budget - u.nodeCount) finish)
      (budget : Nat) (state finish : GetState) (u : Univ) (tag : TagN)
      (flagIMax : tag.flag = 2)
      (h : (do
        let left ← Ixon.getUnivFuel fuel
        let right ← Ixon.getUnivFuel fuel
        pure (Univ.imax left right)) state = .ok u finish)
      (fits : u.nodeCount ≤ budget) :
      Bounded.getUnivFromTag (Bounded.getUnivFuel fuel) budget tag state =
        .ok (u, budget - u.nodeCount) finish := by
        simp only [bind, EStateM.bind] at h
        split at h
        next left leftState leftRead =>
          split at h
          next right rightState rightRead =>
            simp only [pure, EStateM.pure, EStateM.Result.ok.injEq] at h
            rcases h with ⟨rfl, rfl⟩
            have chargeFits : 1 ≤ budget := by simp only [Univ.nodeCount] at fits; omega
            have leftFits : left.nodeCount ≤ budget - 1 := by
              simp only [Univ.nodeCount] at fits
              omega
            have rightFits : right.nodeCount ≤ budget - 1 - left.nodeCount := by
              simp only [Univ.nodeCount] at fits
              omega
            have leftResult := ih (budget - 1) _ _ _ leftRead leftFits
            have rightResult := ih (budget - 1 - left.nodeCount) _ _ _ rightRead rightFits
            simp [Bounded.getUnivFromTag, Bounded.univTagCharge, flagIMax,
              chargeFits, bind, EStateM.bind, leftResult, rightResult, pure,
              EStateM.pure, Univ.nodeCount] <;> omega
          next => cases h
        next => cases h

theorem getUniv_spec (budget : Nat) (start finish : GetState)
    (u : Univ) (remaining : Nat)
    (h : Bounded.getUniv budget start = .ok (u, remaining) finish) :
    Ixon.getUniv start = .ok u finish ∧ remaining + u.nodeCount = budget := by
  change Bounded.getUnivFuel (start.bytes.size - start.idx + 1) budget start = _ at h
  exact getUnivFuel_spec _ _ _ _ _ _ h

theorem getUniv_reads (u : Univ) (wf : u.wireWF) (budget : Nat)
    (fits : u.nodeCount ≤ budget) :
    Codec.Reads (Bounded.getUniv budget)
      (Codec.Univ.wireEncode u) (u, budget - u.nodeCount) := by
  intro before after
  change Bounded.getUnivFuel _ budget _ = _
  apply getUnivFuel_complete _ _ _ _ _ _ fits
  exact Codec.Univ.getUniv_reads u wf before after

theorem reads_fst {decoder : GetM (α × β)} {bytes : ByteArray} {value : α × β}
    (h : Codec.Reads decoder bytes value) :
    Codec.Reads (Prod.fst <$> decoder) bytes value.1 := by
  intro before after
  change (EStateM.map Prod.fst decoder) _ = _
  simp [EStateM.map, h before after]

/-- Full-buffer round trip with independently stated byte and node limits. -/
theorem deUniv_serUniv (u : Univ) (wf : u.wireWF) (maxBytes maxNodes : Nat)
    (bytesFit : (serUniv u).size ≤ maxBytes) (nodesFit : u.nodeCount ≤ maxNodes) :
    Bounded.deUniv maxBytes maxNodes (serUniv u) = .ok u := by
  rw [Bounded.deUniv, ite_eq_left bytesFit, Codec.Univ.serUniv_eq_wireEncode u wf]
  exact (reads_fst (getUniv_reads u wf maxNodes nodesFit)).runGetExact

/-- A successful bounded universe decode respects both limits and agrees
with exact production decoding of the entire supplied buffer. -/
theorem deUniv_spec (maxBytes maxNodes : Nat) (bytes : ByteArray) (u : Univ)
    (h : Bounded.deUniv maxBytes maxNodes bytes = .ok u) :
    bytes.size ≤ maxBytes ∧ u.nodeCount ≤ maxNodes ∧
      Ixon.deUniv bytes = .ok u := by
  unfold Bounded.deUniv at h
  split at h
  next bytesFit =>
    obtain ⟨finish, decoded, consumed⟩ := runGetExact_complete h
    change (EStateM.map Prod.fst (Bounded.getUniv maxNodes)) { bytes } = _ at decoded
    cases read : Bounded.getUniv maxNodes { bytes } with
    | error reason state => simp [EStateM.map, read] at decoded
    | ok value state =>
      obtain ⟨value, remaining⟩ := value
      simp only [EStateM.map, read, EStateM.Result.ok.injEq] at decoded
      rcases decoded with ⟨rfl, rfl⟩
      obtain ⟨same, spent⟩ := getUniv_spec maxNodes _ _ _ remaining read
      refine ⟨bytesFit, by omega, ?_⟩
      simp [Ixon.deUniv, runGetExact, EStateM.run, same, consumed]
  next => cases h

theorem deUniv_noTrailing (u : Univ) (wf : u.wireWF) (maxBytes maxNodes : Nat)
    (nodesFit : u.nodeCount ≤ maxNodes) (suffix : ByteArray) (nonempty : suffix.size ≠ 0) :
    (Bounded.deUniv maxBytes maxNodes (serUniv u ++ suffix)).isOk = false := by
  unfold Bounded.deUniv
  split
  · rw [Codec.Univ.serUniv_eq_wireEncode u wf]
    exact (reads_fst (getUniv_reads u wf maxNodes nodesFit)).noTrailing suffix nonempty
  · rfl

theorem wireWF_of_nodeCount (u : Univ) (fits : u.nodeCount < UInt64.size) : u.wireWF := by
  induction u with
  | zero => trivial
  | var _ => trivial
  | succ u ih =>
    have count := nodeCount_succBase (Univ.succ u)
    refine ⟨by omega, ih ?_⟩
    simp only [Univ.nodeCount] at fits
    omega
  | max left right ihLeft ihRight =>
    simp only [Univ.nodeCount] at fits
    exact ⟨ihLeft (by omega), ihRight (by omega)⟩
  | imax left right ihLeft ihRight =>
    simp only [Univ.nodeCount] at fits
    exact ⟨ihLeft (by omega), ihRight (by omega)⟩

/-- A node limit below the wire count capacity also establishes the complete
structural wire invariant, including every compressed successor prefix. -/
theorem deUniv_wireWF (maxBytes maxNodes : Nat) (bytes : ByteArray) (u : Univ)
    (capacity : maxNodes < UInt64.size)
    (h : Bounded.deUniv maxBytes maxNodes bytes = .ok u) : u.wireWF :=
  wireWF_of_nodeCount u (Nat.lt_of_le_of_lt (deUniv_spec _ _ _ _ h).2.1 capacity)

end Ixon.Verify.BoundedUniverse
