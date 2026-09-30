import Compilatrix.Lam.Erase
import Compilatrix.Lam.Erase.Proof.Layout
import Compilatrix.Src.Proof.NatMap

/-! # `progWF` decides `ProgWF`

`progWF_iff`: erasure's check of the declarations (`Input.progWF`) holds
exactly when the structural facts its correctness proof assumes
(`ProgWF`) do; `erase_progWF`: a successful erasure passed the check. So
`erase_correct` needs no premise about the declarations (M2.2). -/

set_option autoImplicit false

namespace Compilatrix.Lam.Erase.Proof

open Compilatrix.Src (CId)

variable {I : Input}

theorem ctorInfo?_eq {c ind : CId} {i np nf : Nat} :
    I.ctorInfo? c = some (ind, i, np, nf) ↔
      ∃ sf lv ty, I.decl? c = some (.ctor sf lv ind i np nf ty) := by
  unfold Input.ctorInfo?
  constructor
  · intro h
    split at h
    · next sf lv ind' cidx np' nf' ty hd =>
      cases h
      exact ⟨sf, lv, ty, hd⟩
    · cases h
  · rintro ⟨sf, lv, ty, hd⟩
    rw [hd]

/-- The parts of the check. -/
theorem progWF_parts (h : I.progWF = true) :
    (∀ c d, I.decl? c = some d → I.declWF c d = true) ∧ I.natPinsOk = true ∧
      I.zeroPinOk = true ∧ I.boolPinsOk = true ∧ I.decOtherOk = true ∧
      I.ctorIdxOk I.known.decIsFalse 0 = true ∧ I.ctorIdxOk I.known.decIsTrue 1 = true := by
  unfold Input.progWF at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hall, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨fun c d hd => ?_, h1, h2, h3, h4, h5, h6⟩
  have hd' := hd
  unfold Input.decl? at hd'
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.1 hd'
  have := List.all_eq_true.1 hall (c, e) (Src.NatMap.mem_toList he)
  dsimp only at this
  rw [hd] at this
  exact this

/-- **The check is sound**: it establishes `ProgWF`. -/
theorem progWF_sound (h : I.progWF = true) : ProgWF I := by
  obtain ⟨hd, hnat, hzero, hbool, hdec, hdf, hdt⟩ := progWF_parts h
  refine { ctorIn := ?_, ctorOf := ?_, natPins := ?_, zeroPin := ?_, boolFalse := ?_,
           boolTrue := ?_, decOther := ?_, recRules := ?_, recKindIdx := ?_, subMinor := ?_,
           decIsFalse := ?_, decIsTrue := ?_ }
  · intro c sf lv ind cidx np nf ty hc
    have := hd c _ hc
    simp only [Input.declWF] at this
    exact beq_iff_eq.1 this
  · intro t k i h
    unfold Input.ctorsOf at h
    split at h
    · next sf lv np ni ty ctors hdt =>
      have := hd t _ hdt
      simp only [Input.declWF] at this
      have hm := List.all_eq_true.1 this (k, i) (List.mem_zipIdx_iff_getElem?.2 h)
      dsimp only at hm
      split at hm
      · next t' j np' nf' hk =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hm
        obtain ⟨rfl, rfl⟩ := hm
        obtain ⟨sf', lv', ty', hdk⟩ := ctorInfo?_eq.1 hk
        exact ⟨sf', lv', np', nf', ty', hdk⟩
      · cases hm
    · simp at h
  · intro N hN
    unfold Input.natPinsOk at hnat
    rw [hN] at hnat
    dsimp only at hnat
    split at hnat
    · next Z S hZ hS =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hnat
      obtain ⟨sf, lv, ty, hz⟩ := ctorInfo?_eq.1 hnat.1
      obtain ⟨sf', lv', ty', hs⟩ := ctorInfo?_eq.1 hnat.2
      exact ⟨Z, S, hZ, hS, ⟨sf, lv, ty, hz⟩, ⟨sf', lv', ty', hs⟩⟩
    · cases hnat
  · intro Z hZ
    unfold Input.zeroPinOk at hzero
    rw [hZ] at hzero
    dsimp only at hzero
    split at hzero
    · next N cidx np nf hi =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hzero
      obtain ⟨rfl, rfl⟩ := hzero
      obtain ⟨sf, lv, ty, hz⟩ := ctorInfo?_eq.1 hi
      exact ⟨sf, lv, N, cidx, ty, hz⟩
    · cases hzero
  · intro c hc
    unfold Input.boolPinsOk at hbool
    split at hbool
    · next hf _ => rw [hf] at hc; cases hc
    · next f t hf ht =>
      rw [hf] at hc
      cases hc
      split at hbool
      · next B i np nf B' i' np' nf' hif hit =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hbool
        obtain ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := hbool
        obtain ⟨sf, lv, ty, h₁⟩ := ctorInfo?_eq.1 hif
        obtain ⟨sf', lv', ty', h₂⟩ := ctorInfo?_eq.1 hit
        exact ⟨sf, lv, B, np, ty, h₁, t, ht, sf', lv', np', ty', h₂⟩
      · cases hbool
    · cases hbool
  · intro c hc
    unfold Input.boolPinsOk at hbool
    split at hbool
    · next _ ht => rw [ht] at hc; cases hc
    · next f t hf ht =>
      rw [ht] at hc
      cases hc
      split at hbool
      · next B i np nf B' i' np' nf' hif hit =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hbool
        obtain ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := hbool
        obtain ⟨sf, lv, ty, h₁⟩ := ctorInfo?_eq.1 hif
        obtain ⟨sf', lv', ty', h₂⟩ := ctorInfo?_eq.1 hit
        exact ⟨sf', lv', B, np', ty', h₂, f, hf, sf, lv, np, ty, h₁⟩
      · cases hbool
    · cases hbool
  · intro c d hc hd' sf lv ind cidx np nf ty sf' lv' ind' cidx' np' nf' ty' hdc hdd
    unfold Input.decOtherOk at hdec
    have h₁ := List.all_eq_true.1 hdec (some c) (by rcases hc with hc | hc <;> simp [hc])
    have h₂ := List.all_eq_true.1 h₁ (some d) (by rcases hd' with h | h | h | h <;> simp [h])
    unfold Input.otherInd at h₂
    simp only [Option.bind_some, ctorInfo?_eq.2 ⟨sf, lv, ty, hdc⟩,
      ctorInfo?_eq.2 ⟨sf', lv', ty', hdd⟩, bne_iff_ne] at h₂
    exact h₂
  · intro r sf k lv np nmot nmin ni ind rules ty hr
    have := hd r _ hr
    simp only [Input.declWF, Bool.and_eq_true, decide_eq_true_eq] at this
    exact ⟨this.1.1, this.1.2⟩
  · intro r sf k lv np nmot nmin ni ind rules ty w srcs hr hk i hi
    have := hd r _ hr
    simp only [Input.declWF, Bool.and_eq_true, decide_eq_true_eq] at this
    obtain ⟨_, hm⟩ := this
    rw [hk] at hm
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hm
    simpa using hm.2 _ hi
  · intro r sf k lv np nmot nmin ni ind rules ty w srcs hr hk
    have := hd r _ hr
    simp only [Input.declWF, Bool.and_eq_true, decide_eq_true_eq] at this
    obtain ⟨_, hm⟩ := this
    rw [hk] at hm
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
    exact hm.1
  · intro c hc
    unfold Input.ctorIdxOk at hdf
    rw [hc] at hdf
    dsimp only at hdf
    split at hdf
    · next D j np nf hj =>
      rw [beq_iff_eq] at hdf
      subst hdf
      obtain ⟨sf, lv, ty, h₁⟩ := ctorInfo?_eq.1 hj
      exact ⟨sf, lv, D, np, nf, ty, h₁⟩
    · cases hdf
  · intro c hc
    unfold Input.ctorIdxOk at hdt
    rw [hc] at hdt
    dsimp only at hdt
    split at hdt
    · next D j np nf hj =>
      rw [beq_iff_eq] at hdt
      subst hdt
      obtain ⟨sf, lv, ty, h₁⟩ := ctorInfo?_eq.1 hj
      exact ⟨sf, lv, D, np, nf, ty, h₁⟩
    · cases hdt

/-! ## Completeness -/

theorem declWF_of (wf : ProgWF I) {c : CId} {d : Src.Decl} (hd : I.decl? c = some d) :
    I.declWF c d = true := by
  cases d with
  | ctor sf lv ind cidx np nf ty =>
    simp only [Input.declWF, wf.ctorIn hd, BEq.rfl]
  | induct sf lv np ni ty ctors =>
    simp only [Input.declWF]
    refine List.all_eq_true.2 fun ⟨k, i⟩ hm => ?_
    have hk := List.mem_zipIdx_iff_getElem?.1 hm
    have hc : I.ctorsOf c = ctors := by unfold Input.ctorsOf; rw [hd]
    obtain ⟨sf', lv', np', nf', ty', hdk⟩ := wf.ctorOf (hc ▸ hk)
    simp [ctorInfo?_eq.2 ⟨sf', lv', ty', hdk⟩]
  | recr sf k lv np nmot nmin ni ind rules ty =>
    obtain ⟨h₁, h₂⟩ := wf.recRules hd
    simp only [Input.declWF, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨h₁, h₂⟩, ?_⟩
    split
    · next w srcs hk =>
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
      refine ⟨wf.subMinor hd hk, fun s hs => ?_⟩
      cases s with
      | index i => simpa using wf.recKindIdx hd hk i hs
      | proof => rfl
    · rfl
  | defn => rfl
  | quot => rfl
  | axio => rfl

/-- **The check is complete**: `ProgWF` passes it. -/
theorem progWF_complete (wf : ProgWF I) : I.progWF = true := by
  unfold Input.progWF
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · refine List.all_eq_true.2 fun ⟨c, e⟩ _ => ?_
    dsimp only
    split
    · next d hd => exact declWF_of wf hd
    · rfl
  · unfold Input.natPinsOk
    split
    · rfl
    · next N hN =>
      obtain ⟨Z, S, hZ, hS, ⟨sf, lv, ty, hz⟩, ⟨sf', lv', ty', hs⟩⟩ := wf.natPins hN
      rw [hZ, hS]
      simp [ctorInfo?_eq.2 ⟨sf, lv, ty, hz⟩, ctorInfo?_eq.2 ⟨sf', lv', ty', hs⟩]
  · unfold Input.zeroPinOk
    split
    · rfl
    · next Z hZ =>
      obtain ⟨sf, lv, N, cidx, ty, hz⟩ := wf.zeroPin hZ
      simp [ctorInfo?_eq.2 ⟨sf, lv, ty, hz⟩]
  · unfold Input.boolPinsOk
    cases hf : I.known.boolFalse with
    | none =>
      cases ht : I.known.boolTrue with
      | none => rfl
      | some t =>
        obtain ⟨_, _, _, _, _, _, f, hf', _⟩ := wf.boolTrue ht
        rw [hf] at hf'
        cases hf'
    | some f =>
      obtain ⟨sf, lv, B, np, ty, h₁, t, ht, sf', lv', np', ty', h₂⟩ := wf.boolFalse hf
      rw [ht]
      simp [ctorInfo?_eq.2 ⟨sf, lv, ty, h₁⟩, ctorInfo?_eq.2 ⟨sf', lv', ty', h₂⟩]
  · unfold Input.decOtherOk
    refine List.all_eq_true.2 fun c hc => List.all_eq_true.2 fun d hd => ?_
    unfold Input.otherInd
    split
    · next ind x ind' y hc' hd' =>
      cases c with
      | none => cases hc'
      | some c =>
        cases d with
        | none => cases hd'
        | some d =>
          obtain ⟨cidx, np, nf⟩ := x
          obtain ⟨cidx', np', nf'⟩ := y
          simp only [Option.bind_some] at hc' hd'
          obtain ⟨sf, lv, ty, h₁⟩ := ctorInfo?_eq.1 hc'
          obtain ⟨sf', lv', ty', h₂⟩ := ctorInfo?_eq.1 hd'
          have hc'' : I.known.decIsFalse = some c ∨ I.known.decIsTrue = some c := by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
            rcases hc with h | h
            · exact .inl h.symm
            · exact .inr h.symm
          have hd'' : I.known.boolFalse = some d ∨ I.known.boolTrue = some d ∨
              I.known.natZero = some d ∨ I.known.natSucc = some d := by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
            rcases hd with h | h | h | h
            · exact .inl h.symm
            · exact .inr (.inl h.symm)
            · exact .inr (.inr (.inl h.symm))
            · exact .inr (.inr (.inr h.symm))
          exact bne_iff_ne.2 (wf.decOther hc'' hd'' h₁ h₂)
    · rfl
  · unfold Input.ctorIdxOk
    split
    · rfl
    · next c hc =>
      obtain ⟨sf, lv, D, np, nf, ty, h₁⟩ := wf.decIsFalse hc
      simp [ctorInfo?_eq.2 ⟨sf, lv, ty, h₁⟩]
  · unfold Input.ctorIdxOk
    split
    · rfl
    · next c hc =>
      obtain ⟨sf, lv, D, np, nf, ty, h₁⟩ := wf.decIsTrue hc
      simp [ctorInfo?_eq.2 ⟨sf, lv, ty, h₁⟩]

theorem progWF_iff : I.progWF = true ↔ ProgWF I := ⟨progWF_sound, progWF_complete⟩

instance (I : Input) : Decidable (ProgWF I) := decidable_of_iff _ progWF_iff

/-- A successful erasure passed the check. -/
theorem erase_progWF {p : Src.Program} {ch : Src.Relevance.Checked} {L : Program}
    {st : Erase.Stats} (h : erase p ch = .ok (L, st)) : ProgWF (Input.ofProgram p ch) := by
  unfold erase at h
  dsimp only at h
  split at h
  · cases h
  · next hwf => exact progWF_sound (by simpa using hwf)

end Compilatrix.Lam.Erase.Proof
