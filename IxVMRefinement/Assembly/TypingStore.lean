import IxVMRefinement.StatementRel.StoreInhabit
import IxVMRefinement.StatementRel.LoadedReads

/-! # The store a typing run is read against

A typing run is checked against a table whose validity is witnessed over a store `R` it did
not load. The run's own records `E₀` are the bytes it hashed. The proof of the typing
statement reads both through one store `E`:

* `RecordsFor R E`: `E` decodes every record it holds, holds every record of `R` that
  decodes, every blob of `R`, and every committed prelude row. This is the class of stores
  the table witness's invariant is stated for.
* `Merged E₀ R E`: every record of `E` is a record of `E₀`, of `R`, or a committed prelude
  row, and `E` holds something wherever one of them does. `merged_exists` builds one.

With no collision in the sense of the statement (`CollisionWith`, compared with the committed
images), a merged store is a store for `R` (`Merged.recordsFor`), holds the run's records and
blobs (`Merged.run_record`, `Merged.run_blob`), and the run's calls are good for it
(`Merged.good`): two byte strings the run hashed at one address are equal, a byte string it
hashed at an address of `R` or of a committed row is the one held there, and nothing is
held or hashed at the zero address.

Two closed facts about the committed prelude rows are decided here: their addresses are
distinct (`committedPrelude_distinct`), without which no store could hold every row, and
none is the zero address (`committedPrelude_nonzero`).
-/

set_option linter.unusedVariables false

namespace IxVM.Refinement.Typing

open IxVM.Consistency
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open IxVM.Refinement.Claim (mkLazy mkLazy_rawBytes)

/-! ## Reading a store -/

theorem toOption_eq_some {ε α : Type} {x : Except ε α} {a : α} (h : x.toOption = some a) :
    x = .ok a := by
  cases x with
  | error e => simp [Except.toOption] at h
  | ok b =>
    have hb : some b = some a := h
    exact congrArg Except.ok (Option.some.inj hb)

/-- A record a store holds is the exact decoding of bytes it stores. -/
theorem recordOf_some {E : Ixon.Env} {a : _root_.Address} {c : Ixon.Constant}
    (h : recordOf E a = some c) :
    ∃ lc, E.consts.get? a = some lc ∧ Ixon.deConstantExact lc.rawBytes = .ok c := by
  unfold recordOf at h
  cases hl : E.consts.get? a with
  | none =>
    rw [hl] at h
    simp at h
  | some lc =>
    rw [hl] at h
    have h' : (Ixon.deConstantExact lc.rawBytes).toOption = some c := h
    exact ⟨lc, rfl, toOption_eq_some h'⟩

theorem recordOf_of_get {E : Ixon.Env} {a : _root_.Address} {lc : Ixon.LazyConstant}
    {c : Ixon.Constant} (hl : E.consts.get? a = some lc)
    (hd : Ixon.deConstantExact lc.rawBytes = .ok c) : recordOf E a = some c := by
  unfold recordOf
  rw [hl]
  show (Ixon.deConstantExact lc.rawBytes).toOption = some c
  rw [hd]
  rfl

theorem recordAt_of_get {E : Ixon.Env} {a : _root_.Address} {lc : Ixon.LazyConstant}
    {c : Ixon.Constant} (hl : E.consts.get? a = some lc) (hg : lc.get? = some c) :
    Ix.Cert.recordAt E a = some c := by
  unfold Ix.Cert.recordAt
  rw [hl]
  exact hg

/-! ## Stores for a witness store -/

/-- **`E` is a record store for the witness store `R`**: `E` decodes every record it holds;
every record of `R` that decodes is `E`'s record at its address; every blob of `R` is `E`'s;
and `E` holds every committed prelude row. The rows are asked for because an environment can
store a pinned constant whose record `R` does not hold. -/
def RecordsFor (R E : Ixon.Env) : Prop :=
  L1.EnvDecoded E ∧
  (∀ a c, recordOf R a = some c → Ix.Cert.recordAt E a = some c) ∧
  (∀ x b, R.blobs.get? x = some b → E.blobs.get? x = some b) ∧
  ∀ p ∈ committedRows, ∃ lc, E.consts.get? p.1 = some lc ∧ lc.rawBytes = p.2

/-! ## Closed facts about the committed prelude rows -/

/-- The addresses of the committed prelude records are distinct (decided). -/
theorem committedPrelude_distinct :
    RoleVal.committedPreludeList.Pairwise (fun a b => (a.1 == b.1) = false) := by
  decide +kernel

/-- No committed prelude record is at the zero address (decided). -/
theorem committedPrelude_nonzero :
    RoleVal.committedPreludeList.all
      (fun e => !(e.1 == Ix.HostAdmission.Merkle.padding)) = true := by
  decide +kernel

private theorem eq_of_pairwise_fst {β : Type} :
    ∀ {l : List (_root_.Address × β)}, l.Pairwise (fun a b => (a.1 == b.1) = false) →
      ∀ {x y : _root_.Address × β}, x ∈ l → y ∈ l → x.1 = y.1 → x = y
  | [], _, _, _, hx, _, _ => nomatch hx
  | p :: l, hp, x, y, hx, hy, he => by
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hp
    rcases List.mem_cons.mp hx with hxp | hxl
    · rcases List.mem_cons.mp hy with hyp | hyl
      · exact hxp.trans hyp.symm
      · have hf := hhead y hyl
        have ht : (p.1 == y.1) = true := by
          rw [← hxp]
          exact beq_iff_eq.mpr he
        rw [ht] at hf
        cases hf
    · rcases List.mem_cons.mp hy with hyp | hyl
      · have hf := hhead x hxl
        have ht : (p.1 == x.1) = true := by
          rw [← hyp]
          exact beq_iff_eq.mpr he.symm
        rw [ht] at hf
        cases hf
      · exact eq_of_pairwise_fst htail hxl hyl he

/-- **A committed row's bytes decode.** -/
theorem committedRows_decoded {p : _root_.Address × ByteArray} (hp : p ∈ committedRows) :
    ∃ c, Ixon.deConstantExact p.2 = .ok c := by
  rw [StoreInhabit.committedRows_eq] at hp
  obtain ⟨e, he, hpe⟩ := List.mem_map.mp hp
  have hp2 : p.2 = Ixon.serConstant e.2 := congrArg Prod.snd hpe.symm
  refine ⟨e.2, ?_⟩
  rw [hp2]
  exact (ClosedFacts.committedPrelude_rows e he).2

/-- **An address has one committed row.** -/
theorem committedRows_functional {p q : _root_.Address × ByteArray} (hp : p ∈ committedRows)
    (hq : q ∈ committedRows) (h : p.1 = q.1) : p.2 = q.2 := by
  rw [StoreInhabit.committedRows_eq] at hp hq
  obtain ⟨e, he, hpe⟩ := List.mem_map.mp hp
  obtain ⟨e', he', hqe⟩ := List.mem_map.mp hq
  have hp1 : p.1 = e.1 := congrArg Prod.fst hpe.symm
  have hq1 : q.1 = e'.1 := congrArg Prod.fst hqe.symm
  have hp2 : p.2 = Ixon.serConstant e.2 := congrArg Prod.snd hpe.symm
  have hq2 : q.2 = Ixon.serConstant e'.2 := congrArg Prod.snd hqe.symm
  have hee : e = e' :=
    eq_of_pairwise_fst committedPrelude_distinct he he' (hp1.symm.trans (h.trans hq1))
  rw [hp2, hq2, hee]

/-- **No committed row is at the zero address.** -/
theorem committedRows_ne_padding {p : _root_.Address × ByteArray} (hp : p ∈ committedRows) :
    p.1 ≠ Ix.HostAdmission.Merkle.padding := by
  rw [StoreInhabit.committedRows_eq] at hp
  obtain ⟨e, he, hpe⟩ := List.mem_map.mp hp
  have hp1 : p.1 = e.1 := congrArg Prod.fst hpe.symm
  have hb : (!(e.1 == Ix.HostAdmission.Merkle.padding)) = true :=
    List.all_eq_true.mp committedPrelude_nonzero e he
  intro hz
  have ht : (e.1 == Ix.HostAdmission.Merkle.padding) = true :=
    beq_iff_eq.mpr (hp1.symm.trans hz)
  rw [ht] at hb
  exact absurd hb (by decide)

/-- **A committed row's bytes are a committed image**, one of the byte strings every
statement compares with. -/
theorem committedRows_footprint {p : _root_.Address × ByteArray} (hp : p ∈ committedRows) :
    p.2 ∈ committedFootprint := by
  obtain ⟨row, hrow, -, hb⟩ := ClosedFacts.committedRows_inv hp
  have hmem : row ∈ (Ix.Kernel.Reader.RoleData.prelude ++ Ix.Kernel.Reader.RoleData.evidence ++
      Ix.Kernel.Reader.RoleData.blobs).toList := by
    simp only [Array.toList_append, List.mem_append]
    exact Or.inl (Or.inl hrow)
  have himg : p.2 ∈ committedImages :=
    List.mem_filterMap.mpr ⟨row.2, List.mem_map.mpr ⟨row, hmem, rfl⟩, hb⟩
  exact List.mem_append_left _ himg

/-! ## Laying entries over a map -/

/-- Entries laid over a map: the head of the list wins. -/
def overlay {β : Type} (base : Std.HashMap _root_.Address β) :
    List (_root_.Address × β) → Std.HashMap _root_.Address β
  | [] => base
  | p :: ps => (overlay base ps).insert p.1 p.2

private theorem insert_isSome {β : Type} (m : Std.HashMap _root_.Address β)
    (k a : _root_.Address) (w : β) (h : k = a ∨ (m.get? a).isSome = true) :
    ((m.insert k w).get? a).isSome = true := by
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
  by_cases hk : (k == a) = true
  · rw [ite_eq_left hk]
    rfl
  · rw [ite_eq_right hk]
    rcases h with h | h
    · exact absurd (beq_iff_eq.mpr h) hk
    · rw [← Std.HashMap.get?_eq_getElem?]
      exact h

/-- What the overlay holds is an entry of the list or the base's. -/
theorem overlay_get?_inv {β : Type} (base : Std.HashMap _root_.Address β) :
    ∀ (l : List (_root_.Address × β)) {a : _root_.Address} {v : β},
      (overlay base l).get? a = some v → (a, v) ∈ l ∨ base.get? a = some v
  | [], _, _, h => Or.inr h
  | (k, w) :: ps, a, v, h => by
    have h' : ((overlay base ps).insert k w)[a]? = some v := by
      rw [← Std.HashMap.get?_eq_getElem?]
      exact h
    rw [Std.HashMap.getElem?_insert] at h'
    by_cases hk : (k == a) = true
    · rw [ite_eq_left hk] at h'
      have ha : k = a := beq_iff_eq.mp hk
      have hv : w = v := Option.some.inj h'
      rw [← ha, ← hv]
      exact Or.inl (List.mem_cons.mpr (Or.inl rfl))
    · rw [ite_eq_right hk, ← Std.HashMap.get?_eq_getElem?] at h'
      rcases overlay_get?_inv base ps h' with h1 | h1
      · exact Or.inl (List.mem_cons_of_mem _ h1)
      · exact Or.inr h1

theorem overlay_isSome_of_base {β : Type} (base : Std.HashMap _root_.Address β) :
    ∀ (l : List (_root_.Address × β)) {a : _root_.Address},
      (base.get? a).isSome = true → ((overlay base l).get? a).isSome = true
  | [], _, h => h
  | (k, w) :: ps, a, h =>
    insert_isSome (overlay base ps) k a w (Or.inr (overlay_isSome_of_base base ps h))

theorem overlay_isSome_of_mem {β : Type} (base : Std.HashMap _root_.Address β) :
    ∀ (l : List (_root_.Address × β)) {a : _root_.Address} {v : β},
      (a, v) ∈ l → ((overlay base l).get? a).isSome = true
  | [], _, _, h => nomatch h
  | (k, w) :: ps, a, v, h => by
    rcases List.mem_cons.mp h with he | hm
    · have hk : k = a := (congrArg Prod.fst he).symm
      exact insert_isSome (overlay base ps) k a w (Or.inl hk)
    · exact insert_isSome (overlay base ps) k a w
        (Or.inr (overlay_isSome_of_mem base ps hm))

/-! ## The merged store -/

/-- A record of the witness store that decodes, with its bytes and its exact decoding. -/
def witEntry (e : _root_.Address × Ixon.LazyConstant) :
    Option (_root_.Address × Ixon.LazyConstant) :=
  (Ixon.deConstantExact e.2.rawBytes).toOption.map fun c => (e.1, mkLazy e.2.rawBytes c)

/-- The witness store's records that decode. -/
def witEntries (R : Ixon.Env) : List (_root_.Address × Ixon.LazyConstant) :=
  R.consts.toList.filterMap witEntry

/-- The committed prelude records, each with its canonical bytes. -/
def commEntries : List (_root_.Address × Ixon.LazyConstant) :=
  RoleVal.committedPreludeList.map fun e => (e.1, mkLazy (Ixon.serConstant e.2) e.2)

theorem mem_witEntries {R : Ixon.Env} {a : _root_.Address} {lc : Ixon.LazyConstant}
    (h : (a, lc) ∈ witEntries R) :
    ∃ lcR c, R.consts.get? a = some lcR ∧ Ixon.deConstantExact lcR.rawBytes = .ok c ∧
      lc = mkLazy lcR.rawBytes c := by
  obtain ⟨e, he, hf⟩ := List.mem_filterMap.mp h
  have hf' : ((Ixon.deConstantExact e.2.rawBytes).toOption.map
      fun c => (e.1, mkLazy e.2.rawBytes c)) = some (a, lc) := hf
  obtain ⟨c, hc, hpair⟩ := Option.map_eq_some_iff.mp hf'
  have ha : e.1 = a := congrArg Prod.fst hpair
  have hlc : mkLazy e.2.rawBytes c = lc := congrArg Prod.snd hpair
  have hmem : (e.1, e.2) ∈ R.consts.toList := he
  have hget : R.consts.get? e.1 = some e.2 := by
    rw [Std.HashMap.get?_eq_getElem?]
    exact Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hmem
  rw [ha] at hget
  exact ⟨e.2, c, hget, toOption_eq_some hc, hlc.symm⟩

theorem witEntries_of_get {R : Ixon.Env} {a : _root_.Address} {lcR : Ixon.LazyConstant}
    {c : Ixon.Constant} (h : R.consts.get? a = some lcR)
    (hd : Ixon.deConstantExact lcR.rawBytes = .ok c) :
    (a, mkLazy lcR.rawBytes c) ∈ witEntries R := by
  have hmem : (a, lcR) ∈ R.consts.toList := by
    refine Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr ?_
    rw [← Std.HashMap.get?_eq_getElem?]
    exact h
  refine List.mem_filterMap.mpr ⟨(a, lcR), hmem, ?_⟩
  show ((Ixon.deConstantExact lcR.rawBytes).toOption.map
    fun c => (a, mkLazy lcR.rawBytes c)) = some (a, mkLazy lcR.rawBytes c)
  rw [hd]
  rfl

theorem mem_commEntries {a : _root_.Address} {lc : Ixon.LazyConstant}
    (h : (a, lc) ∈ commEntries) :
    ∃ p c, p ∈ committedRows ∧ p.1 = a ∧ Ixon.deConstantExact p.2 = .ok c ∧
      lc.rawBytes = p.2 ∧ lc.get? = some c := by
  obtain ⟨e, he, hpe⟩ := List.mem_map.mp h
  have ha : e.1 = a := congrArg Prod.fst hpe
  have hlc : mkLazy (Ixon.serConstant e.2) e.2 = lc := congrArg Prod.snd hpe
  obtain ⟨hrow, hdec⟩ := ClosedFacts.committedPrelude_rows e he
  refine ⟨(e.1, Ixon.serConstant e.2), e.2, hrow, ha, hdec, ?_, ?_⟩
  · rw [← hlc]
    exact mkLazy_rawBytes _ _
  · rw [← hlc]
    rfl

theorem commEntries_of_row {p : _root_.Address × ByteArray} (hp : p ∈ committedRows) :
    ∃ lc, (p.1, lc) ∈ commEntries := by
  rw [StoreInhabit.committedRows_eq] at hp
  obtain ⟨e, he, hpe⟩ := List.mem_map.mp hp
  have hp1 : p.1 = e.1 := congrArg Prod.fst hpe.symm
  refine ⟨mkLazy (Ixon.serConstant e.2) e.2, ?_⟩
  rw [hp1]
  exact List.mem_map.mpr ⟨e, he, rfl⟩

/-- **`E` merges the run's records `E₀`, the witness's records `R` and the committed
prelude rows**: every record of `E` is `E₀`'s, or has the bytes and the exact decoding of a
record of `R` or of a committed row; `E` holds a record wherever `E₀` does, wherever `R`
holds one that decodes, and at every committed row; its blobs are `E₀`'s and `R`'s; and it
has no role binding. -/
structure Merged (E₀ R E : Ixon.Env) : Prop where
  src : ∀ a lc, E.consts.get? a = some lc →
    E₀.consts.get? a = some lc ∨
    (∃ lcR c, R.consts.get? a = some lcR ∧ Ixon.deConstantExact lcR.rawBytes = .ok c ∧
      lc.rawBytes = lcR.rawBytes ∧ lc.get? = some c) ∨
    ∃ p c, p ∈ committedRows ∧ p.1 = a ∧ Ixon.deConstantExact p.2 = .ok c ∧
      lc.rawBytes = p.2 ∧ lc.get? = some c
  run : ∀ a lc, E₀.consts.get? a = some lc → (E.consts.get? a).isSome = true
  wit : ∀ a lcR c, R.consts.get? a = some lcR → Ixon.deConstantExact lcR.rawBytes = .ok c →
    (E.consts.get? a).isSome = true
  comm : ∀ p ∈ committedRows, (E.consts.get? p.1).isSome = true
  blobSrc : ∀ a b, E.blobs.get? a = some b →
    E₀.blobs.get? a = some b ∨ R.blobs.get? a = some b
  blobRun : ∀ a b, E₀.blobs.get? a = some b → (E.blobs.get? a).isSome = true
  blobWit : ∀ a b, R.blobs.get? a = some b → (E.blobs.get? a).isSome = true
  noBinding : E.roleBinding = none

/-- The merged store: the run's records, with the witness's records that decode and the
committed prelude records laid over them. -/
def mergedEnv (E₀ R : Ixon.Env) : Ixon.Env :=
  { consts := overlay (overlay E₀.consts (witEntries R)) commEntries
    blobs := overlay E₀.blobs R.blobs.toList }

/-- **A merged store exists.** -/
theorem merged_exists (E₀ R : Ixon.Env) : ∃ E, Merged E₀ R E := by
  refine ⟨mergedEnv E₀ R, ?_⟩
  constructor
  · intro a lc h
    have h' : (overlay (overlay E₀.consts (witEntries R)) commEntries).get? a = some lc := h
    rcases overlay_get?_inv _ _ h' with hc | h1
    · exact Or.inr (Or.inr (mem_commEntries hc))
    · rcases overlay_get?_inv _ _ h1 with hw | h0
      · obtain ⟨lcR, c, hR, hd, hlc⟩ := mem_witEntries hw
        refine Or.inr (Or.inl ⟨lcR, c, hR, hd, ?_, ?_⟩)
        · rw [hlc]
          exact mkLazy_rawBytes _ _
        · rw [hlc]
          rfl
      · exact Or.inl h0
  · intro a lc h
    have h1 : (E₀.consts.get? a).isSome = true := by
      rw [h]
      rfl
    exact overlay_isSome_of_base _ _ (overlay_isSome_of_base _ _ h1)
  · intro a lcR c h hd
    exact overlay_isSome_of_base _ _ (overlay_isSome_of_mem _ _ (witEntries_of_get h hd))
  · intro p hp
    obtain ⟨lc, hlc⟩ := commEntries_of_row hp
    exact overlay_isSome_of_mem _ _ hlc
  · intro a b h
    have h' : (overlay E₀.blobs R.blobs.toList).get? a = some b := h
    rcases overlay_get?_inv _ _ h' with hw | h0
    · refine Or.inr ?_
      rw [Std.HashMap.get?_eq_getElem?]
      exact Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hw
    · exact Or.inl h0
  · intro a b h
    have h1 : (E₀.blobs.get? a).isSome = true := by
      rw [h]
      rfl
    exact overlay_isSome_of_base _ _ h1
  · intro a b h
    have hmem : (a, b) ∈ R.blobs.toList := by
      refine Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr ?_
      rw [← Std.HashMap.get?_eq_getElem?]
      exact h
    exact overlay_isSome_of_mem _ _ hmem
  · rfl

/-! ## What the absence of a collision gives -/

section NoCollision

variable {calls : List (Call F)} {V : View} {extra : List ByteArray} {R : Ixon.Env}

/-- Two different byte strings the run hashed at one address are a collision. -/
theorem collision_of_run {b₁ b₂ : ByteArray} (h₁ : Hashed calls b₁) (h₂ : Hashed calls b₂)
    (hne : b₁ ≠ b₂) (he : Address.blake3Pure b₁ = Address.blake3Pure b₂) :
    CollisionWith V extra R calls := by
  unfold CollisionWith View.HashedCollision
  exact Or.inl (Or.inl ⟨Address.blake3Pure b₂, b₂, b₁, Or.inr (Or.inr ⟨h₂, rfl⟩), h₁, hne, he⟩)

/-- A byte string the run hashed at the address of a different compared byte string is a
collision. -/
theorem collision_of_extra {held bytes : ByteArray} (hmem : held ∈ extra)
    (hh : Hashed calls bytes) (hne : bytes ≠ held)
    (he : Address.blake3Pure bytes = Address.blake3Pure held) :
    CollisionWith V extra R calls := by
  unfold CollisionWith View.HashedCollision
  exact Or.inl (Or.inl ⟨Address.blake3Pure held, held, bytes, Or.inr (Or.inl ⟨hmem, rfl⟩), hh,
    hne, he⟩)

/-- A byte string the run hashed at the zero address is a collision. -/
theorem collision_of_zero {bytes : ByteArray} (hh : Hashed calls bytes)
    (hz : Address.blake3Pure bytes = Ix.HostAdmission.Merkle.padding) :
    CollisionWith V extra R calls := by
  unfold CollisionWith View.HashedCollision
  exact Or.inl (Or.inr (Or.inr ⟨bytes, Or.inr hh, hz⟩))

/-- A byte string the run hashed at an address where the witness store holds other bytes is
a collision. -/
theorem collision_of_store {x : _root_.Address} {held bytes : ByteArray}
    (hheld : (∃ lc, R.consts.get? x = some lc ∧ lc.rawBytes = held) ∨
      R.blobs.get? x = some held)
    (hh : Hashed calls bytes) (hne : bytes ≠ held) (hx : Address.blake3Pure bytes = x) :
    CollisionWith V extra R calls := by
  unfold CollisionWith
  exact Or.inr (Or.inl ⟨x, held, bytes, hheld, hh, hne, hx⟩)

/-- A projection image of a block the run hashed, at an address where the witness store holds
other bytes, is a collision. -/
theorem collision_of_store_image {x : _root_.Address} {held image : ByteArray}
    (hheld : (∃ lc, R.consts.get? x = some lc ∧ lc.rawBytes = held) ∨
      R.blobs.get? x = some held)
    (himg : HashedBlockProjImage calls image) (hne : image ≠ held)
    (hx : Address.blake3Pure image = x) :
    CollisionWith V extra R calls := by
  unfold CollisionWith
  exact Or.inr (Or.inr ⟨x, held, image, hheld, himg, hne, hx⟩)

/-- A projection image of a block the run hashed, at the address of a different byte string in
hand (held by the view, one of `extra`, or hashed by the run), is a collision. -/
theorem collision_of_image {x : _root_.Address} {held image : ByteArray}
    (hheld : V.Preimage x held ∨ (held ∈ extra ∧ Address.blake3Pure held = x) ∨
      (Hashed calls held ∧ Address.blake3Pure held = x))
    (himg : HashedBlockProjImage calls image) (hne : image ≠ held)
    (hx : Address.blake3Pure image = x) :
    CollisionWith V extra R calls := by
  obtain ⟨blk, cb, ms, hb, hdec, hms, hi⟩ := himg
  unfold CollisionWith View.HashedCollision
  exact Or.inl (Or.inr (Or.inl ⟨x, held, image, blk, cb, ms, hheld, hb, hdec, hms, hi, hne, hx⟩))

variable {E₀ : Ixon.Env}

/-- **The run's records agree with the witness's**: with no collision, where both stores
hold a record it is the same record. -/
theorem records_agree (hload : LoadedBy calls E₀) (hnc : ¬ CollisionWith V extra R calls) :
    ∀ x c c', recordOf E₀ x = some c → recordOf R x = some c' → c = c' := by
  intro x c c' h0 hR
  obtain ⟨lc0, hl0, hd0⟩ := recordOf_some h0
  obtain ⟨lcR, hlR, hdR⟩ := recordOf_some hR
  obtain ⟨hh, hx⟩ := hload.1 x lc0 hl0
  have hb : lc0.rawBytes = lcR.rawBytes := by
    by_cases hne : lc0.rawBytes = lcR.rawBytes
    · exact hne
    · exact absurd (collision_of_store (Or.inl ⟨lcR, hlR, rfl⟩) hh hne hx) hnc
  rw [hb, hdR] at hd0
  exact (Except.ok.inj hd0).symm

/-- **The run's blobs agree with the witness's.** -/
theorem blobs_agree (hload : LoadedBy calls E₀) (hnc : ¬ CollisionWith V extra R calls) :
    ∀ x b b', E₀.blobs.get? x = some b → R.blobs.get? x = some b' → b = b' := by
  intro x b b' h0 hR
  obtain ⟨hh, hx⟩ := hload.2 x b h0
  by_cases hne : b = b'
  · exact hne
  · exact absurd (collision_of_store (Or.inr hR) hh hne hx) hnc

variable {E : Ixon.Env}

/-- A merged store decodes its records. -/
theorem Merged.decoded (hM : Merged E₀ R E) (hdec : L1.EnvDecoded E₀) : L1.EnvDecoded E := by
  intro x lc h
  rcases hM.src x lc h with h0 | ⟨lcR, c, -, hd, hraw, hget⟩ | ⟨p, c, -, -, hd, hraw, hget⟩
  · exact hdec x lc h0
  · refine ⟨c, hget, ?_⟩
    rw [hraw]
    exact hd
  · refine ⟨c, hget, ?_⟩
    rw [hraw]
    exact hd

/-- **What a merged store holds at an address**: bytes the run hashed there, bytes the
witness store holds there, or a committed row's. -/
theorem Merged.preimage (hM : Merged E₀ R E) (hload : LoadedBy calls E₀) {x : _root_.Address}
    {held : ByteArray} (h : View.Preimage { env := E } x held) :
    (Hashed calls held ∧ Address.blake3Pure held = x) ∨
      ((∃ lc, R.consts.get? x = some lc ∧ lc.rawBytes = held) ∨ R.blobs.get? x = some held) ∨
      ∃ p, p ∈ committedRows ∧ p.1 = x ∧ p.2 = held := by
  rcases h with ⟨lc, hl, hraw⟩ | hbl | ⟨rb, hrb, -, -⟩ | ⟨tr, htr, -⟩
  · have hl' : E.consts.get? x = some lc := hl
    rcases hM.src x lc hl' with h0 | ⟨lcR, c, hR, -, hraw', -⟩ | ⟨p, c, hp, hp1, -, hraw', -⟩
    · obtain ⟨hh, hx⟩ := hload.1 x lc h0
      rw [hraw] at hh hx
      exact Or.inl ⟨hh, hx⟩
    · exact Or.inr (Or.inl (Or.inl ⟨lcR, hR, hraw'.symm.trans hraw⟩))
    · exact Or.inr (Or.inr ⟨p, hp, hp1, hraw'.symm.trans hraw⟩)
  · have hbl' : E.blobs.get? x = some held := hbl
    rcases hM.blobSrc x held hbl' with h0 | hR
    · exact Or.inl (hload.2 x held h0)
    · exact Or.inr (Or.inl (Or.inr hR))
  · have hrb' : E.roleBinding = some rb := hrb
    rw [hM.noBinding] at hrb'
    cases hrb'
  · exact absurd htr List.not_mem_nil

/-- **The run's calls are good for a merged store**: with no collision in the sense of the
statement, compared with the committed images, and a witness store that holds nothing at the
zero address. -/
theorem Merged.good (hM : Merged E₀ R E) (hload : LoadedBy calls E₀)
    (hzero : R.consts.get? Ix.HostAdmission.Merkle.padding = none ∧
      R.blobs.get? Ix.HostAdmission.Merkle.padding = none)
    (hextra : ∀ x ∈ committedFootprint, x ∈ extra) (hnc : ¬ CollisionWith V extra R calls)
    (hb : Bounded calls) (env : Ix.Kernel.Env .anon) (t : Ix.Kernel.RoleTable)
    (lim : Option Nat) : Core.Good ⟨E, env, t, lim⟩ calls := by
  refine ⟨fun hcol => hnc ?_, hb⟩
  rcases hcol with ⟨x, held, bytes, hpre, hh, hne, hx⟩ |
    ⟨x, held, image, blk, cb, ms, hpre, hblk, hdec, hms, himg, hne, hx⟩ | ⟨bytes, hpre, hz⟩
  · rcases hpre with hp | ⟨hmem, -⟩ | ⟨hh', hx'⟩
    · rcases hM.preimage hload hp with ⟨hh', hx'⟩ | hR | ⟨p, hp, hp1, hp2⟩
      · exact collision_of_run hh hh' hne (hx.trans hx'.symm)
      · exact collision_of_store hR hh hne hx
      · have hhash : Address.blake3Pure p.2 = p.1 := ClosedFacts.committedRows_hashed p hp
        rw [← hp2] at hne
        exact collision_of_extra (hextra _ (committedRows_footprint hp)) hh hne
          (hx.trans (hp1.symm.trans hhash.symm))
    · exact absurd hmem List.not_mem_nil
    · exact collision_of_run hh hh' hne (hx.trans hx'.symm)
  · have himg' : HashedBlockProjImage calls image := ⟨blk, cb, ms, hblk, hdec, hms, himg⟩
    rcases hpre with hp | ⟨hmem, -⟩ | ⟨hh', hx'⟩
    · rcases hM.preimage hload hp with hrun | hR | ⟨p, hp, hp1, hp2⟩
      · exact collision_of_image (Or.inr (Or.inr hrun)) himg' hne hx
      · exact collision_of_store_image hR himg' hne hx
      · have hhash : Address.blake3Pure p.2 = p.1 := ClosedFacts.committedRows_hashed p hp
        have hmem : held ∈ extra := by
          rw [← hp2]
          exact hextra _ (committedRows_footprint hp)
        have hheld_x : Address.blake3Pure held = x := by
          rw [← hp2, hhash, hp1]
        exact collision_of_image (Or.inr (Or.inl ⟨hmem, hheld_x⟩)) himg' hne hx
    · exact absurd hmem List.not_mem_nil
    · exact collision_of_image (Or.inr (Or.inr ⟨hh', hx'⟩)) himg' hne hx
  · rcases hpre with hp | hh
    · rcases hM.preimage hload hp with ⟨hh', -⟩ | hR | ⟨p, hp, hp1, -⟩
      · exact collision_of_zero hh' hz
      · rcases hR with ⟨lc, hl, -⟩ | hbl
        · rw [hzero.1] at hl
          cases hl
        · rw [hzero.2] at hbl
          cases hbl
      · exact absurd hp1 (committedRows_ne_padding hp)
    · exact collision_of_zero hh hz

/-- **A merged store is a record store for the witness store.** -/
theorem Merged.recordsFor (hM : Merged E₀ R E) (hload : LoadedBy calls E₀)
    (hdec : L1.EnvDecoded E₀) (hcomm : AgreesCommitted R)
    (hextra : ∀ x ∈ committedFootprint, x ∈ extra) (hnc : ¬ CollisionWith V extra R calls) :
    RecordsFor R E := by
  refine ⟨hM.decoded hdec, ?_, ?_, ?_⟩
  · intro a c h
    obtain ⟨lcR, hR, hd⟩ := recordOf_some h
    obtain ⟨lc, hlc⟩ := Option.isSome_iff_exists.mp (hM.wit a lcR c hR hd)
    rcases hM.src a lc hlc with h0 | ⟨lcR', c', hR', hd', -, hget⟩ | ⟨p, c', hp, hp1, hd', -, hget⟩
    · obtain ⟨c0, hget0, hd0⟩ := hdec a lc h0
      obtain ⟨hh, hx⟩ := hload.1 a lc h0
      have hb : lc.rawBytes = lcR.rawBytes := by
        by_cases hne : lc.rawBytes = lcR.rawBytes
        · exact hne
        · exact absurd (collision_of_store (Or.inl ⟨lcR, hR, rfl⟩) hh hne hx) hnc
      rw [hb, hd] at hd0
      have hcc : c = c0 := Except.ok.inj hd0
      rw [hcc]
      exact recordAt_of_get hlc hget0
    · rw [hR] at hR'
      have hll : lcR = lcR' := Option.some.inj hR'
      rw [← hll, hd] at hd'
      have hcc : c = c' := Except.ok.inj hd'
      rw [hcc]
      exact recordAt_of_get hlc hget
    · rw [← hp1] at hR
      have hbytes : lcR.rawBytes = p.2 := hcomm p hp lcR hR
      rw [← hbytes, hd] at hd'
      have hcc : c = c' := Except.ok.inj hd'
      rw [hcc]
      exact recordAt_of_get hlc hget
  · intro x b h
    obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.mp (hM.blobWit x b h)
    rcases hM.blobSrc x b' hb' with h0 | hR
    · have hbb : b' = b := blobs_agree hload hnc x b' b h0 h
      rw [← hbb]
      exact hb'
    · rw [h] at hR
      have hbb : b = b' := Option.some.inj hR
      rw [hbb]
      exact hb'
  · intro p hp
    obtain ⟨lc, hlc⟩ := Option.isSome_iff_exists.mp (hM.comm p hp)
    refine ⟨lc, hlc, ?_⟩
    rcases hM.src p.1 lc hlc with h0 | ⟨lcR, c, hR, -, hraw, -⟩ | ⟨q, c, hq, hq1, -, hraw, -⟩
    · obtain ⟨hh, hx⟩ := hload.1 p.1 lc h0
      have hhash : Address.blake3Pure p.2 = p.1 := ClosedFacts.committedRows_hashed p hp
      by_cases hne : lc.rawBytes = p.2
      · exact hne
      · exact absurd (collision_of_extra (hextra _ (committedRows_footprint hp)) hh hne
          (hx.trans hhash.symm)) hnc
    · exact hraw.trans (hcomm p hp lcR hR)
    · exact hraw.trans (committedRows_functional hq hp hq1)

/-- **A merged store holds the run's records.** -/
theorem Merged.run_record (hM : Merged E₀ R E) (hload : LoadedBy calls E₀)
    (hdec : L1.EnvDecoded E₀) (hextra : ∀ x ∈ committedFootprint, x ∈ extra)
    (hnc : ¬ CollisionWith V extra R calls) {a : _root_.Address} {c : Ixon.Constant}
    (h : recordOf E₀ a = some c) : Ix.Cert.recordAt E a = some c := by
  obtain ⟨lc0, hl0, hd0⟩ := recordOf_some h
  obtain ⟨hh, hx⟩ := hload.1 a lc0 hl0
  obtain ⟨lc, hlc⟩ := Option.isSome_iff_exists.mp (hM.run a lc0 hl0)
  rcases hM.src a lc hlc with h0 | ⟨lcR, c', hR, hd', -, hget⟩ | ⟨p, c', hp, hp1, hd', -, hget⟩
  · rw [hl0] at h0
    have hll : lc0 = lc := Option.some.inj h0
    obtain ⟨c0, hget0, hdc⟩ := hdec a lc0 hl0
    rw [hd0] at hdc
    have hcc : c = c0 := Except.ok.inj hdc
    rw [← hll] at hlc
    rw [hcc]
    exact recordAt_of_get hlc hget0
  · have hb : lc0.rawBytes = lcR.rawBytes := by
      by_cases hne : lc0.rawBytes = lcR.rawBytes
      · exact hne
      · exact absurd (collision_of_store (Or.inl ⟨lcR, hR, rfl⟩) hh hne hx) hnc
    rw [hb, hd'] at hd0
    have hcc : c' = c := Except.ok.inj hd0
    rw [← hcc]
    exact recordAt_of_get hlc hget
  · have hhash : Address.blake3Pure p.2 = p.1 := ClosedFacts.committedRows_hashed p hp
    have hb : lc0.rawBytes = p.2 := by
      by_cases hne : lc0.rawBytes = p.2
      · exact hne
      · exact absurd (collision_of_extra (hextra _ (committedRows_footprint hp)) hh hne
          (hx.trans (hp1.symm.trans hhash.symm))) hnc
    rw [hb, hd'] at hd0
    have hcc : c' = c := Except.ok.inj hd0
    rw [← hcc]
    exact recordAt_of_get hlc hget

/-- **A merged store holds the run's blobs.** -/
theorem Merged.run_blob (hM : Merged E₀ R E) (hload : LoadedBy calls E₀)
    (hnc : ¬ CollisionWith V extra R calls) {a : _root_.Address} {b : ByteArray}
    (h : E₀.blobs.get? a = some b) : E.blobs.get? a = some b := by
  obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.mp (hM.blobRun a b h)
  rcases hM.blobSrc a b' hb' with h0 | hR
  · rw [h] at h0
    have hbb : b = b' := Option.some.inj h0
    rw [hbb]
    exact hb'
  · have hbb : b = b' := blobs_agree hload hnc a b b' h hR
    rw [hbb]
    exact hb'

end NoCollision

end IxVM.Refinement.Typing
