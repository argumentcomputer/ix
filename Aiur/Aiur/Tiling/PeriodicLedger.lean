import Aiur.Tiling.PeriodicCopy
import Aiur.Tiling.Trim

/-!
# The v2 bus: ledger split and trailing zeros

Every lookup of a shard row is a row message, a lane message or a copy
(`rowLedger_split`). Their tuples have three shapes (`Sharded.Shape`):

* a row message: `W` entries headed by the code of a row channel;
* a lane message: 4 entries headed by the code of a lane channel;
* a copy: 2 entries headed by a packed copy key `3 + 4·n`.

Codes are distinct, nonzero and `1` or `2` mod 4; copy keys are `3` mod 4. So
two tuples of different shapes never agree after dropping trailing zeros, and
multi-stark's trimmed balance is exact balance (`Sharded.exact_of_trimmed`).
Exact balance at a packed copy key involves only the shard that owns the
label, which gives every shard's copy balance (`Sharded.copy_balanced`).
-/

namespace Aiur.Tiling.Periodic

open Aiur.Scalar.Circuit (ArithExpr Var Satisfies)

variable {F : Type} [Field F] [DecidableEq F]

namespace Sharded

variable (S : Sharded F)

/-- The row and lane messages of shard `k` over its `H` rows. -/
noncomputable def msgLedger (k H : Nat) (main : Nat → Nat → F) : Ledger F :=
  ∑ p ∈ Finset.range H, ((rowMessage S.width (S.idOffset k)).entry (S.assign k main p) +
    ((List.range (lanes S.width)).map fun l => (laneMessage S.width l).entry (S.assign k main p)).sum)

theorem rowLedger_split (k : Nat) (main : Nat → Nat → F) (p : Nat) :
    (S.circuit k).rowLedger (S.assign k main p) =
      ((rowMessage S.width (S.idOffset k)).entry (S.assign k main p) +
        ((List.range (lanes S.width)).map fun l => (laneMessage S.width l).entry (S.assign k main p)).sum) +
      ∑ j ∈ Finset.range S.width, (copyLookup S.width (S.labelOffset k) j).entry (S.assign k main p) := by
  simp only [Circuit.rowLedger, circuit, narrowCircuit, List.map_cons, List.sum_cons, List.map_append,
    List.sum_append, List.map_map, Function.comp_def, System.finset_sum_range_list, add_assoc]

theorem ledger_split (H : Nat → Nat) (main : Nat → Nat → Nat → F) :
    S.ledger H main = ∑ k ∈ Finset.range S.shards.length,
      (S.msgLedger k (H k) (main k) + S.copyLedger k (H k) (main k)) := by
  unfold ledger msgLedger copyLedger
  apply Finset.sum_congr rfl; intro k _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro p _
  exact S.rowLedger_split k (main k) p

/-- All copy labels of all shards lie below this. -/
def labelTotal [Zero F] : Nat := S.labelOffset S.shards.length

/-- The tuples of the v2 bus. -/
def Shape (t : List F) : Prop :=
  (∃ e ∈ S.buses, t.head? = some ((e.2.1 : Nat) : F) ∧ t.length = if e.2.2 then 4 else S.width) ∨
    (t.length = 2 ∧ ∃ n < S.labelTotal, t.head? = some ((copyKey n : Nat) : F))

/-- The tuples of row and lane messages. -/
def MsgShape (t : List F) : Prop :=
  ∃ e ∈ S.buses, t.head? = some ((e.2.1 : Nat) : F) ∧ t.length = if e.2.2 then 4 else S.width

/-- Size facts about bus codes and labels that make the shapes separate. -/
structure Separated (bound : Nat) : Prop where
  small : SmallCast F bound
  width : 4 ≤ S.width
  codes : ∀ e ∈ S.buses, e.2.1 < bound ∧ (e.2.1 % 4 = 1 ∨ e.2.1 % 4 = 2)
  nodup : (S.buses.map (·.2.1)).Nodup
  labels : copyKey S.labelTotal < bound

variable {S}

theorem Separated.code_ne {bound : Nat} (sep : S.Separated bound) {e : (F × F) × Nat × Bool}
    (he : e ∈ S.buses) : ((e.2.1 : Nat) : F) ≠ 0 := by
  intro h
  have := sep.small _ (sep.codes e he).1 h
  have := (sep.codes e he).2
  omega

theorem Separated.copy_ne {bound : Nat} (sep : S.Separated bound) {n : Nat} (hn : n < S.labelTotal) :
    ((copyKey n : Nat) : F) ≠ 0 := by
  intro h
  have := sep.small _ (by have := sep.labels; simp only [copyKey] at this ⊢; omega) h
  simp [copyKey, COPY] at this

theorem Separated.injOn {bound : Nat} (sep : S.Separated bound) :
    Set.InjOn (trimZeros (F := F)) {t | S.Shape t} := by
  intro t ht u hu h
  by_cases len : t.length = u.length
  · exact trimZeros_inj_of_length len h
  exfalso
  have headOf : ∀ v : List F, S.Shape v → ∃ a, v.head? = some a ∧ a ≠ 0 := by
    rintro v (⟨e, he, hd, _⟩ | ⟨_, n, hn, hd⟩)
    · exact ⟨_, hd, sep.code_ne he⟩
    · exact ⟨_, hd, sep.copy_ne hn⟩
  obtain ⟨a, ha, a0⟩ := headOf t ht
  have hb := trimZeros_head h ha a0
  have codeInj : ∀ e ∈ S.buses, ∀ e' ∈ S.buses, ((e.2.1 : Nat) : F) = ((e'.2.1 : Nat) : F) → e = e' := by
    intro e he e' he' eq
    have := sep.small.inj (sep.codes e he).1 (sep.codes e' he').1 eq
    exact List.inj_on_of_nodup_map sep.nodup he he' this
  have codeCopy : ∀ e ∈ S.buses, ∀ n < S.labelTotal, ((e.2.1 : Nat) : F) ≠ ((copyKey n : Nat) : F) := by
    intro e he n hn eq
    exact copyKey_ne_code sep.small (sep.codes e he).2
      (by have := sep.labels; simp only [copyKey] at this ⊢; omega) (sep.codes e he).1 eq.symm
  rcases ht with ⟨e, he, hdt, lt⟩ | ⟨lt, n, hn, hdt⟩ <;>
    rcases hu with ⟨e', he', hdu, lu⟩ | ⟨lu, n', hn', hdu⟩
  · rw [hdt, Option.some.injEq] at ha
    rw [hdu, Option.some.injEq, ← ha] at hb
    rw [codeInj e he e' he' hb.symm] at lt
    exact len (lt.trans lu.symm)
  · rw [hdt, Option.some.injEq] at ha
    rw [hdu, Option.some.injEq, ← ha] at hb
    exact codeCopy e he n' hn' hb.symm
  · rw [hdt, Option.some.injEq] at ha
    rw [hdu, Option.some.injEq, ← ha] at hb
    exact codeCopy e' he' n hn hb
  · exact len (lt.trans lu.symm)

/-! ## Supports -/

/-- `List.lookup` returns a member. -/
theorem _root_.List.mem_of_lookup_eq_some {α β : Type} [BEq α] [LawfulBEq α] {l : List (α × β)} {a : α} {b : β}
    (h : l.lookup a = some b) : (a, b) ∈ l := by
  induction l with
  | nil => simp at h
  | cons x l ih =>
      obtain ⟨x1, x2⟩ := x
      simp only [List.lookup] at h
      split at h
      · rename_i e
        simp only [beq_iff_eq] at e
        subst e
        simp only [Option.some.injEq] at h
        subst h
        exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih h)

theorem codeOf_mem {key : F × F} {code : Nat} {lane : Bool} (h : S.buses.lookup key = some (code, lane)) :
    codeOf S.buses key = (code : F) ∧ (key, code, lane) ∈ S.buses := by
  refine ⟨by simp [codeOf, h], ?_⟩
  exact List.mem_of_lookup_eq_some h


/-- What the support and copy lemmas read from `Sharded.check`. -/
def RowsOk (S : Sharded F) : Prop :=
  ∀ k < S.shards.length, ∀ T ∈ (S.layout k).templates, T.width = S.width ∧ T.checkPhysical S.buses = true

/-- Every template's virtual slots pass `checkVirtual`. -/
def VirtualOk (S : Sharded F) : Prop :=
  ∀ k < S.shards.length, ∀ T ∈ (S.layout k).templates, T.checkVirtual = true

/-- Every template's boolean virtual slots pass `checkBool`. -/
def BoolOk (S : Sharded F) : Prop :=
  ∀ k < S.shards.length, ∀ T ∈ (S.layout k).templates, T.checkBool = true

theorem RowsOk.row {S : Sharded F} (ok : S.RowsOk) {k p f i r : Nat} {T : Template2 F} {row : Row2 F}
    (hk : k < S.shards.length) (placed : Placed S k p f i r T row) :
    T.checkRow S.buses row = true := by
  have := (ok k hk T (List.mem_of_getElem? placed.template)).2
  simp only [Template2.checkPhysical, Bool.and_eq_true, List.all_eq_true] at this
  exact this.1.1.1.2 row (List.mem_of_getElem? placed.row)

theorem RowsOk.cells {S : Sharded F} (ok : S.RowsOk) {k : Nat} (hk : k < S.shards.length) :
    ((S.layout k).shadow S.width).CellsValid := shadow_cellsValid (ok k hk)

theorem labelOffset_succ (S : Sharded F) (k : Nat) :
    S.labelOffset (k + 1) = S.labelOffset k + ((S.shadow k).keys.length + 1) := by
  simp [labelOffset, List.range_succ]

theorem labelOffset_mono (S : Sharded F) {k k' : Nat} (h : k < k') :
    S.labelOffset k + ((S.shadow k).keys.length + 1) ≤ S.labelOffset k' := by
  rw [← labelOffset_succ]
  exact sum_range_mono _ h

theorem shadow_eq (S : Sharded F) (k : Nat) : S.shadow k = (S.layout k).shadow S.width := rfl

theorem row_support {k p : Nat} {main : Nat → Nat → F} (ok : S.RowsOk) (hk : k < S.shards.length)
    (w4 : 4 ≤ S.width) {t : List F}
    (h : (rowMessage S.width (S.idOffset k)).entry (S.assign k main p) t ≠ 0) : S.MsgShape t := by
  rw [rowMessage_entry, Finsupp.single_apply] at h
  split at h
  swap
  · exact absurd rfl h
  rename_i eq
  subst eq
  cases hp : ((S.layout k).shadow S.width).places[p]? with
  | none =>
      simp [assign, S.fixedAt_unplaced hp] at h
  | some x =>
      obtain ⟨f, i, r⟩ := x
      obtain ⟨T, row, placed⟩ := S.placed_of_place hp
      have r0 := placed.rowMsg (main := main) (c := 0) (by norm_num)
      have r1 := placed.rowMsg (main := main) (c := 1) (by norm_num)
      have r2 := placed.rowMsg (main := main) (c := 2) (by norm_num)
      rw [r1, r2] at h
      rw [r0]
      cases row with
      | gate => simp [Row2.rowMsg] at h
      | message m key =>
          have rowOk := ok.row hk placed
          simp only [Template2.checkRow, Template2.rowMessageOk, Bool.and_eq_true] at rowOk
          cases hm : T.messages[m]? with
          | none => simp [Row2.rowMsg, hm] at h
          | some msg =>
              obtain ⟨sel, tag, sub, cells⟩ := msg
              rw [hm] at rowOk
              dsimp only at rowOk
              cases hl : S.buses.lookup (tag, sub) with
              | none => rw [hl] at rowOk; simp at rowOk
              | some e =>
                  obtain ⟨code, lane⟩ := e
                  rw [hl] at rowOk
                  simp only [Bool.not_eq_true'] at rowOk
                  obtain ⟨c, mem⟩ := codeOf_mem hl
                  refine ⟨_, mem, ?_, ?_⟩
                  · simp [Row2.rowMsg, hm, c]
                  · simp [rowOk.1]; omega

theorem lane_support {k p l : Nat} {main : Nat → Nat → F} (ok : S.RowsOk) (hk : k < S.shards.length)
    (hl : l < lanes S.width) {t : List F}
    (h : (laneMessage S.width l).entry (S.assign k main p) t ≠ 0) : S.MsgShape t := by
  rw [laneMessage_entry, Finsupp.single_apply] at h
  split at h
  swap
  · exact absurd rfl h
  rename_i eq
  subst eq
  cases hp : ((S.layout k).shadow S.width).places[p]? with
  | none =>
      simp [assign, S.fixedAt_unplaced hp] at h
  | some x =>
      obtain ⟨f, i, r⟩ := x
      obtain ⟨T, row, placed⟩ := S.placed_of_place hp
      have l0 := placed.laneMsg (main := main) (c := 0) hl (by norm_num)
      have l1 := placed.laneMsg (main := main) (c := 1) hl (by norm_num)
      have l2 := placed.laneMsg (main := main) (c := 2) hl (by norm_num)
      rw [l1, l2] at h
      rw [l0]
      cases row with
      | message => simp [Row2.laneMsg] at h
      | gate ls spans =>
          have rowOk := ok.row hk placed
          simp only [Template2.checkRow, Bool.and_eq_true, List.all_eq_true] at rowOk
          cases hu : ls[l]? with
          | none => simp [Row2.laneMsg, hu] at h
          | some u =>
              cases u with
              | gate => simp [Row2.laneMsg, hu] at h
              | empty => simp [Row2.laneMsg, hu] at h
              | message m =>
                  have mOk := rowOk.1.1.2 _ (List.mem_of_getElem? hu)
                  simp only [Template2.laneMessageOk] at mOk
                  cases hm : T.messages[m]? with
                  | none => simp [Row2.laneMsg, hu, hm] at h
                  | some msg =>
                      obtain ⟨sel, tag, sub, cells⟩ := msg
                      rw [hm] at mOk
                      dsimp only at mOk
                      simp only [Bool.and_eq_true] at mOk
                      cases hlk : S.buses.lookup (tag, sub) with
                      | none => rw [hlk] at mOk; simp at mOk
                      | some e =>
                          obtain ⟨code, lane⟩ := e
                          rw [hlk] at mOk
                          obtain ⟨c, mem⟩ := codeOf_mem hlk
                          refine ⟨_, mem, ?_, ?_⟩
                          · simp [Row2.laneMsg, hu, hm, c]
                          · simp [mOk.2]

theorem copy_support {k : Nat} {H : Nat} {main : Nat → Nat → F} (ok : S.RowsOk) (hk : k < S.shards.length)
    {t : List F} (h : S.copyLedger k H main t ≠ 0) : S.Shape t := by
  rw [copyLedger_apply] at h
  obtain ⟨p, _, hp⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨j, _, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hp
  split at hj
  swap
  · exact absurd rfl hj
  rename_i eq
  subst eq
  right
  refine ⟨rfl, _, ?_, rfl⟩
  have le := labelNat_le (ok.cells hk) p j
  have := S.labelOffset_mono hk
  rw [shadow_eq] at this
  simp only [labelTotal]
  omega

theorem msg_support {k H : Nat} {main : Nat → Nat → F} (ok : S.RowsOk) (hk : k < S.shards.length)
    (w4 : 4 ≤ S.width) {t : List F} (h : S.msgLedger k H main t ≠ 0) : S.MsgShape t := by
  simp only [msgLedger, Finsupp.finsetSum_apply, Finsupp.add_apply] at h
  obtain ⟨p, _, hp⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  by_cases r0 : (rowMessage S.width (S.idOffset k)).entry (S.assign k main p) t = 0
  · rw [r0, zero_add, System.ledger_list_sum] at hp
    obtain ⟨x, hx, hx0⟩ : ∃ x ∈ (List.range (lanes S.width)).map (fun l =>
        (laneMessage S.width l).entry (S.assign k main p) t), x ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hp (List.sum_eq_zero (fun x hx => hc x hx) |> fun e => by
        simpa [List.map_map, Function.comp_def] using e)
    simp only [List.map_map, List.mem_map, Function.comp_def] at hx
    obtain ⟨l, hl, rfl⟩ := hx
    exact S.lane_support ok hk (List.mem_range.mp hl) hx0
  · exact S.row_support ok hk w4 r0

/-- **Trailing zeros, v2.** Balance under multi-stark's fingerprint is exact
balance of the shards' lookups and an external ledger of message shapes. -/
theorem exact_of_trimmed {bound : Nat} (sep : S.Separated bound) (ok : S.RowsOk)
    {H : Nat → Nat} {main : Nat → Nat → Nat → F} {ext : Ledger F}
    (extShape : ∀ t, ext t ≠ 0 → S.Shape t)
    (trimmed : Finsupp.mapDomain trimZeros (S.ledger H main + ext) = 0) :
    S.ledger H main + ext = 0 := by
  have outside : ∀ t, ¬ S.Shape t → (S.ledger H main + ext) t = 0 := by
    intro t ht
    have e : ext t = 0 := by by_contra ne; exact ht (extShape t ne)
    rw [Finsupp.add_apply, e, add_zero, ledger_split, Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro k hk
    have hk := Finset.mem_range.mp hk
    rw [Finsupp.add_apply]
    have m : S.msgLedger k (H k) (main k) t = 0 := by
      by_contra ne; exact ht (Or.inl (S.msg_support ok hk sep.width ne))
    have c : S.copyLedger k (H k) (main k) t = 0 := by
      by_contra ne; exact ht (S.copy_support ok hk ne)
    rw [m, c, add_zero]
  have support : ((S.ledger H main + ext).support : Set (List F)) ⊆ {t | S.Shape t} := by
    intro t ht
    by_contra h
    exact (Finsupp.mem_support_iff.mp ht) (outside t h)
  ext t
  by_cases ht : S.Shape t
  · have := Finsupp.mapDomain_apply' _ _ support sep.injOn ht
    rw [trimmed] at this
    simpa using this.symm
  · simpa using outside t ht

/-- **Copy balance per shard.** Exact balance against an external ledger of
message shapes balances every packed key of every shard's own labels on that
shard's copy lookups. -/
theorem copy_balanced {bound : Nat} (sep : S.Separated bound) (ok : S.RowsOk)
    {H : Nat → Nat} {main : Nat → Nat → Nat → F} {ext : Ledger F}
    (extShape : ∀ t, ext t ≠ 0 → t.length ≠ 2) (balanced : S.ledger H main + ext = 0)
    {k : Nat} (hk : k < S.shards.length) {n : Nat} (hn : n ≤ (S.shadow k).keys.length) (v : F) :
    S.copyLedger k (H k) (main k) [((copyKey (n + S.labelOffset k) : Nat) : F), v] = 0 := by
  set t : List F := [((copyKey (n + S.labelOffset k) : Nat) : F), v]
  have at_t := congrArg (fun L : Ledger F => L t) balanced
  simp only [Finsupp.add_apply, Finsupp.coe_zero, Pi.zero_apply] at at_t
  have e : ext t = 0 := by by_contra ne; exact extShape t ne rfl
  rw [e, add_zero, ledger_split, Finsupp.finsetSum_apply] at at_t
  have msg0 : ∀ k' < S.shards.length, S.msgLedger k' (H k') (main k') t = 0 := by
    intro k' hk'
    by_contra ne
    obtain ⟨e, _, _, len⟩ := S.msg_support ok hk' sep.width ne
    simp only [t, List.length_cons, List.length_nil] at len
    split at len <;> have := sep.width <;> omega
  have total : S.labelOffset k + (S.shadow k).keys.length < S.labelTotal := by
    have := S.labelOffset_mono hk; simp only [labelTotal]; omega
  have other : ∀ k' < S.shards.length, k' ≠ k → S.copyLedger k' (H k') (main k') t = 0 := by
    intro k' hk' ne
    rw [copyLedger_apply]
    apply Finset.sum_eq_zero; intro p _
    apply Finset.sum_eq_zero; intro j _
    rw [if_neg]
    intro eq
    simp only [t, List.cons.injEq, and_true] at eq
    have le' : labelNat ((S.layout k').shadow S.width) p j ≤ (S.shadow k').keys.length :=
      labelNat_le (ok.cells hk') p j
    have total' : S.labelOffset k' + (S.shadow k').keys.length < S.labelTotal := by
      have := S.labelOffset_mono hk'; simp only [labelTotal]; omega
    have lb : copyKey S.labelTotal < bound := sep.labels
    have inj := copyKey_inj sep.small (by simp only [copyKey] at lb ⊢; omega)
      (by simp only [copyKey] at lb ⊢; omega) eq.1
    rcases Nat.lt_or_gt_of_ne ne with lt | gt
    · have := S.labelOffset_mono lt; omega
    · have := S.labelOffset_mono gt; omega
  rw [Finset.sum_eq_single k (fun k' hk' ne => by
      rw [Finsupp.add_apply, msg0 k' (Finset.mem_range.mp hk'), other k' (Finset.mem_range.mp hk') ne,
        add_zero])
    (fun h => absurd (Finset.mem_range.mpr hk) h)] at at_t
  rw [Finsupp.add_apply, msg0 k hk, zero_add] at at_t
  exact at_t

end Sharded

end Aiur.Tiling.Periodic
