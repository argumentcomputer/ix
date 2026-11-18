import Aiur.Tiling.PeriodicCompose

/-!
# Stacked tables beside the periodic shards

A stacked table is one circuit of its own, beside the shard circuits, whose
row `r` is one receiver part on the channel `(tag, sub)`:

* main column 0 is the count, the other main columns are witness values;
* fixed column `sel` is 1 on the table's rows and 0 on padding rows, and fixed
  column `key` holds `keyBase + r`;
* further fixed columns hold per-row constants (`data`);
* narrow row `c` of the part reads the columns `slices[c]`. With one slice the
  part is unchunked and the slice is its payload; with several, chunk `c` is
  `[code_c, key, slice_c …]`, keyed by the fixed key.

Lookup `c` is `push(−sel·count, [code_c, key?, slice_c …, 0 …])` at the
channel's v2 tuple length, so a table row's ledger is the v2 encoding of its
part (`Stacked.rowLedger_part`) and a padding row's is zero.

Two kinds are used. A **map table** has only fixed values: `data[r]` is the
encoded map claim's payload, and the slices cover the data columns in order. A
**ROM table** (`tag = ROM`) has witness words: its key is the address
`keyBase + r`, so the verifying key fixes the addresses and capacities but not
the words; row `r` is the ROM entry `(keyBase + r, words)`.
-/

namespace Aiur.Tiling.Periodic

open Aiur.Scalar.Circuit (ArithExpr Var Satisfies)

variable {F : Type} [Field F] [DecidableEq F]

structure Stacked (F : Type) where
  tag : F
  sub : F
  rows : Nat
  keyBase : Nat
  mainWidth : Nat
  slices : List (List Nat)
  data : List (List F) := []

namespace Stacked

variable (T : Stacked F)

def rom : Bool := T.tag == 2

def chunked : Bool := decide (2 ≤ T.slices.length)

def selCol : Nat := T.mainWidth

def keyCol : Nat := T.mainWidth + 1

def dataCol (j : Nat) : Nat := T.mainWidth + 2 + j

def subOf (c : Nat) : F := if T.chunked then chunkSub T.rom T.sub c else T.sub

def slice (c : Nat) : List Nat := T.slices.getD c []

/-- Fixed column `c` of row `r`: `sel`, `key`, then `data[r]`. -/
def fixedAt (r c : Nat) : F :=
  if r < T.rows then
    match c with
    | 0 => 1
    | 1 => ((T.keyBase + r : Nat) : F)
    | j + 2 => (T.data.getD r []).getD j 0
  else 0

def assign (main : Nat → Nat → F) (r : Nat) (v : Var) : F :=
  if v < T.mainWidth then main r v else T.fixedAt r (v - T.mainWidth)

def head : List (ArithExpr F) := if T.chunked then [.var T.keyCol] else []

def lookupAt (buses : Buses F) (W c : Nat) : Lookup F :=
  let e := (buses.lookup (T.tag, T.subOf c)).getD (0, false)
  let len := if e.2 then 4 else W
  ⟨.sub (.const 0) (.mul (.var T.selCol) (.var 0)),
    .const ((e.1 : Nat) : F) :: T.head ++ (T.slice c).map .var ++
      List.replicate (len - 1 - (T.head.length + (T.slice c).length)) (.const 0)⟩

def circuit (buses : Buses F) (W : Nat) : Circuit F where
  width := T.mainWidth
  fixedWidth := 2 + (T.data.headD []).length
  constraints := []
  lookups := (List.range T.slices.length).map (T.lookupAt buses W)

noncomputable def ledger (buses : Buses F) (W H : Nat) (main : Nat → Nat → F) : Ledger F :=
  ∑ p ∈ Finset.range H, (T.circuit buses W).rowLedger (T.assign main p)

def vals (a : Var → F) (c : Nat) : List F := (T.slice c).map a

/-- The receiver part of a row with assignment `a`. -/
def part (a : Var → F) : Part F :=
  if T.chunked then
    ⟨T.tag, T.sub, (if T.rom then [a T.keyCol] else []) ++ ((List.range T.slices.length).map (T.vals a)).flatten,
      -a 0, true, a T.keyCol, (List.range T.slices.length).map (T.vals a), []⟩
  else ⟨T.tag, T.sub, T.vals a 0, -a 0, true, a T.keyCol, [], []⟩

/-- The payload length, independent of the assignment. -/
def payloadLen : Nat :=
  if T.chunked then (if T.rom then 1 else 0) + (T.slices.map List.length).sum else (T.slice 0).length

/-- Every narrow row's channel has a bus entry and its tuple fits. -/
def busOk (buses : Buses F) (W : Nat) : Bool :=
  (List.range T.slices.length).all fun c =>
    match buses.lookup (T.tag, T.subOf c) with
    | some (_, lane) => decide (1 + T.head.length + (T.slice c).length ≤ if lane then 4 else W)
    | none => false

/-- The static facts of a table in system `S`: slices exist, buses fit, the
part is formed and its rows have the system's roles and arities, and a chunked
table's channel has no in-system receiver. -/
def check (S : Sharded F) : Bool :=
  !T.slices.isEmpty && T.busOk S.buses S.width &&
    (if T.chunked then
      decide (S.width ≤ T.payloadLen) &&
        (List.range T.slices.length).all (fun c =>
          decide (S.system.roleOf (T.tag, chunkSub T.rom T.sub c) =
              some (T.sub, some (c, T.slices.length, T.rom))) &&
            decide (S.system.arityAt (T.tag, chunkSub T.rom T.sub c) = some ((T.slice c).length + 1))) &&
        !(S.system.receivers.contains (T.tag, T.sub))
    else
      decide (T.payloadLen + 1 ≤ S.width) &&
        (match S.system.roleOf (T.tag, T.sub) with
          | some r => r.2.isNone
          | none => true) &&
        decide (S.system.arityAt (T.tag, T.sub) = some (T.slice 0).length))

/-- A map table: no witness values; the slices read the data columns in order. -/
def checkMap : Bool :=
  !T.rom && T.mainWidth == 1 &&
    T.slices.flatten == (List.range (T.data.headD []).length).map T.dataCol &&
    T.data.length == T.rows && T.data.all (fun d => d.length == (T.data.headD []).length)

/-- A ROM table: the payload is the key (the address) followed by the words,
and `sub` is the word count. -/
def checkRom : Bool :=
  T.rom && T.data.isEmpty && 1 ≤ T.payloadLen && T.sub == ((T.payloadLen - 1 : Nat) : F) &&
    (T.chunked || (T.slice 0).head? == some T.keyCol)

/-- The ROM entry of a ROM table's row. -/
def entry (a : Var → F) : F × List F := (a T.keyCol, (T.part a).payload.drop 1)

end Stacked

/-! ## Ledger of one row -/

namespace Stacked

variable {T : Stacked F}

theorem slices_eq (T : Stacked F) : (List.range T.slices.length).map T.slice = T.slices := by
  apply List.ext_getElem (by simp)
  intro n h1 h2
  simp [slice, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

theorem getD_range_map {α : Type} (n c : Nat) (f : Nat → List α) (hc : c < n) :
    ((List.range n).map f).getD c [] = f c := by
  simp [List.getD_eq_getElem?_getD, hc]

theorem part_chunks_ne (T : Stacked F) (a : Var → F) (ch : T.chunked = true) : (T.part a).chunks ≠ [] := by
  have hlen : 2 ≤ T.slices.length := by simpa [chunked] using ch
  simp only [part, ch, if_true, ne_eq, List.map_eq_nil_iff, List.range_eq_nil]
  omega

theorem entry_lookup (S : Sharded F) {c : Nat} {code : Nat} {lane : Bool}
    (h : S.buses.lookup (T.tag, T.subOf c) = some (code, lane))
    (fits : 1 + T.head.length + (T.slice c).length ≤ if lane then 4 else S.width) (a : Var → F)
    (sel : a T.selCol = 1) (rest : List F) (hrest : rest = (T.head.map (·.denote a)) ++ T.vals a c) :
    (T.lookupAt S.buses S.width c).entry a = Finsupp.single (S.encode2 (T.tag :: T.subOf c :: rest)) (-a 0) := by
  have hl : (T.head : List (ArithExpr F)).length = (T.head.map (·.denote a)).length := by simp
  simp only [lookupAt, h, Option.getD_some, Lookup.entry, Lookup.tuple, Sharded.encode2, hrest]
  congr 1
  · simp only [List.map_cons, List.map_append, List.map_map, List.map_replicate, Function.comp_def,
      ArithExpr.denote, vals, List.length_append, List.length_map]
    rfl
  · simp [ArithExpr.denote, sel]

/-- **A table row's ledger is its part's v2 encoding.** -/
theorem rowLedger_part (S : Sharded F) (ne : T.slices ≠ []) (ok : T.busOk S.buses S.width = true) (a : Var → F)
    (sel : a T.selCol = 1) :
    (T.circuit S.buses S.width).rowLedger a = S.padded2 (T.part a) := by
  have bus : ∀ c < T.slices.length, ∃ code lane, S.buses.lookup (T.tag, T.subOf c) = some (code, lane) ∧
      1 + T.head.length + (T.slice c).length ≤ if lane then 4 else S.width := by
    intro c hc
    have := List.all_eq_true.mp ok c (List.mem_range.mpr hc)
    cases hl : S.buses.lookup (T.tag, T.subOf c) with
    | none => simp [hl] at this
    | some e => exact ⟨e.1, e.2, rfl, by simpa [hl] using this⟩
  simp only [Circuit.rowLedger, circuit, List.map_map, Sharded.padded2]
  by_cases ch : T.chunked = true
  · have cp := part_chunks_ne T a ch
    rw [Part.narrow, if_neg cp, Finsupp.mapDomain_finsetSum, System.finset_sum_range_list]
    have len : (T.part a).chunks.length = T.slices.length := by simp [part, ch]
    rw [len]
    congr 1
    apply List.map_congr_left
    intro c hc
    have hc := List.mem_range.mp hc
    obtain ⟨code, lane, hl, fits⟩ := bus c hc
    rw [Finsupp.mapDomain_single, Function.comp_apply,
      entry_lookup S hl fits a sel (a T.keyCol :: T.vals a c) (by simp [head, ch, ArithExpr.denote])]
    simp only [Part.chunkTuple, part, ch, if_true, subOf, getD_range_map _ _ _ hc, Part.rom, rom,
      Part.cweight, List.getD_nil]
  · have hch : T.chunked = false := by simpa using ch
    have one : T.slices.length = 1 ∨ T.slices.length = 0 := by
      simp only [chunked, decide_eq_false_iff_not] at hch; omega
    have cp : (T.part a).chunks = [] := by simp [part, hch]
    rw [Part.narrow, if_pos cp, Part.wide, Finsupp.mapDomain_single]
    rcases one with one | zero
    · rw [one, List.range_one, List.map_singleton, List.sum_singleton]
      obtain ⟨code, lane, hl, fits⟩ := bus 0 (by omega)
      rw [Function.comp_apply, entry_lookup S hl fits a sel (T.vals a 0) (by simp [head, hch])]
      simp [part, hch, Part.tuple, subOf]
    · exact absurd (List.length_eq_zero_iff.mp zero) ne

/-! ## Static facts of the parts -/

theorem part_fields (T : Stacked F) (a : Var → F) : (T.part a).tag = T.tag ∧ (T.part a).sub = T.sub ∧
    (T.part a).recv = true ∧ (T.part a).key = a T.keyCol ∧ (T.part a).weight = -a 0 ∧
    (T.part a).rom = T.rom := by
  unfold part; split <;> simp [Part.rom, rom]

theorem part_chunks_eq (T : Stacked F) (a : Var → F) (ch : T.chunked = false) : (T.part a).chunks = [] := by
  simp [part, ch]

theorem length_flatten_vals (T : Stacked F) (a : Var → F) :
    ((List.range T.slices.length).map (T.vals a)).flatten.length = (T.slices.map List.length).sum := by
  rw [List.length_flatten, List.map_map]
  conv_rhs => rw [← slices_eq T, List.map_map]
  congr 1
  apply List.map_congr_left
  intro c _
  simp [vals]

theorem payload_length (T : Stacked F) (a : Var → F) : (T.part a).payload.length = T.payloadLen := by
  unfold part payloadLen
  split
  · rename_i ch
    simp only [ch, if_true, List.length_append, length_flatten_vals]
    split <;> simp
  · rename_i ch
    simp [ch, vals]

theorem chunk_length (T : Stacked F) (a : Var → F) (ch : T.chunked = true) {c : Nat} (hc : c < T.slices.length) :
    ((T.part a).chunks.getD c []).length = (T.slice c).length := by
  simp only [part, ch, if_true]
  rw [getD_range_map _ _ _ hc]
  simp [vals]

theorem chunks_length (T : Stacked F) (a : Var → F) (ch : T.chunked = true) :
    (T.part a).chunks.length = T.slices.length := by
  simp [part, ch]

variable {S : Sharded F}

theorem check_parts (ok : T.check S = true) : T.slices ≠ [] ∧ T.busOk S.buses S.width = true := by
  simp only [check, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at ok
  exact ⟨ok.1.1, ok.1.2⟩

theorem checkRequest2_part (ne : T.slices ≠ []) (ok : T.busOk S.buses S.width = true) (a : Var → F) :
    S.checkRequest2 (T.part a) = true := by
  obtain ⟨tag, sub, _, _, _, _⟩ := part_fields T a
  simp only [Sharded.checkRequest2, List.all_eq_true]
  intro e he
  by_cases ch : T.chunked = true
  · have cp := part_chunks_ne T a ch
    simp only [Sharded.rowKeys, cp, if_false, List.mem_map, List.mem_range, chunks_length T a ch] at he
    obtain ⟨c, hc, rfl⟩ := he
    have := List.all_eq_true.mp ok c (List.mem_range.mpr hc)
    simp only [subOf, ch, if_true] at this
    simp only [tag, sub, (part_fields T a).2.2.2.2.2, chunk_length T a ch hc]
    cases hl : S.buses.lookup (T.tag, chunkSub T.rom T.sub c) with
    | none => simp [hl] at this
    | some e =>
        simp only [hl, head, ch, if_true, List.length_singleton] at this ⊢
        revert this; split <;> simp <;> omega
  · have ch : T.chunked = false := by simpa using ch
    simp only [Sharded.rowKeys, part_chunks_eq T a ch, if_true, List.mem_singleton] at he
    subst he
    have := List.all_eq_true.mp ok 0 (List.mem_range.mpr (List.length_pos_iff.mpr ne))
    simp only [subOf, ch, Bool.false_eq_true, if_false, tag, sub] at this ⊢
    have pl : (T.part a).payload.length = (T.slice 0).length := by simp [part, ch, vals]
    rw [pl]
    cases hl : S.buses.lookup (T.tag, T.sub) with
    | none => simp [hl] at this
    | some e =>
        simp only [hl, head, ch, Bool.false_eq_true, if_false, List.length_nil] at this ⊢
        revert this; split <;> simp <;> omega

theorem check_facts (ok : T.check S = true) (a : Var → F) :
    (T.part a).Formed S.system.width ∧ (T.part a).RowsIn S.system.roleOf S.system.arityAt ∧
      ((T.part a).chunks = [] → S.system.arityAt ((T.part a).tag, (T.part a).sub) = some (T.part a).payload.length) ∧
      ((T.part a).chunks ≠ [] → ((T.part a).tag, (T.part a).sub) ∉ S.system.receivers) := by
  obtain ⟨tag, sub, _, _, _, prom⟩ := part_fields T a
  have W : S.system.width = S.width := rfl
  simp only [check, Bool.and_eq_true] at ok
  obtain ⟨_, rest⟩ := ok
  by_cases ch : T.chunked = true
  · have cp := part_chunks_ne T a ch
    simp only [ch, if_true, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
      Bool.not_eq_true'] at rest
    obtain ⟨⟨wide, roles⟩, nrecv⟩ := rest
    have two : 2 ≤ T.slices.length := by simpa [chunked] using ch
    refine ⟨Or.inr ⟨by rw [chunks_length T a ch]; exact two, by rw [W, payload_length]; exact wide,
        by simp [part, ch, Part.rom, rom], fun h => by simp [(part_fields T a).2.2.1] at h,
        Or.inl (by simp [part, ch])⟩,
      ⟨fun h => absurd h cp, fun _ c hc => ?_⟩, fun h => absurd h cp, fun _ => ?_⟩
    · rw [chunks_length T a ch] at hc ⊢
      rw [tag, sub, prom, chunk_length T a ch hc]
      exact roles c hc
    · rw [tag, sub]
      intro h
      rw [List.contains_iff_mem.mpr h] at nrecv
      cases nrecv
  · have ch : T.chunked = false := by simpa using ch
    have cp := part_chunks_eq T a ch
    simp only [ch, Bool.false_eq_true, if_false, Bool.and_eq_true, decide_eq_true_eq] at rest
    obtain ⟨⟨fits, role⟩, arity⟩ := rest
    refine ⟨Or.inl ⟨cp, by rw [W, payload_length]; exact fits⟩, ⟨fun _ r hr => ?_, fun h => absurd cp h⟩,
      fun _ => ?_, fun h => absurd cp h⟩
    · rw [tag, sub] at hr
      rw [hr] at role
      simpa using role
    · rw [tag, sub, payload_length]
      simpa [payloadLen, ch] using arity

/-- A map table row's wide tuple is the row's data. -/
theorem map_tuple (ok : T.checkMap = true) (main : Nat → Nat → F) {r : Nat} (hr : r < T.rows) :
    (T.part (T.assign main r)).tuple = T.tag :: T.sub :: T.data.getD r [] := by
  simp only [checkMap, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨nrom, mw⟩, flat⟩, len⟩, lens⟩ := ok
  set d := (T.data.headD []).length
  have hlen : (T.data.getD r []).length = d := by
    have hr' : r < T.data.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr', Option.getD_some]
    exact lens _ (List.getElem_mem hr')
  have payload : (T.part (T.assign main r)).payload = T.slices.flatten.map (T.assign main r) := by
    unfold part
    split
    · rename_i ch
      simp only [nrom, Bool.false_eq_true, if_false, List.nil_append, List.map_flatten, List.map_map]
      conv_rhs => rw [← slices_eq T, List.map_map]
      rfl
    · rename_i ch
      have one : T.slices.length ≤ 1 := by simp [chunked] at ch; omega
      rcases hs : T.slices with _ | ⟨s0, _ | ⟨s1, rest⟩⟩
      · simp [vals, slice, hs]
      · simp [vals, slice, hs]
      · rw [hs] at one; simp at one
  have at_j : ∀ j, T.assign main r (T.dataCol j) = (T.data.getD r []).getD j 0 := by
    intro j
    have e : T.dataCol j - T.mainWidth = j + 2 := by simp only [dataCol]; omega
    simp only [assign, show ¬ T.dataCol j < T.mainWidth by simp only [dataCol]; omega, if_false, e, fixedAt,
      if_pos hr]
  simp only [Part.tuple, (part_fields T _).1, (part_fields T _).2.1, payload, flat, List.map_map]
  congr 2
  apply List.ext_getElem (by rw [List.length_map, List.length_range, hlen])
  intro j h1 h2
  rw [List.getElem_map, List.getElem_range, Function.comp_apply, at_j, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h2, Option.getD_some]

/-- A ROM table row's wide tuple is the ROM encoding of its entry, at address `keyBase + r`. -/
theorem rom_tuple (ok : T.checkRom = true) (a : Var → F) :
    (T.part a).tuple = Bridge.encodeRom ((T.entry a).1, Aiur.Circuit.Erasure.pack (T.entry a).2) ∧
      (T.entry a).2.length = T.payloadLen - 1 := by
  simp only [checkRom, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.or_eq_true] at ok
  obtain ⟨⟨⟨⟨hrom, _⟩, one⟩, hsub⟩, shape⟩ := ok
  have hl : (T.entry a).2.length = T.payloadLen - 1 := by
    simp [entry, payload_length]
  have cons : (T.part a).payload = a T.keyCol :: (T.part a).payload.drop 1 := by
    unfold part
    split
    · simp [hrom]
    · rename_i ch
      rcases shape with h | h
      · exact absurd h ch
      · simp only [vals]
        cases hs : T.slice 0 with
        | nil => simp [hs] at h
        | cons k ks => simp [hs] at h ⊢; rw [h]
  refine ⟨?_, hl⟩
  have tag2 : T.tag = 2 := by simpa [rom] using hrom
  simp only [Part.tuple, (part_fields T a).1, (part_fields T a).2.1, Bridge.encodeRom, entry,
    Aiur.Circuit.Erasure.pack_words]
  rw [cons, tag2, hsub]
  simp only [List.drop_succ_cons, List.drop_zero, Bridge.ROM]
  rw [show ((T.part a).payload.drop 1).length = T.payloadLen - 1 by rw [List.length_drop, payload_length]]
  norm_num

theorem sel_assign (T : Stacked F) (main : Nat → Nat → F) {r : Nat} (hr : r < T.rows) :
    T.assign main r T.selCol = 1 := by
  simp [assign, selCol, fixedAt, hr]

theorem key_assign (T : Stacked F) (main : Nat → Nat → F) {r : Nat} (hr : r < T.rows) :
    T.assign main r T.keyCol = ((T.keyBase + r : Nat) : F) := by
  simp [assign, keyCol, fixedAt, hr]

/-- **A table's ledger.** Rows past `rows` have `sel = 0` and contribute nothing. -/
theorem ledger_eq (T : Stacked F) (S : Sharded F) (ne : T.slices ≠ []) (ok : T.busOk S.buses S.width = true)
    {H : Nat} (tall : T.rows ≤ H) (main : Nat → Nat → F) :
    T.ledger S.buses S.width H main =
      ((List.range T.rows).map fun r => S.padded2 (T.part (T.assign main r))).sum := by
  rw [ledger, System.finset_sum_range_list]
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le tall
  rw [List.range_add, List.map_append, List.sum_append, List.map_map]
  have pad : ((List.range d).map ((fun p => (T.circuit S.buses S.width).rowLedger (T.assign main p)) ∘
      (T.rows + ·))).sum = 0 := by
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp hx
    have sel : T.assign main (T.rows + e) T.selCol = 0 := by simp [assign, selCol, fixedAt]
    simp only [Function.comp_apply, Circuit.rowLedger, circuit, List.map_map]
    apply List.sum_eq_zero
    intro y hy
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hy
    simp [Lookup.entry, lookupAt, ArithExpr.denote, sel]
  rw [pad, add_zero]
  congr 1
  apply List.map_congr_left
  intro r hr
  exact rowLedger_part S ne ok _ (sel_assign T main (List.mem_range.mp hr))

end Stacked

/-! ## Tables as external parts -/

section Parts

/-- The parts of all table rows. -/
def tableParts (tables : List (Stacked F)) (mainT : Nat → Nat → Nat → F) : List (Part F) :=
  tables.zipIdx.flatMap fun (a : Stacked F × Nat) =>
    (List.range a.1.rows).map fun r => a.1.part (a.1.assign (mainT a.2) r)

/-- The ROM entries of the ROM tables' rows. -/
def romEntries (tables : List (Stacked F)) (mainT : Nat → Nat → Nat → F) : List (F × List F) :=
  tables.zipIdx.flatMap fun (a : Stacked F × Nat) =>
    if a.1.rom then (List.range a.1.rows).map fun r => a.1.entry (a.1.assign (mainT a.2) r) else []

/-- The lookups of all tables; table `t` has `HT t` rows. -/
noncomputable def tableLedger (S : Sharded F) (tables : List (Stacked F)) (HT : Nat → Nat)
    (mainT : Nat → Nat → Nat → F) : Ledger F :=
  (tables.zipIdx.map fun (a : Stacked F × Nat) => a.1.ledger S.buses S.width (HT a.2) (mainT a.2)).sum

theorem mem_tableParts {tables : List (Stacked F)} {mainT : Nat → Nat → Nat → F} {x : Part F}
    (h : x ∈ tableParts tables mainT) :
    ∃ (T : Stacked F) (t r : Nat), tables[t]? = some T ∧ r < T.rows ∧ x = T.part (T.assign (mainT t) r) := by
  simp only [tableParts, List.mem_flatMap, List.mem_map, List.mem_range] at h
  obtain ⟨⟨T, t⟩, ht, r, hr, rfl⟩ := h
  exact ⟨T, t, r, List.mk_mem_zipIdx_iff_getElem?.mp ht, hr, rfl⟩

theorem mem_romEntries {tables : List (Stacked F)} {mainT : Nat → Nat → Nat → F} {e : F × List F}
    (h : e ∈ romEntries tables mainT) :
    ∃ (T : Stacked F) (t r : Nat), tables[t]? = some T ∧ T.rom = true ∧ r < T.rows ∧
      e = T.entry (T.assign (mainT t) r) := by
  simp only [romEntries, List.mem_flatMap] at h
  obtain ⟨⟨T, t⟩, ht, he⟩ := h
  split at he
  · rename_i hrom
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp he
    exact ⟨T, t, r, List.mk_mem_zipIdx_iff_getElem?.mp ht, hrom, List.mem_range.mp hr, rfl⟩
  · simp at he

theorem length_tableParts (tables : List (Stacked F)) (mainT : Nat → Nat → Nat → F) :
    (tableParts tables mainT).length = (tables.map (·.rows)).sum := by
  simp only [tableParts, List.length_flatMap, List.length_map, List.length_range]
  conv_rhs => rw [← List.zipIdx_map_fst 0 tables, List.map_map]
  rfl

theorem tableLedger_eq {S : Sharded F} {tables : List (Stacked F)} (ok : ∀ T ∈ tables, T.check S = true)
    {HT : Nat → Nat} (tall : ∀ t T, tables[t]? = some T → T.rows ≤ HT t) (mainT : Nat → Nat → Nat → F) :
    tableLedger S tables HT mainT = ((tableParts tables mainT).map S.padded2).sum := by
  rw [tableLedger, tableParts, System.sum_map_flatMap]
  congr 1
  apply List.map_congr_left
  rintro ⟨T, t⟩ ht
  have hT := List.mk_mem_zipIdx_iff_getElem?.mp ht
  obtain ⟨ne, bus⟩ := Stacked.check_parts (ok T (List.mem_of_getElem? hT))
  rw [Stacked.ledger_eq T S ne bus (tall t T hT), List.map_map]
  rfl

theorem exists_of_sum_ne {α : Type} {l : List α} {g : α → Ledger F} {u : List F}
    (h : (l.map g).sum u ≠ 0) : ∃ x ∈ l, g x u ≠ 0 := by
  induction l with
  | nil => simp at h
  | cons x l ih =>
      simp only [List.map_cons, List.sum_cons, Finsupp.add_apply] at h
      by_cases hx : g x u = 0
      · rw [hx, zero_add] at h
        obtain ⟨y, hy, hne⟩ := ih h
        exact ⟨y, by simp [hy], hne⟩
      · exact ⟨x, by simp, hx⟩

theorem mapDomain_list_sum {α : Type} (f : List F → List F) (l : List α) (g : α → Ledger F) :
    Finsupp.mapDomain f (l.map g).sum = (l.map fun x => Finsupp.mapDomain f (g x)).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp [Finsupp.mapDomain_add, ih]

/-- Chunked receivers with equal channel and key. -/
def Clash (x y : Part F) : Prop :=
  x.recv = true → y.recv = true → x.chunks ≠ [] → y.chunks ≠ [] → x.tag = y.tag → x.sub = y.sub →
    x.key = y.key → False

theorem unique_of_pairwise {X : List (Part F)} (h : X.Pairwise Clash) :
    ∀ j (hj : j < X.length) j' (hj' : j' < X.length), X[j].recv = true →
      X[j'].recv = true → X[j].chunks ≠ [] → X[j'].chunks ≠ [] → X[j].tag = X[j'].tag →
      X[j].sub = X[j'].sub → X[j].key = X[j'].key → j = j' := by
  intro j hj j' hj' r r' c c' tg sb ky
  by_contra ne
  rcases Nat.lt_or_gt_of_ne ne with lt | lt
  · exact List.pairwise_iff_getElem.mp h j j' hj hj' lt r r' c c' tg sb ky
  · exact List.pairwise_iff_getElem.mp h j' j hj' hj lt r' r c' c tg.symm sb.symm ky.symm

theorem pairwise_tableParts {tables : List (Stacked F)} {mainT : Nat → Nat → Nat → F} {bound : Nat}
    (small : SmallCast F bound) (channels : (tables.map fun T => (T.tag, T.sub)).Nodup)
    (keysSmall : ∀ T ∈ tables, T.keyBase + T.rows ≤ bound) :
    (tableParts tables mainT).Pairwise Clash := by
  unfold tableParts
  rw [List.pairwise_flatMap]
  constructor
  · rintro ⟨T, t⟩ ht
    have hT := List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.mp ht)
    dsimp only
    rw [List.pairwise_map]
    apply List.Pairwise.imp_of_mem _ List.nodup_range
    intro r r' hr hr' ne _ _ _ _ _ _ ky
    have hr := List.mem_range.mp hr
    have hr' := List.mem_range.mp hr'
    rw [(Stacked.part_fields T _).2.2.2.1, (Stacked.part_fields T _).2.2.2.1, Stacked.key_assign T _ hr,
      Stacked.key_assign T _ hr'] at ky
    have := keysSmall T hT
    exact ne (by have := small.inj (by omega) (by omega) ky; omega)
  · have nd : (tables.zipIdx.map fun a => (a.1.tag, a.1.sub)).Nodup := by
      have e : (tables.zipIdx.map fun a => (a.1.tag, a.1.sub)) =
          (tables.zipIdx.map Prod.fst).map (fun T => (T.tag, T.sub)) := by
        rw [List.map_map]; rfl
      rw [e, List.zipIdx_map_fst]
      exact channels
    have pw := List.pairwise_map.mp nd
    refine pw.imp ?_
    rintro ⟨T, t⟩ ⟨T', t'⟩ ne x hx y hy _ _ _ _ tg sb _
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨r', _, rfl⟩ := List.mem_map.mp hy
    rw [(Stacked.part_fields T _).1, (Stacked.part_fields T' _).1] at tg
    rw [(Stacked.part_fields T _).2.1, (Stacked.part_fields T' _).2.1] at sb
    exact ne (by simp [tg, sb])

end Parts

open Aiur.Circuit
open Aiur.Optimized
open Bridge
open Sharded

/-- **End to end, periodic shards and stacked tables.** `narrow_heap_sound_v2`
with the map tables and the ROM as stacked tables beside the shards. Map rows
are fixed; ROM words are witness values at fixed addresses `keyBase + r`, so
the ROM is the one the trace holds (`romEntries`): it is valid, and the result
is represented in it. -/
theorem narrow_heap_sound_stacked {source : Generic.Source F} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id) (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries)
    {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)} {output : WireValue F}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Circuit.Message F}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    -- the sharded layout
    (idOf : String → Nat) {S : Sharded F} (ok : S.check = true)
    {units : List (Chip F × Option (Unroll F))} (chipsIn : ∀ u ∈ units, u.1 ∈ plan.singles)
    (unrolled : ∀ u ∈ units, unitOk idOf u = true)
    {wide : List (Circuit F)} {groups : List (List (List Nat))}
    (circuits : S.system.circuits = List.zipWith Circuit.mergeBy wide groups)
    (wideEq : wide = units.map (unitCircuit idOf))
    (lenG : groups.length = wide.length)
    (merged : ∀ j (hw : j < wide.length) (hg : j < groups.length), wide[j].checkMerge groups[j] = true)
    -- the stacked tables
    {tables : List (Stacked F)} (tablesOk : ∀ T ∈ tables, T.check S = true)
    (kinds : ∀ T ∈ tables, T.checkMap = true ∨ T.checkRom = true)
    (channels : (tables.map fun T => (T.tag, T.sub)).Nodup)
    (mapsIn : ∀ T ∈ tables, T.checkMap = true → ∀ r < T.rows,
      T.tag :: T.sub :: T.data.getD r [] ∈ (Depth.system cfg prepared.system).mapClaims.map (encode idOf))
    (capacity : capacityRowsU units S.system ≤ 2 ^ 39)
    {bound : Nat} (small : SmallCast F bound) (tags : 3 < bound)
    (codesBound : ∀ e ∈ S.buses, e.2.1 < bound) (labels : copyKey S.labelTotal < bound)
    (shadowBound : ∀ k < S.shards.length, ((S.layout k).shadow S.width).bound ≤ bound)
    (lookups : capacityLookupsU units S.system < bound) (ids : S.system.instances ≤ bound)
    (keysSmall : ∀ T ∈ tables, T.keyBase + T.rows ≤ bound)
    (parts : (S.system.enumerate S.system.lookupCount).length + 1 + (tables.map (·.rows)).sum < bound)
    (characteristic : ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ cfg.bits → (n : F) ≠ 0)
    (shaped : Shaped.check (Depth.system cfg prepared.system) plan.singles idOf root bound = true)
    (context : (Depth.system cfg prepared.system).checkContext (Erasure.rawROM ⟨[]⟩) root = .ok ())
    (req : (Part.request S.width (encode idOf root)).checkRequest S.system (encode idOf root) = true)
    (req2 : S.checkRequest2 (Part.request S.width (encode idOf root)) = true)
    -- the traces
    {H : Nat → Nat} {main : Nat → Nat → Nat → F} {HT : Nat → Nat} {mainT : Nat → Nat → Nat → F}
    (tall : ∀ k < S.shards.length, ((S.layout k).shadow S.width).places.length ≤ H k)
    (tallT : ∀ t T, tables[t]? = some T → T.rows ≤ HT t)
    (rows : ∀ k < S.shards.length, ∀ p < H k,
      Scalar.Circuit.Satisfies (S.circuit k).constraints (S.assign k (main k) p))
    (balanced : Finsupp.mapDomain trimZeros (S.ledger H main + tableLedger S tables HT mainT +
      S.padded2 (Part.request S.width (encode idOf root))) = 0)
    (enablesOk : ∀ c ∈ plan.singles, checkEnables bound c = true) :
    ∃ rom : WidthROM F, rom.entries = romEntries tables mainT ∧ rom.Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system rom).decode specialized.program.enums)
          heap value result := by
  set rom : WidthROM F := ⟨romEntries tables mainT⟩
  have romOf : ∀ T ∈ tables, T.rom = true → T.checkRom = true := by
    intro T hT hr
    rcases kinds T hT with h | h
    · simp [Stacked.checkMap, hr] at h
    · exact h
  have valid : rom.Valid := by
    intro a ha b hb addr len
    obtain ⟨T, t, r, hT, hrom, hr, rfl⟩ := mem_romEntries ha
    obtain ⟨T', t', r', hT', hrom', hr', rfl⟩ := mem_romEntries hb
    have mT := List.mem_of_getElem? hT
    have mT' := List.mem_of_getElem? hT'
    have cr := romOf T mT hrom
    have cr' := romOf T' mT' hrom'
    have l := (Stacked.rom_tuple cr (T.assign (mainT t) r)).2
    have l' := (Stacked.rom_tuple cr' (T'.assign (mainT t') r')).2
    simp only [Stacked.checkRom, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at cr cr'
    have sub : T.sub = T'.sub := by rw [cr.1.2, cr'.1.2, ← l, ← l', len]
    have tag : T.tag = T'.tag := by
      simp only [Stacked.rom, beq_iff_eq] at hrom hrom'
      rw [hrom, hrom']
    have ht : t = t' := by
      have hlt := (List.getElem?_eq_some_iff.mp hT).1
      have hlt' := (List.getElem?_eq_some_iff.mp hT').1
      apply (List.Nodup.getElem_inj_iff channels (i := t) (j := t') (hi := by simpa using hlt)
        (hj := by simpa using hlt')).mp
      simp only [List.getElem_map]
      rw [Option.some.inj ((List.getElem?_eq_getElem hlt).symm.trans hT),
        Option.some.inj ((List.getElem?_eq_getElem hlt').symm.trans hT'), tag, sub]
    subst ht
    rw [hT] at hT'
    obtain rfl := Option.some.inj hT'
    simp only [Stacked.entry, Stacked.key_assign T _ hr, Stacked.key_assign T _ hr'] at addr
    have := keysSmall T mT
    have rr : r = r' := by have := small.inj (by omega) (by omega) addr; omega
    subst rr
    rfl
  have context' : (Depth.system cfg prepared.system).checkContext (Erasure.rawROM rom) root = .ok () := by
    obtain ⟨formed, pub, _, wf⟩ := System.checkContext_iff.mp context
    exact System.checkContext_iff.mpr ⟨formed, pub, Erasure.rawROM_valid valid, wf⟩
  have romPacked : ∀ e ∈ (Erasure.rawROM rom).entries,
      e.2.type = .tuple (List.replicate e.2.words.length .field) := by
    intro e he
    simp only [Erasure.rawROM, List.mem_map] at he
    obtain ⟨_, _, rfl⟩ := he
    simp [Erasure.pack]
  set request := Part.request S.width (encode idOf root)
  have reqFacts : request.Request S.system (encode idOf root) := Part.Request.of_check req
  obtain ⟨_, _, _, nodup, mods⟩ := check_parts ok
  have keyed := (check_parts ok).1
  have valid' := S.system.valid_of_checkKeyed keyed
  have sep : S.Separated bound :=
    ⟨small, by simpa [system] using valid'.width.1, fun e he => ⟨codesBound e he, mods e he⟩, nodup, labels⟩
  set XT := tableParts tables mainT
  have facts : ∀ x ∈ XT, x.recv = true ∧ S.checkRequest2 x = true ∧ x.Formed S.system.width ∧
      x.RowsIn S.system.roleOf S.system.arityAt ∧
      (x.chunks = [] → S.system.arityAt (x.tag, x.sub) = some x.payload.length) ∧
      (x.chunks ≠ [] → (x.tag, x.sub) ∉ S.system.receivers) := by
    intro x hx
    obtain ⟨T, t, r, hT, _, rfl⟩ := mem_tableParts hx
    have c := tablesOk T (List.mem_of_getElem? hT)
    obtain ⟨ne, bus⟩ := Stacked.check_parts c
    exact ⟨(Stacked.part_fields T _).2.2.1, Stacked.checkRequest2_part ne bus _, Stacked.check_facts c _⟩
  set ext := S.padded2 request + (XT.map S.padded2).sum
  have balanced' : Finsupp.mapDomain trimZeros (S.ledger H main + ext) = 0 := by
    rw [tableLedger_eq tablesOk tallT] at balanced
    rw [← balanced, add_assoc]
    congr 2
    exact add_comm _ _
  have extShape : ∀ t, ext t ≠ 0 → S.MsgShape t := by
    intro t h
    simp only [ext, Finsupp.add_apply] at h
    by_cases h0 : S.padded2 request t = 0
    · rw [h0, zero_add] at h
      obtain ⟨x, hx, hne⟩ := exists_of_sum_ne h
      exact padded2_shape (facts x hx).2.1 t hne
    · exact padded2_shape req2 t h0
  have extParts : Finsupp.mapDomain S.proj2 ext = ((request :: XT).map Part.narrow).sum := by
    simp only [ext, Finsupp.mapDomain_add, mapDomain_list_sum, List.map_cons, List.sum_cons]
    rw [padded2_proj sep reqFacts.arity reqFacts.rowsIn req2]
    congr 1
    congr 1
    apply List.map_congr_left
    intro x hx
    have f := facts x hx
    exact padded2_proj sep f.2.2.2.2.1 f.2.2.2.1 f.2.1
  have pw : (request :: XT).Pairwise Clash := by
    refine List.pairwise_cons.mpr ⟨fun y _ r _ => ?_, pairwise_tableParts small channels keysSmall⟩
    rw [reqFacts.send] at r
    cases r
  obtain ⟨holds, wideBalanced⟩ := S.sound ok small codesBound labels shadowBound ids (request :: XT)
    (by simp only [List.length_cons, XT, length_tableParts]; omega) tall rows extShape extParts
    (by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨reqFacts.formed, reqFacts.rowsIn⟩
      · exact ⟨(facts x hx).2.2.1, (facts x hx).2.2.2.1⟩)
    (by
      intro x hx hr hc
      rcases List.mem_cons.mp hx with rfl | hx
      · rw [reqFacts.send] at hr; cases hr
      · exact (facts x hx).2.2.2.2.2 hc)
    (unique_of_pairwise pw) balanced'
  let sys' : System F := { S.system with circuits := wide }
  have lenC : S.system.circuits.length = wide.length := by
    rw [circuits, List.length_zipWith, lenG, Nat.min_self]
  have circuitAt : ∀ f (hw : f < wide.length), S.system.circuits[f]? =
      some (wide[f].mergeBy (groups[f]'(by omega))) := by
    intro f hw
    rw [circuits, List.getElem?_zipWith, List.getElem?_eq_getElem hw,
      List.getElem?_eq_getElem (show f < groups.length by omega)]
  have ledgerEq : S.system.wideLedger (S.system.wideRow (S.mainV main)) =
      sys'.wideLedger (sys'.wideRow (S.mainV main)) := by
    simp only [System.wideLedger, sys', lenC]
    congr 1
    apply List.map_congr_left
    intro f hf
    have hw : f < wide.length := List.mem_range.mp hf
    congr 1
    apply List.map_congr_left
    intro i _
    rw [circuitAt f hw, List.getElem?_eq_getElem hw]
    simp only [Option.map_some, Option.getD_some]
    exact rowLedger_mergeBy (merged f hw (by omega)) _
  rw [ledgerEq] at wideBalanced
  have wideEq' : wide = units.map (unitCircuit idOf) ++ ([] : List (List F)).map tableCircuit := by
    simp [wideEq]
  obtain ⟨tables0, support, split⟩ := System.wideLedger_units sys' wideEq' unrolled (S.mainV main)
  have zero0 : tables0 = 0 := by
    ext t
    by_contra h
    simpa using support t h
  rw [split, zero0, add_zero] at wideBalanced
  have requestWide : request.wide = Finsupp.single (encode idOf root) 1 := by
    simp [Part.wide, reqFacts.tuple, reqFacts.weight]
  simp only [List.map_cons, List.sum_cons, requestWide] at wideBalanced
  rw [← add_assoc] at wideBalanced
  have W : Wide plan idOf bound (Erasure.rawROM rom) root
      (instancesU idOf units S.system (S.mainV main)) (XT.map Part.wide).sum := {
    chips := fun p hp => by
      obtain ⟨f, hf, i, _, e, _⟩ := mem_instancesU hp
      rw [e]
      exact chipsIn _ (List.getElem_mem hf)
    holds := fun p hp => by
      obtain ⟨f, hf, i, hi, e, hr⟩ := mem_instancesU hp
      have hw : f < wide.length := by rw [wideEq]; simp; omega
      have lt : f < S.system.circuits.length := by rw [lenC]; exact hw
      have hw' : wide[f]? = some (unitCircuit idOf units[f]) := by
        rw [wideEq]
        simp [hf]
      have ec : (S.system.circuits[f]'lt).constraints = (unitCircuit idOf units[f]).constraints := by
        rw [Option.some.inj ((List.getElem?_eq_getElem lt).symm.trans (circuitAt f hw)), mergeBy_constraints,
          Option.some.inj ((List.getElem?_eq_getElem hw).symm.trans hw')]
      have := holds f lt i hi
      have h' : (unitCircuit idOf units[f]).Holds (S.system.wideRow (S.mainV main) f i) := by
        unfold Circuit.Holds at this ⊢
        rw [ec] at this
        exact this
      rw [e]
      exact unit_holds h' _ hr
    small := small
    enablesOk := enablesOk
    tags := by omega
    count := by rw [lookupCount_instancesU]; exact lookups
    shaped := Shaped.of_check shaped
    romPacked := romPacked
    tableSupport := fun t ht => by
      obtain ⟨x, hx, hne⟩ := exists_of_sum_ne ht
      have tx : t = x.tuple := by
        by_contra h
        simp [Part.wide, Finsupp.single_apply, Ne.symm h] at hne
      obtain ⟨T, t', r, hT, hr, rfl⟩ := mem_tableParts hx
      have mT := List.mem_of_getElem? hT
      rcases kinds T mT with km | kr
      · left
        rw [tx, Stacked.map_tuple km _ hr]
        obtain ⟨mc, hmc, e⟩ := List.mem_map.mp (mapsIn T mT km r hr)
        exact ⟨mc, hmc, e.symm⟩
      · right
        refine ⟨_, ?_, by rw [tx]; exact (Stacked.rom_tuple kr _).1⟩
        apply (Erasure.mem_rawROM).mpr
        simp only [rom, romEntries, List.mem_flatMap]
        refine ⟨(T, t'), List.mk_mem_zipIdx_iff_getElem?.mpr hT, ?_⟩
        have hrom : T.rom = true := by simp [Stacked.checkRom] at kr; exact kr.1.1.1.1
        simp only [hrom, if_true, List.mem_map, List.mem_range]
        exact ⟨r, hr, rfl⟩
    balanced := wideBalanced }
  obtain ⟨weighted, length, checked⟩ := W.checkMemo activated context'
  exact ⟨rom, rfl, valid, prepared.depth_grouped_activated_heap_sound compiled certified plan activated entry valid
    signed rooted outside ((length.trans (length_instancesU _ _ _ _).le).trans capacity) characteristic checked
    arguments decoded⟩

end Aiur.Tiling.Periodic
