import Aiur.Tiling.PeriodicStacked

/-!
# Compact tables beside the periodic shards

A compact table is one circuit beside the shards that holds many receiver
parts of many channels, one narrow row tuple per physical row. It replaces one
`Stacked` circuit per channel and one ROM circuit per word count.

Columns, for shard width `W` and `n = nFixed`:

* main column 0 is the row's count; main columns `1 … W − 1 − n` are the
  witness cells `n … W − 2`;
* fixed column 0 is `selL` (the row is on a lane channel), 1 is `selW`
  (the row is on a full-width channel), 2 is the bus code of the row's key,
  and `3 + j` is cell `j` for `j < n`.

The two lookups are `push(−selL·count, [code, cell₀, cell₁, cell₂])` and
`push(−selW·count, [code, cell₀, …, cell_{W−2}])`. A row of an unchunked part
is the part's tuple; row `c` of a chunked part is its chunk `c`,
`[code_c, key, chunk_c …]`. Cells past the row key's arity are free: the v2
projection cuts them (`proj2`). Each row carries its own count, so the chunks
of one receiver may have different weights (`Part.cweights`); chunk balance
against boolean senders forces them equal.

Two kinds are used. A **map table** has `n = W − 1`: every cell is fixed, so
its parts are the static `CPart`s, checked against the map claims. A **ROM
table** has `n = 1`: the key (the address) is fixed and the words are
witness values, so the ROM is the one the trace holds. One ROM table holds
every word count.

`Compact.fixedAt` is the fixed matrix; it is computed from the static
description alone.
-/

namespace Aiur.Tiling.Periodic

open Aiur.Scalar.Circuit (ArithExpr Var Satisfies)

variable {F : Type} [Field F] [DecidableEq F]

/-- The static description of one receiver part. A ROM part's `payload` holds
its address followed by placeholder words of the right count. -/
structure CPart (F : Type) where
  tag : F
  sub : F
  key : F
  payload : List F
  /-- Chunk lengths; empty for an unchunked part. -/
  lens : List Nat
  deriving Repr

namespace CPart

variable (q : CPart F)

def rom : Bool := q.tag == 2

def chunked : Bool := !q.lens.isEmpty

def nrows : Nat := if q.chunked then q.lens.length else 1

/-- The payload after a ROM read's address key. -/
def body : List F := if q.rom then q.payload.drop 1 else q.payload

def chunkVals (c : Nat) : List F := (q.body.drop (q.lens.take c).sum).take (q.lens.getD c 0)

def rowKey (c : Nat) : F × F := if q.chunked then (q.tag, chunkSub q.rom q.sub c) else (q.tag, q.sub)

/-- The values of row `c`'s cells, as far as they are known statically. -/
def rowCells (c : Nat) : List F := if q.chunked then q.key :: q.chunkVals c else q.payload

def rowArity (c : Nat) : Nat := if q.chunked then q.lens.getD c 0 + 1 else q.payload.length

/-- The payload length of the trace's part. -/
def payloadLen : Nat := if q.chunked then (if q.rom then 1 else 0) + q.lens.sum else q.payload.length

/-- The receiver part read from the trace: `cells c` are the cells of row `c`
and `count c` its count. -/
def trace (cells : Nat → List F) (count : Nat → F) : Part F :=
  if q.chunked then
    ⟨q.tag, q.sub, (if q.rom then [q.key] else []) ++
        ((List.range q.lens.length).map fun c => ((cells c).drop 1).take (q.lens.getD c 0)).flatten,
      -count 0, true, q.key,
      (List.range q.lens.length).map (fun c => ((cells c).drop 1).take (q.lens.getD c 0)),
      (List.range q.lens.length).map fun c => -count c⟩
  else ⟨q.tag, q.sub, (cells 0).take q.payload.length, -count 0, true, q.key, [], []⟩

end CPart

structure Compact (F : Type) where
  /-- Cells `0 … nFixed − 1` are fixed columns, the others main columns. -/
  nFixed : Nat
  parts : List (CPart F)
  deriving Repr

/-- The part and row of physical row `r`, for blocks of `ns` rows. -/
def locateBlock : List Nat → Nat → Option (Nat × Nat)
  | [], _ => none
  | n :: ns, r => if r < n then some (0, r) else (locateBlock ns (r - n)).map fun x => (x.1 + 1, x.2)

def blockOffset (ns : List Nat) (i : Nat) : Nat := (ns.take i).sum

theorem locateBlock_offset : ∀ (ns : List Nat) {i c : Nat} (hi : i < ns.length), c < ns[i] →
    locateBlock ns (blockOffset ns i + c) = some (i, c)
  | [], _, _, hi, _ => by simp at hi
  | n :: ns, 0, c, _, hc => by simp [locateBlock, blockOffset] at hc ⊢; omega
  | n :: ns, i + 1, c, hi, hc => by
      have ih := locateBlock_offset ns (i := i) (c := c) (by simpa using hi) (by simpa using hc)
      simp only [blockOffset, List.take_succ_cons, List.sum_cons] at ih ⊢
      simp only [locateBlock]
      rw [if_neg (by omega), show n + (ns.take i).sum + c - n = (ns.take i).sum + c by omega, ih]
      rfl

theorem locateBlock_none : ∀ (ns : List Nat) {r : Nat}, ns.sum ≤ r → locateBlock ns r = none
  | [], _, _ => rfl
  | n :: ns, r, h => by
      simp only [List.sum_cons] at h
      simp only [locateBlock, if_neg (show ¬ r < n by omega), locateBlock_none ns (show ns.sum ≤ r - n by omega),
        Option.map_none]

theorem locateBlock_some : ∀ (ns : List Nat) {r i c : Nat}, locateBlock ns r = some (i, c) →
    c < ns.getD i 0
  | [], _, _, _, h => by simp [locateBlock] at h
  | n :: ns, r, i, c, h => by
      simp only [locateBlock] at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simpa
      · obtain ⟨⟨i', c'⟩, h', e⟩ := Option.map_eq_some_iff.mp h
        simp only [Prod.mk.injEq] at e
        obtain ⟨rfl, rfl⟩ := e
        simpa using locateBlock_some ns h'

/-- Sums over blocks of consecutive rows. -/
theorem sum_blocks {M : Type} [AddCommMonoid M] :
    ∀ (ns : List Nat) (f : Nat → M), ∑ r ∈ Finset.range ns.sum, f r =
      ∑ i ∈ Finset.range ns.length, ∑ c ∈ Finset.range (ns.getD i 0), f (blockOffset ns i + c)
  | [], f => by simp
  | n :: ns, f => by
      rw [List.sum_cons, Finset.sum_range_add, sum_blocks ns, List.length_cons, Finset.sum_range_succ']
      simp only [List.getD_cons_zero, List.getD_cons_succ, blockOffset, List.take_succ_cons, List.sum_cons,
        List.take_zero, List.sum_nil, zero_add, add_assoc]
      rw [add_comm]

namespace Compact

variable (T : Compact F) (W : Nat)

def mainWidth : Nat := 1 + (W - 1 - T.nFixed)

def cellVar (j : Nat) : Var := if j < T.nFixed then T.mainWidth W + 3 + j else 1 + (j - T.nFixed)

def counts : List Nat := T.parts.map CPart.nrows

def rows : Nat := T.counts.sum

/-- The part and row number of physical row `r`. -/
def at? (r : Nat) : Option (CPart F × Nat) :=
  (locateBlock T.counts r).bind fun x => T.parts[x.1]?.map (·, x.2)

/-- Fixed column `k` of physical row `r`: `selL`, `selW`, code, fixed cells. -/
def fixedAt (buses : Buses F) (r k : Nat) : F :=
  match T.at? r with
  | none => 0
  | some (q, c) =>
      let e := (buses.lookup (q.rowKey c)).getD (0, false)
      match k with
      | 0 => if e.2 then 1 else 0
      | 1 => if e.2 then 0 else 1
      | 2 => ((e.1 : Nat) : F)
      | j + 3 => (q.rowCells c).getD j 0

def assign (buses : Buses F) (main : Nat → Nat → F) (r : Nat) (v : Var) : F :=
  if v < T.mainWidth W then main r v else T.fixedAt buses r (v - T.mainWidth W)

def cellsAt (a : Var → F) : List F := (List.range (W - 1)).map fun j => a (T.cellVar W j)

def lookupL : Lookup F :=
  ⟨.sub (.const 0) (.mul (.var (T.mainWidth W)) (.var 0)),
    .var (T.mainWidth W + 2) :: (List.range 3).map fun j => .var (T.cellVar W j)⟩

def lookupW : Lookup F :=
  ⟨.sub (.const 0) (.mul (.var (T.mainWidth W + 1)) (.var 0)),
    .var (T.mainWidth W + 2) :: (List.range (W - 1)).map fun j => .var (T.cellVar W j)⟩

def circuit : Circuit F where
  width := T.mainWidth W
  fixedWidth := 3 + T.nFixed
  constraints := []
  lookups := [T.lookupL W, T.lookupW W]

noncomputable def ledger (buses : Buses F) (H : Nat) (main : Nat → Nat → F) : Ledger F :=
  ∑ p ∈ Finset.range H, (T.circuit W).rowLedger (T.assign W buses main p)

/-- The parts read from a trace of the table. -/
def traceParts (buses : Buses F) (main : Nat → Nat → F) : List (Part F) :=
  T.parts.zipIdx.map fun (q, i) =>
    q.trace (fun c => T.cellsAt W (T.assign W buses main (blockOffset T.counts i + c)))
      (fun c => main (blockOffset T.counts i + c) 0)

/-- Row `c` of part `q` after the v2 projection, with cell values `g`. -/
def projRow (q : CPart F) (c : Nat) (g : Nat → F) : List F :=
  (q.rowKey c).1 :: (q.rowKey c).2 :: (List.range (q.rowArity c)).map g

end Compact

/-! ## Physical rows -/

namespace Compact

variable {T : Compact F} {W : Nat}

theorem at?_offset {i c : Nat} (hi : i < T.parts.length) (hc : c < T.parts[i].nrows) :
    T.at? (blockOffset T.counts i + c) = some (T.parts[i], c) := by
  have hi' : i < T.counts.length := by simpa [counts] using hi
  rw [at?, locateBlock_offset T.counts hi' (by simpa [counts] using hc)]
  simp [List.getElem?_eq_getElem hi]

theorem at?_none {r : Nat} (h : T.rows ≤ r) : T.at? r = none := by
  simp [at?, locateBlock_none T.counts h]

theorem cellVar_main {j : Nat} (h : T.nFixed ≤ j) (hj : j < W - 1) : T.cellVar W j < T.mainWidth W := by
  unfold cellVar mainWidth
  split
  · omega
  · show 1 + (j - T.nFixed) < 1 + (W - 1 - T.nFixed)
    have : T.nFixed ≤ j := h
    have : j < W - 1 := hj
    omega

theorem assign_fixed (buses : Buses F) (main : Nat → Nat → F) {r : Nat} {q : CPart F} {c : Nat}
    (h : T.at? r = some (q, c)) {j : Nat} (hj : j < T.nFixed) :
    T.assign W buses main r (T.cellVar W j) = (q.rowCells c).getD j 0 := by
  simp only [assign, cellVar, if_pos hj, show ¬ (T.mainWidth W + 3 + j < T.mainWidth W) by omega,
    if_false, show T.mainWidth W + 3 + j - T.mainWidth W = j + 3 by omega, fixedAt, h]

theorem rowLedger_none (buses : Buses F) (main : Nat → Nat → F) {r : Nat} (h : T.at? r = none) :
    (T.circuit W).rowLedger (T.assign W buses main r) = 0 := by
  have z : ∀ k, T.assign W buses main r (T.mainWidth W + k) = 0 := fun k => by
    simp [assign, fixedAt, h]
  have z0 := z 0
  simp only [add_zero] at z0
  simp [Circuit.rowLedger, circuit, Lookup.entry, lookupL, lookupW, ArithExpr.denote, z, z0]

/-- The tuple of a row on a lane (`lane`) or full-width channel. -/
def rowTuple (code : Nat) (lane : Bool) (g : Nat → F) : List F :=
  ((code : Nat) : F) :: (List.range (if lane then 3 else W - 1)).map g

theorem rowLedger_some (buses : Buses F) (main : Nat → Nat → F) {r : Nat} {q : CPart F} {c : Nat}
    (h : T.at? r = some (q, c)) {code : Nat} {lane : Bool}
    (hl : buses.lookup (q.rowKey c) = some (code, lane)) :
    (T.circuit W).rowLedger (T.assign W buses main r) =
      Finsupp.single (rowTuple (W := W) code lane fun j => T.assign W buses main r (T.cellVar W j))
        (-main r 0) := by
  have mw : 0 < T.mainWidth W := by simp [mainWidth]
  have f0 : T.assign W buses main r (T.mainWidth W) = if lane then 1 else 0 := by
    simp [assign, fixedAt, h, hl]
  have f1 : T.assign W buses main r (T.mainWidth W + 1) = if lane then 0 else 1 := by
    simp [assign, fixedAt, h, hl]
  have f2 : T.assign W buses main r (T.mainWidth W + 2) = ((code : Nat) : F) := by
    simp [assign, fixedAt, h, hl]
  have m0 : T.assign W buses main r 0 = main r 0 := by simp [assign, mw]
  cases lane <;>
    simp [Circuit.rowLedger, circuit, Lookup.entry, Lookup.tuple, lookupL, lookupW, ArithExpr.denote,
      f0, f1, f2, m0, rowTuple, List.map_map, Function.comp_def]

end Compact

/-! ## Static checks -/

namespace CPart

/-- Every row of `q` has a bus entry, fits its channel's tuple and has arity
`rowArity`; a chunked part has the system's chunk roles, does not fit one row
and uses a channel without an in-system receiver; an unchunked part fits one
row and has no chunk role. -/
def check (S : Sharded F) (q : CPart F) : Bool :=
  (List.range q.nrows).all (fun c =>
    match S.buses.lookup (q.rowKey c) with
    | some (_, lane) => decide (q.rowArity c + 1 ≤ if lane then 4 else S.width) &&
        S.system.arityAt (q.rowKey c) == some (q.rowArity c)
    | none => false) &&
  (if q.chunked then
    decide (2 ≤ q.lens.length) && decide (S.width ≤ q.payloadLen) &&
      (List.range q.lens.length).all (fun c =>
        S.system.roleOf (q.rowKey c) == some (q.sub, some (c, q.lens.length, q.rom))) &&
      !(S.system.receivers.contains (q.tag, q.sub))
  else
    decide (q.payload.length + 1 ≤ S.width) &&
      (match S.system.roleOf (q.tag, q.sub) with
        | some r => r.2.isNone
        | none => true))

end CPart

namespace CPart

/-- What `check` reads of a part: channel, chunk lengths, payload length. -/
def shape (q : CPart F) : F × F × List Nat × Nat := (q.tag, q.sub, q.lens, q.payload.length)

/-- A part of shape `sh`. -/
def ofShape (sh : F × F × List Nat × Nat) : CPart F := ⟨sh.1, sh.2.1, 0, List.replicate sh.2.2.2 0, sh.2.2.1⟩

theorem check_shape (S : Sharded F) (q : CPart F) : q.check S = (ofShape q.shape).check S := by
  have : q.payload.length = (ofShape q.shape).payload.length := by simp [ofShape, shape]
  unfold check rowKey rowArity payloadLen nrows chunked rom
  rw [this]
  rfl

end CPart

/-- The distinct elements of a list, in first-seen order reversed. -/
def distinct {α : Type} [DecidableEq α] (l : List α) : List α :=
  l.foldl (fun acc x => if x ∈ acc then acc else x :: acc) []

theorem mem_distinct {α : Type} [DecidableEq α] {l : List α} {x : α} (h : x ∈ l) : x ∈ distinct l := by
  have gen : ∀ (l : List α) (acc : List α), (∀ y ∈ acc, y ∈ l.foldl (fun acc x => if x ∈ acc then acc else x :: acc) acc) ∧
      ∀ y ∈ l, y ∈ l.foldl (fun acc x => if x ∈ acc then acc else x :: acc) acc := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons z l ih =>
        intro acc
        simp only [List.foldl_cons]
        have keep := (ih (if z ∈ acc then acc else z :: acc)).1
        refine ⟨fun y hy => keep y (by split <;> simp_all), fun y hy => ?_⟩
        rcases List.mem_cons.mp hy with rfl | hy
        · exact keep _ (by split <;> simp_all)
        · exact (ih _).2 y hy
  exact (gen l []).2 x h

namespace Compact

/-- The table's cells fit the shard width, cell 0 (a chunk row's key) is
fixed, and every part passes `CPart.check`; the check runs once per distinct
shape. -/
def check (S : Sharded F) (T : Compact F) : Bool :=
  decide (1 ≤ T.nFixed) && decide (T.nFixed + 1 ≤ S.width) &&
    (distinct (T.parts.map CPart.shape)).all fun sh => (CPart.ofShape sh).check S

end Compact

/-! ## Parts read from the trace -/

namespace CPart

variable {S : Sharded F} {q : CPart F}

theorem check_row (ok : q.check S = true) {c : Nat} (hc : c < q.nrows) :
    ∃ code lane, S.buses.lookup (q.rowKey c) = some (code, lane) ∧
      q.rowArity c + 1 ≤ (if lane then 4 else S.width) ∧ S.system.arityAt (q.rowKey c) = some (q.rowArity c) := by
  simp only [check, Bool.and_eq_true, List.all_eq_true, List.mem_range] at ok
  have := ok.1 c hc
  cases hl : S.buses.lookup (q.rowKey c) with
  | none => simp [hl] at this
  | some e =>
      obtain ⟨code, lane⟩ := e
      simp only [hl, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
      exact ⟨code, lane, rfl, this⟩

theorem nrows_chunked (h : q.chunked = true) : q.nrows = q.lens.length := by simp [nrows, h]

theorem lens_ne (h : q.chunked = true) : q.lens ≠ [] := by
  simpa [chunked] using h

theorem take_drop_range (g : Nat → F) {L m : Nat} (h : L + 1 ≤ m) :
    (((List.range m).map g).drop 1).take L = (List.range L).map fun j => g (j + 1) := by
  apply List.ext_getElem
  · simp; omega
  · intro n h1 h2
    simp

theorem take_range_map (g : Nat → F) {L m : Nat} (h : L ≤ m) :
    ((List.range m).map g).take L = (List.range L).map g := by
  apply List.ext_getElem
  · simp; omega
  · intro n h1 h2
    simp

/-- The facts `Sharded.sound` needs of a part read from the trace. -/
theorem trace_facts (ok : q.check S = true) (W4 : 4 ≤ S.width) {g : Nat → Nat → F} {count : Nat → F} :
    let x := q.trace (fun c => (List.range (S.width - 1)).map (g c)) count
    x.recv = true ∧ S.checkRequest2 x = true ∧ x.Formed S.system.width ∧
      x.RowsIn S.system.roleOf S.system.arityAt ∧
      (x.chunks = [] → S.system.arityAt (x.tag, x.sub) = some x.payload.length) ∧
      (x.chunks ≠ [] → (x.tag, x.sub) ∉ S.system.receivers) := by
  intro x
  have Wsys : S.system.width = S.width := rfl
  have rows := fun c hc => check_row (S := S) (q := q) ok (c := c) hc
  have ok' := ok
  simp only [check, Bool.and_eq_true] at ok'
  obtain ⟨_, rest⟩ := ok'
  by_cases ch : q.chunked = true
  · simp only [ch, if_true, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
      beq_iff_eq, Bool.not_eq_true'] at rest
    obtain ⟨⟨⟨two, wide⟩, roles⟩, nrecv⟩ := rest
    have fitsc : ∀ c < q.lens.length, q.lens.getD c 0 + 2 ≤ S.width := by
      intro c hc
      obtain ⟨_, lane, _, fit, _⟩ := rows c (by rw [nrows_chunked ch]; exact hc)
      simp only [rowArity, ch, if_true] at fit
      split at fit <;> omega
    have clen : ∀ c < q.lens.length,
        ((((List.range (S.width - 1)).map (g c)).drop 1).take (q.lens.getD c 0)).length = q.lens.getD c 0 := by
      intro c hc
      rw [take_drop_range _ (by have := fitsc c hc; omega)]; simp
    have xc : x.chunks = (List.range q.lens.length).map
        (fun c => (((List.range (S.width - 1)).map (g c)).drop 1).take (q.lens.getD c 0)) := by
      simp [x, trace, ch]
    have cne : x.chunks ≠ [] := by
      rw [xc]; simpa using lens_ne ch
    have xt : x.tag = q.tag := by simp [x, trace, ch]
    have xs : x.sub = q.sub := by simp [x, trace, ch]
    have xr : x.rom = q.rom := by simp [Part.rom, rom, xt]
    have xlen : x.chunks.length = q.lens.length := by rw [xc]; simp
    have getc : ∀ c < q.lens.length, (x.chunks.getD c []).length = q.lens.getD c 0 := by
      intro c hc
      rw [xc, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hc]
      simpa using clen c hc
    have plen : x.payload.length = q.payloadLen := by
      have : x.payload = (if q.rom then [q.key] else []) ++ x.chunks.flatten := by
        simp [x, trace, ch, xc]
      rw [this, List.length_append, List.length_flatten, xc, List.map_map]
      simp only [payloadLen, ch, if_true]
      congr 1
      · split <;> rfl
      · rw [List.map_congr_left (g := fun c => q.lens.getD c 0) (fun c hc => by
          simpa using clen c (List.mem_range.mp hc))]
        rw [sum_range_getElem q.lens _ id (fun r lt => by simp [List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem lt]), List.map_id]
    have key : ∀ c < x.chunks.length, (x.tag, chunkSub x.rom x.sub c) = q.rowKey c ∧
        (x.chunks.getD c []).length + 1 = q.rowArity c := by
      intro c hc
      rw [xlen] at hc
      exact ⟨by simp [rowKey, ch, xt, xr, xs], by simp only [rowArity, ch, if_true]; rw [getc c hc]⟩
    refine ⟨by simp [x, trace, ch], ?_, ?_, ⟨fun h => absurd h cne, fun _ c hc => ?_⟩,
      fun h => absurd h cne, fun _ => ?_⟩
    · simp only [Sharded.checkRequest2, Sharded.rowKeys, if_neg cne, List.all_eq_true, List.mem_map,
        List.mem_range]
      rintro _ ⟨c, hc, rfl⟩
      obtain ⟨k1, k2⟩ := key c hc
      obtain ⟨code, lane, hl, fit, _⟩ := rows c (by rw [nrows_chunked ch, ← xlen]; exact hc)
      simp only [k1, ← k2, hl] at fit ⊢
      exact decide_eq_true fit
    · refine Or.inr ⟨by rw [xlen]; exact two, by rw [Wsys, plen]; exact wide, by
          rw [xr, xc]; simp only [x, trace, ch, if_true],
        fun h => by simp [x, trace, ch] at h, Or.inr ⟨by simp [x, trace, ch], ?_⟩⟩
      have : 0 < q.lens.length := List.length_pos_iff.mpr (lens_ne ch)
      simp [x, trace, ch, Part.cweight, List.getD_eq_getElem?_getD, List.getElem?_range this]
    · obtain ⟨k1, k2⟩ := key c hc
      rw [xlen] at hc
      obtain ⟨_, _, _, _, ar⟩ := rows c (by rw [nrows_chunked ch]; exact hc)
      refine ⟨?_, by rw [k1, k2]; exact ar⟩
      rw [k1, xs, xlen, xr]
      exact roles c hc
    · rw [xt, xs]
      intro h
      rw [List.contains_iff_mem.mpr h] at nrecv
      cases nrecv
  · have ch : q.chunked = false := by simpa using ch
    simp only [ch, Bool.false_eq_true, if_false, Bool.and_eq_true, decide_eq_true_eq] at rest
    obtain ⟨fits, role⟩ := rest
    have xc : x.chunks = [] := by simp [x, trace, ch]
    have xt : x.tag = q.tag := by simp [x, trace, ch]
    have xs : x.sub = q.sub := by simp [x, trace, ch]
    have plen : x.payload.length = q.payload.length := by
      simp only [x, trace, ch, Bool.false_eq_true, if_false, List.length_take, List.length_map,
        List.length_range]
      omega
    obtain ⟨code, lane, hl, fit, ar⟩ := rows 0 (by simp [nrows, ch])
    simp only [rowKey, rowArity, ch, Bool.false_eq_true, if_false] at hl fit ar
    refine ⟨by simp [x, trace, ch], ?_, Or.inl ⟨xc, by rw [Wsys, plen]; exact fits⟩,
      ⟨fun _ r hr => ?_, fun h => absurd xc h⟩, fun _ => by rw [xt, xs, plen]; exact ar,
      fun h => absurd xc h⟩
    · simp only [Sharded.checkRequest2, Sharded.rowKeys, xc, if_true, List.all_cons, List.all_nil,
        Bool.and_true, xt, xs, plen, hl]
      exact decide_eq_true fit
    · rw [xt, xs] at hr
      rw [hr] at role
      simpa using role

theorem trace_length (ok : q.check S = true) (W4 : 4 ≤ S.width) {g : Nat → Nat → F} {count : Nat → F} :
    (q.trace (fun c => (List.range (S.width - 1)).map (g c)) count).payload.length = q.payloadLen := by
  have rows := fun c hc => check_row (S := S) (q := q) ok (c := c) hc
  by_cases ch : q.chunked = true
  · simp only [trace, ch, if_true, List.length_append, List.length_flatten, List.map_map, payloadLen]
    congr 1
    · split <;> rfl
    · rw [List.map_congr_left (g := fun c => q.lens.getD c 0) (fun c hc => by
          have hc := List.mem_range.mp hc
          obtain ⟨_, lane, _, fit, _⟩ := rows c (by rw [nrows_chunked ch]; exact hc)
          simp only [rowArity, ch, if_true] at fit
          have L : q.lens.getD c 0 + 1 ≤ S.width - 1 := by split at fit <;> omega
          simp only [Function.comp_def]
          rw [take_drop_range _ L]; simp)]
      rw [sum_range_getElem q.lens _ id (fun r lt => by simp [List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem lt]), List.map_id]
  · have ch : q.chunked = false := by simpa using ch
    have rest := ok
    simp only [check, Bool.and_eq_true, ch, Bool.false_eq_true, if_false, decide_eq_true_eq] at rest
    simp only [trace, ch, Bool.false_eq_true, if_false, List.length_take, List.length_map,
      List.length_range, payloadLen]
    omega

/-- The narrow encoding of a part read from the trace is its rows' projections. -/
theorem narrow_trace (ok : q.check S = true) (W4 : 4 ≤ S.width) {g : Nat → Nat → F} {count : Nat → F}
    (keyCell : q.chunked = true → ∀ c < q.lens.length, g c 0 = q.key) :
    (q.trace (fun c => (List.range (S.width - 1)).map (g c)) count).narrow =
      ∑ c ∈ Finset.range q.nrows, Finsupp.single (Compact.projRow q c (g c)) (-count c) := by
  have rows := fun c hc => check_row (S := S) (q := q) ok (c := c) hc
  by_cases ch : q.chunked = true
  · have cne : (q.trace (fun c => (List.range (S.width - 1)).map (g c)) count).chunks ≠ [] := by
      simpa [trace, ch] using lens_ne ch
    rw [Part.narrow, if_neg cne]
    have len : (q.trace (fun c => (List.range (S.width - 1)).map (g c)) count).chunks.length = q.nrows := by
      simp [trace, ch, nrows_chunked ch]
    rw [len]
    apply Finset.sum_congr rfl
    intro c hc
    have hc := Finset.mem_range.mp hc
    have hc' : c < q.lens.length := by rwa [nrows_chunked ch] at hc
    obtain ⟨_, lane, _, fit, _⟩ := rows c hc
    simp only [rowArity, ch, if_true] at fit
    have L : q.lens.getD c 0 + 1 ≤ S.width - 1 := by split at fit <;> omega
    congr 1
    · simp only [Part.chunkTuple, Compact.projRow, rowKey, rowArity, ch, if_true, trace, Part.rom, rom]
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hc', Option.map_some,
        Option.getD_some, take_drop_range _ L, List.range_succ_eq_map, List.map_cons, List.map_map,
        keyCell ch c hc']
      rfl
    · simp [trace, ch, Part.cweight, List.getD_eq_getElem?_getD, List.getElem?_range hc']
  · have ch : q.chunked = false := by simpa using ch
    have cp : (q.trace (fun c => (List.range (S.width - 1)).map (g c)) count).chunks = [] := by
      simp [trace, ch]
    obtain ⟨_, lane, _, fit, _⟩ := rows 0 (by simp [nrows, ch])
    simp only [rowArity, ch, Bool.false_eq_true, if_false] at fit
    have L : q.payload.length ≤ S.width - 1 := by split at fit <;> omega
    rw [Part.narrow, if_pos cp, show q.nrows = 1 by simp [nrows, ch], Finset.sum_range_one]
    simp only [Part.wide, Part.tuple, Compact.projRow, rowKey, rowArity, ch, Bool.false_eq_true, if_false,
      trace]
    rw [take_range_map _ L]

end CPart

namespace Sharded

variable {S : Sharded F}

theorem proj2_row {bound : Nat} (sep : S.Separated bound) {tag sub : F} {code : Nat} {lane : Bool}
    (he : ((tag, sub), code, lane) ∈ S.buses) {n m : Nat} (ar : S.system.arityAt (tag, sub) = some n)
    (le : n ≤ m) (g : Nat → F) :
    S.proj2 (((code : Nat) : F) :: (List.range m).map g) = tag :: sub :: (List.range n).map g := by
  simp only [proj2, unpack_code sep he]
  simp only [System.arityAt] at ar
  simp only [System.proj, System.arityOf, ar, Option.getD_some]
  rw [show 2 + n = n + 1 + 1 by omega, List.take_succ_cons, List.take_succ_cons,
    CPart.take_range_map _ le]

end Sharded

namespace Compact

variable {S : Sharded F} {T : Compact F}

theorem check_parts (ok : T.check S = true) :
    1 ≤ T.nFixed ∧ T.nFixed + 1 ≤ S.width ∧ ∀ q ∈ T.parts, q.check S = true := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at ok
  exact ⟨ok.1.1, ok.1.2, fun q hq => by
    rw [CPart.check_shape]; exact ok.2 _ (mem_distinct (List.mem_map_of_mem hq))⟩

theorem getD_counts {i : Nat} (hi : i < T.parts.length) : T.counts.getD i 0 = T.parts[i].nrows := by
  simp [counts, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

/-- The rows of part `i` of a table, as a ledger. -/
theorem rowLedger_part (ok : T.check S = true) (main : Nat → Nat → F) {i c : Nat}
    (hi : i < T.parts.length) (hc : c < T.parts[i].nrows) :
    ∃ code lane, S.buses.lookup (T.parts[i].rowKey c) = some (code, lane) ∧
      (T.circuit S.width).rowLedger (T.assign S.width S.buses main (blockOffset T.counts i + c)) =
        Finsupp.single (rowTuple (W := S.width) code lane fun j =>
          T.assign S.width S.buses main (blockOffset T.counts i + c) (T.cellVar S.width j))
          (-main (blockOffset T.counts i + c) 0) := by
  obtain ⟨code, lane, hl, _, _⟩ := CPart.check_row ((check_parts ok).2.2 _ (List.getElem_mem hi)) hc
  exact ⟨code, lane, hl, rowLedger_some S.buses main (at?_offset hi hc) hl⟩

theorem ledger_split (main : Nat → Nat → F) {H : Nat} (tall : T.rows ≤ H) :
    T.ledger S.width S.buses H main = ∑ i ∈ Finset.range T.parts.length,
      ∑ c ∈ Finset.range (T.counts.getD i 0),
        (T.circuit S.width).rowLedger (T.assign S.width S.buses main (blockOffset T.counts i + c)) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le tall
  rw [ledger, Finset.sum_range_add, Finset.sum_eq_zero (s := Finset.range d)
    (fun p _ => rowLedger_none S.buses main (at?_none (by omega))), add_zero, rows, sum_blocks]
  rw [show T.counts.length = T.parts.length by simp [counts]]

/-- **The projected ledger of a compact table is the narrow encoding of its parts.** -/
theorem proj_ledger {bound : Nat} (sep : S.Separated bound) (ok : T.check S = true)
    (main : Nat → Nat → F) {H : Nat} (tall : T.rows ≤ H) :
    Finsupp.mapDomain S.proj2 (T.ledger S.width S.buses H main) =
      ((T.traceParts S.width S.buses main).map Part.narrow).sum := by
  obtain ⟨one, fits, partsOk⟩ := check_parts ok
  have W4 := sep.width
  rw [ledger_split main tall, Finsupp.mapDomain_finsetSum, System.finset_sum_range_list, traceParts,
    List.map_map]
  conv_lhs => rw [show T.parts.length = T.parts.zipIdx.length by simp]
  refine sum_range_getElem T.parts.zipIdx _ _ (fun i hi => ?_)
  rw [List.length_zipIdx] at hi
  simp only [List.getElem_zipIdx, Function.comp_apply, zero_add]
  rw [getD_counts hi, Finsupp.mapDomain_finsetSum]
  simp only [cellsAt]
  rw [CPart.narrow_trace (g := fun c j => T.assign S.width S.buses main (blockOffset T.counts i + c)
    (T.cellVar S.width j)) (partsOk _ (List.getElem_mem hi)) W4 (fun ch c hc => ?_)]
  · apply Finset.sum_congr rfl
    intro c hc
    have hc := Finset.mem_range.mp hc
    obtain ⟨code, lane, hl, eq⟩ := rowLedger_part ok main hi hc
    obtain ⟨_, _, hl', fit, ar⟩ := CPart.check_row (partsOk _ (List.getElem_mem hi)) hc
    rw [hl] at hl'
    simp only [Option.some.injEq, Prod.mk.injEq] at hl'
    obtain ⟨rfl, rfl⟩ := hl'
    rw [eq, Finsupp.mapDomain_single, rowTuple]
    rw [Sharded.proj2_row sep (List.mem_of_lookup_eq_some hl) ar (by split <;> split at fit <;> omega)]
    rfl
  · rw [assign_fixed S.buses main (at?_offset hi (by rwa [CPart.nrows_chunked ch])) (by omega)]
    simp [CPart.rowCells, ch]

theorem shape_ledger (ok : T.check S = true) (main : Nat → Nat → F) {H : Nat} (t : List F)
    (h : T.ledger S.width S.buses H main t ≠ 0) : S.MsgShape t := by
  obtain ⟨_, fits, partsOk⟩ := check_parts ok
  simp only [ledger, Finsupp.finsetSum_apply] at h
  obtain ⟨p, _, hp⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  cases hat : T.at? p with
  | none => rw [rowLedger_none S.buses main hat] at hp; exact absurd rfl hp
  | some x =>
      obtain ⟨q, c⟩ := x
      have mem : q ∈ T.parts ∧ c < q.nrows := by
        simp only [at?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hat
        obtain ⟨⟨i, c'⟩, hloc, q', hq, e⟩ := hat
        simp only [Prod.mk.injEq] at e
        obtain ⟨rfl, rfl⟩ := e
        refine ⟨List.mem_of_getElem? hq, ?_⟩
        have := locateBlock_some _ hloc
        have hi := (List.getElem?_eq_some_iff.mp hq).1
        rw [getD_counts hi] at this
        rw [Option.some.inj ((List.getElem?_eq_getElem hi).symm.trans hq)] at this
        exact this
      obtain ⟨code, lane, hl, _, _⟩ := CPart.check_row (partsOk q mem.1) mem.2
      rw [rowLedger_some S.buses main hat hl, Finsupp.single_apply] at hp
      split at hp
      · rename_i e
        subst e
        refine ⟨(q.rowKey c, code, lane), List.mem_of_lookup_eq_some hl, rfl, ?_⟩
        simp only [rowTuple, List.length_cons, List.length_map, List.length_range]
        split <;> omega
      · exact absurd rfl hp

/-- A map table: every cell is fixed, and a chunked part's payload is its chunks. -/
def checkMap (S : Sharded F) (T : Compact F) : Bool :=
  T.nFixed + 1 == S.width && T.parts.all fun q =>
    !q.rom && (!q.chunked || (q.payload == ((List.range q.lens.length).map q.chunkVals).flatten &&
      (List.range q.lens.length).all fun c => (q.chunkVals c).length == q.lens.getD c 0))

/-- A ROM table: every part is a ROM entry whose payload is its address, the
fixed key, followed by `sub` words. -/
def checkRom (T : Compact F) : Bool :=
  T.parts.all fun q => q.rom && decide (1 ≤ q.payloadLen) && q.sub == ((q.payloadLen - 1 : Nat) : F) &&
    (q.chunked || q.payload.head? == some q.key)

theorem getD_range_map (l : List F) : (List.range l.length).map (fun j => l.getD j 0) = l := by
  apply List.ext_getElem (by simp)
  intro n h1 h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

theorem traceParts_getElem {S : Sharded F} {T : Compact F} (main : Nat → Nat → F) {i : Nat}
    (hi : i < T.parts.length) :
    (T.traceParts S.width S.buses main)[i]'(by simp [traceParts, hi]) =
      T.parts[i].trace (fun c => (List.range (S.width - 1)).map fun j =>
          T.assign S.width S.buses main (blockOffset T.counts i + c) (T.cellVar S.width j))
        (fun c => main (blockOffset T.counts i + c) 0) := by
  simp [traceParts, cellsAt]

/-- A map table's part read from the trace is its static part. -/
theorem _root_.Aiur.Tiling.Periodic.CPart.map_trace {S : Sharded F} {q : CPart F} (qok : q.check S = true)
    (W4 : 4 ≤ S.width) (notRom : q.rom = false)
    (shape : q.chunked = true → q.payload = ((List.range q.lens.length).map q.chunkVals).flatten ∧
      ∀ c < q.lens.length, (q.chunkVals c).length = q.lens.getD c 0)
    {g : Nat → Nat → F} (fixedCell : ∀ c < q.nrows, ∀ j < S.width - 1, g c j = (q.rowCells c).getD j 0)
    (count : Nat → F) :
    (q.trace (fun c => (List.range (S.width - 1)).map (g c)) count).tuple = q.tag :: q.sub :: q.payload := by
  by_cases ch : q.chunked = true
  · obtain ⟨flat, lens⟩ := shape ch
    simp only [Part.tuple, CPart.trace, ch, if_true, notRom, Bool.false_eq_true, if_false, List.nil_append,
      List.cons.injEq, true_and]
    conv_rhs => rw [flat]
    congr 1
    apply List.map_congr_left
    intro c hc
    have hc := List.mem_range.mp hc
    have hcn : c < q.nrows := by rwa [CPart.nrows_chunked ch]
    obtain ⟨_, lane, _, fit, _⟩ := CPart.check_row qok hcn
    simp only [CPart.rowArity, ch, if_true] at fit
    have L : q.lens.getD c 0 + 1 ≤ S.width - 1 := by split at fit <;> omega
    rw [CPart.take_drop_range _ L, ← lens c hc]
    conv_rhs => rw [← Compact.getD_range_map (q.chunkVals c)]
    apply List.map_congr_left
    intro j hj
    have hj := List.mem_range.mp hj
    rw [fixedCell c hcn (j + 1) (by rw [lens c hc] at hj; omega)]
    simp [CPart.rowCells, ch]
  · have ch : q.chunked = false := by simpa using ch
    have rest := qok
    simp only [CPart.check, Bool.and_eq_true, ch, Bool.false_eq_true, if_false, decide_eq_true_eq] at rest
    have n := rest.2.1
    simp only [Part.tuple, CPart.trace, ch, Bool.false_eq_true, if_false, List.cons.injEq, true_and]
    rw [CPart.take_range_map _ (by omega)]
    conv_rhs => rw [← Compact.getD_range_map q.payload]
    apply List.map_congr_left
    intro j hj
    rw [fixedCell 0 (by simp [CPart.nrows, ch]) j (by have := List.mem_range.mp hj; omega)]
    simp [CPart.rowCells, ch]

/-- A ROM table's part read from the trace is the ROM entry at its fixed address. -/
theorem _root_.Aiur.Tiling.Periodic.CPart.rom_trace {S : Sharded F} {q : CPart F} (qok : q.check S = true)
    (W4 : 4 ≤ S.width) (hrom : q.rom = true) (hsub : q.sub = ((q.payloadLen - 1 : Nat) : F))
    (shape : q.chunked = false → q.payload.head? = some q.key)
    {g : Nat → Nat → F} (keyCell : ∀ c < q.nrows, g c 0 = (q.rowCells c).getD 0 0) (count : Nat → F) :
    let x := q.trace (fun c => (List.range (S.width - 1)).map (g c)) count
    x.tuple = Bridge.encodeRom (x.key, Aiur.Circuit.Erasure.pack (x.payload.drop 1)) ∧
      x.key = q.key ∧ x.payload.length = q.payloadLen := by
  intro x
  obtain ⟨_, _, formed, _, _, _⟩ := CPart.trace_facts qok W4 (S := S) (g := g) (count := count)
  have tag2 : x.tag = 2 := by
    simp only [x]; unfold CPart.trace; split <;> simpa [CPart.rom] using hrom
  have xsub : x.sub = q.sub := by simp only [x]; unfold CPart.trace; split <;> rfl
  have xkey : x.key = q.key := by simp only [x]; unfold CPart.trace; split <;> rfl
  have plenCons : x.payload.length = q.payloadLen ∧ x.payload = x.key :: x.payload.drop 1 := by
    by_cases ch : q.chunked = true
    · have e : x.payload = q.key :: ((List.range q.lens.length).map
          fun c => (((List.range (S.width - 1)).map (g c)).drop 1).take (q.lens.getD c 0)).flatten := by
        simp [x, CPart.trace, ch, hrom]
      exact ⟨CPart.trace_length qok W4, by rw [e, xkey]; rfl⟩
    · have ch : q.chunked = false := by simpa using ch
      have rest := qok
      simp only [CPart.check, Bool.and_eq_true, ch, Bool.false_eq_true, if_false, decide_eq_true_eq] at rest
      have e : x.payload = ((List.range (S.width - 1)).map (g 0)).take q.payload.length := by
        simp [x, CPart.trace, ch]
      have pl : q.payload.length ≤ S.width - 1 := by omega
      rw [e, CPart.take_range_map _ pl]
      obtain ⟨k, ks, hks⟩ : ∃ k ks, q.payload = k :: ks := by
        cases h : q.payload with
        | nil => have := shape ch; simp [h] at this
        | cons k ks => exact ⟨k, ks, rfl⟩
      have hk : k = q.key := by simpa [hks] using shape ch
      refine ⟨by simp [CPart.payloadLen, ch], ?_⟩
      rw [hks, List.length_cons, List.range_succ_eq_map, List.map_cons, xkey,
        keyCell 0 (by simp [CPart.nrows, ch])]
      simp [CPart.rowCells, ch, hks, hk]
  refine ⟨?_, xkey, plenCons.1⟩
  simp only [Part.tuple, Bridge.encodeRom, Aiur.Circuit.Erasure.pack_words]
  rw [plenCons.2, tag2, xsub, hsub]
  simp only [List.drop_succ_cons, List.drop_zero, Bridge.ROM]
  rw [show (x.payload.drop 1).length = q.payloadLen - 1 by rw [List.length_drop, plenCons.1]]
  norm_num

end Compact

/-! ## Tables as external parts -/

section Tables

variable {S : Sharded F}

/-- The parts of all compact tables, read from their traces; table `t` reads `mainT t`. -/
def compactParts (S : Sharded F) (tables : List (Compact F)) (mainT : Nat → Nat → Nat → F) :
    List (Part F) :=
  tables.zipIdx.flatMap fun (a : Compact F × Nat) => a.1.traceParts S.width S.buses (mainT a.2)

/-- The parts of the ROM tables. -/
def romParts (S : Sharded F) (tables : List (Compact F)) (mainT : Nat → Nat → Nat → F) : List (Part F) :=
  tables.zipIdx.flatMap fun (a : Compact F × Nat) =>
    if a.1.checkRom then a.1.traceParts S.width S.buses (mainT a.2) else []

/-- The ROM the trace holds: every ROM part's address and words. -/
def compactRom (S : Sharded F) (tables : List (Compact F)) (mainT : Nat → Nat → Nat → F) : WidthROM F :=
  ⟨(romParts S tables mainT).map fun x => (x.key, x.payload.drop 1)⟩

/-- The lookups of all tables; table `t` has `HT t` rows. -/
noncomputable def compactLedger (S : Sharded F) (tables : List (Compact F)) (HT : Nat → Nat)
    (mainT : Nat → Nat → Nat → F) : Ledger F :=
  (tables.zipIdx.map fun (a : Compact F × Nat) => a.1.ledger S.width S.buses (HT a.2) (mainT a.2)).sum

def chunkSig (q : CPart F) : Option (F × F × F) := if q.chunked then some (q.tag, q.sub, q.key) else none

def partSig (x : Part F) : Option (F × F × F) := if x.chunks = [] then none else some (x.tag, x.sub, x.key)

/-- Lexicographic order on triples of naturals. -/
def Lex3 (a b : Nat × Nat × Nat) : Prop :=
  a.1 < b.1 ∨ (a.1 = b.1 ∧ (a.2.1 < b.2.1 ∨ (a.2.1 = b.2.1 ∧ a.2.2 < b.2.2)))

instance : DecidableRel Lex3 := fun a b => by unfold Lex3; infer_instance

/-- Adjacent elements are related. -/
def ascending {α : Type} (R : α → α → Prop) [DecidableRel R] : List α → Bool
  | a :: b :: l => decide (R a b) && ascending R (b :: l)
  | _ => true

theorem ascending_pairwise {α : Type} {R : α → α → Prop} [DecidableRel R]
    (trans : ∀ a b c, R a b → R b c → R a c) : ∀ {l : List α}, ascending R l = true → l.Pairwise R
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: l, h => by
      simp only [ascending, Bool.and_eq_true, decide_eq_true_eq] at h
      have rest := ascending_pairwise trans h.2
      refine List.Pairwise.cons ?_ rest
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact h.1
      · exact trans _ _ _ h.1 (List.rel_of_pairwise_cons rest hc)

/-- Distinctness of triples by sorting: `O(n log n)`. -/
def fastNodup (l : List (Nat × Nat × Nat)) : Bool :=
  ascending Lex3 (l.mergeSort fun a b => decide (¬ Lex3 b a))

theorem fastNodup_nodup {l : List (Nat × Nat × Nat)} (h : fastNodup l = true) : l.Nodup := by
  have pw := ascending_pairwise (R := Lex3) (fun a b c hab hbc => by unfold Lex3 at *; omega) h
  have nd : (l.mergeSort fun a b => decide (¬ Lex3 b a)).Nodup :=
    pw.imp fun {a b} hab e => by subst e; unfold Lex3 at hab; omega
  exact (List.mergeSort_perm l _).nodup_iff.mp nd

/-- The static checks of a list of compact tables: each table is accepted and
is a map or a ROM table; chunked receivers of one channel have distinct keys;
ROM addresses are distinct per word count. Distinctness is decided on the
images under any `ν : F → Nat` (the canonical representative, in practice). -/
def checkTables (S : Sharded F) (ν : F → Nat) (tables : List (Compact F)) : Bool :=
  tables.all (fun T => T.check S && (T.checkMap S || T.checkRom)) &&
    fastNodup (((tables.flatMap (·.parts)).filterMap chunkSig).map fun x => (ν x.1, ν x.2.1, ν x.2.2)) &&
    fastNodup ((tables.flatMap fun T => if T.checkRom then T.parts else []).map
      (fun q => (0, ν q.key, q.payloadLen)))

theorem CPart.trace_sig (q : CPart F) (cells : Nat → List F) (count : Nat → F) :
    partSig (q.trace cells count) = chunkSig q := by
  unfold partSig chunkSig CPart.trace
  by_cases ch : q.chunked = true
  · have : q.lens.length ≠ 0 := by simpa using CPart.lens_ne ch
    simp [ch, this]
  · simp [ch]

theorem traceParts_sig (T : Compact F) (main : Nat → Nat → F) :
    (T.traceParts S.width S.buses main).map partSig = T.parts.map chunkSig := by
  simp only [Compact.traceParts, List.map_map, Function.comp_def, CPart.trace_sig]
  conv_rhs => rw [← List.zipIdx_map_fst 0 T.parts, List.map_map]
  rfl

theorem compactParts_sig (tables : List (Compact F)) (mainT : Nat → Nat → Nat → F) :
    (compactParts S tables mainT).map partSig = (tables.flatMap (·.parts)).map chunkSig := by
  simp only [compactParts, List.map_flatMap, traceParts_sig]
  conv_rhs => rw [← List.zipIdx_map_fst 0 tables, List.flatMap_map]

theorem pairwise_compactParts {tables : List (Compact F)} {mainT : Nat → Nat → Nat → F}
    (nd : ((tables.flatMap (·.parts)).filterMap chunkSig).Nodup) :
    (compactParts S tables mainT).Pairwise Clash := by
  have e : (compactParts S tables mainT).filterMap partSig = (tables.flatMap (·.parts)).filterMap chunkSig := by
    have a : ∀ {α : Type} (l : List α) (f : α → Option (F × F × F)),
        l.filterMap f = (l.map f).filterMap id := fun l f => by rw [List.filterMap_map]; rfl
    rw [a _ partSig, a _ chunkSig, compactParts_sig]
  rw [← e] at nd
  have pw := List.pairwise_filterMap.mp nd
  refine pw.imp ?_
  intro x y h _ _ cx cy tg sb ky
  have hx : partSig x = some (x.tag, x.sub, x.key) := by simp [partSig, cx]
  have hy : partSig y = some (y.tag, y.sub, y.key) := by simp [partSig, cy]
  exact h _ hx _ hy (by rw [tg, sb, ky])

theorem mem_compactParts {tables : List (Compact F)} {mainT : Nat → Nat → Nat → F} {x : Part F}
    (h : x ∈ compactParts S tables mainT) :
    ∃ (T : Compact F) (t i : Nat) (hi : i < T.parts.length), tables[t]? = some T ∧
      x = (T.traceParts S.width S.buses (mainT t))[i]'(by simp [Compact.traceParts, hi]) := by
  simp only [compactParts, List.mem_flatMap] at h
  obtain ⟨⟨T, t⟩, ht, hx⟩ := h
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hi' : i < T.parts.length := by simpa [Compact.traceParts] using hi
  exact ⟨T, t, i, hi', List.mk_mem_zipIdx_iff_getElem?.mp ht, rfl⟩

theorem length_compactParts (tables : List (Compact F)) (mainT : Nat → Nat → Nat → F) :
    (compactParts S tables mainT).length = (tables.map (·.parts.length)).sum := by
  simp only [compactParts, List.length_flatMap, Compact.traceParts, List.length_map, List.length_zipIdx]
  conv_rhs => rw [← List.zipIdx_map_fst 0 tables, List.map_map]
  rfl

theorem compactLedger_proj {bound : Nat} (sep : S.Separated bound) {tables : List (Compact F)}
    (ok : ∀ T ∈ tables, T.check S = true) {HT : Nat → Nat}
    (tall : ∀ t T, tables[t]? = some T → T.rows ≤ HT t) (mainT : Nat → Nat → Nat → F) :
    Finsupp.mapDomain S.proj2 (compactLedger S tables HT mainT) =
      ((compactParts S tables mainT).map Part.narrow).sum := by
  rw [compactLedger, mapDomain_list_sum, compactParts, System.sum_map_flatMap]
  congr 1
  apply List.map_congr_left
  rintro ⟨T, t⟩ ht
  have hT := List.mk_mem_zipIdx_iff_getElem?.mp ht
  exact Compact.proj_ledger sep (ok T (List.mem_of_getElem? hT)) _ (tall t T hT)

theorem compactLedger_shape {tables : List (Compact F)} (ok : ∀ T ∈ tables, T.check S = true)
    {HT : Nat → Nat} (mainT : Nat → Nat → Nat → F) (t : List F)
    (h : compactLedger S tables HT mainT t ≠ 0) : S.MsgShape t := by
  obtain ⟨⟨T, k⟩, ht, hne⟩ := exists_of_sum_ne (l := tables.zipIdx) h
  exact Compact.shape_ledger (ok T (List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.mp ht))) _ t hne

theorem checkTables_parts {ν : F → Nat} {tables : List (Compact F)} (ok : checkTables S ν tables = true) :
    (∀ T ∈ tables, T.check S = true ∧ (T.checkMap S = true ∨ T.checkRom = true)) ∧
      ((tables.flatMap (·.parts)).filterMap chunkSig).Nodup ∧
      ((tables.flatMap fun T => if T.checkRom then T.parts else []).map
        (fun q => (q.key, q.payloadLen))).Nodup := by
  simp only [checkTables, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true] at ok
  refine ⟨ok.1.1, (fastNodup_nodup ok.1.2).of_map _, ?_⟩
  have := (fastNodup_nodup ok.2)
  rw [show (fun q : CPart F => (0, ν q.key, q.payloadLen)) =
    (fun x : F × Nat => (0, ν x.1, x.2)) ∘ (fun q => (q.key, q.payloadLen)) from rfl, ← List.map_map] at this
  exact this.of_map _

/-- Cell `j < nFixed` of a part read from the trace is its static value. -/
theorem Compact.trace_fixed {T : Compact F} (main : Nat → Nat → F) {i : Nat} (hi : i < T.parts.length)
    {c j : Nat} (hc : c < T.parts[i].nrows) (hj : j < T.nFixed) :
    T.assign S.width S.buses main (blockOffset T.counts i + c) (T.cellVar S.width j) =
      (T.parts[i].rowCells c).getD j 0 :=
  Compact.assign_fixed S.buses main (Compact.at?_offset hi hc) hj

theorem Compact.rom_part {T : Compact F} (ok : T.check S = true) (kr : T.checkRom = true)
    (W4 : 4 ≤ S.width) (main : Nat → Nat → F) {i : Nat} (hi : i < T.parts.length) :
    let x := (T.traceParts S.width S.buses main)[i]'(by simp [Compact.traceParts, hi])
    x.tuple = Bridge.encodeRom (x.key, Aiur.Circuit.Erasure.pack (x.payload.drop 1)) ∧
      x.key = T.parts[i].key ∧ x.payload.length = T.parts[i].payloadLen ∧ 1 ≤ T.parts[i].payloadLen := by
  intro x
  obtain ⟨one, _, partsOk⟩ := Compact.check_parts ok
  simp only [Compact.checkRom, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    Bool.or_eq_true] at kr
  obtain ⟨⟨⟨hrom, pos⟩, hsub⟩, shape⟩ := kr _ (List.getElem_mem hi)
  have hx : x = _ := Compact.traceParts_getElem (S := S) main hi
  rw [hx]
  have := CPart.rom_trace (partsOk _ (List.getElem_mem hi)) W4 hrom hsub
    (fun ch => by simpa [ch] using shape)
    (g := fun c j => T.assign S.width S.buses main (blockOffset T.counts i + c) (T.cellVar S.width j))
    (fun c hc => Compact.trace_fixed main hi hc (by omega))
    (fun c => main (blockOffset T.counts i + c) 0)
  exact ⟨this.1, this.2.1, this.2.2, pos⟩

theorem Compact.map_part {T : Compact F} (ok : T.check S = true) (km : T.checkMap S = true)
    (W4 : 4 ≤ S.width) (main : Nat → Nat → F) {i : Nat} (hi : i < T.parts.length) :
    ((T.traceParts S.width S.buses main)[i]'(by simp [Compact.traceParts, hi])).tuple =
      T.parts[i].tag :: T.parts[i].sub :: T.parts[i].payload := by
  obtain ⟨_, _, partsOk⟩ := Compact.check_parts ok
  simp only [Compact.checkMap, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.not_eq_true',
    Bool.or_eq_true] at km
  obtain ⟨nf, qm⟩ := km
  obtain ⟨notRom, shape⟩ := qm _ (List.getElem_mem hi)
  rw [Compact.traceParts_getElem (S := S) main hi]
  refine CPart.map_trace (partsOk _ (List.getElem_mem hi)) W4 notRom (fun ch => ?_)
    (fun c hc j hj => Compact.trace_fixed main hi hc (by omega)) _
  have := shape.resolve_left (by simp [ch])
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at this
  exact this

/-- The ROM the trace holds is valid: addresses are distinct per word count. -/
theorem compactRom_valid {ν : F → Nat} {tables : List (Compact F)} (ok : checkTables S ν tables = true) (W4 : 4 ≤ S.width)
    (mainT : Nat → Nat → Nat → F) : (compactRom S tables mainT).Valid := by
  obtain ⟨each, _, nd⟩ := checkTables_parts ok
  set RP := romParts S tables mainT with hRP
  have sig : RP.map (fun x => (x.key, x.payload.length)) =
      (tables.flatMap fun T => if T.checkRom then T.parts else []).map (fun q => (q.key, q.payloadLen)) := by
    simp only [RP, romParts, List.map_flatMap]
    conv_rhs => rw [← List.zipIdx_map_fst 0 tables, List.flatMap_map]
    apply List.flatMap_congr
    rintro ⟨T, t⟩ ht
    have hT : T ∈ tables := List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.mp ht)
    dsimp only
    split
    · rename_i kr
      apply List.ext_getElem (by simp [Compact.traceParts])
      intro i h1 h2
      have hi : i < T.parts.length := by simpa using h2
      have := Compact.rom_part (each T hT).1 kr W4 (mainT t) hi
      simp only [List.getElem_map]
      rw [this.2.1, this.2.2.1]
    · rfl
  intro a ha b hb addr len
  simp only [compactRom, List.mem_map] at ha hb
  obtain ⟨x, hx, rfl⟩ := ha
  obtain ⟨y, hy, rfl⟩ := hb
  have pos : ∀ x ∈ RP, 1 ≤ x.payload.length := by
    intro x hx
    simp only [RP, romParts, List.mem_flatMap] at hx
    obtain ⟨⟨T, t⟩, ht, hx⟩ := hx
    have hT : T ∈ tables := List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.mp ht)
    split at hx
    · rename_i kr
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      have hi' : i < T.parts.length := by simpa [Compact.traceParts] using hi
      have := Compact.rom_part (each T hT).1 kr W4 (mainT t) hi'
      rw [this.2.2.1]; exact this.2.2.2
    · simp at hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
  have pi : 1 ≤ RP[i].payload.length := pos _ (List.getElem_mem hi)
  have pj : 1 ≤ RP[j].payload.length := pos _ (List.getElem_mem hj)
  have len' : RP[i].payload.length - 1 = RP[j].payload.length - 1 := by simpa using len
  have lenEq : RP[i].payload.length = RP[j].payload.length := by omega
  have addr' : RP[i].key = RP[j].key := addr
  have nd' : (RP.map fun x => (x.key, x.payload.length)).Nodup := by rw [sig]; exact nd
  have same : (RP.map fun x => (x.key, x.payload.length))[i]'(by simpa using hi) =
      (RP.map fun x => (x.key, x.payload.length))[j]'(by simpa using hj) := by
    simp only [List.getElem_map]
    exact Prod.ext addr' lenEq
  have := (List.Nodup.getElem_inj_iff nd').mp same
  subst this
  rfl

end Tables


open Aiur.Circuit
open Aiur.Optimized
open Bridge
open Sharded

/-- **End to end, periodic shards and compact tables.** `narrow_heap_sound_stacked`
with the map claims and the ROM in compact tables (`Compact`): one circuit per
kind, one narrow row tuple per physical row. Map rows are fixed; ROM words are
witness values at fixed addresses, so the ROM is the one the trace holds
(`compactRom`): it is valid, and the result is represented in it. -/
theorem narrow_heap_sound_compact {source : Generic.Source F} {entries : List String}
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
    -- the compact tables
    {ν : F → Nat} {tables : List (Compact F)} (tablesOk : checkTables S ν tables = true)
    (mapsIn : ∀ T ∈ tables, T.checkMap S = true → ∀ q ∈ T.parts,
      q.tag :: q.sub :: q.payload ∈ (Depth.system cfg prepared.system).mapClaims.map (encode idOf))
    (capacity : capacityRowsU units S.system ≤ 2 ^ 39)
    {bound : Nat} (small : SmallCast F bound) (tags : 3 < bound)
    (codesBound : ∀ e ∈ S.buses, e.2.1 < bound) (labels : copyKey S.labelTotal < bound)
    (shadowBound : ∀ k < S.shards.length, ((S.layout k).shadow S.width).bound ≤ bound)
    (lookups : capacityLookupsU units S.system < bound) (ids : S.system.instances ≤ bound)
    (parts : (S.system.enumerate S.system.lookupCount).length + 1 +
      (tables.map (·.parts.length)).sum < bound)
    (characteristic : ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ cfg.bits → (n : F) ≠ 0)
    (shaped : Shaped.check (Depth.system cfg prepared.system) plan.singles idOf root bound = true)
    (context : (Depth.system cfg prepared.system).checkContext (Erasure.rawROM ⟨[]⟩) root = .ok ())
    (req : (Part.request S.width (encode idOf root)).checkRequest S.system (encode idOf root) = true)
    (req2 : S.checkRequest2 (Part.request S.width (encode idOf root)) = true)
    (enablesOk : ∀ c ∈ plan.singles, checkEnables bound c = true)
    -- the traces
    {H : Nat → Nat} {main : Nat → Nat → Nat → F} {HT : Nat → Nat} {mainT : Nat → Nat → Nat → F}
    (tall : ∀ k < S.shards.length, ((S.layout k).shadow S.width).places.length ≤ H k)
    (tallT : ∀ t T, tables[t]? = some T → T.rows ≤ HT t)
    (rows : ∀ k < S.shards.length, ∀ p < H k,
      Scalar.Circuit.Satisfies (S.circuit k).constraints (S.assign k (main k) p))
    (balanced : Finsupp.mapDomain trimZeros (S.ledger H main + compactLedger S tables HT mainT +
      S.padded2 (Part.request S.width (encode idOf root))) = 0) :
    (compactRom S tables mainT).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (compactRom S tables mainT)).decode
          specialized.program.enums) heap value result := by
  set rom : WidthROM F := compactRom S tables mainT
  obtain ⟨each, keysNd, _⟩ := checkTables_parts tablesOk
  obtain ⟨_, _, _, nodup, mods⟩ := check_parts ok
  have keyed := (check_parts ok).1
  have valid' := S.system.valid_of_checkKeyed keyed
  have sep : S.Separated bound :=
    ⟨small, by simpa [system] using valid'.width.1, fun e he => ⟨codesBound e he, mods e he⟩, nodup, labels⟩
  have W4 : 4 ≤ S.width := sep.width
  have valid : rom.Valid := compactRom_valid tablesOk W4 mainT
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
  set XT := compactParts S tables mainT
  have facts : ∀ x ∈ XT, x.recv = true ∧ S.checkRequest2 x = true ∧ x.Formed S.system.width ∧
      x.RowsIn S.system.roleOf S.system.arityAt ∧
      (x.chunks = [] → S.system.arityAt (x.tag, x.sub) = some x.payload.length) ∧
      (x.chunks ≠ [] → (x.tag, x.sub) ∉ S.system.receivers) := by
    intro x hx
    obtain ⟨T, t, i, hi, hT, rfl⟩ := mem_compactParts hx
    rw [Compact.traceParts_getElem (S := S) (mainT t) hi]
    exact CPart.trace_facts ((Compact.check_parts (each T (List.mem_of_getElem? hT)).1).2.2 _
      (List.getElem_mem hi)) W4
  have tablesCheck : ∀ T ∈ tables, T.check S = true := fun T hT => (each T hT).1
  set ext := S.padded2 request + compactLedger S tables HT mainT
  have balanced' : Finsupp.mapDomain trimZeros (S.ledger H main + ext) = 0 := by
    rw [← balanced, add_assoc]
    congr 2
    exact add_comm _ _
  have extShape : ∀ t, ext t ≠ 0 → S.MsgShape t := by
    intro t h
    simp only [ext, Finsupp.add_apply] at h
    by_cases h0 : S.padded2 request t = 0
    · rw [h0, zero_add] at h
      exact compactLedger_shape tablesCheck mainT t h
    · exact padded2_shape req2 t h0
  have extParts : Finsupp.mapDomain S.proj2 ext = ((request :: XT).map Part.narrow).sum := by
    simp only [ext, Finsupp.mapDomain_add, List.map_cons, List.sum_cons]
    rw [padded2_proj sep reqFacts.arity reqFacts.rowsIn req2, compactLedger_proj sep tablesCheck tallT]
  have pw : (request :: XT).Pairwise Clash := by
    refine List.pairwise_cons.mpr ⟨fun y _ r _ => ?_, pairwise_compactParts keysNd⟩
    rw [reqFacts.send] at r
    cases r
  obtain ⟨holds, wideBalanced⟩ := S.sound ok small codesBound labels shadowBound ids (request :: XT)
    (by simp only [List.length_cons, XT, length_compactParts]; omega) tall rows extShape extParts
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
      obtain ⟨T, t', i, hi, hT, rfl⟩ := mem_compactParts hx
      have mT := List.mem_of_getElem? hT
      rcases (each T mT).2 with km | kr
      · left
        rw [tx, Compact.map_part (each T mT).1 km W4 _ hi]
        obtain ⟨mc, hmc, e⟩ := List.mem_map.mp (mapsIn T mT km _ (List.getElem_mem hi))
        exact ⟨mc, hmc, e.symm⟩
      · right
        have rp := Compact.rom_part (each T mT).1 kr W4 (mainT t') hi
        refine ⟨_, ?_, by rw [tx]; exact rp.1⟩
        apply (Erasure.mem_rawROM).mpr
        simp only [rom, compactRom, List.mem_map]
        refine ⟨_, ?_, rfl⟩
        simp only [romParts, List.mem_flatMap]
        refine ⟨(T, t'), List.mk_mem_zipIdx_iff_getElem?.mpr hT, ?_⟩
        simp only [kr, if_true]
        exact List.getElem_mem _
    balanced := wideBalanced }
  obtain ⟨weighted, length, checked⟩ := W.checkMemo activated context'
  exact ⟨valid, prepared.depth_grouped_activated_heap_sound compiled certified plan activated entry valid
    signed rooted outside ((length.trans (length_instancesU _ _ _ _).le).trans capacity) characteristic checked
    arguments decoded⟩



/-! ## Building the tables

The tables of a layout are built here, from the encoded map claims and the
ROM capacities; the fixed matrix is `Compact.rowFixed` over the parts in
order, which is `Compact.fixedAt` (`fixedAt_offset`). -/

namespace CPart

/-- The part of an encoded map claim `tag :: sub :: payload` with key `key`,
split as the lowering splits a call: one row if the payload fits, else chunks
of `W − 2`. -/
def ofClaim (W : Nat) (key : F) : List F → CPart F
  | tag :: sub :: payload =>
      if payload.length + 1 ≤ W then ⟨tag, sub, key, payload, []⟩
      else ⟨tag, sub, key, payload, (Part.chunksOf (W - 2) payload.length payload).map List.length⟩
  | _ => ⟨0, 0, key, [], []⟩

/-- The ROM part of address `addr` with `width` words. -/
def ofRom (W width addr : Nat) : CPart F :=
  let payload : List F := (addr : F) :: List.replicate width 0
  if width + 2 ≤ W then ⟨2, (width : F), (addr : F), payload, []⟩
  else ⟨2, (width : F), (addr : F), payload,
    (Part.chunksOf (W - 2) width (List.replicate width (0 : F))).map List.length⟩

theorem ofClaim_tuple (W : Nat) (key : F) {t : List F} (h : 2 ≤ t.length) :
    (ofClaim W key t).tag :: (ofClaim W key t).sub :: (ofClaim W key t).payload = t := by
  match t, h with
  | tag :: sub :: payload, _ => by_cases hp : payload.length + 1 ≤ W <;> simp [ofClaim, hp]

end CPart

namespace Compact

/-- One map table for all map claims, keyed by `keyBase + row`. -/
def ofMaps (W : Nat) (claims : List (List F)) (keyBase : Nat) : Compact F :=
  ⟨W - 1, claims.zipIdx.map fun (t, k) => CPart.ofClaim W ((keyBase + k : Nat) : F) t⟩

/-- One ROM table for every word count: `(width, capacity)` gives addresses `0 … capacity − 1`. -/
def ofRoms (W : Nat) (roms : List (Nat × Nat)) : Compact F :=
  ⟨1, roms.flatMap fun (w, cap) => (List.range cap).map (CPart.ofRom W w)⟩

theorem ofMaps_mem {W : Nat} {claims : List (List F)} {keyBase : Nat}
    (long : ∀ t ∈ claims, 2 ≤ t.length) :
    ∀ q ∈ (ofMaps W claims keyBase).parts, q.tag :: q.sub :: q.payload ∈ claims := by
  intro q hq
  simp only [ofMaps, List.mem_map] at hq
  obtain ⟨⟨t, k⟩, ht, rfl⟩ := hq
  have mem := List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.mp ht)
  rw [CPart.ofClaim_tuple W _ (long t mem)]
  exact mem

/-- The fixed values of row `c` of part `q`. -/
def rowFixed (buses : Buses F) (q : CPart F) (c k : Nat) : F :=
  let e := (buses.lookup (q.rowKey c)).getD (0, false)
  match k with
  | 0 => if e.2 then 1 else 0
  | 1 => if e.2 then 0 else 1
  | 2 => ((e.1 : Nat) : F)
  | j + 3 => (q.rowCells c).getD j 0

/-- The fixed matrix, part by part and row by row. -/
def fixedRows (buses : Buses F) (T : Compact F) : List (List F) :=
  T.parts.flatMap fun q => (List.range q.nrows).map fun c =>
    (List.range (3 + T.nFixed)).map (rowFixed buses q c)

theorem fixedAt_offset (buses : Buses F) {T : Compact F} {i c : Nat} (hi : i < T.parts.length)
    (hc : c < T.parts[i].nrows) (k : Nat) :
    T.fixedAt buses (blockOffset T.counts i + c) k = rowFixed buses T.parts[i] c k := by
  simp only [fixedAt, at?_offset hi hc, rowFixed]

theorem fixedAt_pad (buses : Buses F) {T : Compact F} {r : Nat} (h : T.rows ≤ r) (k : Nat) :
    T.fixedAt buses r k = 0 := by
  simp [fixedAt, at?_none h]

end Compact

end Aiur.Tiling.Periodic
