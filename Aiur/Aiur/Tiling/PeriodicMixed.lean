import Aiur.Tiling.PeriodicCompact

/-!
# Mixed narrow and wide stages

Some chips of the plan are not tiled: each such *wide unit* is one circuit
beside the narrow shards and the compact tables, with the constraints of
`Bridge.lower idOf c` and its lookups emitted in the narrow message encoding
of the shards, so that all circuits share one ledger.

Columns of the unit of chip `c`, with `n = c.numVars` and `s` the number of
sends:

* main columns `0 … n + 1` are the columns of `lower idOf c` (`n` is the
  selector, `n + 1` the receive multiplicity); main column `n + 2 + j` is the
  key cell of send `j` (read only if the send is chunked);
* fixed column 0 (variable `n + 2 + s`) is the row id `keyBase + r`, the key
  of the receive's chunk rows.

Every wide lookup `push(m, [tag, sub, payload…])` of `lower` becomes, as in
`Part.narrow`:

* if the payload fits one row (`|payload| + 1 ≤ W`), one lookup
  `push(m, [code(tag, sub), payload…, 0…])`;
* otherwise, with `body` the payload (after the address for a ROM read) cut
  into chunks of `W − 2`, one lookup per chunk `c`:
  `push(m, [code(tag, chunkSub rom sub c), key, chunk_c…, 0…])`. The key is
  the row id for the receive, the send's key cell for a send, the address for
  a ROM read.

Tuples are padded with zeros to 4 entries on a lane bus and `W` otherwise.

`mixed_heap_sound` is `narrow_heap_sound_compact` with wide units: their
rows' parts join the external parts of `Sharded.sound`, and their rows join
the instances given to `Bridge.Wide.checkMemo`.
-/

namespace Aiur.Tiling.Periodic

open Aiur.Scalar.Circuit (ArithExpr Var Satisfies)

variable {F : Type} [Field F] [DecidableEq F]

/-- One wide lookup `push(mult, [tag, sub, payload…])` with the key its chunk
rows carry when it is chunked. -/
structure WLook (F : Type) where
  tag : F
  sub : F
  payload : List (ArithExpr F)
  mult : ArithExpr F
  recv : Bool
  key : ArithExpr F

namespace WLook

variable (l : WLook F) (W : Nat)

def rom : Bool := l.tag == 2

def chunked : Bool := !decide (l.payload.length + 1 ≤ W)

/-- The payload after a ROM read's address. -/
def body : List (ArithExpr F) := if l.rom then l.payload.drop 1 else l.payload

/-- The key of the chunk rows: a ROM read's address, else `key`. -/
def keyExpr : ArithExpr F := if l.rom then l.payload.headD (.const 0) else l.key

def chunkExprs : List (List (ArithExpr F)) :=
  if l.chunked W then Part.chunksOf (W - 2) l.body.length l.body else []

/-- The part the lookup carries on row `w`. -/
def part (w : Var → F) : Part F :=
  ⟨l.tag, l.sub, l.payload.map (·.denote w), l.mult.denote w, l.recv, l.keyExpr.denote w,
    (l.chunkExprs W).map (·.map (·.denote w)), []⟩

def padE (n : Nat) (es : List (ArithExpr F)) : List (ArithExpr F) :=
  es ++ List.replicate (n - es.length) (.const 0)

/-- `push(mult, [code(key), cells…, 0…])` at the bus's tuple length. -/
def busLookup (buses : Buses F) (W : Nat) (key : F × F) (mult : ArithExpr F)
    (cells : List (ArithExpr F)) : Lookup F :=
  let e := (buses.lookup key).getD (0, false)
  ⟨mult, .const ((e.1 : Nat) : F) :: padE ((if e.2 then 4 else W) - 1) cells⟩

/-- The narrow lookups of the wide lookup. -/
def narrowLookups (buses : Buses F) : List (Lookup F) :=
  if (l.chunkExprs W).isEmpty then [busLookup buses W (l.tag, l.sub) l.mult l.payload]
  else (List.range (l.chunkExprs W).length).map fun c =>
    busLookup buses W (l.tag, chunkSub l.rom l.sub c) l.mult (l.keyExpr :: (l.chunkExprs W).getD c [])

/-- The row keys of the part, with their payload lengths. -/
def rowKeysS : List ((F × F) × Nat) :=
  if (l.chunkExprs W).isEmpty then [((l.tag, l.sub), l.payload.length)]
  else (List.range (l.chunkExprs W).length).map fun c =>
    ((l.tag, chunkSub l.rom l.sub c), ((l.chunkExprs W).getD c []).length + 1)

/-- Every row key has a bus entry and fits its tuple; a chunked lookup has at
least two chunks, the system's chunk roles and arities, and if it is a
receive, a channel without an in-system receiver; an unchunked lookup has no
chunk role and the system's arity. -/
def check (S : Sharded F) : Bool :=
  S.checkRequest2 (l.part S.width fun _ => 0) &&
  (if l.chunked S.width then
    decide (2 ≤ (l.chunkExprs S.width).length) &&
      (List.range (l.chunkExprs S.width).length).all (fun c =>
        S.system.roleOf (l.tag, chunkSub l.rom l.sub c) ==
            some (l.sub, some (c, (l.chunkExprs S.width).length, l.rom)) &&
          S.system.arityAt (l.tag, chunkSub l.rom l.sub c) ==
            some (((l.chunkExprs S.width).getD c []).length + 1)) &&
      (!l.recv || !(S.system.receivers.contains (l.tag, l.sub)))
  else
    (match S.system.roleOf (l.tag, l.sub) with
      | some r => r.2.isNone
      | none => true) &&
      S.system.arityAt (l.tag, l.sub) == some l.payload.length)

variable {l W}

theorem getD_map_list {α β : Type} (L : List (List α)) (f : α → β) (c : Nat) :
    (L.map (·.map f)).getD c [] = (L.getD c []).map f := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases L[c]? <;> rfl

theorem part_chunks (w : Var → F) : (l.part W w).chunks = (l.chunkExprs W).map (·.map (·.denote w)) := rfl

theorem rowKeys_part (w : Var → F) : Sharded.rowKeys (l.part W w) = l.rowKeysS W := by
  unfold Sharded.rowKeys rowKeysS
  rw [part_chunks]
  by_cases h : l.chunkExprs W = []
  · simp [h, part]
  · have h' : (l.chunkExprs W).isEmpty = false := by simpa using h
    rw [if_neg (by simpa using h), h']
    simp only [Bool.false_eq_true, if_false, List.length_map]
    apply List.map_congr_left
    intro c _
    simp only [part, Part.rom, rom, getD_map_list, List.length_map]

theorem checkRequest2_part {S : Sharded F} (w w' : Var → F) :
    S.checkRequest2 (l.part W w) = S.checkRequest2 (l.part W w') := by
  unfold Sharded.checkRequest2
  rw [rowKeys_part, rowKeys_part]

theorem padE_denote (w : Var → F) (n : Nat) (es : List (ArithExpr F)) :
    (padE n es).map (·.denote w) = es.map (·.denote w) ++ List.replicate (n - (es.map (·.denote w)).length) 0 := by
  simp [padE, List.map_replicate, ArithExpr.denote]

theorem busLookup_entry {buses : Buses F} {key : F × F} {code : Nat} {lane : Bool}
    (hl : buses.lookup key = some (code, lane)) (mult : ArithExpr F) (cells : List (ArithExpr F))
    (w : Var → F) :
    (busLookup buses W key mult cells).entry w =
      Finsupp.single (((code : Nat) : F) :: (cells.map (·.denote w) ++
        List.replicate ((if lane then 4 else W) - 1 - (cells.map (·.denote w)).length) 0)) (mult.denote w) := by
  simp only [Lookup.entry, Lookup.tuple, busLookup, hl, Option.getD_some, List.map_cons, padE_denote]
  rfl

theorem bus_of_check {S : Sharded F} (ok : l.check S = true) (w : Var → F) {key : F × F} {n : Nat}
    (hk : (key, n) ∈ Sharded.rowKeys (l.part S.width w)) :
    ∃ code lane, S.buses.lookup key = some (code, lane) := by
  have req : S.checkRequest2 (l.part S.width w) = true := by
    simp only [check, Bool.and_eq_true] at ok
    rw [checkRequest2_part w (fun _ => 0)]; exact ok.1
  have := List.all_eq_true.mp req _ hk
  cases hl : S.buses.lookup key with
  | none => simp [hl] at this
  | some e => exact ⟨e.1, e.2, rfl⟩

/-- **The narrow lookups of a wide lookup carry its part's narrow encoding.** -/
theorem narrowLookups_ledger {S : Sharded F} (ok : l.check S = true) (w : Var → F) :
    ((l.narrowLookups S.width S.buses).map (·.entry w)).sum = S.padded2 (l.part S.width w) := by
  unfold Sharded.padded2 Part.narrow
  by_cases h : l.chunkExprs S.width = []
  · have hc : (l.part S.width w).chunks = [] := by rw [part_chunks, h]; rfl
    obtain ⟨code, lane, hl⟩ := bus_of_check ok w (key := (l.tag, l.sub)) (n := l.payload.length)
      (by rw [rowKeys_part]; simp [rowKeysS, h])
    rw [if_pos hc]
    simp only [narrowLookups, h, List.isEmpty_nil, if_true, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, busLookup_entry hl, Part.wide, Finsupp.mapDomain_single]
    congr 1
    simp [Part.tuple, part, Sharded.encode2, hl]
  · have hc : (l.part S.width w).chunks ≠ [] := by rw [part_chunks]; simpa using h
    have h' : (l.chunkExprs S.width).isEmpty = false := by simpa using h
    rw [if_neg hc, Finsupp.mapDomain_finsetSum, System.finset_sum_range_list]
    simp only [narrowLookups, h', Bool.false_eq_true, if_false, List.map_map]
    rw [show (l.part S.width w).chunks.length = (l.chunkExprs S.width).length by simp [part_chunks]]
    congr 1
    apply List.map_congr_left
    intro c hc'
    have hc' := List.mem_range.mp hc'
    obtain ⟨code, lane, hl⟩ := bus_of_check ok w (key := (l.tag, chunkSub l.rom l.sub c))
      (n := ((l.chunkExprs S.width).getD c []).length + 1)
      (by rw [rowKeys_part]; simp only [rowKeysS, h', Bool.false_eq_true, if_false, List.mem_map,
        List.mem_range]; exact ⟨c, hc', rfl⟩)
    simp only [Function.comp_apply, busLookup_entry hl, Finsupp.mapDomain_single]
    congr 1
    simp only [Part.chunkTuple, part_chunks, getD_map_list]
    have hl' : S.buses.lookup (l.tag, chunkSub (l.tag == 2) l.sub c) = some (code, lane) := hl
    simp [part, Part.rom, Sharded.encode2, hl']

omit [DecidableEq F] in
theorem flatten_chunksOf {α : Type} {n : Nat} (hn : 0 < n) :
    ∀ (k : Nat) (l : List α), l.length ≤ n * k → (Part.chunksOf n k l).flatten = l
  | 0, l, h => by
      have : l = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
      simp [this, Part.chunksOf]
  | k + 1, [], _ => by simp [Part.chunksOf]
  | k + 1, a :: l, h => by
      have h' : (List.drop n (a :: l)).length ≤ n * k := by
        simp only [List.length_drop, List.length_cons] at h ⊢; rw [Nat.mul_succ] at h; omega
      simp only [Part.chunksOf, List.flatten_cons]
      rw [flatten_chunksOf hn k _ h', List.take_append_drop]

/-- The facts `Sharded.sound` needs of the part a checked lookup carries. -/
theorem part_facts {S : Sharded F} (ok : l.check S = true) (W4 : 4 ≤ S.width) (w : Var → F)
    (bool : l.recv = false → l.mult.denote w = 0 ∨ l.mult.denote w = 1) :
    S.checkRequest2 (l.part S.width w) = true ∧ (l.part S.width w).Formed S.system.width ∧
      (l.part S.width w).RowsIn S.system.roleOf S.system.arityAt ∧
      ((l.part S.width w).chunks = [] →
        S.system.arityAt ((l.part S.width w).tag, (l.part S.width w).sub) =
          some (l.part S.width w).payload.length) ∧
      ((l.part S.width w).recv = true → (l.part S.width w).chunks ≠ [] →
        ((l.part S.width w).tag, (l.part S.width w).sub) ∉ S.system.receivers) := by
  have Wsys : S.system.width = S.width := rfl
  simp only [check, Bool.and_eq_true] at ok
  obtain ⟨req, rest⟩ := ok
  have req' : S.checkRequest2 (l.part S.width w) = true := by rw [checkRequest2_part w (fun _ => 0)]; exact req
  refine ⟨req', ?_⟩
  by_cases ch : l.chunked S.width = true
  · simp only [ch, if_true, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
      beq_iff_eq, Bool.or_eq_true, Bool.not_eq_true'] at rest
    obtain ⟨⟨two, roles⟩, nrecv⟩ := rest
    have ne : l.chunkExprs S.width ≠ [] := by
      intro e; rw [e] at two; simp at two
    have xne : (l.part S.width w).chunks ≠ [] := by rw [part_chunks]; simpa using ne
    have wide : S.width ≤ l.payload.length := by
      simp only [chunked, Bool.not_eq_true', decide_eq_false_iff_not] at ch; omega
    have ce : l.chunkExprs S.width = Part.chunksOf (S.width - 2) l.body.length l.body := by
      simp [chunkExprs, ch]
    have flat : (l.part S.width w).chunks.flatten = l.body.map (·.denote w) := by
      rw [part_chunks, ← List.map_flatten, ce, flatten_chunksOf (by omega) _ _ (by
        have := Nat.le_mul_of_pos_left l.body.length (show 0 < S.width - 2 by omega); omega)]
    refine ⟨Or.inr ⟨by simpa [part_chunks] using two, by rw [Wsys]; simpa [part] using wide, ?_,
        fun r => bool r, Or.inl rfl⟩, ⟨fun h => absurd h xne, fun _ c hc => ?_⟩,
      fun h => absurd h xne, fun r _ => ?_⟩
    · rw [flat]
      by_cases hr : l.rom = true
      · obtain ⟨a, t, e⟩ : ∃ a t, l.payload = a :: t := by
          cases hp : l.payload with
          | nil => rw [hp] at wide; simp at wide; omega
          | cons a t => exact ⟨a, t, rfl⟩
        have hr' : (l.part S.width w).rom = true := hr
        rw [hr', if_pos rfl]
        show l.payload.map (·.denote w) = [l.keyExpr.denote w] ++ l.body.map (·.denote w)
        simp only [keyExpr, body, hr, if_true, e, List.drop_one, List.tail_cons, List.headD_cons,
          List.map_cons, List.singleton_append]
      · have hr0 : l.rom = false := by simpa using hr
        have hr' : (l.part S.width w).rom = false := hr0
        rw [hr']
        show l.payload.map (·.denote w) = [] ++ l.body.map (·.denote w)
        simp only [body, hr0, Bool.false_eq_true, if_false, List.nil_append]
    · have hc' : c < (l.chunkExprs S.width).length := by simpa [part_chunks] using hc
      obtain ⟨a, b⟩ := roles c hc'
      refine ⟨?_, ?_⟩
      · simpa [part, part_chunks, Part.rom, rom] using a
      · simp only [part_chunks, getD_map_list, List.length_map]
        simpa [part, Part.rom, rom] using b
    · have h1 : l.recv = true := r
      have := nrecv.resolve_left (by rw [h1]; decide)
      intro h
      have h2 : S.system.receivers.contains (l.tag, l.sub) = true := List.contains_iff_mem.mpr h
      rw [h2] at this
      cases this
  · have ch : l.chunked S.width = false := by simpa using ch
    simp only [ch, Bool.false_eq_true, if_false, Bool.and_eq_true, beq_iff_eq] at rest
    obtain ⟨role, ar⟩ := rest
    have ce : l.chunkExprs S.width = [] := by simp [chunkExprs, ch]
    have xc : (l.part S.width w).chunks = [] := by rw [part_chunks, ce]; rfl
    have fit : l.payload.length + 1 ≤ S.width := by
      simpa [chunked] using ch
    refine ⟨Or.inl ⟨xc, by rw [Wsys]; simpa [part] using fit⟩, ⟨fun _ r hr => ?_, fun h => absurd xc h⟩,
      fun _ => by simpa [part] using ar, fun _ h => absurd xc h⟩
    have hr' : S.system.roleOf (l.tag, l.sub) = some r := hr
    rw [hr'] at role
    simpa using role

end WLook

/-! ## Wide units -/

section Units

open Aiur.Circuit (Chip Send MemoryLookup)
open Aiur.Optimized
open Bridge (CALL receiveLookup sendLookup memoryLookup Boolean)

namespace WLook

/-- The receive of `lower idOf c`, keyed by variable `idCol`. -/
def ofReceive (idOf : String → Nat) (c : Chip F) (idCol : Var) : WLook F :=
  ⟨(CALL : F), (idOf (Activation.compile c).name : F),
    ((Activation.compile c).inputs.flatMap WireValue.words).map .var ++ (Activation.compile c).output.words,
    .sub (.const 0) (.var (c.numVars + 1)), true, .var idCol⟩

/-- A send of `lower idOf c`, keyed by variable `keyCol`. -/
def ofSend (idOf : String → Nat) (s : Send F) (keyCol : Var) : WLook F :=
  ⟨(CALL : F), (idOf s.channel : F), s.args.flatMap WireValue.words ++ s.result.words.map .var, s.enable,
    false, .var keyCol⟩

/-- A memory lookup of `lower idOf c`, keyed by its address. -/
def ofMemory (m : MemoryLookup F) : WLook F :=
  ⟨(Bridge.ROM : F), (m.value.words.length : F), m.address :: m.value.words, m.enable, false, m.address⟩

theorem ofReceive_wide (idOf : String → Nat) (c : Chip F) (idCol : Var) (W : Nat) (w : Var → F) :
    ((ofReceive idOf c idCol).part W w).wide = (receiveLookup idOf (Activation.compile c) (c.numVars + 1)).entry w := by
  simp [Part.wide, Part.tuple, part, ofReceive, Lookup.entry, Lookup.tuple, receiveLookup, ArithExpr.denote]

theorem ofSend_wide (idOf : String → Nat) (s : Send F) (keyCol : Var) (W : Nat) (w : Var → F) :
    ((ofSend idOf s keyCol).part W w).wide = (sendLookup idOf s).entry w := by
  simp [Part.wide, Part.tuple, part, ofSend, Lookup.entry, Lookup.tuple, sendLookup, ArithExpr.denote]

theorem ofMemory_wide (m : MemoryLookup F) (W : Nat) (w : Var → F) :
    ((ofMemory m).part W w).wide = (memoryLookup m).entry w := by
  simp [Part.wide, Part.tuple, part, ofMemory, Lookup.entry, Lookup.tuple, memoryLookup, ArithExpr.denote]

end WLook

/-- A chip of the plan laid out wide, beside the shards: `rows` rows whose
receive keys are `keyBase + r`. -/
structure WideUnit (F : Type) where
  chip : Chip F
  keyBase : Nat
  rows : Nat

namespace WideUnit

variable (idOf : String → Nat) (u : WideUnit F)

def sends : List (Send F) := (Activation.compile u.chip).sends

def mainWidth : Nat := u.chip.numVars + 2 + u.sends.length

/-- The row id: fixed column 0. -/
def idCol : Var := u.mainWidth

def keyCol (j : Nat) : Var := u.chip.numVars + 2 + j

def looks : List (WLook F) :=
  WLook.ofReceive idOf u.chip u.idCol ::
    ((u.sends.zipIdx.map fun a => WLook.ofSend idOf a.1 (u.keyCol a.2)) ++
      (Activation.compile u.chip).memory.map WLook.ofMemory)

def circuit (buses : Buses F) (W : Nat) : Tiling.Circuit F where
  width := u.mainWidth
  fixedWidth := 1
  constraints := (Bridge.lower idOf u.chip).constraints
  lookups := (u.looks idOf).flatMap (·.narrowLookups W buses)

/-- Row `r`: main columns from `main r`, fixed column 0 is `keyBase + r`. -/
def assign (main : Nat → Nat → F) (r : Nat) (v : Var) : F :=
  if v < u.mainWidth then main r v else if v = u.mainWidth then ((u.keyBase + r : Nat) : F) else 0

noncomputable def ledger (buses : Buses F) (W : Nat) (main : Nat → Nat → F) : Ledger F :=
  ∑ r ∈ Finset.range u.rows, (u.circuit idOf buses W).rowLedger (u.assign main r)

def check (S : Sharded F) : Bool := (u.looks idOf).all (·.check S)

variable {idOf u}

theorem wide_looks (W : Nat) (w : Var → F) :
    ((u.looks idOf).map fun l => (l.part W w).wide).sum = (Bridge.lower idOf u.chip).rowLedger w := by
  simp only [looks, Bridge.lower, Tiling.Circuit.rowLedger, List.map_cons, List.map_append, List.map_map,
    List.sum_cons, List.sum_append, Function.comp_def, WLook.ofReceive_wide, WLook.ofSend_wide,
    WLook.ofMemory_wide]
  congr 2
  conv_rhs => rw [← List.zipIdx_map_fst 0 (Activation.compile u.chip).sends, List.map_map]
  rfl

theorem rowLedger_circuit {S : Sharded F} (ok : u.check idOf S = true) (w : Var → F) :
    (u.circuit idOf S.buses S.width).rowLedger w = ((u.looks idOf).map fun l => S.padded2 (l.part S.width w)).sum := by
  simp only [Tiling.Circuit.rowLedger, circuit, System.sum_map_flatMap]
  congr 1
  apply List.map_congr_left
  intro l hl
  exact WLook.narrowLookups_ledger (List.all_eq_true.mp ok l hl) w

theorem looks_bool {w : Var → F} (b : Boolean u.chip w) {l : WLook F} (hl : l ∈ u.looks idOf) :
    l.recv = false → l.mult.denote w = 0 ∨ l.mult.denote w = 1 := by
  intro r
  simp only [looks, List.mem_cons, List.mem_append, List.mem_map] at hl
  rcases hl with rfl | ⟨a, ha, rfl⟩ | ⟨m, hm, rfl⟩
  · simp [WLook.ofReceive] at r
  · exact b.1 a.1 (List.mem_zipIdx_iff_getElem?.mp ha |> fun h => List.mem_of_getElem? h)
  · exact b.2 m hm

theorem length_looks : (u.looks idOf).length = 1 + u.chip.sends.length + u.chip.memory.length := by
  simp [looks, sends, Activation.compile]; omega

end WideUnit

/-! ## The wide units of a stage -/

variable (S : Sharded F) (idOf : String → Nat)

/-- The lookups of all wide units; unit `t` reads `mainW t`. -/
noncomputable def mixedLedger (units : List (WideUnit F)) (mainW : Nat → Nat → Nat → F) : Ledger F :=
  (units.zipIdx.map fun a => a.1.ledger idOf S.buses S.width (mainW a.2)).sum

/-- The parts the rows of the wide units carry. -/
def mixedParts (units : List (WideUnit F)) (mainW : Nat → Nat → Nat → F) : List (Part F) :=
  units.zipIdx.flatMap fun a => (List.range a.1.rows).flatMap fun r =>
    (a.1.looks idOf).map (·.part S.width (a.1.assign (mainW a.2) r))

/-- The rows of the wide units as chip rows. -/
def mixedInsts (units : List (WideUnit F)) (mainW : Nat → Nat → Nat → F) : List (Chip F × (Var → F)) :=
  units.zipIdx.flatMap fun a => (List.range a.1.rows).map fun r => (a.1.chip, a.1.assign (mainW a.2) r)

/-- Channel and key of a chunked receiver. -/
def recvSig (x : Part F) : Option (F × F × F) :=
  if x.recv && !x.chunks.isEmpty then some (x.tag, x.sub, x.key) else none

/-- Channel and key of every chunked receive of the wide units' rows. -/
def mixedSigs (W : Nat) (units : List (WideUnit F)) : List (F × F × F) :=
  units.flatMap fun u =>
    if ((WLook.ofReceive idOf u.chip u.idCol).chunkExprs W).isEmpty then []
    else (List.range u.rows).map fun r =>
      ((CALL : F), (idOf (Activation.compile u.chip).name : F), ((u.keyBase + r : Nat) : F))

/-- The static checks of the wide units beside compact tables: every lookup of
every unit passes `WLook.check`, and the chunked receivers of the tables and
the units have distinct channels and keys, decided on images under `ν`. -/
def checkMixed (ν : F → Nat) (tables : List (Compact F)) (units : List (WideUnit F)) : Bool :=
  units.all (·.check idOf S) &&
    fastNodup ((((tables.flatMap (·.parts)).filterMap chunkSig) ++ mixedSigs idOf S.width units).map
      fun x => (ν x.1, ν x.2.1, ν x.2.2))

/-- Lookups of the wide units' rows (sends and memory). -/
def mixedLookups (units : List (WideUnit F)) : Nat :=
  (units.map fun u => u.rows * (u.chip.sends.length + u.chip.memory.length)).sum

/-- Parts of the wide units' rows. -/
def mixedPartCount (units : List (WideUnit F)) : Nat :=
  (units.map fun u => u.rows * (1 + u.chip.sends.length + u.chip.memory.length)).sum

def mixedRows (units : List (WideUnit F)) : Nat := (units.map (·.rows)).sum

variable {S idOf}

theorem mixedLedger_eq {units : List (WideUnit F)} (ok : ∀ u ∈ units, u.check idOf S = true)
    (mainW : Nat → Nat → Nat → F) :
    mixedLedger S idOf units mainW = ((mixedParts S idOf units mainW).map S.padded2).sum := by
  unfold mixedLedger mixedParts
  rw [System.sum_map_flatMap]
  congr 1
  apply List.map_congr_left
  intro a ha
  have hu : a.1 ∈ units := by
    obtain ⟨u, t⟩ := a
    exact List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.mp ha)
  rw [WideUnit.ledger, System.finset_sum_range_list, System.sum_map_flatMap]
  congr 1
  apply List.map_congr_left
  intro r _
  rw [WideUnit.rowLedger_circuit (ok _ hu), List.map_map]
  rfl

theorem mem_mixedParts {units : List (WideUnit F)} {mainW : Nat → Nat → Nat → F} {x : Part F}
    (hx : x ∈ mixedParts S idOf units mainW) :
    ∃ (t : Nat) (u : WideUnit F), units[t]? = some u ∧ ∃ r < u.rows, ∃ l ∈ u.looks idOf, x = l.part S.width (u.assign (mainW t) r) := by
  simp only [mixedParts, List.mem_flatMap, List.mem_map, List.mem_range] at hx
  obtain ⟨⟨u, t⟩, ht, r, hr, l, hl, rfl⟩ := hx
  exact ⟨t, u, List.mk_mem_zipIdx_iff_getElem?.mp ht, r, hr, l, hl, rfl⟩

theorem mem_mixedInsts {units : List (WideUnit F)} {mainW : Nat → Nat → Nat → F} {p : Chip F × (Var → F)}
    (hp : p ∈ mixedInsts units mainW) :
    ∃ (t : Nat) (u : WideUnit F), units[t]? = some u ∧ ∃ r < u.rows, p = (u.chip, u.assign (mainW t) r) := by
  simp only [mixedInsts, List.mem_flatMap, List.mem_map, List.mem_range] at hp
  obtain ⟨⟨u, t⟩, ht, r, hr, rfl⟩ := hp
  exact ⟨t, u, List.mk_mem_zipIdx_iff_getElem?.mp ht, r, hr, rfl⟩

theorem mixedParts_wide (units : List (WideUnit F)) (mainW : Nat → Nat → Nat → F) :
    ((mixedParts S idOf units mainW).map Part.wide).sum =
      ((mixedInsts units mainW).map fun p => (Bridge.lower idOf p.1).rowLedger p.2).sum := by
  unfold mixedParts mixedInsts
  rw [System.sum_map_flatMap, System.sum_map_flatMap]
  congr 1
  apply List.map_congr_left
  intro a _
  rw [System.sum_map_flatMap, List.map_map]
  congr 1
  apply List.map_congr_left
  intro r _
  rw [List.map_map]
  exact WideUnit.wide_looks _ _

theorem zipIdx_sum_fst {α : Type} (units : List α) (g : α → Nat) :
    (units.zipIdx.map fun a => g a.1).sum = (units.map g).sum := by
  conv_rhs => rw [← List.zipIdx_map_fst 0 units, List.map_map]
  rfl

theorem length_mixedParts (units : List (WideUnit F)) (mainW : Nat → Nat → Nat → F) :
    (mixedParts S idOf units mainW).length = mixedPartCount units := by
  simp only [mixedParts, mixedPartCount, List.length_flatMap, List.length_map, WideUnit.length_looks]
  rw [← zipIdx_sum_fst units (fun u => u.rows * (1 + u.chip.sends.length + u.chip.memory.length))]
  congr 1
  apply List.map_congr_left
  intro a _
  rw [Bridge.sum_const_length]
  simp

theorem length_mixedInsts (units : List (WideUnit F)) (mainW : Nat → Nat → Nat → F) :
    (mixedInsts units mainW).length = mixedRows units := by
  simp only [mixedInsts, mixedRows, List.length_flatMap, List.length_map, List.length_range]
  exact zipIdx_sum_fst units _

theorem lookups_mixedInsts (units : List (WideUnit F)) (mainW : Nat → Nat → Nat → F) :
    ((mixedInsts units mainW).map fun p => p.1.sends.length + p.1.memory.length).sum =
      mixedLookups units := by
  simp only [mixedInsts, mixedLookups, System.sum_map_flatMap, List.map_map, Function.comp_def]
  rw [← zipIdx_sum_fst units (fun u => u.rows * (u.chip.sends.length + u.chip.memory.length))]
  congr 1
  apply List.map_congr_left
  intro a _
  rw [Bridge.sum_const_length]
  simp

/-! ## Distinct chunked receivers -/

theorem pairwise_of_recvSig {X : List (Part F)} (nd : (X.filterMap recvSig).Nodup) : X.Pairwise Clash := by
  have pw := List.pairwise_filterMap.mp nd
  refine pw.imp ?_
  intro x y h rx ry cx cy tg sb ky
  have hx : recvSig x = some (x.tag, x.sub, x.key) := by simp [recvSig, rx, cx]
  have hy : recvSig y = some (y.tag, y.sub, y.key) := by simp [recvSig, ry, cy]
  exact h _ hx _ hy (by rw [tg, sb, ky])

theorem CPart.trace_recv (q : CPart F) (cells : Nat → List F) (count : Nat → F) :
    (q.trace cells count).recv = true := by
  unfold CPart.trace; split <;> rfl

theorem recvSig_of_recv {x : Part F} (h : x.recv = true) : recvSig x = partSig x := by
  unfold recvSig partSig
  by_cases c : x.chunks = [] <;> simp [h, c]

theorem compactParts_recvSig {tables : List (Compact F)} {mainT : Nat → Nat → Nat → F} :
    (compactParts S tables mainT).filterMap recvSig = (tables.flatMap (·.parts)).filterMap chunkSig := by
  have recv : ∀ x ∈ compactParts S tables mainT, recvSig x = partSig x := by
    intro x hx
    obtain ⟨T, t, i, hi, hT, rfl⟩ := mem_compactParts hx
    rw [Compact.traceParts_getElem (S := S) _ hi]
    exact recvSig_of_recv (CPart.trace_recv _ _ _)
  rw [List.filterMap_congr recv]
  have a : ∀ {α : Type} (l : List α) (f : α → Option (F × F × F)),
      l.filterMap f = (l.map f).filterMap id := fun l f => by rw [List.filterMap_map]; rfl
  rw [a _ partSig, a _ chunkSig, compactParts_sig]

theorem call_ne_two : ((CALL : Nat) : F) ≠ 2 := by
  intro h
  have h2 : (2 : F) = 1 + 1 := by norm_num
  simp only [CALL, Nat.cast_one] at h
  rw [h2] at h
  simp at h

theorem mixedParts_recvSig (units : List (WideUnit F)) (mainW : Nat → Nat → Nat → F) :
    (mixedParts S idOf units mainW).filterMap recvSig = mixedSigs idOf S.width units := by
  unfold mixedParts mixedSigs
  rw [List.filterMap_flatMap]
  conv_rhs => rw [← List.zipIdx_map_fst 0 units, List.flatMap_map]
  apply List.flatMap_congr
  rintro ⟨u, t⟩ _
  rw [List.filterMap_flatMap]
  have row : ∀ r, ((u.looks idOf).map (·.part S.width (u.assign (mainW t) r))).filterMap recvSig =
      if ((WLook.ofReceive idOf u.chip u.idCol).chunkExprs S.width).isEmpty then []
      else [((CALL : F), (idOf (Activation.compile u.chip).name : F), ((u.keyBase + r : Nat) : F))] := by
    intro r
    simp only [WideUnit.looks, List.map_cons, List.filterMap_cons]
    rw [List.filterMap_eq_nil_iff.mpr]
    · set R := WLook.ofReceive idOf u.chip u.idCol with hR
      have rom : R.rom = false := by
        simp only [hR, WLook.rom, WLook.ofReceive, beq_eq_false_iff_ne]; exact call_ne_two
      have key : (R.part S.width (u.assign (mainW t) r)).key = ((u.keyBase + r : Nat) : F) := by
        show R.keyExpr.denote _ = _
        simp only [WLook.keyExpr, rom, Bool.false_eq_true, if_false]
        simp [hR, WLook.ofReceive, ArithExpr.denote, WideUnit.assign, WideUnit.idCol]
      have hr : (R.part S.width (u.assign (mainW t) r)).recv = true := rfl
      by_cases h : (R.chunkExprs S.width).isEmpty = true
      · have hc : (R.part S.width (u.assign (mainW t) r)).chunks.isEmpty = true := by
          rw [WLook.part_chunks, List.isEmpty_iff.mp h]; rfl
        simp only [recvSig, hr, hc, h, Bool.not_true, Bool.and_false, Bool.false_eq_true, if_false,
          if_true, Option.toList]
      · have h' : R.chunkExprs S.width ≠ [] := by simpa using h
        have hc : (R.part S.width (u.assign (mainW t) r)).chunks.isEmpty = false := by
          rw [WLook.part_chunks]; simpa using h'
        simp only [recvSig, hr, hc, h, Bool.not_false, Bool.and_true, Bool.false_eq_true, if_false, if_true]
        rw [key]
        rfl
    · intro x hx
      simp only [List.mem_map, List.mem_append] at hx
      obtain ⟨l, hl, rfl⟩ := hx
      have : l.recv = false := by
        rcases hl with ⟨a, _, rfl⟩ | ⟨m, _, rfl⟩ <;> rfl
      simp [recvSig, WLook.part, this]
  simp only [row]
  split
  · simp
  · rw [List.map_eq_flatMap]

end Units

/-! ## End to end -/

open Aiur.Circuit
open Aiur.Optimized
open Bridge
open Sharded

/-- **End to end, a mixed stage.** `narrow_heap_sound_compact` with some chips
of the plan laid out as wide units (`WideUnit.circuit`) beside the shards and
the compact tables, on the same ledger: the units' lookups are emitted in the
shards' narrow encoding, so their rows' parts join the external parts of
`Sharded.sound`, and their rows join the narrow instances as chip rows of
`Bridge.Wide`. -/
theorem mixed_heap_sound {source : Generic.Source F} {entries : List String}
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
    {wide : List (Tiling.Circuit F)} {groups : List (List (List Nat))}
    (circuits : S.system.circuits = List.zipWith Tiling.Circuit.mergeBy wide groups)
    (wideEq : wide = units.map (unitCircuit idOf))
    (lenG : groups.length = wide.length)
    (merged : ∀ j (hw : j < wide.length) (hg : j < groups.length), wide[j].checkMerge groups[j] = true)
    -- the compact tables
    {ν : F → Nat} {tables : List (Compact F)} (tablesOk : checkTables S ν tables = true)
    (mapsIn : ∀ T ∈ tables, T.checkMap S = true → ∀ q ∈ T.parts,
      q.tag :: q.sub :: q.payload ∈ (Depth.system cfg prepared.system).mapClaims.map (encode idOf))
    -- the wide units
    {wideUnits : List (WideUnit F)} (wideIn : ∀ u ∈ wideUnits, u.chip ∈ plan.singles)
    (wideOk : checkMixed S idOf ν tables wideUnits = true)
    (capacity : capacityRowsU units S.system + mixedRows wideUnits ≤ 2 ^ 39)
    {bound : Nat} (small : SmallCast F bound) (tags : 3 < bound)
    (codesBound : ∀ e ∈ S.buses, e.2.1 < bound) (labels : copyKey S.labelTotal < bound)
    (shadowBound : ∀ k < S.shards.length, ((S.layout k).shadow S.width).bound ≤ bound)
    (lookups : capacityLookupsU units S.system + mixedLookups wideUnits < bound)
    (ids : S.system.instances ≤ bound)
    (parts : (S.system.enumerate S.system.lookupCount).length + 1 +
      (tables.map (·.parts.length)).sum + mixedPartCount wideUnits < bound)
    (characteristic : ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ cfg.bits → (n : F) ≠ 0)
    (shaped : Shaped.check (Depth.system cfg prepared.system) plan.singles idOf root bound = true)
    (context : (Depth.system cfg prepared.system).checkContext (Erasure.rawROM ⟨[]⟩) root = .ok ())
    (req : (Part.request S.width (encode idOf root)).checkRequest S.system (encode idOf root) = true)
    (req2 : S.checkRequest2 (Part.request S.width (encode idOf root)) = true)
    (enablesOk : ∀ c ∈ plan.singles, checkEnables bound c = true)
    -- the traces
    {H : Nat → Nat} {main : Nat → Nat → Nat → F} {HT : Nat → Nat} {mainT : Nat → Nat → Nat → F}
    {mainW : Nat → Nat → Nat → F}
    (tall : ∀ k < S.shards.length, ((S.layout k).shadow S.width).places.length ≤ H k)
    (tallT : ∀ t T, tables[t]? = some T → T.rows ≤ HT t)
    (rows : ∀ k < S.shards.length, ∀ p < H k,
      Scalar.Circuit.Satisfies (S.circuit k).constraints (S.assign k (main k) p))
    (rowsW : ∀ (t : Nat) (u : WideUnit F), wideUnits[t]? = some u → ∀ r < u.rows,
      Scalar.Circuit.Satisfies (u.circuit idOf S.buses S.width).constraints (u.assign (mainW t) r))
    (balanced : Finsupp.mapDomain trimZeros (S.ledger H main + compactLedger S tables HT mainT +
      mixedLedger S idOf wideUnits mainW + S.padded2 (Part.request S.width (encode idOf root))) = 0) :
    (compactRom S tables mainT).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (compactRom S tables mainT)).decode
          specialized.program.enums) heap value result := by
  set rom : WidthROM F := compactRom S tables mainT
  obtain ⟨each, _, _⟩ := checkTables_parts tablesOk
  simp only [checkMixed, Bool.and_eq_true, List.all_eq_true] at wideOk
  obtain ⟨unitsOk, sigsOk⟩ := wideOk
  obtain ⟨_, _, _, nodup, mods⟩ := Sharded.check_parts ok
  have keyed := (Sharded.check_parts ok).1
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
  set XW := mixedParts S idOf wideUnits mainW
  have facts : ∀ x ∈ XT, x.recv = true ∧ S.checkRequest2 x = true ∧ x.Formed S.system.width ∧
      x.RowsIn S.system.roleOf S.system.arityAt ∧
      (x.chunks = [] → S.system.arityAt (x.tag, x.sub) = some x.payload.length) ∧
      (x.chunks ≠ [] → (x.tag, x.sub) ∉ S.system.receivers) := by
    intro x hx
    obtain ⟨T, t, i, hi, hT, rfl⟩ := mem_compactParts hx
    rw [Compact.traceParts_getElem (S := S) (mainT t) hi]
    exact CPart.trace_facts ((Compact.check_parts (each T (List.mem_of_getElem? hT)).1).2.2 _
      (List.getElem_mem hi)) W4
  have holdsW : ∀ p ∈ mixedInsts wideUnits mainW, (Bridge.lower idOf p.1).Holds p.2 := by
    intro p hp
    obtain ⟨t, u, hu, r, hr, rfl⟩ := mem_mixedInsts hp
    exact rowsW t u hu r hr
  have factsW : ∀ x ∈ XW, S.checkRequest2 x = true ∧ x.Formed S.system.width ∧
      x.RowsIn S.system.roleOf S.system.arityAt ∧
      (x.chunks = [] → S.system.arityAt (x.tag, x.sub) = some x.payload.length) ∧
      (x.recv = true → x.chunks ≠ [] → (x.tag, x.sub) ∉ S.system.receivers) := by
    intro x hx
    obtain ⟨t, u, hu, r, hr, l, hl, rfl⟩ := mem_mixedParts hx
    have mu := List.mem_of_getElem? hu
    have b : Boolean u.chip (u.assign (mainW t) r) :=
      boolean_of_lower (idOf := idOf) small (enablesOk _ (wideIn u mu)) (rowsW t u hu r hr)
    exact WLook.part_facts (List.all_eq_true.mp (unitsOk u mu) l hl) W4 _ (WideUnit.looks_bool b hl)
  have tablesCheck : ∀ T ∈ tables, T.check S = true := fun T hT => (each T hT).1
  have mixedEq := mixedLedger_eq (S := S) (idOf := idOf) (units := wideUnits) unitsOk mainW
  set ext := S.padded2 request + compactLedger S tables HT mainT + mixedLedger S idOf wideUnits mainW
  have balanced' : Finsupp.mapDomain trimZeros (S.ledger H main + ext) = 0 := by
    rw [← balanced]
    congr 1
    simp only [ext]
    abel
  have extShape : ∀ t, ext t ≠ 0 → S.MsgShape t := by
    intro t h
    simp only [ext, Finsupp.add_apply] at h
    by_cases h2 : mixedLedger S idOf wideUnits mainW t = 0
    · rw [h2, add_zero] at h
      by_cases h0 : S.padded2 request t = 0
      · rw [h0, zero_add] at h
        exact compactLedger_shape tablesCheck mainT t h
      · exact padded2_shape req2 t h0
    · rw [mixedEq] at h2
      obtain ⟨x, hx, hne⟩ := exists_of_sum_ne (g := S.padded2) h2
      exact padded2_shape (factsW x hx).1 t hne
  have extParts : Finsupp.mapDomain S.proj2 ext = ((request :: (XT ++ XW)).map Part.narrow).sum := by
    simp only [ext, Finsupp.mapDomain_add, List.map_cons, List.sum_cons, List.map_append, List.sum_append]
    have hW : (XW.map fun x => Finsupp.mapDomain S.proj2 (S.padded2 x)).sum = (XW.map Part.narrow).sum :=
      congrArg List.sum (List.map_congr_left fun x hx =>
        padded2_proj sep (factsW x hx).2.2.2.1 (factsW x hx).2.2.1 (factsW x hx).1)
    rw [padded2_proj sep reqFacts.arity reqFacts.rowsIn req2, compactLedger_proj sep tablesCheck tallT,
      mixedEq, mapDomain_list_sum, hW, add_assoc]
  have pw : (request :: (XT ++ XW)).Pairwise Clash := by
    refine List.pairwise_cons.mpr ⟨fun y _ r _ => ?_, pairwise_of_recvSig ?_⟩
    · rw [reqFacts.send] at r
      cases r
    · rw [List.filterMap_append, compactParts_recvSig, mixedParts_recvSig]
      exact (fastNodup_nodup sigsOk).of_map _
  obtain ⟨holds, wideBalanced⟩ := S.sound ok small codesBound labels shadowBound ids (request :: (XT ++ XW))
    (by simp only [List.length_cons, List.length_append, XT, XW, length_compactParts, length_mixedParts]; omega)
    tall rows extShape extParts
    (by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨reqFacts.formed, reqFacts.rowsIn⟩
      rcases List.mem_append.mp hx with hx | hx
      · exact ⟨(facts x hx).2.2.1, (facts x hx).2.2.2.1⟩
      · exact ⟨(factsW x hx).2.1, (factsW x hx).2.2.1⟩)
    (by
      intro x hx hr hc
      rcases List.mem_cons.mp hx with rfl | hx
      · rw [reqFacts.send] at hr; cases hr
      rcases List.mem_append.mp hx with hx | hx
      · exact (facts x hx).2.2.2.2.2 hc
      · exact (factsW x hx).2.2.2.2 hr hc)
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
  simp only [List.map_cons, List.sum_cons, List.map_append, List.sum_append, requestWide, XW,
    mixedParts_wide] at wideBalanced
  set NI := instancesU idOf units S.system (S.mainV main)
  set WI := mixedInsts wideUnits mainW
  rw [show instancesU idOf units sys' (S.mainV main) = NI from rfl] at wideBalanced
  have W : Wide plan idOf bound (Erasure.rawROM rom) root (NI ++ WI) (XT.map Part.wide).sum := {
    chips := fun p hp => by
      rcases List.mem_append.mp hp with hp | hp
      · obtain ⟨f, hf, i, _, e, _⟩ := mem_instancesU hp
        rw [e]
        exact chipsIn _ (List.getElem_mem hf)
      · obtain ⟨t, u, hu, r, _, rfl⟩ := mem_mixedInsts hp
        exact wideIn u (List.mem_of_getElem? hu)
    holds := fun p hp => by
      rcases List.mem_append.mp hp with hp | hp
      · obtain ⟨f, hf, i, hi, e, hr⟩ := mem_instancesU hp
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
          unfold Tiling.Circuit.Holds at this ⊢
          rw [ec] at this
          exact this
        rw [e]
        exact unit_holds h' _ hr
      · exact holdsW p hp
    small := small
    enablesOk := enablesOk
    tags := by omega
    count := by
      have a : Bridge.lookupCount NI = capacityLookupsU units S.system :=
        lookupCount_instancesU idOf units S.system (S.mainV main)
      have b := lookups_mixedInsts wideUnits mainW
      simp only [Bridge.lookupCount, List.map_append, List.sum_append] at a ⊢
      rw [b]
      omega
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
    balanced := by
      rw [List.map_append, List.sum_append]
      rw [← wideBalanced]
      abel }
  obtain ⟨weighted, length, checked⟩ := W.checkMemo activated context'
  have lenI : (NI ++ WI).length ≤ 2 ^ 39 := by
    rw [List.length_append, length_instancesU, length_mixedInsts]; exact capacity
  exact ⟨valid, prepared.depth_grouped_activated_heap_sound compiled certified plan activated entry valid
    signed rooted outside (length.trans lenI) characteristic checked arguments decoded⟩

end Aiur.Tiling.Periodic
