import Aiur.Tiling.ComposeKeyed

/-!
# Fixed tables and ROM inside the tiled system

The fixed map tables and the ROM are tiled as ordinary circuits of the
system: `Bridge.tableCircuit t` receives the constant tuple `t` with the
multiplicity in main column 0. A table row of a map claim is a call receive,
keyed by its instance id when chunked; a ROM row is a ROM receive, keyed by
its constant address, which `System.checkKeyed` requires to be distinct per
width. The system's circuits are then the lowered single chips followed by
table rows, and the only external lookup is the entry request.

`System.checkMemo_of_tables` and `narrow_heap_sound_tables` are
`checkMemo_of_keyed` and `narrow_heap_sound_keyed` in that setting. The
external ledger is the entry request's narrow encoding, padded to the narrow
tuple width (`Part.padded`); the fixed-table support, the ledger's narrow
shape, its arity cut and its wide tuples are lemmas here, not hypotheses.
-/

namespace Aiur.Tiling

open Aiur.Circuit
open Aiur.Optimized

variable {F : Type} [Field F] [DecidableEq F]

namespace Bridge

/-- One fixed-table row: the receive of the constant tuple `t`, with its
multiplicity in main column 0. -/
def tableCircuit (t : List F) : Tiling.Circuit F where
  width := 1
  constraints := []
  lookups := [⟨.sub (.const 0) (.var 0), t.map .const⟩]

/-- The tuples of the map tables and the ROM. -/
def fixedRows (source : Circuit.System F) (rom : WireROM F) (idOf : String → Nat) : List (List F) :=
  source.mapClaims.map (encode idOf) ++ rom.entries.map encodeRom

theorem tableCircuit_rowLedger (t : List F) (w : Scalar.Circuit.Var → F) :
    (tableCircuit t).rowLedger w = Finsupp.single t (-(w 0)) := by
  simp [tableCircuit, Circuit.rowLedger, Lookup.entry, Lookup.tuple,
    Scalar.Circuit.ArithExpr.denote, List.map_map, Function.comp_def]

end Bridge

open Bridge

theorem ledger_sum_off {l : List (Ledger F)} {S : List F → Prop}
    (h : ∀ x ∈ l, ∀ t, ¬ S t → x t = 0) : ∀ t, ¬ S t → l.sum t = 0 := by
  intro t ht
  induction l with
  | nil => simp
  | cons x l ih =>
      simp only [List.sum_cons, Finsupp.add_apply]
      rw [h x (by simp) t ht, ih (fun y hy => h y (by simp [hy])), add_zero]

/-- The wide ledger of a system of lowered chips and table rows is the
chips' ledger plus a ledger supported on the table rows. -/
theorem System.wideLedger_tables {chips : List (Chip F)} {idOf : String → Nat} {fixed : List (List F)}
    (sys : System F) (circuits : sys.circuits = chips.map (Bridge.lower idOf) ++ fixed.map tableCircuit)
    (main : Nat → Nat → F) :
    ∃ tables : Ledger F, (∀ t, tables t ≠ 0 → t ∈ fixed) ∧
      sys.wideLedger (sys.wideRow main) =
        ((Bridge.instances chips sys main).map fun p => (Bridge.lower idOf p.1).rowLedger p.2).sum + tables := by
  let G : Nat → Ledger F := fun f => ((List.range (sys.cap f)).map fun i =>
      ((sys.circuits[f]?.map fun C => C.rowLedger (sys.wideRow main f i)).getD 0)).sum
  have len : sys.circuits.length = chips.length + fixed.length := by simp [circuits]
  refine ⟨((List.range fixed.length).map fun j => G (chips.length + j)).sum, ?_, ?_⟩
  · intro t ht
    by_contra nt
    apply ht
    apply ledger_sum_off (S := (· ∈ fixed)) _ t nt
    intro x hx u hu
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    have hj := List.mem_range.mp hj
    apply ledger_sum_off (S := (· ∈ fixed)) _ u hu
    intro y hy v hv
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hy
    have at_j : sys.circuits[chips.length + j]? = some (tableCircuit fixed[j]) := by
      rw [circuits, List.getElem?_append_right (by simp)]
      simp [hj]
    simp only [at_j, Option.map_some, Option.getD_some, tableCircuit_rowLedger, Finsupp.single_apply]
    rw [if_neg]
    rintro rfl
    exact hv (List.getElem_mem hj)
  · unfold System.wideLedger
    rw [len, List.range_add, List.map_append, List.sum_append]
    congr 1
    · simp only [Bridge.instances, System.sum_map_flatMap]
      apply congrArg List.sum
      apply List.map_congr_left
      intro f hf
      have hf := List.mem_range.mp hf
      have at_f : sys.circuits[f]? = some (Bridge.lower idOf chips[f]) := by
        rw [circuits, List.getElem?_append_left (by simpa using hf)]
        simp [hf]
      simp [at_f, List.getElem?_eq_getElem hf, List.map_map, Function.comp_def]
    · simp only [List.map_map, Function.comp_def, G]

namespace Part

/-- A tuple padded with zeros to the narrow tuple width `W + 1`. -/
def pad (W : Nat) (t : List F) : List F := t ++ List.replicate (W + 1 - t.length) 0

/-- A part's narrow encoding with tuples at the narrow tuple width, as the
narrow bus carries them. -/
noncomputable def padded (W : Nat) (p : Part F) : Ledger F := Finsupp.mapDomain (pad W) p.narrow

/-- A part used as the entry request: the send of `t` with weight 1, laid
out on the rows of `sys`. -/
structure Request (sys : System F) (t : List F) (p : Part F) : Prop where
  tuple : p.tuple = t
  weight : p.weight = 1
  send : p.recv = false
  formed : p.Formed sys.width
  fits : ∀ ch ∈ p.chunks, ch.length + 2 ≤ sys.width
  rowsIn : p.RowsIn sys.roleOf sys.arityAt
  arity : p.chunks = [] → sys.arityAt (p.tag, p.sub) = some p.payload.length

theorem narrow_support {p : Part F} {u : List F} (h : p.narrow u ≠ 0) :
    (p.chunks = [] ∧ u = p.tuple) ∨ (p.chunks ≠ [] ∧ ∃ c < p.chunks.length, u = p.chunkTuple c) := by
  by_cases cp : p.chunks = []
  · left
    refine ⟨cp, ?_⟩
    simp only [narrow, cp, if_true, wide, Finsupp.single_apply] at h
    by_contra ne
    exact h (if_neg (Ne.symm ne))
  · right
    rw [narrow_apply cp] at h
    obtain ⟨c, hc, ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    refine ⟨cp, c, Finset.mem_range.mp hc, ?_⟩
    by_contra e
    exact ne (if_neg (Ne.symm e))

theorem length_chunkTuple (p : Part F) (c : Nat) :
    (p.chunkTuple c).length = (p.chunks.getD c []).length + 3 := by
  simp [chunkTuple]

variable {sys : System F} {t : List F} {p : Part F}

theorem Request.fits_getD (req : p.Request sys t) {c : Nat} (hc : c < p.chunks.length) :
    (p.chunks.getD c []).length + 2 ≤ sys.width := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc, Option.getD_some]
  exact req.fits _ (List.getElem_mem hc)

/-- Every tuple of the padded encoding has the narrow tuple width and the
part's tag in front. -/
theorem Request.padded_shape (req : p.Request sys t) (u : List F) (h : p.padded sys.width u ≠ 0) :
    u.length = sys.width + 1 ∧ u.head? = some p.tag := by
  have mem : u ∈ (p.padded sys.width).support := Finsupp.mem_support_iff.mpr h
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support mem)
  have short : v.length ≤ sys.width + 1 ∧ v.head? = some p.tag := by
    rcases narrow_support (Finsupp.mem_support_iff.mp hv) with ⟨cp, rfl⟩ | ⟨_, c, hc, rfl⟩
    · refine ⟨?_, rfl⟩
      rcases req.formed with ⟨_, len⟩ | ⟨h2, _⟩
      · simp only [Part.tuple, List.length_cons]; omega
      · simp [cp] at h2
    · refine ⟨?_, rfl⟩
      rw [length_chunkTuple]
      have := req.fits_getD hc
      omega
  refine ⟨?_, ?_⟩
  · simp only [pad, List.length_append, List.length_replicate]; omega
  · have : v ≠ [] := by intro e; simp [e] at short
    obtain ⟨x, v', rfl⟩ := List.exists_cons_of_ne_nil this
    simpa [pad] using short.2

theorem proj_pad (sys : System F) (W : Nat) {tag s : F} {rest : List F}
    (ar : sys.arityAt (tag, s) = some rest.length) :
    sys.proj (pad W (tag :: s :: rest)) = tag :: s :: rest := by
  simp only [System.arityAt] at ar
  simp [System.proj, System.arityOf, pad, ar, List.take_append_of_le_length, Nat.add_comm]

/-- The padded encoding cut to arities is the narrow encoding. -/
theorem Request.padded_proj (req : p.Request sys t) :
    Finsupp.mapDomain sys.proj (p.padded sys.width) = p.narrow := by
  unfold padded
  rw [← Finsupp.mapDomain_comp]
  conv_rhs => rw [← Finsupp.mapDomain_id (v := p.narrow)]
  apply Finsupp.mapDomain_congr
  intro v hv
  rcases narrow_support (Finsupp.mem_support_iff.mp hv) with ⟨cp, rfl⟩ | ⟨cp, c, hc, rfl⟩
  · exact proj_pad sys _ (req.arity cp)
  · have ar := ((req.rowsIn.2 cp c hc).2)
    simp only [Function.comp_apply, id, chunkTuple]
    exact proj_pad sys _ (by simpa using ar)

/-- Consecutive pieces of `n` entries, with `fuel` pieces at most. -/
def chunksOf {α : Type} (n : Nat) : Nat → List α → List (List α)
  | 0, _ => []
  | _, [] => []
  | k + 1, l => l.take n :: chunksOf n k (l.drop n)

/-- The entry request `t = tag :: sub :: payload` as a send of weight 1, split
as `lower` splits a send: one row if the payload fits, otherwise chunks of
`W − 2` entries under key 0. -/
def request (W : Nat) (t : List F) : Part F :=
  match t with
  | tag :: sub :: payload =>
      if payload.length + 1 ≤ W then ⟨tag, sub, payload, 1, false, 0, [], []⟩
      else ⟨tag, sub, payload, 1, false, 0, chunksOf (W - 2) payload.length payload, []⟩
  | _ => ⟨0, 0, [], 1, false, 0, [], []⟩

/-- Decides `p.Request sys t`. -/
def checkRequest (sys : System F) (t : List F) (p : Part F) : Bool :=
  p.tuple == t && p.weight == 1 && !p.recv && p.cweights.isEmpty &&
    ((p.chunks.isEmpty && decide (p.payload.length + 1 ≤ sys.width)) ||
      (decide (2 ≤ p.chunks.length) && decide (sys.width ≤ p.payload.length) &&
        p.payload == (if p.rom then [p.key] else []) ++ p.chunks.flatten)) &&
    p.chunks.all (fun ch => decide (ch.length + 2 ≤ sys.width)) &&
    (if p.chunks.isEmpty then
      (match sys.roleOf (p.tag, p.sub) with
        | some r => r.2.isNone
        | none => true) &&
      sys.arityAt (p.tag, p.sub) == some p.payload.length
    else
      (List.range p.chunks.length).all fun c =>
        sys.roleOf (p.tag, chunkSub p.rom p.sub c) == some (p.sub, some (c, p.chunks.length, p.rom)) &&
          sys.arityAt (p.tag, chunkSub p.rom p.sub c) == some ((p.chunks.getD c []).length + 1))

theorem Request.of_check {sys : System F} {t : List F} {p : Part F}
    (h : p.checkRequest sys t = true) : p.Request sys t := by
  simp only [checkRequest, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', Bool.or_eq_true,
    decide_eq_true_eq, List.all_eq_true, List.isEmpty_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨tuple, weight⟩, send⟩, cw⟩, formed⟩, fits⟩, rowsOk⟩ := h
  refine ⟨tuple, weight, send, ?_, fits, ?_, ?_⟩
  · rcases formed with ⟨e, len⟩ | ⟨⟨two, wide⟩, flat⟩
    · exact Or.inl ⟨e, len⟩
    · exact Or.inr ⟨two, wide, flat, fun _ => Or.inr weight, Or.inl cw⟩
  · constructor
    · intro e r hr
      simp only [e, if_true, Bool.and_eq_true] at rowsOk
      have := rowsOk.1
      rw [hr] at this
      simpa using this
    · intro e c hc
      simp only [e, if_false, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at rowsOk
      exact rowsOk c hc
  · intro e
    simp only [e, if_true, Bool.and_eq_true, beq_iff_eq] at rowsOk
    exact rowsOk.2

end Part

/-- **Narrow traces with in-system tables are accepted by the memo checker.**
`System.checkMemo_of_keyed` for a system whose circuits are the lowered single
chips followed by rows of the map tables and the ROM: the external ledger is
the entry request alone. -/
theorem System.checkMemo_of_tables {source : Circuit.System F} {id : String → Except String Nat}
    (plan : Grouping.Plan source id) (activated : plan.WellFormedActivation)
    (idOf : String → Nat) {sys : System F} (ok : sys.checkKeyed = true)
    {rom : WireROM F} {fixed : List (List F)}
    (circuits : sys.circuits = plan.singles.map (Bridge.lower idOf) ++ fixed.map tableCircuit)
    (fixedIn : ∀ t ∈ fixed, t ∈ fixedRows source rom idOf)
    {bound : Nat} (small : SmallCast F bound) (sysBound : sys.bound ≤ bound) (tags : 3 < bound)
    (lookups : capacityLookups plan.singles sys < bound) (ids : sys.instances ≤ bound)
    (parts : (sys.enumerate sys.lookupCount).length + 1 < bound)
    {root : Message F} (shaped : Shaped source plan.singles idOf root bound)
    (romPacked : ∀ e ∈ rom.entries, e.2.type = .tuple (List.replicate e.2.words.length .field))
    (context : source.checkContext rom root = .ok ())
    {request : Part F} (req : request.Request sys (encode idOf root))
    {N : Nat} (tall : sys.places.length ≤ N) {main : Nat → Nat → F}
    (rows : ∀ p < N, Scalar.Circuit.Satisfies (narrowCircuit (F := F) sys.width).constraints
      (sys.assign main p))
    (balanced : Finsupp.mapDomain trimZeros
      (sys.narrowLedger N main + request.padded sys.width) = 0)
    (enablesOk : ∀ c ∈ plan.singles, checkEnables bound c = true) :
    ∃ weighted : List (WeightedRow F), weighted.length ≤ capacityRows plan.singles sys ∧
      plan.checkMemo rom root weighted = .ok () := by
  have ne3 : ∀ a : Nat, a < 3 → ((a : F) ≠ (COPY : F)) := fun a ha h => by
    have := small.inj (by omega) (by simp [COPY]; omega) h
    simp [COPY] at this; omega
  have valid := sys.valid_of_checkKeyed ok
  have tagCall : request.tag = (CALL : F) := by
    have := congrArg List.head? req.tuple
    simpa [Part.tuple, encode] using this
  have extShape : ∀ t, request.padded sys.width t ≠ 0 →
      t.length = sys.width + 1 ∧ t.head? ≠ some (COPY : F) := by
    intro t ht
    obtain ⟨len, head⟩ := req.padded_shape t ht
    refine ⟨len, ?_⟩
    rw [head, tagCall]
    intro h
    exact ne3 1 (by omega) (by simpa [CALL] using h)
  have exact := System.exact_of_trimmed valid (fun h => ne3 0 (by omega) (by simpa using h.symm))
    (by simpa using ne3 0 (by omega)) (fun t ht => Or.inl (extShape t ht)) balanced
  have extCopy : ∀ L v, request.padded sys.width [(COPY : F), L, v] = 0 := by
    intro L v
    by_contra ne
    have := (extShape _ ne).1
    simp at this
    have := valid.width.1
    omega
  obtain ⟨holds, wideBalanced⟩ := System.keyed_sound ok small sysBound ids [request]
    (by simpa using parts) tall rows extCopy exact (by simpa using req.padded_proj)
    (by simpa using ⟨req.formed, req.rowsIn⟩) (by simp [req.send])
    (fun j hj j' hj' _ _ _ _ _ _ _ => by simp at hj hj'; omega)
  obtain ⟨tables, support, split⟩ := System.wideLedger_tables sys circuits main
  have requestWide : ([request].map Part.wide).sum = Finsupp.single (encode idOf root) 1 := by
    simp [Part.wide, req.tuple, req.weight]
  rw [requestWide, split, add_right_comm] at wideBalanced
  have lengths : plan.singles.length ≤ sys.circuits.length := by simp [circuits]
  have W : Wide plan idOf bound rom root (Bridge.instances plan.singles sys main) tables := {
    chips := fun p hp => by
      obtain ⟨f, hf, i, _, rfl⟩ := mem_instances hp
      exact List.getElem_mem hf
    holds := fun p hp => by
      obtain ⟨f, hf, i, hi, rfl⟩ := mem_instances hp
      have h1 : sys.circuits[f]? = some (Bridge.lower idOf plan.singles[f]) := by
        rw [circuits, List.getElem?_append_left (by simpa using hf)]
        simp [hf]
      have e : sys.circuits[f]'(by omega) = Bridge.lower idOf plan.singles[f] :=
        Option.some.inj ((List.getElem?_eq_getElem _).symm.trans h1)
      have := holds f (by omega) i hi
      rw [e] at this
      exact this
    small := small
    enablesOk := enablesOk
    tags := by omega
    count := by rw [lookupCount_instances]; exact lookups
    shaped := shaped
    romPacked := romPacked
    tableSupport := fun t ht => by
      have := fixedIn t (support t ht)
      simp only [fixedRows, List.mem_append, List.mem_map] at this
      rcases this with ⟨mc, hmc, rfl⟩ | ⟨e, he, rfl⟩
      · exact Or.inl ⟨mc, hmc, rfl⟩
      · exact Or.inr ⟨e, he, rfl⟩
    balanced := wideBalanced }
  obtain ⟨weighted, length, checked⟩ := W.checkMemo activated context
  exact ⟨weighted, length.trans (length_instances _ _ _), checked⟩

/-- **End to end, tables in the system.** `narrow_heap_sound_keyed` for a
layout whose circuits are the lowered single chips followed by rows of the
map tables and the ROM. The only external lookup is the entry request
`Part.request`, padded to the narrow tuple width; `checkRequest` decides its
layout facts. -/
theorem narrow_heap_sound_tables {source : Generic.Source F} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id) (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries) {rom : WidthROM F} (valid : rom.Valid)
    {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)} {output : WireValue F}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Message F}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    -- the tiled layout
    (idOf : String → Nat) {sys : System F} (ok : sys.checkKeyed = true) {fixed : List (List F)}
    (circuits : sys.circuits = plan.singles.map (Bridge.lower idOf) ++ fixed.map tableCircuit)
    (fixedIn : ∀ t ∈ fixed, t ∈ fixedRows (Depth.system cfg prepared.system) (Erasure.rawROM rom) idOf)
    (capacity : capacityRows plan.singles sys ≤ 2 ^ 39)
    {bound : Nat} (small : SmallCast F bound) (sysBound : sys.bound ≤ bound) (tags : 3 < bound)
    (lookups : capacityLookups plan.singles sys < bound) (ids : sys.instances ≤ bound)
    (parts : (sys.enumerate sys.lookupCount).length + 1 < bound)
    (characteristic : ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ cfg.bits → (n : F) ≠ 0)
    (shaped : Shaped.check (Depth.system cfg prepared.system) plan.singles idOf root bound = true)
    (context : (Depth.system cfg prepared.system).checkContext (Erasure.rawROM rom) root = .ok ())
    (req : (Part.request sys.width (encode idOf root)).checkRequest sys (encode idOf root) = true)
    -- the narrow trace
    {N : Nat} (tall : sys.places.length ≤ N) {main : Nat → Nat → F}
    (rows : ∀ p < N, Scalar.Circuit.Satisfies (narrowCircuit (F := F) sys.width).constraints
      (sys.assign main p))
    (balanced : Finsupp.mapDomain trimZeros
      (sys.narrowLedger N main + (Part.request sys.width (encode idOf root)).padded sys.width) = 0)
    (enablesOk : ∀ c ∈ plan.singles, checkEnables bound c = true) :
    ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
      Represents ((Erasure.typedROM compiled.system rom).decode specialized.program.enums)
        heap value result := by
  have romPacked : ∀ e ∈ (Erasure.rawROM rom).entries,
      e.2.type = .tuple (List.replicate e.2.words.length .field) := by
    intro e he
    simp only [Erasure.rawROM, List.mem_map] at he
    obtain ⟨_, _, rfl⟩ := he
    simp [Erasure.pack]
  obtain ⟨weighted, length, checked⟩ := System.checkMemo_of_tables plan activated idOf ok circuits
    fixedIn small sysBound tags lookups ids parts (Shaped.of_check shaped) romPacked context (Part.Request.of_check req) tall
    rows balanced enablesOk
  exact prepared.depth_grouped_activated_heap_sound compiled certified plan activated entry valid
    signed rooted outside (length.trans capacity) characteristic checked arguments decoded

end Aiur.Tiling
