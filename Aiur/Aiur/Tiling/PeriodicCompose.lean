import Aiur.Tiling.PeriodicSound
import Aiur.Tiling.Tables
import Aiur.Tiling.PeriodicMerge
import Aiur.Tiling.PeriodicUnits

/-!
# The sharded v2 layout under the end-to-end theorem

The entry request is the only external lookup. Its v2 encoding
(`Sharded.padded2`) replaces each row tuple's `(tag, sub)` by the channel's
code and pads it to the channel's tuple length (4 for a lane channel, `W`
otherwise); `checkRequest2` decides that every row key of the request has a
bus entry and fits. `narrow_heap_sound_v2` is `narrow_heap_sound_tables` for a
sharded layout whose logical system's circuits are units (lowered chips of the
plan, or checked unrollings of them; possibly repeated across shards) followed
by table rows. An unrolled instance stands for one chip row per body.
-/

namespace Aiur.Tiling.Periodic

open Aiur.Circuit
open Aiur.Optimized
open Bridge

variable {F : Type} [Field F] [DecidableEq F]

namespace Sharded

variable {S : Sharded F}

variable (S) in
/-- `[tag, sub, rest…] ↦ [code, rest…, 0…]`, at the channel's tuple length. -/
def encode2 (u : List F) : List F :=
  match u with
  | tag :: sub :: rest =>
      match S.buses.lookup (tag, sub) with
      | some (code, lane) => ((code : Nat) : F) :: rest ++
          List.replicate ((if lane then 4 else S.width) - 1 - rest.length) 0
      | none => u
  | _ => u

variable (S) in
/-- A part's narrow encoding on the v2 bus. -/
noncomputable def padded2 (p : Part F) : Ledger F := Finsupp.mapDomain S.encode2 p.narrow

/-- Row keys `(tag, sub_row)` of a part with their payload lengths. -/
def rowKeys (p : Part F) : List ((F × F) × Nat) :=
  if p.chunks = [] then [((p.tag, p.sub), p.payload.length)]
  else (List.range p.chunks.length).map fun c =>
    ((p.tag, chunkSub p.rom p.sub c), (p.chunks.getD c []).length + 1)

variable (S) in
/-- Every row key of the part has a bus entry, and its row fits the channel's tuple. -/
def checkRequest2 (p : Part F) : Bool :=
  (rowKeys p).all fun (key, n) =>
    match S.buses.lookup key with
    | some (_, lane) => n + 1 ≤ (if lane then 4 else S.width)
    | none => false

omit [DecidableEq F] in
theorem rowKey_of_support [DecidableEq F] {p : Part F} {u : List F} (h : p.narrow u ≠ 0) :
    ∃ tag s rest, u = tag :: s :: rest ∧ ((tag, s), rest.length) ∈ rowKeys p := by
  rcases Part.narrow_support h with ⟨cp, rfl⟩ | ⟨cp, c, hc, rfl⟩
  · exact ⟨p.tag, p.sub, p.payload, rfl, by simp [rowKeys, cp]⟩
  · refine ⟨p.tag, chunkSub p.rom p.sub c, p.key :: p.chunks.getD c [], rfl, ?_⟩
    simp only [rowKeys, cp, if_false, List.mem_map, List.mem_range]
    exact ⟨c, hc, by simp⟩

theorem padded2_shape {p : Part F} (req : S.checkRequest2 p = true) (u : List F)
    (h : S.padded2 p u ≠ 0) : S.MsgShape u := by
  have mem : u ∈ (S.padded2 p).support := Finsupp.mem_support_iff.mpr h
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support mem)
  obtain ⟨tag, s, rest, rfl, hkey⟩ := rowKey_of_support (Finsupp.mem_support_iff.mp hv)
  have ok := List.all_eq_true.mp req _ hkey
  cases hl : S.buses.lookup (tag, s) with
  | none => simp [hl] at ok
  | some e =>
      obtain ⟨code, lane⟩ := e
      simp only [hl, decide_eq_true_eq] at ok
      refine ⟨((tag, s), code, lane), List.mem_of_lookup_eq_some hl, ?_, ?_⟩
      · simp [encode2, hl]
      · simp only [encode2, hl, List.length_cons, List.length_append, List.length_replicate]
        cases lane <;> simp only [Bool.false_eq_true, if_false, if_true] at ok ⊢ <;> omega

theorem padded2_proj {bound : Nat} (sep : S.Separated bound) {p : Part F}
    (arityU : p.chunks = [] → S.system.arityAt (p.tag, p.sub) = some p.payload.length)
    (rowsIn : p.RowsIn S.system.roleOf S.system.arityAt) (req2 : S.checkRequest2 p = true) :
    Finsupp.mapDomain S.proj2 (S.padded2 p) = p.narrow := by
  unfold padded2
  rw [← Finsupp.mapDomain_comp]
  conv_rhs => rw [← Finsupp.mapDomain_id (v := p.narrow)]
  apply Finsupp.mapDomain_congr
  intro v hv
  have arity : ∀ tag s rest, v = tag :: s :: rest → S.system.arityAt (tag, s) = some rest.length := by
    intro tag s rest e
    subst e
    rcases Part.narrow_support (Finsupp.mem_support_iff.mp hv) with ⟨cp, e⟩ | ⟨cp, c, hc, e⟩
    · simp only [Part.tuple, List.cons.injEq] at e
      obtain ⟨rfl, rfl, rfl⟩ := e
      exact arityU cp
    · simp only [Part.chunkTuple, List.cons.injEq] at e
      obtain ⟨rfl, rfl, rfl⟩ := e
      simpa using (rowsIn.2 cp c hc).2
  obtain ⟨tag, s, rest, rfl, hkey⟩ := rowKey_of_support (Finsupp.mem_support_iff.mp hv)
  have ok := List.all_eq_true.mp req2 _ hkey
  cases hl : S.buses.lookup (tag, s) with
  | none => simp [hl] at ok
  | some e =>
      obtain ⟨code, lane⟩ := e
      have ar := arity tag s rest rfl
      simp only [System.arityAt] at ar
      simp only [Function.comp_apply, id, encode2, hl, proj2, List.cons_append,
        unpack_code sep (List.mem_of_lookup_eq_some hl)]
      simp [System.proj, System.arityOf, ar, List.take_append_of_le_length, Nat.add_comm]

end Sharded

open Sharded

/-- **End to end, periodic shards.** `narrow_heap_sound_tables` for a sharded
v2 layout: the logical system's circuits are lowered chips of the plan,
possibly repeated across shards, followed by table rows; the shard traces
satisfy their shard circuits with their layouts' fixed matrices and balance
under multi-stark's fingerprint against the v2 encoding of the entry request. -/
theorem narrow_heap_sound_v2 {source : Generic.Source F} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id) (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries) {rom : WidthROM F} (valid : rom.Valid)
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
    (unrolled : ∀ u ∈ units, unitOk idOf u = true) {fixed : List (List F)}
    {wide : List (Circuit F)} {groups : List (List (List Nat))}
    (circuits : S.system.circuits = List.zipWith Circuit.mergeBy wide groups)
    (wideEq : wide = units.map (unitCircuit idOf) ++ fixed.map tableCircuit)
    (lenG : groups.length = wide.length)
    (merged : ∀ j (hw : j < wide.length) (hg : j < groups.length), wide[j].checkMerge groups[j] = true)
    (fixedIn : ∀ t ∈ fixed, t ∈ fixedRows (Depth.system cfg prepared.system) (Erasure.rawROM rom) idOf)
    (capacity : capacityRowsU units S.system ≤ 2 ^ 39)
    {bound : Nat} (small : SmallCast F bound) (tags : 3 < bound)
    (codesBound : ∀ e ∈ S.buses, e.2.1 < bound) (labels : copyKey S.labelTotal < bound)
    (shadowBound : ∀ k < S.shards.length, ((S.layout k).shadow S.width).bound ≤ bound)
    (lookups : capacityLookupsU units S.system < bound) (ids : S.system.instances ≤ bound)
    (parts : (S.system.enumerate S.system.lookupCount).length + 1 < bound)
    (characteristic : ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ cfg.bits → (n : F) ≠ 0)
    (shaped : Shaped.check (Depth.system cfg prepared.system) plan.singles idOf root bound = true)
    (context : (Depth.system cfg prepared.system).checkContext (Erasure.rawROM rom) root = .ok ())
    (req : (Part.request S.width (encode idOf root)).checkRequest S.system (encode idOf root) = true)
    (req2 : S.checkRequest2 (Part.request S.width (encode idOf root)) = true)
    -- the shard traces
    {H : Nat → Nat} {main : Nat → Nat → Nat → F}
    (tall : ∀ k < S.shards.length, ((S.layout k).shadow S.width).places.length ≤ H k)
    (rows : ∀ k < S.shards.length, ∀ p < H k,
      Scalar.Circuit.Satisfies (S.circuit k).constraints (S.assign k (main k) p))
    (balanced : Finsupp.mapDomain trimZeros
      (S.ledger H main + S.padded2 (Part.request S.width (encode idOf root))) = 0)
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
  set request := Part.request S.width (encode idOf root)
  have reqFacts : request.Request S.system (encode idOf root) := Part.Request.of_check req
  obtain ⟨_, _, _, nodup, mods⟩ := check_parts ok
  have keyed := (check_parts ok).1
  have valid' := S.system.valid_of_checkKeyed keyed
  have sep : S.Separated bound :=
    ⟨small, by simpa [system] using valid'.width.1, fun e he => ⟨codesBound e he, mods e he⟩, nodup, labels⟩
  obtain ⟨holds, wideBalanced⟩ := S.sound ok small codesBound labels shadowBound ids [request]
    (by simpa using parts) tall rows (padded2_shape req2) (by simpa using padded2_proj sep reqFacts.arity reqFacts.rowsIn req2)
    (by simpa using ⟨reqFacts.formed, reqFacts.rowsIn⟩) (by simp [reqFacts.send])
    (fun j hj j' hj' _ _ _ _ _ _ _ => by simp at hj hj'; omega) balanced
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
  obtain ⟨tables, support, split⟩ := System.wideLedger_units sys' wideEq unrolled (S.mainV main)
  have requestWide : ([request].map Part.wide).sum = Finsupp.single (encode idOf root) 1 := by
    simp [Part.wide, reqFacts.tuple, reqFacts.weight]
  rw [requestWide, split, add_right_comm] at wideBalanced
  have W : Wide plan idOf bound (Erasure.rawROM rom) root
      (instancesU idOf units S.system (S.mainV main)) tables := {
    chips := fun p hp => by
      obtain ⟨f, hf, i, _, e, _⟩ := mem_instancesU hp
      rw [e]
      exact chipsIn _ (List.getElem_mem hf)
    holds := fun p hp => by
      obtain ⟨f, hf, i, hi, e, hr⟩ := mem_instancesU hp
      have hw : f < wide.length := by rw [wideEq]; simp; omega
      have lt : f < S.system.circuits.length := by rw [lenC]; exact hw
      have hw' : wide[f]? = some (unitCircuit idOf units[f]) := by
        rw [wideEq, List.getElem?_append_left (by simpa using hf)]
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
      have := fixedIn t (support t ht)
      simp only [fixedRows, List.mem_append, List.mem_map] at this
      rcases this with ⟨mc, hmc, rfl⟩ | ⟨e, he, rfl⟩
      · exact Or.inl ⟨mc, hmc, rfl⟩
      · exact Or.inr ⟨e, he, rfl⟩
    balanced := wideBalanced }
  obtain ⟨weighted, length, checked⟩ := W.checkMemo activated context
  exact prepared.depth_grouped_activated_heap_sound compiled certified plan activated entry valid
    signed rooted outside ((length.trans (length_instancesU _ _ _ _).le).trans capacity) characteristic checked
    arguments decoded

end Aiur.Tiling.Periodic
