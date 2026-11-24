import Aiur.Tiling.Compose
import Aiur.Tiling.KeyedLedger

/-!
# Keyed layouts under the end-to-end theorem

`System.checkMemo_of_keyed` and `narrow_heap_sound_keyed` are
`System.checkMemo_of_narrow` and `narrow_heap_sound` for layouts accepted by
`System.checkKeyed`, through `System.keyed_sound`.
-/

namespace Aiur.Tiling

open Aiur.Circuit
open Aiur.Optimized
open Bridge

variable {F : Type} [Field F] [DecidableEq F]

/-- `System.checkMemo_of_narrow` for layouts accepted by `checkKeyed`: the
external ledger is the narrow encoding of parts `X` whose wide tuples are the
entry request plus the fixed tables and ROM. -/
theorem System.checkMemo_of_keyed {source : Circuit.System F} {id : String → Except String Nat}
    (plan : Grouping.Plan source id) (activated : plan.WellFormedActivation)
    (idOf : String → Nat) {sys : System F} (ok : sys.checkKeyed = true)
    (circuits : sys.circuits = plan.singles.map (Bridge.lower idOf))
    {bound : Nat} (small : SmallCast F bound) (sysBound : sys.bound ≤ bound) (tags : 3 < bound)
    (lookups : capacityLookups plan.singles sys < bound) (ids : capacityRows plan.singles sys ≤ bound)
    (X : List (Part F)) (parts : (sys.enumerate sys.lookupCount).length + X.length < bound)
    {rom : WireROM F} {root : Message F} (shaped : Shaped source plan.singles idOf root bound)
    (romPacked : ∀ e ∈ rom.entries, e.2.type = .tuple (List.replicate e.2.words.length .field))
    (context : source.checkContext rom root = .ok ())
    {tables : Ledger F}
    (tableSupport : ∀ t, tables t ≠ 0 →
      (∃ mc ∈ source.mapClaims, t = encode idOf mc) ∨ ∃ e ∈ rom.entries, t = encodeRom e)
    {ext : Ledger F}
    (extShape : ∀ t, ext t ≠ 0 → t.length = sys.width + 1 ∧ t.head? ≠ some (COPY : F))
    (extParts : Finsupp.mapDomain sys.proj ext = (X.map Part.narrow).sum)
    (extFormed : ∀ x ∈ X, x.Formed sys.width ∧ x.RowsIn sys.roleOf sys.arityAt)
    (extRecv : ∀ x ∈ X, x.recv = true → x.chunks ≠ [] → (x.tag, x.sub) ∉ sys.receivers)
    (extUnique : ∀ j (hj : j < X.length) j' (hj' : j' < X.length), X[j].recv = true →
      X[j'].recv = true → X[j].chunks ≠ [] → X[j'].chunks ≠ [] → X[j].tag = X[j'].tag →
      X[j].sub = X[j'].sub → X[j].key = X[j'].key → j = j')
    (extWide : (X.map Part.wide).sum = Finsupp.single (encode idOf root) 1 + tables)
    {N : Nat} (tall : sys.places.length ≤ N) {main : Nat → Nat → F}
    (rows : ∀ p < N, Scalar.Circuit.Satisfies (narrowCircuit (F := F) sys.width).constraints
      (sys.assign main p))
    (balanced : Finsupp.mapDomain trimZeros (sys.narrowLedger N main + ext) = 0)
    (enablesOk : ∀ c ∈ plan.singles, checkEnables bound c = true) :
    ∃ weighted : List (WeightedRow F), weighted.length ≤ capacityRows plan.singles sys ∧
      plan.checkMemo rom root weighted = .ok () := by
  have small' : SmallCast F sys.bound := small.mono sysBound
  have ne3 : ∀ a : Nat, a < 3 → ((a : F) ≠ (COPY : F)) := fun a ha h => by
    have := small.inj (by omega) (by simp [COPY]; omega) h
    simp [COPY] at this; omega
  have valid := sys.valid_of_checkKeyed ok
  have exact := System.exact_of_trimmed valid (fun h => ne3 0 (by omega) (by simpa using h.symm))
    (by simpa using ne3 0 (by omega)) (fun t ht => Or.inl (extShape t ht)) balanced
  have extCopy : ∀ L v, ext [(COPY : F), L, v] = 0 := by
    intro L v
    by_contra ne
    have := (extShape _ ne).1
    simp at this
    have := valid.width.1
    omega
  have lengths : sys.circuits.length = plan.singles.length := by simp [circuits]
  have instCount : sys.instances = capacityRows plan.singles sys := by
    simp only [System.instances, capacityRows, ← valid.lengths.1, lengths]
  obtain ⟨holds, wideBalanced⟩ := System.keyed_sound ok small sysBound (instCount ▸ ids) X parts tall
    rows extCopy exact extParts extFormed extRecv extUnique
  rw [extWide, System.wideLedger_lowered sys circuits, ← add_assoc] at wideBalanced
  have W : Wide plan idOf bound rom root (Bridge.instances plan.singles sys main) tables := {
    chips := fun p hp => by
      obtain ⟨f, hf, i, _, rfl⟩ := mem_instances hp
      exact List.getElem_mem hf
    holds := fun p hp => by
      obtain ⟨f, hf, i, hi, rfl⟩ := mem_instances hp
      have := holds f (by omega) i hi
      simp only [circuits, List.getElem_map] at this
      exact this
    small := small
    enablesOk := enablesOk
    tags := by omega
    count := by rw [lookupCount_instances]; exact lookups
    shaped := shaped
    romPacked := romPacked
    tableSupport := tableSupport
    balanced := wideBalanced }
  obtain ⟨weighted, length, checked⟩ := W.checkMemo activated context
  exact ⟨weighted, length.trans (length_instances _ _ _), checked⟩

/-- **End to end, keyed layouts.** `narrow_heap_sound` for layouts accepted by
`checkKeyed`, chunked templates included. The external ledger is the narrow
encoding of explicit parts `X` (the entry request, the fixed tables and the
ROM) whose wide tuples are the entry request plus `tables`. -/
theorem narrow_heap_sound_keyed {source : Generic.Source F} {entries : List String}
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
    (idOf : String → Nat) {sys : System F} (ok : sys.checkKeyed = true)
    (circuits : sys.circuits = plan.singles.map (Bridge.lower idOf))
    (capacity : capacityRows plan.singles sys ≤ 2 ^ 39)
    {bound : Nat} (small : SmallCast F bound) (sysBound : sys.bound ≤ bound) (tags : 3 < bound)
    (lookups : capacityLookups plan.singles sys < bound) (ids : capacityRows plan.singles sys ≤ bound)
    (X : List (Part F)) (parts : (sys.enumerate sys.lookupCount).length + X.length < bound)
    (characteristic : ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ cfg.bits → (n : F) ≠ 0)
    (shaped : Shaped.check (Depth.system cfg prepared.system) plan.singles idOf root bound = true)
    (context : (Depth.system cfg prepared.system).checkContext (Erasure.rawROM rom) root = .ok ())
    {tables : Ledger F}
    (tableSupport : ∀ t, tables t ≠ 0 →
      (∃ mc ∈ (Depth.system cfg prepared.system).mapClaims, t = encode idOf mc) ∨
        ∃ e ∈ (Erasure.rawROM rom).entries, t = encodeRom e)
    {ext : Ledger F}
    (extShape : ∀ t, ext t ≠ 0 → t.length = sys.width + 1 ∧ t.head? ≠ some (COPY : F))
    (extParts : Finsupp.mapDomain sys.proj ext = (X.map Part.narrow).sum)
    (extFormed : ∀ x ∈ X, x.Formed sys.width ∧ x.RowsIn sys.roleOf sys.arityAt)
    (extRecv : ∀ x ∈ X, x.recv = true → x.chunks ≠ [] → (x.tag, x.sub) ∉ sys.receivers)
    (extUnique : ∀ j (hj : j < X.length) j' (hj' : j' < X.length), X[j].recv = true →
      X[j'].recv = true → X[j].chunks ≠ [] → X[j'].chunks ≠ [] → X[j].tag = X[j'].tag →
      X[j].sub = X[j'].sub → X[j].key = X[j'].key → j = j')
    (extWide : (X.map Part.wide).sum = Finsupp.single (encode idOf root) 1 + tables)
    -- the narrow trace
    {N : Nat} (tall : sys.places.length ≤ N) {main : Nat → Nat → F}
    (rows : ∀ p < N, Scalar.Circuit.Satisfies (narrowCircuit (F := F) sys.width).constraints
      (sys.assign main p))
    (balanced : Finsupp.mapDomain trimZeros (sys.narrowLedger N main + ext) = 0)
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
  obtain ⟨weighted, length, checked⟩ := System.checkMemo_of_keyed plan activated idOf ok circuits
    small sysBound tags lookups ids X parts (Shaped.of_check shaped) romPacked context tableSupport
    extShape extParts extFormed extRecv extUnique extWide tall rows balanced enablesOk
  exact prepared.depth_grouped_activated_heap_sound_certified compiled certified plan activated entry valid
    signed rooted outside (length.trans capacity) characteristic checked arguments decoded

end Aiur.Tiling
