import Aiur.Tiling.Bridge
import Aiur.Tiling.Trim
import Aiur.Optimized.Depth.Grouped

/-!
# The tiled layout under the end-to-end theorem

`System.checkMemo_of_narrow` runs a narrow trace of a tiled system whose
wide circuits are the lowered single chips of a grouping plan through
`System.sound` and `Bridge.Wide.checkMemo`: the reconstructed wide rows give
weighted rows that the plan's memo checker accepts.

`narrow_heap_sound` composes that with
`Physical.Prepared.depth_grouped_activated_heap_sound`, from an accepting
narrow trace to the source evaluation predicate.
-/

namespace Aiur.Tiling

open Aiur.Circuit
open Aiur.Optimized

variable {F : Type} [Field F] [DecidableEq F]

namespace Bridge

/-- The wide instances of a tiled system whose circuits lower `chips`. -/
def instances (chips : List (Chip F)) (sys : System F) (main : Nat → Nat → F) :
    List (Chip F × (Circuit.Var → F)) :=
  (List.range chips.length).flatMap fun f =>
    match chips[f]? with
    | some c => (List.range (sys.cap f)).map fun i => (c, sys.wideRow main f i)
    | none => []

/-- Lookups of all instances: independent of the trace. -/
def capacityLookups (chips : List (Chip F)) (sys : System F) : Nat :=
  ((List.range chips.length).map fun f =>
    match chips[f]? with
    | some c => sys.cap f * (c.sends.length + c.memory.length)
    | none => 0).sum + 1

def capacityRows (chips : List (Chip F)) (sys : System F) : Nat :=
  ((List.range chips.length).map sys.cap).sum

theorem lookupCount_instances (chips : List (Chip F)) (sys : System F) (main : Nat → Nat → F) :
    lookupCount (instances chips sys main) = capacityLookups chips sys := by
  simp only [lookupCount, capacityLookups, instances, System.sum_map_flatMap]
  congr 2
  apply List.map_congr_left
  intro f _
  cases chips[f]? with
  | none => simp
  | some c =>
    simp only [List.map_map, Function.comp_def]
    rw [List.map_const', List.sum_replicate, smul_eq_mul, List.length_range]

theorem length_instances (chips : List (Chip F)) (sys : System F) (main : Nat → Nat → F) :
    (instances chips sys main).length ≤ capacityRows chips sys := by
  simp only [instances, capacityRows, List.length_flatMap]
  apply nat_sum_map_le
  intro f _
  cases chips[f]? <;> simp

theorem mem_instances {chips : List (Chip F)} {sys : System F} {main : Nat → Nat → F}
    {p : Chip F × (Circuit.Var → F)} (hp : p ∈ instances chips sys main) :
    ∃ f, ∃ hf : f < chips.length, ∃ i < sys.cap f, p = (chips[f], sys.wideRow main f i) := by
  simp only [instances, List.mem_flatMap, List.mem_range] at hp
  obtain ⟨f, hf, hp⟩ := hp
  rw [List.getElem?_eq_getElem hf] at hp
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
  exact ⟨f, hf, i, List.mem_range.mp hi, rfl⟩

end Bridge

open Bridge

theorem System.wideLedger_lowered {chips : List (Chip F)} {idOf : String → Nat} (sys : System F)
    (circuits : sys.circuits = chips.map (Bridge.lower idOf)) (main : Nat → Nat → F) :
    sys.wideLedger (sys.wideRow main) =
      ((instances chips sys main).map fun p => (Bridge.lower idOf p.1).rowLedger p.2).sum := by
  simp only [System.wideLedger, instances, System.sum_map_flatMap, circuits, List.length_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro f _
  simp only [List.getElem?_map]
  cases chips[f]? with
  | none => simp
  | some c => simp [List.map_map, Function.comp_def]

/-- **Narrow traces are accepted by the memo checker.** A tiled system whose
wide circuits are the lowered single chips of a grouping plan, and a narrow
trace that satisfies it and balances under multi-stark's fingerprint against
an external ledger of narrow-width tuples (whose arity cut is the entry
request plus the fixed tables and ROM), yield weighted rows that `Grouping.Plan.checkMemo` accepts.
`enablesOk` certifies the boolean enables that LogUp's integer reading needs
(`Bridge.checkEnables`); on the reconstructed rows it follows from the
lowered chips' constraints. -/
theorem System.checkMemo_of_narrow {source : Circuit.System F} {id : String → Except String Nat}
    (plan : Grouping.Plan source id) (activated : plan.WellFormedActivation)
    (idOf : String → Nat) {sys : System F} (ok : sys.check = true)
    (circuits : sys.circuits = plan.singles.map (Bridge.lower idOf))
    {bound : Nat} (small : SmallCast F bound) (sysBound : sys.bound ≤ bound) (tags : 3 < bound)
    (lookups : capacityLookups plan.singles sys < bound)
    {rom : WireROM F} {root : Message F} (shaped : Shaped source plan.singles idOf root bound)
    (romPacked : ∀ e ∈ rom.entries, e.2.type = .tuple (List.replicate e.2.words.length .field))
    (context : source.checkContext rom root = .ok ())
    {tables : Ledger F}
    (tableSupport : ∀ t, tables t ≠ 0 →
      (∃ mc ∈ source.mapClaims, t = encode idOf mc) ∨ ∃ e ∈ rom.entries, t = encodeRom e)
    {ext : Ledger F}
    (extShape : ∀ t, ext t ≠ 0 → t.length = sys.width + 1 ∧ t.head? ≠ some (COPY : F))
    (extWide : Finsupp.mapDomain sys.proj ext = Finsupp.single (encode idOf root) 1 + tables)
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
  have valid := sys.valid_of_check ok
  have exact := System.exact_of_trimmed valid (fun h => ne3 0 (by omega) (by simpa using h.symm))
    (by simpa using ne3 0 (by omega)) (fun t ht => Or.inl (extShape t ht)) balanced
  have extCopy : ∀ L v, ext [(COPY : F), L, v] = 0 := by
    intro L v
    by_contra ne
    have := (extShape _ ne).1
    simp at this
    have := valid.width.1
    omega
  obtain ⟨holds, wideBalanced⟩ := System.sound ok small' tall rows extCopy exact
  rw [extWide, System.wideLedger_lowered sys circuits, ← add_assoc] at wideBalanced
  have lengths : sys.circuits.length = plan.singles.length := by simp [circuits]
  have W : Wide plan idOf bound rom root (instances plan.singles sys main) tables := {
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

/-- **End to end.** An accepting narrow trace of the tiled layout of the
activated single chips of a depth-certified plan proves the entry claim
against the independent source semantics. -/
theorem narrow_heap_sound {source : Generic.Source F} {entries : List String}
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
    (idOf : String → Nat) {sys : System F} (ok : sys.check = true)
    (circuits : sys.circuits = plan.singles.map (Bridge.lower idOf))
    (capacity : capacityRows plan.singles sys ≤ 2 ^ 39)
    {bound : Nat} (small : SmallCast F bound) (sysBound : sys.bound ≤ bound) (tags : 3 < bound)
    (lookups : capacityLookups plan.singles sys < bound)
    (characteristic : ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ cfg.bits → (n : F) ≠ 0)
    (shaped : Shaped.check (Depth.system cfg prepared.system) plan.singles idOf root bound = true)
    (context : (Depth.system cfg prepared.system).checkContext (Erasure.rawROM rom) root = .ok ())
    {tables : Ledger F}
    (tableSupport : ∀ t, tables t ≠ 0 →
      (∃ mc ∈ (Depth.system cfg prepared.system).mapClaims, t = encode idOf mc) ∨
        ∃ e ∈ (Erasure.rawROM rom).entries, t = encodeRom e)
    {ext : Ledger F}
    (extShape : ∀ t, ext t ≠ 0 → t.length = sys.width + 1 ∧ t.head? ≠ some (COPY : F))
    (extWide : Finsupp.mapDomain sys.proj ext = Finsupp.single (encode idOf root) 1 + tables)
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
  obtain ⟨weighted, length, checked⟩ := System.checkMemo_of_narrow plan activated idOf ok circuits
    small sysBound tags lookups (Shaped.of_check shaped) romPacked context tableSupport extShape extWide tall rows
    balanced enablesOk
  exact prepared.depth_grouped_activated_heap_sound compiled certified plan activated entry valid
    signed rooted outside (length.trans capacity) characteristic checked arguments decoded

end Aiur.Tiling
