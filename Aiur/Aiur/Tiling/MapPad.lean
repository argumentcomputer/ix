import Aiur.Tiling.WideStage

/-!
# Map tables without a selector

`WideStage.mapCircuit` weights each claim row by `sel · mult`, so its padding
rows (`sel = 0`) contribute nothing. A PLONK backend that elides count range
checks needs every pulled count to be a plain main column. `mapCircuitD L`
pulls `push(-mult, cells)` instead: there is no `sel` column, and a padding
row repeats the table's last claim (`mapFixedD`), so every row's tuple is a
genuine claim whatever its multiplicity (`mapAirD_support`). That is all the
end-to-end proof uses of the map tables (`tableSupport` of `Bridge.Wide`), so
`wide_heap_sound_insts_dup` and `wide_heap_sound_dup` are
`wide_heap_sound_insts` and `wide_heap_sound` with these tables.

Every table of `mapAirsD` has at least one claim: `mapLengths` lists only
lengths that occur.
-/

namespace Aiur.Tiling.WideStage

open Aiur.Circuit
open Aiur.Optimized
open Bridge

variable {F : Type} [Field F]

/-- The map table circuit for claims of length `L` without a selector: main
`mult` (var 0) and fixed cells (vars `1 … L`). -/
def mapCircuitD (L : Nat) : Tiling.Circuit F where
  width := 1
  fixedWidth := L
  constraints := []
  lookups := [⟨.sub (.const 0) (.var 0), (List.range L).map fun k => .var (k + 1)⟩]

/-- The claim on row `i`: row `i` of the claims, and the last claim on the
padding rows past them. -/
def padRow (claims : List (List F)) (i : Nat) : List F := claims.getD (min i (claims.length - 1)) []

/-- Fixed matrix of a selector-free map table: column `k` is cell `k` of
`padRow claims i`. -/
def mapFixedD (claims : List (List F)) (i k : Nat) : F := (padRow claims i).getD k 0

def mapAirD (L : Nat) (claims : List (List F)) (rows : Nat) : Air F :=
  ⟨mapCircuitD L, rows, mapFixedD claims⟩

/-- One selector-free map table per claim length, `cap L` rows each. -/
def mapAirsD (claims : List (List F)) (cap : Nat → Nat) : List (Air F) :=
  (mapLengths claims).map fun L => mapAirD L (claimsOf claims L) (cap L)

omit [Field F] in
theorem padRow_mem {claims : List (List F)} (nonempty : claims ≠ []) (i : Nat) : padRow claims i ∈ claims := by
  have pos : 0 < claims.length := List.length_pos_iff.mpr nonempty
  have lt : min i (claims.length - 1) < claims.length := by omega
  rw [padRow, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem lt, Option.getD_some]
  exact List.getElem_mem lt

theorem mapAirD_rowLedger (L : Nat) (claims : List (List F)) (rows : Nat)
    (main : Nat → Scalar.Circuit.Var → F) (i : Nat) :
    (mapAirD L claims rows).circuit.rowLedger ((mapAirD L claims rows).assign main i) =
      Finsupp.single ((List.range L).map fun k => (padRow claims i).getD k 0) (-(main i 0)) := by
  simp only [Circuit.rowLedger, Lookup.entry, Lookup.tuple, mapAirD, mapCircuitD]
  simp [Air.assign_apply, Scalar.Circuit.ArithExpr.denote, List.map_map, Function.comp_def, mapFixedD]

section Support

variable [DecidableEq F]

/-- A nonzero entry of a selector-free map table row is one of its claims. -/
theorem mapAirD_support {L : Nat} {claims : List (List F)} (nonempty : claims ≠ [])
    (len : ∀ t ∈ claims, t.length = L) {rows : Nat} (main : Nat → Scalar.Circuit.Var → F) (i : Nat)
    (t : List F) (h : (mapAirD L claims rows).circuit.rowLedger ((mapAirD L claims rows).assign main i) t ≠ 0) :
    t ∈ claims := by
  rw [mapAirD_rowLedger, Finsupp.single_apply] at h
  split at h
  · rename_i e
    have mem := padRow_mem nonempty i
    rw [← e, ← len _ mem, map_getD_range]
    exact mem
  · exact absurd rfl h

omit [Field F] [DecidableEq F] in
theorem claimsOf_ne_nil {claims : List (List F)} {L : Nat} (h : L ∈ mapLengths claims) :
    claimsOf claims L ≠ [] := by
  simp only [mapLengths, List.mem_dedup, List.mem_map] at h
  obtain ⟨t, ht, rfl⟩ := h
  intro e
  have : t ∈ claimsOf claims t.length := List.mem_filter.mpr ⟨ht, by simp⟩
  rw [e] at this
  cases this

/-- A nonzero entry of the selector-free map tables is a claim. -/
theorem mapAirsD_support (claims : List (List F)) (cap : Nat → Nat)
    (main : Nat → Nat → Scalar.Circuit.Var → F) (t : List F)
    (ht : stageLedger (mapAirsD claims cap) main t ≠ 0) : t ∈ claims := by
  refine stage_support (P := (· ∈ claims)) ?_ t ht
  intro x hx i _ u hu
  have mem := List.fst_mem_of_mem_zipIdx hx
  simp only [mapAirsD, List.mem_map] at mem
  obtain ⟨L, hL, e⟩ := mem
  rw [← e] at hu
  exact claimsOf_sub claims L _
    (mapAirD_support (claimsOf_ne_nil hL) (claimsOf_length claims L) _ i u hu)

end Support

section Sound

variable [DecidableEq F]

/-- `wide_heap_sound_insts` with the selector-free map tables `mapAirsD`. -/
theorem wide_heap_sound_insts_dup {source : Generic.Source F} {entries : List String}
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
    (idOf : String → Nat) {insts : List (Chip F × (Scalar.Circuit.Var → F))}
    (chipsIn : ∀ p ∈ insts, p.1 ∈ plan.singles)
    (instsHold : ∀ p ∈ insts, (Bridge.lower idOf p.1).Holds p.2)
    (capacity : insts.length ≤ 2 ^ 39)
    {mapCap : Nat → Nat} {roms : List (Nat × Nat)} (widths : (roms.map Prod.fst).Nodup)
    {bound : Nat} (romCaps : ∀ r ∈ roms, r.2 ≤ bound)
    (small : SmallCast F bound) (tags : 2 < bound) (lookups : lookupCount insts < bound)
    (characteristic : ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ cfg.bits → (n : F) ≠ 0)
    (shaped : Shaped.check (Depth.system cfg prepared.system) plan.singles idOf root bound = true)
    (context : (Depth.system cfg prepared.system).checkContext (Erasure.rawROM ⟨[]⟩) root = .ok ())
    (enablesOk : ∀ c ∈ plan.singles, checkEnables bound c = true)
    {mainM mainR : Nat → Nat → Scalar.Circuit.Var → F}
    (balanced : (insts.map fun p => (Bridge.lower idOf p.1).rowLedger p.2).sum +
      stageLedger (mapAirsD ((Depth.system cfg prepared.system).mapClaims.map (encode idOf)) mapCap) mainM +
      stageLedger (romAirs roms) mainR + Finsupp.single (encode idOf root) 1 = 0) :
    (wideRom roms mainR).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (wideRom roms mainR)).decode
          specialized.program.enums) heap value result := by
  set rom := wideRom roms mainR
  have valid : rom.Valid := wideRom_valid widths (fun r hr i hi i' hi' e =>
    small.inj (by have := romCaps r hr; omega) (by have := romCaps r hr; omega) e) mainR
  have context' : (Depth.system cfg prepared.system).checkContext (Erasure.rawROM rom) root = .ok () := by
    obtain ⟨formed, pub, _, wf⟩ := System.checkContext_iff.mp context
    exact System.checkContext_iff.mpr ⟨formed, pub, Erasure.rawROM_valid valid, wf⟩
  set claims := (Depth.system cfg prepared.system).mapClaims.map (encode idOf)
  set tables := stageLedger (mapAirsD claims mapCap) mainM + stageLedger (romAirs roms) mainR
  have W : Wide plan idOf bound (Erasure.rawROM rom) root insts tables := {
    chips := chipsIn
    holds := instsHold
    small := small
    enablesOk := enablesOk
    tags := tags
    count := lookups
    shaped := Shaped.of_check shaped
    romPacked := rawROM_packed rom
    tableSupport := fun t ht => by
      simp only [tables, Finsupp.add_apply] at ht
      by_cases hm : stageLedger (mapAirsD claims mapCap) mainM t = 0
      · rw [hm, zero_add] at ht
        exact Or.inr (romAirs_support roms mainR t ht)
      · obtain ⟨mc, hmc, e⟩ := List.mem_map.mp (mapAirsD_support claims mapCap mainM t hm)
        exact Or.inl ⟨mc, hmc, e.symm⟩
    balanced := by
      rw [← balanced]
      simp only [tables]
      abel }
  obtain ⟨weighted, length, checked⟩ := W.checkMemo activated context'
  exact ⟨valid, prepared.depth_grouped_activated_heap_sound compiled certified plan activated entry valid
    signed rooted outside (length.trans capacity) characteristic checked arguments decoded⟩

/-- `wide_heap_sound` with the selector-free map tables `mapAirsD`. -/
theorem wide_heap_sound_dup {source : Generic.Source F} {entries : List String}
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
    (idOf : String → Nat) {units : List ((Chip F × Option (Unroll F)) × Nat)}
    (chipsIn : ∀ u ∈ units, u.1.1 ∈ plan.singles)
    (unrolled : ∀ u ∈ units, unitOk idOf u.1 = true)
    (capacity : unitCapRows units ≤ 2 ^ 39)
    {mapCap : Nat → Nat} {roms : List (Nat × Nat)} (widths : (roms.map Prod.fst).Nodup)
    {bound : Nat} (romCaps : ∀ r ∈ roms, r.2 ≤ bound)
    (small : SmallCast F bound) (tags : 2 < bound) (lookups : unitCapLookups units < bound)
    (characteristic : ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ cfg.bits → (n : F) ≠ 0)
    (shaped : Shaped.check (Depth.system cfg prepared.system) plan.singles idOf root bound = true)
    (context : (Depth.system cfg prepared.system).checkContext (Erasure.rawROM ⟨[]⟩) root = .ok ())
    (enablesOk : ∀ c ∈ plan.singles, checkEnables bound c = true)
    {mainU mainM mainR : Nat → Nat → Scalar.Circuit.Var → F}
    (holds : StageHolds (unitAirs idOf units) mainU)
    (balanced : stageLedger (unitAirs idOf units) mainU +
      stageLedger (mapAirsD ((Depth.system cfg prepared.system).mapClaims.map (encode idOf)) mapCap) mainM +
      stageLedger (romAirs roms) mainR + Finsupp.single (encode idOf root) 1 = 0) :
    (wideRom roms mainR).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (wideRom roms mainR)).decode
          specialized.program.enums) heap value result := by
  rw [unitAirs_ledger unrolled] at balanced
  exact wide_heap_sound_insts_dup compiled prepared certified plan activated entry signed rooted outside
    arguments decoded idOf
    (fun p hp => by obtain ⟨u, hu, e⟩ := unitInsts_chip hp; rw [e]; exact chipsIn u hu)
    (fun p hp => unitInsts_holds holds hp)
    (by rw [length_unitInsts]; exact capacity) widths romCaps small tags
    (by rw [lookupCount_unitInsts]; exact lookups) characteristic shaped context enablesOk balanced

end Sound

end Aiur.Tiling.WideStage
