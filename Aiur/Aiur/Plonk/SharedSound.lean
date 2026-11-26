import Aiur.Plonk.WideSound
import Aiur.Tiling.Grouped

/-!
# PLONK soundness over the compiler's shared map tables

`plonk_shared_heap_sound` is `plonk_wide_heap_sound` with the map tables
`shared.map SharedTable.air` (the compiler layout, `Grouped.sharedTablesOf`,
each accepted by `SharedTable.check`) in place of `mapAirs`. It composes
`stage_balanced` with `Grouped.grouped_heap_sound_shared_compiled` at
`groups = []`: the tables are `unitAirs idOf units ++ shared.map
SharedTable.air ++ romAirs roms` followed by the root table, a zero ledger
gives the trimmed balance (`Finsupp.mapDomain_zero`), and the empty group
list holds trivially.

The hypotheses are those of `plonk_wide_heap_sound`, with `sharedOk` for the
map tables and the extra static checks of the grouped theorem (`idOk`,
`names`, `romWidths`, `memWidth`, the channel checks over `allChips plan`).
-/

namespace Aiur.Plonk

open Aiur.Circuit
open Aiur.Optimized
open Aiur.Tiling
open Aiur.Tiling.Bridge
open Aiur.Tiling.WideStage (Air stageLedger)
open Aiur.Tiling.Grouped (SharedTable groupAirs allChips circuitNames)
open Lower (Ref)

section Prime

variable {p : Nat} [Fact (Nat.Prime p)]

theorem plonk_shared_heap_sound {source : Generic.Source (ZMod p)} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id) (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries)
    {args : List (SourceValue (ZMod p))} {result : Value (ZMod p)} {wires : List (WireValue (ZMod p))}
    {output : WireValue (ZMod p)}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Circuit.Message (ZMod p)}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (entryPlain : cfg.recursive name = false)
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat) (idOk : ∀ x n, id x = .ok n → n = idOf x) (names : (circuitNames plan).Nodup)
    {units : List ((Chip (ZMod p) × Option (Unroll (ZMod p))) × Nat)}
    (chipsIn : ∀ u ∈ units, u.1.1 ∈ plan.singles)
    (unrolled : ∀ u ∈ units, Bridge.unitOk idOf u.1 = true)
    (capacity : WideStage.unitCapRows units ≤ 2 ^ 39)
    {shared : List (SharedTable (ZMod p))}
    (sharedOk : ∀ T ∈ shared,
      T.check ((Depth.system cfg prepared.system).mapClaims.map (encode idOf)) = true)
    {roms : List (Nat × Nat)} (widths : (roms.map Prod.fst).Nodup)
    {bound : Nat} (romCaps : ∀ r ∈ roms, r.2 ≤ bound) (romWidths : ∀ r ∈ roms, r.1 < bound)
    (small : SmallCast (ZMod p) bound) (tags : 2 < bound) (lookups : WideStage.unitCapLookups units < bound)
    (characteristic : ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ cfg.bits → (n : ZMod p) ≠ 0)
    (chanIds : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) (allChips plan) root,
      ∀ y ∈ Bridge.channels (Depth.system cfg prepared.system) (allChips plan) root, idOf x = idOf y → x = y)
    (chanBound : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) (allChips plan) root, idOf x < bound)
    (enablesOk : ∀ c ∈ allChips plan, Bridge.checkEnables bound c = true)
    (memWidth : ∀ c ∈ allChips plan, ∀ m ∈ c.memory, m.value.words.length < bound)
    {airs : List (Air (ZMod p))}
    (hairs : airs = WideStage.unitAirs idOf units ++ shared.map SharedTable.air ++ WideStage.romAirs roms)
    {k : ZMod p} {n : Nat} {P : Lower.Pool (ZMod p)} {poolIdx : Ref → Option Nat}
    (ok : stageOk (airs ++ [rootAir k n]) P poolIdx = true)
    (W : Wiring (airs ++ [rootAir k n]) P)
    {nWires publics : Nat} {committed : List Nat} {w : Nat → ZMod p} {pub : List (ZMod p)}
    {H : List (ZMod p) → ZMod p}
    (sat : (emitScs (airs ++ [rootAir k n]) P W nWires publics committed).Satisfied w pub H)
    (entryId : (idOf root.channel : ZMod p) = k)
    (statement : (List.range n).map (W.main w airs.length 0) = (encode idOf root).drop 2)
    (good : ChallengeGood (w (W.poolWire Lower.gammaRef)) (w (W.poolWire Lower.betaRef))
      (MsgTuple (airs ++ [rootAir k n]) (W.main w)) (stageLedger (airs ++ [rootAir k n]) (W.main w))) :
    let mainR := fun t => W.main w ((WideStage.unitAirs idOf units).length + shared.length + t)
    (WideStage.wideRom roms mainR).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (WideStage.wideRom roms mainR)).decode
          specialized.program.enums) heap value result := by
  intro mainR
  obtain ⟨holds, balanced⟩ := stage_balanced ok W w sat.2.2 good
  have hroot : (CALL : ZMod p) :: k :: (encode idOf root).drop 2 = encode idOf root := by
    rw [← entryId]; rfl
  rw [statement, hroot] at balanced
  subst hairs
  rw [stageLedger_append, stageLedger_append] at balanced
  refine Grouped.grouped_heap_sound_shared_compiled compiled prepared certified plan activated entry signed
    rooted outside entryPlain arguments decoded idOf idOk names chipsIn unrolled (groups := [])
    (fun _ h => absurd h List.not_mem_nil) (by simpa using capacity) sharedOk widths romCaps romWidths small
    tags (by simpa using lookups) characteristic chanIds chanBound enablesOk memWidth
    (mainU := W.main w) (mainG := W.main w)
    (mainM := fun t => W.main w ((WideStage.unitAirs idOf units).length + t)) (mainR := mainR)
    (stageHolds_append_left (stageHolds_append_left holds)) (fun _ h => absurd h List.not_mem_nil) ?_
  have hG : stageLedger (groupAirs ([] : List (Grouping.Packed (ZMod p) id × Nat))) (W.main w) = 0 := rfl
  rw [hG, add_zero, ← Finsupp.mapDomain_zero (f := trimZeros)]
  congr 1
  rw [← balanced]
  simp only [List.length_append, List.length_map, mainR, add_assoc]

end Prime

end Aiur.Plonk
