import Aiur.Library.Field.BLS12381.Prime
import Aiur.Plonk.Terminal
import Aiur.Plonk.BetaGadget
import Aiur.Plonk.Logup

/-!
# PLONK SCS soundness theorems over BLS12-381

Corollaries of the generic-prime `Aiur.Plonk` soundness theorems instantiated at
the BLS12-381 scalar field `F := ZMod BLS12381.modulus`
(`r = 52435875175126190479447740508185965837690552500527637822603658699938581184513`,
primality proved via pure Lean Lucas certificates in
`Aiur.Library.Field.BLS12381.Prime`).

The two field hypotheses of the generic theorems become numeric bounds:

* `small : SmallCast BF bound` follows from `hbound : bound ≤ 2 ^ 63`
  (or even `bound ≤ 2 ^ 254`), via `smallCast_zmod`;
* `characteristic : ∀ n, 0 < n → n ≤ 2 ^ 39 * 2 ^ cfg.bits → (n : BF) ≠ 0`
  follows from `hbits : cfg.bits ≤ 24`, since then `n ≤ 2 ^ 63 < modulus`.
-/

namespace Aiur.Plonk.BLS12381

open Aiur.Circuit
open Aiur.Optimized
open Aiur.Tiling
open Aiur.Tiling.Bridge
open Aiur.Tiling.WideStage (Air StageHolds stageLedger)
open Aiur.Tiling.Grouped (SharedTable allChips circuitNames)
open Aiur.Plonk.Lower (Ref)
open Aiur.Library.Field.BLS12381
  (modulus modulus_prime two_pow_63_lt_modulus two_pow_254_lt_modulus modulus_lt_two_pow_255)

abbrev BF := Aiur.Library.Field.BLS12381.F

theorem smallCast {bound : Nat} (hbound : bound ≤ 2 ^ 63) : SmallCast BF bound :=
  smallCast_zmod modulus (by have := two_pow_63_lt_modulus; omega)

theorem smallCast_254 {bound : Nat} (hbound : bound ≤ 2 ^ 254) : SmallCast BF bound :=
  smallCast_zmod modulus (by have := two_pow_254_lt_modulus; omega)

theorem characteristic {cfg : Depth.Config} (hbits : cfg.bits ≤ 24) :
    ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ cfg.bits → (n : BF) ≠ 0 := by
  intro n positive le e
  have : 2 ^ 39 * 2 ^ cfg.bits ≤ 2 ^ 39 * 2 ^ 24 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hbits)
  have h63 : (2 : Nat) ^ 39 * 2 ^ 24 = 2 ^ 63 := by norm_num
  have small : SmallCast BF (2 ^ 63 + 1) :=
    smallCast_zmod modulus (by have := two_pow_63_lt_modulus; omega)
  have := small n (by omega) e
  omega

/-- BLS12-381 scalar modulus has exact bit width 255 (`2^254 < r < 2^255`). -/
theorem beta_nbits_eq : Nat.log2 modulus + 1 = 255 := by
  have hlog : Nat.log2 modulus = 254 := by
    rw [Nat.log2_eq_iff (by have := two_pow_254_lt_modulus; omega)]
    exact ⟨Nat.le_of_lt two_pow_254_lt_modulus, modulus_lt_two_pow_255⟩
  omega

theorem beta_bitsWidthOk_255 (ps : List Nat) : Beta.bitsWidthOk modulus 255 (some ps) = true := by
  simp only [Beta.bitsWidthOk, decide_eq_true_eq]
  exact Nat.le_of_lt modulus_lt_two_pow_255

theorem beta_bitsWidthOk_34 : Beta.bitsWidthOk modulus 34 none = true := by
  simp only [Beta.bitsWidthOk, decide_eq_true_eq]
  have h1 : (2 : Nat) ^ 34 ≤ 2 ^ 63 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have h2 := two_pow_63_lt_modulus
  omega

/-- `Beta.beta_functional` instantiated at BLS12-381. -/
theorem beta_sound (w : Nat → BF) {ss : List (Beta.Step BF)} {γw βw : Nat}
    (ok : Beta.betaOk ss γw βw = true) (sat : ∀ g ∈ Beta.gadgetGates ss, g.Holds w) :
    w βw = Beta.betaFn ss γw βw (w γw) :=
  Beta.beta_functional w ok sat

/-- `stage_sound` instantiated at BLS12-381. -/
theorem stage_sound_bls12381 {airs : List (Air BF)} {P : Lower.Pool BF} {poolIdx : Ref → Option Nat}
    (ok : stageOk airs P poolIdx = true) (W : Wiring airs P) (w : Nat → BF)
    (sat : ∀ g ∈ emitGates airs P W, g.Holds w) :
    StageHolds airs (W.main w) ∧
      ((∀ u, MsgTuple airs (W.main w) u → fp (w (W.poolWire Lower.gammaRef)) (w (W.poolWire Lower.betaRef)) u ≠ 0) →
        logupEval (w (W.poolWire Lower.gammaRef)) (w (W.poolWire Lower.betaRef)) (stageLedger airs (W.main w)) =
          - w W.init) :=
  stage_sound ok W w sat

/-- `plonk_wide_heap_sound` over BLS12-381. -/
theorem plonk_wide_heap_sound_bls12381 {source : Generic.Source BF} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id) (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries)
    {args : List (SourceValue BF)} {result : Value BF} {wires : List (WireValue BF)}
    {output : WireValue BF}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Circuit.Message BF}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (entryPlain : cfg.recursive name = false)
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat) {units : List ((Chip BF × Option (Unroll BF)) × Nat)}
    (chipsIn : ∀ u ∈ units, u.1.1 ∈ plan.singles)
    (unrolled : ∀ u ∈ units, Bridge.unitOk idOf u.1 = true)
    (capacity : WideStage.unitCapRows units ≤ 2 ^ 39)
    {mapCap : Nat → Nat} {roms : List (Nat × Nat)} (widths : (roms.map Prod.fst).Nodup)
    {bound : Nat} (romCaps : ∀ r ∈ roms, r.2 ≤ bound)
    (hbound : bound ≤ 2 ^ 63) (tags : 2 < bound) (lookups : WideStage.unitCapLookups units < bound)
    (hbits : cfg.bits ≤ 24)
    (chanIds : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) plan.singles root,
      ∀ y ∈ Bridge.channels (Depth.system cfg prepared.system) plan.singles root, idOf x = idOf y → x = y)
    (chanBound : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) plan.singles root, idOf x < bound)
    (enablesOk : ∀ c ∈ plan.singles, Bridge.checkEnables bound c = true)
    {airs : List (Air BF)}
    (hairs : airs = WideStage.unitAirs idOf units ++
      WideStage.mapAirs ((Depth.system cfg prepared.system).mapClaims.map (encode idOf)) mapCap ++
      WideStage.romAirs roms)
    {k : BF} {n : Nat} {P : Lower.Pool BF} {poolIdx : Ref → Option Nat}
    (ok : stageOk (airs ++ [rootAir k n]) P poolIdx = true)
    (W : Wiring (airs ++ [rootAir k n]) P)
    {nWires publics : Nat} {committed : List Nat} {w : Nat → BF} {pub : List BF} {H : List BF → BF}
    (sat : (emitScs (airs ++ [rootAir k n]) P W nWires publics committed).Satisfied w pub H)
    (entryId : (idOf root.channel : BF) = k)
    (statement : (List.range n).map (W.main w airs.length 0) = (encode idOf root).drop 2)
    (good : ChallengeGood (w (W.poolWire Lower.gammaRef)) (w (W.poolWire Lower.betaRef))
      (MsgTuple (airs ++ [rootAir k n]) (W.main w)) (stageLedger (airs ++ [rootAir k n]) (W.main w))) :
    let mainR := fun t => W.main w ((WideStage.unitAirs idOf units).length +
      (WideStage.mapAirs ((Depth.system cfg prepared.system).mapClaims.map (Bridge.encode idOf)) mapCap).length + t)
    (WideStage.wideRom roms mainR).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (WideStage.wideRom roms mainR)).decode
          specialized.program.enums) heap value result :=
  plonk_wide_heap_sound compiled prepared certified plan activated entry signed rooted outside entryPlain
    arguments decoded idOf chipsIn unrolled capacity widths romCaps (smallCast hbound) tags lookups
    (characteristic hbits) chanIds chanBound enablesOk hairs ok W sat entryId statement good

/-- `plonk_shared_heap_sound` over BLS12-381. -/
theorem plonk_shared_heap_sound_bls12381 {source : Generic.Source BF} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id) (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries)
    {args : List (SourceValue BF)} {result : Value BF} {wires : List (WireValue BF)}
    {output : WireValue BF}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Circuit.Message BF}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (entryPlain : cfg.recursive name = false)
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat) (idOk : ∀ x n, id x = .ok n → n = idOf x) (names : (circuitNames plan).Nodup)
    {units : List ((Chip BF × Option (Unroll BF)) × Nat)}
    (chipsIn : ∀ u ∈ units, u.1.1 ∈ plan.singles)
    (unrolled : ∀ u ∈ units, Bridge.unitOk idOf u.1 = true)
    (capacity : WideStage.unitCapRows units ≤ 2 ^ 39)
    {shared : List (SharedTable BF)}
    (sharedOk : ∀ T ∈ shared,
      T.check ((Depth.system cfg prepared.system).mapClaims.map (encode idOf)) = true)
    {roms : List (Nat × Nat)} (widths : (roms.map Prod.fst).Nodup)
    {bound : Nat} (romCaps : ∀ r ∈ roms, r.2 ≤ bound) (romWidths : ∀ r ∈ roms, r.1 < bound)
    (hbound : bound ≤ 2 ^ 63) (tags : 2 < bound) (lookups : WideStage.unitCapLookups units < bound)
    (hbits : cfg.bits ≤ 24)
    (chanIds : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) (allChips plan) root,
      ∀ y ∈ Bridge.channels (Depth.system cfg prepared.system) (allChips plan) root, idOf x = idOf y → x = y)
    (chanBound : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) (allChips plan) root, idOf x < bound)
    (enablesOk : ∀ c ∈ allChips plan, Bridge.checkEnables bound c = true)
    (memWidth : ∀ c ∈ allChips plan, ∀ m ∈ c.memory, m.value.words.length < bound)
    {airs : List (Air BF)}
    (hairs : airs = WideStage.unitAirs idOf units ++ shared.map SharedTable.air ++ WideStage.romAirs roms)
    {k : BF} {n : Nat} {P : Lower.Pool BF} {poolIdx : Ref → Option Nat}
    (ok : stageOk (airs ++ [rootAir k n]) P poolIdx = true)
    (W : Wiring (airs ++ [rootAir k n]) P)
    {nWires publics : Nat} {committed : List Nat} {w : Nat → BF} {pub : List BF} {H : List BF → BF}
    (sat : (emitScs (airs ++ [rootAir k n]) P W nWires publics committed).Satisfied w pub H)
    (entryId : (idOf root.channel : BF) = k)
    (statement : (List.range n).map (W.main w airs.length 0) = (encode idOf root).drop 2)
    (good : ChallengeGood (w (W.poolWire Lower.gammaRef)) (w (W.poolWire Lower.betaRef))
      (MsgTuple (airs ++ [rootAir k n]) (W.main w)) (stageLedger (airs ++ [rootAir k n]) (W.main w))) :
    let mainR := fun t => W.main w ((WideStage.unitAirs idOf units).length + shared.length + t)
    (WideStage.wideRom roms mainR).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (WideStage.wideRom roms mainR)).decode
          specialized.program.enums) heap value result :=
  plonk_shared_heap_sound compiled prepared certified plan activated entry signed rooted outside entryPlain
    arguments decoded idOf idOk names chipsIn unrolled capacity sharedOk widths romCaps romWidths
    (smallCast hbound) tags lookups (characteristic hbits) chanIds chanBound enablesOk memWidth hairs ok W
    sat entryId statement good

/-- `plonk_terminal_sound` over BLS12-381. -/
theorem plonk_terminal_sound_bls12381 {source : Generic.Source BF} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id) (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries)
    {args : List (SourceValue BF)} {result : Value BF} {wires : List (WireValue BF)}
    {output : WireValue BF}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Circuit.Message BF}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (entryPlain : cfg.recursive name = false)
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat) {units : List ((Chip BF × Option (Unroll BF)) × Nat)}
    (chipsIn : ∀ u ∈ units, u.1.1 ∈ plan.singles)
    (unrolled : ∀ u ∈ units, Bridge.unitOk idOf u.1 = true)
    (capacity : WideStage.unitCapRows units ≤ 2 ^ 39)
    {mapCap : Nat → Nat} {roms : List (Nat × Nat)} (widths : (roms.map Prod.fst).Nodup)
    {bound : Nat} (romCaps : ∀ r ∈ roms, r.2 ≤ bound)
    (hbound : bound ≤ 2 ^ 63) (tags : 2 < bound) (lookups : WideStage.unitCapLookups units < bound)
    (hbits : cfg.bits ≤ 24)
    (chanIds : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) plan.singles root,
      ∀ y ∈ Bridge.channels (Depth.system cfg prepared.system) plan.singles root, idOf x = idOf y → x = y)
    (chanBound : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) plan.singles root, idOf x < bound)
    (enablesOk : ∀ c ∈ plan.singles, Bridge.checkEnables bound c = true)
    {airs : List (Air BF)}
    (hairs : airs = WideStage.unitAirs idOf units ++
      WideStage.mapAirs ((Depth.system cfg prepared.system).mapClaims.map (encode idOf)) mapCap ++
      WideStage.romAirs roms)
    {k : BF} {n : Nat} {P : Lower.Pool BF} {poolIdx : Ref → Option Nat}
    (ok : stageOk (airs ++ [rootAir k n]) P poolIdx = true)
    (W : Wiring (airs ++ [rootAir k n]) P) {steps : List (Beta.Step BF)}
    (bok : Beta.betaOk steps (W.poolWire Lower.gammaRef) (W.poolWire Lower.betaRef) = true)
    {nWires publics : Nat} {w : Nat → BF} {pub : List BF} {H : List BF → BF}
    (sat : (emitScsFull (airs ++ [rootAir k n]) P W steps nWires publics).Satisfied w pub H)
    (entryId : (idOf root.channel : BF) = k)
    (statement : (List.range n).map (W.main w airs.length 0) = (encode idOf root).drop 2)
    (good : let c := (commitList (airs ++ [rootAir k n]) W.cellWire).map w
      ChallengeGood (H c) (W.betaB steps (H c)) (tuplesOf W c) (ledgerOf W c)) :
    let mainR := fun t => W.main w ((WideStage.unitAirs idOf units).length +
      (WideStage.mapAirs ((Depth.system cfg prepared.system).mapClaims.map (Bridge.encode idOf)) mapCap).length + t)
    (WideStage.wideRom roms mainR).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (WideStage.wideRom roms mainR)).decode
          specialized.program.enums) heap value result :=
  plonk_terminal_sound compiled prepared certified plan activated entry signed rooted outside entryPlain
    arguments decoded idOf chipsIn unrolled capacity widths romCaps (smallCast hbound) tags lookups
    (characteristic hbits) chanIds chanBound enablesOk hairs ok W bok sat entryId statement good

/-- `plonk_shared_terminal_sound` over BLS12-381 (shared map tables + in-circuit `β` gadget). -/
theorem plonk_shared_terminal_sound_bls12381 {source : Generic.Source BF} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id) (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries)
    {args : List (SourceValue BF)} {result : Value BF} {wires : List (WireValue BF)}
    {output : WireValue BF}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Circuit.Message BF}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (entryPlain : cfg.recursive name = false)
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat) (idOk : ∀ x n, id x = .ok n → n = idOf x) (names : (circuitNames plan).Nodup)
    {units : List ((Chip BF × Option (Unroll BF)) × Nat)}
    (chipsIn : ∀ u ∈ units, u.1.1 ∈ plan.singles)
    (unrolled : ∀ u ∈ units, Bridge.unitOk idOf u.1 = true)
    (capacity : WideStage.unitCapRows units ≤ 2 ^ 39)
    {shared : List (SharedTable BF)}
    (sharedOk : ∀ T ∈ shared,
      T.check ((Depth.system cfg prepared.system).mapClaims.map (encode idOf)) = true)
    {roms : List (Nat × Nat)} (widths : (roms.map Prod.fst).Nodup)
    {bound : Nat} (romCaps : ∀ r ∈ roms, r.2 ≤ bound) (romWidths : ∀ r ∈ roms, r.1 < bound)
    (hbound : bound ≤ 2 ^ 63) (tags : 2 < bound) (lookups : WideStage.unitCapLookups units < bound)
    (hbits : cfg.bits ≤ 24)
    (chanIds : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) (allChips plan) root,
      ∀ y ∈ Bridge.channels (Depth.system cfg prepared.system) (allChips plan) root, idOf x = idOf y → x = y)
    (chanBound : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) (allChips plan) root, idOf x < bound)
    (enablesOk : ∀ c ∈ allChips plan, Bridge.checkEnables bound c = true)
    (memWidth : ∀ c ∈ allChips plan, ∀ m ∈ c.memory, m.value.words.length < bound)
    {airs : List (Air BF)}
    (hairs : airs = WideStage.unitAirs idOf units ++ shared.map SharedTable.air ++ WideStage.romAirs roms)
    {k : BF} {n : Nat} {P : Lower.Pool BF} {poolIdx : Ref → Option Nat}
    (ok : stageOk (airs ++ [rootAir k n]) P poolIdx = true)
    (W : Wiring (airs ++ [rootAir k n]) P) {steps : List (Beta.Step BF)}
    (bok : Beta.betaOk steps (W.poolWire Lower.gammaRef) (W.poolWire Lower.betaRef) = true)
    {nWires publics : Nat} {w : Nat → BF} {pub : List BF} {H : List BF → BF}
    (sat : (emitScsFull (airs ++ [rootAir k n]) P W steps nWires publics).Satisfied w pub H)
    (entryId : (idOf root.channel : BF) = k)
    (statement : (List.range n).map (W.main w airs.length 0) = (encode idOf root).drop 2)
    (good : let c := (commitList (airs ++ [rootAir k n]) W.cellWire).map w
      ChallengeGood (H c) (W.betaB steps (H c)) (tuplesOf W c) (ledgerOf W c)) :
    let mainR := fun t => W.main w ((WideStage.unitAirs idOf units).length + shared.length + t)
    (WideStage.wideRom roms mainR).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (WideStage.wideRom roms mainR)).decode
          specialized.program.enums) heap value result :=
  plonk_shared_terminal_sound compiled prepared certified plan activated entry signed rooted outside entryPlain
    arguments decoded idOf idOk names chipsIn unrolled capacity sharedOk widths romCaps romWidths
    (smallCast hbound) tags lookups (characteristic hbits) chanIds chanBound enablesOk memWidth hairs ok W
    bok sat entryId statement good

/-! ## Axiom audit -/

/-- info: 'Aiur.Library.Field.BLS12381.modulus_prime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.Field.BLS12381.modulus_prime

/-- info: 'Aiur.Plonk.BLS12381.beta_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Plonk.BLS12381.beta_sound

/-- info: 'Aiur.Plonk.BLS12381.stage_sound_bls12381' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Plonk.BLS12381.stage_sound_bls12381

/-- info: 'Aiur.Plonk.BLS12381.plonk_wide_heap_sound_bls12381' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Plonk.BLS12381.plonk_wide_heap_sound_bls12381

/-- info: 'Aiur.Plonk.BLS12381.plonk_shared_heap_sound_bls12381' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Plonk.BLS12381.plonk_shared_heap_sound_bls12381

/-- info: 'Aiur.Plonk.BLS12381.plonk_terminal_sound_bls12381' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Plonk.BLS12381.plonk_terminal_sound_bls12381

/-- info: 'Aiur.Plonk.BLS12381.plonk_shared_terminal_sound_bls12381' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Plonk.BLS12381.plonk_shared_terminal_sound_bls12381

end Aiur.Plonk.BLS12381
