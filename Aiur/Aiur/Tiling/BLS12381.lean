import Aiur.Tiling.PeriodicCompact
import Aiur.Tiling.PeriodicMixed
import Aiur.Tiling.WideStage
import Aiur.Tiling.SingleCircuit
import Aiur.Library.Field.BLS12381.Prime

/-!
# The tiling soundness theorems over BLS12-381

Corollaries of the end-to-end tiling and horizontal single-circuit packing
theorems at `BF := Aiur.Library.Field.BLS12381.F = ZMod p` with the BLS12-381
scalar field prime
`p = 52435875175126190479447740508185965837690552500527637822603658699938581184513`
(Lucas primality certificate: `Aiur.Library.Field.BLS12381.modulus_prime`).

The two field hypotheses of the generic theorems become numeric bounds:

* `small : SmallCast BF bound` follows from `hbound : bound ≤ 2 ^ 254`
  (`smallCast`, as `2^254 < p`), with `smallCast_63` specializing to
  `bound ≤ 2 ^ 63` (covering BN3's `566,935,683,439 ≈ 2^39` layout bound);
* `characteristic : ∀ n, 0 < n → n ≤ 2^39 · 2^cfg.bits → (n : BF) ≠ 0`
  follows from `hbits : cfg.bits ≤ 214`, since
  `2^39 · 2^214 = 2^253 < 2^254 < p`.

End-to-end corollaries (Endpoint 2, BLS12-381):

* `narrow_heap_sound_compact_bls12381`: `Periodic.narrow_heap_sound_compact` over `BF`.
* `mixed_heap_sound_bls12381`: `Periodic.mixed_heap_sound` over `BF`.
* `wide_heap_sound_insts_bls12381`: `WideStage.wide_heap_sound_insts` over `BF`.
* `wide_heap_sound_bls12381`: `WideStage.wide_heap_sound` over `BF`.
* `wide_single_circuit_sound_bls12381`: horizontally packed `WideStage` (`num_circuits == 1`) over `BF`.
* `wide_single_circuit_complete_bls12381`: prover completeness for horizontally packed `WideStage` over `BF`.
* `narrow_compact_single_circuit_sound_bls12381`: horizontally packed periodic sharded + compact
  tables (`num_circuits == 1`) over `BF`.
-/

namespace Aiur.Tiling.BLS12381

open Aiur.Circuit
open Aiur.Optimized
open Bridge
open Aiur.Library.Field.BLS12381 (modulus)

local notation "BF" => Aiur.Library.Field.BLS12381.F

theorem two_pow_254_lt : 2 ^ 254 < modulus :=
  Aiur.Library.Field.BLS12381.two_pow_254_lt_modulus

theorem two_pow_63_lt : 2 ^ 63 < modulus :=
  Aiur.Library.Field.BLS12381.two_pow_63_lt_modulus

theorem bn3_bound_ok : 566935683439 ≤ 2 ^ 63 := by norm_num

theorem smallCast {bound : Nat} (hbound : bound ≤ 2 ^ 254) : SmallCast BF bound :=
  smallCast_zmod modulus (by have := two_pow_254_lt; omega)

theorem smallCast_63 {bound : Nat} (hbound : bound ≤ 2 ^ 63) : SmallCast BF bound :=
  smallCast (le_trans hbound (by norm_num))

theorem characteristic {cfg : Depth.Config} (hbits : cfg.bits ≤ 214) :
    ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ cfg.bits → (n : BF) ≠ 0 := by
  intro n positive le hzero
  have hpow : 2 ^ 39 * 2 ^ cfg.bits ≤ 2 ^ 39 * 2 ^ 214 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hbits)
  have h253 : (2 : Nat) ^ 39 * 2 ^ 214 < 2 ^ 254 := by norm_num
  have hlt : n < 2 ^ 254 := lt_of_le_of_lt (le.trans hpow) h253
  have hzero' := smallCast (bound := 2 ^ 254) le_rfl n hlt hzero
  omega

/-- `Periodic.narrow_heap_sound_compact` over BLS12-381. -/
theorem narrow_heap_sound_compact_bls12381 {source : Generic.Source BF} {entries : List String}
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
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat) {S : Periodic.Sharded BF} (ok : S.check = true)
    {units : List (Chip BF × Option (Unroll BF))} (chipsIn : ∀ u ∈ units, u.1 ∈ plan.singles)
    (unrolled : ∀ u ∈ units, unitOk idOf u = true)
    {wide : List (Circuit BF)} {groups : List (List (List Nat))}
    (circuits : S.system.circuits = List.zipWith Circuit.mergeBy wide groups)
    (wideEq : wide = units.map (unitCircuit idOf))
    (lenG : groups.length = wide.length)
    (merged : ∀ j (hw : j < wide.length) (hg : j < groups.length), wide[j].checkMerge groups[j] = true)
    {ν : BF → Nat} {tables : List (Periodic.Compact BF)}
    (tablesOk : Periodic.checkTables S ν tables = true)
    (mapsIn : ∀ T ∈ tables, T.checkMap S = true → ∀ q ∈ T.parts,
      q.tag :: q.sub :: q.payload ∈ (Depth.system cfg prepared.system).mapClaims.map (encode idOf))
    (capacity : Bridge.capacityRowsU units S.system ≤ 2 ^ 39)
    {bound : Nat} (hbound : bound ≤ 2 ^ 254) (tags : 3 < bound)
    (codesBound : ∀ e ∈ S.buses, e.2.1 < bound) (labels : Periodic.copyKey S.labelTotal < bound)
    (shadowBound : ∀ k < S.shards.length, ((S.layout k).shadow S.width).bound ≤ bound)
    (lookups : Bridge.capacityLookupsU units S.system < bound) (ids : S.system.instances ≤ bound)
    (parts : (S.system.enumerate S.system.lookupCount).length + 1 +
      (tables.map (·.parts.length)).sum < bound)
    (hbits : cfg.bits ≤ 214)
    (shaped : Shaped.check (Depth.system cfg prepared.system) plan.singles idOf root bound = true)
    (context : (Depth.system cfg prepared.system).checkContext (Erasure.rawROM ⟨[]⟩) root = .ok ())
    (req : (Part.request S.width (encode idOf root)).checkRequest S.system
      (encode idOf root) = true)
    (req2 : S.checkRequest2 (Part.request S.width (encode idOf root)) = true)
    (enablesOk : ∀ c ∈ plan.singles, checkEnables bound c = true)
    {H : Nat → Nat} {main : Nat → Nat → Nat → BF} {HT : Nat → Nat} {mainT : Nat → Nat → Nat → BF}
    (tall : ∀ k < S.shards.length, ((S.layout k).shadow S.width).places.length ≤ H k)
    (tallT : ∀ t T, tables[t]? = some T → T.rows ≤ HT t)
    (rows : ∀ k < S.shards.length, ∀ p < H k,
      Scalar.Circuit.Satisfies (S.circuit k).constraints (S.assign k (main k) p))
    (balanced : Finsupp.mapDomain trimZeros (S.ledger H main + Periodic.compactLedger S tables HT mainT +
      S.padded2 (Part.request S.width (encode idOf root))) = 0) :
    (Periodic.compactRom S tables mainT).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (Periodic.compactRom S tables mainT)).decode
          specialized.program.enums) heap value result :=
  Periodic.narrow_heap_sound_compact compiled prepared certified plan activated entry signed rooted
    outside arguments decoded idOf ok chipsIn unrolled circuits wideEq lenG merged tablesOk mapsIn
    capacity (smallCast hbound) tags codesBound labels shadowBound lookups ids parts
    (characteristic hbits) shaped context req req2 enablesOk tall tallT rows balanced

/-- `Periodic.mixed_heap_sound` over BLS12-381. -/
theorem mixed_heap_sound_bls12381 {source : Generic.Source BF} {entries : List String}
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
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat) {S : Periodic.Sharded BF} (ok : S.check = true)
    {units : List (Chip BF × Option (Unroll BF))} (chipsIn : ∀ u ∈ units, u.1 ∈ plan.singles)
    (unrolled : ∀ u ∈ units, unitOk idOf u = true)
    {wide : List (Circuit BF)} {groups : List (List (List Nat))}
    (circuits : S.system.circuits = List.zipWith Circuit.mergeBy wide groups)
    (wideEq : wide = units.map (unitCircuit idOf))
    (lenG : groups.length = wide.length)
    (merged : ∀ j (hw : j < wide.length) (hg : j < groups.length), wide[j].checkMerge groups[j] = true)
    {ν : BF → Nat} {tables : List (Periodic.Compact BF)}
    (tablesOk : Periodic.checkTables S ν tables = true)
    (mapsIn : ∀ T ∈ tables, T.checkMap S = true → ∀ q ∈ T.parts,
      q.tag :: q.sub :: q.payload ∈ (Depth.system cfg prepared.system).mapClaims.map (encode idOf))
    {wideUnits : List (Periodic.WideUnit BF)} (wideIn : ∀ u ∈ wideUnits, u.chip ∈ plan.singles)
    (wideOk : Periodic.checkMixed S idOf ν tables wideUnits = true)
    (capacity : Bridge.capacityRowsU units S.system + Periodic.mixedRows wideUnits ≤ 2 ^ 39)
    {bound : Nat} (hbound : bound ≤ 2 ^ 254) (tags : 3 < bound)
    (codesBound : ∀ e ∈ S.buses, e.2.1 < bound) (labels : Periodic.copyKey S.labelTotal < bound)
    (shadowBound : ∀ k < S.shards.length, ((S.layout k).shadow S.width).bound ≤ bound)
    (lookups : Bridge.capacityLookupsU units S.system + Periodic.mixedLookups wideUnits < bound)
    (ids : S.system.instances ≤ bound)
    (parts : (S.system.enumerate S.system.lookupCount).length + 1 +
      (tables.map (·.parts.length)).sum + Periodic.mixedPartCount wideUnits < bound)
    (hbits : cfg.bits ≤ 214)
    (shaped : Shaped.check (Depth.system cfg prepared.system) plan.singles idOf root bound = true)
    (context : (Depth.system cfg prepared.system).checkContext (Erasure.rawROM ⟨[]⟩) root = .ok ())
    (req : (Part.request S.width (encode idOf root)).checkRequest S.system
      (encode idOf root) = true)
    (req2 : S.checkRequest2 (Part.request S.width (encode idOf root)) = true)
    (enablesOk : ∀ c ∈ plan.singles, checkEnables bound c = true)
    {H : Nat → Nat} {main : Nat → Nat → Nat → BF} {HT : Nat → Nat} {mainT : Nat → Nat → Nat → BF}
    {mainW : Nat → Nat → Nat → BF}
    (tall : ∀ k < S.shards.length, ((S.layout k).shadow S.width).places.length ≤ H k)
    (tallT : ∀ t T, tables[t]? = some T → T.rows ≤ HT t)
    (rows : ∀ k < S.shards.length, ∀ p < H k,
      Scalar.Circuit.Satisfies (S.circuit k).constraints (S.assign k (main k) p))
    (rowsW : ∀ (t : Nat) (u : Periodic.WideUnit BF), wideUnits[t]? = some u → ∀ r < u.rows,
      Scalar.Circuit.Satisfies (u.circuit idOf S.buses S.width).constraints (u.assign (mainW t) r))
    (balanced : Finsupp.mapDomain trimZeros (S.ledger H main + Periodic.compactLedger S tables HT mainT +
      Periodic.mixedLedger S idOf wideUnits mainW + S.padded2 (Part.request S.width (encode idOf root))) = 0) :
    (Periodic.compactRom S tables mainT).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (Periodic.compactRom S tables mainT)).decode
          specialized.program.enums) heap value result :=
  Periodic.mixed_heap_sound compiled prepared certified plan activated entry signed rooted
    outside arguments decoded idOf ok chipsIn unrolled circuits wideEq lenG merged tablesOk mapsIn
    wideIn wideOk capacity (smallCast hbound) tags codesBound labels shadowBound lookups ids parts
    (characteristic hbits) shaped context req req2 enablesOk tall tallT rows rowsW balanced

/-- `WideStage.wide_heap_sound_insts` over BLS12-381. -/
theorem wide_heap_sound_insts_bls12381 {source : Generic.Source BF} {entries : List String}
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
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat) {insts : List (Chip BF × (Scalar.Circuit.Var → BF))}
    (chipsIn : ∀ p ∈ insts, p.1 ∈ plan.singles)
    (instsHold : ∀ p ∈ insts, (Bridge.lower idOf p.1).Holds p.2)
    (capacity : insts.length ≤ 2 ^ 39)
    {mapCap : Nat → Nat} {roms : List (Nat × Nat)} (widths : (roms.map Prod.fst).Nodup)
    {bound : Nat} (romCaps : ∀ r ∈ roms, r.2 ≤ bound)
    (hbound : bound ≤ 2 ^ 254) (tags : 2 < bound) (lookups : Bridge.lookupCount insts < bound)
    (hbits : cfg.bits ≤ 214)
    (shaped : Shaped.check (Depth.system cfg prepared.system) plan.singles idOf root bound = true)
    (context : (Depth.system cfg prepared.system).checkContext (Erasure.rawROM ⟨[]⟩) root = .ok ())
    (enablesOk : ∀ c ∈ plan.singles, checkEnables bound c = true)
    {mainM mainR : Nat → Nat → Scalar.Circuit.Var → BF}
    (balanced : (insts.map fun p => (Bridge.lower idOf p.1).rowLedger p.2).sum +
      WideStage.stageLedger (WideStage.mapAirs
        ((Depth.system cfg prepared.system).mapClaims.map (encode idOf)) mapCap) mainM +
      WideStage.stageLedger (WideStage.romAirs roms) mainR + Finsupp.single (encode idOf root) 1 = 0) :
    (WideStage.wideRom roms mainR).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (WideStage.wideRom roms mainR)).decode
          specialized.program.enums) heap value result :=
  WideStage.wide_heap_sound_insts compiled prepared certified plan activated entry signed rooted
    outside arguments decoded idOf chipsIn instsHold capacity widths romCaps (smallCast hbound) tags
    lookups (characteristic hbits) shaped context enablesOk balanced

/-- `WideStage.wide_heap_sound` over BLS12-381. -/
theorem wide_heap_sound_bls12381 {source : Generic.Source BF} {entries : List String}
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
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat) {units : List ((Chip BF × Option (Unroll BF)) × Nat)}
    (chipsIn : ∀ u ∈ units, u.1.1 ∈ plan.singles)
    (unrolled : ∀ u ∈ units, unitOk idOf u.1 = true)
    (capacity : WideStage.unitCapRows units ≤ 2 ^ 39)
    {mapCap : Nat → Nat} {roms : List (Nat × Nat)} (widths : (roms.map Prod.fst).Nodup)
    {bound : Nat} (romCaps : ∀ r ∈ roms, r.2 ≤ bound)
    (hbound : bound ≤ 2 ^ 254) (tags : 2 < bound) (lookups : WideStage.unitCapLookups units < bound)
    (hbits : cfg.bits ≤ 214)
    (shaped : Shaped.check (Depth.system cfg prepared.system) plan.singles idOf root bound = true)
    (context : (Depth.system cfg prepared.system).checkContext (Erasure.rawROM ⟨[]⟩) root = .ok ())
    (enablesOk : ∀ c ∈ plan.singles, checkEnables bound c = true)
    {mainU mainM mainR : Nat → Nat → Scalar.Circuit.Var → BF}
    (holds : WideStage.StageHolds (WideStage.unitAirs idOf units) mainU)
    (balanced : WideStage.stageLedger (WideStage.unitAirs idOf units) mainU +
      WideStage.stageLedger (WideStage.mapAirs
        ((Depth.system cfg prepared.system).mapClaims.map (encode idOf)) mapCap) mainM +
      WideStage.stageLedger (WideStage.romAirs roms) mainR + Finsupp.single (encode idOf root) 1 = 0) :
    (WideStage.wideRom roms mainR).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (WideStage.wideRom roms mainR)).decode
          specialized.program.enums) heap value result :=
  WideStage.wide_heap_sound compiled prepared certified plan activated entry signed rooted outside
    arguments decoded idOf chipsIn unrolled capacity widths romCaps (smallCast hbound) tags lookups
    (characteristic hbits) shaped context enablesOk holds balanced

/-- **End-to-end wide stage, single horizontally packed circuit over BLS12-381.**
Packs all unit, map, and ROM tables into ONE circuit `SingleCircuit.pack airs rows`
(`num_circuits == 1`). A single packed main trace satisfying `(pack airs rows).Holds main`
whose single-circuit ledger balances against `Finsupp.single (encode idOf root) 1` implies
`EvalFn` and a valid ROM. -/
theorem wide_single_circuit_sound_bls12381 {source : Generic.Source BF} {entries : List String}
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
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat) {units : List ((Chip BF × Option (Unroll BF)) × Nat)}
    (chipsIn : ∀ u ∈ units, u.1.1 ∈ plan.singles)
    (unrolled : ∀ u ∈ units, unitOk idOf u.1 = true)
    (unitsInBounds : ∀ u ∈ units, SingleCircuit.Circuit.inBounds (Bridge.unitCircuit idOf u.1) = true)
    (capacity : WideStage.unitCapRows units ≤ 2 ^ 39)
    {mapCap : Nat → Nat} {roms : List (Nat × Nat)} (widths : (roms.map Prod.fst).Nodup)
    {bound : Nat} (romCaps : ∀ r ∈ roms, r.2 ≤ bound)
    (hbound : bound ≤ 2 ^ 254) (tags : 2 < bound) (lookups : WideStage.unitCapLookups units < bound)
    (hbits : cfg.bits ≤ 214)
    (shaped : Shaped.check (Depth.system cfg prepared.system) plan.singles idOf root bound = true)
    (context : (Depth.system cfg prepared.system).checkContext (Erasure.rawROM ⟨[]⟩) root = .ok ())
    (enablesOk : ∀ c ∈ plan.singles, checkEnables bound c = true)
    {rows : Nat}
    (unitsTall : ∀ u ∈ units, u.2 ≤ rows)
    (mapsTall : ∀ L ∈ WideStage.mapLengths
      ((Depth.system cfg prepared.system).mapClaims.map (encode idOf)), mapCap L ≤ rows)
    (romsTall : ∀ r ∈ roms, r.2 ≤ rows)
    {main : Nat → Nat → BF}
    (holds : (SingleCircuit.pack (SingleCircuit.wideAirs idOf units
      ((Depth.system cfg prepared.system).mapClaims.map (encode idOf)) mapCap roms) rows).Holds main)
    (balanced : (SingleCircuit.pack (SingleCircuit.wideAirs idOf units
      ((Depth.system cfg prepared.system).mapClaims.map (encode idOf)) mapCap roms) rows).ledger main +
      Finsupp.single (encode idOf root) 1 = 0) :
    let claims := (Depth.system cfg prepared.system).mapClaims.map (encode idOf)
    let airs := SingleCircuit.wideAirs idOf units claims mapCap roms
    let mainR := fun j => SingleCircuit.sliceMain airs main
      (units.length + (WideStage.mapLengths claims).length + j)
    (WideStage.wideRom roms mainR).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (WideStage.wideRom roms mainR)).decode
          specialized.program.enums) heap value result := by
  set claims := (Depth.system cfg prepared.system).mapClaims.map (encode idOf)
  set airs := SingleCircuit.wideAirs idOf units claims mapCap roms
  set mainU := SingleCircuit.sliceMain airs main
  set mainM := fun j => SingleCircuit.sliceMain airs main (units.length + j)
  set mainR := fun j => SingleCircuit.sliceMain airs main
    (units.length + (WideStage.mapLengths claims).length + j)
  have hIn : ∀ a ∈ airs, SingleCircuit.Circuit.inBounds a.circuit = true :=
    SingleCircuit.wideAirs_inBounds unitsInBounds
  have hRows : ∀ a ∈ airs, a.rows ≤ rows :=
    SingleCircuit.wideAirs_rows_le unitsTall mapsTall romsTall
  have hStage : WideStage.StageHolds airs (SingleCircuit.sliceMain airs main) :=
    SingleCircuit.pack_holds_sound hIn hRows holds
  have hUnitsHolds : WideStage.StageHolds (WideStage.unitAirs idOf units) mainU := by
    have h1 := (SingleCircuit.stageHolds_append _ _ _).mp hStage
    exact ((SingleCircuit.stageHolds_append _ _ _).mp h1.1).1
  have hLedger : (SingleCircuit.pack airs rows).ledger main =
      WideStage.stageLedger (WideStage.unitAirs idOf units) mainU +
      WideStage.stageLedger (WideStage.mapAirs claims mapCap) mainM +
      WideStage.stageLedger (WideStage.romAirs roms) mainR := by
    rw [SingleCircuit.pack_ledger_eq main hIn hRows]
    simp only [airs, SingleCircuit.wideAirs, SingleCircuit.stageLedger_append, WideStage.unitAirs,
      WideStage.mapAirs, List.length_append, List.length_map]
    rfl
  rw [hLedger] at balanced
  exact wide_heap_sound_bls12381 compiled prepared certified plan activated entry signed rooted
    outside arguments decoded idOf chipsIn unrolled capacity widths romCaps hbound tags lookups
    hbits shaped context enablesOk hUnitsHolds balanced

/-- **Prover completeness for a horizontally packed wide stage over BLS12-381.** -/
theorem wide_single_circuit_complete_bls12381 {idOf : String → Nat}
    {units : List ((Chip BF × Option (Unroll BF)) × Nat)}
    {claims : List (List BF)} {mapCap : Nat → Nat} {roms : List (Nat × Nat)} {rows : Nat}
    (unitsInBounds : ∀ u ∈ units, SingleCircuit.Circuit.inBounds (Bridge.unitCircuit idOf u.1) = true)
    (unitsTall : ∀ u ∈ units, u.2 ≤ rows)
    (mapsTall : ∀ L ∈ WideStage.mapLengths claims, mapCap L ≤ rows)
    (romsTall : ∀ r ∈ roms, r.2 ≤ rows)
    {mainU mainM mainR : Nat → Nat → Nat → BF}
    (holdsU : WideStage.StageHolds (WideStage.unitAirs idOf units) mainU) :
    let airs := SingleCircuit.wideAirs idOf units claims mapCap roms
    let mains := SingleCircuit.appendMains (units.length + (WideStage.mapLengths claims).length)
      (SingleCircuit.appendMains units.length mainU mainM) mainR
    (SingleCircuit.pack airs rows).Holds (SingleCircuit.packMain airs mains) ∧
      (SingleCircuit.pack airs rows).ledger (SingleCircuit.packMain airs mains) =
        WideStage.stageLedger (WideStage.unitAirs idOf units) mainU +
        WideStage.stageLedger (WideStage.mapAirs claims mapCap) mainM +
        WideStage.stageLedger (WideStage.romAirs roms) mainR := by
  set airs := SingleCircuit.wideAirs idOf units claims mapCap roms
  set mains := SingleCircuit.appendMains (units.length + (WideStage.mapLengths claims).length)
    (SingleCircuit.appendMains units.length mainU mainM) mainR
  have hIn : ∀ a ∈ airs, SingleCircuit.Circuit.inBounds a.circuit = true :=
    SingleCircuit.wideAirs_inBounds unitsInBounds
  have hRows : ∀ a ∈ airs, a.rows ≤ rows :=
    SingleCircuit.wideAirs_rows_le unitsTall mapsTall romsTall
  have hLenU : (WideStage.unitAirs idOf units).length = units.length := by simp [WideStage.unitAirs]
  have hLenM : (WideStage.mapAirs claims mapCap).length = (WideStage.mapLengths claims).length := by
    simp [WideStage.mapAirs]
  have hLenUM : (WideStage.unitAirs idOf units ++ WideStage.mapAirs claims mapCap).length =
      units.length + (WideStage.mapLengths claims).length := by
    rw [List.length_append, hLenU, hLenM]
  have holdsM : WideStage.StageHolds (WideStage.mapAirs claims mapCap) mainM := by
    rintro ⟨a, j⟩ hx i _ p hp
    have hmem := List.fst_mem_of_mem_zipIdx hx
    simp only [WideStage.mapAirs, List.mem_map] at hmem
    obtain ⟨L, _, rfl⟩ := hmem
    cases hp
  have holdsR : WideStage.StageHolds (WideStage.romAirs roms) mainR := by
    rintro ⟨a, j⟩ hx i _ p hp
    have hmem := List.fst_mem_of_mem_zipIdx hx
    simp only [WideStage.romAirs, List.mem_map] at hmem
    obtain ⟨r, _, rfl⟩ := hmem
    cases hp
  have hStage : WideStage.StageHolds airs mains := by
    simp only [airs, SingleCircuit.wideAirs, mains, ← hLenUM]
    rw [SingleCircuit.stageHolds_appendMains]
    refine ⟨?_, holdsR⟩
    rw [← hLenU, SingleCircuit.stageHolds_appendMains]
    exact ⟨holdsU, holdsM⟩
  refine ⟨SingleCircuit.pack_holds_complete hIn hRows hStage, ?_⟩
  rw [SingleCircuit.pack_ledger_packMain mains hIn hRows]
  simp only [airs, SingleCircuit.wideAirs, mains, ← hLenUM]
  rw [SingleCircuit.stageLedger_appendMains, ← hLenU, SingleCircuit.stageLedger_appendMains]

/-- **End-to-end periodic sharded + compact tables, single horizontally packed circuit
over BLS12-381 (`num_circuits == 1`).**
Wraps every shard `k` via `SingleCircuit.shardAir` and every compact table `t` via
`SingleCircuit.compactAir`, packs them horizontally into ONE single circuit
`SingleCircuit.pack (SingleCircuit.compactSystemAirs S H tables HT) rows`, and derives
`EvalFn` and a valid `Periodic.compactRom` directly from `narrow_heap_sound_compact_bls12381`. -/
theorem narrow_compact_single_circuit_sound_bls12381 {source : Generic.Source BF}
    {entries : List String} {specialized : Generic.Specialized source entries}
    (compiled : GenericArtifact specialized) (prepared : Physical.Prepared compiled.artifact)
    {cfg : Depth.Config} (certified : Depth.Certified cfg prepared.system)
    {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id) (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries)
    {args : List (SourceValue BF)} {result : Value BF} {wires : List (WireValue BF)}
    {output : WireValue BF}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Circuit.Message BF}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat) {S : Periodic.Sharded BF} (ok : S.check = true)
    {units : List (Chip BF × Option (Unroll BF))} (chipsIn : ∀ u ∈ units, u.1 ∈ plan.singles)
    (unrolled : ∀ u ∈ units, unitOk idOf u = true)
    {wide : List (Circuit BF)} {groups : List (List (List Nat))}
    (circuits : S.system.circuits = List.zipWith Circuit.mergeBy wide groups)
    (wideEq : wide = units.map (unitCircuit idOf))
    (lenG : groups.length = wide.length)
    (merged : ∀ j (hw : j < wide.length) (hg : j < groups.length), wide[j].checkMerge groups[j] = true)
    {ν : BF → Nat} {tables : List (Periodic.Compact BF)}
    (tablesOk : Periodic.checkTables S ν tables = true)
    (mapsIn : ∀ T ∈ tables, T.checkMap S = true → ∀ q ∈ T.parts,
      q.tag :: q.sub :: q.payload ∈ (Depth.system cfg prepared.system).mapClaims.map (encode idOf))
    (capacity : Bridge.capacityRowsU units S.system ≤ 2 ^ 39)
    {bound : Nat} (hbound : bound ≤ 2 ^ 254) (tags : 3 < bound)
    (codesBound : ∀ e ∈ S.buses, e.2.1 < bound) (labels : Periodic.copyKey S.labelTotal < bound)
    (shadowBound : ∀ k < S.shards.length, ((S.layout k).shadow S.width).bound ≤ bound)
    (lookups : Bridge.capacityLookupsU units S.system < bound) (ids : S.system.instances ≤ bound)
    (parts : (S.system.enumerate S.system.lookupCount).length + 1 +
      (tables.map (·.parts.length)).sum < bound)
    (hbits : cfg.bits ≤ 214)
    (shaped : Shaped.check (Depth.system cfg prepared.system) plan.singles idOf root bound = true)
    (context : (Depth.system cfg prepared.system).checkContext (Erasure.rawROM ⟨[]⟩) root = .ok ())
    (req : (Part.request S.width (encode idOf root)).checkRequest S.system
      (encode idOf root) = true)
    (req2 : S.checkRequest2 (Part.request S.width (encode idOf root)) = true)
    (enablesOk : ∀ c ∈ plan.singles, checkEnables bound c = true)
    {H : Nat → Nat} {HT : Nat → Nat} {rows : Nat}
    (tall : ∀ k < S.shards.length, ((S.layout k).shadow S.width).places.length ≤ H k)
    (tallT : ∀ t T, tables[t]? = some T → T.rows ≤ HT t)
    (shardsFit : ∀ k < S.shards.length, H k ≤ rows)
    (tablesFit : ∀ t < tables.length, HT t ≤ rows)
    {main : Nat → Nat → BF}
    (holds : (SingleCircuit.pack (SingleCircuit.compactSystemAirs S H tables HT) rows).Holds main)
    (balanced : Finsupp.mapDomain trimZeros
      ((SingleCircuit.pack (SingleCircuit.compactSystemAirs S H tables HT) rows).ledger main +
        S.padded2 (Part.request S.width (encode idOf root))) = 0) :
    let airs := SingleCircuit.compactSystemAirs S H tables HT
    let mainT := fun t => SingleCircuit.sliceMain airs main (S.shards.length + t)
    (Periodic.compactRom S tables mainT).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (Periodic.compactRom S tables mainT)).decode
          specialized.program.enums) heap value result := by
  set airs := SingleCircuit.compactSystemAirs S H tables HT
  set mainS := SingleCircuit.sliceMain airs main
  set mainT := fun t => SingleCircuit.sliceMain airs main (S.shards.length + t)
  have hW4 : 4 ≤ S.width := by
    have keyed := (Periodic.Sharded.check_parts ok).1
    have valid' := S.system.valid_of_checkKeyed keyed
    simpa [Periodic.Sharded.system] using valid'.width.1
  have hIn : ∀ a ∈ airs, SingleCircuit.Circuit.inBounds a.circuit = true :=
    SingleCircuit.compactSystemAirs_inBounds hW4 H tables HT
  have hRows : ∀ a ∈ airs, a.rows ≤ rows :=
    SingleCircuit.compactSystemAirs_rows_le shardsFit tablesFit
  have hStage : WideStage.StageHolds airs (SingleCircuit.sliceMain airs main) :=
    SingleCircuit.pack_holds_sound hIn hRows holds
  have hShardRows : ∀ k < S.shards.length, ∀ p < H k,
      Scalar.Circuit.Satisfies (S.circuit k).constraints (S.assign k (mainS k) p) :=
    (SingleCircuit.shardAirs_holds_iff S H mainS).mp ((SingleCircuit.stageHolds_append _ _ _).mp hStage).1
  have hLedger : (SingleCircuit.pack airs rows).ledger main =
      S.ledger H mainS + Periodic.compactLedger S tables HT mainT := by
    rw [SingleCircuit.pack_ledger_eq main hIn hRows]
    simp only [airs, SingleCircuit.compactSystemAirs, SingleCircuit.stageLedger_append]
    have hLen : (SingleCircuit.shardAirs S H).length = S.shards.length := by
      simp [SingleCircuit.shardAirs]
    rw [hLen, SingleCircuit.shardAirs_ledger, SingleCircuit.compactAirs_ledger]
    rfl
  rw [hLedger] at balanced
  exact narrow_heap_sound_compact_bls12381 compiled prepared certified plan activated entry signed
    rooted outside arguments decoded idOf ok chipsIn unrolled circuits wideEq lenG merged tablesOk
    mapsIn capacity hbound tags codesBound labels shadowBound lookups ids parts hbits shaped
    context req req2 enablesOk tall tallT hShardRows balanced

/-! ## Axiom audit guards -/

/-- info: 'Aiur.Tiling.BLS12381.smallCast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms smallCast

/-- info: 'Aiur.Tiling.BLS12381.smallCast_63' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms smallCast_63

/-- info: 'Aiur.Tiling.BLS12381.characteristic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms characteristic

/-- info: 'Aiur.Tiling.BLS12381.narrow_heap_sound_compact_bls12381' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms narrow_heap_sound_compact_bls12381

/-- info: 'Aiur.Tiling.BLS12381.mixed_heap_sound_bls12381' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mixed_heap_sound_bls12381

/-- info: 'Aiur.Tiling.BLS12381.wide_heap_sound_insts_bls12381' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wide_heap_sound_insts_bls12381

/-- info: 'Aiur.Tiling.BLS12381.wide_heap_sound_bls12381' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wide_heap_sound_bls12381

/-- info: 'Aiur.Tiling.BLS12381.wide_single_circuit_sound_bls12381' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wide_single_circuit_sound_bls12381

/-- info: 'Aiur.Tiling.BLS12381.wide_single_circuit_complete_bls12381' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wide_single_circuit_complete_bls12381

/-- info: 'Aiur.Tiling.BLS12381.narrow_compact_single_circuit_sound_bls12381' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms narrow_compact_single_circuit_sound_bls12381

end Aiur.Tiling.BLS12381
