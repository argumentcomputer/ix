import Aiur.Tiling.PeriodicCompact
import Aiur.Tiling.PeriodicMixed
import Aiur.Tiling.WideStage
import Aiur.Library.U32.Goldilocks

/-!
# The tiling soundness theorems over Goldilocks

Corollaries of the end-to-end theorems at `F := ZMod p` with the Goldilocks
prime `p = 2^64 − 2^32 + 1 = 18446744069414584321 ≈ 1.8·10^19 > 2^63`
(primality: `Aiur.Library.U32.Goldilocks.modulus_prime`). The two field
hypotheses of the generic theorems become numeric bounds:

* `small : SmallCast F bound` follows from `hbound : bound ≤ 2 ^ 63`
  (`smallCast_zmod`, as `2^63 < p`);
* `characteristic : ∀ n, 0 < n → n ≤ 2^39 · 2^cfg.bits → (n : F) ≠ 0`
  follows from `hbits : cfg.bits ≤ 24`, since then `n ≤ 2^63 < p`.

BN3's exporter bound `566,935,683,439 ≈ 2^39` is below `2^63`
(`bn3_bound_ok`), so the layout sizes checked for BN254 also fit here.

Remaining hypotheses, per corollary:

* `narrow_heap_sound_compact_goldilocks`: the compiled artifact, certified
  depth system, activation plan and entry call; the sharded layout checks
  (`ok`, `unrolled`, `merged`, the circuit shape equations); the compact table
  checks (`tablesOk`, `mapsIn`); the size bounds `capacity` (rows `≤ 2^39`),
  `tags`, `codesBound`, `labels`, `shadowBound`, `lookups`, `ids`, `parts`
  (all `< bound`), `hbound`, `hbits`; the decidable checks `shaped`,
  `context`, `req`, `req2`, `enablesOk`; and the trace hypotheses `tall`,
  `tallT`, `rows`, `balanced`.
* `mixed_heap_sound_goldilocks`: those of the compact corollary plus the
  wide units' `wideIn`, `wideOk` (`checkMixed`), `rowsW`, with `capacity`,
  `lookups` and `parts` extended by `mixedRows`, `mixedLookups` and
  `mixedPartCount`, and `mixedLedger` in `balanced`.
* `wide_heap_sound_goldilocks`: the same artifact and entry data; the unit
  checks `chipsIn`, `unrolled`; the size bounds `capacity` (rows `≤ 2^39`),
  `widths`, `romCaps`, `tags`, `lookups`, `hbound`, `hbits`; the checks
  `shaped`, `context`, `enablesOk`; and the traces `holds`, `balanced`.
* `wide_heap_sound_insts_goldilocks`: as above, over rows `insts` with
  `instsHold` in place of the unit tables.
-/

namespace Aiur.Tiling.Goldilocks

open Aiur.Circuit
open Aiur.Optimized
open Bridge
open Aiur.Library.U32.Goldilocks (modulus)

local notation "GF" => ZMod modulus

theorem two_pow_63_lt : 2 ^ 63 < modulus := by norm_num

theorem bn3_bound_ok : 566935683439 ≤ 2 ^ 63 := by norm_num

theorem smallCast {bound : Nat} (hbound : bound ≤ 2 ^ 63) : SmallCast GF bound :=
  smallCast_zmod modulus (by have := two_pow_63_lt; omega)

theorem characteristic {cfg : Depth.Config} (hbits : cfg.bits ≤ 24) :
    ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ cfg.bits → (n : GF) ≠ 0 := by
  intro n positive le
  have : 2 ^ 39 * 2 ^ cfg.bits ≤ 2 ^ 39 * 2 ^ 24 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hbits)
  exact Depth.goldilocks_characteristic n positive (le.trans this)

/-- `Periodic.narrow_heap_sound_compact` over Goldilocks. -/
theorem narrow_heap_sound_compact_goldilocks {source : Generic.Source GF} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id) (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries)
    {args : List (SourceValue GF)} {result : Value GF} {wires : List (WireValue GF)}
    {output : WireValue GF}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Circuit.Message GF}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat) {S : Periodic.Sharded GF} (ok : S.check = true)
    {units : List (Chip GF × Option (Unroll GF))} (chipsIn : ∀ u ∈ units, u.1 ∈ plan.singles)
    (unrolled : ∀ u ∈ units, unitOk idOf u = true)
    {wide : List (Circuit GF)} {groups : List (List (List Nat))}
    (circuits : S.system.circuits = List.zipWith Circuit.mergeBy wide groups)
    (wideEq : wide = units.map (unitCircuit idOf))
    (lenG : groups.length = wide.length)
    (merged : ∀ j (hw : j < wide.length) (hg : j < groups.length), wide[j].checkMerge groups[j] = true)
    {ν : GF → Nat} {tables : List (Periodic.Compact GF)}
    (tablesOk : Periodic.checkTables S ν tables = true)
    (mapsIn : ∀ T ∈ tables, T.checkMap S = true → ∀ q ∈ T.parts,
      q.tag :: q.sub :: q.payload ∈ (Depth.system cfg prepared.system).mapClaims.map (encode idOf))
    (capacity : Bridge.capacityRowsU units S.system ≤ 2 ^ 39)
    {bound : Nat} (hbound : bound ≤ 2 ^ 63) (tags : 3 < bound)
    (codesBound : ∀ e ∈ S.buses, e.2.1 < bound) (labels : Periodic.copyKey S.labelTotal < bound)
    (shadowBound : ∀ k < S.shards.length, ((S.layout k).shadow S.width).bound ≤ bound)
    (lookups : Bridge.capacityLookupsU units S.system < bound) (ids : S.system.instances ≤ bound)
    (parts : (S.system.enumerate S.system.lookupCount).length + 1 +
      (tables.map (·.parts.length)).sum < bound)
    (hbits : cfg.bits ≤ 24)
    (shaped : Shaped.check (Depth.system cfg prepared.system) plan.singles idOf root bound = true)
    (context : (Depth.system cfg prepared.system).checkContext (Erasure.rawROM ⟨[]⟩) root = .ok ())
    (req : (Part.request S.width (encode idOf root)).checkRequest S.system
      (encode idOf root) = true)
    (req2 : S.checkRequest2 (Part.request S.width (encode idOf root)) = true)
    (enablesOk : ∀ c ∈ plan.singles, checkEnables bound c = true)
    {H : Nat → Nat} {main : Nat → Nat → Nat → GF} {HT : Nat → Nat} {mainT : Nat → Nat → Nat → GF}
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

/-- `Periodic.mixed_heap_sound` over Goldilocks. -/
theorem mixed_heap_sound_goldilocks {source : Generic.Source GF} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id) (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries)
    {args : List (SourceValue GF)} {result : Value GF} {wires : List (WireValue GF)}
    {output : WireValue GF}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Circuit.Message GF}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat) {S : Periodic.Sharded GF} (ok : S.check = true)
    {units : List (Chip GF × Option (Unroll GF))} (chipsIn : ∀ u ∈ units, u.1 ∈ plan.singles)
    (unrolled : ∀ u ∈ units, unitOk idOf u = true)
    {wide : List (Circuit GF)} {groups : List (List (List Nat))}
    (circuits : S.system.circuits = List.zipWith Circuit.mergeBy wide groups)
    (wideEq : wide = units.map (unitCircuit idOf))
    (lenG : groups.length = wide.length)
    (merged : ∀ j (hw : j < wide.length) (hg : j < groups.length), wide[j].checkMerge groups[j] = true)
    {ν : GF → Nat} {tables : List (Periodic.Compact GF)}
    (tablesOk : Periodic.checkTables S ν tables = true)
    (mapsIn : ∀ T ∈ tables, T.checkMap S = true → ∀ q ∈ T.parts,
      q.tag :: q.sub :: q.payload ∈ (Depth.system cfg prepared.system).mapClaims.map (encode idOf))
    {wideUnits : List (Periodic.WideUnit GF)} (wideIn : ∀ u ∈ wideUnits, u.chip ∈ plan.singles)
    (wideOk : Periodic.checkMixed S idOf ν tables wideUnits = true)
    (capacity : Bridge.capacityRowsU units S.system + Periodic.mixedRows wideUnits ≤ 2 ^ 39)
    {bound : Nat} (hbound : bound ≤ 2 ^ 63) (tags : 3 < bound)
    (codesBound : ∀ e ∈ S.buses, e.2.1 < bound) (labels : Periodic.copyKey S.labelTotal < bound)
    (shadowBound : ∀ k < S.shards.length, ((S.layout k).shadow S.width).bound ≤ bound)
    (lookups : Bridge.capacityLookupsU units S.system + Periodic.mixedLookups wideUnits < bound)
    (ids : S.system.instances ≤ bound)
    (parts : (S.system.enumerate S.system.lookupCount).length + 1 +
      (tables.map (·.parts.length)).sum + Periodic.mixedPartCount wideUnits < bound)
    (hbits : cfg.bits ≤ 24)
    (shaped : Shaped.check (Depth.system cfg prepared.system) plan.singles idOf root bound = true)
    (context : (Depth.system cfg prepared.system).checkContext (Erasure.rawROM ⟨[]⟩) root = .ok ())
    (req : (Part.request S.width (encode idOf root)).checkRequest S.system
      (encode idOf root) = true)
    (req2 : S.checkRequest2 (Part.request S.width (encode idOf root)) = true)
    (enablesOk : ∀ c ∈ plan.singles, checkEnables bound c = true)
    {H : Nat → Nat} {main : Nat → Nat → Nat → GF} {HT : Nat → Nat} {mainT : Nat → Nat → Nat → GF}
    {mainW : Nat → Nat → Nat → GF}
    (tall : ∀ k < S.shards.length, ((S.layout k).shadow S.width).places.length ≤ H k)
    (tallT : ∀ t T, tables[t]? = some T → T.rows ≤ HT t)
    (rows : ∀ k < S.shards.length, ∀ p < H k,
      Scalar.Circuit.Satisfies (S.circuit k).constraints (S.assign k (main k) p))
    (rowsW : ∀ (t : Nat) (u : Periodic.WideUnit GF), wideUnits[t]? = some u → ∀ r < u.rows,
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

/-- `WideStage.wide_heap_sound_insts` over Goldilocks. -/
theorem wide_heap_sound_insts_goldilocks {source : Generic.Source GF} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id) (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries)
    {args : List (SourceValue GF)} {result : Value GF} {wires : List (WireValue GF)}
    {output : WireValue GF}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Circuit.Message GF}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat) {insts : List (Chip GF × (Scalar.Circuit.Var → GF))}
    (chipsIn : ∀ p ∈ insts, p.1 ∈ plan.singles)
    (instsHold : ∀ p ∈ insts, (Bridge.lower idOf p.1).Holds p.2)
    (capacity : insts.length ≤ 2 ^ 39)
    {mapCap : Nat → Nat} {roms : List (Nat × Nat)} (widths : (roms.map Prod.fst).Nodup)
    {bound : Nat} (romCaps : ∀ r ∈ roms, r.2 ≤ bound)
    (hbound : bound ≤ 2 ^ 63) (tags : 2 < bound) (lookups : Bridge.lookupCount insts < bound)
    (hbits : cfg.bits ≤ 24)
    (shaped : Shaped.check (Depth.system cfg prepared.system) plan.singles idOf root bound = true)
    (context : (Depth.system cfg prepared.system).checkContext (Erasure.rawROM ⟨[]⟩) root = .ok ())
    (enablesOk : ∀ c ∈ plan.singles, checkEnables bound c = true)
    {mainM mainR : Nat → Nat → Scalar.Circuit.Var → GF}
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

/-- `WideStage.wide_heap_sound` over Goldilocks. -/
theorem wide_heap_sound_goldilocks {source : Generic.Source GF} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id) (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries)
    {args : List (SourceValue GF)} {result : Value GF} {wires : List (WireValue GF)}
    {output : WireValue GF}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Circuit.Message GF}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat) {units : List ((Chip GF × Option (Unroll GF)) × Nat)}
    (chipsIn : ∀ u ∈ units, u.1.1 ∈ plan.singles)
    (unrolled : ∀ u ∈ units, unitOk idOf u.1 = true)
    (capacity : WideStage.unitCapRows units ≤ 2 ^ 39)
    {mapCap : Nat → Nat} {roms : List (Nat × Nat)} (widths : (roms.map Prod.fst).Nodup)
    {bound : Nat} (romCaps : ∀ r ∈ roms, r.2 ≤ bound)
    (hbound : bound ≤ 2 ^ 63) (tags : 2 < bound) (lookups : WideStage.unitCapLookups units < bound)
    (hbits : cfg.bits ≤ 24)
    (shaped : Shaped.check (Depth.system cfg prepared.system) plan.singles idOf root bound = true)
    (context : (Depth.system cfg prepared.system).checkContext (Erasure.rawROM ⟨[]⟩) root = .ok ())
    (enablesOk : ∀ c ∈ plan.singles, checkEnables bound c = true)
    {mainU mainM mainR : Nat → Nat → Scalar.Circuit.Var → GF}
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

end Aiur.Tiling.Goldilocks
