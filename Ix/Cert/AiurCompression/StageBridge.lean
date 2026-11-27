import Aiur.Tiling.Claims
import Aiur.Tiling.Grouped
import Aiur.Plonk.SharedSound
import Ix.Cert.AiurCompression.ProgramPins
import Ix.Cert.AiurCompression.StatementBinding
import Ix.Cert.AiurCompression.DeferredFold
import Ix.Cert.Aggr.EndToEnd

/-! # Stage Compilation Soundness Wrappers & Typed Functional-Refinement / TCB Bridges

Directly instantiates the proved Lean compiler, tiling, grouped-wide, and shared-map PLONK
soundness theorems from `Aiur.Tiling` and `Aiur.Plonk` for each of the four Aiur compression
stages, and isolates every remaining open functional-refinement and cryptographic-extraction
bridge as an explicit typed hypothesis structure (NEVER a Lean `axiom` or `sorry`):

1. **Stage 1 (`CompressWrap::verify_root` — Goldilocks Wide STARK):**
   `GoldilocksWideStageWitness.eval_sound` invokes
   `Aiur.Tiling.Claims.wide_heap_sound_goldilocks_exported`.
2. **Stage 2 (`CompressGL::verify_root` — Emulated-Goldilocks Grouped Wide KZG):**
   - BN254: `Bn254GroupedWideStageWitness.eval_sound` invokes
     `Aiur.Tiling.Claims.grouped_heap_sound_bn254_exported`.
   - Generic prime field (including `BLS12381Fr`):
     `FieldGroupedSharedStageWitness.eval_sound` invokes
     `Aiur.Tiling.Grouped.grouped_heap_sound_shared_compiled`.
3. **Stage 3 (`CompressNarrowFixed::step_v1` — Tiled Narrow Compact-Table KZG):**
   `NarrowCompactStageWitness.eval_sound` (polymorphic over any field `F`, instantiated at both
   `BN254Fr` and `BLS12381Fr`) invokes `Aiur.Tiling.Claims.narrow_heap_sound_compact_exported`.
4. **Stage 4 (`CompressFinalNarrow::verify_accumulator_v1` — Shared-Map PLONK SCS):**
   - BN254: `PlonkSharedTerminalWitness.eval_sound` invokes `Aiur.Plonk.plonk_shared_heap_sound`.
   - Generic prime field (including `BLS12381Fr`): reuses
     `FieldGroupedSharedStageWitness.eval_sound` (`grouped_heap_sound_shared_compiled` at
     `groups = []`, matching `Aiur.Plonk.SharedSound`'s shared-table layout).
5. **Typed TCB-Gap Records (`Bn254AiurCompressionTcbGaps`, `Bls12381AiurCompressionTcbGaps`):**
   Explicitly separate:
   - the 4 program functional-refinement contracts (`CompressFinal`, `CompressNarrow`,
     `CompressGL`, `CompressWrap`),
   - the 5 cryptographic extraction bridges (`Outer → FinalSCS`, `NarrowKZG → Tiling`,
     `GLKZG → GroupedWide`, `WrapFRI → WideGoldilocks`, `RootFRI → ix_aggr`), and
   - external cryptographic assumptions (SRS / AGM / key-writer faithfulness).

   **Both records have no inhabitant** (`Bn254AiurCompressionTcbGaps.inconsistent`,
   `Bls12381AiurCompressionTcbGaps.inconsistent`): their bridges quantify over every statement and
   every free result record rather than over the execution at hand. They are kept only as the record
   of the withdrawn end-to-end composition and are a hypothesis of no theorem.

Zero `sorry`, zero custom `axiom`, zero `native_decide`, zero `bv_decide`.
-/

namespace Ix.Cert.AiurCompression

open Aiur Aiur.Circuit Aiur.Optimized Aiur.Tiling Aiur.Tiling.Bridge Aiur.Tiling.Grouped
open Aiur.Plonk
open Ix.Cert.Compression.Foreign
open Ix.Cert.Compression.OuterRelation
open Ix.Cert.Compression.Bls12381.Field
open Ix.Cert.Compression.Bls12381.OuterRelation
open Ix.Cert.Compression.Bls12381.EndToEnd
open Ix.Cert.MultiStark
open Ix.Cert.Aggr

/-! ## 1. Canonical Aiur `SourceValue` Argument Encodings for All 4 Compression Stages -/

/-- Encode an 8-word `u32` digest as an Aiur `[Field; 8]` tuple value over field `F`
(matching `Ix.Cert.MultiStarkRefinement.digest8SourceValue`). -/
def u32Array8SourceValue (F : Type) [Field F] (ws : List Nat) : Aiur.SourceValue F :=
  .tuple (ws.map fun w => .field (w : F))

/-- Encode the 8 reserved zero words `[0; 8]` for `CompressWrap::verify_root` and
`CompressGL::verify_root`. -/
def zeroArray8SourceValue (F : Type) [Field F] : Aiur.SourceValue F :=
  .tuple (List.replicate 8 (.field (0 : F)))

/-- Entry arguments of `CompressWrap::verify_root([0; 8], statement_digest)` over Goldilocks. -/
def compressWrapArgs (stmtWords : List Nat) : List (Aiur.SourceValue _root_.MultiStark.F) :=
  [zeroArray8SourceValue _root_.MultiStark.F, u32Array8SourceValue _root_.MultiStark.F stmtWords]

/-- Entry arguments of `CompressGL::verify_root([0; 8], statement_digest)` over field `F`. -/
def compressGLArgs (F : Type) [Field F] (stmtWords : List Nat) : List (Aiur.SourceValue F) :=
  [zeroArray8SourceValue F, u32Array8SourceValue F stmtWords]

/-- Entry arguments of `CompressNarrowFixed::step_v1(policy_digest, stage, statement)` over `F`. -/
def compressNarrowArgs (F : Type) [Field F]
    (policyWords : List Nat) (stage : Nat) (stmtWords : List Nat) : List (Aiur.SourceValue F) :=
  [u32Array8SourceValue F policyWords, .field (stage : F), u32Array8SourceValue F stmtWords]

/-- Entry arguments of `CompressFinalNarrow::verify_accumulator_v1(statement_low, statement_high)`
over field `F`. -/
def compressFinalArgs (F : Type) [Field F] (stmtLow stmtHigh : Nat) : List (Aiur.SourceValue F) :=
  [.field (stmtLow : F), .field (stmtHigh : F)]

/-! ## 2. Direct Wrappers Around the Proved `Aiur.Tiling` & `Aiur.Plonk` Soundness Theorems -/

/-- **Stage 1 (`CompressWrap`) Goldilocks Wide-Export Witness:**
Packages every static and trace hypothesis of `Aiur.Tiling.Claims.wide_heap_sound_goldilocks_exported`. -/
structure GoldilocksWideStageWitness
    (source : Generic.Source _root_.MultiStark.F) (entries : List String)
    (name : String) (args : List (Aiur.SourceValue _root_.MultiStark.F)) where
  specialized : Generic.Specialized source entries
  compiled : GenericArtifact specialized
  prepared : Physical.Prepared compiled.artifact
  cfg : Depth.Config
  certified : Depth.Certified cfg prepared.system
  id : String → Except String Nat
  plan : Grouping.Plan (Depth.system cfg prepared.system) id
  activated : plan.WellFormedActivation
  entry : name ∈ entries
  result : Aiur.Value _root_.MultiStark.F
  wires : List (Aiur.WireValue _root_.MultiStark.F)
  output : Aiur.WireValue _root_.MultiStark.F
  signed : Erasure.Signed compiled.system ⟨name, wires, output⟩
  root : Circuit.Message _root_.MultiStark.F
  rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩
  outside : root.channel ∉ cfg.names
  entryPlain : cfg.recursive name = false
  arguments : DecodesValues specialized.program.enums wires (entryValues args)
  decoded : output.decode specialized.program.enums = some result
  idOf : String → Nat
  units : List ((Chip _root_.MultiStark.F × Option (Unroll _root_.MultiStark.F)) × Nat)
  chipsIn : ∀ u ∈ units, u.1.1 ∈ plan.singles
  unrolled : ∀ u ∈ units, Bridge.unitOk idOf u.1 = true
  capacity : WideStage.unitCapRows units ≤ 2 ^ 39
  mapCap : Nat → Nat
  roms : List (Nat × Nat)
  widths : (roms.map Prod.fst).Nodup
  bound : Nat
  romCaps : ∀ r ∈ roms, r.2 ≤ bound
  hbound : bound ≤ 2 ^ 63
  tags : 2 < bound
  lookups : WideStage.unitCapLookups units < bound
  hbits : cfg.bits ≤ 24
  callables : List String
  hid : idOf = callables.idxOf
  ids : Claims.ExportedIds compiled prepared cfg callables bound root
  enablesOk : ∀ c ∈ plan.singles, Bridge.checkEnables bound c = true
  mainU : Nat → Nat → Scalar.Circuit.Var → _root_.MultiStark.F
  mainM : Nat → Nat → Scalar.Circuit.Var → _root_.MultiStark.F
  mainR : Nat → Nat → Scalar.Circuit.Var → _root_.MultiStark.F
  holds : WideStage.StageHolds (WideStage.unitAirs idOf units) mainU
  balanced : WideStage.stageLedger (WideStage.unitAirs idOf units) mainU +
    WideStage.stageLedger (WideStage.mapAirs
      ((Depth.system cfg prepared.system).mapClaims.map (Bridge.encode idOf)) mapCap) mainM +
    WideStage.stageLedger (WideStage.romAirs roms) mainR +
    Finsupp.single (Bridge.encode idOf root) 1 = 0

/-- Direct soundness extraction for Stage 1 (`CompressWrap`) via
`Aiur.Tiling.Claims.wide_heap_sound_goldilocks_exported`. -/
theorem GoldilocksWideStageWitness.eval_sound
    {source : Generic.Source _root_.MultiStark.F} {entries : List String}
    {name : String} {args : List (Aiur.SourceValue _root_.MultiStark.F)}
    (w : GoldilocksWideStageWitness source entries name args) :
    (WideStage.wideRom w.roms w.mainR).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM w.compiled.system (WideStage.wideRom w.roms w.mainR)).decode
          w.specialized.program.enums) heap value w.result :=
  Aiur.Tiling.Claims.wide_heap_sound_goldilocks_exported
    w.compiled w.prepared w.certified w.plan w.activated w.entry w.signed w.rooted w.outside
    w.entryPlain w.arguments w.decoded w.idOf w.chipsIn w.unrolled w.capacity w.widths
    w.romCaps w.hbound w.tags w.lookups w.hbits w.callables w.hid w.ids w.enablesOk
    w.holds w.balanced

/-- **Stage 2 (`CompressGL`, BN254) Grouped Wide-Export Witness:**
Packages every static and trace hypothesis of `Aiur.Tiling.Claims.grouped_heap_sound_bn254_exported`. -/
structure Bn254GroupedWideStageWitness
    (source : Generic.Source BN254Fr) (entries : List String)
    (name : String) (args : List (Aiur.SourceValue BN254Fr)) where
  specialized : Generic.Specialized source entries
  compiled : GenericArtifact specialized
  prepared : Physical.Prepared compiled.artifact
  cfg : Depth.Config
  certified : Depth.Certified cfg prepared.system
  id : String → Except String Nat
  plan : Grouping.Plan (Depth.system cfg prepared.system) id
  activated : plan.WellFormedActivation
  entry : name ∈ entries
  result : Aiur.Value BN254Fr
  wires : List (Aiur.WireValue BN254Fr)
  output : Aiur.WireValue BN254Fr
  signed : Erasure.Signed compiled.system ⟨name, wires, output⟩
  root : Circuit.Message BN254Fr
  rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩
  outside : root.channel ∉ cfg.names
  entryPlain : cfg.recursive name = false
  arguments : DecodesValues specialized.program.enums wires (entryValues args)
  decoded : output.decode specialized.program.enums = some result
  idOf : String → Nat
  idOk : ∀ x n, id x = .ok n → n = idOf x
  names : (circuitNames plan).Nodup
  units : List ((Chip BN254Fr × Option (Unroll BN254Fr)) × Nat)
  chipsIn : ∀ u ∈ units, u.1.1 ∈ plan.singles
  unrolled : ∀ u ∈ units, Bridge.unitOk idOf u.1 = true
  groups : List (Grouping.Packed BN254Fr id × Nat)
  groupsIn : ∀ x ∈ groups, x.1 ∈ plan.groups
  capacity : WideStage.unitCapRows units + (groups.map (·.2)).sum ≤ 2 ^ 39
  mapCap : Nat → Nat
  roms : List (Nat × Nat)
  widths : (roms.map Prod.fst).Nodup
  bound : Nat
  romCaps : ∀ r ∈ roms, r.2 ≤ bound
  romWidths : ∀ r ∈ roms, r.1 < bound
  hbound : bound ≤ 2 ^ 63
  tags : 2 < bound
  lookups : WideStage.unitCapLookups units + (groups.map fun x => x.2 * groupCost x.1).sum < bound
  hbits : cfg.bits ≤ 24
  callables : List String
  hid : idOf = callables.idxOf
  ids : Claims.ExportedIds compiled prepared cfg callables bound root
  enablesOk : ∀ c ∈ allChips plan, Bridge.checkEnables bound c = true
  memWidth : ∀ c ∈ allChips plan, ∀ m ∈ c.memory, m.value.words.length < bound
  mainU : Nat → Nat → Scalar.Circuit.Var → BN254Fr
  mainG : Nat → Nat → Scalar.Circuit.Var → BN254Fr
  mainM : Nat → Nat → Scalar.Circuit.Var → BN254Fr
  mainR : Nat → Nat → Scalar.Circuit.Var → BN254Fr
  holds : WideStage.StageHolds (WideStage.unitAirs idOf units) mainU
  holdsG : WideStage.StageHolds (groupAirs groups) mainG
  balanced : Finsupp.mapDomain trimZeros
    (WideStage.stageLedger (WideStage.unitAirs idOf units) mainU +
      WideStage.stageLedger (groupAirs groups) mainG +
      WideStage.stageLedger (WideStage.mapAirs
        ((Depth.system cfg prepared.system).mapClaims.map (Bridge.encode idOf)) mapCap) mainM +
      WideStage.stageLedger (WideStage.romAirs roms) mainR +
      Finsupp.single (Bridge.encode idOf root) 1) = 0

/-- Direct soundness extraction for Stage 2 (`CompressGL` over BN254) via
`Aiur.Tiling.Claims.grouped_heap_sound_bn254_exported`. -/
theorem Bn254GroupedWideStageWitness.eval_sound
    {source : Generic.Source BN254Fr} {entries : List String}
    {name : String} {args : List (Aiur.SourceValue BN254Fr)}
    (w : Bn254GroupedWideStageWitness source entries name args) :
    (WideStage.wideRom w.roms w.mainR).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM w.compiled.system (WideStage.wideRom w.roms w.mainR)).decode
          w.specialized.program.enums) heap value w.result :=
  Aiur.Tiling.Claims.grouped_heap_sound_bn254_exported
    w.compiled w.prepared w.certified w.plan w.activated w.entry w.signed w.rooted w.outside
    w.entryPlain w.arguments w.decoded w.idOf w.idOk w.names w.chipsIn w.unrolled w.groupsIn
    w.capacity w.widths w.romCaps w.romWidths w.hbound w.tags w.lookups w.hbits w.callables
    w.hid w.ids w.enablesOk w.memWidth w.holds w.holdsG w.balanced

/-- **Field-Polymorphic Grouped Shared-Map Stage Witness (instantiated at `BLS12381Fr`):**
Packages every static and trace hypothesis of `Aiur.Tiling.Grouped.grouped_heap_sound_shared_compiled`,
covering both `CompressGL` and shared-map `CompressFinalNarrow` over `BLS12381Fr`. -/
structure FieldGroupedSharedStageWitness (F : Type) [Field F] [DecidableEq F]
    (source : Generic.Source F) (entries : List String)
    (name : String) (args : List (Aiur.SourceValue F)) where
  specialized : Generic.Specialized source entries
  compiled : GenericArtifact specialized
  prepared : Physical.Prepared compiled.artifact
  cfg : Depth.Config
  certified : Depth.Certified cfg prepared.system
  id : String → Except String Nat
  plan : Grouping.Plan (Depth.system cfg prepared.system) id
  activated : plan.WellFormedActivation
  entry : name ∈ entries
  result : Aiur.Value F
  wires : List (Aiur.WireValue F)
  output : Aiur.WireValue F
  signed : Erasure.Signed compiled.system ⟨name, wires, output⟩
  root : Circuit.Message F
  rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩
  outside : root.channel ∉ cfg.names
  entryPlain : cfg.recursive name = false
  arguments : DecodesValues specialized.program.enums wires (entryValues args)
  decoded : output.decode specialized.program.enums = some result
  idOf : String → Nat
  idOk : ∀ x n, id x = .ok n → n = idOf x
  names : (circuitNames plan).Nodup
  units : List ((Chip F × Option (Unroll F)) × Nat)
  chipsIn : ∀ u ∈ units, u.1.1 ∈ plan.singles
  unrolled : ∀ u ∈ units, Bridge.unitOk idOf u.1 = true
  groups : List (Grouping.Packed F id × Nat)
  groupsIn : ∀ x ∈ groups, x.1 ∈ plan.groups
  capacity : WideStage.unitCapRows units + (groups.map (·.2)).sum ≤ 2 ^ 39
  shared : List (SharedTable F)
  sharedOk : ∀ T ∈ shared,
    T.check ((Depth.system cfg prepared.system).mapClaims.map (Bridge.encode idOf)) = true
  roms : List (Nat × Nat)
  widths : (roms.map Prod.fst).Nodup
  bound : Nat
  romCaps : ∀ r ∈ roms, r.2 ≤ bound
  romWidths : ∀ r ∈ roms, r.1 < bound
  small : SmallCast F bound
  tags : 2 < bound
  lookups : WideStage.unitCapLookups units + (groups.map fun x => x.2 * groupCost x.1).sum < bound
  characteristic : ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ cfg.bits → (n : F) ≠ 0
  chanIds : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) (allChips plan) root,
    ∀ y ∈ Bridge.channels (Depth.system cfg prepared.system) (allChips plan) root,
    idOf x = idOf y → x = y
  chanBound : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) (allChips plan) root,
    idOf x < bound
  enablesOk : ∀ c ∈ allChips plan, Bridge.checkEnables bound c = true
  memWidth : ∀ c ∈ allChips plan, ∀ m ∈ c.memory, m.value.words.length < bound
  mainU : Nat → Nat → Scalar.Circuit.Var → F
  mainG : Nat → Nat → Scalar.Circuit.Var → F
  mainM : Nat → Nat → Scalar.Circuit.Var → F
  mainR : Nat → Nat → Scalar.Circuit.Var → F
  holds : WideStage.StageHolds (WideStage.unitAirs idOf units) mainU
  holdsG : WideStage.StageHolds (groupAirs groups) mainG
  balanced : Finsupp.mapDomain trimZeros
    (WideStage.stageLedger (WideStage.unitAirs idOf units) mainU +
      WideStage.stageLedger (groupAirs groups) mainG +
      WideStage.stageLedger (shared.map SharedTable.air) mainM +
      WideStage.stageLedger (WideStage.romAirs roms) mainR +
      Finsupp.single (Bridge.encode idOf root) 1) = 0

/-- Direct soundness extraction for grouped/shared stages over any prime field `F`
(including `BLS12381Fr`) via `Aiur.Tiling.Grouped.grouped_heap_sound_shared_compiled`. -/
theorem FieldGroupedSharedStageWitness.eval_sound {F : Type} [Field F] [DecidableEq F]
    {source : Generic.Source F} {entries : List String}
    {name : String} {args : List (Aiur.SourceValue F)}
    (w : FieldGroupedSharedStageWitness F source entries name args) :
    (WideStage.wideRom w.roms w.mainR).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM w.compiled.system (WideStage.wideRom w.roms w.mainR)).decode
          w.specialized.program.enums) heap value w.result :=
  Aiur.Tiling.Grouped.grouped_heap_sound_shared_compiled
    w.compiled w.prepared w.certified w.plan w.activated w.entry w.signed w.rooted w.outside
    w.entryPlain w.arguments w.decoded w.idOf w.idOk w.names w.chipsIn w.unrolled w.groupsIn
    w.capacity w.sharedOk w.widths w.romCaps w.romWidths w.small w.tags w.lookups
    w.characteristic w.chanIds w.chanBound w.enablesOk w.memWidth w.holds w.holdsG w.balanced

/-- **Stage 3 (`CompressNarrowFixed`) Tiled Narrow Compact-Table Witness (`tiling_export2`):**
Polymorphic over any field `F` (instantiated at BOTH `BN254Fr` and `BLS12381Fr`), packaging
every static and trace hypothesis of `Aiur.Tiling.Claims.narrow_heap_sound_compact_exported`. -/
structure NarrowCompactStageWitness (F : Type) [Field F] [DecidableEq F]
    (source : Generic.Source F) (entries : List String)
    (name : String) (args : List (Aiur.SourceValue F)) where
  specialized : Generic.Specialized source entries
  compiled : GenericArtifact specialized
  prepared : Physical.Prepared compiled.artifact
  cfg : Depth.Config
  certified : Depth.Certified cfg prepared.system
  id : String → Except String Nat
  plan : Grouping.Plan (Depth.system cfg prepared.system) id
  activated : plan.WellFormedActivation
  entry : name ∈ entries
  result : Aiur.Value F
  wires : List (Aiur.WireValue F)
  output : Aiur.WireValue F
  signed : Erasure.Signed compiled.system ⟨name, wires, output⟩
  root : Circuit.Message F
  rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩
  outside : root.channel ∉ cfg.names
  entryPlain : cfg.recursive name = false
  arguments : DecodesValues specialized.program.enums wires (entryValues args)
  decoded : output.decode specialized.program.enums = some result
  idOf : String → Nat
  S : Periodic.Sharded F
  ok : S.check = true
  units : List (Chip F × Option (Unroll F))
  chipsIn : ∀ u ∈ units, u.1 ∈ plan.singles
  unrolled : ∀ u ∈ units, Bridge.unitOk idOf u = true
  wide : List (Tiling.Circuit F)
  groups : List (List (List Nat))
  circuits : S.system.circuits = List.zipWith Tiling.Circuit.mergeBy wide groups
  wideEq : wide = units.map (Bridge.unitCircuit idOf)
  lenG : groups.length = wide.length
  merged : ∀ j (hw : j < wide.length) (hg : j < groups.length), wide[j].checkMerge groups[j] = true
  ν : F → Nat
  tables : List (Periodic.Compact F)
  tablesOk : Periodic.checkTables S ν tables = true
  mapsIn : ∀ T ∈ tables, T.checkMap S = true → ∀ q ∈ T.parts,
    q.tag :: q.sub :: q.payload ∈ (Depth.system cfg prepared.system).mapClaims.map (Bridge.encode idOf)
  capacity : Bridge.capacityRowsU units S.system ≤ 2 ^ 39
  bound : Nat
  small : SmallCast F bound
  tags : 3 < bound
  codesBound : ∀ e ∈ S.buses, e.2.1 < bound
  labels : Periodic.copyKey S.labelTotal < bound
  shadowBound : ∀ k < S.shards.length, ((S.layout k).shadow S.width).bound ≤ bound
  lookups : Bridge.capacityLookupsU units S.system < bound
  idsBound : S.system.instances ≤ bound
  parts : (S.system.enumerate S.system.lookupCount).length + 1 +
    (tables.map (·.parts.length)).sum < bound
  characteristic : ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ cfg.bits → (n : F) ≠ 0
  req : (Part.request S.width (Bridge.encode idOf root)).checkRequest S.system
    (Bridge.encode idOf root) = true
  req2 : S.checkRequest2 (Part.request S.width (Bridge.encode idOf root)) = true
  callables : List String
  hid : idOf = callables.idxOf
  exportedIds : Claims.ExportedIds compiled prepared cfg callables bound root
  enablesOk : ∀ c ∈ plan.singles, Bridge.checkEnables bound c = true
  H : Nat → Nat
  main : Nat → Nat → Nat → F
  HT : Nat → Nat
  mainT : Nat → Nat → Nat → F
  tall : ∀ k < S.shards.length, ((S.layout k).shadow S.width).places.length ≤ H k
  tallT : ∀ t T, tables[t]? = some T → T.rows ≤ HT t
  rows : ∀ k < S.shards.length, ∀ p < H k,
    Scalar.Circuit.Satisfies (S.circuit k).constraints (S.assign k (main k) p)
  balanced : Finsupp.mapDomain trimZeros
    (S.ledger H main + Periodic.compactLedger S tables HT mainT +
      S.padded2 (Part.request S.width (Bridge.encode idOf root))) = 0

/-- Direct soundness extraction for Stage 3 (`CompressNarrowFixed`) via
`Aiur.Tiling.Claims.narrow_heap_sound_compact_exported` (built on `Aiur.Tiling.Sound`). -/
theorem NarrowCompactStageWitness.eval_sound {F : Type} [Field F] [DecidableEq F]
    {source : Generic.Source F} {entries : List String}
    {name : String} {args : List (Aiur.SourceValue F)}
    (w : NarrowCompactStageWitness F source entries name args) :
    (Periodic.compactRom w.S w.tables w.mainT).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM w.compiled.system
          (Periodic.compactRom w.S w.tables w.mainT)).decode
          w.specialized.program.enums) heap value w.result :=
  Aiur.Tiling.Claims.narrow_heap_sound_compact_exported
    w.compiled w.prepared w.certified w.plan w.activated w.entry w.signed w.rooted w.outside
    w.entryPlain w.arguments w.decoded w.idOf w.ok w.chipsIn w.unrolled w.circuits w.wideEq
    w.lenG w.merged w.tablesOk w.mapsIn w.capacity w.small w.tags w.codesBound w.labels
    w.shadowBound w.lookups w.idsBound w.parts w.characteristic w.req w.req2 w.callables
    w.hid w.exportedIds w.enablesOk w.tall w.tallT w.rows w.balanced

/-- **Stage 4 (`CompressFinalNarrow`, BN254) Shared-Map PLONK SCS Witness (`plonk_export`):**
Packages every static and constraint-system hypothesis of `Aiur.Plonk.plonk_shared_heap_sound`
(built on `Aiur.Plonk.Sound`). -/
structure PlonkSharedTerminalWitness
    (source : Generic.Source BN254Fr) (entries : List String)
    (name : String) (args : List (Aiur.SourceValue BN254Fr)) where
  specialized : Generic.Specialized source entries
  compiled : GenericArtifact specialized
  prepared : Physical.Prepared compiled.artifact
  cfg : Depth.Config
  certified : Depth.Certified cfg prepared.system
  id : String → Except String Nat
  plan : Grouping.Plan (Depth.system cfg prepared.system) id
  activated : plan.WellFormedActivation
  entry : name ∈ entries
  result : Aiur.Value BN254Fr
  wires : List (Aiur.WireValue BN254Fr)
  output : Aiur.WireValue BN254Fr
  signed : Erasure.Signed compiled.system ⟨name, wires, output⟩
  root : Circuit.Message BN254Fr
  rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩
  outside : root.channel ∉ cfg.names
  entryPlain : cfg.recursive name = false
  arguments : DecodesValues specialized.program.enums wires (entryValues args)
  decoded : output.decode specialized.program.enums = some result
  idOf : String → Nat
  idOk : ∀ x n, id x = .ok n → n = idOf x
  names : (circuitNames plan).Nodup
  units : List ((Chip BN254Fr × Option (Unroll BN254Fr)) × Nat)
  chipsIn : ∀ u ∈ units, u.1.1 ∈ plan.singles
  unrolled : ∀ u ∈ units, Bridge.unitOk idOf u.1 = true
  capacity : WideStage.unitCapRows units ≤ 2 ^ 39
  shared : List (SharedTable BN254Fr)
  sharedOk : ∀ T ∈ shared,
    T.check ((Depth.system cfg prepared.system).mapClaims.map (Bridge.encode idOf)) = true
  roms : List (Nat × Nat)
  widths : (roms.map Prod.fst).Nodup
  bound : Nat
  romCaps : ∀ r ∈ roms, r.2 ≤ bound
  romWidths : ∀ r ∈ roms, r.1 < bound
  small : SmallCast BN254Fr bound
  tags : 2 < bound
  lookups : WideStage.unitCapLookups units < bound
  characteristic : ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ cfg.bits → (n : BN254Fr) ≠ 0
  chanIds : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) (allChips plan) root,
    ∀ y ∈ Bridge.channels (Depth.system cfg prepared.system) (allChips plan) root,
    idOf x = idOf y → x = y
  chanBound : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) (allChips plan) root,
    idOf x < bound
  enablesOk : ∀ c ∈ allChips plan, Bridge.checkEnables bound c = true
  memWidth : ∀ c ∈ allChips plan, ∀ m ∈ c.memory, m.value.words.length < bound
  airs : List (WideStage.Air BN254Fr)
  hairs : airs = WideStage.unitAirs idOf units ++ shared.map SharedTable.air ++ WideStage.romAirs roms
  k : BN254Fr
  n : Nat
  P : Lower.Pool BN254Fr
  poolIdx : Lower.Ref → Option Nat
  ok : stageOk (airs ++ [rootAir k n]) P poolIdx = true
  W : Wiring (airs ++ [rootAir k n]) P
  nWires : Nat
  publics : Nat
  committed : List Nat
  w : Nat → BN254Fr
  pub : List BN254Fr
  H : List BN254Fr → BN254Fr
  sat : (emitScs (airs ++ [rootAir k n]) P W nWires publics committed).Satisfied w pub H
  entryId : (idOf root.channel : BN254Fr) = k
  statement : (List.range n).map (W.main w airs.length 0) = (Bridge.encode idOf root).drop 2
  good : ChallengeGood (w (W.poolWire Lower.gammaRef)) (w (W.poolWire Lower.betaRef))
    (MsgTuple (airs ++ [rootAir k n]) (W.main w)) (WideStage.stageLedger (airs ++ [rootAir k n]) (W.main w))

/-- Direct soundness extraction for Stage 4 (`CompressFinalNarrow` over BN254) via
`Aiur.Plonk.plonk_shared_heap_sound` (built on `Aiur.Plonk.Sound`). -/
theorem PlonkSharedTerminalWitness.eval_sound
    {source : Generic.Source BN254Fr} {entries : List String}
    {name : String} {args : List (Aiur.SourceValue BN254Fr)}
    (w : PlonkSharedTerminalWitness source entries name args) :
    let mainR := fun t => w.W.main w.w ((WideStage.unitAirs w.idOf w.units).length + w.shared.length + t)
    (WideStage.wideRom w.roms mainR).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM w.compiled.system (WideStage.wideRom w.roms mainR)).decode
          w.specialized.program.enums) heap value w.result :=
  Aiur.Plonk.plonk_shared_heap_sound
    w.compiled w.prepared w.certified w.plan w.activated w.entry w.signed w.rooted w.outside
    w.entryPlain w.arguments w.decoded w.idOf w.idOk w.names w.chipsIn w.unrolled w.capacity
    w.sharedOk w.widths w.romCaps w.romWidths w.small w.tags w.lookups w.characteristic
    w.chanIds w.chanBound w.enablesOk w.memWidth w.hairs w.ok w.W w.sat w.entryId w.statement
    w.good

/-! ## 3. Typed Functional-Refinement Contracts & Cryptographic Extraction Bridges (Explicit TCB Gaps) -/

/-- Semantic result extracted from an `EvalFn` execution of `CompressWrap::verify_root`:
authenticated `(rootKeyBytes, rootClaimsBytes, rootProofBytes)` matching `stmtWords`
under `"ix/compress-wrap/v1\0"` and accepted by `Ix.Cert.MultiStark.verifyBatchBytes`. -/
structure CompressWrapSemanticResult (stmtWords : List Nat) where
  rootKeyBytes : List UInt8
  rootClaimsBytes : List UInt8
  rootProofBytes : ByteArray
  stmt_eq : stmtWords = packBytes32ToU32Words
    (compressWrapStatementDigest (Blake3.Pure.digest rootKeyBytes).toList
      (Blake3.Pure.digest rootClaimsBytes).toList).toList
  batch_accepted :
    verifyBatchBytes (ByteArray.mk rootKeyBytes.toArray) (ByteArray.mk rootClaimsBytes.toArray)
      rootProofBytes = true

/-- **Open TCB Gap (Program Functional Refinement 1 — `CompressWrap`):**
Proving that every `EvalFn` of `CompressWrap::verify_root([0; 8], stmtWords)` yields
`CompressWrapSemanticResult stmtWords` (listed in `docs/aiur-compression-architecture.md` §3). -/
def CompressWrapSemanticContract (wrapSrc : Generic.Source _root_.MultiStark.F) : Prop :=
  ∀ (stmtWords : List Nat) (value : Aiur.SourceValue _root_.MultiStark.F) (heap : Aiur.Heap _root_.MultiStark.F),
    Generic.SourceSemantics.EvalFn wrapSrc.world compressWrapEntry
      (compressWrapArgs stmtWords) [] value heap →
    Nonempty (CompressWrapSemanticResult stmtWords)

/-- **Open TCB Gap (Program Functional Refinement 2 — `CompressGL`):**
Proving that every `EvalFn` of `CompressGL::verify_root([0; 8], stmtWords)` certifies that the
emulated-Goldilocks FRI verifier accepted a `CompressWrap` proof under `wrapKeyDigest` on
`stmtWords`. -/
def CompressGLSemanticContract (F : Type) [Field F] [DecidableEq F] (glSrc : Generic.Source F)
    (wrapKeyDigest : Vector UInt8 32) (WrapFriAccepted : Vector UInt8 32 → List Nat → Prop) : Prop :=
  ∀ (stmtWords : List Nat) (value : Aiur.SourceValue F) (heap : Aiur.Heap F),
    Generic.SourceSemantics.EvalFn glSrc.world MultiStark.CompressGL.entry
      (compressGLArgs F stmtWords) [] value heap →
    WrapFriAccepted wrapKeyDigest stmtWords

/-- Semantic result extracted from an `EvalFn` of `CompressNarrowFixed::step_v1(policyWords, 1, stmtWords)`:
authenticates the `IXAUKG01` policy against `policyWords`, binds the embedded GL key and anchors,
and emits the stage-1 deferred KZG pair `cur₁` folded from `(0, 0)` with weight `w₁`. -/
structure Bn254NarrowSemanticResult (bp : BilinearPairing)
    (policyWords stmtWords : List Nat) (glKeyBytes : List UInt8) where
  policy : PackedPolicy
  policy_wf : policy.WellFormed
  policy_digest_eq : policyWords = packBytes32ToU32Words policy.digest.toList
  gl_key_bound : policy.glKeyDigest = (Blake3.Pure.digest glKeyBytes).toList
  w₁ : BN254Fr
  w₁_nonzero : w₁ ≠ 0
  cur₁ : bp.G1 × bp.G1
  acc₁ : bp.G1 × bp.G1
  acc₁_eq : acc₁ = bn254FoldStep bp w₁ (0, 0) cur₁

/-- **Open TCB Gap (Program Functional Refinement 3 — `CompressNarrowFixed`, BN254):** -/
def Bn254NarrowSemanticContract (bp : BilinearPairing)
    (narrowSrc : Generic.Source BN254Fr) (glKeyBytes : List UInt8) : Prop :=
  ∀ (policyWords stmtWords : List Nat) (value : Aiur.SourceValue BN254Fr)
    (heap : Aiur.Heap BN254Fr),
    Generic.SourceSemantics.EvalFn narrowSrc.world compressNarrowFixedEntry
      (compressNarrowArgs BN254Fr policyWords 1 stmtWords) [] value heap →
    Nonempty (Bn254NarrowSemanticResult bp policyWords stmtWords glKeyBytes)

/-- Semantic result extracted from an `EvalFn` of `CompressFinalNarrow::verify_accumulator_v1(low, high)`
against concrete fixed witness parameters `(finalPolicy, w₂, prevAcc, cur₂)`:
decodes `(low, high)` to 8 `u32` words, authenticates `finalPolicy` against `cfg.policyDigest`,
binds the 128-byte anchors and embedded narrow key, checks the 21-word keyed `step_v1` claim,
and emits `acc₂ = fold(w₂, prevAcc, cur₂)` matching the terminal deferred pair `(d0, d1)`. -/
structure Bn254FinalSemanticResult (bp : BilinearPairing)
    (cfg : _root_.MultiStark.Final.Configuration) (stmtLow stmtHigh : Nat) (d0 d1 : bp.G1)
    (finalPolicy : PackedPolicy) (w₂ : BN254Fr) (prevAcc cur₂ : bp.G1 × bp.G1) where
  policy_wf : finalPolicy.WellFormed
  policy_digest_eq : cfg.policyDigest = packBytes32ToU32Words finalPolicy.digest.toList
  stmtWords : List Nat
  stmt_eq : stmtWords = unpackLimbsToU32Words stmtLow stmtHigh
  w₂_nonzero : w₂ ≠ 0
  folded_eq : (d0, d1) = bn254FoldStep bp w₂ prevAcc cur₂

/-- **Open TCB Gap (Program Functional Refinement 4 — `CompressFinalNarrow`, BN254):** -/
def Bn254FinalSemanticContract (bp : BilinearPairing)
    (finalSrc : Generic.Source BN254Fr) (cfg : _root_.MultiStark.Final.Configuration)
    (d0 d1 : bp.G1) (finalPolicy : PackedPolicy) (w₂ : BN254Fr)
    (prevAcc cur₂ : bp.G1 × bp.G1) : Prop :=
  ∀ (stmtLow stmtHigh : Nat) (value : Aiur.SourceValue BN254Fr) (heap : Aiur.Heap BN254Fr),
    Generic.SourceSemantics.EvalFn finalSrc.world compressFinalNarrowEntry
      (compressFinalArgs BN254Fr stmtLow stmtHigh) [] value heap →
    Nonempty (Bn254FinalSemanticResult bp cfg stmtLow stmtHigh d0 d1 finalPolicy w₂ prevAcc cur₂)

/-- BLS12-381 subgroup-enforced semantic result for `CompressNarrowFixed::step_v1`. -/
structure Bls12381NarrowSemanticResult (bp : Bls12381BilinearPairing)
    (policyWords stmtWords : List Nat) (glKeyBytes : List UInt8) where
  policy : PackedPolicy
  policy_wf : policy.WellFormed
  policy_digest_eq : policyWords = packBytes32ToU32Words policy.digest.toList
  gl_key_bound : policy.glKeyDigest = (Blake3.Pure.digest glKeyBytes).toList
  w₁ : BLS12381Fr
  w₁_nonzero : w₁ ≠ 0
  cur₁ : bp.G1 × bp.G1
  cur₁_sub : BlsPairInSubgroup bp cur₁
  acc₁ : bp.G1 × bp.G1
  acc₁_eq : acc₁ = bls12381FoldStep bp w₁ (0, 0) cur₁

def Bls12381NarrowSemanticContract (bp : Bls12381BilinearPairing)
    (narrowSrc : Generic.Source BLS12381Fr) (glKeyBytes : List UInt8) : Prop :=
  ∀ (policyWords stmtWords : List Nat) (value : Aiur.SourceValue BLS12381Fr)
    (heap : Aiur.Heap BLS12381Fr),
    Generic.SourceSemantics.EvalFn narrowSrc.world compressNarrowFixedEntry
      (compressNarrowArgs BLS12381Fr policyWords 1 stmtWords) [] value heap →
    Nonempty (Bls12381NarrowSemanticResult bp policyWords stmtWords glKeyBytes)

/-- BLS12-381 subgroup-enforced semantic result for `CompressFinalNarrow::verify_accumulator_v1`
against concrete fixed witness parameters `(finalPolicy, w₂, prevAcc, cur₂)`. -/
structure Bls12381FinalSemanticResult (bp : Bls12381BilinearPairing)
    (cfg : _root_.MultiStark.Final.Configuration) (stmtLow stmtHigh : Nat) (d0 d1 : bp.G1)
    (finalPolicy : PackedPolicy) (w₂ : BLS12381Fr) (prevAcc cur₂ : bp.G1 × bp.G1) where
  policy_wf : finalPolicy.WellFormed
  policy_digest_eq : cfg.policyDigest = packBytes32ToU32Words finalPolicy.digest.toList
  stmtWords : List Nat
  stmt_eq : stmtWords = unpackLimbsToU32Words stmtLow stmtHigh
  w₂_nonzero : w₂ ≠ 0
  prevAcc_sub : BlsPairInSubgroup bp prevAcc
  cur₂_sub : BlsPairInSubgroup bp cur₂
  folded_eq : (d0, d1) = bls12381FoldStep bp w₂ prevAcc cur₂

def Bls12381FinalSemanticContract (bp : Bls12381BilinearPairing)
    (finalSrc : Generic.Source BLS12381Fr) (cfg : _root_.MultiStark.Final.Configuration)
    (d0 d1 : bp.G1) (finalPolicy : PackedPolicy) (w₂ : BLS12381Fr)
    (prevAcc cur₂ : bp.G1 × bp.G1) : Prop :=
  ∀ (stmtLow stmtHigh : Nat) (value : Aiur.SourceValue BLS12381Fr)
    (heap : Aiur.Heap BLS12381Fr),
    Generic.SourceSemantics.EvalFn finalSrc.world compressFinalNarrowEntry
      (compressFinalArgs BLS12381Fr stmtLow stmtHigh) [] value heap →
    Nonempty (Bls12381FinalSemanticResult bp cfg stmtLow stmtHigh d0 d1 finalPolicy w₂ prevAcc cur₂)

/-! ## 4. Unified `ix_aggr` Root Payload & Auditable TCB-Gap Bundles -/

/-- Root `ix_aggr` accepted aggregation witness + ROM tree error budget, directly matching
the conclusion of `Ix.Cert.Aggr.aggregated_root_sound`. -/
structure RootAggrCertified (rootKeyPin : Vector UInt8 32)
    (rootKeyBytes rootClaimsBytes : List UInt8)
    {sem : _root_.Aggr.AggrSemantics Address Address Ix.DynamicLink.EvalAssumption Address K
      Ix.DynamicLink.DynamicLinkStatement Ix.DynamicLink.LinkedCircuitEntry}
    {batchClaim : Nat → _root_.Aggr.ValidatorMode Address → (Address → Prop) → (Address → Prop) →
      (Address → Prop) → (Ix.DynamicLink.EvalAssumption → Prop) → Prop}
    {rootStmt : _root_.Aggr.AggrNodeStmt Address Address Ix.DynamicLink.EvalAssumption Address K
      Ix.DynamicLink.DynamicLinkStatement Ix.DynamicLink.LinkedCircuitEntry}
    (t : AcceptedAggrTree sem batchClaim rootStmt) (nodeProbs : List ℝ) (ε : ℝ) : Prop where
  rootKey_pinned : Blake3.Pure.digest rootKeyBytes = rootKeyPin
  aggr_ast_pinned : AggregateProgramAstPinned MultiStark.aggregateProgram = true
  node_err_bound : nodeProbs.sum ≤ (t.verificationCount : ℝ) * ε
  root_holds : _root_.Aggr.AggrNodeHolds sem rootStmt
  children_verified_or_collision :
    t.HasTreeCollision ∨
      ∀ vp ∈ t.childProofs, ∃ proofBytes,
        verifyBatchBytes vp.vkBytes vp.claimsBytes proofBytes = true

/-- **TCB-Gap Bundle for the L3 BN254 Aiur Compression Pipeline (inconsistent; withdrawn):**
This record has NO inhabitant in any model (`Bn254AiurCompressionTcbGaps.inconsistent`), so it
must not be used as a hypothesis: a theorem assuming it holds whatever it concludes. It is not a
statement of the open bridges of the deployed chain. Its fields are:
- 4 program functional-refinement contracts (`finalSemantic`, `narrowSemantic`, `glSemantic`,
  `wrapSemantic`),
- 5 cryptographic extraction bridges (`outerToFinalScs`, `narrowKzgToTiling`,
  `glKzgToGroupedWide`, `wrapFriToWideGoldilocks`, `rootFriToAggr`),
- 1 accumulator handoff equality (`narrowAccMatchesFinalPrev`) connecting Stage 3's packed
  output accumulator to Stage 4's unpacked `prevAcc`,
- explicit external crypto assumptions (`ignitionSrsAndAgmSound`, `keyWritersFaithful`). -/
structure Bn254AiurCompressionTcbGaps
    (sha256 : List UInt8 → List UInt8)
    (manifest : StageManifest)
    (finalCfg : _root_.MultiStark.Final.Configuration)
    (finalHeaders : List NarrowClaimHeader)
    (bp : BilinearPairing)
    (outerKeys deferredKeys : bp.G2 × bp.G2)
    (vk : GnarkVerifyingKey)
    (inp : OuterInputs)
    (stmtLow stmtHigh : Nat)
    (d0 d1 : bp.G1)
    (finalPolicy : PackedPolicy)
    (w₂ : BN254Fr)
    (prevAcc cur₂ : bp.G1 × bp.G1)
    (wrapSrc : Generic.Source _root_.MultiStark.F) (wrapEntries : List String)
    (glSrc : Generic.Source BN254Fr) (glEntries : List String)
    (narrowSrc : Generic.Source BN254Fr) (narrowEntries : List String)
    (finalSrc : Generic.Source BN254Fr) (finalEntries : List String)
    {sem : _root_.Aggr.AggrSemantics Address Address Ix.DynamicLink.EvalAssumption Address K
      Ix.DynamicLink.DynamicLinkStatement Ix.DynamicLink.LinkedCircuitEntry}
    {batchClaim : Nat → _root_.Aggr.ValidatorMode Address → (Address → Prop) → (Address → Prop) →
      (Address → Prop) → (Ix.DynamicLink.EvalAssumption → Prop) → Prop}
    {rootStmt : _root_.Aggr.AggrNodeStmt Address Address Ix.DynamicLink.EvalAssumption Address K
      Ix.DynamicLink.DynamicLinkStatement Ix.DynamicLink.LinkedCircuitEntry}
    (t : AcceptedAggrTree sem batchClaim rootStmt)
    (nodeProbs : List ℝ) (ε : ℝ) where
  -- Pure export-time configuration validation for `CompressFinalNarrow`
  finalCfg_validated : validateFinalNarrowConfig finalCfg finalHeaders = .ok ()
  finalCfg_matches_manifest :
    finalCfg.policyDigest = manifest.finalPolicyDigestWords ∧
    finalCfg.anchors = manifest.finalAnchors.map (·.toNat)
  -- Public statement limb binding into outer `plonk::native` terminal inputs
  stmtLow_lt : stmtLow < 2 ^ 128
  stmtHigh_lt : stmtHigh < 2 ^ 128
  outerPublics_bind_limbs :
    inp.publics 0 = (stmtLow : BN254Fr) ∧ inp.publics 1 = (stmtHigh : BN254Fr)
  -- Wrap FRI predicate shared between CompressGL semantic contract and Wrap extractor
  WrapFriAccepted : Vector UInt8 32 → List Nat → Prop
  -- 4 Program functional-refinement contracts
  finalSemantic : Bn254FinalSemanticContract bp finalSrc finalCfg d0 d1 finalPolicy w₂ prevAcc cur₂
  narrowSemantic : Bn254NarrowSemanticContract bp narrowSrc manifest.glKey.bytes
  glSemantic : CompressGLSemanticContract BN254Fr glSrc manifest.wrapKeyDigest WrapFriAccepted
  wrapSemantic : CompressWrapSemanticContract wrapSrc
  -- 5 Cryptographic extraction bridges (chained stage-to-stage!)
  outerToFinalScs :
    (∃ out, vk.expectedProgram.Satisfied inp out) →
    Nonempty (PlonkSharedTerminalWitness finalSrc finalEntries compressFinalNarrowEntry
      (compressFinalArgs BN254Fr stmtLow stmtHigh))
  narrowKzgToTiling :
    ∀ (fRes : Bn254FinalSemanticResult bp finalCfg stmtLow stmtHigh d0 d1 finalPolicy w₂ prevAcc cur₂),
      bn254DeferredVal bp deferredKeys cur₂ = 1 →
      Nonempty (NarrowCompactStageWitness BN254Fr narrowSrc narrowEntries compressNarrowFixedEntry
        (compressNarrowArgs BN254Fr finalCfg.policyDigest 1 fRes.stmtWords))
  narrowAccMatchesFinalPrev :
    ∀ (fRes : Bn254FinalSemanticResult bp finalCfg stmtLow stmtHigh d0 d1 finalPolicy w₂ prevAcc cur₂)
      (nRes : Bn254NarrowSemanticResult bp finalCfg.policyDigest fRes.stmtWords manifest.glKey.bytes),
      prevAcc = nRes.acc₁
  glKzgToGroupedWide :
    ∀ (stmtWords : List Nat) (nRes : Bn254NarrowSemanticResult bp finalCfg.policyDigest stmtWords manifest.glKey.bytes),
      bn254DeferredVal bp deferredKeys nRes.cur₁ = 1 →
      Nonempty (Bn254GroupedWideStageWitness glSrc glEntries MultiStark.CompressGL.entry
        (compressGLArgs BN254Fr stmtWords))
  wrapFriToWideGoldilocks :
    ∀ (stmtWords : List Nat),
      WrapFriAccepted manifest.wrapKeyDigest stmtWords →
      Nonempty (GoldilocksWideStageWitness wrapSrc wrapEntries compressWrapEntry
        (compressWrapArgs stmtWords))
  rootFriToAggr :
    ∀ (stmtWords : List Nat) (wRes : CompressWrapSemanticResult stmtWords),
      Blake3.Pure.digest wRes.rootKeyBytes = manifest.rootKeyPin ∧
      RootAggrCertified manifest.rootKeyPin wRes.rootKeyBytes wRes.rootClaimsBytes t nodeProbs ε
  -- Explicit external cryptographic assumptions (never Lean axioms)
  ignitionSrsAndAgmSound : Prop
  ignitionSrsAndAgmHolds : ignitionSrsAndAgmSound
  keyWritersFaithful : Prop
  keyWritersFaithfulHolds : keyWritersFaithful
  -- Manifest check
  manifest_pinned : ManifestPinned sha256 manifest

/-- **`Bn254AiurCompressionTcbGaps` is inconsistent:**
for every instantiation of every parameter, the record proves `False`. `glKzgToGroupedWide` is
quantified over every statement and every free `Bn254NarrowSemanticResult`; at the empty statement
with `cur₁ := (0, 0)` it yields a `CompressGL` witness, which `glSemantic`,
`wrapFriToWideGoldilocks` and `wrapSemantic` turn into a `CompressWrapSemanticResult []`, whose
`stmt_eq` equates `[]` with a list of length 8. -/
theorem Bn254AiurCompressionTcbGaps.inconsistent
    {sha256 : List UInt8 → List UInt8}
    {manifest : StageManifest}
    {finalCfg : _root_.MultiStark.Final.Configuration}
    {finalHeaders : List NarrowClaimHeader}
    {bp : BilinearPairing} {outerKeys deferredKeys : bp.G2 × bp.G2}
    {vk : GnarkVerifyingKey} {inp : OuterInputs}
    {stmtLow stmtHigh : Nat} {d0 d1 : bp.G1}
    {finalPolicy : PackedPolicy} {w₂ : BN254Fr} {prevAcc cur₂ : bp.G1 × bp.G1}
    {wrapSrc : Generic.Source _root_.MultiStark.F} {wrapEntries : List String}
    {glSrc : Generic.Source BN254Fr} {glEntries : List String}
    {narrowSrc : Generic.Source BN254Fr} {narrowEntries : List String}
    {finalSrc : Generic.Source BN254Fr} {finalEntries : List String}
    {sem : _root_.Aggr.AggrSemantics Address Address Ix.DynamicLink.EvalAssumption Address K
      Ix.DynamicLink.DynamicLinkStatement Ix.DynamicLink.LinkedCircuitEntry}
    {batchClaim : Nat → _root_.Aggr.ValidatorMode Address → (Address → Prop) → (Address → Prop) →
      (Address → Prop) → (Ix.DynamicLink.EvalAssumption → Prop) → Prop}
    {rootStmt : _root_.Aggr.AggrNodeStmt Address Address Ix.DynamicLink.EvalAssumption Address K
      Ix.DynamicLink.DynamicLinkStatement Ix.DynamicLink.LinkedCircuitEntry}
    {t : AcceptedAggrTree sem batchClaim rootStmt} {nodeProbs : List ℝ} {ε : ℝ}
    (gaps : Bn254AiurCompressionTcbGaps sha256 manifest finalCfg finalHeaders bp outerKeys
      deferredKeys vk inp stmtLow stmtHigh d0 d1 finalPolicy w₂ prevAcc cur₂
      wrapSrc wrapEntries glSrc glEntries narrowSrc narrowEntries finalSrc finalEntries
      t nodeProbs ε) :
    False := by
  have hpd : finalCfg.policyDigest = packBytes32ToU32Words manifest.policy.digest.toList := by
    rw [gaps.finalCfg_matches_manifest.1, gaps.manifest_pinned.final_binds_policy]
  let nRes : Bn254NarrowSemanticResult bp finalCfg.policyDigest [] manifest.glKey.bytes :=
    { policy := manifest.policy
      policy_wf := gaps.manifest_pinned.policy_wf
      policy_digest_eq := hpd
      gl_key_bound := gaps.manifest_pinned.policy_binds_glKey
      w₁ := 1
      w₁_nonzero := one_ne_zero
      cur₁ := (0, 0)
      acc₁ := bn254FoldStep bp 1 (0, 0) (0, 0)
      acc₁_eq := rfl }
  have hcur : bn254DeferredVal bp deferredKeys nRes.cur₁ = 1 :=
    bn254DeferredVal_zero bp deferredKeys
  obtain ⟨wGl⟩ := gaps.glKzgToGroupedWide [] nRes hcur
  obtain ⟨_, vG, hG, hEvalG, _⟩ := wGl.eval_sound
  have hWrapFri := gaps.glSemantic [] vG hG hEvalG
  obtain ⟨wWrap⟩ := gaps.wrapFriToWideGoldilocks [] hWrapFri
  obtain ⟨_, vW, hW, hEvalW, _⟩ := wWrap.eval_sound
  obtain ⟨wRes⟩ := gaps.wrapSemantic [] vW hW hEvalW
  have h := congrArg List.length wRes.stmt_eq
  simp [packBytes32ToU32Words_length] at h

/-- **TCB-Gap Bundle for the BLS12-381 Aiur Compression Pipeline (inconsistent; withdrawn):**
Same shape as `Bn254AiurCompressionTcbGaps` over `BLS12381Fr`, and likewise has NO inhabitant
(`Bls12381AiurCompressionTcbGaps.inconsistent`). No BLS12-381 stage program is deployed, and the
`security128_ok` field is a predicate on the constants it names, tied to no stage. -/
structure Bls12381AiurCompressionTcbGaps
    (sha256 : List UInt8 → List UInt8)
    (manifest : StageManifest)
    (finalCfg : _root_.MultiStark.Final.Configuration)
    (finalHeaders : List NarrowClaimHeader)
    (assumptions : Bls12381CryptoAssumptions)
    (starkParams : StarkParams) (requireUd : Bool)
    (bp : Bls12381BilinearPairing)
    (outerKeys deferredKeys : bp.G2 × bp.G2)
    (vk : Bls12381GnarkVerifyingKey)
    (inp : Bls12381OuterInputs)
    (stmtLow stmtHigh : Nat)
    (d0 d1 : bp.G1)
    (finalPolicy : PackedPolicy)
    (w₂ : BLS12381Fr)
    (prevAcc cur₂ : bp.G1 × bp.G1)
    (wrapSrc : Generic.Source _root_.MultiStark.F) (wrapEntries : List String)
    (glSrc : Generic.Source BLS12381Fr) (glEntries : List String)
    (narrowSrc : Generic.Source BLS12381Fr) (narrowEntries : List String)
    (finalSrc : Generic.Source BLS12381Fr) (finalEntries : List String)
    {sem : _root_.Aggr.AggrSemantics Address Address Ix.DynamicLink.EvalAssumption Address K
      Ix.DynamicLink.DynamicLinkStatement Ix.DynamicLink.LinkedCircuitEntry}
    {batchClaim : Nat → _root_.Aggr.ValidatorMode Address → (Address → Prop) → (Address → Prop) →
      (Address → Prop) → (Ix.DynamicLink.EvalAssumption → Prop) → Prop}
    {rootStmt : _root_.Aggr.AggrNodeStmt Address Address Ix.DynamicLink.EvalAssumption Address K
      Ix.DynamicLink.DynamicLinkStatement Ix.DynamicLink.LinkedCircuitEntry}
    (t : AcceptedAggrTree sem batchClaim rootStmt)
    (nodeProbs : List ℝ) (ε : ℝ) where
  -- 128-bit v6 (Fp^3 + BLAKE2b-512) + BLS12-381 security profile
  security128_ok :
    AiurCompression128Ok 3 6 64 starkParams requireUd .bls12381
      Ix.Cert.Compression.Security128.bls12381CurveSpec
  -- Pure export-time configuration validation for `CompressFinalNarrow`
  finalCfg_validated : validateFinalNarrowConfig finalCfg finalHeaders = .ok ()
  finalCfg_matches_manifest :
    finalCfg.policyDigest = manifest.finalPolicyDigestWords ∧
    finalCfg.anchors = manifest.finalAnchors.map (·.toNat)
  -- Public statement limb binding into outer BLS12-381 `plonk::native` terminal inputs
  stmtLow_lt : stmtLow < 2 ^ 128
  stmtHigh_lt : stmtHigh < 2 ^ 128
  outerPublics_bind_limbs :
    inp.publics 0 = (stmtLow : BLS12381Fr) ∧ inp.publics 1 = (stmtHigh : BLS12381Fr)
  -- Wrap FRI predicate
  WrapFriAccepted : Vector UInt8 32 → List Nat → Prop
  -- 4 Program functional-refinement contracts (subgroup-enforced on BLS12-381)
  finalSemantic : Bls12381FinalSemanticContract bp finalSrc finalCfg d0 d1 finalPolicy w₂ prevAcc cur₂
  narrowSemantic : Bls12381NarrowSemanticContract bp narrowSrc manifest.glKey.bytes
  glSemantic : CompressGLSemanticContract BLS12381Fr glSrc manifest.wrapKeyDigest WrapFriAccepted
  wrapSemantic : CompressWrapSemanticContract wrapSrc
  -- 5 Chained cryptographic extraction bridges
  outerToFinalShared :
    (∃ out, vk.expectedProgram.Satisfied inp out) →
    Nonempty (FieldGroupedSharedStageWitness BLS12381Fr finalSrc finalEntries
      compressFinalNarrowEntry (compressFinalArgs BLS12381Fr stmtLow stmtHigh))
  narrowKzgToTiling :
    ∀ (fRes : Bls12381FinalSemanticResult bp finalCfg stmtLow stmtHigh d0 d1 finalPolicy w₂ prevAcc cur₂),
      bls12381DeferredVal bp deferredKeys cur₂ = 1 →
      Nonempty (NarrowCompactStageWitness BLS12381Fr narrowSrc narrowEntries
        compressNarrowFixedEntry
        (compressNarrowArgs BLS12381Fr finalCfg.policyDigest 1 fRes.stmtWords))
  narrowAccMatchesFinalPrev :
    ∀ (fRes : Bls12381FinalSemanticResult bp finalCfg stmtLow stmtHigh d0 d1 finalPolicy w₂ prevAcc cur₂)
      (nRes : Bls12381NarrowSemanticResult bp finalCfg.policyDigest fRes.stmtWords manifest.glKey.bytes),
      prevAcc = nRes.acc₁
  glKzgToGroupedShared :
    ∀ (stmtWords : List Nat)
      (nRes : Bls12381NarrowSemanticResult bp finalCfg.policyDigest stmtWords manifest.glKey.bytes),
      bls12381DeferredVal bp deferredKeys nRes.cur₁ = 1 →
      Nonempty (FieldGroupedSharedStageWitness BLS12381Fr glSrc glEntries
        MultiStark.CompressGL.entry (compressGLArgs BLS12381Fr stmtWords))
  wrapFriToWideGoldilocks :
    ∀ (stmtWords : List Nat),
      WrapFriAccepted manifest.wrapKeyDigest stmtWords →
      Nonempty (GoldilocksWideStageWitness wrapSrc wrapEntries compressWrapEntry
        (compressWrapArgs stmtWords))
  rootFriToAggr :
    ∀ (stmtWords : List Nat) (wRes : CompressWrapSemanticResult stmtWords),
      Blake3.Pure.digest wRes.rootKeyBytes = manifest.rootKeyPin ∧
      RootAggrCertified manifest.rootKeyPin wRes.rootKeyBytes wRes.rootClaimsBytes t nodeProbs ε
  -- Key-writer faithfulness (never a Lean axiom)
  keyWritersFaithful : Prop
  keyWritersFaithfulHolds : keyWritersFaithful
  -- Manifest check
  manifest_pinned : ManifestPinned sha256 manifest

/-- **`Bls12381AiurCompressionTcbGaps` is inconsistent:**
the same route as `Bn254AiurCompressionTcbGaps.inconsistent`, through `glKzgToGroupedShared`, with
the subgroup obligation of the free narrow record met by `blsPairInSubgroup_zero`. -/
theorem Bls12381AiurCompressionTcbGaps.inconsistent
    {sha256 : List UInt8 → List UInt8}
    {manifest : StageManifest}
    {finalCfg : _root_.MultiStark.Final.Configuration}
    {finalHeaders : List NarrowClaimHeader}
    {assumptions : Bls12381CryptoAssumptions}
    {starkParams : StarkParams} {requireUd : Bool}
    {bp : Bls12381BilinearPairing} {outerKeys deferredKeys : bp.G2 × bp.G2}
    {vk : Bls12381GnarkVerifyingKey} {inp : Bls12381OuterInputs}
    {stmtLow stmtHigh : Nat} {d0 d1 : bp.G1}
    {finalPolicy : PackedPolicy} {w₂ : BLS12381Fr} {prevAcc cur₂ : bp.G1 × bp.G1}
    {wrapSrc : Generic.Source _root_.MultiStark.F} {wrapEntries : List String}
    {glSrc : Generic.Source BLS12381Fr} {glEntries : List String}
    {narrowSrc : Generic.Source BLS12381Fr} {narrowEntries : List String}
    {finalSrc : Generic.Source BLS12381Fr} {finalEntries : List String}
    {sem : _root_.Aggr.AggrSemantics Address Address Ix.DynamicLink.EvalAssumption Address K
      Ix.DynamicLink.DynamicLinkStatement Ix.DynamicLink.LinkedCircuitEntry}
    {batchClaim : Nat → _root_.Aggr.ValidatorMode Address → (Address → Prop) → (Address → Prop) →
      (Address → Prop) → (Ix.DynamicLink.EvalAssumption → Prop) → Prop}
    {rootStmt : _root_.Aggr.AggrNodeStmt Address Address Ix.DynamicLink.EvalAssumption Address K
      Ix.DynamicLink.DynamicLinkStatement Ix.DynamicLink.LinkedCircuitEntry}
    {t : AcceptedAggrTree sem batchClaim rootStmt} {nodeProbs : List ℝ} {ε : ℝ}
    (gaps : Bls12381AiurCompressionTcbGaps sha256 manifest finalCfg finalHeaders assumptions
      starkParams requireUd bp outerKeys deferredKeys vk inp stmtLow stmtHigh d0 d1
      finalPolicy w₂ prevAcc cur₂
      wrapSrc wrapEntries glSrc glEntries narrowSrc narrowEntries finalSrc finalEntries
      t nodeProbs ε) :
    False := by
  have hpd : finalCfg.policyDigest = packBytes32ToU32Words manifest.policy.digest.toList := by
    rw [gaps.finalCfg_matches_manifest.1, gaps.manifest_pinned.final_binds_policy]
  let nRes : Bls12381NarrowSemanticResult bp finalCfg.policyDigest [] manifest.glKey.bytes :=
    { policy := manifest.policy
      policy_wf := gaps.manifest_pinned.policy_wf
      policy_digest_eq := hpd
      gl_key_bound := gaps.manifest_pinned.policy_binds_glKey
      w₁ := 1
      w₁_nonzero := one_ne_zero
      cur₁ := (0, 0)
      cur₁_sub := blsPairInSubgroup_zero bp
      acc₁ := bls12381FoldStep bp 1 (0, 0) (0, 0)
      acc₁_eq := rfl }
  have hcur : bls12381DeferredVal bp deferredKeys nRes.cur₁ = 1 :=
    bls12381DeferredVal_zero bp deferredKeys
  obtain ⟨wGl⟩ := gaps.glKzgToGroupedShared [] nRes hcur
  obtain ⟨_, vG, hG, hEvalG, _⟩ := wGl.eval_sound
  have hWrapFri := gaps.glSemantic [] vG hG hEvalG
  obtain ⟨wWrap⟩ := gaps.wrapFriToWideGoldilocks [] hWrapFri
  obtain ⟨_, vW, hW, hEvalW, _⟩ := wWrap.eval_sound
  obtain ⟨wRes⟩ := gaps.wrapSemantic [] vW hW hEvalW
  have h := congrArg List.length wRes.stmt_eq
  simp [packBytes32ToU32Words_length] at h

end Ix.Cert.AiurCompression
