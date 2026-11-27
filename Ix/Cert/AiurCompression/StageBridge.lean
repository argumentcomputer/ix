import Ix.Cert.AiurCompression.DepthBridge
import Ix.Cert.AiurCompression.ProgramPins
import Ix.Cert.AiurCompression.StatementBinding
import Ix.Cert.AiurCompression.DeferredFold
import Ix.Cert.AiurCompression.OuterRelation
import Ix.Cert.Aggr.EndToEnd

/-! # Exempt-SCC Stage Witnesses & Execution-Indexed BN254 Aiur Compression Bridges

Directly instantiates the proved Lean compiler, tiling, grouped-wide, and shared-map PLONK
soundness theorems (lifted to `Aiur.Optimized.Physical.Prepared.DepthCertified` in `DepthBridge`,
supporting exempt SCCs) for the four stages of the deployed L3 BN254 Aiur compression chain,
and defines the **execution-indexed** functional-refinement and cryptographic-extraction
hypothesis bundle (`Bn254AiurCompressionTcbGaps`):

1. **Stage 1 (`CompressWrap::verify_root` — Goldilocks Wide STARK):**
   `GoldilocksWideStageWitness.eval_sound` invokes
   `DepthBridge.wide_heap_sound_goldilocks_structural`.
2. **Stage 2 (`CompressGL::verify_root` — Emulated-Goldilocks Grouped Wide KZG):**
   `Bn254GroupedWideStageWitness.eval_sound` invokes
   `DepthBridge.grouped_heap_sound_bn254_structural`.
3. **Stage 3 (`CompressNarrowFixed::step_v1` — Tiled Narrow Compact-Table KZG):**
   `NarrowCompactStageWitness.eval_sound` invokes
   `DepthBridge.narrow_heap_sound_compact_structural`.
4. **Stage 4 (`CompressFinalNarrow::verify_accumulator_v1` — Shared-Map PLONK SCS):**
   `PlonkSharedTerminalWitness.eval_sound` invokes
   `DepthBridge.plonk_shared_heap_sound_structural`.
5. **Execution-Indexed Semantic Relations & Bridges (`Bn254AiurCompressionTcbGaps`):**
   - Every stage semantic relation (`FinalExecRel`, `NarrowExecRel`, `GlExecRel`, `WrapExecRel`)
     is indexed by the actual `(args, value, heap)` of an `EvalFn` execution (never free records).
   - Stage 4's 18-word `affine-u80-v1` output and Stage 3's 4-word `KzgAccumulator::pack` output
     are decoded directly from each execution's returned `SourceValue`, so accumulator handoff
     (`prevAcc = acc₁`) and terminal pairing operands `(d0, d1)` are **proved** from
     `represents_field_tuple`, not assumed globally.
   - Supports both the deployed two-layer `--aiur-stages` statement chain
     (`StatementPolicy.twoLayerWrap wp`) and the single-layer fixed-wrapper policy
     (`StatementPolicy.singleLayerDirect`).
   - Ties `rootKeyPin` to the public statement `(stmtLow, stmtHigh)` (never universally forcing
     every accepting key to hash to `rootKeyPin`) and binds `rootStmt` directly to
     `rootClaimsBytes` via `claimsBindStmt`.
   - Constructively proved satisfiable (reaching the main non-escape soundness branch) in
     `Ix.Cert.AiurCompression.Consistency`.
   - For Lean-compiled stages emitted via `IxCCAiur`, `IxCC.AiurBackend.CompiledCert.Cert`
     (`IxCCAiur/IxCCAiur/CompiledCert.lean`) discharges `DepthCertified`, `cfg.bits ≤ 24`,
     `WellFormedActivation`, entry resolution, and pure-Lean BLAKE3 `.ixa` pinning, while
     `IxCC.AiurBackend.CompressionIntrinsics` (`IxCCAiur/IxCCAiur/CompressionIntrinsics.lean`)
     certifies compression intrinsic lowering and custom entry-point aliasing (`aliasEntry_sound`)
     for all four stage entry signatures.

Zero `sorry`, zero custom `axiom`, zero `native_decide`, zero `bv_decide`.
-/

namespace Ix.Cert.AiurCompression

open Aiur Aiur.Circuit Aiur.Optimized Aiur.Tiling Aiur.Tiling.Bridge Aiur.Tiling.Grouped
open Aiur.Plonk
open Ix.Cert.Compression.Foreign
open Ix.Cert.Compression.OuterRelation
open Ix.Cert.MultiStark
open Ix.Cert.Aggr

/-! ## 1. Canonical Aiur `SourceValue` Argument Encodings & Output Decoders -/

/-- Encode an 8-word `u32` digest as an Aiur `[Field; 8]` tuple value over field `F`. -/
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

/-- Extract a flat list of field elements from a `SourceValue.tuple` of `SourceValue.field`s. -/
def extractFieldList {F : Type} : List (Aiur.SourceValue F) → Option (List F)
  | [] => some []
  | .field x :: rest => (extractFieldList rest).map (x :: ·)
  | _ :: _ => none

/-- Extract a flat `[Field; n]` tuple from an `Aiur.SourceValue F`. -/
def extractFieldTuple {F : Type} : Aiur.SourceValue F → Option (List F)
  | .tuple items => extractFieldList items
  | _ => none

theorem extractFieldList_map {F : Type} (ws : List F) :
    extractFieldList (ws.map Aiur.Value.field) = some ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [extractFieldList, ih]

theorem extractFieldTuple_map {F : Type} (ws : List F) :
    extractFieldTuple (.tuple (ws.map Aiur.Value.field)) = some ws := by
  simp [extractFieldTuple, extractFieldList_map]

/-- Decode the 18-word `affine-u80-v1` `[Field; 18]` `SourceValue` returned by
`CompressFinalNarrow::verify_accumulator_v1` into a BN254 `bp.G1 × bp.G1` deferred pair. -/
def decodeFinalSourceValue {bp : BilinearPairing} (codec : Bn254AffineCodec bp)
    (v : Aiur.SourceValue BN254Fr) : Option (bp.G1 × bp.G1) :=
  (extractFieldTuple v).bind (decodeBn254AffinePairWords codec)

theorem decodeFinalSourceValue_fieldTuple {bp : BilinearPairing} (codec : Bn254AffineCodec bp)
    (ws : List BN254Fr) :
    decodeFinalSourceValue codec (.tuple (ws.map Aiur.Value.field)) =
      decodeBn254AffinePairWords codec ws := by
  simp [decodeFinalSourceValue, extractFieldTuple_map]

/-- Decode the 4-word packed `[Field; 4]` `SourceValue` returned by
`CompressNarrowFixed::step_v1` (`KzgAccumulator::pack`) into `bp.G1 × bp.G1`. -/
def decodeNarrowSourceValue {bp : BilinearPairing} (codec : Bn254PackedAccCodec bp)
    (v : Aiur.SourceValue BN254Fr) : Option (bp.G1 × bp.G1) :=
  (extractFieldTuple v).bind codec.decodePacked

theorem decodeNarrowSourceValue_fieldTuple {bp : BilinearPairing} (codec : Bn254PackedAccCodec bp)
    (ws : List BN254Fr) :
    decodeNarrowSourceValue codec (.tuple (ws.map Aiur.Value.field)) =
      codec.decodePacked ws := by
  simp [decodeNarrowSourceValue, extractFieldTuple_map]

/-! ## 2. Exempt-SCC Stage Witness Structures (All 4 L3 BN254 Stages) -/

/-- **Stage 1 (`CompressWrap`) Goldilocks Wide-Stage Witness:**
Packages every static and trace hypothesis of `DepthBridge.wide_heap_sound_goldilocks_structural`,
using `Physical.Prepared.DepthCertified` (supporting exempt SCCs). -/
structure GoldilocksWideStageWitness
    (source : Generic.Source _root_.MultiStark.F) (entries : List String)
    (name : String) (args : List (Aiur.SourceValue _root_.MultiStark.F)) where
  specialized : Generic.Specialized source entries
  compiled : GenericArtifact specialized
  prepared : Physical.Prepared compiled.artifact
  cfg : Depth.Config
  certified : Physical.Prepared.DepthCertified compiled prepared cfg
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
  chanIds : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) plan.singles root,
    ∀ y ∈ Bridge.channels (Depth.system cfg prepared.system) plan.singles root,
    idOf x = idOf y → x = y
  chanBound : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) plan.singles root,
    idOf x < bound
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
`DepthBridge.wide_heap_sound_goldilocks_structural`. -/
theorem GoldilocksWideStageWitness.eval_sound
    {source : Generic.Source _root_.MultiStark.F} {entries : List String}
    {name : String} {args : List (Aiur.SourceValue _root_.MultiStark.F)}
    (w : GoldilocksWideStageWitness source entries name args) :
    (WideStage.wideRom w.roms w.mainR).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM w.compiled.system (WideStage.wideRom w.roms w.mainR)).decode
          w.specialized.program.enums) heap value w.result :=
  DepthBridge.wide_heap_sound_goldilocks_structural
    w.compiled w.prepared w.certified w.plan w.activated w.entry w.signed w.rooted w.outside
    w.entryPlain w.arguments w.decoded w.idOf w.chipsIn w.unrolled w.capacity w.widths
    w.romCaps w.hbound w.tags w.lookups w.hbits w.chanIds w.chanBound w.enablesOk
    w.holds w.balanced

/-- **Stage 2 (`CompressGL`, BN254) Grouped Wide-Stage Witness:**
Packages every static and trace hypothesis of `DepthBridge.grouped_heap_sound_bn254_structural`,
using `Physical.Prepared.DepthCertified` (supporting exempt SCCs). -/
structure Bn254GroupedWideStageWitness
    (source : Generic.Source BN254Fr) (entries : List String)
    (name : String) (args : List (Aiur.SourceValue BN254Fr)) where
  specialized : Generic.Specialized source entries
  compiled : GenericArtifact specialized
  prepared : Physical.Prepared compiled.artifact
  cfg : Depth.Config
  certified : Physical.Prepared.DepthCertified compiled prepared cfg
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
  chanIds : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) (allChips plan) root,
    ∀ y ∈ Bridge.channels (Depth.system cfg prepared.system) (allChips plan) root,
    idOf x = idOf y → x = y
  chanBound : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) (allChips plan) root,
    idOf x < bound
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
`DepthBridge.grouped_heap_sound_bn254_structural`. -/
theorem Bn254GroupedWideStageWitness.eval_sound
    {source : Generic.Source BN254Fr} {entries : List String}
    {name : String} {args : List (Aiur.SourceValue BN254Fr)}
    (w : Bn254GroupedWideStageWitness source entries name args) :
    (WideStage.wideRom w.roms w.mainR).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM w.compiled.system (WideStage.wideRom w.roms w.mainR)).decode
          w.specialized.program.enums) heap value w.result :=
  DepthBridge.grouped_heap_sound_bn254_structural
    w.compiled w.prepared w.certified w.plan w.activated w.entry w.signed w.rooted w.outside
    w.entryPlain w.arguments w.decoded w.idOf w.idOk w.names w.chipsIn w.unrolled w.groupsIn
    w.capacity w.widths w.romCaps w.romWidths w.hbound w.tags w.lookups w.hbits w.chanIds
    w.chanBound w.enablesOk w.memWidth w.holds w.holdsG w.balanced

/-- **Stage 3 (`CompressNarrowFixed`, BN254) Tiled Narrow Compact-Table Witness (`tiling_export2`):**
Packages every static and trace hypothesis of `DepthBridge.narrow_heap_sound_compact_structural`,
using `Physical.Prepared.DepthCertified` (supporting exempt SCCs). -/
structure NarrowCompactStageWitness (F : Type) [Field F] [DecidableEq F]
    (source : Generic.Source F) (entries : List String)
    (name : String) (args : List (Aiur.SourceValue F)) where
  specialized : Generic.Specialized source entries
  compiled : GenericArtifact specialized
  prepared : Physical.Prepared compiled.artifact
  cfg : Depth.Config
  certified : Physical.Prepared.DepthCertified compiled prepared cfg
  hbits : cfg.bits ≤ 24
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
  characteristic : ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ 24 → (n : F) ≠ 0
  req : (Part.request S.width (Bridge.encode idOf root)).checkRequest S.system
    (Bridge.encode idOf root) = true
  req2 : S.checkRequest2 (Part.request S.width (Bridge.encode idOf root)) = true
  chanIds : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) plan.singles root,
    ∀ y ∈ Bridge.channels (Depth.system cfg prepared.system) plan.singles root,
    idOf x = idOf y → x = y
  chanBound : ∀ x ∈ Bridge.channels (Depth.system cfg prepared.system) plan.singles root,
    idOf x < bound
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
`DepthBridge.narrow_heap_sound_compact_structural`. -/
theorem NarrowCompactStageWitness.eval_sound {F : Type} [Field F] [DecidableEq F]
    {source : Generic.Source F} {entries : List String}
    {name : String} {args : List (Aiur.SourceValue F)}
    (w : NarrowCompactStageWitness F source entries name args) :
    (Periodic.compactRom w.S w.tables w.mainT).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM w.compiled.system
          (Periodic.compactRom w.S w.tables w.mainT)).decode
          w.specialized.program.enums) heap value w.result :=
  DepthBridge.narrow_heap_sound_compact_structural
    w.compiled w.prepared w.certified w.hbits w.plan w.activated w.entry w.signed w.rooted
    w.outside w.entryPlain w.arguments w.decoded w.idOf w.ok w.chipsIn w.unrolled w.circuits
    w.wideEq w.lenG w.merged w.tablesOk w.mapsIn w.capacity w.small w.tags w.codesBound w.labels
    w.shadowBound w.lookups w.idsBound w.parts w.characteristic w.req w.req2 w.chanIds w.chanBound
    w.enablesOk w.tall w.tallT w.rows w.balanced

/-- **Stage 4 (`CompressFinalNarrow`, BN254) Shared-Map PLONK SCS Witness (`plonk_export`):**
Packages every static and constraint-system hypothesis of
`DepthBridge.plonk_shared_heap_sound_structural`, using `Physical.Prepared.DepthCertified`. -/
structure PlonkSharedTerminalWitness
    (source : Generic.Source BN254Fr) (entries : List String)
    (name : String) (args : List (Aiur.SourceValue BN254Fr)) where
  specialized : Generic.Specialized source entries
  compiled : GenericArtifact specialized
  prepared : Physical.Prepared compiled.artifact
  cfg : Depth.Config
  certified : Physical.Prepared.DepthCertified compiled prepared cfg
  hbits : cfg.bits ≤ 24
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
  cert : DepthBridge.PlonkStageCert (airs ++ [rootAir k n]) P
  W : DepthBridge.PlonkStageWiring (airs ++ [rootAir k n]) P cert.rowFin
  nWires : Nat
  publics : Nat
  committed : List Nat
  w : Nat → BN254Fr
  pub : List BN254Fr
  H : List BN254Fr → BN254Fr
  sat : (DepthBridge.emitCertifiedScs (airs ++ [rootAir k n]) P cert.rowGates cert.rowFin W
    nWires publics committed).Satisfied w pub H
  entryId : (idOf root.channel : BN254Fr) = k
  statement : (List.range n).map (W.main w airs.length 0) = (Bridge.encode idOf root).drop 2
  good : ChallengeGood (w (W.poolWire Lower.gammaRef)) (w (W.poolWire Lower.betaRef))
    (MsgTuple (airs ++ [rootAir k n]) (W.main w))
    (WideStage.stageLedger (airs ++ [rootAir k n]) (W.main w))

/-- Direct soundness extraction for Stage 4 (`CompressFinalNarrow` over BN254) via
`DepthBridge.plonk_shared_heap_sound_certified`. -/
theorem PlonkSharedTerminalWitness.eval_sound
    {source : Generic.Source BN254Fr} {entries : List String}
    {name : String} {args : List (Aiur.SourceValue BN254Fr)}
    (w : PlonkSharedTerminalWitness source entries name args) :
    let mainR := fun t => w.W.main w.w ((WideStage.unitAirs w.idOf w.units).length + w.shared.length + t)
    (WideStage.wideRom w.roms mainR).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM w.compiled.system (WideStage.wideRom w.roms mainR)).decode
          w.specialized.program.enums) heap value w.result :=
  DepthBridge.plonk_shared_heap_sound_certified
    w.compiled w.prepared w.certified w.hbits w.plan w.activated w.entry w.signed w.rooted w.outside
    w.entryPlain w.arguments w.decoded w.idOf w.idOk w.names w.chipsIn w.unrolled w.capacity
    w.sharedOk w.widths w.romCaps w.romWidths w.small w.tags w.lookups
    w.chanIds w.chanBound w.enablesOk w.memWidth w.hairs w.cert w.W w.sat w.entryId w.statement
    w.good

/-! ## 3. Root `ix_aggr` Payload Tied Directly to `rootClaimsBytes` -/

/-- Root `ix_aggr` certification payload derived from `(rootKeyBytes, rootClaimsBytes)`:
binds `rootStmt` directly to `rootClaimsBytes` via `claimsBindStmt`, pins `rootKeyBytes` to
`rootKeyPin`, and carries the ROM tree error bound, `AggrNodeHolds`, and child verification
disjunction from `Ix.Cert.Aggr.acceptedAggrTree_refines_derivation19`. -/
structure RootAggrCertified (rootKeyPin : Vector UInt8 32)
    (rootKeyBytes rootClaimsBytes : List UInt8)
    {sem : _root_.Aggr.AggrSemantics Address Address Ix.DynamicLink.EvalAssumption Address K
      Ix.DynamicLink.DynamicLinkStatement Ix.DynamicLink.LinkedCircuitEntry}
    {batchClaim : Nat → _root_.Aggr.ValidatorMode Address → (Address → Prop) → (Address → Prop) →
      (Address → Prop) → (Ix.DynamicLink.EvalAssumption → Prop) → Prop}
    (claimsBindStmt : List UInt8 →
      _root_.Aggr.AggrNodeStmt Address Address Ix.DynamicLink.EvalAssumption Address K
        Ix.DynamicLink.DynamicLinkStatement Ix.DynamicLink.LinkedCircuitEntry → Prop)
    (rootStmt : _root_.Aggr.AggrNodeStmt Address Address Ix.DynamicLink.EvalAssumption Address K
      Ix.DynamicLink.DynamicLinkStatement Ix.DynamicLink.LinkedCircuitEntry)
    (t : AcceptedAggrTree sem batchClaim rootStmt) (nodeProbs : List ℝ) (ε : ℝ) : Prop where
  rootKey_pinned : Blake3.Pure.digest rootKeyBytes = rootKeyPin
  claims_bind_stmt : claimsBindStmt rootClaimsBytes rootStmt
  node_err_bound : nodeProbs.sum ≤ (t.verificationCount : ℝ) * ε
  root_holds : _root_.Aggr.AggrNodeHolds sem rootStmt
  children_verified_or_collision :
    t.HasTreeCollision ∨
      ∀ vp ∈ t.childProofs, ∃ proofBytes,
        verifyBatchBytes vp.vkBytes vp.claimsBytes proofBytes = true

/-! ## 4. Execution-Indexed, Satisfiable TCB-Gap Bundle for L3 BN254 Aiur Compression -/

/-- Canonical 8-word little-endian `u32` digest predicate (`ws.length = 8` and each word `< 2^32`). -/
def CanonicalU32Digest8 (ws : List Nat) : Prop :=
  ws.length = 8 ∧ ∀ w ∈ ws, w < 2 ^ 32

theorem canonicalU32Digest8_packBytes32 (bs : List UInt8) :
    CanonicalU32Digest8 (packBytes32ToU32Words bs) :=
  ⟨packBytes32ToU32Words_length bs, packBytes32ToU32Words_lt bs⟩

theorem canonicalU32Digest8_terminalStatementWords (pol : StatementPolicy)
    (pin : Vector UInt8 32) (claims : List UInt8) :
    CanonicalU32Digest8 (pol.terminalStatementWords pin claims) :=
  ⟨pol.terminalStatementWords_length pin claims, pol.terminalStatementWords_lt pin claims⟩

theorem canonicalU32Digest8_rootStatementWords (pin : Vector UInt8 32) (claims : List UInt8) :
    CanonicalU32Digest8 (rootStatementWords pin claims) :=
  ⟨rootStatementWords_length pin claims, rootStatementWords_lt pin claims⟩

/-- Policy-conditional proposition active only in two-layer `WrapPolicy` mode (trivially `True`
in `singleLayerDirect` mode). Factored outside `Bn254AiurCompressionTcbGaps` so dependent `match`
motives stay tiny. -/
def StatementPolicy.whenTwoLayer (pol : StatementPolicy) (P : WrapPolicySpec → Prop) : Prop :=
  match pol with
  | .twoLayerWrap wp => P wp
  | .singleLayerDirect => True

/-- Policy-selected inner FRI acceptance predicate checked by Stage 2 (`CompressGL`):
`WrapFriAccepted` in `twoLayerWrap` mode, `RootFriAccepted` in `singleLayerDirect` mode. -/
def StatementPolicy.glAccepted (pol : StatementPolicy)
    (WrapFriAccepted RootFriAccepted : List UInt8 → List UInt8 → Prop)
    (innerKeyBytes innerClaimsBytes : List UInt8) : Prop :=
  match pol with
  | .twoLayerWrap _ => WrapFriAccepted innerKeyBytes innerClaimsBytes
  | .singleLayerDirect => RootFriAccepted innerKeyBytes innerClaimsBytes

/-- **Execution-Indexed TCB-Gap Bundle for the L3 BN254 Aiur Compression Chain:**
Isolates every remaining open program-refinement and cryptographic-extraction bridge between
the deployed `ix-aiur-scs-v1` outer PLONK proof and the `ix_aggr` root claim, parameterized
over `stmtPolicy : StatementPolicy` (supporting both the two-layer `WrapPolicy::statement_for`
chain and a single-layer direct fixed-wrapper chain):

- **Manifest & configuration pinning:** `manifest_pinned`, `finalCfg_validated`,
  `finalCfg_matches_manifest`, `vk_matches_manifest`, `policy_matches_manifest`, and
  `public_statement_eq` binding `(stmtLow, stmtHigh)` to `(stmtPolicy, manifest.rootKeyPin, rootClaimsBytes)`.
- **Execution-indexed semantic relations (`FinalExecRel`, `NarrowExecRel`, `GlExecRel`,
  `WrapExecRel`):** every relation is indexed by the actual `(args, value, heap)` of an `EvalFn`
  execution, decoding Stage 4's 18-word `affine-u80-v1` output and Stage 3's 4-word
  `KzgAccumulator::pack` output directly from `value` (never quantifying over free records or
  fixing per-execution accumulators globally).
- **4 execution-indexed functional-refinement contracts:** `finalSemantic`, `narrowSemantic`,
  `glSemantic`, `wrapSemantic`.
- **5 execution-indexed cryptographic extraction bridges:** `outerToFinalScs`,
  `narrowKzgToTiling`, `glKzgToGroupedWide`, `wrapFriToWideGoldilocks`, `rootFriToAggr`.
  (`rootFriToAggr` is quantified ONLY over root keys matching `manifest.rootKeyPin` and
  existentially produces `(rootStmt, t, nodeProbs)` tied to `rootClaimsBytes` via `claimsBindStmt`.)

Constructively proved satisfiable (with non-trivial pairing, compiled stage witnesses, and
provably false escape predicate) in `Ix.Cert.AiurCompression.Consistency`. -/
structure Bn254AiurCompressionTcbGaps
    (sha256 : List UInt8 → List UInt8)
    (manifest : StageManifest)
    (stmtPolicy : StatementPolicy)
    (rootClaimsBytes : List UInt8)
    (finalCfg : _root_.MultiStark.Final.Configuration)
    (finalHeaders : List NarrowClaimHeader)
    (bp : BilinearPairing)
    (vk : AiurScsVerifyingKey bp sha256)
    (packedCodec : Bn254PackedAccCodec bp)
    (stmtLow stmtHigh : Nat)
    (wrapSrc : Generic.Source _root_.MultiStark.F) (wrapEntries : List String)
    (glSrc : Generic.Source BN254Fr) (glEntries : List String)
    (narrowSrc : Generic.Source BN254Fr) (narrowEntries : List String)
    (finalSrc : Generic.Source BN254Fr) (finalEntries : List String)
    (sem : _root_.Aggr.AggrSemantics Address Address Ix.DynamicLink.EvalAssumption Address K
      Ix.DynamicLink.DynamicLinkStatement Ix.DynamicLink.LinkedCircuitEntry)
    (batchClaim : Nat → _root_.Aggr.ValidatorMode Address → (Address → Prop) → (Address → Prop) →
      (Address → Prop) → (Ix.DynamicLink.EvalAssumption → Prop) → Prop)
    (claimsBindStmt : List UInt8 →
      _root_.Aggr.AggrNodeStmt Address Address Ix.DynamicLink.EvalAssumption Address K
        Ix.DynamicLink.DynamicLinkStatement Ix.DynamicLink.LinkedCircuitEntry → Prop)
    (ε : ℝ) where
  -- Manifest, configuration, and outer VK binding
  manifest_pinned : ManifestPinned sha256 manifest
  finalCfg_validated : validateFinalNarrowConfig finalCfg finalHeaders = .ok ()
  finalCfg_matches_manifest :
    finalCfg.policyDigest = manifest.finalPolicyDigestWords ∧
    finalCfg.anchors = manifest.finalAnchors.map (·.toNat)
  vk_matches_manifest :
    vk.expectedSpec.anchorsBytes = manifest.outerPairingAnchors ∧
    manifest.terminalScs.bytes = vk.scsBytes
  policy_matches_manifest :
    stmtPolicy.whenTwoLayer fun wp => wp.wrapKeyDigest = manifest.wrapKeyDigest
  -- Public statement limb binding (rootKeyPin is a hypothesis on the public statement!)
  public_statement_eq :
    (stmtLow, stmtHigh) = stmtPolicy.terminalLimbs manifest.rootKeyPin rootClaimsBytes
  -- Abstract inner FRI acceptance predicates (in production: `∃ proofBytes, verifyBatchBytes ... = true`)
  WrapFriAccepted : List UInt8 → List UInt8 → Prop
  RootFriAccepted : List UInt8 → List UInt8 → Prop
  -- Execution-indexed semantic relations (indexed by actual `(args, value, heap)` executions!)
  FinalExecRel :
    Nat → Nat → Aiur.SourceValue BN254Fr → Aiur.Heap BN254Fr →
    PackedPolicy → BN254Fr → (bp.G1 × bp.G1) → (bp.G1 × bp.G1) → List BN254Fr → Prop
  finalExecRel_spec :
    ∀ (low high : Nat) (value₄ : Aiur.SourceValue BN254Fr) (heap₄ : Aiur.Heap BN254Fr)
      (finalPolicy : PackedPolicy) (w₂ : BN254Fr) (prevAcc cur₂ : bp.G1 × bp.G1)
      (prevAccWords : List BN254Fr),
      low < 2 ^ 128 → high < 2 ^ 128 →
      Generic.SourceSemantics.EvalFn finalSrc.world compressFinalNarrowEntry
        (compressFinalArgs BN254Fr low high) [] value₄ heap₄ →
      FinalExecRel low high value₄ heap₄ finalPolicy w₂ prevAcc cur₂ prevAccWords →
      finalPolicy.WellFormed ∧
      finalCfg.policyDigest = packBytes32ToU32Words finalPolicy.digest.toList ∧
      finalCfg.anchors = finalPolicy.anchors.map (·.toNat) ∧
      w₂ ≠ 0 ∧
      packedCodec.decodePacked prevAccWords = some prevAcc ∧
      decodeFinalSourceValue vk.expectedSpec.affineCodec value₄ =
        some (bn254FoldStep bp w₂ prevAcc cur₂)
  NarrowExecRel :
    List Nat → List Nat → Aiur.SourceValue BN254Fr → Aiur.Heap BN254Fr →
    PackedPolicy → BN254Fr → (bp.G1 × bp.G1) → Prop
  narrowExecRel_spec :
    ∀ (policyWords stmtWords : List Nat) (value₃ : Aiur.SourceValue BN254Fr)
      (heap₃ : Aiur.Heap BN254Fr) (narrowPolicy : PackedPolicy) (w₁ : BN254Fr)
      (cur₁ : bp.G1 × bp.G1),
      CanonicalU32Digest8 policyWords → CanonicalU32Digest8 stmtWords →
      Generic.SourceSemantics.EvalFn narrowSrc.world compressNarrowFixedEntry
        (compressNarrowArgs BN254Fr policyWords 1 stmtWords) [] value₃ heap₃ →
      NarrowExecRel policyWords stmtWords value₃ heap₃ narrowPolicy w₁ cur₁ →
      narrowPolicy.WellFormed ∧
      policyWords = packBytes32ToU32Words narrowPolicy.digest.toList ∧
      narrowPolicy.glKeyDigest = (Blake3.Pure.digest manifest.glKey.bytes).toList ∧
      w₁ ≠ 0 ∧
      decodeNarrowSourceValue packedCodec value₃ =
        some (bn254FoldStep bp w₁ (0, 0) cur₁)
  GlExecRel :
    List Nat → Aiur.SourceValue BN254Fr → Aiur.Heap BN254Fr →
    List UInt8 → List UInt8 → Prop
  glExecRel_spec :
    ∀ (stmtWords : List Nat) (value₂ : Aiur.SourceValue BN254Fr) (heap₂ : Aiur.Heap BN254Fr)
      (innerKeyBytes innerClaimsBytes : List UInt8),
      CanonicalU32Digest8 stmtWords →
      Generic.SourceSemantics.EvalFn glSrc.world MultiStark.CompressGL.entry
        (compressGLArgs BN254Fr stmtWords) [] value₂ heap₂ →
      GlExecRel stmtWords value₂ heap₂ innerKeyBytes innerClaimsBytes →
      stmtWords = packBytes32ToU32Words
        (compressWrapStatementDigest (Blake3.Pure.digest innerKeyBytes).toList
          (Blake3.Pure.digest innerClaimsBytes).toList).toList ∧
      stmtPolicy.glAccepted WrapFriAccepted RootFriAccepted innerKeyBytes innerClaimsBytes
  WrapExecRel :
    List Nat → Aiur.SourceValue _root_.MultiStark.F → Aiur.Heap _root_.MultiStark.F →
    List UInt8 → List UInt8 → Prop
  wrapExecRel_spec :
    stmtPolicy.whenTwoLayer fun _ =>
      ∀ (stmtWords : List Nat) (value₁ : Aiur.SourceValue _root_.MultiStark.F)
        (heap₁ : Aiur.Heap _root_.MultiStark.F)
        (rootKeyBytes' rootClaimsBytes' : List UInt8),
        CanonicalU32Digest8 stmtWords →
        Generic.SourceSemantics.EvalFn wrapSrc.world compressWrapEntry
          (compressWrapArgs stmtWords) [] value₁ heap₁ →
        WrapExecRel stmtWords value₁ heap₁ rootKeyBytes' rootClaimsBytes' →
        stmtWords = packBytes32ToU32Words
          (compressWrapStatementDigest (Blake3.Pure.digest rootKeyBytes').toList
            (Blake3.Pure.digest rootClaimsBytes').toList).toList ∧
        RootFriAccepted rootKeyBytes' rootClaimsBytes'
  -- 4 Execution-indexed program functional-refinement contracts
  finalSemantic :
    ∀ (low high : Nat) (value₄ : Aiur.SourceValue BN254Fr) (heap₄ : Aiur.Heap BN254Fr),
      low < 2 ^ 128 → high < 2 ^ 128 →
      Generic.SourceSemantics.EvalFn finalSrc.world compressFinalNarrowEntry
        (compressFinalArgs BN254Fr low high) [] value₄ heap₄ →
      ∃ finalPolicy w₂ prevAcc cur₂ prevAccWords,
        FinalExecRel low high value₄ heap₄ finalPolicy w₂ prevAcc cur₂ prevAccWords
  narrowSemantic :
    ∀ (policyWords stmtWords : List Nat) (value₃ : Aiur.SourceValue BN254Fr)
      (heap₃ : Aiur.Heap BN254Fr),
      CanonicalU32Digest8 policyWords → CanonicalU32Digest8 stmtWords →
      Generic.SourceSemantics.EvalFn narrowSrc.world compressNarrowFixedEntry
        (compressNarrowArgs BN254Fr policyWords 1 stmtWords) [] value₃ heap₃ →
      ∃ narrowPolicy w₁ cur₁,
        NarrowExecRel policyWords stmtWords value₃ heap₃ narrowPolicy w₁ cur₁
  glSemantic :
    ∀ (stmtWords : List Nat) (value₂ : Aiur.SourceValue BN254Fr) (heap₂ : Aiur.Heap BN254Fr),
      CanonicalU32Digest8 stmtWords →
      Generic.SourceSemantics.EvalFn glSrc.world MultiStark.CompressGL.entry
        (compressGLArgs BN254Fr stmtWords) [] value₂ heap₂ →
      ∃ innerKeyBytes innerClaimsBytes,
        GlExecRel stmtWords value₂ heap₂ innerKeyBytes innerClaimsBytes
  wrapSemantic :
    stmtPolicy.whenTwoLayer fun _ =>
      ∀ (stmtWords : List Nat) (value₁ : Aiur.SourceValue _root_.MultiStark.F)
        (heap₁ : Aiur.Heap _root_.MultiStark.F),
        CanonicalU32Digest8 stmtWords →
        Generic.SourceSemantics.EvalFn wrapSrc.world compressWrapEntry
          (compressWrapArgs stmtWords) [] value₁ heap₁ →
        ∃ rootKeyBytes' rootClaimsBytes',
          WrapExecRel stmtWords value₁ heap₁ rootKeyBytes' rootClaimsBytes'
  -- 5 Execution-indexed cryptographic extraction bridges
  outerToFinalScs :
    ∀ (w : Nat → BN254Fr) (H : List BN254Fr → BN254Fr),
      vk.expectedSpec.scs.Satisfied w [(stmtLow : BN254Fr), (stmtHigh : BN254Fr)] H →
      ∃ w₄ : PlonkSharedTerminalWitness finalSrc finalEntries compressFinalNarrowEntry
        (compressFinalArgs BN254Fr stmtLow stmtHigh),
        w₄.result = .tuple ((vk.expectedSpec.outputWires.map w).map Aiur.Value.field)
  narrowKzgToTiling :
    ∀ (low high : Nat) (value₄ : Aiur.SourceValue BN254Fr) (heap₄ : Aiur.Heap BN254Fr)
      (finalPolicy : PackedPolicy) (w₂ : BN254Fr) (prevAcc cur₂ : bp.G1 × bp.G1)
      (prevAccWords : List BN254Fr),
      low < 2 ^ 128 → high < 2 ^ 128 →
      Generic.SourceSemantics.EvalFn finalSrc.world compressFinalNarrowEntry
        (compressFinalArgs BN254Fr low high) [] value₄ heap₄ →
      FinalExecRel low high value₄ heap₄ finalPolicy w₂ prevAcc cur₂ prevAccWords →
      bn254DeferredVal bp vk.expectedSpec.anchors cur₂ = 1 →
      ∃ w₃ : NarrowCompactStageWitness BN254Fr narrowSrc narrowEntries compressNarrowFixedEntry
        (compressNarrowArgs BN254Fr finalCfg.policyDigest 1 (unpackLimbsToU32Words low high)),
        w₃.result = .tuple (prevAccWords.map Aiur.Value.field)
  glKzgToGroupedWide :
    ∀ (stmtWords : List Nat) (value₃ : Aiur.SourceValue BN254Fr) (heap₃ : Aiur.Heap BN254Fr)
      (narrowPolicy : PackedPolicy) (w₁ : BN254Fr) (cur₁ : bp.G1 × bp.G1),
      CanonicalU32Digest8 stmtWords →
      Generic.SourceSemantics.EvalFn narrowSrc.world compressNarrowFixedEntry
        (compressNarrowArgs BN254Fr finalCfg.policyDigest 1 stmtWords) [] value₃ heap₃ →
      NarrowExecRel finalCfg.policyDigest stmtWords value₃ heap₃ narrowPolicy w₁ cur₁ →
      bn254DeferredVal bp vk.expectedSpec.anchors cur₁ = 1 →
      Nonempty (Bn254GroupedWideStageWitness glSrc glEntries MultiStark.CompressGL.entry
        (compressGLArgs BN254Fr stmtWords))
  wrapFriToWideGoldilocks :
    stmtPolicy.whenTwoLayer fun wp =>
      ∀ (wrapKeyBytes : List UInt8) (rootStmtWords : List Nat),
        CanonicalU32Digest8 rootStmtWords →
        Blake3.Pure.digest wrapKeyBytes = wp.wrapKeyDigest →
        WrapFriAccepted wrapKeyBytes (wp.claimsBytes rootStmtWords) →
        Nonempty (GoldilocksWideStageWitness wrapSrc wrapEntries compressWrapEntry
          (compressWrapArgs rootStmtWords))
  rootFriToAggr :
    ∀ (rootKeyBytes : List UInt8),
      Blake3.Pure.digest rootKeyBytes = manifest.rootKeyPin →
      RootFriAccepted rootKeyBytes rootClaimsBytes →
      ∃ (rootStmt : _root_.Aggr.AggrNodeStmt Address Address Ix.DynamicLink.EvalAssumption Address K
          Ix.DynamicLink.DynamicLinkStatement Ix.DynamicLink.LinkedCircuitEntry)
        (t : AcceptedAggrTree sem batchClaim rootStmt)
        (nodeProbs : List ℝ),
        claimsBindStmt rootClaimsBytes rootStmt ∧
        nodeProbs.length = t.verificationCount ∧
        (∀ p ∈ nodeProbs, p ≤ ε)

end Ix.Cert.AiurCompression
