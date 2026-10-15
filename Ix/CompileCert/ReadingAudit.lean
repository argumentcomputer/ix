import Ix.CompileCert.UniverseAudit
import Ix.CompileCert.CacheSound
import Ix.CompileCert.Serializers
import Ix.CompileCert.PreseedValidation

/-! # Audit of the reading-chain proofs

Every theorem of the reading chain's shared layers that a later proof uses
is a root here: the run layer (`Ix.CompileCert.RawRun`, beyond the universe
proofs' part, which `Ix.CompileCert.UniverseAudit` audits), the memo
invariant (`Ix.CompileCert.CacheSound`), the certified reader on the
compiler's in-flight tables (`Ix.CompileCert.ExpressionRead`), the table
interners (`Ix.CompileCert.Interning`), the checked blob writes
(`Ix.CompileCert.BlobWrites`), the metadata serializers' footprint
(`Ix.CompileCert.Serializers`) and the preseed's universe-wire guard
(`Ix.CompileCert.PreseedValidation`). Each root must exist, occur once, and
depend on no axiom but `propext`, `Classical.choice` and `Quot.sound`
(`Ix.CompileCert.UniverseAudit.checkRoots`, through the certified kernel's
traversal `Ix.Kernel.Audit.collectCached`, so `sorryAx` fails it).

The proofs are about the definitions that run: the production functions
they unfold carry no `@[csimp]` replacement and no `@[implemented_by]`, and
are safe definitions (`Ix.CompileCert.UniverseAudit.checkRuntime`). -/

namespace Ix.CompileCert.ReadingAudit

/-- The run equations, bind inversions, frame combinators and success-only
triples. -/
def runRoots : Array Lean.Name :=
  #[`rawRun_throw, `rawRun_modifyGet, `rawRun_withBlockEnv, `rawRun_applyBlockState,
    `run_eq_rawRun, `run_success, `bind_ok, `bind_success,
    `Preserves.readCompile, `Preserves.modifyGet, `Preserves.map, `Preserves.withBlockEnv,
    `Preserves.mapM_list, `Preserves.mapM_array, `Preserves.forIn'_list, `Preserves.forIn'_array,
    `Preserves.forIn_list, `Preserves.forIn_array, `Preserves.of_ok,
    `Triple.pure, `Triple.throw, `Triple.bind, `Triple.consequence, `Triple.map, `Triple.get,
    `Triple.readBlock, `Triple.readCompile, `Triple.modify, `Triple.modifyGet,
    `Triple.withBlockEnv, `Triple.forIn_list, `Triple.forIn_array].map (`Ix.CompileCert ++ ·)

/-- The memo invariant. -/
def cacheRoots : Array Lean.Name :=
  #[`CacheSound.empty, `CacheSound.mono, `CacheSound.insert_of_respects,
    `CacheSound.insert].map (`Ix.CompileCert ++ ·)

/-- The certified reader's readings survive table growth, and so do the
expression cache's meanings. -/
def readRoots : Array Lean.Name :=
  #[`Preserves.refl, `Preserves.bind, `Extends.refl, `Extends.levels, `convExpr_preserves,
    `Extends.of_tables, `withBlockBlobs_keyAt, `blockReader_tbl, `blockReader_level,
    `blockReader_growth, `blockReader_growth_tables, `blockReader_cache_blind,
    `reading_cache_blind, `Reading.of_growth, `cache_sound_of_growth,
    `blockReader_cache_sound].map (`Ix.CompileCert.ExpressionRead ++ ·)

/-- The table interners: index integrity, retained slots, readings and
cache meanings. -/
def internRoots : Array Lean.Name :=
  #[`Retains.refl, `Retains.trans, `Retains.push, `Retains.map, `Retains.append_right,
    `IndexSound.empty, `IndexSound.insert, `refIndexSound_empty,
    `internRef_retains, `internRef_lookup, `internRef_sound, `internRef_limit_wraps,
    `internUniv_lookup, `internUniv_sound,
    `checkedTableIndex_state, `checkedTableIndex_value, `checkedTableCount_state,
    `checkedTableCount_value,
    `internRef_hit, `internRef_miss, `internRef_correct, `internRef_tables, `internRef_reading,
    `internRef_cache_sound,
    `internUniv_hit, `internUniv_miss, `internUniv_correct, `internUniv_tables,
    `internUniv_reading, `internUniv_cache_sound,
    `add_index_eq, `internMetaUniv_hit, `internMetaUniv_miss, `internMetaUniv_correct,
    `internMetaUniv_tables, `internMetaUniv_reading,
    `internMetaUniv_cache_sound].map (`Ix.CompileCert.Interning ++ ·)

/-- Checked blob writes and name compilation. -/
def blobRoots : Array Lean.Name :=
  #[`Extends.refl, `Extends.trans, `contentMatches_agree, `storeBlob_success,
    `compileName_success, `storeBlob_run, `storeBlob_preserves, `compileName_preserves,
    `compileNames_success, `compileNames_preserves, `reader_extends, `storeBlob_reading,
    `compileName_reading, `cache_preserved,
    `storeBlob_refuses_local].map (`Ix.CompileCert.BlobWrites ++ ·)

/-- The metadata serializers' footprint and its consequences. -/
def serializerRoots : Array Lean.Name :=
  #[`NamesBlobs.pure, `NamesBlobs.throw, `NamesBlobs.get, `NamesBlobs.read, `NamesBlobs.bind,
    `NamesBlobs.map, `NamesBlobs.mapM_list, `NamesBlobs.mapM_array, `NamesBlobs.storeBlob,
    `NamesBlobs.storeString, `NamesBlobs.compileName, `NamesBlobs.compileNames,
    `NamesBlobs.serializeIxSubstring, `NamesBlobs.serializeIxSourceInfo,
    `NamesBlobs.serializeIxSyntaxPreresolved, `NamesBlobs.serializeIxSyntax,
    `NamesBlobs.compileDataValue, `NamesBlobs.compileKVMap, `NamesBlobs.reading,
    `NamesBlobs.cache_sound, `NamesBlobs.preserves].map (`Ix.CompileCert.Serializers ++ ·)

/-- The preseed's universe-wire guard. -/
def preseedRoots : Array Lean.Name :=
  #[`array_valid, `run, `state, `accepts, `valid_of_success, `refuses, `wire_count,
    `refuses_count, `after_check].map (`Ix.CompileCert.PreseedValidation ++ ·)

/-- The production definitions the table, blob and serializer proofs unfold,
and the reader functions the reading proofs unfold. -/
def tableRuntime : Array Lean.Name :=
  #[``Ix.CompileM.BlockState.internRef, ``Ix.CompileM.BlockState.internUniv,
    ``Ix.CompileM.BlockState.internMetaUniv, ``Ix.CompileM.internRef, ``Ix.CompileM.internUniv,
    ``Ix.CompileM.internMetaUniv, ``Ix.CompileM.checkedTableIndex, ``Ix.CompileM.checkedTableCount,
    ``Ix.CompileM.contentMatches, ``Ix.CompileM.BlockState.storeBlob, ``Ix.CompileM.applyBlockState,
    ``Ix.CompileM.storeBlob, ``Ix.CompileM.storeString, ``Ix.CompileM.BlockState.compileName,
    ``Ix.CompileM.compileName, ``Ix.CompileM.BlockState.compileNames, ``Ix.CompileM.compileNames,
    ``Ix.CompileM.serializeIxSubstring, ``Ix.CompileM.serializeIxSourceInfo,
    ``Ix.CompileM.serializeIxSyntaxPreresolved, ``Ix.CompileM.serializeIxSyntax,
    ``Ix.CompileM.compileDataValue, ``Ix.CompileM.compileKVMap, ``Ix.CompileM.checkPreseedUnivs]

def readerRuntime : Array Lean.Name :=
  #[``Ix.Kernel.Reader.convExpr, ``Ix.Kernel.Reader.MemberReader.mk',
    ``Ix.Kernel.Reader.MemberReader.read, ``Ix.Kernel.Reader.ECx.keyAt,
    ``Ix.Kernel.Reader.ECx.blobAt, ``Ix.Kernel.Reader.ECx.levels, ``Ix.Kernel.Reader.Ctx.keyAt]

end Ix.CompileCert.ReadingAudit

open Ix.CompileCert.UniverseAudit (checkRoots checkRuntime) in
run_cmd do
  checkRoots (tag := "reading-audit") "run layer" Ix.CompileCert.ReadingAudit.runRoots
  checkRoots (tag := "reading-audit") "memo invariant" Ix.CompileCert.ReadingAudit.cacheRoots
  checkRoots (tag := "reading-audit") "reader extension" Ix.CompileCert.ReadingAudit.readRoots
  checkRoots (tag := "reading-audit") "interners" Ix.CompileCert.ReadingAudit.internRoots
  checkRoots (tag := "reading-audit") "blobs" Ix.CompileCert.ReadingAudit.blobRoots
  checkRoots (tag := "reading-audit") "serializers" Ix.CompileCert.ReadingAudit.serializerRoots
  checkRoots (tag := "reading-audit") "preseed guard" Ix.CompileCert.ReadingAudit.preseedRoots
  checkRuntime (tag := "reading-audit") "tables, blobs and serializers"
    Ix.CompileCert.ReadingAudit.tableRuntime
  checkRuntime (tag := "reading-audit") "reader" Ix.CompileCert.ReadingAudit.readerRuntime
