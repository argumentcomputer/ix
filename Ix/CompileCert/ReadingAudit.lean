import Ix.CompileCert.UniverseAudit
import Ix.CompileCert.CacheSound
import Ix.CompileCert.Serializers
import Ix.CompileCert.PreseedValidation
import Ix.CompileCert.WireTables
import Ix.CompileCert.UniversePipeline
import Ix.CompileCert.ExpressionCorrectness
import Ix.CompileCert.RecordState
import Ix.CompileCert.RecordRead
import Ix.CompileCert.RecordSourceShape
import Ix.CompileCert.RecordSubst
import Ix.CompileCert.RecordSubstReading
import Ix.CompileCert.RewriteArityPrimitives
import Ix.CompileCert.DevelopmentArity
import Ix.CompileCert.SemanticFrames
import Ix.CompileCert.SemanticPresence
import Ix.CompileCert.FramePrimitives
import Ix.CompileCert.DevelopmentFrames
import Ix.CompileCert.DevelopmentState
import Ix.CompileCert.RewriteCalls
import Ix.CompileCert.FrontendReceipts
import Ix.CompileCert.ExpressionIngress
import Ix.CompileCert.PreseedWire
import Ix.CompileCert.FinalUniverses
import Ix.CompileCert.PreseedInsertion
import Ix.CompileCert.EmissionWire
import Ix.CompileCert.SharingRoots
import Ix.CompileCert.Emission
import Ix.CompileCert.EmissionBlocks
import Ix.CompileCert.EmissionDispatch
import Ix.CompileCert.HeaderReading
import Ix.CompileCert.ReaderSourceSpines
import Ix.CompileCert.ProjectionLayout
import Ix.CompileCert.MutualArtifact
import Ix.CompileCert.ReaderIndexDiscovery
import Ix.CompileCert.InductiveReading
import Ix.CompileCert.SourceConstructorPositions
import Ix.CompileCert.MutualInductiveReading
import Ix.CompileCert.Canon.EqSound
import Ix.CompileCert.CanonLevelReading

/-! # Audit of the reading-chain proofs

Every theorem of the reading chain's shared layers that a later proof uses
is a root here: the run layer (`Ix.CompileCert.RawRun`, beyond the universe
proofs' part, which `Ix.CompileCert.UniverseAudit` audits), the memo
invariant (`Ix.CompileCert.CacheSound`), the certified reader on the
compiler's in-flight tables (`Ix.CompileCert.ExpressionRead`), the table
interners (`Ix.CompileCert.Interning`), the checked blob writes
(`Ix.CompileCert.BlobWrites`), the metadata serializers' footprint
(`Ix.CompileCert.Serializers`), the preseed's universe-wire guard
(`Ix.CompileCert.PreseedValidation`), the primary tables' wire validity
(`Ix.CompileCert.WireTables`), the raw universe compiler's exact lowering
and its value (`Ix.CompileCert.UniverseMeaning`), the universe pipeline
(`Ix.CompileCert.UniversePipeline`), the ordinary expression compiler's
core (`Ix.CompileCert.ExpressionState`, `ExpressionSteps`,
`ExpressionCorrectness`, `ExpressionIngress`), the preseed
(`Ix.CompileCert.PreseedState`, `PreseedWire`, `FinalUniverses`,
`PreseedCoverage`, `PreseedInsertion`), the emitters' wire validity
(`Ix.CompileCert.EmissionWire`), the sharing builder's root reading
(`Ix.CompileCert.SharingRoots`), the payload emitters (`Ix.CompileCert.Emission`),
the singleton blocks and public dispatch (`Ix.CompileCert.EmissionBlocks`,
`EmissionDispatch`), the reading of compiled singleton records
(`Ix.CompileCert.DefinitionReading`, `HeaderReading`), and the reader's
syntactic walks through sharing and along the source
(`Ix.CompileCert.ReaderSpines`, `ReaderSourceSpines`), and the mutual layout
(`Ix.CompileCert.ProjectionLayout`) and its projections (`Ix.CompileCert.MutualProjections`,
`MutualArtifact`), and the reader's recursor index (`Ix.CompileCert.ReaderIndex`,
`ReaderIndexDiscovery`), and the reading of compiled standalone inductives
(`Ix.CompileCert.InductiveReading`, and through the driver's mutual path:
`MutualInductiveReading`), and what Source mode admits of an
inductive block (`Ix.CompileCert.SourceConstructorPositions`), and the shared
loop lemmas (`Ix.CompileCert.Loop`), and Pass 1's comparator as a total preorder
(`Ix.CompileCert.Canon.Basic` … `Rel`) and its classes, the coarsest consistent
partition (`Ix.CompileCert.Canon.Cache` … `Coarsest`), and what its `eq` means
(`Ix.CompileCert.Canon.EqSound`).
Each root must exist, occur once, and depend on no axiom but `propext`, `Classical.choice` and `Quot.sound`
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
    `Triple.withBlockEnv, `Triple.forIn_list, `Triple.forIn_array,
    `Keeps.pure, `Keeps.throw, `Keeps.bind, `Keeps.throwBind, `Keeps.consequence, `Keeps.get,
    `Keeps.readBlock, `Keeps.readCompile, `Keeps.modify, `Keeps.of_preserves,
    `Keeps.checkedIndex, `Returns.pure, `Returns.bind, `Returns.get, `Returns.readBlock,
    `Returns.modify, `Returns.run].map (`Ix.CompileCert ++ ·)

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
    `internRef_narrow, `internRef_hit, `internRef_miss, `internRef_correct, `internRef_tables,
    `internRef_reading,
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

/-- The primary tables stay on the wire through the interners. -/
def wireRoots : Array Lean.Name :=
  #[`of_same, `empty, `internRef_preserves, `internUniv_preserves, `internMetaUniv_preserves,
    `internRef_count_failure, `internUniv_count_failure,
    `internAdmission_preserves].map (`Ix.CompileCert.WireTables ++ ·)

/-- The table half of the universe pipeline: interning the canonical form,
success, and reading it back. -/
def pipelineRoots : Array Lean.Name :=
  #[`internUniv_frame, `internMetaUniv_frame, `compileAndInternUnivCanon_eq,
    `TablesSound.primary, `TablesSound.metadata, `tablesSound_empty, `finishSpelling_correct,
    `internCanonical_correct, `internMetaUniv_returns, `internUniv_returns,
    `finishSpelling_returns, `internCanonical_returns, `finishSpelling_frame,
    `internCanonical_frame, `canonUnivCached_frame, `canonicalTail_frame,
    `canonicalTail_correct, `canonicalTail_returns, `canonicalTail_read, `canonicalTail_reading,
    `canonicalTail_cache_sound,
    `Sound.of_view, `sound_empty, `compileAndInternUnivCanon_correct, `levelMeaning_of_lower,
    `compileAndInternUnivCanon_read, `compileAndInternUnivCanon_returns,
    `compileAndInternUnivCanon_total_read, `compileAndInternUnivCanon_empty_read,
    `compileAndInternUnivCanon_frame, `compileAndInternUnivCanon_reading,
    `compileAndInternUnivCanon_cache_sound].map (`Ix.CompileCert.UniversePipeline ++ ·)

/-- The raw universe compiler computes the exact positional lowering, which
has the value Source mode reads. -/
def meaningRoots : Array Lean.Name :=
  #[`nameIndex_correct, `nameIndex_lt, `nameIndex_exists, `lower_occurs, `lower_eval, `lower_some,
    `univCacheExact_empty, `univCacheExact_cacheUniv, `keeps_finish, `compileUniv_exact,
    `compileUniv_value, `compileUniv_same, `compileUniv_eval, `returns_finish,
    `compileUniv_returns, `compileUniv_total,
    `compileUniv_total_eval].map (`Ix.CompileCert.UniverseMeaning ++ ·)

/-- The ordinary expression compiler's core (CT-13): the state and its
effects, one step per constructor, the spine's fold, the memo and the top
induction, and the correspondence with Source mode's reading. -/
def expressionRoots : Array Lean.Name :=
  #[`lookupConstAddr_run, `lookupConstAddr_state, `lookupConstAddr_correct, `constsSatisfy_of_forall,
    `constsSatisfy_mono,
    `internRef_frame, `natural_go, `natural_toBytes, `string_toBytes, `extends_trans, `checked_error,
    `meaning_grows, `read_grows, `withoutExprMetadata_reader, `good_metadata, `checked_metadata,
    `internRef_good, `good_namesBlobs, `storeBlob_good, `compileName_good, `compileKVMap_good,
    `blockReader_blob, `blockReader_key, `compileLevel_good, `compileLevels_list_good, `compileLevels_good,
    `bvar_step_eq, `sort_step_eq, `const_step_eq, `binder_step_eq, `let_step_eq, `nat_step_eq,
    `string_step_eq, `projection_step_eq, `then_checked, `child_then_checked, `index_then_checked,
    `allocFinish_checked, `bvar_step_checked, `finishSort_run, `sort_step_checked,
    `finishLiteral_checked, `literal_checked, `nat_step_checked, `string_step_checked,
    `finishReference_run, `finishReference_checked, `compileConstExprRaw_eq, `constBody_checked,
    `const_step_checked, `finishBinder_checked, `binder_step_checked, `finishLet_checked,
    `let_step_checked, `finishProjection_checked, `projection_step_checked, `bvar_step_refuses,
    `projection_step_refuses, `read_lam, `read_all, `read_letE, `lowerContract_read,
    `metadata_step_checked, `decomposeApps_go, `decomposeApps_app, `constsSatisfy_spine,
    `forall₂_snoc, `spine_related, `app_step_eq, `appLoop_checked, `app_step_checked,
    `cached_checked, `compileExprNoSurgery_scoped, `compileExprNoSurgery_checked,
    `compileExprNoSurgery_read, `compileExpr_surgeryFree, `compileExpr_read, `initialState_good,
    `compileExprNoSurgery_initial_read, `withContract_matches, `levels_ingress, `related_ingress,
    `related_ingress_value].map (`Ix.CompileCert.ExpressionState ++ ·)

/-- The preseed (CT-14): it keeps the expression invariant and the binding
view, it keeps the primary tables on the wire, and a final table does not
grow. -/
def preseedStateRoots : Array Lean.Name :=
  (#[`good_of_growth, `good_of_same, `GoodStep.pure, `GoodStep.throw, `GoodStep.get, `GoodStep.readBlock,
    `GoodStep.bind, `GoodStep.discard, `GoodStep.withBlockEnv, `GoodStep.lookup, `GoodStep.check,
    `GoodStep.blob, `GoodStep.ref, `GoodStep.compileUniv, `GoodStep.canon, `GoodStep.univ,
    `GoodStep.final, `GoodStep.resetUnivCache, `GoodStep.withUnivCtx, `GoodStep.collectUnivs,
    `GoodStep.collectStructural, `GoodStep.collect, `GoodStep.collectRoots, `GoodStep.internRefs,
    `GoodStep.canonUnivs, `GoodStep.internUnivs, `preseed_good, `preseed_final,
    `preseed_compileExpr_read].map (`Ix.CompileCert.PreseedState ++ ·)) ++
  (#[`frame_compileUniv, `frame_lookup, `frame_blob, `frame_collectUnivs, `frame_structural,
    `frame_collect, `frame_withUnivCtx, `collection_frame, `Wire.pure, `Wire.bind, `Wire.of_frame,
    `Wire.discard, `internRefs_wire, `internUnivs_wire, `canonUnivs_wire, `preseed_wire,
    `binding_internRefs, `binding_internUnivs, `binding_canonUnivs,
    `preseed_binding].map (`Ix.CompileCert.PreseedWire ++ ·)) ++
  (#[`internMetaUniv_univs, `finishSpelling_univs, `internCanonical_no_growth,
    `compile_no_growth].map (`Ix.CompileCert.FinalUniverses ++ ·))

/-- The preseed's universe coverage: the collector covers every level of its
roots, and the insertion gives each canonical form a slot, so every level
of every root is preseeded. -/
def coverageRoots : Array Lean.Name :=
  (#[`insert_other, `insert_retains, `CoveredBelow.empty, `CoveredBelow.mono, `CoveredBelow.restrict,
    `CoveredBelow.insert, `CoveredBelow.insert_above, `CoveredBelow.lookup, `collect_hit,
    `root_run].map (`Ix.CompileCert.PreseedKeys ++ ·)) ++
  (#[`CacheSafe.pure, `CacheSafe.throw, `CacheSafe.bind, `CacheSafe.compileUniv, `CacheSafe.lookup,
    `CacheSafe.blob, `CacheSafe.levels, `CacheSafe.structural, `LevelsSatisfy.imp, `Present.mono,
    `Present.value, `Covered.mono, `levels_correct, `Added.refl, `Added.mono, `Added.trans,
    `Added.close_parent, `Added.ready, `Result.cached, `Result.insert, `prepare_child, `cached_run,
    `cache_after, `binary, `unary, `ternary, `Correct.of_miss, `collect_correct, `Complete.empty,
    `Complete.ready, `Complete.after, `root_correct, `roots_correct,
    `roots_initial].map (`Ix.CompileCert.PreseedUniverses ++ ·)) ++
  (#[`bytes_beq_iff, `MapExtends.refl, `MapExtends.trans, `MapExtends.insert_fresh, `internUniv_index,
    `discard_ok, `univ_key_injective, `univs_inserted, `sortedUnivs_valid, `sortedUnivs_member,
    `univs_sorted, `canonicalize, `refs_frame,
    `preseed_preseeded].map (`Ix.CompileCert.PreseedInsertion ++ ·))


/-- Successful compilation keeps the primary tables on the wire (CT-14's
`EmissionWire`, CT-15's `FamilyWire` traversal): the combinators, the
leaves, the well-founded expression compiler, every emitter and the preseed. -/
def emissionWireRoots : Array Lean.Name :=
  #[`Valid.of_view, `Safe.framed, `Safe.pure, `Safe.returns, `Safe.throw, `Safe.bind, `Safe.throwBind,
    `Safe.forget, `Safe.seq, `Safe.get, `Safe.readCompile, `Safe.readBlock, `Safe.modify, `Safe.modifyGet,
    `Safe.map, `Safe.withBlockEnv, `Safe.withCurrent, `Safe.withMutCtx, `Safe.withUnivCtx,
    `Safe.checkedIndex, `Safe.checkedCount, `Safe.mapM_list, `Safe.mapM_array, `Safe.forIn_list,
    `Safe.forIn_array, `Safe.compileLevel, `Safe.internRef, `Safe.lookup, `Safe.blob, `Safe.namesBlobs,
    `Safe.compileName, `Safe.compileNames, `Safe.kvmap, `Safe.alloc, `Safe.patch, `Safe.finishReference,
    `Safe.step, `Safe.noSurgery, `Safe.expression, `Safe.takeArena, `Safe.takeSurgerySharing,
    `Safe.takeUnivPatches, `Safe.clearExprCache, `Safe.resetArena, `Safe.recordDefHints,
    `Safe.mutCtxAddrs, `Safe.finishDefinition, `Safe.definitionData, `Safe.finishAxiom,
    `Safe.axiomPayload, `Safe.finishQuotient, `Safe.quotientPayload, `Safe.rule, `Safe.rules,
    `Safe.finishRecursor, `Safe.recursorPayload, `Safe.finishConstructor, `Safe.constructorPayload,
    `Safe.constructors, `Safe.inductiveMetadata, `Safe.finishInductive, `Safe.inductivePayload,
    `Safe.finishInductiveData, `Safe.inductiveData, `Safe.member, `Safe.equivalents, `Safe.constClass,
    `Safe.classes, `Safe.mutConsts, `seeded_valid].map (`Ix.CompileCert.EmissionWire ++ ·)

/-- Canonical sharing preserves the reading of every root (R07-01/02): the
certified reader against a sharing substitution, the root write-back's
inversion for every payload kind, and the builder's reading. -/
def sharingRootRoots : Array Lean.Name :=
  #[`convExpr_subst, `table_empty, `table_push, `buildTable_meaning, `memberReader_eq,
    `memberReader_table, `memberReader_subst, `meaning_read, `convExpr_same_tables, `memberReader_empty,
    `meaning_read_before, `unshared_read, `zip_ctors, `zip_rules, `withMutConstRoots_inv, `withRoots_inv,
    `build_roots, `RootsRead.transfer, `RootsRead.grow, `RootsRead.append,
    `build_read].map (`Ix.CompileCert.SharingRoots ++ ·)

/-- The payload emitters read back as their sources (CT-15's emission, as one
skeleton): the finishers' invariant and frames, the header counts, and the
definition, axiom, quotient, constructor, inductive and recursor emitters. -/
def emissionRoots : Array Lean.Name :=
  #[`Clean.good, `Frame.tidy, `Frame.same, `Frame.display, `Frame.namesBlobs, `Frame.compileName,
    `Frame.compileNames, `Frame.checkedCount, `Frame.checkedIndex, `Frame.readBlock, `Frame.mutCtxAddrs,
    `Frame.takeArena, `Frame.takeSurgerySharing, `Frame.recordDefHints, `Frame.takeUnivPatches, `clear_tidy,
    `finishDefinition_tidy, `finishAxiom_tidy, `finishQuotient_tidy, `finishConstructor_tidy,
    `finishRecursor_tidy, `inductiveMetadata_tidy, `finishInductiveData_tidy, `finish_clean, `Yields.pure,
    `Yields.bind, `Yields.bindAny, `Yields.count, `Yields.index, `exact_header, `definitionHeader,
    `axiomHeader, `quotientHeader, `recursorRuleHeader, `recursorHeader, `constructorHeader,
    `inductiveDataHeader, `Yields.withBlockEnv, `Yields.withCurrent, `Yields.withUnivCtx, `enter_ok,
    `current_ok, `prepared_good, `reset_good, `compileExpr_checked, `compiled_root, `definition_correct,
    `definitionData_header, `single_correct, `axiom_correct, `axiomPayload_header, `quotient_correct,
    `quotientPayload_header, `constructor_correct, `constructors_correct, `compileInductive_eq,
    `inductiveData_correct, `rules_correct, `recursor_correct].map (`Ix.CompileCert.Emission ++ ·)

/-- The singleton blocks read back as their sources and decode exactly
(CT-15's blocks): the block finisher's inversion, the skeletons, the
definition-like, axiom, quotient, recursor and inductive-family blocks,
with and without their preseed. -/
def blockRoots : Array Lean.Name :=
  #[`finish_run, `build_block_run, `block_ok, `block_codec, `rules_skeleton, `ctors_skeleton,
    `definition_erase, `axiom_erase, `quotient_erase, `recursor_erase, `inductive_erase, `family_roots,
    `preseed_then, `definitionBlock_correct, `definitionBlock_codec, `definitionInfo_correct,
    `definitionInfo_codec, `axiomBlock_correct, `axiomBlock_codec, `axiomInfo_correct, `axiomInfo_codec,
    `quotientBlock_correct, `quotientBlock_codec, `quotientInfo_correct, `quotientInfo_codec,
    `recursorPayload_rules, `recursorBlock_correct, `recursorBlock_codec, `recursorInfo_correct,
    `recursorInfo_codec, `familyFinish_ok, `inductiveData_ctors, `familyBlock_correct, `familyBlock_codec,
    `familyInfo_correct, `familyInfo_codec].map (`Ix.CompileCert.EmissionBlocks ++ ·)

/-- Public constant dispatch: dispatch is the kind's block compiler in the
singleton context,
every kind's block decodes exactly, and so does a mutual block (CT-15's
`FamilyWire` and `PayloadArrays`). -/
def dispatchRoots : Array Lean.Name :=
  #[`compileDefinitionInfo_eq, `definition_run,
    `axiom_run, `quotient_run, `recursor_run, `inductive_run, `constructor_run, `find_state, `collect_state,
    `family_run, `inductive_codec, `constant_codec, `member_counts, `forIn_checks, `mutual_counts,
    `member_state, `mutual_state, `standalone_header, `build_mutual_codec, `finish_mutual_codec,
    `mutualBlock_codec].map (`Ix.CompileCert.EmissionDispatch ++ ·)

/-- Compiled singleton records are read back as their sources (CT-16's
definition and header reading): the reader on definition, axiom and
quotient records, the skeletons' inversions, and public dispatch composed
with `readRecord`. -/
def singletonReadRoots : Array Lean.Name :=
  (#[`definitionReader_eq, `singleton_lookup, `singleton_self, `readDefinition_ok, `readRecord_ok,
    `readRecord_declines, `erase_defn, `definitionInfo_levels, `constant_reads,
    `constant_declines].map (`Ix.CompileCert.DefinitionReading ++ ·)) ++
  (#[`readAxiom_ok, `readAxiom_declines, `readQuotient_ok, `erase_axio, `erase_quot, `axiomInfo_levels,
    `quotientInfo_levels, `axiom_unsafe, `axiom_reads, `axiom_declines,
    `quotient_reads].map (`Ix.CompileCert.HeaderReading ++ ·))

/-- The reader's syntactic walks (CT-16's spines): through a sharing table
they commute with the expansion and the sharing builder keeps the recursor
analysis; on an unshared record they follow the converted reading and the
source expression. -/
def spineRoots : Array Lean.Name :=
  (#[`shares_mono, `unshare_go, `unshare_expansion, `unshare_empty, `stripAll_expand, `stripAll_bounded,
    `stripAllFull_expand, `stripAllFull_bounded, `appHead_expand, `appHead_inline, `headRef_expand,
    `lastHead_expand, `carrier_expand, `carriers_expand, `analyse_expand,
    `build_analyse].map (`Ix.CompileCert.ReaderSpines ++ ·)) ++
  (#[`read_outer, `read_forall, `read_bvar, `piTypes_zero, `piTypes_forall, `read_stripAll, `read_appDepth,
    `read_appHead, `read_variable_head, `withContract_shape, `withContract_depth, `withContract_head,
    `withContract_piTypes, `related_appDepth, `source_appDepth, `related_variable_head, `source_variable_head,
    `related_constant_head, `read_constant_head, `source_constant_head, `sourceStrip_zero, `related_strip,
    `pairs_match, `source_stripAll, `source_telescope_variable, `withContract_nonForall,
    `related_kernelNonForall, `related_nonForall, `full_of_nonForall, `full_of_strip, `source_stripAllFull,
    `last_pair, `source_lastHead, `source_carrier, `recursor_counts,
    `compiled_telescope_variable].map (`Ix.CompileCert.ReaderSourceSpines ++ ·))

/-- The mutual layout (CT-15, R9a): what the constructor and class folds keep
of the source, the write-back keeps every member's kind and constructor
positions, the class sort leaves no empty class, and the standalone
family's projections resolve. -/
def layoutRoots : Array Lean.Name :=
  #[`constructor_header, `constructor_index, `constructors_headers, `headers_indices, `constructors_layout,
    `equivalents_count, `class_count, `classes_count, `payload_count, `finish_mutual_ok, `mutual_class_capacity,
    `mutual_block, `mutual_block_capacity, `mutual_class_index, `sorted_nonempty, `throwCmpError_fails,
    `sort_nonempty, `finish_inductive_layout, `finish_inductiveData_layout, `inductiveData_headers,
    `inductiveData_layout, `inductive_layout, `member_shape, `equivalents_payloads, `class_shapes,
    `classes_shapes, `payload_shapes, `memberShape_erase, `blockShape_erase, `writeback_member_shape,
    `writeback_shape, `erase_muts, `writeback_mutual_shape, `sharing_shape, `sharing_mutual_shape,
    `standalone_shape, `build_mutual_shape, `finish_mutual_shape, `mutual_shape, `mutual_block_shape,
    `singleton_inductive_shape, `shared_inductive_shape, `familyFinish_pairs, `finish_inductive_shape,
    `family_layout, `familyInfo_layout, `dispatch_layout, `inductive_projection_resolves,
    `constructor_projection_resolves].map (`Ix.CompileCert.ProjectionLayout ++ ·)

/-- A mutual block's projections (CT-15, R9a): the rows the compiler emits,
their wire validity and codec, and what the certified reader resolves them
to. -/
def projectionRoots : Array Lean.Name :=
  (#[`indexed_rows, `constructor_rows, `memberStep_yield, `memberStep_rows, `members_rows, `classes_rows,
    `build_rows, `pushed_rows, `standalone_classes_rows, `standalone_rows, `empty_tables_wire, `member_wire,
    `constructor_wire, `source_rows_wire, `build_rows_wire, `build_rows_codec, `standalone_rows_wire,
    `build_projection_wire, `finish_projection_wire, `payload_projection_wire, `mutual_projection_wire,
    `mutual_codec, `member_resolves, `constructor_resolves, `selected_member, `class_member,
    `source_rows_resolve, `build_resolves].map (`Ix.CompileCert.MutualProjections ++ ·)) ++
  (#[`standalone_erase, `writeback_standalone, `sharing_standalone, `chosen_standalone, `build_cases,
    `selected_length, `no_ctor_references, `collapsed_references, `standalone_resolves, `build_resolves,
    `finish_references, `payload_references, `mutual_references,
    `mutual_correct].map (`Ix.CompileCert.MutualArtifact ++ ·))

/-- The compiler's classes agree (R9b): its sort is `sortClasses
Rules.compiler` on an address map of the unchanged state, two members of one
class match and so have one shape, and a sorted and compiled mutual block is
a correct artifact with no class premise, also in the driver's recursor-family
order (N5 a). -/
def mutualClassRoots : Array Lean.Name :=
  (#[`constAddrLookup_run, `sort_run].map (`Ix.CompileCert.ProjectionLayout ++ ·)) ++
  (#[`ctor_match_indices, `match_shape, `sorted_classes_agree,
    `sort_classes].map (`Ix.CompileCert.MutualProjections ++ ·)) ++
  (#[`mutual_sorted_correct, `orderRecursorFamily_perm, `ordered_partition, `ordered_agree,
    `mutual_ordered_correct].map (`Ix.CompileCert.MutualArtifact ++ ·))

/-- The reader's recursor index (CT-16, R10a, re-derived for D8): the
builder's two loops and one candidate inversion, validated block shapes,
provenance and grouping, the reader's lookups, per-motive coverage and one
recursor per motive. -/
def indexRoots : Array Lean.Name :=
  (#[`run_eq, `candidate_step, `valid_empty, `shapes_insert, `supported_insert_shape, `added_valid,
    `candidate_valid, `record_valid, `collect_valid, `complete_valid, `run_shapes, `buildIndex_shapes,
    `singleton_inductives, `array_one, `singleton_order, `buildIndex_singleton_order, `compiled_order,
    `recs_insert_extends, `provenance_insert, `grouped_extends, `grouped_empty_insert, `found_getD,
    `found_insert, `origins_empty, `added_origins, `candidate_origins, `record_origins, `collect_origins,
    `complete_origins, `buildIndex_valid, `entry_stored, `grouped_entry, `member_source, `member_unique,
    `member_lookup, `entry_lookup, `grouped_lookup].map (`Ix.CompileCert.ReaderIndex ++ ·)) ++
  (#[`from_role_unique, `found_push_extends, `added_recs, `added_found, `backed_added, `candidate_transition,
    `covered_extends, `candidate_covers, `valid_empty, `candidate_next, `record_next, `record_covers,
    `collect_covers, `complete_pair, `complete_preserves, `complete_covers, `complete_recs, `buildIndex_covers,
    `buildIndex_unique_reference, `one_push, `candidate_unique, `collect_unique, `collect_backed,
    `buildIndex_role_unique].map (`Ix.CompileCert.ReaderIndexDiscovery ++ ·))

/-- Compiled standalone inductives are read back as their sources (CT-16,
R10a): the reader's inductive block as named steps, its loops on a
one-member block, what the compiled family keeps of the source, and public
dispatch composed with `readRecord` = `lowerInductive` of the source's
`BlockRead`, its self references from `NoCtorIn` and the family's name related
to its key (N-READS N4 a). -/
def inductiveReadRoots : Array Lean.Name :=
  #[`readInductive_eq, `blockSelf_blobs, `readRecord_inductive, `indcs_singleton, `typeLoop, `ctorStep_ok,
    `ctorLoop_ok, `ctorClassLoop, `readRecord_singleton, `blockSelf_singleton, `erase_singleton,
    `headers_transfer, `family_headers, `familyInfo_headers, `erase_family, `piTeleLen_of_piTypes,
    `arity_of_related, `rootsRead_split, `ctorFacts_of, `ctorReads_source, `forall₂_map_left, `rootsRead_cons,
    `noCtorIn_iff, `familyCtx_lookup, `scope_of_noCtor, `inductive_reads,
    `inductive_reads_indexed,
    `inductive_declines_unindexed].map (`Ix.CompileCert.InductiveReading ++ ·)

/-- The shared loop lemmas (`Ix.CompileCert.Loop`): folds in `Id`, loops
that push or exit, invariants of fallible loops, and `List.mapM`. -/
def loopRoots : Array Lean.Name :=
  #[`except_bind_ok, `except_pure_ok, `idBind, `idPure, `forIn_id_list, `forIn_id_array, `forIn_exit,
    `forIn_exit_array, `exit_of_fst, `pushed_of_fst, `forIn_all_some, `no_exit, `forall₂_append, `forIn_inv,
    `forIn_inv_array, `forIn_push_array, `mapM_forall₂].map (`Ix.CompileCert.Loop ++ ·)

/-- What Source mode admits of an inductive block (R12): `inductiveGroup`
and `convertInductive` read (positions, safety, parameters, telescopes),
the compiler's constructor resolution as environment lookups, and
`inductive_reads` with its Source premises discharged by Source admission. -/
def sourceRoots : Array Lean.Name :=
  #[`memberValue_some, `ctorValue_some, `ctorsValue_forall₂, `forall₂_some_unique, `inductiveGroup_spec,
    `flush_ok, `exprsOf_spec, `drop_cons, `drop_of_append, `forall₂_getElem?, `getElem!_of_toList, `telescope_at,
    `items_layout, `convertInductive_spec, `strip_of_ingress, `find_ok, `find_run, `collect_lookups,
    `collectMut_lookups, `mkIndc_lookups, `inductiveGroup_cases, `admits_layout, `forall₂_mem, `ctors_agree,
    `admitted_member, `forall₂_mono_mem, `source_premises, `mkIndc_positions,
    `inductive_reads_source].map (`Ix.CompileCert.SourceConstructorPositions ++ ·)

/-- Pass 1's comparator is a total preorder on its ok-domain at a fixed
context (CS-01): the preorder combinators, the level, reference, expression
and constant comparisons, `nameCompareExact` lawful, and
the comparisons under two contexts (strength, `eq` monotonicity). -/
def canonOrderRoots : Array Lean.Name :=
  #[`le_ok, `Le.ok, `not_le_error, `PreOn.mono, `PreOn.comap, `PreOn.congr, `PreOn.swap_iff, `PreOn.refl,
    `PreOn.lt_of_lt_le, `PreOn.lt_of_le_lt, `PreOn.eq_trans, `PreOn.pureCmp, `PreOn.const_eq, `cmpM_ok,
    `lexIf_error, `lexIf_okLeft, `lexIf_ok, `PreOn.cmpM, `PreOn.lexIf, `PreOn.ofTag, `PreOn.ofGood,
    `PreOn.empty, `PreOn.ofSizeOn, `PreOn.ofSize, `zipM_cons, `zipM_nil_nil, `zipM_nil_cons, `zipM_cons_nil,
    `PreOn.zipCtx, `cmpM_pure, `transCmp_of_total, `univC_total, `compareUniv_eq_iff, `compareLevel_total,
    `compareLevels_eq, `compareLevels_total, `addr_beq_iff, `addr_data_inj, `transCmp_comap,
    `address_compare_eq_iff, `name_beq_iff, `name_beq_refl, `name_beq_symm, `name_beq_trans, `name_beq_comm,
    `name_beq_of_eq, `nameCompare_eq_iff, `cmpHash_eq, `cmpRaw_str, `cmpRaw_num, `rawC_total, `cmpRaw_eq_iff,
    `nameCompareExact_eq, `nameCompareExact_eq_iff, `nameEq_true, `nameEq_false, `nameEq_comm,
    `compareRef_self, `compareRef_in_in,
    `compareRef_in_out, `compareRef_out_in, `compareRef_out_out, `compareExternal_swap, `ne_of_refTag,
    `compareRef_total, `literal_compare_natVal, `literal_compare_strVal, `literal_total, `ehd_spec,
    `ehd_of_HN, `HN_etag_lt, `NotVar_of_ehd, `cE_mdata_left, `cE_mdata_right, `compareExpr_strip_lt,
    `compareExpr_strip, `compareExpr_bad_lt, `compareExpr_bad, `compareExpr_diff, `etag_eq_mdata,
    `cE_contract,
    `compareExpr_total, `cmp_true, `compareDef_total, `ctorP_total, `indHeader_eq, `indP_total,
    `compareRule_total, `compareRecr_total, `constP_total, `cE_bvar, `cE_sort, `cE_const, `cE_app, `cE_lam,
    `cE_forallE, `cE_letE, `cE_lit, `cE_proj, `ResRel.zipCtx, `compareExpr_rel, `compareDef_rel, `ctorP_rel,
    `indP_rel, `compareRecr_rel, `constP_rel, `strongRel, `compareRef_strong, `constP_strong, `ctorP_strong,
    `eqRel, `compareRef_eq_mono, `constP_eq_mono].map (`Ix.CompileCert.Canon ++ ·)

/-- Pass 1's classes (CS-01): the strong-result cache returns the pure
comparison, the merge sort sorts, `List.groupByM` groups adjacent equals,
the class context's values, the code is the pure refinement, one round's
specification, and the coarsest consistent partition (`sortClasses_coarsest`). -/
def canonClassRoots : Array Lean.Name :=
  #[`cacheKey_eq, `mem_ents_mem, `mem_ents_ctor, `entP_swap, `entP_strong,
    `Run.Adm.sameDom, `coh_empty, `Sim.pure', `Sim.bind, `Sim.liftE', `Sim.congr, `Sim.cmpM, `Sim.zipM,
    `cacheGet_run, `cachePut_run, `cacheGet_spec, `cachePut_coh, `liftE_run, `cached_sim, `compareCtor_sim,
    `compareInd_sim, `compareConstBody_sim, `Run.adm_ctxOf, `compareConst_sim, `PreOn.ord, `constOrd_total,
    `sorted_cons_cons, `sorted_tail, `sorted_cons, `sorted_append_single, `leC_of_gt, `mergeM_spec,
    `runs_spec, `mergePairs_spec, `mergeAll_spec, `sortByM_spec, `mergeM_sim, `runs_sim, `mergePairs_sim,
    `mergeAll_sim, `sortByM_sim, `sorted_append_iff, `groupsOK_extend, `groupsOK_new, `groupGoP_spec,
    `groupAdjP_spec, `lastRev_append_single, `groupByMAux_eq, `groupByM_eq, `lastRev_length,
    `lastRev_getElem_mem, `mem_lastRev, `groupByMAux_sim, `groupByM_sim, `ctx_eq, `foldl_max, `ctor_fold,
    `class_fold, `classes_fold, `ctx_fold, `treeMap_insert_self, `treeMap_insert_ne, `foldl_insP_getElem?,
    `KeysDistinct.perm, `map_zipIdx_fst, `keys_pairsOf, `offs_zero, `offs_cons_succ, `keys_ctxPairs,
    `mem_pairsOf, `mem_ctxPairs, `default_getElem?, `KeysDistinct.ne, `ctx_lookup, `ctx_member, `ctx_ctor,
    `ctx_val, `ctx_dom, `maxC_ge, `offs_succ, `offs_mono, `slot_disjoint, `class_index, `ctx_merge,
    `insertByName_perm, `sortByName_perm, `seedOf_perm, `map_sortByName_flatten_perm, `lastRev_flatten_perm,
    `ents_names, `pairwise_map_inj, `KeysDistinct.nameInj, `ctx_dom_perm, `constOrd_oriented,
    `refineClassP_perm, `refineClassesP_perm, `refineClass_sim, `refineClasses_sim, `sortLoop_sim,
    `sortClasses_eq, `ord_swap, `le_of_ok, `ok_of_le, `eq_symm', `eq_trans', `lt_of_lt_le', `lt_of_le_lt',
    `sorted_getElem, `sorted_flatten_adjacent, `eqOf_true, `eqOf_false, `group_eq, `group_eq_mem,
    `groups_lt, `repOf_length, `repOf_getElem_mem, `mem_repOf, `refineClassP_spec, `same_group_of_eq,
    `refineClassesP_spec, `coarser_ctxOf, `constOrd_eq_mono, `sortLoopP_spec, `sortClassesP_coarsest,
    `sortClasses_coarsest].map (`Ix.CompileCert.Canon ++ ·)

/-- What Pass 1's `eq` means (CS-01): an `eq` comparison relates the two
sides by `ExprEq`/`ConstMatch` (the comparator's identifications), and two
members of one class of `sortClasses` match under the classes' context. -/
def canonEqRoots : Array Lean.Name :=
  #[`cmpM_eq_parts, `lexIf_eq_parts, `pure_eq_nat, `zipM_eq, `literal_compare_eq, `forall₂_imp,
    `defKind_compare_eq, `bool_compare_eq, `compareLevel_eq_sound, `compareLevels_eq_sound,
    `compareRef_eq_sound, `exprEq_strip_left, `exprEq_strip_right, `compareExpr_eq_sound,
    `ctorKeys_eq_sound, `compareDef_eq_sound, `indP_eq_sound, `compareRecr_eq_sound, `constP_eq_sound,
    `constOrd_eq_sound, `sortClasses_match].map (`Ix.CompileCert.Canon ++ ·)

/-- The preseed's definitions the preseed proofs unfold. `preseedExprTables` and
`collectExprTables` run as their proved-equal worklists (the CQ2.9 `@[csimp]`
theorems `preseedExprTables_eq_worklist`, `collectExprTables_eq_worklist`,
roots of `IxSharingVerify.Audit.Statements`), so they are not listed. -/
def preseedRuntime : Array Lean.Name :=
  #[``Ix.CompileM.collectPreseedExprs,
    ``Ix.CompileM.collectExprTablesStructural, ``Ix.CompileM.collectExprTableUnivs,
    ``Ix.CompileM.internPreseedRefs, ``Ix.CompileM.canonPreseedUnivs, ``Ix.CompileM.internPreseedUnivs,
    ``Ix.CompileM.withUnivCtx, ``Ix.CompileM.univParamsKey, ``Ix.CompileM.univSortKey,
    ``Ix.CompileM.byteArrayCmp]

/-- The expression compiler's definitions the expression proofs unfold, and
Source mode's term conversion the correspondence is about. -/
def expressionRuntime : Array Lean.Name :=
  #[``Ix.CompileM.compileExprNoSurgery, ``Ix.CompileM.compileExprNoSurgeryStep, ``Ix.CompileM.compileExpr,
    ``Ix.CompileM.CompileEnv.surgeryFree, ``Ix.CompileM.compileConstExprRaw, ``Ix.CompileM.lookupConstAddr,
    ``Ix.CompileM.allocArenaNode, ``Ix.CompileM.pushUnivPatch, ``Ix.CompileM.compileAndInternUnivCanon,
    ``Ix.AuxGen.decomposeApps, ``Ix.AuxGen.decomposeApps.go, ``Ix.SemanticContract.hasMetadata,
    ``Ix.SemanticContract.read, ``Ix.SemanticContract.Contract.lower, ``Ix.LeanIngress.ingressExpr,
    ``Ix.LeanIngress.ingressMData, ``Ix.LeanIngress.withContract, ``Ix.LeanIngress.ingressLevel,
    ``Ix.LeanIngress.ingressKey]

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
    ``Ix.CompileM.compileDataValue, ``Ix.CompileM.compileKVMap, ``Ix.CompileM.checkPreseedUnivs,
    ``Ix.CompileM.BlockState.cacheUniv, ``Ix.Compile.ExactKey.nameIndex, ``Ix.CompileM.compileUniv]

def readerRuntime : Array Lean.Name :=
  #[``Ix.Kernel.Reader.convExpr, ``Ix.Kernel.Reader.MemberReader.mk',
    ``Ix.Kernel.Reader.MemberReader.read, ``Ix.Kernel.Reader.ECx.keyAt,
    ``Ix.Kernel.Reader.ECx.blobAt, ``Ix.Kernel.Reader.ECx.levels, ``Ix.Kernel.Reader.Ctx.keyAt]

/-- The payload emitters, their finishers and drains, which the emission
proofs unfold. -/
def emissionRuntime : Array Lean.Name :=
  #[``Ix.CompileM.takeArena, ``Ix.CompileM.takeSurgerySharing, ``Ix.CompileM.takeUnivPatches,
    ``Ix.CompileM.clearExprCache, ``Ix.CompileM.resetArena, ``Ix.CompileM.recordDefHints,
    ``Ix.CompileM.getMutCtxAddrs, ``Ix.CompileM.withCurrent, ``Ix.CompileM.withMutCtx,
    ``Ix.CompileM.withBlockEnv, ``Ix.CompileM.finishDefinitionDataCompilation,
    ``Ix.CompileM.compileDefinitionData, ``Ix.CompileM.finishAxiomCompilation, ``Ix.CompileM.compileAxiom,
    ``Ix.CompileM.finishQuotientCompilation, ``Ix.CompileM.compileQuotient,
    ``Ix.CompileM.compileRecursorRule, ``Ix.CompileM.compileRecursorRules,
    ``Ix.CompileM.finishRecursorCompilation, ``Ix.CompileM.compileRecursor,
    ``Ix.CompileM.finishConstructorCompilation, ``Ix.CompileM.compileConstructor,
    ``Ix.CompileM.compileInductiveConstructors, ``Ix.CompileM.takeInductiveTypeCompileMeta,
    ``Ix.CompileM.finishInductiveCompilation, ``Ix.CompileM.compileInductive,
    ``Ix.CompileM.finishInductiveDataCompilation, ``Ix.CompileM.compileInductiveData,
    ``Ix.CompileM.compileMutConstMember, ``Ix.CompileM.compileEquivalentMutConsts,
    ``Ix.CompileM.compileMutConstClass, ``Ix.CompileM.compileMutConstClasses,
    ``Ix.CompileM.compileMutConsts]

/-- The sharing builder's root extraction and write-back, which the sharing
proofs unfold (the construction itself, `canonicalSharingTiered`, is audited
by `IxSharingVerify`). -/
def sharingRuntime : Array Lean.Name :=
  #[``Ix.CompileM.buildConstantWithSharing, ``Ix.CompileM.withRootExprs,
    ``Ix.CompileM.constantInfoRootExprs, ``Ix.CompileM.mutConstRootExprs,
    ``Ix.Sharing.Exact.withRoots, ``Ix.Sharing.Exact.withMutConstRoots, ``Ix.Sharing.Exact.takeRoot,
    ``Ix.Sharing.Exact.takeRoots, ``Ix.Sharing.Exact.constantInfoRoots, ``Ix.Sharing.Exact.mutConstRoots]

/-- The block finishers and the preseeded singleton block compilers, which
the block proofs unfold. -/
def blockRuntime : Array Lean.Name :=
  #[``Ix.CompileM.finishConstantInfoWithSharing, ``Ix.CompileM.finishConstantWithSharing,
    ``Ix.CompileM.buildBlockConstant, ``Ix.CompileM.liftSharing, ``Ix.CompileM.BlockResult.mk',
    ``Ix.CompileM.compileDefinitionDataBlock, ``Ix.CompileM.compileDefinitionDataInfo,
    ``Ix.CompileM.compileAxiomBlock, ``Ix.CompileM.compileAxiomInfo, ``Ix.CompileM.compileQuotientBlock,
    ``Ix.CompileM.compileQuotientInfo, ``Ix.CompileM.compileRecursorBlock, ``Ix.CompileM.compileRecursorInfo,
    ``Ix.CompileM.compileInductiveFamilyBlock, ``Ix.CompileM.compileInductiveFamilyInfo,
    ``Ix.CompileM.finishInductiveFamilyBlock, ``Ix.CompileM.buildInductiveProjections]

/-- The public dispatch, constructor resolution and
the mutual block's finisher, which the dispatch proofs unfold. -/
def dispatchRuntime : Array Lean.Name :=
  #[``Ix.CompileM.compileConstantInfo,
    ``Ix.CompileM.compileConstantInfoCore, ``Ix.CompileM.compileDefinitionConstantInfo,
    ``Ix.CompileM.compileTheoremConstantInfo, ``Ix.CompileM.compileOpaqueConstantInfo,
    ``Ix.CompileM.compileQuotientConstantInfo, ``Ix.CompileM.compileRecursorConstantInfo,
    ``Ix.CompileM.compileInductiveConstantInfo, ``Ix.CompileM.compileConstructorConstantInfo,
    ``Ix.CompileM.compileDefinitionInfo, ``Ix.CompileM.compileTheoremInfo, ``Ix.CompileM.compileOpaqueInfo,
    ``Ix.CompileM.compileInductiveInfo, ``Ix.CompileM.compileConstructorInfo,
    ``Ix.CompileM.lookupInductiveConstructors, ``Ix.CompileM.collectInductiveConstructors,
    ``Ix.CompileM.findConst, ``Ix.CompileM.checkMutConstArrayCounts, ``Ix.CompileM.checkMutualPayloadCounts,
    ``Ix.CompileM.standaloneMutConstInfo?, ``Ix.CompileM.buildCompiledMutualBlock,
    ``Ix.CompileM.finishMutualCompilation, ``Ix.CompileM.compileMutualPayload, ``Ix.CompileM.compileMutualBlock]

/-- The record reader's functions the reading proofs unfold. -/
def recordReaderRuntime : Array Lean.Name :=
  #[``Ix.Kernel.Reader.readRecord, ``Ix.Kernel.Reader.readDefinition, ``Ix.Kernel.Reader.lowerDefinition,
    ``Ix.Kernel.Reader.safetyDeclineOf, ``Ix.Kernel.Reader.Ctx.memberKey]

/-- The reader's syntactic walks and the recursor analysis the spine proofs
unfold, and the kernel term views their statements use. -/
def spineRuntime : Array Lean.Name :=
  #[``Ix.Kernel.Reader.unshare, ``Ix.Kernel.Reader.unshare.go, ``Ix.Kernel.Reader.stripAll,
    ``Ix.Kernel.Reader.stripAllFull, ``Ix.Kernel.Reader.appHead, ``Ix.Kernel.Reader.headRef,
    ``Ix.Kernel.Reader.analyseRecursor, ``Ix.Kernel.Reader.resolve, ``Ix.Kernel.Reader.keyOfAddress,
    ``Ix.Kernel.Expr.stripPis, ``Ix.Kernel.Expr.getAppFn]

/-- The class sort, the projection builders and the reader's reference
resolution, which the layout and projection proofs unfold. -/
def layoutRuntime : Array Lean.Name :=
  #[``Ix.CompileM.sortConsts, ``Ix.CompileM.throwCmpError, ``Ix.CompileM.constAddrLookup,
    ``Ix.Compile.Canon.sortClasses, ``Ix.Kernel.Reader.resolveSource, ``Ix.Kernel.Reader.emptyTables,
    ``Ix.CompileM.buildMutualProjections, ``Ix.CompileM.buildStandaloneMutualProjections]

/-- The reader's recursor index builder, which the index proofs unfold. -/
def indexRuntime : Array Lean.Name :=
  #[``Ix.Kernel.Reader.buildIndex, ``Ix.Kernel.Reader.recursorMembers]

/-- The reader's inductive block and its lowering, which the inductive
reading proofs unfold and state. -/
def inductiveReadRuntime : Array Lean.Name :=
  #[``Ix.Kernel.Reader.readInductive, ``Ix.Kernel.Reader.lowerInductive, ``Ix.Kernel.Reader.piTeleLen,
    ``Ix.Kernel.Reader.inductiveAt]

/-- Source mode's inductive group and conversion, and the compiler's
constructor resolution, which the Source admission proofs unfold. -/
def sourceRuntime : Array Lean.Name :=
  #[``Ix.LeanIngress.inductiveGroup, ``Ix.LeanIngress.convertInductive, ``Ix.LeanIngress.convert,
    ``Ix.LeanIngress.exprsOf, ``Ix.LeanIngress.ingressExpr, ``Ix.LeanIngress.ingressMData,
    ``Ix.LeanIngress.withContract, ``Ix.CompileM.findConst, ``Ix.CompileM.collectMutConstConstructors,
    ``Ix.CompileM.MutConst.mkIndc]

/-- Pass 1's comparator and refinement, which the class proofs unfold. -/
def canonRuntime : Array Lean.Name :=
  #[``Ix.Compile.Canon.toUniv, ``Ix.Compile.Canon.compareUniv, ``Ix.Compile.Canon.compareLevel,
    ``Ix.Compile.Canon.compareLevels, ``Ix.Compile.Canon.compareExternal, ``Ix.Compile.Canon.compareRef,
    ``Ix.Compile.Canon.compareExpr, ``Ix.Compile.Canon.liftE, ``Ix.Compile.Canon.cacheKey,
    ``Ix.Compile.Canon.cacheGet, ``Ix.Compile.Canon.cachePut, ``Ix.Compile.Canon.compareDef,
    ``Ix.Compile.Canon.compareCtorKeys, ``Ix.Compile.Canon.compareCtor, ``Ix.Compile.Canon.compareCtors,
    ``Ix.Compile.Canon.indHeader, ``Ix.Compile.Canon.compareInd, ``Ix.Compile.Canon.compareRule,
    ``Ix.Compile.Canon.compareRecr, ``Ix.Compile.Canon.kindTag, ``Ix.Compile.Canon.compareConstBody,
    ``Ix.Compile.Canon.compareConst, ``Ix.Compile.Canon.insertByName, ``Ix.Compile.Canon.sortByName,
    ``Ix.Compile.Canon.refineClass, ``Ix.Compile.Canon.refineClasses, ``Ix.Compile.Canon.sortLoop,
    ``Ix.Compile.Canon.sortClasses, ``Ix.MutConst.ctx, ``Ix.nameCompare, ``Ix.nameCompareExact,
    ``Ix.Name.cmpRaw, ``Ix.Name.cmpHash, ``List.sortByM, ``List.sequencesM, ``List.descendingM,
    ``List.ascendingM, ``List.mergeAllM, ``List.mergeAllMFuel, ``List.mergePairsM, ``List.mergeM,
    ``List.groupByM, ``List.groupByMAux, ``SOrder.cmpM, ``SOrder.zipM, ``SOrder.cmp, ``SOrder.cmpMany]


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
  checkRoots (tag := "reading-audit") "wire tables" Ix.CompileCert.ReadingAudit.wireRoots
  checkRoots (tag := "reading-audit") "universe meaning" Ix.CompileCert.ReadingAudit.meaningRoots
  checkRoots (tag := "reading-audit") "universe pipeline" Ix.CompileCert.ReadingAudit.pipelineRoots
  checkRoots (tag := "reading-audit") "expression core" Ix.CompileCert.ReadingAudit.expressionRoots
  checkRoots (tag := "reading-audit") "preseed state" Ix.CompileCert.ReadingAudit.preseedStateRoots
  checkRoots (tag := "reading-audit") "preseed coverage" Ix.CompileCert.ReadingAudit.coverageRoots
  checkRoots (tag := "reading-audit") "emission wire" Ix.CompileCert.ReadingAudit.emissionWireRoots
  checkRoots (tag := "reading-audit") "sharing roots" Ix.CompileCert.ReadingAudit.sharingRootRoots
  checkRoots (tag := "reading-audit") "emitters" Ix.CompileCert.ReadingAudit.emissionRoots
  checkRoots (tag := "reading-audit") "blocks" Ix.CompileCert.ReadingAudit.blockRoots
  checkRoots (tag := "reading-audit") "dispatch" Ix.CompileCert.ReadingAudit.dispatchRoots
  checkRoots (tag := "reading-audit") "singleton reading" Ix.CompileCert.ReadingAudit.singletonReadRoots
  checkRoots (tag := "reading-audit") "reader walks" Ix.CompileCert.ReadingAudit.spineRoots
  checkRoots (tag := "reading-audit") "mutual layout" Ix.CompileCert.ReadingAudit.layoutRoots
  checkRoots (tag := "reading-audit") "mutual projections" Ix.CompileCert.ReadingAudit.projectionRoots
  checkRoots (tag := "reading-audit") "mutual classes" Ix.CompileCert.ReadingAudit.mutualClassRoots
  checkRoots (tag := "reading-audit") "reader index" Ix.CompileCert.ReadingAudit.indexRoots
  checkRoots (tag := "reading-audit") "inductive reading" Ix.CompileCert.ReadingAudit.inductiveReadRoots
  checkRoots (tag := "reading-audit") "loops" Ix.CompileCert.ReadingAudit.loopRoots
  checkRoots (tag := "reading-audit") "canon order" Ix.CompileCert.ReadingAudit.canonOrderRoots
  checkRoots (tag := "reading-audit") "canon classes" Ix.CompileCert.ReadingAudit.canonClassRoots
  checkRoots (tag := "reading-audit") "canon eq" Ix.CompileCert.ReadingAudit.canonEqRoots
  checkRoots (tag := "reading-audit") "source admission" Ix.CompileCert.ReadingAudit.sourceRoots
  checkRuntime (tag := "reading-audit") "tables, blobs and serializers"
    Ix.CompileCert.ReadingAudit.tableRuntime
  checkRuntime (tag := "reading-audit") "reader" Ix.CompileCert.ReadingAudit.readerRuntime
  checkRuntime (tag := "reading-audit") "expression compiler" Ix.CompileCert.ReadingAudit.expressionRuntime
  checkRuntime (tag := "reading-audit") "preseed" Ix.CompileCert.ReadingAudit.preseedRuntime
  checkRuntime (tag := "reading-audit") "emission" Ix.CompileCert.ReadingAudit.emissionRuntime
  checkRuntime (tag := "reading-audit") "sharing" Ix.CompileCert.ReadingAudit.sharingRuntime
  checkRuntime (tag := "reading-audit") "blocks" Ix.CompileCert.ReadingAudit.blockRuntime
  checkRuntime (tag := "reading-audit") "dispatch" Ix.CompileCert.ReadingAudit.dispatchRuntime
  checkRuntime (tag := "reading-audit") "record reader" Ix.CompileCert.ReadingAudit.recordReaderRuntime
  checkRuntime (tag := "reading-audit") "reader walks" Ix.CompileCert.ReadingAudit.spineRuntime
  checkRuntime (tag := "reading-audit") "mutual layout" Ix.CompileCert.ReadingAudit.layoutRuntime
  checkRuntime (tag := "reading-audit") "reader index" Ix.CompileCert.ReadingAudit.indexRuntime
  checkRuntime (tag := "reading-audit") "inductive reading" Ix.CompileCert.ReadingAudit.inductiveReadRuntime
  checkRuntime (tag := "reading-audit") "source admission" Ix.CompileCert.ReadingAudit.sourceRuntime
  checkRuntime (tag := "reading-audit") "canon" Ix.CompileCert.ReadingAudit.canonRuntime

/-! ## N-READS, N2: levels read syntactically

Since IxC's U lowers Source levels to the compiler's canonical form
(`Ix.LeanIngress.canonLevelIn`), the reader's level is the Source level in that
form, not only equal to it in value (`CanonLevelReading.related_ingress_canon`). -/

def Ix.CompileCert.ReadingAudit.levelCanonRoots : Array Lean.Name :=
  #[`idxIn_map, `univOfLevel_ingress, `levelOfUniv_eq_convUniv, `canonLevelIn_ingress,
    `levelMeaning_canon, `related_ingress_canon].map (`Ix.CompileCert.CanonLevelReading ++ ·)

/-- info: [reading-audit] levels canonically: 6 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd checkRoots (tag := "reading-audit") "levels canonically" Ix.CompileCert.ReadingAudit.levelCanonRoots

/-! ## N-READS, N5 b: inductives through the driver's mutual path

The driver compiles every inductive block, singletons included, through
`compileMutualBlock` over `MutConst.mkIndc` members
(`Ix.CompileCert.MutualInductiveReading`). For a block of one inductive: the
member emitter is the family path's, the class's mutual context is the
family's, the driver's sort and recursor-family order keep the one class, and
the block reads back as its source (`inductive_reads_driver`), with its Source
premises from Source admission (`inductive_reads_driver_source`). -/

def Ix.CompileCert.ReadingAudit.driverInductiveRoots : Array Lean.Name :=
  #[`mutConsts_indc, `mutCtx_singleton, `mutBlock_family, `singletonBlock_correct, `singleton_headers,
    `sortClasses_singleton, `orderRecursorFamily_singleton, `driver_singleton, `mkIndc_constructors,
    `inductive_reads_mutual, `inductive_reads_driver,
    `inductive_reads_driver_source].map (`Ix.CompileCert.MutualInductiveReading ++ ·)

/-- The driver's recursor-family order and the family's mutual context, which
the driver-path proofs unfold. -/
def Ix.CompileCert.ReadingAudit.driverInductiveRuntime : Array Lean.Name :=
  #[``Ix.CompileM.orderRecursorFamily, ``Ix.CompileM.buildInductiveMutCtx]

/-- info: [reading-audit] driver inductives: 12 roots; axioms used: [propext, Classical.choice, Quot.sound]
---
info: [reading-audit] driver inductives: 2 safe definitions, no runtime substitution -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots checkRuntime) in
run_cmd do
  checkRoots (tag := "reading-audit") "driver inductives" Ix.CompileCert.ReadingAudit.driverInductiveRoots
  checkRuntime (tag := "reading-audit") "driver inductives" Ix.CompileCert.ReadingAudit.driverInductiveRuntime

/-- info: [reading-audit] metadata state: 3 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "reading-audit") "metadata state"
    #[`Ix.CompileCert.RecordState.Step.pure, `Ix.CompileCert.RecordState.Step.bind,
      `Ix.CompileCert.RecordState.compileExprMeta_preserves]

/-- info: [reading-audit] record subrun: 3 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "reading-audit") "record subrun"
    #[`Ix.CompileCert.RecordState.compileRecords_preserves, `Ix.CompileCert.RecordRead.ordinary_subrun,
      `Ix.CompileCert.RecordRead.withRecords_read]

/-- info: [reading-audit] decorated contract arity: 1 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "reading-audit") "decorated contract arity"
    #[`Ix.CompileCert.RecordSourceShape.decorateExpr_canonical]

/-- info: [reading-audit] source contract arity: 3 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "reading-audit") "source contract arity"
    #[`Ix.CompileCert.RecordSourceShape.decorate_constant, `Ix.CompileCert.RecordSourceShape.ingress,
      `Ix.CompileCert.RecordSourceShape.canonical_ingress]

/-- info: [reading-audit] record substitution producer: 1 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "reading-audit") "record substitution producer"
    #[`Ix.CompileCert.RecordSubst.produced]

/-- info: [reading-audit] record substitution reading: 2 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "reading-audit") "record substitution reading"
    #[`Ix.CompileCert.RecordSubst.substRecords_related, `Ix.CompileCert.RecordSubst.withRecords_read]

/-- info: [reading-audit] rewrite arity primitives: 9 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "reading-audit") "rewrite arity primitives"
    (#[`substLevels, `liftP, `lowerP, `liftM, `lowerM, `share, `shareInput, `decorated_levels,
      `decorated_liftM].map (`Ix.CompileCert.RewriteArityPrimitives ++ ·))

/-- info: [reading-audit] development arity leaves: 7 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "reading-audit") "development arity leaves"
    (#[`empty, `insert, `probe, `helperFrames, `spine, `field, `shareAppN_run].map
      (`Ix.CompileCert.DevelopmentArity ++ ·))

/-- info: [reading-audit] development arity recursion: 2 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "reading-audit") "development arity recursion"
    #[`Ix.CompileCert.DevelopmentArity.hinst_run, `Ix.CompileCert.DevelopmentArity.happ_run]

/-- info: [reading-audit] development arity history: 4 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "reading-audit") "development arity history"
    (#[`history_sound, `instantiateWith_produced, `instantiateWith_fresh, `instantiate_fresh].map
      (`Ix.CompileCert.DevelopmentArity ++ ·))

/-- info: [reading-audit] semantic inspection traversal: 10 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "reading-audit") "semantic inspection traversal"
    (#[`frames_iff, `children_weight, `inspect_eq, `scan_eq, `step_fresh, `covered_frames,
      `covered_seen, `covered_next, `initial, `next_decreases].map
      (`Ix.CompileCert.SemanticFrames ++ ·))

/-- info: [reading-audit] semantic inspection validity: 1 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "reading-audit") "semantic inspection validity"
    #[`Ix.CompileCert.SemanticFrames.inspect_frames_iff]

/-- info: [reading-audit] semantic source presence and acceptance: 8 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "reading-audit") "semantic source presence and acceptance"
    (#[`Ix.Compile.SemanticPresence.go_result, `Ix.Compile.SemanticPresence.runWith_eq_spec,
      `Ix.Compile.SemanticPresence.run_eq_spec] ++
      (#[`spec_false_canonical, `production_absent, `source_absent, `guard_frames, `prepared_member_frames].map
        (`Ix.CompileCert.SemanticPresence ++ ·)))

/-- info: [reading-audit] semantic frame primitives: 13 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "reading-audit") "semantic frame primitives"
    (#[`shell_refl, `fits_liftP, `fits_lowerP, `liftP, `lowerP, `fits_shell, `mdata_root_shell,
      `substLevels, `abstractFVars, `liftM, `lowerM, `share_eq, `shareInput_eq].map
      (`Ix.CompileCert.FramePrimitives ++ ·))

/-- info: [reading-audit] semantic development cache: 6 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "reading-audit") "semantic development cache"
    (#[`empty, `insert, `probe, `probe_fits, `spine, `field].map (`Ix.CompileCert.DevelopmentFrames ++ ·))

/-- info: [reading-audit] semantic development workers: 3 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "reading-audit") "semantic development workers"
    (#[`shareAppN_run, `hinst_run, `happ_run].map (`Ix.CompileCert.DevelopmentFrames ++ ·))

/-- info: [reading-audit] semantic development histories: 6 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "reading-audit") "semantic development histories"
    (#[`history_sound, `instantiateWith_produced, `instantiateWith_fresh, `instantiate_fresh,
      `instantiateWith_inspected, `instantiateWith_fresh_inspected].map (`Ix.CompileCert.DevelopmentFrames ++ ·))

/-- info: [reading-audit] frontend and development call receipts: 5 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "reading-audit") "frontend and development call receipts"
    (#[`compileLeanInput_prefix, `compileDecoratedConsts_guards, `compileLeanInput_members,
      `compileLeanInput_frames, `development_call].map (`Ix.CompileCert.FrontendReceipts ++ ·))

/-- info: [reading-audit] unconditional development cache preservation: 4 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "reading-audit") "unconditional development cache preservation"
    (#[`insert_invalid, `hinst_state, `happ_state, `instantiateWith_state].map
      (`Ix.CompileCert.DevelopmentState ++ ·))

/-- info: [reading-audit] actual rewrite development call chains: 6 roots; axioms used: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Ix.CompileCert.UniverseAudit (checkRoots) in
run_cmd do
  checkRoots (tag := "reading-audit") "actual rewrite development call chains"
    (#[`Chain.append, `Chain.preserves, `expansionOf_calls, `rw_calls,
      `expansionOf_state, `rw_state].map (`Ix.CompileCert.RewriteCalls ++ ·))
