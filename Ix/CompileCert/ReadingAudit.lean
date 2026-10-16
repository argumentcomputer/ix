import Ix.CompileCert.UniverseAudit
import Ix.CompileCert.CacheSound
import Ix.CompileCert.Serializers
import Ix.CompileCert.PreseedValidation
import Ix.CompileCert.WireTables
import Ix.CompileCert.UniversePipeline
import Ix.CompileCert.ExpressionCorrectness
import Ix.CompileCert.ExpressionIngress
import Ix.CompileCert.PreseedWire
import Ix.CompileCert.FinalUniverses
import Ix.CompileCert.PreseedInsertion
import Ix.CompileCert.EmissionWire
import Ix.CompileCert.SharingRoots
import Ix.CompileCert.Emission

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
(`Ix.CompileCert.SharingRoots`) and the payload emitters (`Ix.CompileCert.Emission`).
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
  (#[`AllWidths.push, `frame_compileUniv, `frame_lookup, `frame_blob, `frame_collectUnivs,
    `frame_structural, `frame_collect, `frame_withUnivCtx, `collection_frame, `Widths.pure,
    `Widths.throw, `Widths.forget, `Widths.bind, `Widths.lookup, `Widths.blob, `widths_structural,
    `widths_collect, `collect_widths, `Wire.pure, `Wire.bind, `Wire.of_frame, `Wire.discard,
    `internRefs_wire, `internUnivs_wire, `canonUnivs_wire, `preseed_wire, `binding_internRefs,
    `binding_internUnivs, `binding_canonUnivs, `preseed_binding,
    `preseed_widths].map (`Ix.CompileCert.PreseedWire ++ ·)) ++
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
  checkRuntime (tag := "reading-audit") "tables, blobs and serializers"
    Ix.CompileCert.ReadingAudit.tableRuntime
  checkRuntime (tag := "reading-audit") "reader" Ix.CompileCert.ReadingAudit.readerRuntime
  checkRuntime (tag := "reading-audit") "expression compiler" Ix.CompileCert.ReadingAudit.expressionRuntime
  checkRuntime (tag := "reading-audit") "preseed" Ix.CompileCert.ReadingAudit.preseedRuntime
  checkRuntime (tag := "reading-audit") "emission" Ix.CompileCert.ReadingAudit.emissionRuntime
  checkRuntime (tag := "reading-audit") "sharing" Ix.CompileCert.ReadingAudit.sharingRuntime
