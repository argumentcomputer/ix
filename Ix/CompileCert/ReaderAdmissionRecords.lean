import Ix.CompileCert.ReaderStore
import Ix.CompileCert.MutualArtifact
import IxC.Kernel.Admission.Bytes.Theorems
import IxC.Kernel.Admission

/-! Production byte preparation supplies compatible decoded records and
preserves included compiler artifacts. These results use duplicate/decode
success before target reading, not successful kernel admission. -/

namespace Ix.CompileCert.ReaderAdmissionRecords

open Ix Kernel.Reader Kernel.Admission
open Ix.CompileM

theorem consistent_of_keys (records : Array (Address × Ixon.Constant))
    (unique : (records.toList.map Prod.fst).Nodup) : ReaderStore.Consistent records := by
  suffices sound : ∀ rows : List (Address × Ixon.Constant), (rows.map Prod.fst).Nodup →
      ∀ key left right, (key, left) ∈ rows → (key, right) ∈ rows → left = right from
    fun key left right first second => sound records.toList unique key left right
      (by simpa using first) (by simpa using second)
  intro rows
  induction rows with
  | nil => intro _ key left right first; simp at first
  | cons head rows ih =>
    intro unique key left right first second
    have nodup := List.nodup_cons.mp unique
    rcases List.mem_cons.mp first with same | later
    · cases same
      rcases List.mem_cons.mp second with same | later
      · exact (congrArg Prod.snd same).symm
      · exact False.elim (nodup.1 (List.mem_map.mpr ⟨(key, right), later, rfl⟩))
    · rcases List.mem_cons.mp second with same | last
      · cases same
        exact False.elim (nodup.1 (List.mem_map.mpr ⟨(key, left), later, rfl⟩))
      · exact ih nodup.2 key left right later last

theorem decoded_keys (limits : Limits) (records : Records) (constants : Kernel.Ingress.Constants)
    (decoded : decodeRecords limits records = .ok constants) : records.map Prod.fst = constants.map Prod.fst :=
  ((decodeRecords_ok_iff limits records constants).mp decoded).keys

/-- The real byte-stage checks supply decoded record compatibility without
assuming successful reading or target admission. -/
theorem decoded_consistent (limits : Limits) (records : Records) (blobs : Kernel.Ingress.Blobs)
    (constants : Kernel.Ingress.Constants) (unique : uniqueKeys records blobs = .ok ())
    (decoded : decodeRecords limits records = .ok constants) : ReaderStore.Consistent constants.toArray := by
  apply consistent_of_keys
  have keys := (uniqueKeys_ok_iff records blobs).mp unique
  have same := decoded_keys limits records constants decoded
  simpa only [List.toList_toArray, ← same] using keys.1

theorem reading_member {limits : Limits} {records : Records} {constants : Kernel.Ingress.Constants}
    (reading : RecordsRead limits records constants) (address : Address) (bytes : ByteArray)
    (present : (address, bytes) ∈ records) :
    ∃ constant, (address, constant) ∈ constants ∧ Ixon.deConstant bytes = .ok constant := by
  induction reading with
  | nil => simp at present
  | @cons owner payload constant rest constants read tail ih =>
    rcases List.mem_cons.mp present with same | later
    · cases same
      refine ⟨constant, by simp, ?_⟩
      rw [← read.encoded]
      exact Ixon.Verify.deConstant_serConstant constant read.wire
    · obtain ⟨constant, present, decoded⟩ := ih later
      exact ⟨constant, by simp [present], decoded⟩

theorem decoded_member (limits : Limits) (records : Records) (constants : Kernel.Ingress.Constants)
    (decoded : decodeRecords limits records = .ok constants) (address : Address) (bytes : ByteArray)
    (present : (address, bytes) ∈ records) :
    ∃ constant, (address, constant) ∈ constants ∧ Ixon.deConstant bytes = .ok constant :=
  reading_member ((decodeRecords_ok_iff limits records constants).mp decoded) address bytes present

/-- The decoder returns the exact compiler block whose bytes were included;
the output's proved codec supplies equality rather than a hash assumption. -/
theorem decoded_block (limits : Limits) (records : Records) (constants : Kernel.Ingress.Constants)
    (decoded : decodeRecords limits records = .ok constants) (output : BlockResult)
    (included : (output.blockAddr, output.blockBytes) ∈ records)
    (codec : Sharing.Verify.BlockResultCodecWF output) : (output.blockAddr, output.block) ∈ constants.toArray := by
  obtain ⟨constant, present, read⟩ := decoded_member limits records constants decoded output.blockAddr output.blockBytes included
  have same : constant = output.block := Except.ok.inj (read.symm.trans codec.2)
  subst constant
  simpa using present

/-- Checked publication supplies the byte-array membership consumed by the
actual decoder; its subsequent decoding retains the emitted main block. -/
theorem published_decoded_block (before : DriverAcc) (lo : Name) (output : BlockResult) (cache : BlockState)
    (accepted : checkCompiledBlock before.cenv lo output cache = .ok ())
    (codec : Sharing.Verify.BlockResultCodecWF output) (limits : Limits) (constants : Kernel.Ingress.Constants)
    (decoded : decodeRecords limits (mergeCompiledBlock before lo output cache).cenv.constants.toList = .ok constants) :
    (output.blockAddr, output.block) ∈ constants.toArray := by
  have stored := (Publication.checkCompiledBlock_present before lo output cache accepted).1
    output.blockAddr output.blockBytes List.mem_cons_self
  have included : (output.blockAddr, output.blockBytes) ∈ (mergeCompiledBlock before lo output cache).cenv.constants.toList :=
    Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr stored
  exact decoded_block limits _ constants decoded output included codec

theorem decoded_context_coherent (limits : Limits) (records : Records) (blobs : Kernel.Ingress.Blobs)
    (constants : Kernel.Ingress.Constants) (unique : uniqueKeys records blobs = .ok ())
    (decoded : decodeRecords limits records = .ok constants) (pins : Pins)
    (fallback : Array (Address × Ixon.Constant)) (hint : Kernel.ConstRef Address → Option Kernel.ReducibilityHint)
    (fallbackConsistent : ReaderStore.Consistent fallback) :
    ReaderIndexEntries.Coherent (contextOf pins constants.toArray blobs fallback hint).store
      (ReaderStore.allRecords constants.toArray fallback) :=
  ReaderStore.context_coherent pins constants.toArray blobs fallback hint
    (decoded_consistent limits records blobs constants unique decoded) fallbackConsistent

theorem decoded_context_block (limits : Limits) (records : Records) (blobs : Kernel.Ingress.Blobs)
    (constants : Kernel.Ingress.Constants) (unique : uniqueKeys records blobs = .ok ())
    (decoded : decodeRecords limits records = .ok constants) (pins : Pins)
    (fallback : Array (Address × Ixon.Constant)) (hint : Kernel.ConstRef Address → Option Kernel.ReducibilityHint)
    (output : BlockResult) (included : (output.blockAddr, output.blockBytes) ∈ records)
    (codec : Sharing.Verify.BlockResultCodecWF output) :
    (contextOf pins constants.toArray blobs fallback hint).store output.blockAddr = some output.block :=
  ReaderStore.context_primary pins constants.toArray blobs fallback hint
    (decoded_consistent limits records blobs constants unique decoded) output.blockAddr output.block
    (decoded_block limits records constants decoded output included codec)

theorem map_keys_unique (map : Std.HashMap Address α) : (map.toList.map Prod.fst).Nodup := by
  rw [Std.HashMap.map_fst_toList_eq_keys]
  exact map.nodup_keys

/-- The compiler's published maps satisfy the actual duplicate-key stage;
neither a fresh-address nor hash-injectivity premise is needed. -/
theorem published_uniqueKeys (environment : CompileEnv) :
    uniqueKeys environment.constants.toList environment.blobs.toList = .ok () := by
  apply (uniqueKeys_ok_iff _ _).mpr
  exact ⟨map_keys_unique environment.constants, map_keys_unique environment.blobs⟩

theorem decoded_published_consistent (environment : CompileEnv) (limits : Limits)
    (constants : Kernel.Ingress.Constants)
    (decoded : decodeRecords limits environment.constants.toList = .ok constants) :
    ReaderStore.Consistent constants.toArray :=
  decoded_consistent limits environment.constants.toList environment.blobs.toList constants
    (published_uniqueKeys environment) decoded

/-- Actual checked merge, decoding and context construction supply the
published main-block lookup consumed by the index/reader theorems. -/
theorem published_context_block (before : DriverAcc) (lo : Name) (output : BlockResult) (cache : BlockState)
    (accepted : checkCompiledBlock before.cenv lo output cache = .ok ())
    (codec : Sharing.Verify.BlockResultCodecWF output) (limits : Limits) (constants : Kernel.Ingress.Constants)
    (decoded : decodeRecords limits (mergeCompiledBlock before lo output cache).cenv.constants.toList = .ok constants)
    (pins : Pins) (fallback : Array (Address × Ixon.Constant))
    (hint : Kernel.ConstRef Address → Option Kernel.ReducibilityHint) :
    (contextOf pins constants.toArray (mergeCompiledBlock before lo output cache).cenv.blobs.toList fallback hint).store
      output.blockAddr = some output.block :=
  ReaderStore.context_primary pins constants.toArray _ fallback hint
    (decoded_published_consistent _ limits constants decoded) output.blockAddr output.block
    (published_decoded_block before lo output cache accepted codec limits constants decoded)

theorem prelude_consistent (pins : Pins) (records : Array (Address × Ixon.Constant)) (pre : Prelude)
    (ran : readPrelude pins records = .ok pre) : ReaderStore.Consistent pre.records := by
  unfold readPrelude at ran
  cases reading : readRecords (contextOf pins records []) {} records with
  | error error => simp [reading, throw, throwThe, MonadExceptOf.throw] at ran
  | ok result =>
    rcases result with ⟨state, declarations⟩
    simp only [reading, pure, Except.pure, Except.ok.injEq] at ran
    cases ran
    exact consistent_of_keys records (readRecords_nodup reading)

theorem builtinPrelude_consistent (pre : Prelude) (ran : builtinPrelude = .ok pre) :
    ReaderStore.Consistent pre.records := by
  unfold builtinPrelude at ran
  generalize pins : defaultPins = pinResult at ran
  generalize records : preludeRecords = recordResult at ran
  cases pinResult with
  | error reason => simp [bind, Except.bind] at ran
  | ok pinsValue =>
    cases recordResult with
    | error reason => simp [bind, Except.bind] at ran
    | ok values =>
      simp only [bind, Except.bind] at ran
      exact prelude_consistent pinsValue values pre ran

theorem stream_coherent (environment : CompileEnv) (limits : Limits) (constants : Kernel.Ingress.Constants)
    (decoded : decodeRecords limits environment.constants.toList = .ok constants)
    (pins : Pins) (pre : Prelude) (preludeReady : builtinPrelude = .ok pre)
    (hint : Kernel.ConstRef Address → Option Kernel.ReducibilityHint) :
    ReaderIndexEntries.Coherent (streamContext pins pre constants environment.blobs.toList hint).store
      (ReaderStore.allRecords constants.toArray pre.records) :=
  ReaderStore.context_coherent pins constants.toArray environment.blobs.toList pre.records hint
    (decoded_published_consistent environment limits constants decoded) (builtinPrelude_consistent pre preludeReady)

theorem stream_grouped_lookup (environment : CompileEnv) (limits : Limits) (constants : Kernel.Ingress.Constants)
    (decoded : decodeRecords limits environment.constants.toList = .ok constants)
    (pins : Pins) (pre : Prelude) (preludeReady : builtinPrelude = .ok pre)
    (hint : Kernel.ConstRef Address → Option Kernel.ReducibilityHint) (block : Address) (shape : BlockShape)
    (shapeFound : (streamContext pins pre constants environment.blobs.toList hint).index.blocks[block]? = some shape)
    (ref : Kernel.ConstRef Address) (present : ref ∈ shape.recs) :
    ∃ entry owner constant position recursor carriers,
      (streamContext pins pre constants environment.blobs.toList hint).index.recs[ref]? = some entry ∧ entry.block = block ∧
      ref = .member owner position ∧ (streamContext pins pre constants environment.blobs.toList hint).store owner = some constant ∧
      (recursorMembers constant).find? (·.1 == position) = some (position, recursor) ∧
      analyseRecursor (streamContext pins pre constants environment.blobs.toList hint).store owner constant recursor =
        some (entry.motive, carriers, entry.major) :=
  ReaderStore.context_grouped_lookup pins constants.toArray environment.blobs.toList pre.records hint
    (decoded_published_consistent environment limits constants decoded) (builtinPrelude_consistent pre preludeReady)
    block shape shapeFound ref present

open Ix.CompileCert.HeadWriterFrame in
/-- The original source compilation, actual checked publication and byte
decoding discharge the store/context premises for singleton index order.
Only index presence remains an independent discovery condition. -/
theorem published_stream_order (before : DriverAcc) (lo : Name) (source : InductiveVal)
    (blockEnv : BlockEnv) (initial cache : BlockState) (output : BlockResult)
    (compiled : rawRun (compileConstantInfo (.inductInfo source)) (before.cenv, blockEnv) initial = (.ok output, cache))
    (accepted : checkCompiledBlock before.cenv lo output cache = .ok ())
    (codec : Sharing.Verify.BlockResultCodecWF output) (limits : Limits) (constants : Kernel.Ingress.Constants)
    (decoded : decodeRecords limits (mergeCompiledBlock before lo output cache).cenv.constants.toList = .ok constants)
    (pins : Pins) (pre : Prelude) (hint : Kernel.ConstRef Address → Option Kernel.ReducibilityHint)
    (shape : BlockShape)
    (indexed : (streamContext pins pre constants (mergeCompiledBlock before lo output cache).cenv.blobs.toList hint).index.blocks[output.blockAddr]? = some shape) :
    shape.order = #[0] :=
  ReaderStore.context_compiled_order source (before.cenv, blockEnv) initial cache output compiled
    pins constants.toArray (mergeCompiledBlock before lo output cache).cenv.blobs.toList pre.records hint
    (decoded_published_consistent _ limits constants decoded)
    (published_decoded_block before lo output cache accepted codec limits constants decoded) shape indexed

end Ix.CompileCert.ReaderAdmissionRecords
