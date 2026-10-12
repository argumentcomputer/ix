import IxSharingVerify.CanonicalMeaning
import IxSharingVerify.Builder
import IxC.Kernel.Ixon.Reader
import Ix.CompileCert.DefinitionEmission

/-! Canonical sharing preserves the actual anonymous kernel reader's results.
The production definition-like payload compiler and sharing builder compose
through that result, and existing codec correctness gives exact serialization.
Primary-table wire validity remains explicit. Address hashing, publication,
whole-declaration admission and totality are separate obligations. -/

namespace Ix.CompileCert.SharingRead

open Ix.Kernel.Reader Ix.Sharing.Verify.SharingExact Ix.Sharing.Verify.CanonicalMeaning

def TableMeaning (context : ECx) (substitution : Nat → Ixon.Expr) (table : Array (ReadM CExpr)) : Prop :=
  ∀ index, index < table.size → table[index]? = some (convExpr context #[] (substitution index))

/-- The certified expression reader agrees with Share substitution, including
errors, whenever every referenced table slot has the specified interpretation. -/
theorem convExpr_subst (context : ECx) (substitution : Nat → Ixon.Expr)
    (table : Array (ReadM CExpr)) (meaning : TableMeaning context substitution table)
    (source : Ixon.Expr) (bounded : SharesIn (fun index => index < table.size) source) :
    convExpr context table source = convExpr context #[] (substShares substitution source) := by
  induction source with
  | share index => simp only [convExpr, substShares, meaning index.toNat bounded]
  | prj _ _ _ ih => simp only [convExpr, substShares, ih bounded]
  | app _ _ ihf iha | lam _ _ _ ihf iha | all _ _ _ _ ihf iha =>
    simp only [convExpr, substShares, ihf bounded.1, iha bounded.2]
  | letE _ _ _ _ iht ihv ihb =>
    simp only [convExpr, substShares, iht bounded.1, ihv bounded.2.1, ihb bounded.2.2]
  | _ => rfl

theorem table_empty (context : ECx) (substitution : Nat → Ixon.Expr) : TableMeaning context substitution #[] := by
  intro index bound
  simp at bound

theorem table_push (context : ECx) (substitution : Nat → Ixon.Expr)
    (table : Array (ReadM CExpr)) (meaning : TableMeaning context substitution table)
    (source : Ixon.Expr) (bounded : SharesIn (fun index => index < table.size) source)
    (equation : substitution table.size = substShares substitution source) :
    TableMeaning context substitution (table.push (convExpr context table source)) := by
  have read : convExpr context table source = convExpr context #[] (substitution table.size) := by
    rw [convExpr_subst context substitution table meaning source bounded, equation]
  intro index bound
  by_cases old : index < table.size
  · rw [Array.getElem?_push_lt old]
    have prior := meaning index old
    rw [Array.getElem?_eq_getElem old] at prior
    exact prior
  · have last : index = table.size := by simp only [Array.size_push] at bound; omega
    subst index
    rw [Array.getElem?_push_size, read]

def buildTable (context : ECx) (sources : List Ixon.Expr) (initial : Array (ReadM CExpr)) : Array (ReadM CExpr) :=
  sources.foldl (fun table source => table.push (convExpr context table source)) initial

theorem buildTable_meaning (context : ECx) (substitution : Nat → Ixon.Expr)
    (sources : List Ixon.Expr) (initial : Array (ReadM CExpr))
    (meaning : TableMeaning context substitution initial)
    (entries : ∀ index, index < sources.length →
      substitution (initial.size + index) = substShares substitution sources[index]! ∧
      SharesIn (fun slot => slot < initial.size + index) sources[index]!) :
    (buildTable context sources initial).size = initial.size + sources.length ∧
      TableMeaning context substitution (buildTable context sources initial) := by
  induction sources generalizing initial with
  | nil => exact ⟨by simp [buildTable], meaning⟩
  | cons source rest ih =>
    have first := entries 0 (by simp)
    simp only [Nat.add_zero, List.getElem!_cons_zero] at first
    have next := table_push context substitution initial meaning source first.2 first.1
    have tail := ih (initial.push (convExpr context initial source)) next (by
      intro index bound
      have row := entries (index + 1) (by simp only [List.length_cons]; omega)
      simpa only [Array.size_push, List.getElem!_cons_succ, Nat.add_assoc, Nat.add_comm 1 index] using row)
    refine ⟨?_, tail.2⟩
    change (buildTable context rest (initial.push (convExpr context initial source))).size = _
    rw [tail.1]
    simp only [Array.size_push, List.length_cons]
    omega

def expressionContext (context : Ctx) (source : Ixon.Constant) (params : Nat → CName) (self : Nat → Option CName) : ECx :=
  ⟨context, source, source.univs.map (convUniv params), self⟩

theorem memberReader_eq (context : Ctx) (source : Ixon.Constant) (params : Nat → CName) (self : Nat → Option CName) :
    MemberReader.mk' context source params self =
      ⟨expressionContext context source params self,
        buildTable (expressionContext context source params self) source.sharing.toList #[]⟩ := by
  simp [MemberReader.mk', expressionContext, buildTable, Array.forIn_pure_yield_eq_foldl]

theorem memberReader_table (context : Ctx) (source : Ixon.Constant) (params : Nat → CName) (self : Nat → Option CName)
    (substitution : Nat → Ixon.Expr)
    (entries : ∀ index, index < source.sharing.size →
      substitution index = substShares substitution source.sharing[index]! ∧
      SharesIn (fun slot => slot < index) source.sharing[index]!) :
    (MemberReader.mk' context source params self).tbl.size = source.sharing.size ∧
      TableMeaning (expressionContext context source params self) substitution (MemberReader.mk' context source params self).tbl := by
  rw [memberReader_eq]
  have built := buildTable_meaning (expressionContext context source params self) substitution source.sharing.toList #[]
    (table_empty _ _) (by
      intro index bound
      simpa [getElem!_def] using entries index (by simpa using bound))
  simpa using built

theorem memberReader_subst (context : Ctx) (source : Ixon.Constant) (params : Nat → CName) (self : Nat → Option CName)
    (substitution : Nat → Ixon.Expr)
    (entries : ∀ index, index < source.sharing.size →
      substitution index = substShares substitution source.sharing[index]! ∧
      SharesIn (fun slot => slot < index) source.sharing[index]!)
    (root : Ixon.Expr) (bounded : SharesIn (fun slot => slot < source.sharing.size) root) :
    (MemberReader.mk' context source params self).read root =
      convExpr (expressionContext context source params self) #[] (substShares substitution root) := by
  have table := memberReader_table context source params self substitution entries
  have reading := convExpr_subst (expressionContext context source params self) substitution
    (MemberReader.mk' context source params self).tbl table.2 root (by simpa only [table.1] using bounded)
  exact reading

/-- The actual member reader interprets a sharing encoding exactly as the
unfolded ordered source roots, with equality of errors as well as values. -/
theorem meaning_read (context : Ctx) (source : Ixon.Constant) (params : Nat → CName) (self : Nat → Option CName)
    (originals roots : Array Ixon.Expr) (meaning : SharingMeaning originals source.sharing roots) :
    roots.map (MemberReader.mk' context source params self).read =
      originals.map (convExpr (expressionContext context source params self) #[]) := by
  obtain ⟨substitution, entries, bounded, same⟩ := meaning
  rw [← same, Array.map_map]
  apply Array.ext (by simp)
  intro index beforeBound afterBound
  simp only [Array.size_map] at beforeBound afterBound
  simp only [Array.getElem_map, Function.comp_apply]
  exact memberReader_subst context source params self substitution entries roots[index]
    (bounded _ (Array.getElem_mem beforeBound))

theorem convExpr_same_tables (context : Ctx) (before after : Ixon.Constant) (params : Nat → CName)
    (self : Nat → Option CName) (refs : before.refs = after.refs) (univs : before.univs = after.univs)
    (table : Array (ReadM CExpr)) (source : Ixon.Expr) :
    convExpr (expressionContext context before params self) table source =
      convExpr (expressionContext context after params self) table source := by
  have levels : (expressionContext context before params self).levels = (expressionContext context after params self).levels := by
    funext indices
    unfold ECx.levels
    have point : (expressionContext context before params self).level = (expressionContext context after params self).level := by
      funext index
      simp only [ECx.level, expressionContext, univs]
    rw [point]
  have level : (expressionContext context before params self).level = (expressionContext context after params self).level := by
    funext index
    simp only [ECx.level, expressionContext, univs]
  have ref : (expressionContext context before params self).refAt = (expressionContext context after params self).refAt := by
    funext index
    simp only [ECx.refAt, expressionContext, refs]
  have blob : (expressionContext context before params self).blobAt = (expressionContext context after params self).blobAt := by
    funext index
    simp only [ECx.blobAt, expressionContext, refs]
  induction source
  all_goals simp only [convExpr, *]
  all_goals rfl

theorem memberReader_empty (context : Ctx) (source : Ixon.Constant) (params : Nat → CName) (self : Nat → Option CName)
    (empty : source.sharing = #[]) (root : Ixon.Expr) :
    (MemberReader.mk' context source params self).read root = convExpr (expressionContext context source params self) #[] root := by
  rw [memberReader_eq]
  simp only [MemberReader.read, empty, Array.toList_empty, buildTable, List.foldl_nil]

theorem meaning_read_before (context : Ctx) (before after : Ixon.Constant) (params : Nat → CName)
    (self : Nat → Option CName) (refs : before.refs = after.refs) (univs : before.univs = after.univs)
    (empty : before.sharing = #[]) (originals roots : Array Ixon.Expr)
    (meaning : SharingMeaning originals after.sharing roots) :
    roots.map (MemberReader.mk' context after params self).read =
      originals.map (MemberReader.mk' context before params self).read := by
  rw [meaning_read context after params self originals roots meaning]
  apply Array.ext (by simp)
  intro index leftBound rightBound
  simp only [Array.size_map] at leftBound rightBound
  simp only [Array.getElem_map]
  rw [memberReader_empty context before params self empty]
  exact (convExpr_same_tables context before after params self refs univs #[] originals[index]).symm

theorem array_two (values : Array α) (size : values.size = 2) : ∃ first second, values = #[first, second] := by
  rcases values with ⟨values⟩
  change values.length = 2 at size
  match values, size with
  | [first, second], _ => exact ⟨first, second, rfl⟩

theorem definition_writeback (source : Ixon.Definition) (roots : Array Ixon.Expr) (info : Ixon.ConstantInfo)
    (size : roots.size = 2) (ran : Ix.CompileM.withRootExprs (.defn source) roots = .ok info) :
    ∃ type value, roots = #[type, value] ∧ info = .defn { source with typ := type, value } := by
  obtain ⟨type, value, rfl⟩ := array_two roots size
  have actual : Ix.CompileM.withRootExprs (.defn source) #[type, value] =
      .ok (.defn { source with typ := type, value }) := rfl
  rw [actual] at ran
  exact ⟨type, value, rfl, (Except.ok.inj ran).symm⟩

/-- Actual definition-like block construction preserves both root readings
and the declaration header. The supplied logical parameter/self maps and
external store are the same on both sides. -/
theorem buildDefinition_read (context : Ctx) (params : Nat → CName) (self : Nat → Option CName)
    (limits : Ix.Sharing.Exact.Limits) (source : Ixon.Definition) (refs : Array Address) (univs : Array Ixon.Univ)
    (out : Ixon.Constant) (ran : Ix.CompileM.buildConstantWithSharing limits (.defn source) refs univs = .ok out) :
    ∃ target : Ixon.Definition, out.info = .defn target ∧
      target.kind = source.kind ∧ target.safety = source.safety ∧ target.lvls = source.lvls ∧
      (MemberReader.mk' context out params self).read target.typ =
        (MemberReader.mk' context { info := .defn source, sharing := #[], refs, univs } params self).read source.typ ∧
      (MemberReader.mk' context out params self).read target.value =
        (MemberReader.mk' context { info := .defn source, sharing := #[], refs, univs } params self).read source.value := by
  obtain ⟨shared, info, sharedRan, size, written, shape⟩ := Ix.Sharing.Verify.buildConstantWithSharing_eq_ok ran
  have meaning := canonicalSharingTiered_meaning .tagN limits #[source.typ, source.value] shared sharedRan
  obtain ⟨type, value, roots, header⟩ := definition_writeback source shared.result.roots info size written
  subst info
  subst out
  rw [roots] at meaning
  have readings := meaning_read_before context
    { info := .defn source, sharing := #[], refs, univs }
    { info := .defn { source with typ := type, value }, sharing := shared.result.sharing, refs, univs }
    params self rfl rfl rfl #[source.typ, source.value] #[type, value] meaning
  refine ⟨{ source with typ := type, value }, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · have first := congrArg (fun values : Array (ReadM CExpr) => values[0]?) readings
    simpa using first
  · have second := congrArg (fun values : Array (ReadM CExpr) => values[1]?) readings
    simpa using second

/-- The reader sees literal blobs accumulated by the current block before
looking in the previously published store. Presentation names are absent. -/
def blobContext (context : Ctx) (state : Ix.CompileM.BlockState) : Ctx :=
  { context with blob := fun address =>
    (state.blockBlobs.get? address).orElse (fun _ => context.blob address) }

theorem unshared_read (context : Ctx) (base : Ixon.Constant) (params : Nat → CName)
    (self : Nat → Option CName) (state : Ix.CompileM.BlockState) (ordinary : state.p3MetaMode = false)
    (info : Ixon.ConstantInfo) (root : Ixon.Expr) :
    (MemberReader.mk' (blobContext context state)
      { info, sharing := #[], refs := state.refs, univs := state.univs } params self).read root =
      (ExpressionRead.blockReader context base params self state).read root := by
  simp only [ExpressionRead.blockReader, ordinary, Bool.false_eq_true, ↓reduceIte]
  rw [memberReader_empty _ _ _ _ rfl, memberReader_empty _ _ _ _ rfl]
  exact convExpr_same_tables (blobContext context state)
    { info, sharing := #[], refs := state.refs, univs := state.univs }
    { base with sharing := #[], refs := state.refs, univs := state.univs }
    params self rfl rfl #[] root

/-- Canonical sharing and root write-back preserve the source relation of a
compiled definition payload. This includes theorem and opaque payload kinds. -/
theorem buildDefinition_payload (context : Ctx) (base : Ixon.Constant) (self : Nat → Option CName)
    (names : Ix.Name → CName → Prop) (sourceParams : List Ix.Name) (params : List CName)
    (state : Ix.CompileM.BlockState) (ordinary : state.p3MetaMode = false)
    (source : Ix.Def) (payload : Ixon.Definition)
    (related : DefinitionEmission.PayloadRelated names sourceParams params
      (ExpressionRead.blockReader context base (paramOf params) self state) source payload)
    (limits : Ix.Sharing.Exact.Limits) (out : Ixon.Constant)
    (ran : Ix.CompileM.buildConstantWithSharing limits (.defn payload) state.refs state.univs = .ok out) :
    ∃ target, out.info = .defn target ∧
      DefinitionEmission.PayloadRelated names sourceParams params
        (MemberReader.mk' (blobContext context state) out (paramOf params) self) source target := by
  obtain ⟨target, info, kind, safety, levels, typeRead, valueRead⟩ :=
    buildDefinition_read (blobContext context state) (paramOf params) self limits payload state.refs state.univs out ran
  obtain ⟨sourceKind, sourceSafety, sourceLevels, type, value, sourceType, sourceValue, readType, readValue⟩ := related
  refine ⟨target, info, kind.trans sourceKind, safety.trans sourceSafety, levels.trans sourceLevels,
    type, value, sourceType, sourceValue, ?_, ?_⟩
  · rw [typeRead, unshared_read context base (paramOf params) self state ordinary]
    exact readType
  · rw [valueRead, unshared_read context base (paramOf params) self state ordinary]
    exact readValue

/-- The successful construction supplies both expression wire obligations;
only the external reference and universe tables need a separate wire premise. -/
theorem buildDefinition_wireWF (limits : Ix.Sharing.Exact.Limits) (source : Ixon.Definition)
    (state : Ix.CompileM.BlockState) (tables : Ix.Sharing.Verify.BlockWireTablesWF state)
    (out : Ixon.Constant)
    (ran : Ix.CompileM.buildConstantWithSharing limits (.defn source) state.refs state.univs = .ok out) :
    out.wireWF := by
  obtain ⟨shared, info, sharedRan, size, written, shape⟩ := Ix.Sharing.Verify.buildConstantWithSharing_eq_ok ran
  obtain ⟨entries, rootsWire, capacity, _, _⟩ := Ix.Sharing.Verify.Tiered.canonicalSharingTiered_format sharedRan
  obtain ⟨type, value, roots, header⟩ := definition_writeback source shared.result.roots info size written
  subst info
  subst out
  rw [roots] at rootsWire
  refine ⟨⟨rootsWire type (by simp), rootsWire value (by simp)⟩, capacity, ?_,
    tables.refsCount, tables.refs, tables.univsCount, tables.univs⟩
  intro expression member
  exact entries expression (by simpa using member)

/-- Exact anonymous serialization, without going through the separate
address-hashing wrapper or introducing a hash-injectivity assumption. -/
theorem buildDefinition_codec (limits : Ix.Sharing.Exact.Limits) (source : Ixon.Definition)
    (state : Ix.CompileM.BlockState) (tables : Ix.Sharing.Verify.BlockWireTablesWF state)
    (out : Ixon.Constant)
    (ran : Ix.CompileM.buildConstantWithSharing limits (.defn source) state.refs state.univs = .ok out) :
    Ixon.deConstant (Ixon.serConstant out) = .ok out :=
  Ixon.Verify.deConstant_serConstant out (buildDefinition_wireWF limits source state tables out ran)

/-- Composition of production payload compilation with the production
canonical-sharing builder. Success is an explicit outcome, not the definition
of source validity. Address hashing and publication are later boundaries. -/
theorem compileDefinitionData_shared_correct (context : Ctx) (base : Ixon.Constant)
    (self : Nat → Option CName) (names : Ix.Name → CName → Prop) (params : List CName)
    (bindings : ExpressionState.Bindings) (environment : Ix.CompileM.CompileEnv × Ix.CompileM.BlockEnv)
    (source : Ix.Def) (arity : params.length = source.levelParams.size)
    (aligned : ∀ address, context.blob address = environment.1.blobs.get? address)
    (external : ExpressionState.BindingsCorrect environment.1 bindings context names)
    (selfSound : ExpressionState.SelfCorrect environment.2 self names)
    (before : Ix.CompileM.BlockState) (ready : DefinitionEmission.Ready bindings before)
    (payload : Ixon.Definition × Ixon.ConstantMeta × Ixon.Expr × Ixon.Expr) (after : Ix.CompileM.BlockState)
    (compiled : HeadWriterFrame.rawRun (Ix.CompileM.compileDefinitionData source) environment before = (.ok payload, after))
    (out : Ixon.Constant)
    (built : Ix.CompileM.buildConstantWithSharing environment.1.sharingLimits (.defn payload.1) after.refs after.univs = .ok out) :
    DefinitionEmission.Clean bindings after ∧
      ∃ target, out.info = .defn target ∧
        DefinitionEmission.PayloadRelated names source.levelParams.toList params
          (MemberReader.mk' (blobContext context after) out (paramOf params) self) source target := by
  have checked := DefinitionEmission.compileDefinitionData_correct context base self names params bindings environment source
    arity aligned external selfSound before ready
  rw [compiled] at checked
  obtain ⟨clean, related, _⟩ := checked.2.2 payload rfl
  exact ⟨clean, buildDefinition_payload context base self names source.levelParams.toList params after clean.2.2
    source payload.1 related environment.1.sharingLimits out built⟩

/-- The production payload/sharing pipeline yields a wire-safe anonymous
constant, exact bytes and source-related kernel readings, given independently
well-formed primary tables. This does not claim successful compilation of all
valid sources or admission of the complete published declaration. -/
theorem compileDefinitionData_serialized_correct (context : Ctx) (base : Ixon.Constant)
    (self : Nat → Option CName) (names : Ix.Name → CName → Prop) (params : List CName)
    (bindings : ExpressionState.Bindings) (environment : Ix.CompileM.CompileEnv × Ix.CompileM.BlockEnv)
    (source : Ix.Def) (arity : params.length = source.levelParams.size)
    (aligned : ∀ address, context.blob address = environment.1.blobs.get? address)
    (external : ExpressionState.BindingsCorrect environment.1 bindings context names)
    (selfSound : ExpressionState.SelfCorrect environment.2 self names)
    (before : Ix.CompileM.BlockState) (ready : DefinitionEmission.Ready bindings before)
    (payload : Ixon.Definition × Ixon.ConstantMeta × Ixon.Expr × Ixon.Expr) (after : Ix.CompileM.BlockState)
    (compiled : HeadWriterFrame.rawRun (Ix.CompileM.compileDefinitionData source) environment before = (.ok payload, after))
    (tables : Ix.Sharing.Verify.BlockWireTablesWF after) (out : Ixon.Constant)
    (built : Ix.CompileM.buildConstantWithSharing environment.1.sharingLimits (.defn payload.1) after.refs after.univs = .ok out) :
    DefinitionEmission.Clean bindings after ∧ out.wireWF ∧
      Ixon.deConstant (Ixon.serConstant out) = .ok out ∧
      ∃ target, out.info = .defn target ∧
        DefinitionEmission.PayloadRelated names source.levelParams.toList params
          (MemberReader.mk' (blobContext context after) out (paramOf params) self) source target := by
  have shared := compileDefinitionData_shared_correct context base self names params bindings environment source
    arity aligned external selfSound before ready payload after compiled out built
  exact ⟨shared.1, buildDefinition_wireWF environment.1.sharingLimits payload.1 after tables out built,
    buildDefinition_codec environment.1.sharingLimits payload.1 after tables out built, shared.2⟩

end Ix.CompileCert.SharingRead
