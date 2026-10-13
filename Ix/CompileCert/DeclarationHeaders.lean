import Ix.CompileCert.PreseedState

/-! Exact natural-number headers for successful production declaration
finalizers. The bounds come from executable guards, not new source-domain
premises. Metadata contents and whole-declaration admission remain separate. -/

namespace Ix.CompileCert.DeclarationHeaders

open Ix Ix.CompileM Ix.CompileCert.HeadWriterFrame

def Returns (action : CompileM α) (post : α → Prop) : Prop :=
  ∀ context before output after, rawRun action context before = (.ok output, after) → post output

theorem Returns.pure {output : α} {post : α → Prop} (valid : post output) : Returns (pure output) post := by
  intro context before value after ran
  cases Except.ok.inj (congrArg Prod.fst ran)
  exact valid

theorem Returns.bind {action : CompileM α} {next : α → CompileM β} {first : α → Prop} {last : β → Prop}
    (head : Returns action first) (tail : ∀ value, first value → Returns (next value) last) : Returns (action >>= next) last := by
  intro context before output after ran
  obtain ⟨value, middle, headRan, tailRan⟩ := PreseedReferences.bind_ok _ _ context before output after ran
  exact tail value (head context before value middle headRan) context middle output after tailRan

theorem Returns.bindAny (action : CompileM α) {next : α → CompileM β} {post : β → Prop}
    (tail : ∀ value, Returns (next value) post) : Returns (action >>= next) post := by
  intro context before output after ran
  obtain ⟨value, middle, _, tailRan⟩ := PreseedReferences.bind_ok _ _ context before output after ran
  exact tail value context middle output after tailRan

theorem Returns.count (label : String) (count : Nat) :
    Returns (checkedTableCount label count) (fun _ => count < UInt64.size) := by
  intro context before output after ran
  exact (Interning.checkedTableCount_value label count context before (congrArg Prod.fst ran)).2

theorem Returns.index (label : String) (index : Nat) :
    Returns (checkedTableIndex label index) (fun _ => index < UInt64.size) := by
  intro context before output after ran
  exact (Interning.checkedTableIndex_value label index context before (congrArg Prod.fst ran)).2

theorem exact_header (count : Nat) (bounded : count < UInt64.size) : count.toUInt64.toNat = count :=
  UInt64.toNat_ofNat_of_lt' bounded

local macro "header_proof" : tactic => `(tactic|
  with_reducible repeat' first
    | exact Returns.pure (by repeat' first | constructor | apply exact_header; assumption)
    | refine Returns.bind (Returns.count _ _) (fun _ bounded => ?_)
    | refine Returns.bind (Returns.index _ _) (fun _ bounded => ?_)
    | refine Returns.bindAny _ (fun _ => ?_)
    | dsimp only)

theorem definition (source : Def) (type value : Ixon.Expr) (typeRoot valueRoot : UInt64) :
    Returns (finishDefinitionDataCompilation source type typeRoot value valueRoot)
      (fun output => output.1.lvls.toNat = source.levelParams.size) := by
  unfold finishDefinitionDataCompilation
  header_proof

theorem axiomHeader (source : AxiomVal) (type : Ixon.Expr) (root : UInt64) :
    Returns (finishAxiomCompilation source type root)
      (fun output => output.1.lvls.toNat = source.cnst.levelParams.size) := by
  unfold finishAxiomCompilation
  header_proof

theorem quotient (source : QuotVal) (type : Ixon.Expr) (root : UInt64) :
    Returns (finishQuotientCompilation source type root)
      (fun output => output.1.lvls.toNat = source.cnst.levelParams.size) := by
  unfold finishQuotientCompilation
  header_proof

theorem recursorRule (source : RecursorRule) : Returns (compileRecursorRule source)
    (fun output => output.1.fields.toNat = source.nfields) := by
  unfold compileRecursorRule
  header_proof

theorem recursor (source : RecursorVal) (type : Ixon.Expr) (root : UInt64) (rules : RecursorRuleCompileState) :
    Returns (finishRecursorCompilation source type root rules) (fun output =>
      output.1.lvls.toNat = source.cnst.levelParams.size ∧ output.1.params.toNat = source.numParams ∧
      output.1.indices.toNat = source.numIndices ∧ output.1.motives.toNat = source.numMotives ∧
      output.1.minors.toNat = source.numMinors) := by
  unfold finishRecursorCompilation
  header_proof

theorem constructorHeader (source : ConstructorVal) (type : Ixon.Expr) (root : UInt64) :
    Returns (finishConstructorCompilation source type root) (fun output =>
      output.1.lvls.toNat = source.cnst.levelParams.size ∧ output.1.cidx.toNat = source.cidx ∧
      output.1.params.toNat = source.numParams ∧ output.1.fields.toNat = source.numFields) := by
  unfold finishConstructorCompilation
  header_proof

theorem inductiveHeader (source : InductiveVal) (type : Ixon.Expr) (root : UInt64)
    (metadata : InductiveTypeCompileMeta) (constructors : InductiveConstructorCompileState) :
    Returns (finishInductiveCompilation source type root metadata constructors) (fun output =>
      output.1.lvls.toNat = source.cnst.levelParams.size ∧ output.1.params.toNat = source.numParams ∧
      output.1.indices.toNat = source.numIndices) := by
  unfold finishInductiveCompilation
  header_proof

theorem inductiveDataHeader (source : Ind) (type : Ixon.Expr) (root : UInt64)
    (metadata : InductiveTypeCompileMeta) (constructors : InductiveConstructorCompileState) :
    Returns (finishInductiveDataCompilation source type root metadata constructors) (fun output =>
      output.1.lvls.toNat = source.levelParams.size ∧ output.1.params.toNat = source.numParams ∧
      output.1.indices.toNat = source.numIndices) := by
  unfold finishInductiveDataCompilation
  header_proof

theorem definitionBody (source : Def) : Returns (DefinitionEmission.body source)
    (fun output => output.1.lvls.toNat = source.levelParams.size) := by
  rw [DefinitionEmission.body]
  exact Returns.bindAny _ fun type => Returns.bindAny _ fun value => definition source type.1 value.1 type.2 value.2

theorem definitionData (source : Def) : Returns (compileDefinitionData source)
    (fun output => output.1.lvls.toNat = source.levelParams.size) := by
  intro context before output after ran
  rw [DefinitionEmission.compileDefinitionData_run] at ran
  exact definitionBody source _ _ output after ran

theorem sharing_header (limits : Ix.Sharing.Exact.Limits) (source : Ixon.Definition)
    (refs : Array Address) (univs : Array Ixon.Univ) (output : Ixon.Constant)
    (ran : buildConstantWithSharing limits (.defn source) refs univs = .ok output) :
    ∃ target : Ixon.Definition, output.info = .defn target ∧ target.lvls = source.lvls := by
  obtain ⟨shared, info, _, size, written, shape⟩ := Ix.Sharing.Verify.buildConstantWithSharing_eq_ok ran
  obtain ⟨type, value, _, header⟩ := SharingRead.definition_writeback source shared.result.roots info size written
  subst info
  subst output
  exact ⟨_, rfl, rfl⟩

theorem definitionBlock (source : Def) : Returns (compileDefinitionDataBlock source)
    (fun output => ∃ target : Ixon.Definition, output.block.info = .defn target ∧ target.lvls.toNat = source.levelParams.size) := by
  intro context before output after ran
  obtain ⟨payload, compiled, built, _⟩ := DefinitionBlock.compileDefinitionDataBlock_eq_ok context source before output after ran
  have exactLevels := definitionData source context before payload after compiled
  obtain ⟨target, shape, levels⟩ := sharing_header context.1.sharingLimits payload.1 after.refs after.univs output.block built
  exact ⟨target, shape, by rw [levels]; exact exactLevels⟩

/-- The actual returned singleton block has the exact source natural arity;
no externally supplied header-capacity bound is needed. -/
theorem definitionInfo (source : Def) : Returns (compileDefinitionDataInfo source)
    (fun output => ∃ target : Ixon.Definition, output.block.info = .defn target ∧ target.lvls.toNat = source.levelParams.size) := by
  rw [compileDefinitionDataInfo]
  exact Returns.bindAny _ (fun _ => definitionBlock source)

theorem projection_count (source : InductiveVal) (ind : Ixon.Inductive) (metadata : Ixon.ConstantMeta)
    (constructors : Array (Name × Ixon.ConstantMeta)) : Returns (finishInductiveFamilyBlock source ind metadata constructors)
      (fun _ => source.ctors.size < UInt64.size) := by
  unfold finishInductiveFamilyBlock
  with_reducible refine Returns.bind (Returns.count "inductive constructors" source.ctors.size) (fun _ bounded => ?_)
  with_reducible repeat' first
    | exact Returns.pure bounded
    | refine Returns.bindAny _ (fun _ => ?_)

theorem projection_index (source : InductiveVal) (ind : Ixon.Inductive) (metadata : Ixon.ConstantMeta)
    (constructors : Array (Name × Ixon.ConstantMeta)) (context : CompileEnv × BlockEnv)
    (before after : BlockState) (output : BlockResult)
    (ran : rawRun (finishInductiveFamilyBlock source ind metadata constructors) context before = (.ok output, after))
    (index : Nat) (inside : index < source.ctors.size) : index.toUInt64.toNat = index :=
  exact_header index (Nat.lt_trans inside (projection_count source ind metadata constructors context before output after ran))

theorem recursorRule_refuses (source : RecursorRule) (context : CompileEnv × BlockEnv)
    (before after : BlockState) (rhs : Ixon.Expr) (root : UInt64)
    (compiled : rawRun (compileExpr source.rhs) context before = (.ok (rhs, root), after))
    (oversized : UInt64.size ≤ source.nfields) :
    ∃ reason, rawRun (compileRecursorRule source) context before = (.error (.resourceLimit reason), after) := by
  rw [compileRecursorRule, rawRun_bind, compiled]
  dsimp only
  rw [rawRun_bind]
  have noRoom : ¬source.nfields < UInt64.size := by omega
  simp only [checkedTableCount, noRoom, ↓reduceIte]
  exact ⟨_, rfl⟩

end Ix.CompileCert.DeclarationHeaders
