import Ix.CompileCert.SourceExportFast
import Ix.CompileCert.MutualProjections
import Ix.CompileCert.Opt.IngestionLookup

/-! Constructor positions from actual source-export guards, preserved by
ingestion and used by the anonymous projection resolver. Exact lookup/run
provenance, store availability and the original source-domain bridge remain
explicit; no name/expression-cache fidelity is inferred from scalar fields. -/

namespace Ix.CompileCert.SourceConstructorPositions

def ConstructorAt (find : Lean.Name → Option Lean.ConstantInfo) (owner : Lean.Name) (params : Nat)
    (entry : Lean.Name × Nat) : Prop :=
  ∃ ctor : Lean.ConstructorVal, find entry.1 = some (.ctorInfo ctor) ∧
    ctor.induct = owner ∧ ctor.cidx = entry.2 ∧ ctor.numParams = params

def ctorStep (find : Lean.Name → Option Lean.ConstantInfo) (owner : Lean.Name) (params : Nat)
    (entry : Lean.Name × Nat) (initial : List Kernel.ConstantInfo) :
    ExportM (ForInStep (List Kernel.ConstantInfo)) := do
  let (name, index) := entry
  let some (.ctorInfo ctor) := find name | throw s!"source constructor missing: {name}"
  unless ctor.induct == owner && ctor.cidx == index && ctor.numParams == params do
    throw s!"source constructor ownership mismatch: {name}"
  let .ctor cv np nf ← exportSourceEntry (.ctorInfo ctor) | throw "source constructor kind mismatch"
  pure (.yield (initial ++ [Kernel.ConstantInfo.ctorInfo cv np nf]))

theorem forIn_checked {α β : Type} (sources : List α) (initial : β) (body : α → β → ExportM (ForInStep β))
    (post : α → Prop)
    (checked : ∀ source state step, body source state = .ok step → ∃ next, step = .yield next ∧ post source)
    (output : β) (ran : forIn sources initial body = .ok output) : ∀ source ∈ sources, post source := by
  induction sources generalizing initial with
  | nil => simp
  | cons source rest ih =>
    rw [List.forIn_cons] at ran
    obtain ⟨step, first, last⟩ := Ix.Sharing.Verify.except_bind_eq_ok ran
    obtain ⟨next, rfl, valid⟩ := checked source initial step first
    have tail := ih next last
    intro query present
    rcases List.mem_cons.mp present with rfl | later
    · exact valid
    · exact tail query later

theorem ctorStep_checked (find : Lean.Name → Option Lean.ConstantInfo) (owner : Lean.Name) (params : Nat)
    (entry : Lean.Name × Nat) (initial : List Kernel.ConstantInfo) (output : ForInStep (List Kernel.ConstantInfo))
    (ran : ctorStep find owner params entry initial = .ok output) :
    ∃ next, output = .yield next ∧ ConstructorAt find owner params entry := by
  rcases entry with ⟨name, index⟩
  dsimp only [ctorStep] at ran
  cases found : find name with
  | none => rw [found] at ran; cases ran
  | some constant =>
    cases constant with
    | ctorInfo ctor =>
      rw [found] at ran
      by_cases valid : (ctor.induct == owner && ctor.cidx == index && ctor.numParams == params) = true
      · simp only [valid, ↓reduceIte] at ran
        obtain ⟨exported, _, returned⟩ := Ix.Sharing.Verify.except_bind_eq_ok ran
        cases exported <;> simp [throw, throwThe, MonadExceptOf.throw, pure, Except.pure] at returned
        cases returned
        refine ⟨_, rfl, ctor, found, ?_⟩
        simpa [Bool.and_eq_true, and_assoc] using valid
      · simp only [valid] at ran
        cases ran
    | _ => rw [found] at ran; cases ran

abbrev GroupState := List Lean.Name × List Kernel.ConstantInfo × List Kernel.ConstantInfo

def InductiveAt (find : Lean.Name → Option Lean.ConstantInfo) (owner : Lean.InductiveVal) (name : Lean.Name) : Prop :=
  ∃ value : Lean.InductiveVal, find name = some (.inductInfo value) ∧ value.all = owner.all ∧
    value.numParams = owner.numParams ∧
    ∀ entry ∈ value.ctors.zipIdx, ConstructorAt find name value.numParams entry

def inductiveStep (find : Lean.Name → Option Lean.ConstantInfo) (owner : Lean.InductiveVal)
    (name : Lean.Name) (initial : GroupState) : ExportM (ForInStep GroupState) := do
  let some (.inductInfo value) := find name | throw s!"source inductive member missing: {name}"
  unless value.all == owner.all && value.numParams == owner.numParams do
    throw s!"inconsistent source inductive group: {name}"
  let .induct cv _ ← exportSourceEntry (.inductInfo value) | throw "source inductive kind mismatch"
  let ctors ← forIn value.ctors.zipIdx initial.2.2 (ctorStep find name value.numParams)
  pure (.yield (initial.1 ++ value.ctors, initial.2.1 ++ [Kernel.ConstantInfo.indInfo cv {}], ctors))

theorem inductiveStep_checked (find : Lean.Name → Option Lean.ConstantInfo) (owner : Lean.InductiveVal)
    (name : Lean.Name) (initial : GroupState) (output : ForInStep GroupState)
    (ran : inductiveStep find owner name initial = .ok output) :
    ∃ next, output = .yield next ∧ InductiveAt find owner name := by
  dsimp only [inductiveStep] at ran
  cases found : find name with
  | none => rw [found] at ran; cases ran
  | some constant =>
    cases constant with
    | inductInfo value =>
      rw [found] at ran
      by_cases valid : (value.all == owner.all && value.numParams == owner.numParams) = true
      · simp only [valid, ↓reduceIte] at ran
        obtain ⟨exported, _, returned⟩ := Ix.Sharing.Verify.except_bind_eq_ok ran
        cases exported with
        | induct cv params =>
          obtain ⟨ctors, loopRan, finished⟩ := Ix.Sharing.Verify.except_bind_eq_ok returned
          have checked := forIn_checked value.ctors.zipIdx initial.2.2 (ctorStep find name value.numParams)
            (ConstructorAt find name value.numParams) (ctorStep_checked find name value.numParams) ctors loopRan
          cases Except.ok.inj finished
          have fields : value.all = owner.all ∧ value.numParams = owner.numParams := by simpa using valid
          exact ⟨_, rfl, value, found, fields.1, fields.2, checked⟩
        | _ => cases returned
      · simp only [valid] at ran
        cases ran
    | _ => rw [found] at ran; cases ran

theorem export_checked (find : Lean.Name → Option Lean.ConstantInfo)
    (deps : List Lean.Name → ExportM (List Lean.Name)) (owner : Lean.InductiveVal)
    (output : SourceDeclGroup) (ran : exportSourceInductiveP find deps owner = .ok output) :
    owner.name ∈ owner.all ∧ ∀ name ∈ owner.all, InductiveAt find owner name := by
  unfold exportSourceInductiveP at ran
  by_cases present : owner.all.contains owner.name = true
  · simp only [present, ↓reduceIte] at ran
    obtain ⟨state, loopRan, _⟩ := Ix.Sharing.Verify.except_bind_eq_ok ran
    have checkedLoop : forIn owner.all (owner.all, [], []) (inductiveStep find owner) = .ok state := loopRan
    exact ⟨by simpa using present,
      forIn_checked owner.all (owner.all, [], []) (inductiveStep find owner)
        (InductiveAt find owner) (inductiveStep_checked find owner) state checkedLoop⟩
  · simp only [present] at ran
    cases ran

theorem source_export_checked (source : Source) (owner : Lean.InductiveVal)
    (output : SourceDeclGroup) (ran : exportSourceInductive source owner = .ok output) :
    owner.name ∈ owner.all ∧ ∀ name ∈ owner.all, InductiveAt source.find owner name :=
  export_checked source.find (sourceGroupDependencies source) owner output ran

theorem exported_constructor (source : Source) (owner : Lean.InductiveVal)
    (output : SourceDeclGroup) (ran : exportSourceInductive source owner = .ok output)
    (name : Lean.Name) (member : name ∈ owner.all) (value : Lean.InductiveVal)
    (found : source.find name = some (.inductInfo value))
    (index : Nat) (inside : index < value.ctors.length) :
    ConstructorAt source.find name value.numParams (value.ctors[index], index) := by
  obtain ⟨actual, actualFound, _, _, checked⟩ := (source_export_checked source owner output ran).2 name member
  have same := Lean.ConstantInfo.inductInfo.inj (Option.some.inj (actualFound.symm.trans found))
  subst actual
  exact checked (value.ctors[index], index)
    (List.mk_mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem inside))

/-- Constructor scalar fields survive the actual ingestion function for every
cache state. This makes no claim about cached names or expression contents. -/
theorem canonical_constructor (source : Lean.ConstructorVal) (state : Ix.CanonM.CanonState) :
    ∃ target : Ix.ConstructorVal, ((Ix.CanonM.canonConst (.ctorInfo source)).run state).1 = .ctorInfo target ∧
      target.cidx = source.cidx ∧ target.numParams = source.numParams ∧
      target.numFields = source.numFields ∧ target.isUnsafe = source.isUnsafe := by
  exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

theorem canonical_constructor_index (source : Lean.ConstructorVal) (state : Ix.CanonM.CanonState)
    (target : Ix.ConstructorVal) (decoded : ((Ix.CanonM.canonConst (.ctorInfo source)).run state).1 = .ctorInfo target) :
    target.cidx = source.cidx := by
  obtain ⟨actual, actualRun, index, _, _, _⟩ := canonical_constructor source state
  have same := Ix.ConstantInfo.ctorInfo.inj (actualRun.symm.trans decoded)
  exact same ▸ index

theorem exported_canonical_constructor (source : Source) (owner : Lean.InductiveVal)
    (output : SourceDeclGroup) (ran : exportSourceInductive source owner = .ok output)
    (name : Lean.Name) (member : name ∈ owner.all) (value : Lean.InductiveVal)
    (found : source.find name = some (.inductInfo value))
    (index : Nat) (inside : index < value.ctors.length) (state : Ix.CanonM.CanonState) :
    ∃ original : Lean.ConstructorVal, ∃ target : Ix.ConstructorVal,
      source.find value.ctors[index] = some (.ctorInfo original) ∧
      ((Ix.CanonM.canonConst (.ctorInfo original)).run state).1 = .ctorInfo target ∧
      target.cidx = index ∧ target.numParams = value.numParams := by
  obtain ⟨original, selected, _, position, params⟩ := exported_constructor source owner output ran name member value found index inside
  obtain ⟨target, decoded, indexEq, paramsEq, _, _⟩ := canonical_constructor original state
  exact ⟨original, target, selected, decoded, indexEq.trans position, paramsEq.trans params⟩

theorem captured_canonical_constructor {find : Lean.Name → Option Lean.ConstantInfo}
    (captured : CapturedSource find) (owner : Lean.InductiveVal)
    (output : SourceDeclGroup) (ran : exportSourceInductive captured.source owner = .ok output)
    (name : Lean.Name) (member : name ∈ owner.all) (value : Lean.InductiveVal)
    (found : captured.source.find name = some (.inductInfo value))
    (index : Nat) (inside : index < value.ctors.length) (state : Ix.CanonM.CanonState) :
    ∃ original : Lean.ConstructorVal, ∃ target : Ix.ConstructorVal,
      find value.ctors[index] = some (.ctorInfo original) ∧
      ((Ix.CanonM.canonConst (.ctorInfo original)).run state).1 = .ctorInfo target ∧
      target.cidx = index ∧ target.numParams = value.numParams := by
  obtain ⟨original, target, selected, decoded, position, params⟩ :=
    exported_canonical_constructor captured.source owner output ran name member value found index inside state
  exact ⟨original, target, Opt.IngestionLookup.captured_lookup captured selected, decoded, position, params⟩

/-- The singleton chunk decoder used by the production lazy fallback retains
constructor scalar fields, regardless of the supplied registration name. -/
theorem lazy_constructor (name : Lean.Name) (source : Lean.ConstructorVal) :
    ∃ target : Ix.ConstructorVal,
      ((Ix.CanonM.canonChunk #[(name, .ctorInfo source)])[0]?).map (·.2) = some (.ctorInfo target) ∧
      target.cidx = source.cidx ∧ target.numParams = source.numParams ∧
      target.numFields = source.numFields ∧ target.isUnsafe = source.isUnsafe := by
  exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

theorem lazy_lookup_constructor (index : Std.HashMap Ix.Name (Lean.Name × Lean.ConstantInfo))
    (key : Ix.Name) (name : Lean.Name) (source : Lean.ConstructorVal)
    (found : index.get? key = some (name, .ctorInfo source)) :
    ∃ target : Ix.ConstructorVal,
      ({ index, fetch := fun (n, ci) => ((Ix.CanonM.canonChunk #[(n, ci)])[0]?).map (·.2) } : Ix.LazyConstants).get? key =
        some (.ctorInfo target) ∧ target.cidx = source.cidx ∧ target.numParams = source.numParams := by
  obtain ⟨target, decoded, position, params, _, _⟩ := lazy_constructor name source
  refine ⟨target, ?_, position, params⟩
  simpa only [Ix.LazyConstants.get?, found, Option.bind_some] using decoded

theorem lazy_lookup_provenance (index : Std.HashMap Ix.Name (Lean.Name × Lean.ConstantInfo))
    (key : Ix.Name) (name : Lean.Name) (source : Lean.ConstructorVal) (target : Ix.ConstructorVal)
    (found : index.get? key = some (name, .ctorInfo source))
    (decoded : ({ index, fetch := fun (n, ci) => ((Ix.CanonM.canonChunk #[(n, ci)])[0]?).map (·.2) } : Ix.LazyConstants).get? key =
      some (.ctorInfo target)) :
    ((Ix.CanonM.canonConst (.ctorInfo source)).run ((Ix.CanonM.canonName name).run {}).2).1 = .ctorInfo target := by
  rw [Ix.LazyConstants.get?, found, Option.bind_some] at decoded
  exact Option.some.inj decoded

/-- Exact per-element ingestion provenance for a source constructor array.
The driver must supply these lookup/run facts; this is not a new final-domain
predicate or a claim about arbitrary hash-keyed environment contents. -/
structure ConstructorProvenance (source : Source) (value : Lean.InductiveVal)
    (constructors : Array Ix.ConstructorVal) : Prop where
  length : constructors.size = value.ctors.length
  entries : ∀ index (inside : index < constructors.size),
    ∃ original : Lean.ConstructorVal, ∃ state : Ix.CanonM.CanonState,
      source.find (value.ctors[index]'(by omega)) = some (.ctorInfo original) ∧
      ((Ix.CanonM.canonConst (.ctorInfo original)).run state).1 = .ctorInfo constructors[index]

theorem array_positions (source : Source) (owner : Lean.InductiveVal)
    (output : SourceDeclGroup) (ran : exportSourceInductive source owner = .ok output)
    (name : Lean.Name) (member : name ∈ owner.all) (value : Lean.InductiveVal)
    (found : source.find name = some (.inductInfo value)) (constructors : Array Ix.ConstructorVal)
    (provenance : ConstructorProvenance source value constructors) :
    ∀ index (inside : index < constructors.size), constructors[index].cidx = index := by
  intro index inside
  obtain ⟨original, state, selected, decoded⟩ := provenance.entries index inside
  have sourceInside : index < value.ctors.length := by rw [← provenance.length]; exact inside
  obtain ⟨expected, expectedFound, _, position, _⟩ :=
    exported_constructor source owner output ran name member value found index sourceInside
  have same := Lean.ConstantInfo.ctorInfo.inj (Option.some.inj (selected.symm.trans expectedFound))
  have retained := canonical_constructor_index original state constructors[index] decoded
  exact retained.trans (by simpa only [same] using position)

theorem projection_positions (source : Source) (owner : Lean.InductiveVal)
    (output : SourceDeclGroup) (ran : exportSourceInductive source owner = .ok output)
    (name : Lean.Name) (member : name ∈ owner.all) (value : Lean.InductiveVal)
    (found : source.find name = some (.inductInfo value)) (inductiveValue : Ix.Ind)
    (provenance : ConstructorProvenance source value inductiveValue.ctors) :
    MutualProjections.ConstructorPositions (.indc inductiveValue) :=
  array_positions source owner output ran name member value found inductiveValue.ctors provenance

theorem compiled_constructor_resolves (source : Source) (owner : Lean.InductiveVal)
    (group : SourceDeclGroup) (exported : exportSourceInductive source owner = .ok group)
    (name : Lean.Name) (member : name ∈ owner.all) (value : Lean.InductiveVal)
    (found : source.find name = some (.inductInfo value)) (constructors : Array Ix.ConstructorVal)
    (provenance : ConstructorProvenance source value constructors)
    (inductiveValue : Ix.InductiveVal) (context : Ix.CompileM.CompileEnv × Ix.CompileM.BlockEnv)
    (before after : Ix.CompileM.BlockState) (output : Ix.CompileM.BlockResult)
    (compiled : HeadWriterFrame.rawRun (Ix.CompileM.compileInductiveFamilyBlock inductiveValue constructors) context before =
      (.ok output, after)) (store : Kernel.Reader.Store) (stored : store output.blockAddr = some output.block)
    (index : Nat) (inside : index < constructors.size) :
    ∃ projection metadata,
      output.projections[index + 1]? = some (constructors[index].cnst.name, projection, metadata) ∧
      Kernel.Reader.resolveSource store (Address.blake3 (Ixon.ser projection)) projection =
        some (.ctor output.blockAddr 0 index) :=
  ProjectionLayout.constructor_projection_resolves inductiveValue constructors output
    (ProjectionLayout.family_layout inductiveValue constructors context before output after compiled)
    store stored index inside (array_positions source owner group exported name member value found constructors provenance index inside)

/-- The actual rewrite may change a constructor's type, but retains its
scalar fields for every callback and successful stateful execution. -/
theorem rewritten_constructor (expansion : Ix.Name → Except String (Option Ix.Compile.Pass.Expansion))
    (source : Ix.ConstructorVal) (before after : Ix.Compile.Pass.RwState) (output : Ix.ConstantInfo)
    (ran : (Ix.Compile.Pass.rewriteConstM expansion (.ctorInfo source)).run before = .ok (output, after)) :
    ∃ target : Ix.ConstructorVal, output = .ctorInfo target ∧ target.cidx = source.cidx ∧
      target.numParams = source.numParams ∧ target.numFields = source.numFields ∧ target.isUnsafe = source.isUnsafe := by
  unfold Ix.Compile.Pass.rewriteConstM at ran
  simp only [StateT.run_bind, StateT.run_pure] at ran
  cases rewritten : (Ix.Compile.Pass.rw expansion Ix.Compile.Pass.rewriteFuel true source.cnst.type).run before with
  | error reason => simp [rewritten, bind, Except.bind] at ran
  | ok result =>
    rcases result with ⟨type, state⟩
    simp only [rewritten, bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at ran
    exact ⟨_, ran.1.symm, rfl, rfl, rfl, rfl⟩

theorem rewritten_constructor_index (expansion : Ix.Name → Except String (Option Ix.Compile.Pass.Expansion))
    (source target : Ix.ConstructorVal) (before after : Ix.Compile.Pass.RwState)
    (ran : (Ix.Compile.Pass.rewriteConstM expansion (.ctorInfo source)).run before = .ok (.ctorInfo target, after)) :
    target.cidx = source.cidx := by
  obtain ⟨actual, same, position, _, _, _⟩ := rewritten_constructor expansion source before after (.ctorInfo target) ran
  cases Ix.ConstantInfo.ctorInfo.inj same
  exact position

theorem rewritten_positions (sources targets : Array Ix.ConstructorVal) (length : targets.size = sources.size)
    (positions : ∀ index (inside : index < sources.size), sources[index].cidx = index)
    (runs : ∀ index (inside : index < targets.size),
      ∃ expansion before after,
        (Ix.Compile.Pass.rewriteConstM expansion (.ctorInfo (sources[index]'(by omega)))).run before =
          .ok (.ctorInfo targets[index], after)) :
    ∀ index (inside : index < targets.size), targets[index].cidx = index := by
  intro index inside
  obtain ⟨expansion, before, after, ran⟩ := runs index inside
  have sourceInside : index < sources.size := by omega
  exact (rewritten_constructor_index expansion sources[index] targets[index] before after ran).trans (positions index sourceInside)

theorem compiled_rewritten_constructor_resolves (source : Source) (owner : Lean.InductiveVal)
    (group : SourceDeclGroup) (exported : exportSourceInductive source owner = .ok group)
    (name : Lean.Name) (member : name ∈ owner.all) (value : Lean.InductiveVal)
    (found : source.find name = some (.inductInfo value)) (originals constructors : Array Ix.ConstructorVal)
    (provenance : ConstructorProvenance source value originals) (length : constructors.size = originals.size)
    (runs : ∀ index (inside : index < constructors.size),
      ∃ expansion before after,
        (Ix.Compile.Pass.rewriteConstM expansion (.ctorInfo (originals[index]'(by omega)))).run before =
          .ok (.ctorInfo constructors[index], after))
    (inductiveValue : Ix.InductiveVal) (context : Ix.CompileM.CompileEnv × Ix.CompileM.BlockEnv)
    (before after : Ix.CompileM.BlockState) (output : Ix.CompileM.BlockResult)
    (compiled : HeadWriterFrame.rawRun (Ix.CompileM.compileInductiveFamilyBlock inductiveValue constructors) context before =
      (.ok output, after)) (store : Kernel.Reader.Store) (stored : store output.blockAddr = some output.block)
    (index : Nat) (inside : index < constructors.size) :
    ∃ projection metadata,
      output.projections[index + 1]? = some (constructors[index].cnst.name, projection, metadata) ∧
      Kernel.Reader.resolveSource store (Address.blake3 (Ixon.ser projection)) projection =
        some (.ctor output.blockAddr 0 index) :=
  ProjectionLayout.constructor_projection_resolves inductiveValue constructors output
    (ProjectionLayout.family_layout inductiveValue constructors context before output after compiled)
    store stored index inside
    (rewritten_positions originals constructors length
      (array_positions source owner group exported name member value found originals provenance) runs index inside)

end Ix.CompileCert.SourceConstructorPositions
