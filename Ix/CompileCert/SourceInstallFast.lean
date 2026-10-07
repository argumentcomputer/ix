import Ix.CompileCert.SourceInstallation
import Ix.CompileCert.SourceExportFast

/-! # The source installation's proposal and correspondence, indexed (M7 WP-F)

Two more parts of the normalised source installation (`installSourceNormalizedComplete`)
read the source or the stream through lists:

* the model proposal (`proposeSourceModels`, an untrusted proposal whose result the
  installation records, so it is computed by the decision path) captures each inductive
  block's evidence through `exportSourceBlockEvidence`, which looks the owner, its
  members and their constructors and recursors up with `Source.find`;
* the entry correspondence (`SourceEntryCorrespondence`) is decided by list membership of
  every exported entry in the whole stream.

`proposeSourceModelsF` and `entriesFastDecidable` compute the same proposal and decide the
same proposition through `sourceIndex` and a name index of the stream, and replace them
by `@[csimp]` for the code compiled after this module (the normalised installation in
`SourceNormalization.lean`, the S certifier). Statements and proofs keep reading the
originals: `proposeSourceModelsF_eq` is an equation; a decision is a subsingleton. -/

namespace Ix.CompileCert

/-! ## Block evidence with the lookup given -/

/-- `exportSourceBlockEvidence` with its lookup (and a proof that it is `source.find`) and
its group export given: at `source.find`, `rfl` and `exportSourceInductive source` it is
`exportSourceBlockEvidence source` by `rfl`. -/
def exportSourceBlockEvidenceP (source : Source) (find : Lean.Name → Option Lean.ConstantInfo)
    (hfind : find = source.find) (inductive_ : Lean.InductiveVal → ExportM SourceDeclGroup)
    (ownerName : Lean.Name) : ExportM (SourceBlockEvidence source) :=
  match ho : find ownerName with
  | some (.inductInfo owner) => do
    let group ← inductive_ owner
    let captured ← captureNames find group.members
    let original : CapturedSource source.find := hfind ▸ captured
    if hm : original.source.names = group.members then
      let mut types := []
      let mut ctors := []
      let mut recs := []
      for ci in original.source.declarations do
        match ci with
        | .inductInfo v =>
          let .induct cv _ ← exportSourceEntry ci | throw "source shape: expected inductive"
          let row : Kernel.Frontend.InModel.IndTypeRec := {
            cv, nP := v.numParams, nIdx := v.numIndices
            ctors := v.ctors.map sourceName, isRec := v.isRec
            isReflexive := v.isReflexive, numNested := v.numNested }
          types := types ++ [row]
        | .ctorInfo v =>
          let .ctor cv _ _ ← exportSourceEntry ci | throw "source shape: expected constructor"
          ctors := ctors ++ [{ cv, nP := v.numParams, nF := v.numFields }]
        | .recInfo v =>
          let .recursor cv _ _ rules ← exportSourceEntry ci | throw "source shape: expected recursor"
          let row : Kernel.Frontend.InModel.IndRecRec := {
            cv, nP := v.numParams, nM := v.numMotives
            nm := v.numMinors, nI := v.numIndices, rules }
          recs := recs ++ [row]
        | _ => throw "source block contains a non-inductive member"
      let shape : Kernel.Frontend.InModel.BlockRec := ⟨types, ctors, recs⟩
      if hd : Kernel.Declaration.indDecl
          (shape.types.map (fun t => .indInfo t.cv {}) ++
            shape.ctors.map (fun c => .ctorInfo c.cv c.nP c.nF) ++
            shape.recs.map (fun r => .recInfo r.cv (r.nP + r.nM + r.nm + r.nI)
              (r.nP + r.nM + r.nm) r.rules)) owner.numParams = group.declaration then
        return ⟨ownerName, owner, by subst hfind; exact ho, group, original, hm, shape, hd⟩
      else throw "source model shape does not describe its original declaration group"
    else throw "source block capture changed the member inventory"
  | _ => .error s!"source model owner is not an original inductive: {ownerName}"

theorem exportSourceBlockEvidenceP_find (source : Source) (ownerName : Lean.Name) :
    exportSourceBlockEvidenceP source source.find rfl (exportSourceInductive source) ownerName =
      exportSourceBlockEvidence source ownerName := rfl

theorem exportSourceBlockEvidenceP_subst (source : Source) (find : Lean.Name → Option Lean.ConstantInfo)
    (hfind : find = source.find) (inductive_ : Lean.InductiveVal → ExportM SourceDeclGroup)
    (ownerName : Lean.Name) :
    exportSourceBlockEvidenceP source find hfind inductive_ ownerName =
      exportSourceBlockEvidenceP source source.find rfl inductive_ ownerName := by
  subst hfind; rfl

/-- Block evidence through the source index and the fast group export. -/
def exportSourceBlockEvidenceF (source : Source) (idx : Std.HashMap Lean.Name Lean.ConstantInfo)
    (hidx : idx = sourceIndex source) (ownerName : Lean.Name) : ExportM (SourceBlockEvidence source) :=
  exportSourceBlockEvidenceP source (fun n => idx[n]?) (by subst hidx; exact sourceIndex_find source)
    (exportSourceInductiveP (fun n => idx[n]?) (sourceGroupDependenciesF (fun n => idx[n]?))) ownerName

theorem exportSourceInductiveP_index (source : Source) :
    exportSourceInductiveP (fun n => (sourceIndex source)[n]?)
      (sourceGroupDependenciesF (fun n => (sourceIndex source)[n]?)) = exportSourceInductive source := by
  funext owner
  rw [sourceIndex_find,
    show sourceGroupDependenciesF source.find = sourceGroupDependencies source from
      funext fun members => (sourceGroupDependenciesF_eq _ members).trans
        (sourceGroupDependenciesP_find source members)]
  rfl

theorem exportSourceBlockEvidenceF_eq (source : Source) (ownerName : Lean.Name) :
    exportSourceBlockEvidenceF source (sourceIndex source) rfl ownerName =
      exportSourceBlockEvidence source ownerName := by
  unfold exportSourceBlockEvidenceF
  rw [exportSourceBlockEvidenceP_subst, exportSourceInductiveP_index]
  rfl

/-! ## The model proposal with the block evidence given -/

/-- `proposeSourceModels` with its block evidence given: at `exportSourceBlockEvidence source`
it is `proposeSourceModels source` by `rfl`. -/
def proposeSourceModelsP (source : Source) (blockEvidence : Lean.Name → ExportM (SourceBlockEvidence source))
    (original : Array Kernel.Declaration) : ExportM (SourceModelProposal source) := do
  let groups ← exportSourceGroups source
  let mut state : SourceModelState := {}
  let mut declarations := #[]
  let mut evidence := []
  let mut basisSupport := []
  for declaration in original do
    if let .indDecl _ _ := declaration then
      let some group := groups.find? (fun group => decide (group.declaration = declaration))
        | throw "source model preparation could not associate an original group"
      let some owner := group.members.head? | throw "source model group has no owner"
      let block ← blockEvidence owner
      unless decide (block.group.declaration = declaration) do
        throw "source model block evidence differs from the original declaration"
      evidence := evidence ++ [block]
      for type in block.shape.types do
        state := { state with blocks := state.blocks.insert type.cv.name block.shape }
      if Kernel.Frontend.InModel.wants block.shape then
        for (name, kind) in sourceModelBasisSupport do
          if (state.types[name]?).isNone then
            if original.any (fun d => d.names.contains name) then
              throw s!"source-owned support {repr name} is scheduled after a model that requires it"
            let support := Kernel.Declaration.basisDecl kind
            declarations := declarations.push support
            basisSupport := basisSupport ++ [kind]
            state := state.note support
        let context : Kernel.Frontend.InModel.Ctx :=
          ⟨fun n => state.types[n]?, fun n => state.heights.getD n 0, fun n => state.blocks[n]?⟩
        let proposed ← Kernel.Frontend.InModel.generate context block.shape
        for auxiliary in proposed do
          declarations := declarations.push auxiliary
          state := state.note auxiliary
    declarations := declarations.push declaration
    state := state.note declaration
  return ⟨declarations, evidence, basisSupport⟩

theorem proposeSourceModelsP_find (source : Source) (original : Array Kernel.Declaration) :
    proposeSourceModelsP source (exportSourceBlockEvidence source) original =
      proposeSourceModels source original := rfl

/-- **The model proposal through the source index.** -/
def proposeSourceModelsF (source : Source) (original : Array Kernel.Declaration) :
    ExportM (SourceModelProposal source) :=
  let idx := sourceIndex source
  proposeSourceModelsP source (exportSourceBlockEvidenceF source idx rfl) original

theorem proposeSourceModelsF_eq (source : Source) (original : Array Kernel.Declaration) :
    proposeSourceModelsF source original = proposeSourceModels source original := by
  unfold proposeSourceModelsF
  dsimp only
  rw [show exportSourceBlockEvidenceF source (sourceIndex source) rfl = exportSourceBlockEvidence source from
    funext (exportSourceBlockEvidenceF_eq source)]
  rfl

/-- Compiled code runs the indexed proposal wherever it calls `proposeSourceModels`. -/
@[csimp] theorem proposeSourceModels_eq_fast : @proposeSourceModels = @proposeSourceModelsF := by
  funext source original
  exact (proposeSourceModelsF_eq source original).symm

/-! ## The entry correspondence through a name index of the stream -/

/-- The name an entry is installed under. -/
def directEntryName : DirectEntry → Kernel.Name
  | .axiom cv | .defn cv _ _ | .thm cv _ | .opaque cv _ | .quot _ cv | .induct cv _ | .ctor cv _ _
  | .recursor cv _ _ _ => cv.name

/-- The stream's entries under their names (the first of a name wins). -/
def entryIndex (entries : List DirectEntry) : Std.HashMap Kernel.Name DirectEntry :=
  entries.foldr (fun e m => m.insert (directEntryName e) e) {}

theorem entryIndex_mem : ∀ {entries : List DirectEntry} {k : Kernel.Name} {e : DirectEntry},
    (entryIndex entries)[k]? = some e → e ∈ entries
  | [], k, e, h => by simp [entryIndex] at h
  | x :: xs, k, e, h => by
    simp only [entryIndex, List.foldr_cons, Std.HashMap.getElem?_insert] at h
    split at h
    · cases h; exact List.mem_cons_self
    · exact List.mem_cons_of_mem x (entryIndex_mem h)

/-- `SourceEntryCorrespondence` through the index: every exported entry is the entry
the stream has under its name (compared through WP-B's memoised entry equality). -/
def entriesFast (source : Source) (declarations : Array Kernel.Declaration) : Bool :=
  let idx := entryIndex (streamEntries declarations)
  source.declarations.all fun ci => match exportSourceEntry ci with
    | .error _ => false
    | .ok expected => match idx[directEntryName expected]? with
      | some e => decide (e = expected)
      | none => false

theorem entriesFast_sound {source : Source} {declarations : Array Kernel.Declaration}
    (h : entriesFast source declarations = true) : SourceEntryCorrespondence source declarations := by
  intro ci hci
  have row := List.all_eq_true.mp h ci hci
  unfold SourceEntryMatches
  split at row
  · contradiction
  · rename_i expected hexp
    rw [hexp]
    split at row
    · rename_i e he
      have same : e = expected := of_decide_eq_true row
      subst same
      exact entryIndex_mem he
    · contradiction

/-- The correspondence decided through the index; a refusal falls back to the list
decision, so it decides the same proposition. -/
def entriesFastDecidable (source : Source) (declarations : Array Kernel.Declaration) :
    Decidable (SourceEntryCorrespondence source declarations) :=
  if h : entriesFast source declarations = true then isTrue (entriesFast_sound h)
  else instDecidableSourceEntryCorrespondence source declarations

/-- Compiled code decides the correspondence through the index. -/
@[csimp] theorem instDecidableSourceEntryCorrespondence_eq_fast :
    @instDecidableSourceEntryCorrespondence = @entriesFastDecidable := by
  funext source declarations
  exact Subsingleton.elim _ _

end Ix.CompileCert
