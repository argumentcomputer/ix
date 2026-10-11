import Ix.CompileCert.Opt.IngestionArity

/-! Exact lookup facts for the existing captured source.
These are internal bridges, not new assumptions on the compiler's final Dom.
No claim about CanonM cache contents or hash-keyed driver tables is made. -/

namespace Ix.CompileCert.Opt.IngestionLookup

theorem source_find_mem {source : Source} {name : Lean.Name} {ci : Lean.ConstantInfo}
    (found : source.find name = some ci) : ci ∈ source.declarations :=
  List.mem_of_find?_eq_some found

theorem source_find_name {source : Source} {name : Lean.Name} {ci : Lean.ConstantInfo}
    (found : source.find name = some ci) : ci.name = name := by
  have named := List.find?_some found
  simpa only [beq_iff_eq] using named

theorem source_find_exists {source : Source} {name : Lean.Name}
    (present : name ∈ source.names) : ∃ ci, source.find name = some ci := by
  obtain ⟨ci, member, named⟩ := List.mem_map.mp present
  have has : (source.find name).isSome := by
    apply List.find?_isSome.mpr
    exact ⟨ci, member, by simpa only [beq_iff_eq] using named⟩
  cases found : source.find name with
  | none => simp only [found, Option.isSome_none, Bool.false_eq_true] at has
  | some ci => exact ⟨ci, rfl⟩

/-- A selected source lookup is the exact supplied lookup value, not a value
recovered through its printed name or a cached digest. -/
theorem captured_lookup {find : Lean.Name → Option Lean.ConstantInfo}
    (captured : CapturedSource find) {name : Lean.Name} {ci : Lean.ConstantInfo}
    (found : captured.source.find name = some ci) : find name = some ci := by
  have original := captured.faithful ci (source_find_mem found)
  simpa only [source_find_name found] using original

/-- Even without a new uniqueness assumption, original lookup fidelity makes
every retained member equal to the selected hit at its own name. -/
theorem captured_member_lookup {find : Lean.Name → Option Lean.ConstantInfo}
    (captured : CapturedSource find) {ci : Lean.ConstantInfo}
    (member : ci ∈ captured.source.declarations) :
    captured.source.find ci.name = some ci := by
  have named : ci.name ∈ captured.source.names := List.mem_map.mpr ⟨ci, member, rfl⟩
  obtain ⟨other, found⟩ := source_find_exists named
  have same : other = ci := Option.some.inj
    ((captured_lookup captured found).symm.trans (captured.faithful ci member))
  simpa only [same] using found

/-- Closure and original lookup provenance are already fields of ClosedCapture.
An unrelated ambient declaration is neither requested nor added here. -/
theorem closed_reference_lookup {find : Lean.Name → Option Lean.ConstantInfo}
    {roots : List Lean.Name} (captured : ClosedCapture find roots)
    {caller : Lean.ConstantInfo} (member : caller ∈ captured.source.declarations)
    {name : Lean.Name} (reference : name ∈ declarationRefs caller) :
    ∃ ci, captured.source.find name = some ci ∧ find name = some ci ∧ ci.name = name := by
  obtain ⟨ci, found⟩ := source_find_exists (captured.complete.2.2 caller member name reference)
  exact ⟨ci, found, captured_lookup captured.toCapturedSource found, source_find_name found⟩

/-- Compose the actual source lookup with the actual ingestion header count.
The count holds for every cache state; the returned header's identities still
require the separate ingestion refinement. -/
theorem closed_reference_canon_arity {find : Lean.Name → Option Lean.ConstantInfo}
    {roots : List Lean.Name} (captured : ClosedCapture find roots)
    {caller : Lean.ConstantInfo} (member : caller ∈ captured.source.declarations)
    {name : Lean.Name} (reference : name ∈ declarationRefs caller)
    (state : Ix.CanonM.CanonState) :
    ∃ ci, captured.source.find name = some ci ∧ find name = some ci ∧
      ((Ix.CanonM.canonConst ci).run state).1.getCnst.levelParams.size = ci.levelParams.length := by
  obtain ⟨ci, selected, original, _⟩ := closed_reference_lookup captured member reference
  exact ⟨ci, selected, original, IngestionArity.canonConst_params_size ci state⟩

/-- Apply the same original-lookup bridge to every actual body dependency of a
retained definition; declarationRefs already includes the entire source body. -/
theorem definition_reference_lookup {find : Lean.Name → Option Lean.ConstantInfo}
    {roots : List Lean.Name} (captured : ClosedCapture find roots)
    {definition : Lean.DefinitionVal}
    (member : Lean.ConstantInfo.defnInfo definition ∈ captured.source.declarations)
    {name : Lean.Name} (reference : name ∈ exprRefs definition.value) :
    ∃ ci, captured.source.find name = some ci ∧ find name = some ci ∧ ci.name = name := by
  apply closed_reference_lookup captured member
  exact List.mem_append_right _ (List.mem_append_right _ reference)

end Ix.CompileCert.Opt.IngestionLookup

