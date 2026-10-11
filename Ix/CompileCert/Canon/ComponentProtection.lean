import Ix.CompileCert.Canon.ComponentDiscovery
import Ix.CompileCert.Canon.SourceComponentBridge
import Ix.CompileCert.Canon.ExpansionOriginValues

/-!
UNCOMPILED proposal. The source-backed specialization derives protection from
the actual block-reference collector, rather than accepting a caller-provided
forbidden list. Queue-origin values cover every emitted auxiliary and every
constructor, so these statements are not merely about whichever origin-table
entries happen to be present. The generic callback interface has no finite
source-representation premise; source-specific conclusions are kept here.
-/

namespace Ix.CompileCert.Canon.ComponentCoreProof
open Ix.Compile.Canon
open Ix.Compile.Canon.FreshFamilySeparation
open Ix (Name Expr ConstantInfo)

/-- Structural lookup supplies the entry spelling used by the protection
proof even if the query has different cached hash fields. -/
theorem nameTable_lookup_sourceFree {α : Type} (table : NameTable α)
    (protectedNames : List Lean.Name)
    (free : ∀ entry ∈ table.entries, ∀ original ∈ protectedNames,
      (keyName entry.1).isPrefixOf original = false)
    {query : Name} {value : α} (found : table.get? query = some value) :
    ∀ original ∈ protectedNames, (keyName query).isPrefixOf original = false := by
  obtain ⟨stored, member, same⟩ := nameLookup_some_mem found
  intro original included
  simpa only [same] using free (stored, value) member original included

theorem aux_toList (x : Expanded) :
    x.aux.toList = x.types.toList.drop x.nOriginals := by
  rw [Expanded.aux, Array.toList_extract, List.extract_eq_take_drop]
  have length : (x.types.toList.drop x.nOriginals).length =
      x.types.size - x.nOriginals := by
    simp only [List.length_drop, Array.length_toList]
  rw [← length, List.take_length]

/-- The origin-value theorem is stated on the exact public auxiliary array,
with no filtering, deduplication or dropped constructor case. -/
theorem expand_aux_originValues (source : Ix.Environment) (dedup : Dedup)
    (classes : Array (Array Name)) (groups : SourceGroups)
    (keyAddr? : Option (Name → Option Address)) {x : Expanded}
    (run : expandSourceSpec source dedup (repsOf classes) (aliasesOf classes) groups keyAddr? = .ok x) :
    ∀ member ∈ x.aux,
      ∃ (sourceName : Name) (view : IndView) (levels : Array Ix.Level) (specs : Array Expr),
        IndView.ofConst? source.get? sourceName = some view ∧
        x.auxToNested.get? member.name = some (mkAppN (Expr.mkConst sourceName levels) specs) ∧
        ∀ generated ∈ member.ctors, ∃ original ∈ view.ctors,
          x.auxCtorMap.get? generated.name = some (original.1, member.name) := by
  have values := (expand_queueOriginValues source dedup classes groups keyAddr? run).2
  intro member included
  apply values member
  rw [← aux_toList]
  exact Array.mem_toList_iff.mpr included

/-- Every emitted auxiliary and constructor family avoids the exact names
in the actual source collector, including its retained metadata fields. -/
theorem expand_aux_sourceFree (source : Ix.Environment) (dedup : Dedup)
    (classes : Array (Array Name)) (groups : SourceGroups)
    (keyAddr? : Option (Name → Option Address)) {x : Expanded}
    (run : expandSourceSpec source dedup (repsOf classes) (aliasesOf classes) groups keyAddr? = .ok x) :
    ∀ member ∈ x.aux,
      (∀ original ∈ (sourceContext source (repsOf classes) groups.blocks).protectedNames,
        (keyName member.name).isPrefixOf original = false) ∧
      ∀ generated ∈ member.ctors,
        ∀ original ∈ (sourceContext source (repsOf classes) groups.blocks).protectedNames,
          (keyName generated.name).isPrefixOf original = false := by
  obtain ⟨membersFree, ctorsFree⟩ :=
    expand_originSourceFree source dedup classes groups keyAddr? run
  intro member included
  obtain ⟨_, _, _, _, _, memberFound, constructors⟩ :=
    expand_aux_originValues source dedup classes groups keyAddr? run member included
  constructor
  · exact nameTable_lookup_sourceFree x.auxToNested _ membersFree memberFound
  · intro generated inMember
    obtain ⟨_, _, found⟩ := constructors generated inMember
    exact nameTable_lookup_sourceFree x.auxCtorMap _ ctorsFree found

/-- This specializes the exact protected-name result to actual reachable
query spellings. No constant lookup success or caller completeness is needed. -/
theorem expand_aux_reachable_sourceFree (source : Ix.Environment) (dedup : Dedup)
    (classes : Array (Array Name)) (groups : SourceGroups)
    (keyAddr? : Option (Name → Option Address)) {x : Expanded}
    (run : expandSourceSpec source dedup (repsOf classes) (aliasesOf classes) groups keyAddr? = .ok x)
    {name : Name} (reached : SourceReach source groups.blocks (repsOf classes).toList name) :
    ∀ member ∈ x.aux,
      (keyName member.name).isPrefixOf (keyName name) = false ∧
      ∀ generated ∈ member.ctors, (keyName generated.name).isPrefixOf (keyName name) = false := by
  have protectedName :=
    (sourceContext_reachable_done source (repsOf classes) groups.blocks reached).1
  intro member included
  obtain ⟨auxFree, ctorFree⟩ := expand_aux_sourceFree source dedup classes groups keyAddr? run member included
  exact ⟨auxFree _ protectedName, fun generated inMember => ctorFree generated inMember _ protectedName⟩

/-- All name fields of every actually fetched reachable source record are
covered, not only the record's declaration name or expression references. -/
theorem expand_aux_sourceFieldsFree (source : Ix.Environment) (dedup : Dedup)
    (classes : Array (Array Name)) (groups : SourceGroups)
    (keyAddr? : Option (Name → Option Address)) {x : Expanded}
    (run : expandSourceSpec source dedup (repsOf classes) (aliasesOf classes) groups keyAddr? = .ok x)
    {name : Name} {info : ConstantInfo}
    (reached : SourceReach source groups.blocks (repsOf classes).toList name)
    (found : source.get? name = some info) :
    ∀ member ∈ x.aux,
      (∀ original ∈ sourceConstNames info, (keyName member.name).isPrefixOf original = false) ∧
      ∀ generated ∈ member.ctors,
        ∀ original ∈ sourceConstNames info, (keyName generated.name).isPrefixOf original = false := by
  have covered := sourceContext_reachable_names source (repsOf classes) groups.blocks reached found
  intro member included
  obtain ⟨auxFree, ctorFree⟩ := expand_aux_sourceFree source dedup classes groups keyAddr? run member included
  refine ⟨fun original inRecord => auxFree original (covered inRecord), ?_⟩
  exact fun generated inMember original inRecord => ctorFree generated inMember original (covered inRecord)

/-- Every emitted constructor is separate in both prefix directions from
the reserved later suffix families of every emitted auxiliary. -/
theorem expand_aux_suffixApart (source : Ix.Environment) (dedup : Dedup)
    (classes : Array (Array Name)) (groups : SourceGroups)
    (keyAddr? : Option (Name → Option Address)) {x : Expanded}
    (run : expandSourceSpec source dedup (repsOf classes) (aliasesOf classes) groups keyAddr? = .ok x) :
    ∀ member ∈ x.aux, ∀ generated ∈ member.ctors, ∀ auxiliary ∈ x.aux,
      ∀ suffix ∈ auxSuffixFamilies auxiliary.name, Apart (keyName generated.name) suffix := by
  intro member inAux generated inMember auxiliary otherAux suffix inSuffix
  obtain ⟨_, _, _, _, _, _, constructors⟩ :=
    expand_aux_originValues source dedup classes groups keyAddr? run member inAux
  obtain ⟨_, _, ctorFound⟩ := constructors generated inMember
  obtain ⟨storedCtor, ctorEntry, ctorKey⟩ := nameLookup_some_mem ctorFound
  obtain ⟨_, _, _, _, _, auxFound, _⟩ :=
    expand_aux_originValues source dedup classes groups keyAddr? run auxiliary otherAux
  obtain ⟨storedAux, auxEntry, auxKey⟩ := nameLookup_some_mem auxFound
  have sameSuffixes : auxSuffixFamilies storedAux = auxSuffixFamilies auxiliary.name := by
    unfold auxSuffixFamilies
    rw [auxKey]
  have separated := expand_originSuffixApart source dedup classes groups keyAddr? run
    _ ctorEntry _ auxEntry suffix (sameSuffixes.symm ▸ inSuffix)
  simpa only [ctorKey] using separated

/-- The actual component reaches the unrestricted interface, whose generic
success characterization identifies the exact canonical expansion. Protection
of all its emitted members/constructors then comes from its real source run.
The only public hypotheses are the original rule and success hypotheses. -/
theorem componentNested_sourceProtection {rules : Rules} (discovery : rules.nested = .discovery)
    {env : Ix.Compile.Canon.SourceEnv} {all : Array Name} {classes : Array (Array Name)}
    {nested : NestedCanon}
    (run : Ix.Compile.Canon.SourceBlock.componentNested rules env all classes = .ok (some nested)) :
    ∃ x, Ix.Compile.Canon.SourceBlock.canonExpand rules env classes = .ok x ∧
      nested.canonClasses = x.aux.map (fun member => #[member.name]) ∧
      sigsInOrder x nested.canonClasses = .ok nested.canon ∧
      AllocationForest (keyName (Name.mkStr x.all0 "_nested"))
        (x.auxToNested.entries.map (fun entry => keyName entry.1))
        (x.auxCtorMap.entries.map (fun entry => keyName entry.1)) ∧
      ∀ member ∈ x.aux,
        (∀ original ∈ (sourceContext env.source (repsOf classes) env.groupOf.blocks).protectedNames,
          (keyName member.name).isPrefixOf original = false) ∧
        ∀ generated ∈ member.ctors,
          ∀ original ∈ (sourceContext env.source (repsOf classes) env.groupOf.blocks).protectedNames,
            (keyName generated.name).isPrefixOf original = false := by
  rw [SourceComponentCoreProof.componentNested_eq_core] at run
  obtain ⟨x, generic, classesEq, signatures, _, _, _⟩ := componentNested_some discovery run
  have actual : Ix.Compile.Canon.SourceBlock.canonExpand rules env classes = .ok x := by
    rw [SourceComponentCoreProof.canonExpand_eq_core]
    exact generic
  refine ⟨x, actual, classesEq, signatures, ?_, ?_⟩
  · exact expand_originForest env.source rules.dedup classes env.groupOf
      (if rules.nested == .discovery then some env.addr? else none) actual
  · exact expand_aux_sourceFree env.source rules.dedup classes env.groupOf
      (if rules.nested == .discovery then some env.addr? else none) actual

end Ix.CompileCert.Canon.ComponentCoreProof
