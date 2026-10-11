import Ix.CompileCert.Canon.ComponentBridge
import Ix.CompileCert.Canon.ComponentProtection
import Ix.Compile.Pass.ImageView

/-!
Complete production-adapter refinement. The old finite program remains under
explicit SourceEnv/SourceBlock/SourceSpec names. Every equality below compares
an entire return value, including refusals and all result fields. Protection is
constructed from actual source data, not supplied as an extra caller premise.
This relocation is uncompiled and byte neutrality is untested until the full gates.
-/

namespace Ix.CompileCert.Canon.SourceAdapter
open Ix.Compile.Canon
open Ix.Compile.Canon.FreshFamilySeparation
open Ix (Name)

/-- Every old callback environment embeds without any predicate on its callbacks. -/
theorem callbacks_exact (const? : Name → Option Ix.ConstantInfo)
    (addr? : Name → Option Address) (groups : GroupOf) :
    (Env.ofCallbacks const? addr? groups).const? = const? ∧
    (Env.ofCallbacks const? addr? groups).addr? = addr? ∧
    (Env.ofCallbacks const? addr? groups).groupOf = groups := ⟨rfl, rfl, rfl⟩

/-- The production canonical protection thunk is exactly the reachable-source
collector at the actual representatives and registry, still delayed by Unit. -/
theorem source_canonical_protection (env : SourceEnv) (members : Array Name) :
    (Env.ofSource env).protection.canonical members =
      fun () => (sourceContext env.source members env.groupOf.blocks).protectedNames := rfl

/-- Source-order discovery retains Lean's grouping and the exact source closure. -/
theorem source_discovery_protection (env : SourceEnv) (members : Array Name) :
    (Env.ofSource env).protection.source members =
      fun () => (sourceContext env.source members leanSourceGroup.blocks).protectedNames := rfl

theorem mutConstOf_eq_spec (env : SourceEnv) (name : Name) :
    mutConstOf (Env.ofSource env) name = SourceBlock.mutConstOf env name := by
  exact (ComponentCoreProof.mutConstOf_eq_core (Env.ofSource env) name).trans
    (SourceComponentCoreProof.mutConstOf_eq_core env name).symm

theorem blockComponents_eq_spec (env : SourceEnv) (all : Array Name) :
    blockComponents (Env.ofSource env) all = SourceBlock.blockComponents env all := by
  exact (ComponentCoreProof.blockComponents_eq_core (Env.ofSource env) all).trans
    (SourceComponentCoreProof.blockComponents_eq_core env all).symm

theorem canonExpand_eq_spec (rules : Rules) (env : SourceEnv) (classes : Array (Array Name)) :
    canonExpand rules (Env.ofSource env) classes = SourceBlock.canonExpand rules env classes := by
  exact (ComponentCoreProof.canonExpand_eq_core rules (Env.ofSource env) classes).trans
    (SourceComponentCoreProof.canonExpand_eq_core rules env classes).symm

theorem componentNested_eq_spec (rules : Rules) (env : SourceEnv)
    (all : Array Name) (classes : Array (Array Name)) :
    componentNested rules (Env.ofSource env) all classes =
      SourceBlock.componentNested rules env all classes := by
  exact (ComponentCoreProof.componentNested_eq_core rules (Env.ofSource env) all classes).trans
    (SourceComponentCoreProof.componentNested_eq_core rules env all classes).symm

theorem evaporate_eq_spec (env : SourceEnv) (rules : Rules) (all : Array Name)
    (comps : Array (Array (Array Name))) (here : Nat) (nested : NestedCanon) :
    evaporate (Env.ofSource env) rules all comps here nested =
      SourceBlock.evaporate env rules all comps here nested := by
  exact (ComponentCoreProof.evaporate_eq_core (Env.ofSource env) rules all comps here nested).trans
    (SourceComponentCoreProof.evaporate_eq_core env rules all comps here nested).symm

theorem canonBlock_eq_spec (rules : Rules) (env : SourceEnv) (all : Array Name) :
    canonBlock rules (Env.ofSource env) all = SourceBlock.canonBlock rules env all := by
  exact (ComponentCoreProof.canonBlock_eq_core rules (Env.ofSource env) all).trans
    (SourceComponentCoreProof.canonBlock_eq_core rules env all).symm

/-- The real compiled-component path preserves all sorting guards, skipped
components, nested data, evaporation, and complete errors. -/
theorem canonBlockCompiled_eq_spec (env : SourceEnv) (compiled? : Name → Bool)
    (all : Array Name) :
    Ix.Compile.Pass.canonBlockCompiled (Env.ofSource env) compiled? all =
      Ix.Compile.Pass.canonBlockCompiledSourceSpec env compiled? all := by
  have constants : mutConstOf (Env.ofSource env) = SourceBlock.mutConstOf env := by
    funext name
    exact mutConstOf_eq_spec env name
  have nested : componentNested Rules.compiler (Env.ofSource env) all =
      SourceBlock.componentNested Rules.compiler env all := by
    funext classes
    exact componentNested_eq_spec Rules.compiler env all classes
  have evaporation : evaporate (Env.ofSource env) = SourceBlock.evaporate env := by
    funext rules names comps here entry
    exact evaporate_eq_spec env rules names comps here entry
  have addresses : (Env.ofSource env).addr? = env.addr? := rfl
  unfold Ix.Compile.Pass.canonBlockCompiled Ix.Compile.Pass.canonBlockCompiledSourceSpec
  simp only [blockComponents_eq_spec, constants, nested, evaporation, addresses]

/-- The production buildView result is unchanged as a complete Except value.
The remainder of image construction is byte-for-byte retained in the companion. -/
theorem buildView_eq_spec (input : Ix.Compile.Pass.ViewInput) (all : Array Name) :
    Ix.Compile.Pass.buildView input all = Ix.Compile.Pass.buildViewSourceSpec input all := by
  unfold Ix.Compile.Pass.buildView Ix.Compile.Pass.buildViewSourceSpec
  simp only [canonBlockCompiled_eq_spec]

/-- Actual production, rather than only a retained companion, has the proven
source-derived family separation. No closure/freshness premise is added. -/
theorem componentNested_sourceProtection {rules : Rules} (discovery : rules.nested = .discovery)
    {env : SourceEnv} {all : Array Name} {classes : Array (Array Name)} {nested : NestedCanon}
    (run : componentNested rules (Env.ofSource env) all classes = .ok (some nested)) :
    ∃ x, canonExpand rules (Env.ofSource env) classes = .ok x ∧
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
  rw [componentNested_eq_spec] at run
  obtain ⟨x, expanded, classesEq, signatures, forest, free⟩ :=
    ComponentCoreProof.componentNested_sourceProtection discovery run
  exact ⟨x, by rw [canonExpand_eq_spec]; exact expanded, classesEq, signatures, forest, free⟩

end Ix.CompileCert.Canon.SourceAdapter
