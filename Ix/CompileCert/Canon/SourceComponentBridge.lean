import Ix.Compile.Canon.ComponentCore
import Ix.CompileCert.Canon.CoreBridge
import Ix.CompileCert.Canon.NestedCanonSource

/-!
The previously checked finite-source bridge, relocated to explicit SourceEnv
and SourceBlock names. Its complete result/error statements are retained. The
relocation is UNCOMPILED; the runtime adapter consumes these exact source thunks.
-/

namespace Ix.CompileCert.Canon.SourceComponentCoreProof

open Ix.Compile.Canon
open Ix (Name MutConst)

theorem mutConstOf_eq_core (env : Ix.Compile.Canon.SourceEnv) (name : Name) :
    Ix.Compile.Canon.SourceBlock.mutConstOf env name =
      ComponentCore.mutConstOf (ComponentCore.Env.ofSource env) name := rfl

theorem blockComponents_eq_core (env : Ix.Compile.Canon.SourceEnv) (all : Array Name) :
    Ix.Compile.Canon.SourceBlock.blockComponents env all =
      ComponentCore.blockComponents (ComponentCore.Env.ofSource env) all := rfl

theorem canonExpand_eq_core (rules : Rules) (env : Ix.Compile.Canon.SourceEnv)
    (classes : Array (Array Name)) :
    Ix.Compile.Canon.SourceBlock.canonExpand rules env classes =
      ComponentCore.canonExpand (ComponentCore.Protection.ofSource env) rules
        (ComponentCore.Env.ofSource env) classes := by
  exact CoreBridge.expand_eq_core env.source rules.dedup (repsOf classes)
    (aliasesOf classes) env.groupOf
    (if rules.nested == .discovery then some env.addr? else none)

/-- Includes every early return, both expansion failures, ordering/signature
and permutation failures, and every field of the optional NestedCanon. -/
theorem componentNested_eq_core (rules : Rules) (env : Ix.Compile.Canon.SourceEnv)
    (all : Array Name) (classes : Array (Array Name)) :
    Ix.Compile.Canon.SourceBlock.componentNested rules env all classes =
      ComponentCore.componentNested (ComponentCore.Protection.ofSource env) rules
        (ComponentCore.Env.ofSource env) all classes := by
  unfold Ix.Compile.Canon.SourceBlock.componentNested ComponentCore.componentNested
  simp only [CoreBridge.expand_eq_core, ComponentCore.canonExpand]
  rfl

/-- Includes the out-of-range error, every skipped position/component,
all lookup/address decisions, and the complete updated NestedCanon. -/
theorem evaporate_eq_core (env : Ix.Compile.Canon.SourceEnv) (rules : Rules)
    (all : Array Name) (comps : Array (Array (Array Name)))
    (here : Nat) (nested : NestedCanon) :
    Ix.Compile.Canon.SourceBlock.evaporate env rules all comps here nested =
      ComponentCore.evaporate (ComponentCore.Protection.ofSource env)
        (ComponentCore.Env.ofSource env) rules all comps here nested := by
  unfold Ix.Compile.Canon.SourceBlock.evaporate ComponentCore.evaporate
  simp only [CoreBridge.expand_eq_core]
  rfl

/-- The actual component caller reaches the generic component construction.
No success, source completeness, freshness, address or group premise is added. -/
theorem canonBlock_eq_core (rules : Rules) (env : Ix.Compile.Canon.SourceEnv)
    (all : Array Name) :
    Ix.Compile.Canon.SourceBlock.canonBlock rules env all =
      ComponentCore.canonBlock (ComponentCore.Protection.ofSource env) rules
        (ComponentCore.Env.ofSource env) all := by
  have constants : Ix.Compile.Canon.SourceBlock.mutConstOf env =
      ComponentCore.mutConstOf (ComponentCore.Env.ofSource env) := by
    funext name
    exact mutConstOf_eq_core env name
  have evaporation : Ix.Compile.Canon.SourceBlock.evaporate env =
      ComponentCore.evaporate (ComponentCore.Protection.ofSource env)
        (ComponentCore.Env.ofSource env) := by
    funext rules all comps here nested
    exact evaporate_eq_core env rules all comps here nested
  unfold Ix.Compile.Canon.SourceBlock.canonBlock ComponentCore.canonBlock
  simp only [blockComponents_eq_core, constants, componentNested_eq_core, evaporation]
  rfl

theorem canonBlock_outputs_eq (rules : Rules) (env : Ix.Compile.Canon.SourceEnv)
    (all : Array Name) {left right : BlockCanon}
    (actual : Ix.Compile.Canon.SourceBlock.canonBlock rules env all = .ok left)
    (generic : ComponentCore.canonBlock (ComponentCore.Protection.ofSource env) rules
      (ComponentCore.Env.ofSource env) all = .ok right) : left = right := by
  have same := canonBlock_eq_core rules env all
  rw [actual, generic] at same
  exact Except.ok.inj same

theorem canonBlock_errors_iff (rules : Rules) (env : Ix.Compile.Canon.SourceEnv)
    (all : Array Name) (error : String) :
    (Ix.Compile.Canon.SourceBlock.canonBlock rules env all = .error error) ↔
      (ComponentCore.canonBlock (ComponentCore.Protection.ofSource env) rules
        (ComponentCore.Env.ofSource env) all = .error error) := by
  rw [canonBlock_eq_core]

end Ix.CompileCert.Canon.SourceComponentCoreProof
