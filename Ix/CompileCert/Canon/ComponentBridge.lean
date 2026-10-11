import Ix.Compile.Canon.Block
import Ix.CompileCert.Canon.SourceComponentBridge
import Ix.CompileCert.Canon.CoreBridge
import Ix.CompileCert.Canon.NestedCanonSource

/-! Complete result/error bridges for the actual public callback entry points.
The concrete source implementation is retained in SourceComponentBridge; these
statements quantify over all callbacks and all fixed protection data. No success
premise is used in any function equality. The relocation is UNCOMPILED. -/

namespace Ix.CompileCert.Canon.ComponentCoreProof

open Ix.Compile.Canon
open Ix (Name MutConst)

theorem mutConstOf_eq_core (env : Ix.Compile.Canon.Env) (name : Name) :
    Ix.Compile.Canon.mutConstOf env name =
      ComponentCore.mutConstOf env.asCore name := rfl

theorem blockComponents_eq_core (env : Ix.Compile.Canon.Env) (all : Array Name) :
    Ix.Compile.Canon.blockComponents env all =
      ComponentCore.blockComponents env.asCore all := rfl

theorem canonExpand_eq_core (rules : Rules) (env : Ix.Compile.Canon.Env)
    (classes : Array (Array Name)) :
    Ix.CompileCert.Canon.canonExpand rules env classes =
      ComponentCore.canonExpand env.protection rules
        env.asCore classes := by
  rfl

/-- Includes every early return, both expansion failures, ordering/signature
and permutation failures, and every field of the optional NestedCanon. -/
theorem componentNested_eq_core (rules : Rules) (env : Ix.Compile.Canon.Env)
    (all : Array Name) (classes : Array (Array Name)) :
    Ix.Compile.Canon.componentNested rules env all classes =
      ComponentCore.componentNested env.protection rules
        env.asCore all classes := by
  rfl

/-- Includes the out-of-range error, every skipped position/component,
all lookup/address decisions, and the complete updated NestedCanon. -/
theorem evaporate_eq_core (env : Ix.Compile.Canon.Env) (rules : Rules)
    (all : Array Name) (comps : Array (Array (Array Name)))
    (here : Nat) (nested : NestedCanon) :
    Ix.Compile.Canon.evaporate env rules all comps here nested =
      ComponentCore.evaporate env.protection
        env.asCore rules all comps here nested := by
  rfl

/-- The actual component caller reaches the generic component construction.
No success, source completeness, freshness, address or group premise is added. -/
theorem canonBlock_eq_core (rules : Rules) (env : Ix.Compile.Canon.Env)
    (all : Array Name) :
    Ix.Compile.Canon.canonBlock rules env all =
      ComponentCore.canonBlock env.protection rules
        env.asCore all := by
  rfl

theorem canonBlock_outputs_eq (rules : Rules) (env : Ix.Compile.Canon.Env)
    (all : Array Name) {left right : BlockCanon}
    (actual : Ix.Compile.Canon.canonBlock rules env all = .ok left)
    (generic : ComponentCore.canonBlock env.protection rules
      env.asCore all = .ok right) : left = right := by
  have same := canonBlock_eq_core rules env all
  rw [actual, generic] at same
  exact Except.ok.inj same

theorem canonBlock_errors_iff (rules : Rules) (env : Ix.Compile.Canon.Env)
    (all : Array Name) (error : String) :
    (Ix.Compile.Canon.canonBlock rules env all = .error error) ↔
      (ComponentCore.canonBlock env.protection rules
        env.asCore all = .error error) := by
  rw [canonBlock_eq_core]

end Ix.CompileCert.Canon.ComponentCoreProof
