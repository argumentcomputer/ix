import LSpec
import Ix.CompileM

/-! Finite boundary controls for declaration-header numbers. These directly
exercise structured compiler inputs, without claiming that oversized headers
are well-typed Lean declarations or allocating huge arrays/telescopes. -/

namespace Tests.Ix.Compile.HeaderCounts

open LSpec
open _root_.Ix (Name Expr Level ConstantVal ConstructorVal RecursorVal RecursorRule InductiveVal Ind Def)
open _root_.Ix.CompileM

private def name := Name.fromLeanName `HeaderBoundary
private def context : CompileEnv × BlockEnv :=
  ({ (default : CompileEnv) with pass3 := true },
    { all := {}, current := name, mutCtx := {}, univCtx := [] })
private def sourceType := Expr.mkSort Level.mkZero
private def cnst : ConstantVal := { name, levelParams := #[], type := sourceType }
private def ctor : ConstructorVal :=
  { cnst, induct := name, cidx := 0, numParams := 0, numFields := 0, isUnsafe := false }
private def recursor : RecursorVal :=
  { cnst, all := #[], numParams := 0, numIndices := 0, numMotives := 0, numMinors := 0,
    rules := #[], k := false, isUnsafe := false }
private def inductiveVal : InductiveVal :=
  { cnst, numParams := 0, numIndices := 0, all := #[], ctors := #[], numNested := 0,
    isRec := false, isUnsafe := false, isReflexive := false }
private def inductiveData : Ind :=
  { name, levelParams := #[], type := sourceType, numParams := 0, numIndices := 0,
    all := #[], ctors := #[], numNested := 0, isRec := false, isUnsafe := false, isReflexive := false }
private def metadata : InductiveTypeCompileMeta :=
  { arena := {}, metaSharing := #[], metaUnivs := #[], univPatches := #[] }
private def raw (action : CompileM α) (state : BlockState := {}) : Except CompileError α × BlockState := (action context).run state
private def refused (result : Except CompileError α) : Bool := match result with
  | .error (.resourceLimit _) => true
  | _ => false

private def ruleAt (fields : Nat) : RecursorRule := { ctor := name, nfields := fields, rhs := Expr.mkBVar 0 }

def controls : List (String × Bool) := Id.run do
  let last := UInt64.size - 1
  let mut result := []
  for fields in [0, 1, last] do
    let (compiled, _) := raw (compileRecursorRule (ruleAt fields))
    result := result ++ [(s!"recursor rule preserves {fields} fields",
      compiled.toOption.map (fun output => output.1.fields.toNat) == some fields)]
  for fields in [UInt64.size, UInt64.size + 7] do
    result := result ++ [(s!"recursor rule refuses {fields} fields", refused (raw (compileRecursorRule (ruleAt fields))).1)]
  let badRule := ruleAt UInt64.size
  result := result ++ [("recursor rule loop propagates header overflow",
    refused (raw (compileRecursorRules [ruleAt 0, badRule] {})).1)]
  let (_, failedRule) := raw (compileRecursorRule badRule)
  result := result ++ [("rule overflow retains completed RHS effects",
    failedRule.arena.nodes == #[.leaf] && failedRule.exprCache.contains badRule.rhs)]
  for count in [UInt64.size, UInt64.size + 7] do
    for (label, modified) in [
        ("constructor index", { ctor with cidx := count }),
        ("constructor parameters", { ctor with numParams := count }),
        ("constructor fields", { ctor with numFields := count })] do
      let (compiled, _) := raw (finishConstructorCompilation modified (.sort 0) 0)
      result := result ++ [(s!"{label} refuses {count}", refused compiled)]
    for (label, modified) in [
        ("recursor parameters", { recursor with numParams := count }),
        ("recursor indices", { recursor with numIndices := count }),
        ("recursor motives", { recursor with numMotives := count }),
        ("recursor minors", { recursor with numMinors := count })] do
      let (compiled, _) := raw (finishRecursorCompilation modified (.sort 0) 0 {})
      result := result ++ [(s!"{label} refuses {count}", refused compiled)]
    for (label, modified) in [
        ("inductive parameters", { inductiveVal with numParams := count }),
        ("inductive indices", { inductiveVal with numIndices := count })] do
      result := result ++ [(s!"{label} refuses {count}",
        refused (raw (finishInductiveCompilation modified (.sort 0) 0 metadata {})).1)]
    for (label, modified) in [
        ("mutual inductive parameters", { inductiveData with numParams := count }),
        ("mutual inductive indices", { inductiveData with numIndices := count })] do
      result := result ++ [(s!"{label} refuses {count}",
        refused (raw (finishInductiveDataCompilation modified (.sort 0) 0 metadata {})).1)]
  let maxCtor := { ctor with cidx := last, numParams := last, numFields := last }
  let ctorResult := (raw (finishConstructorCompilation maxCtor (.sort 0) 0)).1
  result := result ++ [("constructor maximum headers remain exact", ctorResult.toOption.any fun output =>
    output.1.cidx.toNat == last && output.1.params.toNat == last && output.1.fields.toNat == last)]
  let maxRec := { recursor with numParams := last, numIndices := last, numMotives := last, numMinors := last }
  let recResult := (raw (finishRecursorCompilation maxRec (.sort 0) 0 {})).1
  result := result ++ [("recursor maximum headers remain exact", recResult.toOption.any fun output =>
    output.1.params.toNat == last && output.1.indices.toNat == last && output.1.motives.toNat == last && output.1.minors.toNat == last)]
  let maxInd := { inductiveVal with numParams := last, numIndices := last }
  let indResult := (raw (finishInductiveCompilation maxInd (.sort 0) 0 metadata {})).1
  let maxData := { inductiveData with numParams := last, numIndices := last }
  let dataResult := (raw (finishInductiveDataCompilation maxData (.sort 0) 0 metadata {})).1
  result := result ++ [("inductive maximum headers remain exact", indResult.toOption.any fun output =>
    output.1.params.toNat == last && output.1.indices.toNat == last),
    ("mutual inductive maximum headers remain exact", dataResult.toOption.any fun output =>
      output.1.params.toNat == last && output.1.indices.toNat == last)]
  let params := #[Name.fromLeanName `u, Name.fromLeanName `v]
  let polymorphic := { cnst with levelParams := params }
  let definition : Def := {
    name := name
    levelParams := params
    type := sourceType
    value := Expr.mkBVar 0
    kind := .defn
    hints := .opaque
    safety := .safe
    all := #[] }
  result := result ++ [
    ("definition preserves universe arity", (raw (finishDefinitionDataCompilation definition (.sort 0) 0 (.var 0) 1)).1.toOption.any
      (fun output => output.1.lvls == 2)),
    ("axiom preserves universe arity", (raw (finishAxiomCompilation ⟨polymorphic, false⟩ (.sort 0) 0)).1.toOption.any
      (fun output => output.1.lvls == 2)),
    ("quotient preserves universe arity", (raw (finishQuotientCompilation ⟨polymorphic, .type⟩ (.sort 0) 0)).1.toOption.any
      (fun output => output.1.lvls == 2)),
    ("recursor preserves universe arity", (raw (finishRecursorCompilation { recursor with cnst := polymorphic } (.sort 0) 0 {})).1.toOption.any
      (fun output => output.1.lvls == 2)),
    ("constructor preserves universe arity", (raw (finishConstructorCompilation { ctor with cnst := polymorphic } (.sort 0) 0)).1.toOption.any
      (fun output => output.1.lvls == 2)),
    ("inductive preserves universe arity", (raw (finishInductiveCompilation { inductiveVal with cnst := polymorphic }
      (.sort 0) 0 metadata {})).1.toOption.any (fun output => output.1.lvls == 2)),
    ("mutual inductive preserves universe arity", (raw (finishInductiveDataCompilation { inductiveData with levelParams := params }
      (.sort 0) 0 metadata {})).1.toOption.any (fun output => output.1.lvls == 2))]
  let heads := #[(name, name)]
  let initial : BlockState := {
    arena := { nodes := #[.leaf] }
    refs := #[default]
    univs := #[.zero]
    exprCache := ({} : Std.HashMap _ _).insert (Expr.mkBVar 0) (.var 0, 0)
    p3Heads := heads }
  let (failed, failedState) := raw (finishConstructorCompilation { ctor with numFields := UInt64.size } (.sort 0) 0) initial
  result := result ++ [("header refusal drains per-constant state and retains tables and claims",
    refused failed && failedState.arena.nodes.isEmpty && failedState.exprCache.isEmpty &&
      failedState.refs == initial.refs && failedState.univs == initial.univs && failedState.p3Heads == heads)]
  return result

def suite : List TestSeq := controls.map fun (label, ok) => test s!"header count: {label}" ok

end Tests.Ix.Compile.HeaderCounts
