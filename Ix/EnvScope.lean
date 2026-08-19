/-
  Shared environment-scoping helpers for the CLI drivers: the transitive
  dependency closure and the default (unfiltered) constant list of a file.

  Lives under the `Ix.EnvScope` namespace (not top-level in a Cli module) so
  test modules can import it: `Tests.Ix.Compile.ValidateAux` carries its own
  top-level `collectDeps` mirror, and a top-level name here would collide
  with it as soon as both reach `Tests.Main`.
-/
module
public import Ix.Meta

public section

namespace Ix.EnvScope

/-- Collect the transitive closure of constants referenced by a set of seed
names. Mirrors the identically-named helper in `Tests/Ix/Compile/ValidateAux.lean`
so the CLI and test runner share the same dep-discovery semantics.

Walks each seed's type + value + recursor rules + ctor/all links until no
new names are discovered. The returned list preserves the source environment's
iteration order over the computed name set. -/
partial def collectDeps (env : Lean.Environment) (seeds : List Lean.Name)
    : List (Lean.Name × Lean.ConstantInfo) := Id.run do
  let mut needed : Std.HashSet Lean.Name := {}
  let mut worklist := seeds
  while !worklist.isEmpty do
    match worklist with
    | [] => break
    | n :: rest =>
      worklist := rest
      if needed.contains n then continue
      needed := needed.insert n
      if let some ci := env.constants.find? n then
        let mut refs : Lean.NameSet := ci.type.getUsedConstantsAsSet
        match ci with
        | .defnInfo v =>
          for r in v.value.getUsedConstantsAsSet do refs := refs.insert r
        | .thmInfo v =>
          for r in v.value.getUsedConstantsAsSet do refs := refs.insert r
        | .opaqueInfo v =>
          for r in v.value.getUsedConstantsAsSet do refs := refs.insert r
        | .inductInfo v =>
          for ctorName in v.ctors do
            refs := refs.insert ctorName
            if let some ctorCi := env.constants.find? ctorName then
              for r in ctorCi.type.getUsedConstantsAsSet do refs := refs.insert r
          for mutName in v.all do
            refs := refs.insert mutName
        | .ctorInfo v =>
          refs := refs.insert v.induct
        | .recInfo v =>
          for mutName in v.all do
            refs := refs.insert mutName
          for rule in v.rules do
            for r in rule.rhs.getUsedConstantsAsSet do refs := refs.insert r
        | _ => pure ()
        for r in refs do
          if !needed.contains r then
            worklist := r :: worklist
  env.constants.toList.filter fun (n, _) => needed.contains n

/-- Default (unfiltered) constant list for a file env. Classic files keep the
historical whole-import-env behavior (byte-identical artifacts). Module-mode
files seed from the module-visible surface — the `OLeanLevel.exported` name
set plus everything the file itself elaborates — closed over transitive deps
against the full-content env: referenced foreign `_private.*` proof
auxiliaries are pulled in (their content is mandatory for groundedness and
their named rows for decompile/tc lookups), while unreferenced foreign
privates stay out — the qualified-package isolation the `module` header asks
for. Content always comes from `fe.env` (full, private-level); the exported
view contributes names only. -/
def defaultConstList (fe : FileEnv) (pathStr : String)
    : IO (List (Lean.Name × Lean.ConstantInfo)) := do
  if !fe.isModule then
    return fe.env.constants.toList
  let some visible ← moduleVisibleNames pathStr
    | return fe.env.constants.toList
  let mut seeds : List Lean.Name := []
  for (n, _) in fe.env.constants.toList do
    if visible.contains n || (fe.env.getModuleIdxFor? n).isNone then
      seeds := n :: seeds
  let closed := collectDeps fe.env seeds
  IO.println s!"[env] module scope: {seeds.length} visible seed constant(s), \
{closed.length} after transitive-dep closure"
  return closed

end Ix.EnvScope

end
