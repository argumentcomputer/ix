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

Walks each seed's type + value + recursor rules + ctor links + `all` links
(of inductives, recursors, definitions, theorems and opaques) + auxiliary
family siblings (`Lean.auxFamilySiblings`) until no new names are
discovered. The returned list preserves the source environment's
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
        -- An auxiliary's family (`A.brecOn`/`B.brecOn`/`A.brecOn_1`, …) is
        -- one compiled block: its other members, and their dependencies,
        -- must be in the closure or the block's address depends on it
        -- (`Lean.auxFamilySiblings`).
        for r in Lean.auxFamilySiblings env.constants n do refs := refs.insert r
        match ci with
        -- A definition's `all` (its `mutual` siblings) is metadata the
        -- compiled entry names, and meta kernel ingress resolves each name
        -- through `named`: the sibling must be in the closure even when the
        -- value does not mention it (structural, well-founded and `partial`
        -- mutual definitions go through auxiliaries).
        | .defnInfo v =>
          for r in v.value.getUsedConstantsAsSet do refs := refs.insert r
          for mutName in v.all do refs := refs.insert mutName
        | .thmInfo v =>
          for r in v.value.getUsedConstantsAsSet do refs := refs.insert r
          for mutName in v.all do refs := refs.insert mutName
        | .opaqueInfo v =>
          for r in v.value.getUsedConstantsAsSet do refs := refs.insert r
          for mutName in v.all do refs := refs.insert mutName
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

/-- The recursors Lean generated for inductive `n`: `n.rec` and the nested
auxiliaries `n.rec_1`, `n.rec_2`, … (present on the first member of a block). -/
def recursorsOf (env : Lean.Environment) (n : Lean.Name) : List Lean.Name := Id.run do
  let mut out : List Lean.Name := []
  if env.constants.contains (Lean.mkRecName n) then out := Lean.mkRecName n :: out
  let mut i := 1
  while env.constants.contains (n.str s!"rec_{i}") do
    out := n.str s!"rec_{i}" :: out
    i := i + 1
  return out

/-- The constants the file itself elaborates (no imported module owns them),
closed over their transitive dependencies and over the recursors of every
inductive in the closure: the `--local` scope of `ix compile` and `ix
compile-lean`. A block's compiled form depends only on its dependency closure,
so on the file's own constants this scope compiles what the whole import
environment would, without recompiling the unrelated imports. The recursors
are there for the checkers, which read an inductive block together with its
recursor (a whole environment always has both). -/
def localConstList (fe : FileEnv) : List (Lean.Name × Lean.ConstantInfo) := Id.run do
  let env := fe.env
  let mut seeds : Std.HashSet Lean.Name := env.constants.toList.foldl (init := {})
    fun s (n, _) => if (env.getModuleIdxFor? n).isNone then s.insert n else s
  let mut closed := collectDeps env seeds.toList
  repeat
    let mut added := false
    for (n, ci) in closed do
      if ci matches .inductInfo _ then
        for r in recursorsOf env n do
          if !seeds.contains r then
            seeds := seeds.insert r
            added := true
    if !added then break
    -- The closure so far stays in: every name in it is reachable from a seed.
    closed := collectDeps env seeds.toList
  return closed

end Ix.EnvScope

end
