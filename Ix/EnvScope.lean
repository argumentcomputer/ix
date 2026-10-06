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
public import Ix.Compile.Image.Expr
public import Ix.Compile.Pass.Cliques

public section

namespace Ix.EnvScope

/-- The recursors Lean generated for inductive `n`: `n.rec` and the nested
auxiliaries `n.rec_1`, `n.rec_2`, … (present on the first member of a block). -/
def recursorsOf (env : Lean.Environment) (n : Lean.Name) : List Lean.Name :=
  Lean.sourceRecursorsOf env.constants n

/-- Source declarations needed by the compiler's sizeOf rewrite, discovered
from the selected declaration's own owner, never from its callers. A generated
`all₀._sizeOf_N` may use the instances of other components of its declared
mutual family after splitting. Include all existing family instances as a
conservative source set; O11a's scheduler separately adds only the precise
cross-component edges. These are closure-membership links, not dependency
edges: the instance's reference back to its own sizeOf function is harmless
in this finite visited-set walk and must not become a new scheduling cycle.

The selected walk also carries the whole logical unit of every declaration
it reaches (`Lean.unitMembers`, design document §6.3): eager auxiliaries and
whichever on-demand auxiliaries exist (equation lemmas, `_arg_pusher`
lemmas, splitters, `match_N`). These belong to the unit, not to a caller:
a block may read them (a clique its equation lemmas), so a closure that
lacked them could compile the block differently from the whole environment.
(Before M1-d the selected walk took argument pushers and equation lemmas
only when a carried proof referenced them.) -/
def compilerSupportOf (env : Lean.Environment) (n : Lean.Name) : List Lean.Name :=
  Lean.compilerSupportOf env.constants n

/-- Collect the transitive closure of constants referenced by a set of seed
names: the closure producer behind `ix compile --consts`/`--module`/`--exclude`,
`ix validate-lean --ns`/`--local`, the module scope of `defaultConstList` and the
closure suites.

Walks each seed's type + value + recursor rules + ctor links + `all` links
(of inductives, recursors, definitions, theorems and opaques) + auxiliary
family siblings (`Lean.auxFamilySiblings`) until no new names are discovered.
The returned list preserves the source environment's iteration order over the
computed name set. (`Tests/Ix/Compile/ValidateAux.lean` keeps its own mirror.)

`withRecursors` also adds **the recursors of every inductive** (`recursorsOf`:
`I.rec`, and `I.rec_N` on a nested block's first member). The closure modes
whose output is handed to the checkers set it (`ix compile --consts`, `--local`
via `localConstList`, `ix validate-lean --ns`, `--local`): the certified checker
reads an inductive block together with its recursor and declines it otherwise
(`reader: inductive block without a recursor in the input`); a whole
environment always has both. It is off by default so that a whole-file compile
(`defaultConstList`, including the module scope) and the other producers
include exactly what they did before (A3v follow-up: the fixtures' bytes and
the Rust producer are unchanged). A block's compiled form depends only on its
dependency closure, so adding recursors moves no address already in the
closure. `withCompilerSupport` additionally follows `compilerSupportOf` and the
whole logical unit (`Lean.unitMembers`, §6.3) at
every visited declaration. Selected CLI scopes use `collectSelectedDeps` to
enable these and the separate `withCheckerSupport` certificate-ground policy;
a raw caller must opt in explicitly. Certificate ground is not a compiler
rewrite or scheduling edge and does not change the frozen checker pins. -/
partial def collectDeps (env : Lean.Environment) (seeds : List Lean.Name)
    (withRecursors : Bool := false)
    (withCompilerSupport : Bool := false)
    (withCheckerSupport : Bool := false)
    : List (Lean.Name × Lean.ConstantInfo) := Id.run do
  let units : Lean.UnitIndex := if withCompilerSupport then Lean.unitIndex env.constants else {}
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
        if withCheckerSupport then
          for r in Lean.checkerSupportOf env.constants n do refs := refs.insert r
        if withCompilerSupport then
          for r in compilerSupportOf env n do refs := refs.insert r
          -- the whole logical unit of the declaration (§6.3)
          for r in Lean.unitMembers env.constants units n do refs := refs.insert r
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
          if withRecursors then
            for r in recursorsOf env n do refs := refs.insert r
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

/-- The library constants the compiler's output may reference although the
selected declarations' Lean terms do not (design document §6.3, obligation 2
of a pass whose output adds a reference: every closure producer carries the
target): the Pass 3 images' packing and rule constants
(`Ix.Compile.Image.imageSupport`) and the clique transport's
(`Ix.Compile.Pass.transportPrereqs`: `monotone_compose`, `Eq.trans`, `id`,
the `PSigma`/`PSum` case splits). Read from the compiler's own declarations,
so a constant a pass starts to introduce is carried once it is declared
there. Only the ones the environment has. -/
def introducedSupport (env : Lean.Environment) : List Lean.Name :=
  let rec toLean : Ix.Name → Lean.Name
    | .anonymous _ => .anonymous
    | .str p s _ => .str (toLean p) s
    | .num p i _ => .num (toLean p) i
  ((Ix.Compile.Image.imageSupport ++ Ix.Compile.Pass.transportPrereqs).toList.map toLean).eraseDups.filter
    env.contains

/-- A selected compiler/checker input closes recursors, compiler support and
certificate ground (`Lean.checkerSupportOf`), together with the compiler's introduced
references (`introducedSupport`), to the same fixed point as ordinary
source references, mutual `all` members,
and auxiliary-family siblings. Raw collection and whole-file/module-default
selection retain their existing contract through `collectDeps`'s defaults. -/
def collectSelectedDeps (env : Lean.Environment) (seeds : List Lean.Name) :
    List (Lean.Name × Lean.ConstantInfo) :=
  collectDeps env (seeds ++ introducedSupport env) (withRecursors := true) (withCompilerSupport := true)
    (withCheckerSupport := true)

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

/-- The constants the file itself elaborates (no imported module owns them),
closed over their transitive dependencies (with the recursors of every
inductive and compiler support, through `collectSelectedDeps`): the `--local` scope of `ix
compile`, `ix compile-lean` and `ix validate-lean`. A block's compiled form
depends only on its dependency closure, so on the file's own constants this
scope compiles what the whole import environment would, without recompiling
the unrelated imports. -/
def localConstList (fe : FileEnv) : List (Lean.Name × Lean.ConstantInfo) :=
  let env := fe.env
  let seeds := env.constants.toList.filterMap fun (n, _) =>
    if (env.getModuleIdxFor? n).isNone then some n else none
  collectSelectedDeps env seeds

end Ix.EnvScope

end
