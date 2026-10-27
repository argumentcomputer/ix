import Lean.Elab.Command
import Lean.Util.FoldConsts

/-! # Exact axiom checks for the kernel's public roots

Adapted from the `jcb/ix-kernel-consistency` branch's
`Ix.Kernel.Verify.Audit.AxiomAudit`. The traversal follows checked types,
bodies, and inductive constructor types directly, so it sees dependencies that
imported axiom summaries can omit. The checked sets use resolved declaration
names; both missing and additional axioms fail, so a namespace migration
cannot silently widen a recorded boundary.

`#guard_kernel_axioms root [axioms]` fails elaboration unless the transitive
axiom set of `root` is exactly the listed one. `#guard_module_axioms` and
`#guard_module_axioms_under` bound every safe declaration of whole modules by
the standard logical axioms (below). The negative controls at the end of this
module exercise each rejection. -/

open Lean Elab Command

namespace Ix.Kernel.Audit

/-- Constants referenced directly by a declaration's checked type, body, and
constructor list. -/
def directConstants : ConstantInfo → Array Name
  | .axiomInfo v => v.type.getUsedConstants
  | .defnInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .thmInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .opaqueInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .quotInfo _ => #[]
  | .ctorInfo v => v.type.getUsedConstants
  | .recInfo v => v.type.getUsedConstants
  | .inductInfo v => v.type.getUsedConstants ++ v.ctors

structure State where
  visited : NameSet := {}
  names : Array Name := #[]
  /-- Declarations that reference `sorryAx` directly. -/
  origins : Array Name := #[]
  axioms : Array Name := #[]

structure Node where
  isAxiom : Bool := false
  dependencies : Array Name := #[]

/-- Direct dependencies may be reused across roots in one fixed environment.
Reachability and axiom sets are computed afresh for each root. -/
abbrev Cache := NameMap Node

abbrev M := ReaderT Environment (StateM (State × Cache))

partial def visit (name : Name) : M Unit := do
  let (state, cache) ← get
  unless state.visited.contains name do
    let env ← read
    let (node, cache) := match cache.find? name with
      | some node => (node, cache)
      | none =>
        let node : Node := match env.checked.get.find? name with
          | some info =>
            { isAxiom := (info matches .axiomInfo _)
              dependencies := directConstants info }
          | none => {}
        (node, cache.insert name node)
    let state := { state with
      visited := state.visited.insert name
      names := state.names.push name
      axioms := if node.isAxiom then state.axioms.push name else state.axioms
      origins := if name != ``sorryAx && node.dependencies.contains ``sorryAx then
        state.origins.push name else state.origins }
    set (state, cache)
    node.dependencies.forM visit

def collectCached (env : Environment) (root : Name) (cache : Cache) : State × Cache :=
  ((visit root).run env).run ({}, cache) |>.2

/-- The transitive closure of `root` with its axioms and direct `sorryAx` users. -/
def collect (env : Environment) (root : Name) : State :=
  (collectCached env root {}).1

/-- Fail unless `root` exists and its axiom set is exactly `expected`. -/
def checkAxioms (root : Name) (expected : Array Name) : CommandElabM Unit := do
  let env ← getEnv
  unless env.contains root do
    throwError m!"required root is missing: {root}"
  let actual := (collect env root).axioms
  unless actual.qsort Name.lt == expected.qsort Name.lt do
    let missing := expected.filter (!actual.contains ·)
    let additional := actual.filter (!expected.contains ·)
    throwError m!"axiom boundary changed for {root}\n\
      expected but absent: {missing}\nactual but unlisted: {additional}"

syntax (name := guardKernelAxioms) "#guard_kernel_axioms " ident " [" ident,* "]" : command

elab_rules : command
  | `(#guard_kernel_axioms $root:ident [$axioms:ident,*]) => do
    let rootName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo root
    let expected ← axioms.getElems.mapM fun axiomSyntax =>
      liftCoreM <| realizeGlobalConstNoOverloadWithInfo axiomSyntax
    checkAxioms rootName expected

/-! ## Whole modules

`#guard_module_axioms M₁ M₂ …` fails elaboration unless every safe
declaration of each named module (every constant the module adds, auxiliary
ones included) depends on no axiom beyond the standard logical axioms `propext`,
`Classical.choice` and `Quot.sound`. Unsafe declarations (the implementations
behind `implemented_by` and `partial`, which may use the compiler's `lcProof`)
are outside the logic: no safe declaration can refer to one. A named module
that is not imported, or that declares nothing safe, fails as well, so a
listed module cannot drop out of the check unnoticed.
`#guard_module_axioms_under P₁ P₂ …` checks every imported module whose name
some `Pᵢ` prefixes, skips the ones that declare nothing safe, and fails if a
`Pᵢ` prefixes no imported module.

One traversal covers all the declarations at once; on a failure, each module
is traversed again to name the declarations that reach the extra axiom. -/

/-- The standard logical axioms. -/
def logicalAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

/-- The axioms that the closures of `decls` reach, together. -/
def axiomsOf (env : Environment) (decls : Array Name) : Array Name :=
  (((decls.forM visit).run env).run ({}, {})).2.1.axioms

/-- The safe declarations of an imported module. -/
def moduleDecls (env : Environment) (module : Name) : Option (Array Name) := do
  let idx ← env.getModuleIdx? module
  return (← env.header.moduleData[idx]?).constants.filterMap fun c =>
    if c.isUnsafe then none else some c.name

/-- At most `limit` declarations of `decls` whose closure reaches `ax`. -/
def reaching (env : Environment) (decls : Array Name) (ax : Name) (limit : Nat := 5) :
    Array Name := Id.run do
  let mut out := #[]
  let mut cache : Cache := {}
  for d in decls do
    if out.size ≥ limit then break
    let (state, cache') := collectCached env d cache
    cache := cache'
    if state.axioms.contains ax then out := out.push d
  return out

/-- Fail unless every declaration of every module in `modules` depends on no
axiom beyond `allowed`. With `allowEmpty`, a module that declares nothing is
skipped; otherwise it fails. -/
def checkModules (modules : Array Name) (allowEmpty : Bool := false)
    (allowed : Array Name := logicalAxioms) : CommandElabM Unit := do
  let env ← getEnv
  let mut all : Array Name := #[]
  let mut present : Array (Name × Array Name) := #[]
  for m in modules do
    let some decls := moduleDecls env m | throwError m!"module is not imported: {m}"
    if decls.isEmpty then
      if allowEmpty then continue
      throwError m!"module declares nothing: {m}"
    all := all ++ decls
    present := present.push (m, decls)
  if (axiomsOf env all).all allowed.contains then return
  let mut lines : Array String := #[]
  for (m, decls) in present do
    for ax in (axiomsOf env decls).filter (!allowed.contains ·) do
      lines := lines.push s!"  {m}: {ax}, reached from {reaching env decls ax}"
  throwError m!"axiom boundary changed: beyond {allowed}\n{"\n".intercalate lines.toList}"

/-- The imported modules whose names `pre` prefixes. -/
def modulesUnder (env : Environment) (pre : Name) : Array Name :=
  env.header.moduleNames.filter (pre.isPrefixOf ·)

syntax (name := guardModuleAxioms) "#guard_module_axioms " ident+ : command
syntax (name := guardModuleAxiomsUnder) "#guard_module_axioms_under " ident+ : command

elab_rules : command
  | `(#guard_module_axioms $modules:ident*) =>
    checkModules (modules.map (·.getId))
  | `(#guard_module_axioms_under $prefixes:ident*) => do
    let env ← getEnv
    let mut modules : Array Name := #[]
    for p in prefixes.map (·.getId) do
      let under := modulesUnder env p
      if under.isEmpty then throwError m!"no imported module under {p}"
      modules := modules ++ under
    checkModules modules (allowEmpty := true)

end Ix.Kernel.Audit

/-! ## Controls

Successful exact checks in both directions, a constructor that depends on its
whole inductive definition, cache reuse across roots, and the two rejection
directions. -/

#guard_kernel_axioms Eq.refl []
#guard_kernel_axioms propext [propext]

private inductive AuditFixture : Prop where
  | plain
  | withAxiom (proof : propext (Iff.rfl : True ↔ True) = rfl)

#guard_kernel_axioms AuditFixture.plain [propext]

run_cmd do
  let env ← getEnv
  let (first, cache) := Ix.Kernel.Audit.collectCached env ``AuditFixture.plain {}
  let (independent, cache) := Ix.Kernel.Audit.collectCached env ``Eq.refl cache
  let (sibling, _) := Ix.Kernel.Audit.collectCached env ``AuditFixture.withAxiom cache
  unless first.axioms == #[``propext] && independent.axioms.isEmpty &&
      sibling.axioms == #[``propext] do
    throwError "cached axiom traversal changed a root's dependency boundary"

/--
error: axiom boundary changed for propext
expected but absent: []
actual but unlisted: [propext]
-/
#guard_msgs (whitespace := lax) in
#guard_kernel_axioms propext []

/--
error: axiom boundary changed for Eq.refl
expected but absent: [propext]
actual but unlisted: []
-/
#guard_msgs (whitespace := lax) in
#guard_kernel_axioms Eq.refl [propext]

/-- error: required root is missing: Ix.Kernel.Audit.doesNotExist -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkAxioms `Ix.Kernel.Audit.doesNotExist #[]

/-! Whole modules: a clean module passes, a module that declares `sorryAx`
fails and names it, and a missing module or prefix fails. -/

#guard_module_axioms Init.Data.List.Lemmas
#guard_module_axioms_under Init.Data.List

run_cmd do
  let rejected ← try
      Ix.Kernel.Audit.checkModules #[`Init.Prelude]
      pure false
    catch e => pure ((← e.toMessageData.toString).contains "Init.Prelude: sorryAx")
  unless rejected do
    throwError "the module check accepted a module that declares sorryAx"

/-- error: module is not imported: Ix.Kernel.Audit.NoSuchModule -/
#guard_msgs (whitespace := lax) in
#guard_module_axioms Ix.Kernel.Audit.NoSuchModule

/-- error: no imported module under Ix.Kernel.Audit.NoSuchModule -/
#guard_msgs (whitespace := lax) in
#guard_module_axioms_under Ix.Kernel.Audit.NoSuchModule
