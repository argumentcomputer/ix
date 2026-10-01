/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Lean.Elab.Command
import Lean.Elab.ComputedFields
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.CSimpAttr
import Lean.Compiler.MetaAttr
import Lean.Compiler.IR.CompilerM
import Lean.Compiler.IR.EmitUtil
import Lean.Util.CollectAxioms

/-! # Runtime closure of the public operations

The theorems are about the Lean functions; execution runs their compiled
code. This audit walks the compiled code reachable from the public
operations: the IR the code generator emits, after proofs and types are
erased and `csimp` and `implemented_by` replacements are applied. It reports
every constant it reaches that execution treats specially:
* `@[extern]` symbols;
* `implemented_by` redirections and `unsafe` declarations. The overrides
  that `@[computed_field]` generates are both;
* `csimp` replacements, found by their source or, since the IR already
  calls the replacement, by their target;
* opaque constants with compiled code. On Lean 4.34 a `partial` definition
  executes this way, as an opaque whose code is compiled from its
  `_unsafe_rec` body, with no `implemented_by` entry.

Replacements that belong to Lean's own runtime (modules under the allowed
prefixes) are inherited execution foundations. Any other one fails the
audit unless a ruling (`RuntimeRulings`) names it exactly. Every audited
root must have compiled code, so the audit cannot pass vacuously. -/

open Lean Elab Command

namespace Ix.Kernel.Audit

structure RuntimeReport where
  /-- Compiled functions reached, roots included. -/
  visited : Array Name := #[]
  externs : Array Name := #[]
  implementedBy : Array (Name × Name) := #[]
  unsafes : Array Name := #[]
  csimp : Array (Name × Name) := #[]
  /-- Names reached that have no compiled code. -/
  uncompiled : Array Name := #[]
  /-- `csimp` entries whose replacement was reached: source, target, theorem. -/
  csimpTargets : Array (Name × Name × Name) := #[]
  /-- Opaque constants reached with compiled code of their own (not an
  extern, not an `implemented_by` redirection): `partial` definitions. -/
  opaqueCode : Array Name := #[]

/-- `csimp` entries by the name of their replacement. -/
def csimpByTarget (env : Environment) : NameMap (Array Compiler.CSimp.Entry) :=
  (Compiler.CSimp.ext.getState env).map.fold (init := {}) fun acc _ entry =>
    acc.insert entry.toDeclName ((acc.find? entry.toDeclName).getD #[] |>.push entry)

/-- Compiled code reachable through execution from `roots`. -/
partial def runtimeClosure (env : Environment) (roots : Array Name) : RuntimeReport :=
  go (csimpByTarget env) roots {} {}
where
  go (targets : NameMap (Array Compiler.CSimp.Entry)) (todo : Array Name) (seen : NameSet)
      (report : RuntimeReport) : RuntimeReport :=
    match todo.back? with
    | none => report
    | some name =>
      let todo := todo.pop
      if seen.contains name then go targets todo seen report else
      let seen := seen.insert name
      let report := if (env.find? name).any (·.isUnsafe) then
        { report with unsafes := report.unsafes.push name } else report
      let implementation := Compiler.getImplementedBy? env name
      let (todo, report) := match implementation with
        | some target =>
          (todo.push target, { report with implementedBy := report.implementedBy.push (name, target) })
        | none => (todo, report)
      let (todo, report) := match (Compiler.CSimp.ext.getState env).map.find? name with
        | some entry =>
          (todo.push entry.toDeclName, { report with csimp := report.csimp.push (name, entry.toDeclName) })
        | none => (todo, report)
      let report := match targets.find? name with
        | some entries =>
          let found := entries.map fun (entry : Compiler.CSimp.Entry) =>
            (entry.fromDeclName, entry.toDeclName, entry.thmName)
          { report with csimpTargets := report.csimpTargets ++ found }
        | none => report
      match IR.findEnvDecl env name with
      | none => go targets todo seen { report with uncompiled := report.uncompiled.push name }
      | some decl =>
        let report := { report with visited := report.visited.push name }
        match decl with
        | .extern .. => go targets todo seen { report with externs := report.externs.push name }
        | .fdecl .. =>
          let report := match env.find? name, implementation with
            | some (.opaqueInfo _), none => { report with opaqueCode := report.opaqueCode.push name }
            | _, _ => report
          go targets (todo ++ IR.collectUsedDecls env [decl]) seen report

/-- The module declaring `name`; the module being elaborated for a local
declaration. -/
def moduleOf (env : Environment) (name : Name) : Option Name :=
  match env.getModuleIdxFor? name with
  | some idx => env.header.moduleNames[idx.toNat]?
  | none => if env.contains name then some env.mainModule else none

/-- The standard logical axioms. -/
def standardAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

/-- Ruled exceptions to the runtime audit. Each field
names exactly what it admits; a project-level replacement that no field
names is still flagged. -/
structure RuntimeRulings where
  /-- Inductive types whose `@[computed_field]` machinery is admitted:
  the `unsafe` overrides `C._override` of each constructor, `casesOn._override`,
  and `f._override` of each computed field `f`, installed by `implemented_by`. -/
  computedFieldTypes : Array Name := #[]
  /-- Module prefixes whose `@[csimp]` replacements are admitted, each only
  when its theorem depends on no axiom outside `csimpAxioms`. -/
  csimpModules : Array Name := #[]
  csimpAxioms : Array Name := standardAxioms
  /-- Exact Lean runtime primitives (`withPtrEq`, `withPtrAddr` and
  their implementations; `isExclusiveUnsafe` behind `withExclusive`). They
  are inherited from `Init` anyway; naming them keeps them admitted under a
  narrower prefix list. -/
  primitives : Array Name := #[]
  /-- Exact `implemented_by` pairs (logical definition, `unsafe`
  implementation) whose type carries the obligation that licenses the
  substitution, such as `withExclusive`'s `k true = k false`. -/
  implementations : Array (Name × Name) := #[]
  /-- Modules whose `meta` declarations may be `unsafe` or `implemented_by`.
  `meta` code cannot be called from compiled non-`meta` code, so a
  declaration from these modules reached at run time that is not `meta`
  stays flagged. -/
  elaborationModules : Array Name := #[]
  /-- Module prefixes whose `partial` definitions are admitted. -/
  partialModules : Array Name := #[]

/-- What the audit found at one reached constant. -/
inductive Finding where
  | extern (name : Name)
  | implementedBy (name target : Name)
  | «unsafe» (name : Name)
  | csimp (source target thm : Name)
  | opaqueCode (name : Name)

def Finding.name : Finding → Name
  | .extern name | .implementedBy name _ | .unsafe name | .opaqueCode name => name
  | .csimp source _ _ => source

/-- The declaration whose module decides inheritance and rulings: the
theorem, for a `csimp` replacement. -/
def Finding.anchor : Finding → Name
  | .csimp _ _ thm => thm
  | finding => finding.name

def underAny (prefixes : Array Name) (module : Name) : Bool :=
  prefixes.any (·.isPrefixOf module)

/-- `name` is a `@[computed_field]` override of one of `types`: `p._override`
where `p` is a constructor, the `casesOn`, or a computed field of the type,
and `p` is `implemented_by` exactly `name`. -/
def computedFieldOverride (env : Environment) (types : Array Name) (name : Name) : Bool :=
  match name with
  | .str source "_override" =>
    let owner := match env.find? source with
      | some (.ctorInfo info) => some info.induct
      | _ => if Lean.Elab.ComputedFields.computedFieldAttr.hasTag env source ||
          source.getString! == "casesOn" then some source.getPrefix else none
    owner.any types.contains && Compiler.getImplementedBy? env source == some name
  | _ => false

/-- `name` is a `partial` definition, or its `_unsafe_rec` body, declared in
one of `modules`. -/
def partialIn (env : Environment) (modules : Array Name) (name : Name) : Bool :=
  let definition := match name with
    | .str source "_unsafe_rec" => source
    | _ => name
  let isPartial := match env.find? definition with
    | some (.opaqueInfo _) => env.contains (definition.str "_unsafe_rec")
    | _ => false
  isPartial && (moduleOf env definition).any (underAny modules)

/-- The ruling that admits `finding`, if any. -/
def RuntimeRulings.admits (rulings : RuntimeRulings) (finding : Finding) :
    CommandElabM (Option String) := do
  let env ← getEnv
  let name := finding.name
  if rulings.primitives.contains name then return some "primitive"
  match finding with
  | .extern _ => return none
  | .csimp _ _ thm =>
    unless (moduleOf env thm).any (underAny rulings.csimpModules) do return none
    let axioms ← collectAxioms thm
    return if axioms.all rulings.csimpAxioms.contains then some "csimp" else none
  | .opaqueCode _ => return if partialIn env rulings.partialModules name then some "partial" else none
  | .implementedBy _ target =>
    if computedFieldOverride env rulings.computedFieldTypes target then return some "computed_field"
    if rulings.implementations.contains (name, target) then return some "implemented_by"
    if isMarkedMeta env name && (moduleOf env name).any rulings.elaborationModules.contains then
      return some "elaboration"
    return none
  | .unsafe _ =>
    if computedFieldOverride env rulings.computedFieldTypes name then return some "computed_field"
    if rulings.implementations.any fun (source, target) =>
        target == name && Compiler.getImplementedBy? env source == some name then
      return some "implemented_by"
    if isMarkedMeta env name && (moduleOf env name).any rulings.elaborationModules.contains then
      return some "elaboration"
    if partialIn env rulings.partialModules name then return some "partial"
    return none

/-- Fail if any replaced or unchecked constant reached from `roots` lives
outside the allowed module prefixes and no ruling admits it, or a root has
no compiled code. -/
def checkRuntimeWith (roots : Array Name) (prefixes : Array Name) (rulings : RuntimeRulings) :
    CommandElabM Unit := do
  let env ← getEnv
  for root in roots do
    unless env.contains root do throwError m!"required root is missing: {root}"
    unless (IR.findEnvDecl env root).isSome || (Compiler.getImplementedBy? env root).isSome do
      throwError m!"root has no compiled code: {root}"
  let report := runtimeClosure env roots
  let inherited (name : Name) : Bool := (moduleOf env name).any (underAny prefixes)
  let findings := report.externs.map Finding.extern ++
    report.implementedBy.map (fun (name, target) => Finding.implementedBy name target) ++
    report.unsafes.map Finding.unsafe ++
    report.csimp.filterMap (fun (source, target) =>
      (((Compiler.CSimp.ext.getState env).map.find? source).map fun entry =>
        Finding.csimp source target entry.thmName)) ++
    report.csimpTargets.map (fun (source, target, thm) => Finding.csimp source target thm) ++
    report.opaqueCode.map Finding.opaqueCode
  let mut flagged : Array Name := #[]
  let mut ruled : Array (String × Name) := #[]
  for finding in findings do
    if inherited finding.anchor then continue
    match ← rulings.admits finding with
    | some ruling => unless ruled.contains (ruling, finding.name) do ruled := ruled.push (ruling, finding.name)
    | none => unless flagged.contains finding.name do flagged := flagged.push finding.name
  unless flagged.isEmpty do
    throwError m!"project-level execution replacements reached from {roots}:\n{flagged.qsort Name.lt}"
  let kinds := ruled.foldl (fun kinds (kind, _) => if kinds.contains kind then kinds else kinds.push kind) #[]
  let ruledSummary := if ruled.isEmpty then "" else
    "; ruled " ++ ", ".intercalate (kinds.toList.map fun kind =>
      s!"{kind} {(ruled.filter (·.1 == kind)).size}")
  logInfo m!"runtime closure of {roots}: {report.visited.size} compiled functions; inherited \
    externs {report.externs.size}, implemented_by {report.implementedBy.size}, unsafe \
    {report.unsafes.size}, csimp {report.csimp.size}{ruledSummary}"

/-- `checkRuntimeWith` with no rulings. -/
def checkRuntime (roots : Array Name) (prefixes : Array Name) : CommandElabM Unit :=
  checkRuntimeWith roots prefixes {}

end Ix.Kernel.Audit

/-! ## Controls -/

namespace Ix.Kernel.Audit.RuntimeControls

def plainSquare (n : Nat) : Nat := n * n

#guard_msgs (drop info) in
run_cmd Ix.Kernel.Audit.checkRuntime #[``plainSquare] #[`Init]

@[extern "ix_kernel_audit_control"]
opaque projectExtern (n : Nat) : Nat

def usesProjectExtern (n : Nat) : Nat := projectExtern n

/-- error: project-level execution replacements reached from [Ix.Kernel.Audit.RuntimeControls.usesProjectExtern]:
[Ix.Kernel.Audit.RuntimeControls.projectExtern] -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntime #[``usesProjectExtern] #[`Init]

unsafe def projectUnsafe (n : Nat) : Nat := n

@[implemented_by projectUnsafe]
def usesImplementedBy (n : Nat) : Nat := n

/-- error: project-level execution replacements reached from [Ix.Kernel.Audit.RuntimeControls.usesImplementedBy]:
[Ix.Kernel.Audit.RuntimeControls.projectUnsafe, Ix.Kernel.Audit.RuntimeControls.usesImplementedBy] -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntime #[``usesImplementedBy] #[`Init]

/-- An exact `implemented_by` ruling admits the pair and nothing else. -/
def pairRuling : Ix.Kernel.Audit.RuntimeRulings :=
  { implementations := #[(``usesImplementedBy, ``projectUnsafe)] }

/-- info: runtime closure of [Ix.Kernel.Audit.RuntimeControls.usesImplementedBy]: 1 compiled functions;
inherited externs 0, implemented_by 1, unsafe 1, csimp 0; ruled implemented_by 2 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith #[``usesImplementedBy] #[`Init] pairRuling

/-- error: project-level execution replacements reached from [Ix.Kernel.Audit.RuntimeControls.usesProjectExtern]:
[Ix.Kernel.Audit.RuntimeControls.projectExtern] -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith #[``usesProjectExtern] #[`Init] pairRuling

/-- A proof-only constant has no compiled code and cannot be audited. -/
theorem noCode : True := trivial

/-- error: root has no compiled code: Ix.Kernel.Audit.RuntimeControls.noCode -/
#guard_msgs in
run_cmd Ix.Kernel.Audit.checkRuntime #[``noCode] #[`Init]

/-! A `partial` definition executes as an opaque constant with compiled code;
the audit flags it unless its module is ruled. -/

partial def projectLoop (n : Nat) : Nat := if n > 100 then n else projectLoop (2 * n + 1)

def usesLoop (n : Nat) : Nat := projectLoop n + 1

/-- error: project-level execution replacements reached from [Ix.Kernel.Audit.RuntimeControls.usesLoop]:
[Ix.Kernel.Audit.RuntimeControls.projectLoop] -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntime #[``usesLoop] #[`Init]

/-- info: runtime closure of [Ix.Kernel.Audit.RuntimeControls.usesLoop]: 5 compiled functions;
inherited externs 3, implemented_by 0, unsafe 0, csimp 0; ruled partial 1 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith #[``usesLoop] #[`Init] { partialModules := #[`Ix.Kernel.Audit.Runtime] }

/-- error: project-level execution replacements reached from [Ix.Kernel.Audit.RuntimeControls.usesLoop]:
[Ix.Kernel.Audit.RuntimeControls.projectLoop] -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith #[``usesLoop] #[`Init] { partialModules := #[`Ix.Kernel.Audit.Imports] }

/-! `@[computed_field]` overrides are `unsafe`; the ruling names the type. -/

inductive Tree where
  | leaf (n : Nat)
  | node (left right : Tree)
with
  @[computed_field] size : Tree → Nat
  | .leaf _ => 1
  | .node left right => left.size + right.size + 1

def treeSize (n : Nat) : Nat := (Tree.node (.leaf n) (.leaf 0)).size

/-- error: project-level execution replacements reached from [Ix.Kernel.Audit.RuntimeControls.treeSize]:
[Ix.Kernel.Audit.RuntimeControls.Tree.leaf._override, Ix.Kernel.Audit.RuntimeControls.Tree.node._override] -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntime #[``treeSize] #[`Init]

/-- info: runtime closure of [Ix.Kernel.Audit.RuntimeControls.treeSize]: 5 compiled functions;
inherited externs 1, implemented_by 0, unsafe 2, csimp 0; ruled computed_field 2 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith #[``treeSize] #[`Init] { computedFieldTypes := #[``Tree] }

/-- error: project-level execution replacements reached from [Ix.Kernel.Audit.RuntimeControls.treeSize]:
[Ix.Kernel.Audit.RuntimeControls.Tree.leaf._override, Ix.Kernel.Audit.RuntimeControls.Tree.node._override] -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith #[``treeSize] #[`Init] { computedFieldTypes := #[``Nat] }

/-! A `csimp` replacement is found by its target; the ruling admits it only
with a theorem on the standard axioms. -/

def slowId (n : Nat) : Nat := n
@[noinline] def fastId (n : Nat) : Nat := n + 0
@[csimp] theorem slowId_eq : @slowId = @fastId := by funext n; rfl
def usesSlowId (n : Nat) : Nat := slowId n

/-- error: project-level execution replacements reached from [Ix.Kernel.Audit.RuntimeControls.usesSlowId]:
[Ix.Kernel.Audit.RuntimeControls.slowId] -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntime #[``usesSlowId] #[`Init]

/-- info: runtime closure of [Ix.Kernel.Audit.RuntimeControls.usesSlowId]: 2 compiled functions;
inherited externs 0, implemented_by 0, unsafe 0, csimp 0; ruled csimp 1 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith #[``usesSlowId] #[`Init] { csimpModules := #[`Ix.Kernel.Audit] }

/-- error: project-level execution replacements reached from [Ix.Kernel.Audit.RuntimeControls.usesSlowId]:
[Ix.Kernel.Audit.RuntimeControls.slowId] -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith #[``usesSlowId] #[`Init] { csimpModules := #[`Ix.Kernel.Audit], csimpAxioms := #[] }

/-! The elaboration-time ruling admits `meta` declarations of the named
modules only; a non-`meta` pair there stays flagged. -/

meta unsafe def metaUnsafe (n : Nat) : Nat := n

@[implemented_by metaUnsafe]
meta def metaEval (n : Nat) : Nat := n + 1

/-- info: runtime closure of [Ix.Kernel.Audit.RuntimeControls.metaEval]: 1 compiled functions;
inherited externs 0, implemented_by 1, unsafe 1, csimp 0; ruled elaboration 2 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith #[``metaEval] #[`Init] { elaborationModules := #[`Ix.Kernel.Audit.Runtime] }

/-- error: project-level execution replacements reached from [Ix.Kernel.Audit.RuntimeControls.usesImplementedBy]:
[Ix.Kernel.Audit.RuntimeControls.projectUnsafe, Ix.Kernel.Audit.RuntimeControls.usesImplementedBy] -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith #[``usesImplementedBy] #[`Init] { elaborationModules := #[`Ix.Kernel.Audit.Runtime] }

end Ix.Kernel.Audit.RuntimeControls
