import Lean.Elab.Command
import Lean.Elab.ComputedFields
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.CSimpAttr
import Lean.Compiler.MetaAttr
import Lean.Compiler.IR.CompilerM
import Lean.Compiler.IR.EmitUtil
import IxCK.Kernel.Audit.Axioms

/-! # Runtime closure of the public operations

The theorems are about the Lean functions; execution runs their compiled
code. This audit walks the compiled code reachable from the public
operations: the IR the code generator emits, after proofs and types are
erased and `csimp` and `implemented_by` replacements are applied. It reports
every constant it reaches that execution treats specially:
* `@[extern]` symbols;
* `implemented_by` redirections, found by their source, by their
  implementation when a caller's IR already calls the implementation, or by
  walking logical definition bodies from the reached functions when an
  `@[inline]` or auto-inlined implementation (direct or behind inlined
  wrappers) leaves no call in the IR, and `unsafe` declarations. The overrides
  that `@[computed_field]` generates are both;
* `csimp` replacements, found by their source, by their target when the IR
  already calls the replacement, or by walking logical definition bodies
  when an `@[inline]` replacement target was inlined into its caller;
* the source `f` of each arity-reduced auxiliary `f._redArg` reached, whose
  code the auxiliary carries;
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
  /-- `implemented_by` substitutions met at their implementation: a caller's compiled
  code already calls the implementation, so the walk reaches it without the
  source. Each entry is the source and the implementation reached. -/
  implementationsReached : Array (Name × Name) := #[]

/-- All `csimp` entries registered across imported modules and the current
module. `(Compiler.CSimp.ext.getState env).map` keys by `fromDeclName`, so a
second `@[csimp]` for the same source in a downstream module overwrites the
first in `map`; reading `getModuleEntries` keeps every entry. -/
def allCSimpEntries (env : Environment) : Array Compiler.CSimp.Entry := Id.run do
  let mut entries : Array Compiler.CSimp.Entry := #[]
  for idx in [0:env.header.moduleNames.size] do
    for s in Compiler.CSimp.ext.ext.getModuleEntries env (idx : ModuleIdx) do
      let e := match s with
        | .global e => e
        | .scoped _ e => e
      unless entries.any (·.thmName == e.thmName) do
        entries := entries.push e
  for (_, e) in (Compiler.CSimp.ext.getState env).map do
    unless entries.any (·.thmName == e.thmName) do
      entries := entries.push e
  return entries

/-- `csimp` entries by the name of their replacement. -/
def csimpByTarget (env : Environment) : NameMap (Array Compiler.CSimp.Entry) :=
  (allCSimpEntries env).foldl (init := {}) fun acc entry =>
    acc.insert entry.toDeclName ((acc.find? entry.toDeclName).getD #[] |>.push entry)

/-- `csimp` entries by the name of the declaration they replace. -/
def csimpBySource (env : Environment) : NameMap (Array Compiler.CSimp.Entry) :=
  (allCSimpEntries env).foldl (init := {}) fun acc entry =>
    acc.insert entry.fromDeclName ((acc.find? entry.fromDeclName).getD #[] |>.push entry)

/-- `implemented_by` entries by their implementation, over every module: the
walk meets a substitution at its implementation when the source's callers were
compiled against it. -/
def implementedByTargets (env : Environment) : NameMap (Array Name) := Id.run do
  let ext := Compiler.implementedByAttr.ext
  let add (acc : NameMap (Array Name)) (source target : Name) : NameMap (Array Name) :=
    acc.insert target ((acc.find? target).getD #[] |>.push source)
  let mut acc : NameMap (Array Name) := {}
  for idx in [0:env.header.moduleNames.size] do
    for (source, target) in ext.getModuleEntries env (idx : ModuleIdx) do
      acc := add acc source target
  return (ext.getState env).2.foldl (fun acc source target => add acc source target) acc

/-- Whether `s` is a compiler-generated specialization suffix (`_spec_<n>` or `spec_<n>`). -/
def isSpecSuffix (s : String) : Bool :=
  let rest? := if s.startsWith "_spec_" then some (s.drop 6)
    else if s.startsWith "spec_" then some (s.drop 5)
    else none
  match rest? with
  | some rest => !rest.isEmpty && rest.all Char.isDigit
  | none => false

/-- Whether `s` is a compiler-generated wrapper/auxiliary suffix. -/
def isCompilerSuffix (s : String) : Bool :=
  s == "_redArg" || s == "_boxed" || s == "_impl" || isSpecSuffix s

/-- Prefix before the earliest `_at_` component in a specialized name
(`Foo._at_.Caller.spec_0` → `some Foo`, handling nested `_at_`s). -/
def stripAtPrefix? : Name → Option Name
  | .str p "_at_" =>
    match stripAtPrefix? p with
    | some root => some root
    | none => some p
  | .str p _ => stripAtPrefix? p
  | .num p _ => stripAtPrefix? p
  | .anonymous => none

/-- Strip trailing compiler-generated suffixes (`_redArg`, `_boxed`, `_impl`,
`spec_<n>`, `_spec_<n>`) down to a declaration present in `env`. -/
def stripSuffixesSource? (env : Environment) : Name → Option Name
  | .str source s =>
    if isCompilerSuffix s then
      match stripSuffixesSource? env source with
      | some root => some root
      | none => if env.contains source then some source else none
    else none
  | _ => none

/-- The source declaration a compiler-generated auxiliary (`_redArg`, `_boxed`,
`_impl`, `_spec_<n>`, `._at_.<caller>.spec_<n>`) was derived from. The code
generator drops erased and unused parameters or boxes/specializes calls by
moving or wrapping `f`'s body under a suffixed name, so a closure that reaches
the auxiliary executes `f`'s code under another name. The walk visits `f` as
well, where its `unsafe`, `implemented_by`, `csimp` and `partial` status is
reported. -/
def reducedAritySource? (env : Environment) (name : Name) : Option Name :=
  match stripAtPrefix? name with
  | some base =>
    match stripSuffixesSource? env base with
    | some root => some root
    | none => if env.contains base then some base else none
  | none => stripSuffixesSource? env name

/-- Compiled code reachable through execution from `roots`. When `skipLogical`
returns `true` for a constant (e.g. inherited runtime prefixes like `Init`/`Std`),
its direct `implemented_by`/`csimp` status is still inspected and targets are
followed, but the logical body walk does not recurse into its definition body. -/
partial def runtimeClosure (env : Environment) (roots : Array Name)
    (skipLogical : Name → Bool := fun _ => false) : RuntimeReport :=
  let csimpSources := csimpBySource env
  let report := go (csimpByTarget env) csimpSources (implementedByTargets env) roots {} {}
  let seenImpl : NameSet :=
    report.implementedBy.foldl (fun s (n, _) => s.insert n) <|
      report.implementationsReached.foldl (fun s (n, _) => s.insert n) {}
  let seenCSimp : NameSet :=
    report.csimp.foldl (fun s (n, _) => s.insert n) <|
      report.csimpTargets.foldl (fun s (n, _, _) => s.insert n) {}
  let seenUnsafe : NameSet := report.unsafes.foldl (fun s n => s.insert n) {}
  let seenExtern : NameSet := report.externs.foldl (fun s n => s.insert n) {}
  let seenOpaque : NameSet := report.opaqueCode.foldl (fun s n => s.insert n) {}
  let (initTodo, initQueued) : Array Name × NameSet :=
    (report.visited ++ roots).foldl (init := (#[], {})) fun (todo, queued) n =>
      if skipLogical n || queued.contains n then (todo, queued)
      else (todo.push n, queued.insert n)
  scanLogical csimpSources initTodo initQueued seenImpl seenCSimp seenUnsafe seenExtern seenOpaque report
where
  /-- Walk project-level logical definition bodies from reached functions so that
  `@[inline]` or auto-inlined `@[implemented_by]`, `@[csimp]`, `partial`, `unsafe`,
  and `@[extern]` declarations (even behind multiple inlined wrapper definitions,
  chains crossing inherited prefixes, or ruled targets) cannot vanish from
  post-inlining IR undetected. `queued` deduplicates at push time (`O(V + E)`). -/
  scanLogical (csimpSources : NameMap (Array Compiler.CSimp.Entry))
      (initTodo : Array Name) (initQueued initSeenImpl initSeenCSimp initSeenUnsafe initSeenExtern initSeenOpaque : NameSet)
      (initReport : RuntimeReport) : RuntimeReport := Id.run do
    let mut todo := initTodo
    let mut queued := initQueued
    let mut seenImpl := initSeenImpl
    let mut seenCSimp := initSeenCSimp
    let mut seenUnsafe := initSeenUnsafe
    let mut seenExtern := initSeenExtern
    let mut seenOpaque := initSeenOpaque
    let mut report := initReport
    while h : todo.size > 0 do
      let name := todo.back
      todo := todo.pop
      if let some target := Compiler.getImplementedBy? env name then
        unless queued.contains target do
          todo := todo.push target
          queued := queued.insert target
        unless seenImpl.contains name do
          seenImpl := seenImpl.insert name
          report := { report with implementationsReached := report.implementationsReached.push (name, target) }
      if let some entries := csimpSources.find? name then
        for e in entries do
          unless queued.contains e.toDeclName do
            todo := todo.push e.toDeclName
            queued := queued.insert e.toDeclName
        unless seenCSimp.contains name do
          seenCSimp := seenCSimp.insert name
          for e in entries do
            report := { report with
              csimpTargets := report.csimpTargets.push (e.fromDeclName, e.toDeclName, e.thmName) }
      if skipLogical name then
        continue
      if !seenUnsafe.contains name && (env.find? name).any (·.isUnsafe) then
        seenUnsafe := seenUnsafe.insert name
        report := { report with unsafes := report.unsafes.push name }
      let isExt := match IR.findEnvDecl env name with
        | some (.extern ..) => true
        | _ => isExtern env name
      if !seenExtern.contains name && isExt then
        seenExtern := seenExtern.insert name
        report := { report with externs := report.externs.push name }
      let hasImpl := (Compiler.getImplementedBy? env name).isSome
      if let some (.opaqueInfo _) := env.find? name then
        let unsafeRec := name.str "_unsafe_rec"
        let hasUnsafeRec := env.contains unsafeRec
        let hasCompiledCode := match IR.findEnvDecl env name with
          | some (.fdecl _ #[] _ (.ret .erased) _) => false
          | some (.fdecl ..) => true
          | _ => false
        if !seenOpaque.contains name && !isExt && !hasImpl && (hasCompiledCode || hasUnsafeRec) then
          seenOpaque := seenOpaque.insert name
          report := { report with opaqueCode := report.opaqueCode.push name }
        if hasUnsafeRec && !queued.contains unsafeRec then
          todo := todo.push unsafeRec
          queued := queued.insert unsafeRec
      unless hasImpl do
        let val? := match env.find? name with
          | some (.defnInfo v) => some v.value
          | some (.opaqueInfo v) => some v.value
          | _ => none
        if let some val := val? then
          for c in val.getUsedConstants do
            unless queued.contains c do
              todo := todo.push c
              queued := queued.insert c
    return report
  go (targets : NameMap (Array Compiler.CSimp.Entry))
      (csimpSources : NameMap (Array Compiler.CSimp.Entry))
      (implementations : NameMap (Array Name))
      (todo : Array Name) (seen : NameSet) (report : RuntimeReport) : RuntimeReport :=
    match todo.back? with
    | none => report
    | some name =>
      let todo := todo.pop
      if seen.contains name then go targets csimpSources implementations todo seen report else
      let seen := seen.insert name
      let todo := match reducedAritySource? env name with
        | some source => todo.push source
        | none => todo
      let report := if (env.find? name).any (·.isUnsafe) then
        { report with unsafes := report.unsafes.push name } else report
      let implementation := Compiler.getImplementedBy? env name
      let (todo, report) := match implementation with
        | some target =>
          (todo.push target, { report with implementedBy := report.implementedBy.push (name, target) })
        | none => (todo, report)
      let (todo, report) : Array Name × RuntimeReport := match csimpSources.find? name with
        | some entries =>
          entries.foldl (init := (todo, report)) fun ((todo, report) : Array Name × RuntimeReport) entry =>
            (todo.push entry.toDeclName,
              { report with csimp := report.csimp.push (name, entry.toDeclName) })
        | none => (todo, report)
      let report := match targets.find? name with
        | some entries =>
          let found := entries.map fun (entry : Compiler.CSimp.Entry) =>
            (entry.fromDeclName, entry.toDeclName, entry.thmName)
          { report with csimpTargets := report.csimpTargets ++ found }
        | none => report
      let report := match implementations.find? name with
        | some sources =>
          { report with implementationsReached :=
              report.implementationsReached ++ sources.map ((·, name)) }
        | none => report
      match IR.findEnvDecl env name with
      | none =>
        go targets csimpSources implementations todo seen
          { report with uncompiled := report.uncompiled.push name }
      | some decl =>
        let report := { report with visited := report.visited.push name }
        match decl with
        | .extern .. =>
          go targets csimpSources implementations todo seen
            { report with externs := report.externs.push name }
        | .fdecl .. =>
          let report := match env.find? name, implementation with
            | some (.opaqueInfo _), none => { report with opaqueCode := report.opaqueCode.push name }
            | _, _ => report
          let usedIr := IR.collectUsedDecls env [decl]
          go targets csimpSources implementations (todo ++ usedIr) seen report

/-- The module declaring `name`; the module being elaborated for a local
declaration. -/
def moduleOf (env : Environment) (name : Name) : Option Name :=
  match env.getModuleIdxFor? name with
  | some idx => env.header.moduleNames[idx.toNat]?
  | none => if env.contains name then some env.mainModule else none

/-- The standard logical axioms. -/
def standardAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

/-- An `implemented_by` substitution admitted on an explicit assumption, not
a proof: the logical definition `source` executes as `target`, whose compiled
code reaches the foreign primitives `externs`. -/
structure AssumedSubstitution where
  source : Name
  target : Name
  externs : Array Name

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
  /-- Substitutions admitted on an assumption (`AssumedSubstitution`). Each
  must be installed (`source` is `implemented_by` exactly `target`), and
  `externs` must be exactly the foreign primitives `target`'s own closure
  reaches. The code generator calls `target` in place of `source`, and may
  inline it, so a closure applies the substitution where it reaches `target`
  or those primitives: the substitution is reported, and the primitives are
  admitted. The kernel's own closures admit none; the one substitution the
  root library's authenticated entries admit, the BLAKE3 admission hash
  (`Address.admissionHash` executed as `Address.blake3`), is enumerated in
  `Ix.Kernel.Audit.assumedSubstitutions`. -/
  assumed : Array AssumedSubstitution := #[]

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
  | .extern _ => return if rulings.assumed.any (·.externs.contains name) then some "assumed" else none
  | .csimp _ _ thm =>
    unless (moduleOf env thm).any (underAny rulings.csimpModules) do return none
    let axioms := (Ix.Kernel.Audit.collect (← getEnv) thm).axioms
    return if axioms.all rulings.csimpAxioms.contains then some "csimp" else none
  | .opaqueCode _ => return if partialIn env rulings.partialModules name then some "partial" else none
  | .implementedBy _ target =>
    if computedFieldOverride env rulings.computedFieldTypes target then return some "computed_field"
    if rulings.assumed.any (fun s => s.source == name && s.target == target) then return some "assumed"
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

/-- Collect all non-inherited findings from `report` and classify them as
admitted (ruled) or unruled (flagged). -/
def evaluateReport (inherited : Name → Bool) (rulings : RuntimeRulings)
    (csimpSources : NameMap (Array Compiler.CSimp.Entry)) (report : RuntimeReport)
    (initRuled : Array (String × Name) := #[]) :
    CommandElabM (Array Name × Array (String × Name)) := do
  let findings := report.externs.map Finding.extern ++
    report.implementedBy.map (fun (name, target) => Finding.implementedBy name target) ++
    report.unsafes.map Finding.unsafe ++
    (report.csimp.flatMap fun (source, target) =>
      ((csimpSources.find? source).getD #[]).filterMap fun entry =>
        if entry.toDeclName == target then some (Finding.csimp source target entry.thmName) else none) ++
    report.csimpTargets.map (fun (source, target, thm) => Finding.csimp source target thm) ++
    report.opaqueCode.map Finding.opaqueCode
  let mut flagged : Array Name := #[]
  let mut ruled : Array (String × Name) := initRuled
  for finding in findings do
    if inherited finding.anchor then continue
    match ← rulings.admits finding with
    | some ruling => unless ruled.contains (ruling, finding.name) do ruled := ruled.push (ruling, finding.name)
    | none => unless flagged.contains finding.name do flagged := flagged.push finding.name
  -- A substitution met at its implementation: flagged unless inherited or ruled. One that is
  -- admitted adds nothing to the summary below.
  for (source, target) in report.implementationsReached do
    if inherited source then continue
    if (← rulings.admits (.implementedBy source target)).isNone then
      unless flagged.contains source do flagged := flagged.push source
  return (flagged, ruled)

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
  let csimpSources := csimpBySource env
  let inherited (name : Name) : Bool := (moduleOf env name).any (underAny prefixes)
  for s in rulings.assumed do
    unless Compiler.getImplementedBy? env s.source == some s.target do
      throwError m!"assumed substitution is not installed: {s.source} implemented_by {s.target}"
    let targetReport := runtimeClosure env #[s.target] inherited
    let own := targetReport.externs.filter (!inherited ·) |>.qsort Name.lt
    unless own == s.externs.qsort Name.lt do
      throwError m!"assumed substitution {s.source}: {s.target} reaches the externs {own}, not {s.externs}"
    let (targetFlagged, _) ← evaluateReport inherited rulings csimpSources targetReport
    unless targetFlagged.isEmpty do
      throwError m!"assumed substitution {s.source}: {s.target} reaches unruled execution replacements:\n{targetFlagged.qsort Name.lt}"
  let report := runtimeClosure env roots inherited
  -- the substitution is applied where its implementation's primitives are reached
  let applied := rulings.assumed.filter fun s =>
    s.externs.any report.externs.contains || report.visited.contains s.target
  let (flagged, ruled) ← evaluateReport inherited rulings csimpSources report
    (applied.map fun s => ("assumed", s.source))
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

/-! An assumed substitution admits exactly the foreign primitives its
implementation reaches, and is reported where they are reached (the code
generator calls the implementation in place of the definition, and here
inlines it); a ruling must name the implementation's primitives exactly. -/

def assumedTarget (n : Nat) : Nat := projectExtern n

@[implemented_by assumedTarget]
def assumedSource (n : Nat) : Nat := n

def usesAssumed (n : Nat) : Nat := assumedSource n + 1

def assumedRuling : Ix.Kernel.Audit.RuntimeRulings :=
  { assumed := #[{ source := ``assumedSource, target := ``assumedTarget, externs := #[``projectExtern] }] }

/-- error: project-level execution replacements reached from [Ix.Kernel.Audit.RuntimeControls.usesAssumed]:
[Ix.Kernel.Audit.RuntimeControls.assumedSource, Ix.Kernel.Audit.RuntimeControls.projectExtern] -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntime #[``usesAssumed] #[`Init]

/-- info: runtime closure of [Ix.Kernel.Audit.RuntimeControls.usesAssumed]: 3 compiled functions;
inherited externs 2, implemented_by 0, unsafe 0, csimp 0; ruled assumed 2 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith #[``usesAssumed] #[`Init] assumedRuling

def missingExterns : Ix.Kernel.Audit.RuntimeRulings :=
  { assumed := #[{ source := ``assumedSource, target := ``assumedTarget, externs := #[] }] }

/-- error: assumed substitution Ix.Kernel.Audit.RuntimeControls.assumedSource: Ix.Kernel.Audit.RuntimeControls.assumedTarget
reaches the externs [Ix.Kernel.Audit.RuntimeControls.projectExtern], not [] -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith #[``usesAssumed] #[`Init] missingExterns

def notInstalled : Ix.Kernel.Audit.RuntimeRulings :=
  { assumed := #[{ source := ``usesAssumed, target := ``assumedTarget, externs := #[``projectExtern] }] }

/-- error: assumed substitution is not installed: Ix.Kernel.Audit.RuntimeControls.usesAssumed implemented_by
Ix.Kernel.Audit.RuntimeControls.assumedTarget -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith #[``usesAssumed] #[`Init] notInstalled

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
run_cmd Ix.Kernel.Audit.checkRuntimeWith #[``usesLoop] #[`Init] { partialModules := #[`IxCK.Kernel.Audit.Runtime] }

/-- error: project-level execution replacements reached from [Ix.Kernel.Audit.RuntimeControls.usesLoop]:
[Ix.Kernel.Audit.RuntimeControls.projectLoop] -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith #[``usesLoop] #[`Init] { partialModules := #[`IxCK.Kernel.Audit.Imports] }

/-! `@[computed_field]` overrides are `unsafe`, and implement the constructors, which the
walk meets at their overrides; the ruling names the type. -/

inductive Tree where
  | leaf (n : Nat)
  | node (left right : Tree)
with
  @[computed_field] size : Tree → Nat
  | .leaf _ => 1
  | .node left right => left.size + right.size + 1

def treeSize (n : Nat) : Nat := (Tree.node (.leaf n) (.leaf 0)).size

/-- error: project-level execution replacements reached from [Ix.Kernel.Audit.RuntimeControls.treeSize]:
[Ix.Kernel.Audit.RuntimeControls.Tree.leaf,
 Ix.Kernel.Audit.RuntimeControls.Tree.node,
 Ix.Kernel.Audit.RuntimeControls.Tree.size,
 Ix.Kernel.Audit.RuntimeControls.Tree.leaf._override,
 Ix.Kernel.Audit.RuntimeControls.Tree.node._override,
 Ix.Kernel.Audit.RuntimeControls.Tree.size._override] -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntime #[``treeSize] #[`Init]

/-- info: runtime closure of [Ix.Kernel.Audit.RuntimeControls.treeSize]: 5 compiled functions;
inherited externs 1, implemented_by 0, unsafe 3, csimp 0; ruled computed_field 3 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith #[``treeSize] #[`Init] { computedFieldTypes := #[``Tree] }

/-- error: project-level execution replacements reached from [Ix.Kernel.Audit.RuntimeControls.treeSize]:
[Ix.Kernel.Audit.RuntimeControls.Tree.leaf,
 Ix.Kernel.Audit.RuntimeControls.Tree.node,
 Ix.Kernel.Audit.RuntimeControls.Tree.size,
 Ix.Kernel.Audit.RuntimeControls.Tree.leaf._override,
 Ix.Kernel.Audit.RuntimeControls.Tree.node._override,
 Ix.Kernel.Audit.RuntimeControls.Tree.size._override] -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith #[``treeSize] #[`Init] { computedFieldTypes := #[``Nat] }

/-! An unused parameter makes the code generator move a function's body into
an arity-reduced `f._redArg` that callers reach directly. The walk visits `f`
from it, so the overrides of an indexed type stay flagged. -/

inductive IndexedTree (k : Bool) where
  | leaf (n : Nat)
  | node (left right : IndexedTree k)
with
  @[computed_field] size : (k : Bool) → IndexedTree k → Nat
  | _, .leaf _ => 1
  | _, .node left right => left.size + right.size + 1

def indexedTreeSize (n : Nat) : Nat := (IndexedTree.node (k := true) (.leaf n) (.leaf 0)).size

/-- error: project-level execution replacements reached from [Ix.Kernel.Audit.RuntimeControls.indexedTreeSize]:
[Ix.Kernel.Audit.RuntimeControls.IndexedTree.leaf,
 Ix.Kernel.Audit.RuntimeControls.IndexedTree.node,
 Ix.Kernel.Audit.RuntimeControls.IndexedTree.size,
 Ix.Kernel.Audit.RuntimeControls.IndexedTree.leaf._override,
 Ix.Kernel.Audit.RuntimeControls.IndexedTree.node._override,
 Ix.Kernel.Audit.RuntimeControls.IndexedTree.size._override] -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntime #[``indexedTreeSize] #[`Init]

/-- info: runtime closure of [Ix.Kernel.Audit.RuntimeControls.indexedTreeSize]: 7 compiled functions;
inherited externs 1, implemented_by 0, unsafe 3, csimp 0; ruled computed_field 3 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith #[``indexedTreeSize] #[`Init] { computedFieldTypes := #[``IndexedTree] }

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
run_cmd Ix.Kernel.Audit.checkRuntimeWith #[``usesSlowId] #[`Init] { csimpModules := #[`IxCK.Kernel.Audit] }

/-- error: project-level execution replacements reached from [Ix.Kernel.Audit.RuntimeControls.usesSlowId]:
[Ix.Kernel.Audit.RuntimeControls.slowId] -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith #[``usesSlowId] #[`Init] { csimpModules := #[`IxCK.Kernel.Audit], csimpAxioms := #[] }

/-! A `csimp` replacement whose target is `@[inline]` disappears from
post-inlining IR, yet the caller's logical definition still references the
source; the audit catches and rules it the same way. -/

def slowInlineId (n : Nat) : Nat := n
@[inline] def fastInlineId (n : Nat) : Nat := n + 0
@[csimp] theorem slowInlineId_eq : @slowInlineId = @fastInlineId := by funext n; rfl
def usesSlowInlineId (n : Nat) : Nat := slowInlineId n

/-- error: project-level execution replacements reached from [Ix.Kernel.Audit.RuntimeControls.usesSlowInlineId]:
[Ix.Kernel.Audit.RuntimeControls.slowInlineId] -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntime #[``usesSlowInlineId] #[`Init]

/-- info: runtime closure of [Ix.Kernel.Audit.RuntimeControls.usesSlowInlineId]: 1 compiled functions;
inherited externs 0, implemented_by 0, unsafe 0, csimp 0; ruled csimp 1 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith #[``usesSlowInlineId] #[`Init] { csimpModules := #[`IxCK.Kernel.Audit] }

/-- error: project-level execution replacements reached from [Ix.Kernel.Audit.RuntimeControls.usesSlowInlineId]:
[Ix.Kernel.Audit.RuntimeControls.slowInlineId] -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith #[``usesSlowInlineId] #[`Init] { csimpModules := #[`IxCK.Kernel.Audit], csimpAxioms := #[] }

/-! The elaboration-time ruling admits `meta` declarations of the named
modules only; a non-`meta` pair there stays flagged. -/

meta unsafe def metaUnsafe (n : Nat) : Nat := n

@[implemented_by metaUnsafe]
meta def metaEval (n : Nat) : Nat := n + 1

/-- info: runtime closure of [Ix.Kernel.Audit.RuntimeControls.metaEval]: 1 compiled functions;
inherited externs 0, implemented_by 1, unsafe 1, csimp 0; ruled elaboration 2 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith #[``metaEval] #[`Init] { elaborationModules := #[`IxCK.Kernel.Audit.Runtime] }

/-- error: project-level execution replacements reached from [Ix.Kernel.Audit.RuntimeControls.usesImplementedBy]:
[Ix.Kernel.Audit.RuntimeControls.projectUnsafe, Ix.Kernel.Audit.RuntimeControls.usesImplementedBy] -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith #[``usesImplementedBy] #[`Init] { elaborationModules := #[`IxCK.Kernel.Audit.Runtime] }

/-! A substitution is found where its implementation is reached, AND even when
the code generator inlines both the implementation and intermediate wrappers
into the caller, via the logical-body walk. -/

def wrongTarget (n : Nat) : Nat := n + 1

@[implemented_by wrongTarget]
def specIdentity (n : Nat) : Nat := n

def callsSpecIdentity (n : Nat) : Nat := specIdentity n * 2

/-- error: project-level execution replacements reached from [Ix.Kernel.Audit.RuntimeControls.callsSpecIdentity]:
[Ix.Kernel.Audit.RuntimeControls.specIdentity] -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntime #[``callsSpecIdentity] #[`Init]

@[inline] def inlineWrongTarget (n : Nat) : Nat := n + 1

@[inline, implemented_by inlineWrongTarget]
def inlineSpecIdentity (n : Nat) : Nat := n

def callsInlineSpecIdentity (n : Nat) : Nat := inlineSpecIdentity n * 2

/-- error: project-level execution replacements reached from [Ix.Kernel.Audit.RuntimeControls.callsInlineSpecIdentity]:
[Ix.Kernel.Audit.RuntimeControls.inlineSpecIdentity] -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntime #[``callsInlineSpecIdentity] #[`Init]

@[inline] def inlineWrapper (n : Nat) : Nat := inlineSpecIdentity n + 3

def callsInlineWrapper (n : Nat) : Nat := inlineWrapper n * 2

/-- error: project-level execution replacements reached from [Ix.Kernel.Audit.RuntimeControls.callsInlineWrapper]:
[Ix.Kernel.Audit.RuntimeControls.inlineSpecIdentity] -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntime #[``callsInlineWrapper] #[`Init]

@[noinline] def hashTarget (n : Nat) : Nat := projectExtern n

@[implemented_by hashTarget]
def hashSpec (n : Nat) : Nat := n + 7

def externOnly (n : Nat) : Nat := projectExtern n
def externAndSubstitution (n : Nat) : Nat := projectExtern n + hashSpec n

/-- error: project-level execution replacements reached from [Ix.Kernel.Audit.RuntimeControls.externOnly]:
[Ix.Kernel.Audit.RuntimeControls.projectExtern] -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntime #[``externOnly] #[`Init]

/-- error: project-level execution replacements reached from [Ix.Kernel.Audit.RuntimeControls.externAndSubstitution]:
[Ix.Kernel.Audit.RuntimeControls.hashSpec, Ix.Kernel.Audit.RuntimeControls.projectExtern] -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntime #[``externAndSubstitution] #[`Init]

-- Stacked compiler suffixes (`_redArg`, `_boxed`, `_impl`, `_spec_<n>`) and
-- `._at_.<caller>.spec_<n>` specializations resolve back to the underlying
-- declaration in the environment.
run_cmd do
  let env ← Lean.getEnv
  let base := ``plainSquare
  for suffixed in #[
    base.str "_redArg",
    base.str "_boxed",
    base.str "_impl",
    base.str "_spec_0",
    (base.str "_redArg").str "_boxed",
    ((base.str "_impl").str "_redArg").str "_spec_12",
    (((base.str "_at_").str "Caller").str "spec_0"),
    (((((base.str "_at_").str "Caller").str "spec_0").str "_redArg").str "_boxed"),
    (((((base.str "_redArg").str "_at_").str "A").str "B").str "spec_1")
  ] do
    unless Ix.Kernel.Audit.reducedAritySource? env suffixed == some base do
      Lean.throwError m!"expected {suffixed} to resolve to {base}"

/-! ### Negative controls for H3, H4, H5 -/

/-! H3: A project `@[csimp]` chaining off an inherited `Init` `@[csimp]` target
(`List.length` → `List.lengthTR` → `altLengthTR`, inlined completely out of IR)
must be caught even though `List.length` and `List.lengthTR` live in `Init`. -/
section CSimpChainControl
@[inline] def altLengthTR {α : Type u} (as : List α) : Nat := as.lengthTRAux 0
theorem altLengthTR_eq : @List.lengthTR = @altLengthTR := rfl
attribute [local csimp] altLengthTR_eq
def callsListLength (xs : List Nat) : Nat := xs.length

/-- error: project-level execution replacements reached from [Ix.Kernel.Audit.RuntimeControls.callsListLength]:
[List.lengthTR] -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntime #[``callsListLength] #[`Init]
end CSimpChainControl

/-! H4: Both a polymorphic `partial def` specialized to `._at_.<caller>.spec_0`
in IR and an `@[inline] partial def` folded out of IR are detected. -/
partial def polyPartial [BEq α] (x y : α) : Bool :=
  if x == y then true else polyPartial x x

def callsPolyPartial (a b : Nat) : Bool := polyPartial a b

/-- error: project-level execution replacements reached from [Ix.Kernel.Audit.RuntimeControls.callsPolyPartial]:
[Ix.Kernel.Audit.RuntimeControls.polyPartial] -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntime #[``callsPolyPartial] #[`Init]

@[inline] partial def inlinePartial (n : Nat) : Nat :=
  if n > 10 then inlinePartial (n - 1) else n + 1

def callsInlinePartial (_ : Nat) : Nat := inlinePartial 5

/-- error: project-level execution replacements reached from [Ix.Kernel.Audit.RuntimeControls.callsInlinePartial]:
[Ix.Kernel.Audit.RuntimeControls.inlinePartial] -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntime #[``callsInlinePartial] #[`Init]

/-! H5: An unruled `@[inline, implemented_by ...]` hidden inside a ruled
`@[csimp]` target, a ruled `implementations` target, a ruled `partial` body
(`._unsafe_rec`), or a ruled `assumed` target is caught. -/
@[inline] def sneakyImpl (n : Nat) : Nat := n + 99
@[inline, implemented_by sneakyImpl] def sneakySpec (n : Nat) : Nat := n

partial def ruledPartialWithSneaky (n : Nat) : Nat :=
  if n > 10 then ruledPartialWithSneaky (n - 1) else sneakySpec n

def callsRuledPartialWithSneaky (n : Nat) : Nat := ruledPartialWithSneaky n

/-- error: project-level execution replacements reached from [Ix.Kernel.Audit.RuntimeControls.callsRuledPartialWithSneaky]:
[Ix.Kernel.Audit.RuntimeControls.sneakySpec] -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith #[``callsRuledPartialWithSneaky] #[`Init] { partialModules := #[`IxCK.Kernel.Audit.Runtime] }

def ruledCSimpSrc (n : Nat) : Nat := n
@[inline] def ruledCSimpTgt (n : Nat) : Nat := sneakySpec n
@[csimp] theorem ruledCSimp_eq : @ruledCSimpSrc = @ruledCSimpTgt := rfl
def callsRuledCSimp (n : Nat) : Nat := ruledCSimpSrc n

/-- error: project-level execution replacements reached from [Ix.Kernel.Audit.RuntimeControls.callsRuledCSimp]:
[Ix.Kernel.Audit.RuntimeControls.sneakySpec] -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith #[``callsRuledCSimp] #[`Init] { csimpModules := #[`IxCK.Kernel.Audit] }

unsafe def ruledImplTgt (n : Nat) : Nat := sneakySpec n
@[implemented_by ruledImplTgt] def ruledImplSrc (n : Nat) : Nat := n
def callsRuledImpl (n : Nat) : Nat := ruledImplSrc n

/-- error: project-level execution replacements reached from [Ix.Kernel.Audit.RuntimeControls.callsRuledImpl]:
[Ix.Kernel.Audit.RuntimeControls.sneakySpec] -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith #[``callsRuledImpl] #[`Init] { implementations := #[(``ruledImplSrc, ``ruledImplTgt)] }

def ruledAssumedTgt (n : Nat) : Nat := projectExtern (sneakySpec n)
@[implemented_by ruledAssumedTgt] def ruledAssumedSrc (n : Nat) : Nat := n
def callsRuledAssumed (n : Nat) : Nat := ruledAssumedSrc n

/-- error: assumed substitution Ix.Kernel.Audit.RuntimeControls.ruledAssumedSrc: Ix.Kernel.Audit.RuntimeControls.ruledAssumedTgt reaches unruled execution replacements:
[Ix.Kernel.Audit.RuntimeControls.sneakySpec] -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith #[``callsRuledAssumed] #[`Init] { assumed := #[{ source := ``ruledAssumedSrc, target := ``ruledAssumedTgt, externs := #[``projectExtern] }] }

end Ix.Kernel.Audit.RuntimeControls
