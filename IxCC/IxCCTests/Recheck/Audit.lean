import IxCC.Recheck.Run
import IxCC.CompileClaim
import IxCC.Exe.Cert
import IxCC.Anf.Semantics
import Lean
import Lean.Elab.ComputedFields
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.CSimpAttr
import Lean.Compiler.MetaAttr
import Lean.Compiler.IR.CompilerM
import Lean.Compiler.IR.EmitUtil

/-! # Recheck Kernel-Style & Transitive Runtime Closure Audit (`BE-5` / `KF-4`)

Two complementary build-time audits over the certified verification stack:

1. **Kernel-evaluable style audit (`violations`)** over `Recheck.run` and `RcReplay.run`, covering
   **all** project and dependency namespaces (`IxCC.*`, `IxCK.*`, `Blake3.*`,
   NOT just `IxCC.*`): no constant on the path may use well-founded recursion,
   hash maps, `implemented_by`/`extern`, library `Array` loops, or `ByteArray`
   copies (with only the documented diagnostic/pure-hasher exceptions).
2. **Compiled-IR runtime closure audit (`checkRuntimeWith`)** mirroring
   `Ix.Kernel.Audit.checkRuntimeWith` (and additionally scanning logical bodies
   for inlined `implemented_by` substitutions, closing `BE-5`), run over:
   - `IxCC.Recheck.run` (zero `Lean.*` runtime dependencies, strictly `Init`/`Std`)
   - `IxCC.CompileClaim.verifyBytes` (KF-4 + SP-0 + N5 + pure BLAKE3 + Recheck)
   - `IxCC.Exe.Cert.verifyExeBytes` (full hardened `.ix.cert` v1 + deterministic
     re-assembly + `CompileClaim` + KF-4 + N5 + pure BLAKE3)

   Every `@[extern]`, `implemented_by`, `unsafe`, `@[csimp]`, or `partial`
   (`opaque` with compiled code) reached outside Lean's inherited runtime fails
   the build unless explicitly named in `RuntimeRulings` (with every ruled
   `csimp` theorem audited to depend ONLY on `[propext, Classical.choice,
   Quot.sound]`), and any `Blake3.Rust.*` / `rs_blake3_*` FFI is unconditionally
   rejected.

Note: we implement `checkRuntimeWith` directly here rather than importing
`IxCK.Kernel.Audit.Runtime`, because `IxCCTests.Recheck.Audit` is imported by
the `tests-recheck` executable whereas `IxCK.Kernel.Audit.Runtime` declares an
unlinked `@[extern "ix_kernel_audit_control"]` control symbol. -/

namespace IxCCTests.Recheck.Audit

open Lean Elab Command

/-! ## Part 1: Kernel-evaluable style audit (`IxCC.*`, `IxCK.*`, `Blake3.*`) -/

/-- The constants a definition's value mentions. -/
def valueConsts (env : Environment) (n : Name) : Array Name :=
  match env.find? n with
  | some (.defnInfo d) => d.value.getUsedConstants
  | some (.opaqueInfo d) => d.value.getUsedConstants
  | _ => #[]

/-- Every constant a value reaches from `root`. -/
def reach (env : Environment) (root : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo := [root]
  let mut fuel := 1000000
  while fuel > 0 do
    fuel := fuel - 1
    match todo with
    | [] => break
    | n :: rest =>
      todo := rest
      if seen.contains n then continue
      seen := seen.insert n
      for c in valueConsts env n do
        unless seen.contains c do todo := c :: todo
  return seen

def wellFounded : List Name := [``WellFounded.fix, ``WellFounded.fixF, ``Acc.rec]

def arrayLoops : List Name :=
  [``Array.all, ``Array.any, ``Array.contains, ``Array.map, ``Array.mapM, ``Array.foldl, ``Array.foldlM,
   ``Array.forIn', ``Array.anyM, ``Array.allM]

def byteCopies : List Name :=
  [``ByteArray.append, ``ByteArray.instAppend, ``ByteArray.extract, ``ByteArray.copySlice, ``ByteArray.push,
   ``ByteArray.set!]

def hashed (c : Name) : Bool :=
  [`Std.HashMap, `Std.DHashMap, `Std.HashSet].any (·.isPrefixOf c)

/-- Project & dependency namespaces audited for kernel-evaluable style.
(`Name.mkSimple` avoids a lexical `Blake3` name token that `TrustLedger.namesUnder`
would treat as a code entrypoint under `Blake3`.) -/
def auditedNamespaces : List Name := [`IxCC, `IxCK, `Ix, `Ixon, Name.mkSimple "Blake3"]

def isAuditedName (n : Name) : Bool :=
  auditedNamespaces.any (·.isPrefixOf n)

/-- Constants that break a rule on failure or diagnostic paths only. -/
def allowed : List Name :=
  [ -- A diagnostic address rendering (`Array.foldl`).
    ``IxCC.Ixon.Address.toHex ]

/-- The violations on the path from `root`, as `(constant, rule)`, across
`IxCC.*`, `IxCK.*`/`Ix.*`/`Ixon.*`, and `Blake3.*`. -/
def violations (env : Environment) (root : Name) : Array (Name × String) := Id.run do
  let mut out := #[]
  for n in (reach env root).toList do
    unless isAuditedName n do continue
    if allowed.contains n then continue
    let cs := valueConsts env n
    if cs.any wellFounded.contains then out := out.push (n, "well-founded recursion")
    if cs.any hashed then out := out.push (n, "hash map")
    if (Compiler.getImplementedBy? env n).isSome || isExtern env n then
      out := out.push (n, "implemented_by/extern")
    if cs.any arrayLoops.contains then out := out.push (n, "Array loop")
    if cs.any byteCopies.contains then out := out.push (n, "ByteArray copy")
  return out.qsort fun a b => a.1.toString < b.1.toString

run_cmd do
  let env ← getEnv
  let found := violations env ``IxCC.Recheck.run
  unless found.isEmpty do
    throwError "Recheck.run's path is not in kernel-evaluable style: {found.toList}"

/-! The plain-RC replay too: `RcReplay.run`'s path (its own lowering, the Lir graph and
well-formedness checks, critical-edge splitting) is in kernel-evaluable style. -/

run_cmd do
  let env ← getEnv
  let found := violations env ``IxCC.Recheck.RcReplay.run
  unless found.isEmpty do
    throwError "RcReplay.run's path is not in kernel-evaluable style: {found.toList}"

/-! Sanity: the style audit sees what it looks for off the path. -/

run_cmd do
  let env ← getEnv
  unless (violations env ``IxCC.Lir.Func.idoms).any (·.2 == "Array loop") do
    throwError "the audit missed Lir.Func.idoms' Array.map"
  unless (violations env ``IxCC.Anf.eval).any (·.2 == "well-founded recursion") do
    throwError "the audit missed Anf.eval's well-founded recursion"
  unless (violations env ``IxCC.X86.ELF.write).any (·.2 == "ByteArray copy") do
    throwError "the audit missed ELF.write's ByteArray appends"

/-! ## Part 2: Compiled-IR Runtime Closure Audit (`checkRuntimeWith`) -/

structure RuntimeReport where
  visited : Array Name := #[]
  externs : Array Name := #[]
  implementedBy : Array (Name × Name) := #[]
  unsafes : Array Name := #[]
  csimp : Array (Name × Name) := #[]
  uncompiled : Array Name := #[]
  csimpTargets : Array (Name × Name × Name) := #[]
  opaqueCode : Array Name := #[]
  implementationsReached : Array (Name × Name) := #[]

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

def csimpByTarget (env : Environment) : NameMap (Array Compiler.CSimp.Entry) :=
  (allCSimpEntries env).foldl (init := {}) fun acc entry =>
    acc.insert entry.toDeclName ((acc.find? entry.toDeclName).getD #[] |>.push entry)

def csimpBySource (env : Environment) : NameMap (Array Compiler.CSimp.Entry) :=
  (allCSimpEntries env).foldl (init := {}) fun acc entry =>
    acc.insert entry.fromDeclName ((acc.find? entry.fromDeclName).getD #[] |>.push entry)

def implementedByTargets (env : Environment) : NameMap (Array Name) := Id.run do
  let ext := Compiler.implementedByAttr.ext
  let add (acc : NameMap (Array Name)) (source target : Name) : NameMap (Array Name) :=
    acc.insert target ((acc.find? target).getD #[] |>.push source)
  let mut acc : NameMap (Array Name) := {}
  for idx in [0:env.header.moduleNames.size] do
    for (source, target) in ext.getModuleEntries env (idx : ModuleIdx) do
      acc := add acc source target
  return (ext.getState env).2.foldl (fun acc source target => add acc source target) acc

def isSpecSuffix (s : String) : Bool :=
  let rest? := if s.startsWith "_spec_" then some (s.drop 6)
    else if s.startsWith "spec_" then some (s.drop 5)
    else none
  match rest? with
  | some rest => !rest.isEmpty && rest.all Char.isDigit
  | none => false

def isCompilerSuffix (s : String) : Bool :=
  s == "_redArg" || s == "_boxed" || s == "_impl" || isSpecSuffix s

def stripAtPrefix? : Name → Option Name
  | .str p "_at_" =>
    match stripAtPrefix? p with
    | some root => some root
    | none => some p
  | .str p _ => stripAtPrefix? p
  | .num p _ => stripAtPrefix? p
  | .anonymous => none

def stripSuffixesSource? (env : Environment) : Name → Option Name
  | .str source s =>
    if isCompilerSuffix s then
      match stripSuffixesSource? env source with
      | some root => some root
      | none => if env.contains source then some source else none
    else none
  | _ => none

def reducedAritySource? (env : Environment) (name : Name) : Option Name :=
  match stripAtPrefix? name with
  | some base =>
    match stripSuffixesSource? env base with
    | some root => some root
    | none => if env.contains base then some base else none
  | none => stripSuffixesSource? env name

/-- Walk compiled IR reachable from `roots`, and transitively walk project-level
logical definition bodies (`scanLogical`, ported from `IxCK/Kernel/Audit/Runtime.lean`)
so `@[inline]` or auto-inlined `@[csimp]`, `@[implemented_by]`, `partial`, `unsafe`,
and `@[extern]` declarations cannot vanish across multi-hop inlining (closing `BE-5`). -/
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

def moduleOf (env : Environment) (name : Name) : Option Name :=
  match env.getModuleIdxFor? name with
  | some idx => env.header.moduleNames[idx.toNat]?
  | none => if env.contains name then some env.mainModule else none

def standardAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

def collectAxioms (env : Environment) (root : Name) : Array Name := Id.run do
  let mut seen : NameSet := {}
  let mut todo := #[root]
  let mut axioms : Array Name := #[]
  while !todo.isEmpty do
    let name := todo.back!
    todo := todo.pop
    if seen.contains name then continue
    seen := seen.insert name
    match env.find? name with
    | some (.axiomInfo _) => axioms := axioms.push name
    | some info =>
      for c in info.type.getUsedConstants do
        unless seen.contains c do todo := todo.push c
      if let some val := info.value? then
        for c in val.getUsedConstants do
          unless seen.contains c do todo := todo.push c
    | none => pure ()
  return axioms

structure RuntimeRulings where
  computedFieldTypes : Array Name := #[]
  csimpModules : Array Name := #[]
  csimpAxioms : Array Name := standardAxioms
  primitives : Array Name := #[]
  implementations : Array (Name × Name) := #[]
  elaborationModules : Array Name := #[]
  partialModules : Array Name := #[]

inductive Finding where
  | extern (name : Name)
  | implementedBy (name target : Name)
  | «unsafe» (name : Name)
  | csimp (source target thm : Name)
  | opaqueCode (name : Name)

def Finding.name : Finding → Name
  | .extern name | .implementedBy name _ | .unsafe name | .opaqueCode name => name
  | .csimp source _ _ => source

def Finding.anchor : Finding → Name
  | .csimp _ _ thm => thm
  | finding => finding.name

def underAny (prefixes : Array Name) (module : Name) : Bool :=
  prefixes.any (·.isPrefixOf module)

def computedFieldOverride (env : Environment) (types : Array Name) (name : Name) : Bool :=
  match name with
  | .str source "_override" =>
    let owner := match env.find? source with
      | some (.ctorInfo info) => some info.induct
      | _ => if Lean.Elab.ComputedFields.computedFieldAttr.hasTag env source ||
          source.getString! == "casesOn" then some source.getPrefix else none
    owner.any types.contains && Compiler.getImplementedBy? env source == some name
  | _ => false

def partialIn (env : Environment) (modules : Array Name) (name : Name) : Bool :=
  let definition := match name with
    | .str source "_unsafe_rec" => source
    | _ => name
  let isPartial := match env.find? definition with
    | some (.opaqueInfo _) => env.contains (definition.str "_unsafe_rec")
    | _ => false
  isPartial && (moduleOf env definition).any (underAny modules)

def RuntimeRulings.admits (env : Environment) (rulings : RuntimeRulings) (finding : Finding) :
    Option String :=
  let name := finding.name
  if rulings.primitives.contains name then some "primitive"
  else match finding with
  | .extern _ => none
  | .csimp _ _ thm =>
    if (moduleOf env thm).any (underAny rulings.csimpModules) &&
        (collectAxioms env thm).all rulings.csimpAxioms.contains then
      some "csimp"
    else none
  | .opaqueCode _ => if partialIn env rulings.partialModules name then some "partial" else none
  | .implementedBy _ target =>
    if computedFieldOverride env rulings.computedFieldTypes target then some "computed_field"
    else if rulings.implementations.contains (name, target) then some "implemented_by"
    else if isMarkedMeta env name && (moduleOf env name).any rulings.elaborationModules.contains then
      some "elaboration"
    else none
  | .unsafe _ =>
    if computedFieldOverride env rulings.computedFieldTypes name then some "computed_field"
    else if rulings.implementations.any fun (source, target) =>
        target == name && Compiler.getImplementedBy? env source == some name then
      some "implemented_by"
    else if isMarkedMeta env name && (moduleOf env name).any rulings.elaborationModules.contains then
      some "elaboration"
    else if partialIn env rulings.partialModules name then some "partial"
    else none

/-- Fail if any replaced or unchecked constant reached from `roots` lives outside
`prefixes` (covering `IxCC.*`, `IxCK.*`, `Blake3.*`, etc.) and no ruling admits it,
or if any Rust BLAKE3 symbol is reached, or if any root has no compiled code. -/
def checkRuntimeWith (roots : Array Name) (prefixes : Array Name) (rulings : RuntimeRulings) :
    CommandElabM Unit := do
  let env ← getEnv
  for root in roots do
    unless env.contains root do throwError m!"required root is missing: {root}"
    unless (IR.findEnvDecl env root).isSome || (Compiler.getImplementedBy? env root).isSome do
      throwError m!"root has no compiled code: {root}"
  let inherited (name : Name) : Bool := (moduleOf env name).any (underAny prefixes)
  let report := runtimeClosure env roots inherited
  -- Unconditionally reject any native/Rust BLAKE3 FFI in the closure.
  let blake3RustNs : Name := Name.str (Name.mkSimple "Blake3") "Rust"
  for n in report.visited ++ report.externs ++ report.unsafes ++
      report.implementedBy.map (·.2) ++ report.implementationsReached.map (·.2) do
    if blake3RustNs.isPrefixOf n then
      throwError m!"Rust BLAKE3 FFI symbol reached from {roots}: {n}"
  let csimpSources := csimpBySource env
  let findings := report.externs.map Finding.extern ++
    report.implementedBy.map (fun (name, target) => Finding.implementedBy name target) ++
    report.unsafes.map Finding.unsafe ++
    (report.csimp.flatMap fun (source, target) =>
      ((csimpSources.find? source).getD #[]).filterMap fun entry =>
        if entry.toDeclName == target then some (Finding.csimp source target entry.thmName) else none) ++
    report.csimpTargets.map (fun (source, target, thm) => Finding.csimp source target thm) ++
    report.opaqueCode.map Finding.opaqueCode
  let mut flagged : Array Name := #[]
  for finding in findings do
    if inherited finding.anchor then continue
    if (rulings.admits env finding).isNone then
      unless flagged.contains finding.name do flagged := flagged.push finding.name
  for (source, target) in report.implementationsReached do
    if inherited source then continue
    if (rulings.admits env (.implementedBy source target)).isNone then
      unless flagged.contains source do flagged := flagged.push source
  unless flagged.isEmpty do
    throwError m!"project-level execution replacements reached from {roots}:\n{flagged.qsort Name.lt}"

/-- Exact `IxCC` recheck rulings: the 4 modules carrying the 6 proved `@[csimp]`
tail-recursion/fast-path replacements (each verified to depend ONLY on
`[propext, Classical.choice, Quot.sound]`), plus `IxCC.Key`'s compiler-generated
`deriving Repr` helper (diagnostic formatting only). Zero `extern`, zero `unsafe`,
zero `implemented_by`, zero non-`Key` `partial`. -/
def recheckRulings : RuntimeRulings where
  csimpModules := #[`IxCC.Anf.Shrink, `IxCC.X86.EncodeK, `IxCC.Xv.Alloc.Apply, `IxCC.Xv.Validate.State]
  partialModules := #[`IxCC.Key]

/-- Exact `IxCK` + `IxCC` rulings (matching `IxCK/Kernel/Audit/Roots.lean` +
`recheckRulings`, zero `Blake3` overrides, zero assumed FFI, zero Rust BLAKE3). -/
def kernelRulings : RuntimeRulings where
  computedFieldTypes := #[`Ix.Kernel.Level, `Ix.Kernel.Expr, `Ix.Kernel.Name, `Ix.Kernel.Key]
  csimpModules := #[`IxCK.Kernel, `IxCK.Ixon.Codec,
    `IxCC.Anf.Shrink, `IxCC.X86.EncodeK, `IxCC.Xv.Alloc.Apply, `IxCC.Xv.Validate.State]
  primitives := #[``withPtrEq, ``withPtrEqUnsafe, ``withPtrEqDecEq, ``withPtrAddr,
    ``withPtrAddrUnsafe, ``ptrEq, ``ptrAddrUnsafe, ``isExclusiveUnsafe]
  implementations := #[(`Ix.Kernel.withExclusive, `Ix.Kernel.withExclusiveUnsafe)]
  elaborationModules := #[`IxCK.Kernel.BasisGen]
  partialModules := #[`IxCC.Key]

/- Pure-Lean `Recheck.run` and `Recheck.RcReplay.run` closures: strictly `Init`
and `Std`, only the 6 proved `@[csimp]`s and `IxCC.Key`'s `deriving Repr` (no
`unsafe`, `extern`, or `implemented_by` anywhere in `IxCC.*`, `IxCK.*`, or
`Blake3.*`). -/
run_cmd checkRuntimeWith #[``IxCC.Recheck.run] #[`Init, `Std] recheckRulings

run_cmd checkRuntimeWith #[``IxCC.Recheck.RcReplay.run] #[`Init, `Std] recheckRulings

/- Full `CompileClaim.verifyBytes` & `Exe.Cert.verifyExeBytes` transitive
closures across `IxCC.*`, `IxCK.*`, and `Blake3.*`: only the audited `IxCK` +
`IxCC` rulings above are permitted (strictly pure `Blake3.Pure`, zero `Blake3`
`extern`/`implemented_by`/`unsafe`, zero `Blake3.Rust.*`). `Lean.Data.Json`
and `Lean.Data.Parsec` enter only for parsing the untrusted equations JSON. -/
run_cmd do
  checkRuntimeWith
    #[``IxCC.CompileClaim.verifyBytes, ``IxCC.Exe.Cert.verifyExeBytes]
    #[`Init, `Std, `Lean]
    kernelRulings

/-! ### Negative sanity controls for `checkRuntimeWith` -/

namespace Controls

def plainSquare (n : Nat) : Nat := n * n

#guard_msgs in
run_cmd checkRuntimeWith #[``plainSquare] #[`Init, `Std] {}

partial def controlPartial (n : Nat) : Nat :=
  if n > 100 then n else controlPartial (2 * n + 1)

def usesControlPartial (n : Nat) : Nat := controlPartial n + 1

/-- error: project-level execution replacements reached from [IxCCTests.Recheck.Audit.Controls.usesControlPartial]:
[IxCCTests.Recheck.Audit.Controls.controlPartial] -/
#guard_msgs (whitespace := lax) in
run_cmd checkRuntimeWith #[``usesControlPartial] #[`Init, `Std] {}

unsafe def controlUnsafeImpl (n : Nat) : Nat := n

@[implemented_by controlUnsafeImpl]
def controlImplementedBy (n : Nat) : Nat := n

/-- error: project-level execution replacements reached from [IxCCTests.Recheck.Audit.Controls.controlImplementedBy]:
[IxCCTests.Recheck.Audit.Controls.controlImplementedBy, IxCCTests.Recheck.Audit.Controls.controlUnsafeImpl] -/
#guard_msgs (whitespace := lax) in
run_cmd checkRuntimeWith #[``controlImplementedBy] #[`Init, `Std] {}

@[inline] def controlInlinedImpl (n : Nat) : Nat := n + 1

@[inline, implemented_by controlInlinedImpl]
def controlInlinedSrc (n : Nat) : Nat := n

def usesControlInlined (n : Nat) : Nat := controlInlinedSrc n * 2

/-- error: project-level execution replacements reached from [IxCCTests.Recheck.Audit.Controls.usesControlInlined]:
[IxCCTests.Recheck.Audit.Controls.controlInlinedSrc] -/
#guard_msgs (whitespace := lax) in
run_cmd checkRuntimeWith #[``usesControlInlined] #[`Init, `Std] {}

/-- 2-hop inlined wrapper over `controlInlinedSrc`: both the wrapper and the
`implemented_by` target inline away in IR, so only transitive `scanLogical`
catches it. -/
@[inline] def controlInlinedMid (n : Nat) : Nat := controlInlinedSrc n + 3

def usesControlInlined2Hop (n : Nat) : Nat := controlInlinedMid n * 2

/-- error: project-level execution replacements reached from [IxCCTests.Recheck.Audit.Controls.usesControlInlined2Hop]:
[IxCCTests.Recheck.Audit.Controls.controlInlinedSrc] -/
#guard_msgs (whitespace := lax) in
run_cmd checkRuntimeWith #[``usesControlInlined2Hop] #[`Init, `Std] {}

/-- Polymorphic `partial def` specialized to `._at_.<caller>.spec_0` in IR. -/
partial def controlPolyPartial [BEq α] (x y : α) : Bool :=
  if x == y then true else controlPolyPartial x x

def usesControlPolyPartial (a b : Nat) : Bool := controlPolyPartial a b

/-- error: project-level execution replacements reached from [IxCCTests.Recheck.Audit.Controls.usesControlPolyPartial]:
[IxCCTests.Recheck.Audit.Controls.controlPolyPartial] -/
#guard_msgs (whitespace := lax) in
run_cmd checkRuntimeWith #[``usesControlPolyPartial] #[`Init, `Std] {}

-- Verify `reducedAritySource?` strips stacked compiler suffixes and `_at_` specializations.
run_cmd do
  let env ← getEnv
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
    unless reducedAritySource? env suffixed == some base do
      throwError m!"expected {suffixed} to resolve to {base}"

end Controls

end IxCCTests.Recheck.Audit
