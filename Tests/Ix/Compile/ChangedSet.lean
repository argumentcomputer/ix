/-
  changed-set: the changed set of a compile (`Ix.Compile.ChangedSet`, H1).

  1. **The predicates** on hand-made components: the plan predicate's causes,
     their combinations and the unchanged shapes (`blockCauses`, `isChanged`);
     the set's predicate (`componentCauses`, `componentChanged`): a definition
     component that collapses inside is changed for the set and for no plan,
     one only out of name order is not changed.
  2. **The corpus** (`validateAuxClosure`, the aux-heavy fixtures that
     `validate-aux` and `aux-gen-diff` compile), compiled by Rust
     (`rsCompilePhasesFFI`) and by the Lean fold (`compileEnvFold`):
     a. the set read off the two artifacts is the same;
     b. **the plan registrations**: the changed inductive components are
        exactly the components that own a call-site plan, Rust's
        (`rs_aux_gen_dump_plans`, plan keys by their printed name) and the
        Lean fold's (`CompileEnv.callSitePlans`, by name). A key `X.rec`
        belongs to `X`'s component; `all₀.rec_N` to the component of Lean's
        block that holds nested position `N - 1` (canonical there, or
        evaporated there). The components of regenerated families (members
        compiled by an aux tail) register no plan and are listed apart. On
        every inductive component the set's predicate is the plan predicate;
     c. every constant whose metadata records a surgered call site is in the
        set (the callers of the planned heads), except the callers of a
        regenerated `IndPredBelow` family, which are in its cone;
     d. pinned fixtures with their causes (`pinned`);
     e. the definition components that collapse inside are exactly
        `pinnedDefinitions`, each `collapsed`.
  3. `changed-set-initstd` (landing): Init+Std, compiled by the statements'
     compiler (`Ix.Cert.compileReport`): no changed inductive component, the
     definition components of `initStdDefinitions` (none), and the fibers
     with two names in one Lean `all` (`initStdLeanMutualFibers`) out of the
     set. `changed-set-testenv` (manual): the whole test environment,
     compiled by Rust (`rs_compile_env_to_ixon`), against Rust's plan
     registrations (the `IX_LOG_AUX_NAMES` calibration of batch 4: 124
     changed components in 90 Lean blocks).

  Run with: `lake test -- changed-set` (and `changed-set-initstd`,
  `changed-set-testenv`).
-/
import Ix.Compile.ChangedSet
import Ix.CompileM
import Ix.CompileDriver
import Tests.Ix.Compile.ValidateAux
import Tests.Ix.Compile.AuxGenDiff
import Tests.Ix.Kernel.SourceIngressStep
import Ix.Cert.Compile

namespace Tests.Ix.Compile.ChangedSet

open _root_.Ix.Compile.ChangedSet

abbrev IxName := _root_.Ix.Name

def say (s : String) : IO Unit := do
  IO.println s!"[changed-set] {s}"
  (← IO.getStdout).flush

/-! ## 1. The predicate -/

def nm (s : String) : IxName := _root_.Ix.Name.mkStr _root_.Ix.Name.mkAnon s

def layout (perm : List UInt64) (evaporated : List UInt64 := []) : Ixon.AuxLayout :=
  { perm := perm.toArray, evaporated := evaporated.toArray }

/-- `(case, all, classes, layout, expected causes)`. -/
def predicateCases : List (String × Array IxName × Array (Array IxName) ×
    Option Ixon.AuxLayout × Array BlockCause) :=
  let (a, b, c, d) := (nm "A", nm "B", nm "C", nm "D")
  [("Lean's order", #[a, b], #[#[a], #[b]], none, #[]),
   ("permuted", #[a, b], #[#[b], #[a]], none, #[.permuted]),
   ("split, first component", #[a, b, c], #[#[a], #[c]], none, #[.split]),
   ("split, second component", #[a, b, c], #[#[b]], none, #[.split]),
   ("collapsed", #[a, b], #[#[a, b]], none, #[.collapsed]),
   ("collapsed, representative not first", #[a, b, c], #[#[c], #[a, b]], none, #[.collapsed]),
   ("split and collapsed", #[a, b, c], #[#[a, b]], none, #[.split, .collapsed]),
   ("non-members dropped", #[a, b], #[#[d], #[a], #[b]], none, #[]),
   ("nested in place", #[a], #[#[a]], some (layout [0, 1]), #[]),
   ("nested moved", #[a], #[#[a]], some (layout [1, 0]), #[.nestedMoved 0 1, .nestedMoved 1 0]),
   ("nested out of the component", #[a], #[#[a]], some (layout [permOut, permOut] [0, 0]), #[]),
   ("nested moved past an outside position", #[a], #[#[a]], some (layout [permOut, 0]),
     #[.nestedMoved 1 0]),
   ("nested evaporated", #[a], #[#[a]], some (layout [permOut] [1]), #[.nestedEvaporated 0]),
   ("permuted and nested moved", #[a, b], #[#[b], #[a]], some (layout [1, 0]),
     #[.permuted, .nestedMoved 0 1, .nestedMoved 1 0]),
   ("no block", #[], #[#[a]], none, #[])]

/-- The set's predicate on components: `(case, all, classes, layout, expected
componentCauses, expected isChanged)`. A definition component comes with no
`all`, as the aux tail sees it. -/
def componentCases : List (String × Array IxName × Array (Array IxName) ×
    Option Ixon.AuxLayout × Array BlockCause × Bool) :=
  let (a, b, c) := (nm "A", nm "B", nm "C")
  [("definitions, one class", #[], #[#[a, b]], none, #[.collapsed], false),
   ("definitions, a class of two among others", #[], #[#[c], #[a, b]], none, #[.collapsed], false),
   ("definitions out of name order", #[], #[#[b], #[a]], none, #[], false),
   ("definitions, no collapse", #[], #[#[a], #[b], #[c]], none, #[], false),
   ("inductive, collapsed (no second cause)", #[a, b], #[#[a, b]], none, #[.collapsed], true),
   ("inductive, permuted", #[a, b], #[#[b], #[a]], none, #[.permuted], true),
   ("inductive, Lean's order", #[a, b], #[#[a], #[b]], none, #[], false)]

def predicateProblems : Array String := Id.run do
  let mut ps := #[]
  for (what, all, classes, layout?, expected) in predicateCases do
    let got := blockCauses all classes layout?
    if got != expected then
      ps := ps.push s!"predicate, {what}: causes {repr got}, expected {repr expected}"
    if isChanged all classes layout? != !expected.isEmpty then
      ps := ps.push s!"predicate, {what}: isChanged {isChanged all classes layout?}"
  for (what, all, classes, layout?, expected, plan) in componentCases do
    let got := componentCauses all classes layout?
    if got != expected then
      ps := ps.push s!"component, {what}: causes {repr got}, expected {repr expected}"
    if componentChanged all classes layout? != !expected.isEmpty then
      ps := ps.push s!"component, {what}: componentChanged {componentChanged all classes layout?}"
    if isChanged all classes layout? != plan then
      ps := ps.push s!"component, {what}: isChanged {isChanged all classes layout?}"
  return ps

/-! ## 2. The corpus -/

/-- Every component of an artifact's `Muts` records that reads as a component
of an input inductive block, with whether it is changed. -/
def components (env : _root_.Ix.Environment) (ixe : Ixon.Env) :
    Array (Array IxName × Array (Array IxName) × Option Ixon.AuxLayout × Bool) :=
  let lean := leanBlocks env
  (mutsRecords ixe).filterMap fun r => do
    let (all, classes, layout?) ← componentOf lean r
    pure (all, classes, layout?, isChanged all classes layout?)

/-- The plan keys a component owns: `X.rec` for its members of `all`, and
`all₀.rec_N` for the nested positions it holds (canonical or evaporated). -/
def ownedKeys (all : Array IxName) (classes : Array (Array IxName))
    (layout? : Option Ixon.AuxLayout) : Array IxName := Id.run do
  let mut keys := #[]
  for m in (planClasses all classes).flatten do
    keys := keys.push (m.mkStr "rec")
  if let (some all0, some l) := (all[0]?, layout?) then
    for (p, j) in l.perm.zipIdx do
      let evap := (l.evaporated[j]?).getD 0 != 0
      if p != permOut || evap then
        keys := keys.push (all0.mkStr s!"rec_{j + 1}")
  return keys

/-- A component of a regenerated family: an aux tail compiled its members, so
the promotion route recorded their original form (`Named.original`). -/
def regeneratedFamily (ixe : Ixon.Env) (classes : Array (Array IxName)) : Bool :=
  classes.any (·.any fun m => ((ixe.named.get? m).bind (·.original)).isSome)

/-- Whether a constant's metadata records a surgered call site. -/
def hasCallSite (cm : Ixon.ConstantMeta) : Bool :=
  let surgered (a : Ixon.ExprMetaArena) := a.nodes.any fun
    | .callSite .. | .etaCallSite .. => true
    | _ => false
  match cm.info with
  | .defn _ _ _ _ a _ _ | .axio _ _ a _ | .quot _ _ a _ | .indc _ _ _ _ _ a _
  | .ctor _ _ _ a _ | .recr _ _ _ _ _ a _ _ => surgered a
  | _ => false

/-- Fixtures of the corpus and their changed components' causes, by the
first member of Lean's block (recorded at push 47; components in `ofCompile`'s order). -/
def pinned : List (Lean.Name × Array (Array BlockCause)) :=
  let fx (s : Lean.Name) : Lean.Name := `Tests.Ix.Compile.Mutual ++ s
  [-- unchanged: a nested block and a higher-order one
   (fx `NestedSimple.Tree, #[]),
   (fx `HigherOrderRec.WTree, #[]),
   -- one cause each
   (fx `AlphaCollapse.A, #[#[.collapsed]]),
   (fx `OverMerge2.B3, #[#[.permuted]]),
   (`IxVMInd.Even, #[#[.permuted]]),
   (fx `OverMerge.A, #[#[.split], #[.split]]),
   -- combinations, nested moves and evaporations
   (fx `NestedAlphaCollapse.TreeA, #[#[.collapsed, .nestedMoved 1 0]]),
   (`Tests.Ix.Compile.Canonicity.CrossNamespaceNestedTwin1.A,
     #[#[.permuted, .nestedMoved 0 1, .nestedMoved 1 0]]),
   (fx `AuxOwnership.Evap.M, #[#[.split, .nestedEvaporated 0, .nestedEvaporated 1], #[.split]]),
   (`Test.Ix.Fixtures.Inductives.BLE, #[#[.split, .collapsed], #[.split]]),
   -- finding 23's block: three components, the owner's evaporating both positions
   (.mkNum `_private.Tests.Ix.Compile.Mutual 0 ++ fx `AuxDedup1.A,
     #[#[.split], #[.split], #[.split, .nestedEvaporated 0, .nestedEvaporated 1]]),
   -- a regenerated `IndPredBelow` family out of Lean's order (no plan)
   (fx `BelowPredicate.EvenP.below, #[#[.permuted]])]

/-- Up to twelve names, in parentheses; nothing for none. -/
def sample (xs : Array IxName) : String :=
  if xs.isEmpty then "" else s!" ({", ".intercalate (xs.toList.take 12 |>.map (·.pretty))})"

/-- The corpus's definition components that collapse inside (block-internal
fibers), by their members (recorded at push 47): the `_unsafe_rec`
implementations of the `partial`/well-founded fixture families, whose
α-equivalent members share a class inside their component, one of them stored
as a lone constant (`G`/`H`, no `Muts` record). -/
def pinnedDefinitions : List (Array Lean.Name) :=
  let unsafeRec (ns : Lean.Name) (ms : List String) : Array Lean.Name :=
    ms.toArray.map fun m => (ns.str m).str "_unsafe_rec"
  [unsafeRec `Test.Ix.Fixtures.Partial ["G", "H"],
   unsafeRec `Test.Ix.Fixtures.Partial ["A", "B", "C", "E", "F"],
   unsafeRec `Test.Ix.Fixtures.WellFounded ["A", "B", "C", "E", "F"],
   unsafeRec `Test.Ix.Fixtures.WellFounded ["A'", "B'", "C'", "E'", "F'"]]

/-- A component's members by printed name, sorted, as one string. -/
def memberSet (classes : Array (Array IxName)) : String :=
  ", ".intercalate ((classes.flatten.map (·.pretty)).qsort (· < ·)).toList

def showCauses (cs : Array BlockCause) : String :=
  "[" ++ ", ".intercalate (cs.toList.map fun c => match c with
    | .nestedMoved j i => s!"nested-moved {j}→{i}"
    | .nestedEvaporated j => s!"nested-evaporated {j}"
    | c => c.tag) ++ "]"

/-- The checks of one corpus compile. -/
def corpusProblems (rawEnv : _root_.Ix.Environment) (rustEnv leanEnv : Ixon.Env)
    (cenv : _root_.Ix.CompileM.CompileEnv) (rustDump : String) : IO (Array String) := do
  let mut ps : Array String := #[]
  let rustSet := ofCompile rawEnv rustEnv
  let leanSet := ofCompile rawEnv leanEnv
  say s!"Rust artifact: {rustSet.counts.summary}"
  say s!"Lean artifact: {leanSet.counts.summary}"
  -- a. one set
  let render (cs : ChangedSet) : Array String :=
    cs.entries.map fun e => s!"{e.name.pretty} {e.cause.tag} {(e.ref.map (·.pretty)).getD "-"}"
  if render rustSet != render leanSet then
    ps := ps.push "the sets read off the Rust and the Lean artifacts differ"
  if rustSet.blocks.size != leanSet.blocks.size then
    ps := ps.push "the changed components of the Rust and the Lean artifacts differ"
  -- b. the plan registrations
  let comps := components rawEnv leanEnv
  let mut owner : Std.HashMap IxName Nat := {}
  let mut ownerPretty : Std.HashMap String Nat := {}
  for ((all, classes, layout?, _), i) in comps.zipIdx do
    for k in ownedKeys all classes layout? do
      if let some j := owner.get? k then
        if j != i then ps := ps.push s!"plan key {k.pretty} has two owners"
      owner := owner.insert k i
      ownerPretty := ownerPretty.insert k.pretty i
  let regenerated (i : Nat) : Bool := match comps[i]? with
    | some (_, classes, _, _) => classes.any (·.any cenv.auxGenExtraNames.contains)
    | none => false
  for ((_, classes, _, _), i) in comps.zipIdx do
    if regeneratedFamily leanEnv classes != regenerated i then
      ps := ps.push s!"component #{i}: the artifact and the driver disagree on a regenerated family"
  let changed : Std.HashSet Nat := comps.zipIdx.foldl (init := {}) fun s ((_, _, _, ch), i) =>
    if ch && !regenerated i then s.insert i else s
  let familyChanged := comps.zipIdx.filter fun ((_, _, _, ch), i) => ch && regenerated i
  let mut leanOwners : Std.HashSet Nat := {}
  for (k, _) in cenv.callSitePlans do
    match owner.get? k with
    | some i => leanOwners := leanOwners.insert i
    | none => ps := ps.push s!"Lean plan {k.pretty}: no component owns it"
  let mut rustOwners : Std.HashSet Nat := {}
  let mut rustPlans := 0
  for line in rustDump.splitOn "\n" do
    if let some rest := line.dropPrefix? "plan " then
      rustPlans := rustPlans + 1
      let key := (rest.toString.splitOn " ").headD ""
      match ownerPretty.get? key with
      | some i => rustOwners := rustOwners.insert i
      | none => ps := ps.push s!"Rust plan {key}: no component owns it"
  let blocksOf (s : Std.HashSet Nat) : Std.HashSet IxName := s.fold (init := {}) fun acc i =>
    match comps[i]? with
    | some (all, _, _, _) => match all[0]? with
      | some a => acc.insert a
      | none => acc
    | none => acc
  let showComp (i : Nat) : String := match comps[i]? with
    | some (all, classes, _, _) =>
      s!"{((all[0]?).map (·.pretty)).getD "?"} \
[{", ".intercalate (classes.toList.map fun c => "/".intercalate (c.toList.map (·.pretty)))}]"
    | none => s!"#{i}"
  for (what, owners) in [("Rust", rustOwners), ("Lean", leanOwners)] do
    for i in changed do
      unless owners.contains i do
        ps := ps.push s!"changed component {showComp i} owns no {what} plan"
    for i in owners do
      unless changed.contains i do
        ps := ps.push s!"{what} plan from a component that is not changed: {showComp i}"
  say s!"plan registrations: {rustPlans} Rust plans from {rustOwners.size} components in \
{(blocksOf rustOwners).size} Lean blocks; {cenv.callSitePlans.size} Lean plans from \
{leanOwners.size} components; {changed.size} changed components in \
{(blocksOf changed).size} Lean blocks"
  for ((_, _, _, _), i) in familyChanged do
    say s!"regenerated family out of Lean's order (no plan): {showComp i}"
  -- the set's predicate adds nothing on inductive components: collapse inside
  -- an inductive component is a plan change already
  for ((all, classes, layout?, ch), i) in comps.zipIdx do
    if componentChanged all classes layout? != ch then
      ps := ps.push s!"inductive component {showComp i}: componentChanged differs from isChanged"
  -- c. surgered call sites: in the set, or (the callers of a regenerated
  -- family's inductives, which keep their names) in the cone of a member
  let mut surgered := 0
  let mut cone : Array IxName := #[]
  for (n, named) in leanEnv.named do
    if hasCallSite named.constMeta then
      surgered := surgered + 1
      unless leanSet.contains n do
        let near := match rawEnv.get? n with
          | some ci => (_root_.Ix.Compile.Canon.refsConst ci).toList.any leanSet.contains
          | none => false
        if near then cone := cone.push n
        else ps := ps.push s!"{n.pretty} has surgered call sites, and is neither in the set \
nor next to it"
  say s!"{surgered} constants with surgered call sites; outside the set, next to a member: \
{cone.size}{sample cone}"
  -- regenerated auxiliaries outside the changed blocks' members and heads
  let byName : Std.HashMap IxName (Array Cause) := leanSet.entries.foldl (init := {}) fun m e =>
    m.insert e.name ((m.getD e.name #[]).push e.cause)
  let lone := byName.fold (init := (#[] : Array IxName)) fun acc n cs =>
    if cs == #[.regenerated] then acc.push n else acc
  say s!"regenerated auxiliaries that are no member or image head of a changed block: \
{lone.size}{sample lone}"
  -- d. pinned fixtures
  for (first, expected) in pinned do
    let first := _root_.Ix.Name.fromLeanName first
    let got := (leanSet.blocks.filter fun b =>
      b.kind == .inductiveBlock && b.all[0]? == some first).map (·.causes)
    if got != expected then
      ps := ps.push s!"{first.pretty}: causes {got.toList.map showCauses}, \
expected {expected.toList.map showCauses}"
  -- e. the definition components that collapse inside, exactly
  let defs := leanSet.blocks.filter (·.kind == .definitions)
  let gotDefs := (defs.map fun b => memberSet b.classes).qsort (· < ·)
  let wantDefs := (pinnedDefinitions.toArray.map fun ns =>
    memberSet #[ns.map _root_.Ix.Name.fromLeanName]).qsort (· < ·)
  if gotDefs != wantDefs then
    ps := ps.push s!"definition components collapsing inside: {gotDefs}, expected {wantDefs}"
  unless defs.all (·.causes == #[.collapsed]) do
    ps := ps.push "a definition component with a cause other than `collapsed`"
  -- the changed components, for the record
  for b in leanSet.blocks do
    let kind := if b.kind == .definitions then "definitions " else ""
    say s!"  {kind}{(b.first.map (·.pretty)).getD "?"} \
[{", ".intercalate (b.classes.toList.map fun c => "/".intercalate (c.toList.map (·.pretty)))}] \
{showCauses b.causes}"
  return ps

def run (env : Lean.Environment) : IO UInt32 := do
  let mut ps := predicateProblems
  say s!"predicate: {predicateCases.length} plan cases, {componentCases.length} component cases"
  let filtered := validateAuxClosure env
  say s!"corpus: {filtered.length} constants"
  let raw ← _root_.Ix.CompileM.rsCompilePhasesFFI filtered
  let rawEnv := raw.rawEnv.toEnvironment
  let condensed := raw.condensed.toCondensedBlocks
  let rustEnv := raw.compileEnv.toEnv
  let (leanEnv, _, cenv) ← IO.ofExcept (_root_.Ix.CompileM.compileEnvFold rawEnv condensed)
  let rustDump ← Tests.Compile.AuxGenDiff.rsAuxGenDumpPlansFFI filtered
  ps := ps ++ (← corpusProblems rawEnv rustEnv leanEnv cenv rustDump)
  for p in ps do IO.eprintln s!"[changed-set] FAIL {p}"
  say (if ps.isEmpty then "ok" else s!"{ps.size} problems")
  return if ps.isEmpty then 0 else 1

/-! ## 3. Init+Std and the test environment -/

/-- Init+Std's definition components that collapse inside, by their members
(recorded at push 47: none). ALPHA-COLLAPSE §8.4's "2 block-internal fibers"
were counted over Lean's `all` (its units), not over components: they are the
two fibers of `initStdLeanMutualFibers`, whose members are each a component of
their own. -/
def initStdDefinitions : List (Array Lean.Name) := []

/-- A name of each Init+Std fiber with two names in one Lean `all` (recorded
at push 47): the `partial` `Std.Http.Protocol.H1.Machine` handlers, opaques of
one value, each its own component, so each fiber spans Source's groups and
stays out of the set. -/
def initStdLeanMutualFibers : List Lean.Name :=
  [`Std.Http.Protocol.H1.Machine.processRead,
   .mkNum `_private.Std.Http.Protocol.H1 0 ++ `Std.Http.Protocol.H1.Machine.processFixedBody]

/-- The fibers (input names published at one address) with two names in one
Lean `all` (`DefinitionVal.all`, `InductiveVal.all`, …): ALPHA-COLLAPSE's
units. When those names lie in different components the fiber spans Source's
groups (Source groups definitions by component), so it is no block-internal
fiber, and quotient Source collapses it. -/
def leanMutualFibers (env : _root_.Ix.Environment) (ixe : Ixon.Env) : Array (Array IxName) :=
  let byAddr : Std.HashMap Address (Array IxName) := ixe.named.fold (init := {}) fun m n named =>
    if (env.get? n).isSome then m.insert named.addr ((m.getD named.addr #[]).push n) else m
  let allOf (n : IxName) : Array IxName := match env.get? n with
    | some (.defnInfo v) => v.all | some (.thmInfo v) => v.all | some (.opaqueInfo v) => v.all
    | some (.inductInfo v) => v.all | some (.recInfo v) => v.all | _ => #[]
  let fibers := byAddr.fold (init := #[]) fun acc _ ns =>
    if ns.size ≥ 2 && ns.any (fun a => ns.any fun b => !(a == b) && (allOf a).contains b) then
      acc.push (ns.qsort fun a b => a.pretty < b.pretty)
    else acc
  fibers.qsort fun a b => ((a[0]?).map (·.pretty)).getD "" < ((b[0]?).map (·.pretty)).getD ""

/-- Init+Std, canonicalized as `cert-compile-parity-init` does it and compiled
by the statements' compiler (`Ix.Cert.compileReport`): no changed inductive
component, no entry but the members of `initStdDefinitions`' components. -/
def runInitStd : IO UInt32 := do
  let leanEnv ← getCompileEnv #[`Init, `Std]
  let consts := leanEnv.constants.toList.toArray
  let t0 ← IO.monoMsNow
  let env ← IO.lazyPure fun _ => Tests.Ix.Kernel.SourceIngressStep.canon consts 32
  let (ixe, failures) ← IO.ofExcept (← IO.lazyPure fun _ => _root_.Ix.Cert.compileReport env)
  let t1 ← IO.monoMsNow
  let cs ← IO.lazyPure fun _ => ofCompile env ixe
  let t2 ← IO.monoMsNow
  say s!"Init+Std ({consts.size} constants, {failures.toMap.size} failures; compile {t1 - t0} ms, \
set {t2 - t1} ms): {cs.counts.summary}"
  let mut ps : Array String := #[]
  let defs := cs.blocks.filter (·.kind == .definitions)
  for b in defs do
    say s!"  definitions {memberSet b.classes} {showCauses b.causes}"
  let gotDefs := (defs.map fun b => memberSet b.classes).qsort (· < ·)
  let wantDefs := (initStdDefinitions.toArray.map fun ns =>
    memberSet #[ns.map _root_.Ix.Name.fromLeanName]).qsort (· < ·)
  if gotDefs != wantDefs then
    ps := ps.push s!"definition components collapsing inside: {gotDefs}, expected {wantDefs}"
  for b in cs.blocks.filter (·.kind == .inductiveBlock) do
    ps := ps.push s!"changed inductive component {(b.first.map (·.pretty)).getD "?"}"
  for e in cs.entries do
    unless e.cause == .member do ps := ps.push s!"{e.name.pretty}: {e.cause.tag}"
  let fibers := leanMutualFibers env ixe
  say s!"fibers with two names in one Lean `all`: {fibers.size}, of them in the set: \
{(fibers.filter (·.any cs.contains)).size}"
  for f in fibers do say s!"  {", ".intercalate (f.toList.map (·.pretty))}"
  let pinnedFibers := initStdLeanMutualFibers.map _root_.Ix.Name.fromLeanName
  unless fibers.size == pinnedFibers.length &&
      pinnedFibers.all (fun n => fibers.any (·.contains n)) do
    ps := ps.push s!"fibers with two names in one Lean `all`: {fibers.size}, expected \
{pinnedFibers.length} ({", ".intercalate (pinnedFibers.map (·.pretty))})"
  if fibers.any (·.any cs.contains) then
    ps := ps.push "a fiber with two names in one Lean `all` is in the set"
  for p in ps.toList.take 20 do IO.eprintln s!"[changed-set] FAIL Init+Std: {p}"
  return if ps.isEmpty then 0 else 1

/-- The whole test environment, compiled by Rust: the set read off Rust's
artifact against Rust's plan registrations. The constants of
`Tests.Ix.SourceContract.*` are left out, as `rust-compile` leaves them out
(their source binder annotations are refused for the whole input). -/
def runTestEnv (env : Lean.Environment) : IO UInt32 := do
  let moduleNames := env.allImportedModuleNames
  let inSourceContract (n : Lean.Name) : Bool :=
    match (env.getModuleIdxFor? n).bind (moduleNames[·]?) with
    | some m => `Tests.Ix.SourceContract |>.isPrefixOf m
    | none => false
  let consts := env.constants.toList.filter fun (n, _) => !inSourceContract n
  say s!"test environment: {consts.length} constants"
  -- `rs_compile_env_to_ixon` (the ground filter first, as `rust-compile`'s
  -- compile does); the input canonicalized on the Lean side
  let rustEnv := (← _root_.Ix.CompileM.rsCompileEnvFFI consts).toEnv
  let rawEnv ← IO.lazyPure fun _ => Tests.Ix.Kernel.SourceIngressStep.canon consts.toArray 32
  let rustDump ← Tests.Compile.AuxGenDiff.rsAuxGenDumpPlansFFI consts
  let cs := ofCompile rawEnv rustEnv
  say s!"Rust artifact: {cs.counts.summary}"
  let comps := components rawEnv rustEnv
  let mut ownerPretty : Std.HashMap String Nat := {}
  for ((all, classes, layout?, _), i) in comps.zipIdx do
    for k in ownedKeys all classes layout? do
      ownerPretty := ownerPretty.insert k.pretty i
  let mut ps : Array String := #[]
  let mut owners : Std.HashSet Nat := {}
  for line in rustDump.splitOn "\n" do
    if let some rest := line.dropPrefix? "plan " then
      let key := (rest.toString.splitOn " ").headD ""
      match ownerPretty.get? key with
      | some i => owners := owners.insert i
      | none => ps := ps.push s!"Rust plan {key}: no component owns it"
  let changed : Std.HashSet Nat := comps.zipIdx.foldl (init := {}) fun s ((_, classes, _, ch), i) =>
    if ch && !regeneratedFamily rustEnv classes then s.insert i else s
  let first (i : Nat) : String := match comps[i]? with
    | some (all, classes, _, _) =>
      let rep := ((classes[0]?).bind (·[0]?)).map (·.pretty)
      s!"{((all[0]?).map (·.pretty)).getD "?"} ({rep.getD "?"})"
    | none => s!"#{i}"
  let alls (s : Std.HashSet Nat) : Nat := (s.fold (init := ({} : Std.HashSet IxName)) fun acc i =>
    match comps[i]? with
    | some (all, _, _, _) => match all[0]? with
      | some a => acc.insert a
      | none => acc
    | none => acc).size
  say s!"Rust plans from {owners.size} components in {alls owners} Lean blocks; \
{changed.size} changed components in {alls changed} Lean blocks"
  for i in changed do
    unless owners.contains i do ps := ps.push s!"changed component {first i} owns no Rust plan"
  for i in owners do
    unless changed.contains i do ps := ps.push s!"Rust plan from component {first i}, not changed"
  for ((all, classes, layout?, ch), i) in comps.zipIdx do
    if componentChanged all classes layout? != ch then
      ps := ps.push s!"inductive component {first i}: componentChanged differs from isChanged"
  for b in cs.blocks.filter (·.kind == .definitions) do
    say s!"  definitions {memberSet b.classes} {showCauses b.causes}"
  for p in ps.toList.take 40 do IO.eprintln s!"[changed-set] FAIL {p}"
  return if ps.isEmpty then 0 else 1

end Tests.Ix.Compile.ChangedSet
