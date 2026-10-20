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
     b. **the Pass 3 hooks**. No call-site plan is registered (Rust's dump
        has no `plan`/`bplan`/`wplan` line, the Lean fold's
        `CompileEnv.callSitePlans` is empty). The components the first hook
        edits (`editChangedBlock`) are exactly the changed inductive
        components by the plan predicate (`isChanged`, not
        `componentChanged`): on both artifacts a member `m` of a component
        is displayed `m._ix.rec` (the side-car edit moved its auxiliaries)
        iff the component is changed, except that a regenerated
        `IndPredBelow` family (members compiled by an aux tail) is edited
        (A3V-IPB, `editPermutedBelowFamily`) iff it is only permuted. The
        Lean fold's tables agree: `p3Blocks` holds exactly the Lean blocks of
        the edited components, with their `all`, and every published head
        (`p3Heads`) is an `imageHead` entry of the set whose key is in
        `p3Blocks`. A Lean recursor stored as a definition (its image) is an
        `imageHead` entry; these are the same names on both artifacts, and on
        the Lean side exactly the recursor heads of `p3Heads`. On every
        inductive component the set's predicate is the plan predicate;
     c. every constant whose metadata carries an `_ix.inline` decompile
        record is a `caller` entry of the set (the same names on both
        artifacts), and no constant carries surgered call-site metadata;
     d. pinned fixtures with their causes (`pinned`);
     e. the definition components that collapse inside are exactly
        `pinnedDefinitions`, each `collapsed`.
  3. `changed-set-initstd` (landing): Init+Std, compiled by the statements'
     compiler (`Ix.Cert.compileReport`): no changed inductive component, the
     definition components of `initStdDefinitions` (none), and the fibers
     with two names in one Lean `all` (`initStdLeanMutualFibers`) out of the
     set. `changed-set-testenv` (manual): the whole test environment,
     compiled by Rust (`rs_compile_env_to_ixon`): 2b's edited components and
     image recursors and 2c's record carriers on Rust's artifact. (Before
     the flip it compared with Rust's plan registrations: 124 changed
     components in 90 Lean blocks, the `IX_LOG_AUX_NAMES` calibration of
     batch 4.)

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

/-- A component of a regenerated family: an aux tail compiled its members, so
the promotion route recorded their original form (`Named.original`). -/
def regeneratedFamily (ixe : Ixon.Env) (classes : Array (Array IxName)) : Bool :=
  classes.any (·.any fun m => ((ixe.named.get? m).bind (·.original)).isSome)

/-- The first Pass 3 hook edited the component: the side-car edit moved a
member's recursor to its display name, `m.rec ↦ m._ix.rec`
(`Ix.Compile.Pass.ixAuxName`; an unchanged component's tail keeps `m.rec`). -/
def edited (ixe : Ixon.Env) (all : Array IxName) (classes : Array (Array IxName)) : Bool :=
  (planClasses all classes).any (·.any fun m =>
    ixe.named.contains ((m.mkStr _root_.Ix.Compile.Pass.ixComponent).mkStr "rec"))

/-- Whether the first hook edits the component: a changed component (the plan
predicate), but of a regenerated `IndPredBelow` family only one that is
permuted and nothing else (A3V-IPB leaves a family that collapses or splits as
it is). -/
def editExpected (ixe : Ixon.Env) (all : Array IxName) (classes : Array (Array IxName))
    (layout? : Option Ixon.AuxLayout) : Bool :=
  isChanged all classes layout? &&
    (!regeneratedFamily ixe classes || blockCauses all classes layout? == #[.permuted])

/-- The expression metadata of a constant. -/
def arenaOf (cm : Ixon.ConstantMeta) : Option Ixon.ExprMetaArena :=
  match cm.info with
  | .defn _ _ _ _ a _ _ | .axio _ _ a _ | .quot _ _ a _ | .indc _ _ _ _ _ a _
  | .ctor _ _ _ a _ | .recr _ _ _ _ _ a _ _ => some a
  | _ => none

/-- Whether a constant's metadata records a surgered call site. -/
def hasCallSite (cm : Ixon.ConstantMeta) : Bool :=
  match arenaOf cm with
  | some a => a.nodes.any fun
    | .callSite .. | .etaCallSite .. => true
    | _ => false
  | none => false

/-- Whether a constant's metadata carries a Pass 3 decompile record: a KV map
with the key `_ix.inline` (`Ix.Compile.Pass.inlineKey`). -/
def hasRecord (cm : Ixon.ConstantMeta) : Bool :=
  match arenaOf cm with
  | some a => a.nodes.any fun
    | .mdata kvmaps _ => kvmaps.any (·.any fun (k, _) => k == _root_.Ix.Compile.Pass.inlineKey.getHash)
    | _ => false
  | none => false

/-- The names whose metadata carries a decompile record, by printed name. -/
def recordCarriers (ixe : Ixon.Env) : Array IxName :=
  (ixe.named.fold (init := #[]) fun acc n named =>
    if hasRecord named.constMeta then acc.push n else acc).qsort (·.pretty < ·.pretty)

/-- The input recursors an artifact stores as definitions (their images), by
printed name. -/
def imageRecursors (rawEnv : _root_.Ix.Environment) (ixe : Ixon.Env) : Array IxName :=
  (ixe.named.fold (init := #[]) fun acc n named =>
    match rawEnv.get? n, ixe.getConst? named.addr with
    | some (.recInfo _), some c => match c.info with
      | .defn _ | .dPrj _ => acc.push n
      | _ => acc
    | _, _ => acc).qsort (·.pretty < ·.pretty)

/-- The names of the set's entries with one cause. -/
def entriesWith (cs : ChangedSet) (cause : Cause) : Std.HashSet IxName :=
  cs.entries.foldl (init := {}) fun s e => if e.cause == cause then s.insert e.name else s

/-- A component, for messages: Lean's first member and the classes. -/
def showComponent (all : Array IxName) (classes : Array (Array IxName)) : String :=
  s!"{((all[0]?).map (·.pretty)).getD "?"} \
[{", ".intercalate (classes.toList.map fun c => "/".intercalate (c.toList.map (·.pretty)))}]"

/-- The components the first hook edited, against the expected ones, on one
artifact: the problems, the edited components (by index) and the first
members of their Lean blocks. -/
def editProblems (what : String) (ixe : Ixon.Env)
    (comps : Array (Array IxName × Array (Array IxName) × Option Ixon.AuxLayout × Bool)) :
    Array String × Array Nat × Std.HashSet IxName := Id.run do
  let mut ps : Array String := #[]
  let mut done : Array Nat := #[]
  let mut alls : Std.HashSet IxName := {}
  for ((all, classes, layout?, _), i) in comps.zipIdx do
    let got := edited ixe all classes
    if got then
      done := done.push i
      if let some a := all[0]? then alls := alls.insert a
    if got && !editExpected ixe all classes layout? then
      ps := ps.push s!"{what}: component {showComponent all classes} was edited by the first \
hook, but is not changed (or is a family that is not only permuted)"
    if !got && editExpected ixe all classes layout? then
      ps := ps.push s!"{what}: changed component {showComponent all classes} was not edited by \
the first hook"
  return (ps, done, alls)

/-- `xs ⊆ s`: one problem per name of `xs` outside `s`. -/
def subsetProblems (what : String) (xs : Array IxName) (s : Std.HashSet IxName) :
    Array String :=
  xs.filterMap fun n => if s.contains n then none else some s!"{n.pretty} {what}"

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
   -- a regenerated `IndPredBelow` family out of Lean's order (edited by A3V-IPB since the flip)
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
  -- b. the Pass 3 hooks: no plan; the edited components; the Lean fold's tables
  let planLines := (rustDump.splitOn "\n").filter fun l =>
    l.startsWith "plan " || l.startsWith "bplan " || l.startsWith "wplan "
  unless planLines.isEmpty do
    ps := ps.push s!"the Rust compile registered {planLines.length} call-site plan(s): \
{planLines.take 3}"
  unless cenv.callSitePlans.isEmpty do
    ps := ps.push s!"the Lean fold registered {cenv.callSitePlans.size} call-site plan(s)"
  let comps := components rawEnv leanEnv
  let regenerated (i : Nat) : Bool := match comps[i]? with
    | some (_, classes, _, _) => classes.any (·.any cenv.auxGenExtraNames.contains)
    | none => false
  for ((_, classes, _, _), i) in comps.zipIdx do
    if regeneratedFamily leanEnv classes != regenerated i then
      ps := ps.push s!"component #{i}: the artifact and the driver disagree on a regenerated family"
  let changed := comps.filter (·.2.2.2)
  let (leanEdit, leanDone, leanAlls) := editProblems "Lean" leanEnv comps
  let rustComps := components rawEnv rustEnv
  let (rustEdit, rustDone, rustAlls) := editProblems "Rust" rustEnv rustComps
  ps := ps ++ leanEdit ++ rustEdit
  if rustComps.size != comps.size || rustDone.size != leanDone.size then
    ps := ps.push s!"the Rust and the Lean artifacts differ in their components \
({rustComps.size}/{comps.size}) or edited components ({rustDone.size}/{leanDone.size})"
  -- the Lean fold's tables: the edited components' Lean blocks, with their `all`
  let mut blockAll : Std.HashMap IxName (Array IxName) := {}
  for i in leanDone do
    if let some (all, _, _, _) := comps[i]? then
      if let some a := all[0]? then blockAll := blockAll.insert a all
  for (k, all) in cenv.p3Blocks do
    let k : IxName := k
    match blockAll.get? k with
    | some want => if all != want then ps := ps.push s!"p3Blocks: {k.pretty} has another `all`"
    | none => ps := ps.push s!"p3Blocks: {k.pretty} is the Lean block of no edited component"
  for a in leanAlls do
    unless cenv.p3Blocks.contains a do
      ps := ps.push s!"p3Blocks: the Lean block {a.pretty} of an edited component is missing"
  -- the heads: entries of the set, keyed by a changed Lean block; the recursor
  -- heads are the input recursors stored as definitions (their images)
  let heads := entriesWith leanSet .imageHead
  let mut recHeads : Array IxName := #[]
  for (h, key) in cenv.p3Heads do
    let h : IxName := h
    unless heads.contains h do ps := ps.push s!"published head {h.pretty} is no imageHead entry"
    unless cenv.p3Blocks.contains key do
      ps := ps.push s!"published head {h.pretty}: its key {key.pretty} is not in p3Blocks"
    if let some (.recInfo _) := rawEnv.get? h then recHeads := recHeads.push h
  let recHeadsSorted := recHeads.qsort (·.pretty < ·.pretty)
  let leanImages := imageRecursors rawEnv leanEnv
  let rustImages := imageRecursors rawEnv rustEnv
  ps := ps ++ subsetProblems "is stored as an image (Lean), but is no imageHead entry" leanImages heads
  ps := ps ++ subsetProblems "is stored as an image (Rust), but is no imageHead entry" rustImages heads
  if leanImages.map (·.pretty) != recHeadsSorted.map (·.pretty) then
    ps := ps.push s!"the Lean recursors stored as images ({leanImages.size}) are not the published \
recursor heads ({recHeads.size})"
  if rustImages.map (·.pretty) != leanImages.map (·.pretty) then
    ps := ps.push s!"the Rust and the Lean artifacts store different recursors as images \
({rustImages.size}/{leanImages.size})"
  let familyEdited := leanDone.filter regenerated
  say s!"Pass 3 hooks: no call-site plan; {leanDone.size} of {comps.size} inductive components \
edited ({changed.size} changed by the plan predicate, {familyEdited.size} regenerated families \
edited) in {leanAlls.size} Lean blocks (Rust: {rustDone.size} in {rustAlls.size}); \
{cenv.p3Blocks.size} blocks and {cenv.p3Heads.size} heads published ({recHeads.size} recursors), \
{leanImages.size} recursors stored as images"
  for ((all, classes, _, ch), i) in comps.zipIdx do
    if regenerated i && ch then
      say s!"regenerated family out of Lean's order: {showComponent all classes} \
({if leanDone.contains i then "edited" else "not edited"})"
  -- the set's predicate adds nothing on inductive components: collapse inside
  -- an inductive component is a plan change already
  for (all, classes, layout?, ch) in comps do
    if componentChanged all classes layout? != ch then
      ps := ps.push s!"inductive component {showComponent all classes}: componentChanged differs \
from isChanged"
  -- c. decompile records only on callers; no surgered call site
  let callers := entriesWith leanSet .caller
  let leanCarriers := recordCarriers leanEnv
  let rustCarriers := recordCarriers rustEnv
  ps := ps ++ subsetProblems "carries an `_ix.inline` record (Lean), but is no caller entry"
    leanCarriers callers
  ps := ps ++ subsetProblems "carries an `_ix.inline` record (Rust), but is no caller entry"
    rustCarriers callers
  if rustCarriers.map (·.pretty) != leanCarriers.map (·.pretty) then
    ps := ps.push s!"the Rust and the Lean artifacts carry records on different constants \
({rustCarriers.size}/{leanCarriers.size})"
  for (what, ixe) in [("Lean", leanEnv), ("Rust", rustEnv)] do
    for (n, named) in ixe.named do
      if hasCallSite named.constMeta then
        ps := ps.push s!"{n.pretty} carries surgered call-site metadata ({what})"
  say s!"decompile records on {leanCarriers.size} constants (Rust {rustCarriers.size}), of \
{callers.size} caller entries"
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
artifact, and against it the components the first Pass 3 hook edited, the
recursors stored as images and the constants carrying decompile records (the
checks of `run`'s 2b and 2c that need no Lean compile). The constants of
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
  let mut ps : Array String := #[]
  let planLines := (rustDump.splitOn "\n").filter fun l =>
    l.startsWith "plan " || l.startsWith "bplan " || l.startsWith "wplan "
  unless planLines.isEmpty do
    ps := ps.push s!"the Rust compile registered {planLines.length} call-site plan(s): \
{planLines.take 3}"
  let comps := components rawEnv rustEnv
  let (edit, done, alls) := editProblems "Rust" rustEnv comps
  ps := ps ++ edit
  let changed := comps.filter (·.2.2.2)
  let images := imageRecursors rawEnv rustEnv
  let carriers := recordCarriers rustEnv
  ps := ps ++ subsetProblems "is stored as an image, but is no imageHead entry" images
    (entriesWith cs .imageHead)
  ps := ps ++ subsetProblems "carries an `_ix.inline` record, but is no caller entry" carriers
    (entriesWith cs .caller)
  say s!"{done.size} of {comps.size} inductive components edited by the first hook \
({changed.size} changed by the plan predicate) in {alls.size} Lean blocks; {images.size} \
recursors stored as images; decompile records on {carriers.size} constants"
  for (all, classes, layout?, ch) in comps do
    if componentChanged all classes layout? != ch then
      ps := ps.push s!"inductive component {showComponent all classes}: componentChanged differs \
from isChanged"
  for b in cs.blocks.filter (·.kind == .definitions) do
    say s!"  definitions {memberSet b.classes} {showCauses b.causes}"
  for p in ps.toList.take 40 do IO.eprintln s!"[changed-set] FAIL {p}"
  return if ps.isEmpty then 0 else 1

end Tests.Ix.Compile.ChangedSet
