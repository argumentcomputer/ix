import Ix.CompileCert.Indexed
import Ix.CompileCert.ProjectionLoweringLean
import Ix.Meta
import Benchmarks.Kernel.CheckIxeStep

/-! # The certifier: a Lean environment and an `.ixe`, one verdict per constant

`run` takes a Lean environment (a `.lean` file elaborated as `ix compile`
does, or a list of modules) and a compiled environment (`.ixe`), and reports
every Lean constant named in the `.ixe` as **certified**, **unsupported**
(with its class), **blocked** (by which dependency) or **rejected** (with the
diagnostic). It builds everything the certified check needs itself: the source
inventory, the name map, the admitted records, the reader-stream index and the
position hints. Nothing it builds is trusted.

**What a certified verdict means.** Every certified constant is a member of the
source of one `Input` for which `checkIndexed` returned an
`AcceptedAssociation`; by `checkIndexed_sound` that is the conclusion of
`faithful_sound` for that input: the exact record bytes are admitted by
`checkBytes`, the source is closed and uniquely named, and every source
declaration's independent export equals an entry of the certified reader's
output (definition hints quotiented; projection definitions through the raw
record), whole inductive blocks match, and touched definition blocks are
covered.

**What is executable-only (no proof).** The classification of the
constants that are *not* certified: which class, which blocking dependency,
which diagnostic. The triage that picks the candidate set (record selection by
the reader, the expression-size budget, the per-declaration pre-pass) only
decides what is *offered* to the certified check; a wrong triage can only make
a constant uncertified, never certified. The source capture trusts the host's
`Lean.Environment` (as `captureCone` does) and the Lean runtime that executes
the check (as every certified entry does).

**Projection lowering receipts (for S, not W).** For every constant with a raw
`.proj` on a structure-like the checker's direct route does not take, the
certifier builds the Lean lowering equation of a projection function, submits
it to Lean's kernel (`addDeclCore`, checking on) and decides the lane's receipt
(`checkSourceProjectionLowering`); the census is `<prefix>.receipts.tsv`, the
statements `<prefix>.receipts.statements`. A constant without an accepted
receipt stays blocked for the S endpoint's normalised route
(`SourceNormalizedInstallation.artifact_strong_model`) and fails the run. W's
verdicts do not depend on it. `--receipts-only` runs the census without W. -/

namespace Ix.CompileCert.Certifier

deriving instance Repr for Ix.Kernel.ConstRef
deriving instance Repr for Ix.CompileCert.DirectEntry
deriving instance Repr for Ix.CompileCert.DirectBlock

open Benchmarks.Kernel.CheckIxeStep
open Ix.CompileCert

/-! ## Verdicts -/

inductive Verdict where
  | certified
  | unsupported (cls : String)
  | blocked (dependency : Lean.Name) (cls : String)
  | rejected (diagnostic : String)
  deriving Inhabited

def Verdict.word : Verdict → String
  | .certified => "certified"
  | .unsupported _ => "unsupported"
  | .blocked .. => "blocked"
  | .rejected _ => "rejected"

def Verdict.cause : Verdict → String
  | .certified => ""
  | .unsupported c => c
  | .blocked d c => s!"{d}: {c}"
  | .rejected d => d

/-- The class for the summary tables: a blocked constant's class is its
dependency's class. -/
def Verdict.cls : Verdict → String
  | .certified => "certified"
  | .unsupported c => c
  | .blocked _ c => c
  | .rejected d => (d.splitOn ":").headD d

def Verdict.isCertified : Verdict → Bool
  | .certified => true
  | _ => false

/-! ## Expression size and references, sharing-aware (untrusted triage) -/

/-- Tree size of an expression, stopping at `cap`. The certified export and
the closure check walk expressions as trees; this bounds their work. -/
def treeSize (cap : Nat) : Lean.Expr → Nat → Nat
  | e, acc =>
    if acc ≥ cap then acc else
    match e with
    | .app f a => treeSize cap a (treeSize cap f (acc + 1))
    | .lam _ t b _ | .forallE _ t b _ => treeSize cap b (treeSize cap t (acc + 1))
    | .letE _ t v b _ => treeSize cap b (treeSize cap v (treeSize cap t (acc + 1)))
    | .mdata _ b | .proj _ _ b => treeSize cap b (acc + 1)
    | _ => acc + 1

def declTreeSize (cap : Nat) (ci : Lean.ConstantInfo) : Nat :=
  let acc := treeSize cap ci.type 0
  match ci with
  | .defnInfo v => treeSize cap v.value acc
  | .thmInfo v => treeSize cap v.value acc
  | .opaqueInfo v => treeSize cap v.value acc
  | .recInfo v => v.rules.foldl (fun acc r => treeSize cap r.rhs acc) acc
  | _ => acc

/-- A visited set of expressions under core's pointer-first equality
(`Lean.Expr.eqv`), not the structural `BEq` that `Ix.Common` derives, which
would compare a revisited shared subterm node by node. Untrusted triage only. -/
abbrev ExprSet := @Std.HashSet Lean.Expr ⟨Lean.Expr.eqv⟩ _

def ExprSet.empty : ExprSet := @Std.HashSet.emptyWithCapacity Lean.Expr ⟨Lean.Expr.eqv⟩ _ 1024

def ExprSet.has (s : ExprSet) (e : Lean.Expr) : Bool :=
  @Std.HashSet.contains Lean.Expr ⟨Lean.Expr.eqv⟩ _ s e

def ExprSet.add (s : ExprSet) (e : Lean.Expr) : ExprSet :=
  @Std.HashSet.insert Lean.Expr ⟨Lean.Expr.eqv⟩ _ s e

/-- `exprRefs` of several expressions as a set, visiting each distinct subterm
once (a worklist over a hash set of visited terms). -/
def collectRefs (roots : Array Lean.Expr) : Std.HashSet Lean.Name := Id.run do
  let mut seen : ExprSet := ExprSet.empty
  let mut out : Std.HashSet Lean.Name := {}
  let mut todo := roots
  while h : todo.size > 0 do
    let e := todo[todo.size - 1]
    todo := todo.pop
    if seen.has e then continue
    seen := seen.add e
    match e with
    | .const n _ => out := out.insert n
    | .app f a => todo := (todo.push f).push a
    | .lam _ t b _ | .forallE _ t b _ => todo := (todo.push t).push b
    | .letE _ t v b _ => todo := ((todo.push t).push v).push b
    | .mdata _ b => todo := todo.push b
    | .proj n _ b => out := out.insert n; todo := todo.push b
    | .lit (.natVal _) => out := out.insertMany [`Nat, `Nat.zero, `Nat.succ]
    | .lit (.strVal _) =>
      out := out.insertMany [`String, `String.ofList, `List, `List.nil, `List.cons, `Char, `Char.ofNat]
    | _ => pure ()
  return out

/-- `declarationRefs` as a set (same names, sharing-aware). -/
def refsOf (ci : Lean.ConstantInfo) : Array Lean.Name := Id.run do
  let exprs : Array Lean.Expr := #[ci.type] ++ match ci with
    | .defnInfo v => #[v.value]
    | .thmInfo v => #[v.value]
    | .opaqueInfo v => #[v.value]
    | .recInfo v => v.rules.toArray.map (·.rhs)
    | _ => #[]
  let refs := collectRefs exprs
  let extra : List Lean.Name := match ci with
    | .defnInfo v => v.all
    | .thmInfo v => v.all
    | .opaqueInfo v => v.all
    | .inductInfo v => v.all ++ v.ctors ++ v.all.map (·.str "rec") ++
        (List.range v.numNested).filterMap (fun i => v.all.head?.map (·.str s!"rec_{i + 1}"))
    | .ctorInfo v => [v.induct]
    | .recInfo v => v.all ++ v.all.map (·.str "rec") ++
        (List.range (v.numMotives - v.all.length)).filterMap
          (fun i => v.all.head?.map (·.str s!"rec_{i + 1}")) ++
        v.rules.map (·.ctor)
    | _ => []
  return (refs.insertMany extra).toArray

/-- Append to a reverse-edge list in place: take the array out of the map
first, so the push does not copy it (a popular name has hundreds of
thousands of users). -/
def pushUser (users : Std.HashMap Lean.Name (Array Lean.Name)) (r n : Lean.Name) :
    Std.HashMap Lean.Name (Array Lean.Name) :=
  let arr := users.getD r #[]
  let users := users.erase r
  users.insert r (arr.push n)

/-! ## Raw projections (measurement for the owner's decision, untrusted) -/

/-- The structure names of the raw projection nodes of some expressions,
each distinct subterm visited once. -/
def projOwners (roots : Array Lean.Expr) : Std.HashSet Lean.Name := Id.run do
  let mut seen : ExprSet := ExprSet.empty
  let mut out : Std.HashSet Lean.Name := {}
  let mut todo := roots
  while h : todo.size > 0 do
    let e := todo[todo.size - 1]
    todo := todo.pop
    if seen.has e then continue
    seen := seen.add e
    match e with
    | .app f a => todo := (todo.push f).push a
    | .lam _ t b _ | .forallE _ t b _ => todo := (todo.push t).push b
    | .letE _ t v b _ => todo := ((todo.push t).push v).push b
    | .mdata _ b => todo := todo.push b
    | .proj n _ b => out := out.insert n; todo := todo.push b
    | _ => pure ()
  return out

/-- The checker serves `.proj` natively only on a *direct* structure (one
type, not recursive, not nested: `structParts?`); a projection on any other
structure-like is what the owner's decision is about. -/
def structureClass (env : Lean.Environment) (owner : Lean.Name) : String :=
  match env.find? owner with
  | some (.inductInfo v) =>
    if v.all.length > 1 then "mutual" else if v.numNested > 0 then "nested"
    else if v.isRec then "recursive" else "direct"
  | _ => "unknown"

/-- A coarse kind for a constant with a raw projection. -/
def projKind (ci : Lean.ConstantInfo) : String :=
  let last := match ci.name with
    | .str _ s => s
    | _ => ""
  let value? : Option Lean.Expr := match ci with
    | .defnInfo v => some v.value
    | .thmInfo v => some v.value
    | .opaqueInfo v => some v.value
    | _ => none
  if (value?.bind sourceProjectionBody).isSome then "projection function"
  else if last.startsWith "match_" then "match compilation"
  else if last.startsWith "proof_" || last == "_proof" then "auxiliary proof"
  else if last.startsWith "eq_" || last == "eq_def" || last.endsWith "_eq" then "equation lemma"
  else if last == "noConfusion" || last == "noConfusionType" then "noConfusion"
  else if last.startsWith "inst" then "instance"
  else match ci with
    | .thmInfo _ => "theorem"
    | .defnInfo _ => "definition"
    | .recInfo _ => "recursor"
    | _ => "other"

/-- Per constant with a raw projection on a non-direct structure-like: its
kind, the classes of the structures, and whether it is certified by W. -/
def measureProjections (env : Lean.Environment) (names : Array Lean.Name)
    (refs : Std.HashMap Lean.Name (Array Lean.Name)) (verdicts : Std.HashMap Lean.Name Verdict) :
    String × Lean.Json := Id.run do
  let mut rows := "name\tkind\tstructures\tW verdict\n"
  let mut affected : Std.HashSet Lean.Name := {}
  let mut anyProj := 0
  let mut byKind : Std.HashMap String Nat := {}
  let mut byClass : Std.HashMap String Nat := {}
  let mut wByKind : Std.HashMap (String × String) Nat := {}
  let mut allByKind : Std.HashMap String Nat := {}
  let mut allByClass : Std.HashMap String Nat := {}
  for n in names do
    let some ci := env.find? n | continue
    let exprs : Array Lean.Expr := #[ci.type] ++ match ci with
      | .defnInfo v => #[v.value]
      | .thmInfo v => #[v.value]
      | .opaqueInfo v => #[v.value]
      | .recInfo v => v.rules.toArray.map (·.rhs)
      | _ => #[]
    let owners := projOwners exprs
    if owners.isEmpty then continue
    anyProj := anyProj + 1
    let classes := owners.toArray.map (structureClass env)
    let nonDirect := classes.filter (· != "direct")
    let kindAll := projKind ci
    allByKind := allByKind.insert kindAll (allByKind.getD kindAll 0 + 1)
    for c in classes.toList.eraseDups do allByClass := allByClass.insert c (allByClass.getD c 0 + 1)
    if nonDirect.isEmpty then continue
    affected := affected.insert n
    let kind := projKind ci
    byKind := byKind.insert kind (byKind.getD kind 0 + 1)
    for c in nonDirect.toList.eraseDups do byClass := byClass.insert c (byClass.getD c 0 + 1)
    let w := (verdicts.getD n (.unsupported "no verdict")).word
    wByKind := wByKind.insert (kind, w) (wByKind.getD (kind, w) 0 + 1)
    rows := rows ++ s!"{n}\t{kind}\t{",".intercalate (nonDirect.toList.eraseDups)}\t{w}\n"
  -- dependents: constants whose declarationRefs closure reaches an affected constant
  let mut users : Std.HashMap Lean.Name (Array Lean.Name) := {}
  for n in names do
    for r in refs.getD n #[] do users := pushUser users r n
  let mut reached : Std.HashSet Lean.Name := affected
  let mut todo := affected.toArray
  while h : todo.size > 0 do
    let n := todo[todo.size - 1]
    todo := todo.pop
    for u in users.getD n #[] do
      unless reached.contains u do
        reached := reached.insert u
        todo := todo.push u
  let toJ (m : Std.HashMap String Nat) : Lean.Json :=
    Lean.Json.mkObj (m.toList.map fun (k, v) => (k, Lean.toJson v))
  let json := Lean.Json.mkObj [
    ("withRawProjection", Lean.toJson anyProj),
    ("allByKind", toJ allByKind), ("allByStructureClass", toJ allByClass),
    ("onNonDirectStructure", Lean.toJson affected.size),
    ("dependentsOfThose", Lean.toJson (reached.size - affected.size)),
    ("byKind", toJ byKind), ("byStructureClass", toJ byClass),
    ("byKindAndWVerdict", Lean.Json.mkObj (wByKind.toList.map fun ((k, w), v) =>
      (s!"{k} / {w}", Lean.toJson v)))]
  return (rows, json)

/-! ## Projection lowering receipts (for the S endpoint's normalised route)

For every constant with a raw `.proj` on a non-direct structure-like: if it is
a projection function, build its Lean lowering equation, have Lean's kernel
check it (`addDeclCore`, checking on), and decide the lane's receipt
(`checkSourceProjectionLowering`, `Ix/CompileCert/SourceProjectionLowering.lean`)
on the four source entries it reads; otherwise it stays blocked for S. The
executable census is untrusted; what a receipt means is
`SourceProjectionLowering.faithful`. -/

/-- The constants whose closure under users reaches `seeds` (the seeds excluded). -/
def dependentsOf (names : Array Lean.Name) (refs : Std.HashMap Lean.Name (Array Lean.Name))
    (seeds : Array Lean.Name) : Nat := Id.run do
  let mut users : Std.HashMap Lean.Name (Array Lean.Name) := {}
  for n in names do
    for r in refs.getD n #[] do users := pushUser users r n
  let mut reached : Std.HashSet Lean.Name := seeds.foldl (·.insert ·) {}
  let mut todo := seeds
  while h : todo.size > 0 do
    let n := todo[todo.size - 1]
    todo := todo.pop
    for u in users.getD n #[] do
      unless reached.contains u do
        reached := reached.insert u
        todo := todo.push u
  return reached.size - seeds.size

def oneLine (s : String) : String := (s.replace "\n" " ").replace "\t" " "

/-- The receipt census; returns the number of refusals. Writes
`<out>.receipts.tsv` and `<out>.receipts.statements` (each lowering equation's
name, universe telescope and statement). -/
def projectionReceipts (env : Lean.Environment) (names : Array Lean.Name)
    (refs : Std.HashMap Lean.Name (Array Lean.Name)) (out : String) : IO (Nat × Lean.Json) := do
  let mut affected : Array Lean.Name := #[]
  for n in names do
    let some ci := env.find? n | continue
    let exprs : Array Lean.Expr := #[ci.type] ++ match ci with
      | .defnInfo v => #[v.value]
      | .thmInfo v => #[v.value]
      | .opaqueInfo v => #[v.value]
      | .recInfo v => v.rules.toArray.map (·.rhs)
      | _ => #[]
    if (projOwners exprs).toArray.any (structureClass env · != "direct") then
      affected := affected.push n
  let mut rows := "name\tkind\tclass\tlowering equation\telimination level\tLean kernel\treceipt\tcause\n"
  let mut statements := ""
  let mut accepted := 0
  let mut kernelRefused := 0
  let mut receiptRefused := 0
  let mut witnessFailed := 0
  let mut notFunction := 0
  let mut stillBlocked : Array Lean.Name := #[]
  let mut byClass : Std.HashMap String Nat := {}
  for n in affected do
    let some ci := env.find? n | continue
    let kind := projKind ci
    let cls := match (projectionSourceValue ci).bind sourceProjectionBody with
      | some (owner, _, _) => structureClass env owner
      | none => "-"
    if kind != "projection function" then
      notFunction := notFunction + 1
      stillBlocked := stillBlocked.push n
      rows := rows ++ s!"{n}\t{kind}\t{cls}\t-\t-\t-\t-\tnot a projection function: no lowering\n"
      continue
    byClass := byClass.insert cls (byClass.getD cls 0 + 1)
    match ← LoweringLean.lowerProjection env n with
    | .error why =>
      witnessFailed := witnessFailed + 1
      stillBlocked := stillBlocked.push n
      rows := rows ++ s!"{n}\t{kind}\t{cls}\t-\t-\t-\t-\t{oneLine why}\n"
    | .ok o =>
      statements := statements ++
        s!"{o.witness.name}\t{o.witness.levelParams}\t{oneLine (toString o.witness.type)}\n"
      let (kernel, receipt, cause) := match o.kernel, o.receipt with
        | .ok (), .ok () => ("accepted", "accepted", "")
        | .error why, .ok () => ("refused", "accepted", why)
        | .ok (), .error why => ("accepted", "refused", why)
        | .error k, .error r => ("refused", "refused", s!"{k}; {r}")
      if kernel == "accepted" && receipt == "accepted" then accepted := accepted + 1
      else
        stillBlocked := stillBlocked.push n
        if kernel != "accepted" then kernelRefused := kernelRefused + 1
        else receiptRefused := receiptRefused + 1
      rows := rows ++ s!"{n}\t{kind}\t{cls}\t{o.witness.name}\t{o.level}\t{kernel}\t{receipt}\t{oneLine cause}\n"
  IO.FS.writeFile s!"{out}.receipts.tsv" rows
  IO.FS.writeFile s!"{out}.receipts.statements" statements
  let functions := affected.size - notFunction
  let before := dependentsOf names refs affected
  let after := dependentsOf names refs stillBlocked
  let refused := kernelRefused + receiptRefused + witnessFailed
  IO.println s!"[certify] projection receipts: functions={functions} accepted={accepted} refused={refused} \
    (Lean kernel refused {kernelRefused}, receipt refused {receiptRefused}, no witness {witnessFailed}); \
    other constants with a raw projection on a non-direct structure-like: {notFunction}; \
    blocked for S by a raw projection: {stillBlocked.size} constants, {after} dependents \
    (without receipts: {affected.size} constants, {before} dependents)"
  (← IO.getStdout).flush
  let json := Lean.Json.mkObj [
    ("functions", Lean.toJson functions), ("accepted", Lean.toJson accepted),
    ("kernelRefused", Lean.toJson kernelRefused), ("receiptRefused", Lean.toJson receiptRefused),
    ("witnessFailed", Lean.toJson witnessFailed), ("otherConstants", Lean.toJson notFunction),
    ("byClass", Lean.Json.mkObj (byClass.toList.map fun (k, v) => (k, Lean.toJson v))),
    ("blockedForS", Lean.toJson stillBlocked.size), ("blockedDependents", Lean.toJson after),
    ("withoutReceipts", Lean.toJson affected.size), ("withoutReceiptsDependents", Lean.toJson before)]
  return (refused + notFunction, json)

/-! ## Records the reader accepts (untrusted triage) -/

/-- The records in check order, with the recursor and projection records of
kept blocks; a record the reader declines, and every record depending on one,
is left out with its cause (`CheckIxeFold.acceptedRecords`, with causes). -/
def selectRecords (s : Setup) :
    Array (Address × Ixon.Constant) × Std.HashMap Address (Bool × String) := Id.run do
  let mut st : Kernel.Reader.State := {}
  let mut failed : Std.HashMap Address (Bool × String) := {}
  let mut consumed : Std.HashSet Address := {}
  let mut out : Array (Address × Ixon.Constant) := #[]
  for address in s.ordered do
    if consumed.contains address then continue
    let some source := s.store[address]? | continue
    let recs := recursorRecords s.cx.index address
    for r in recs do consumed := consumed.insert r
    match Kernel.Reader.readRecord s.cx st address source with
    | .error e =>
      let reason := match e with
        | .malformed m => s!"reader: malformed: {m}"
        | .declined m => s!"reader: {m}"
      failed := failed.insert address (true, reason)
    | .ok rd =>
      st := st.commit rd
      let deps := dependencies s.store s.cx.index s.extra address source
      match deps.toList.find? failed.contains with
      | some dep => failed := failed.insert address (false, s!"record {dep}")
      | none =>
        out := out.push (address, source)
        for r in recs do
          if let some c := s.store[r]? then out := out.push (r, c)
  let kept : Std.HashSet Address := out.foldl (fun acc (a, _) => acc.insert a) {}
  let mut projs : Array (Address × Ixon.Constant) := #[]
  for (a, c) in s.store.toArray do
    let o := owner a c
    if o != a && kept.contains o && !kept.contains a then projs := projs.push (a, c)
  projs := projs.qsort (fun x y => x.1.cmpBytes y.1 == .lt)
  return (out ++ projs, failed)

/-! ## Inputs and hints -/

def entryName : DirectEntry → Kernel.Name
  | .axiom cv | .defn cv _ _ | .thm cv _ | .opaque cv _ | .quot _ cv | .induct cv _
  | .ctor cv _ _ | .recursor cv _ _ _ => cv.name

/-- Position hints for one input: positions by source name (source and map
share an order), stream positions by reader name, record positions. -/
def buildHints (input : Input) (sh : Shared) (queries : Lean.Name → Array Lean.Name)
    (workers : Nat) : Hints :=
  let pos : Std.HashMap Lean.Name Nat := Id.run do
    let mut m : Std.HashMap Lean.Name Nat := {}
    for (ci, i) in input.source.declarations.zipIdx do m := m.insert ci.name i
    return m
  let entryPos : Std.HashMap Kernel.Name Nat := Id.run do
    let mut m : Std.HashMap Kernel.Name Nat := {}
    for i in [0:sh.entries.size] do
      let n := match sh.entries[i]? with
        | some e => entryName e
        | none => .anonymous
      unless m.contains n do m := m.insert n i
    return m
  let recordPos : Std.HashMap Address Nat := Id.run do
    let mut m : Std.HashMap Address Nat := {}
    for i in [0:sh.constants.size] do
      let a := sh.constants[i]!.1
      unless m.contains a do m := m.insert a i
    return m
  let targets : Std.HashMap Lean.Name MapEntry :=
    input.map.foldl (fun m e => m.insert e.source e) {}
  let at_ (n : Lean.Name) : List Nat :=
    ((queries n).toList.filterMap (pos[·]?)).eraseDups
  { sourceAt := at_, mapAt := at_, workers
    entryAt := fun n => match targets[n]? with
      | some e => (entryPos[sh.reader.nameOf e.target]?).getD 0
      | none => 0
    recordAt := fun n => match targets[n]? with
      | some e => (recordPos[e.record]?).getD 0
      | none => 0 }

/-! ## Diagnostics for a declaration that fails its checks (untrusted) -/

def diagnose (sh : Shared) (hints : Hints) (ci : Lean.ConstantInfo) (entry : Option MapEntry) :
    Verdict :=
  let cy := sh.small hints ci.name
  match directExport cy ci with
  | .error e =>
    if (e.splitOn "missing source").length > 1 then
      .rejected s!"certifier: small context incomplete: {e}"
    else if (e.splitOn "unsupported").length > 1 then .unsupported s!"export: {e}"
    else .rejected s!"export: {e}"
  | .ok e =>
    let corr := directAt cy sh.entries (hints.entryAt ci.name) ci ||
      rawAt cy sh.constants (hints.recordAt ci.name) sh.reader ci
    if !corr then
      let at_ := sh.entries[hints.entryAt ci.name]?
      let detail := match at_ with
        | none => "no reader entry under the target's name"
        | some actual =>
          match actual, e.withoutHint with
          | .defn a v _, .defn b w _ =>
            if a.name != b.name then "name differs"
            else if a.levelParams != b.levelParams then "universe parameters differ"
            else if a.type != b.type then "type differs"
            else if v != w then "value differs" else "hint-quotiented entries differ"
          | .thm a v, .thm b w | .opaque a v, .opaque b w =>
            if a.type != b.type then "type differs"
            else if v != w then "value differs" else "entries differ"
          | _, _ => "kind or fields differ"
      .rejected s!"correspondence: {detail}"
    else if !decide (BlockMatch cy sh.state ci) then .rejected "inductive block differs"
    else if !(definitionGroupImage cy ci).isSome then .rejected "definition group member unmapped"
    else match entry with
      | none => .rejected "no map entry"
      | some e =>
        if !decide (Kernel.Reader.resolve sh.reader.store e.record = some e.target) then
          .rejected "map: record does not resolve to the proposed member"
        else if !decide (NameAgrees cy e.source (sh.reader.nameOf e.target)) then
          .rejected "map: reader name differs from the exported name"
        else .rejected "map: recursor flags differ"

/-! ## The run -/

inductive LeanSource where
  | file (path : System.FilePath)
  | modules (names : Array Lean.Name)

def loadLean : LeanSource → IO Lean.Environment
  | .file path => getFileEnv path
  | .modules names => getCompileEnv names

structure Config where
  lean : LeanSource
  ixe : String
  out : String
  /-- Tree-size budget per declaration (type, value and rules together). -/
  budget : Nat := 268435456
  /-- Tasks for the per-declaration checks. -/
  workers : Nat := 16
  /-- Names whose export and reader entries to print in full (diagnostics). -/
  explain : Array Lean.Name := #[]
  /-- Only the raw-projection measurement and the receipt census (no W check). -/
  receiptsOnly : Bool := false

/-- Propagate blocking: every candidate referring (`declarationRefs`) to a
name that is not a candidate is blocked by it, until nothing changes. -/
def closeCandidates (refs : Std.HashMap Lean.Name (Array Lean.Name))
    (verdicts : Std.HashMap Lean.Name Verdict) (candidates : Array Lean.Name) :
    Std.HashMap Lean.Name Verdict × Array Lean.Name := Id.run do
  let mut verdicts := verdicts
  let mut live : Std.HashSet Lean.Name := candidates.foldl (·.insert ·) {}
  -- reverse edges among candidates
  let mut users : Std.HashMap Lean.Name (Array Lean.Name) := {}
  for n in candidates do
    for r in refs.getD n #[] do
      users := pushUser users r n
  let mut todo : Array (Lean.Name × Lean.Name) := #[]
  for n in candidates do
    for r in refs.getD n #[] do
      unless live.contains r do todo := todo.push (n, r)
  while h : todo.size > 0 do
    let (n, r) := todo[todo.size - 1]
    todo := todo.pop
    unless live.contains n do continue
    live := live.erase n
    let cls := match verdicts[r]? with
      | some v => v.cls
      | none => "dependency outside the artifact or the environment"
    -- name the root cause: a blocked dependency passes on its own blocker
    let root := match verdicts[r]? with
      | some (.blocked x _) => x
      | _ => r
    verdicts := verdicts.insert n (.blocked root cls)
    for u in users.getD n #[] do
      if live.contains u then todo := todo.push (u, n)
  return (verdicts, candidates.filter live.contains)

def say (s : String) : IO Unit := do
  IO.println s
  (← IO.getStdout).flush

def jsonEscape (s : String) : String := (Lean.Json.str s).compress

/-- The Lean constants named in the artifact, sorted, with their addresses. -/
def namedConstants (env : Lean.Environment) (produced : Ixon.Env) :
    Array Lean.Name × Nat × Std.HashMap Lean.Name Address := Id.run do
  let mut names : Array Lean.Name := #[]
  let mut notInArtifact := 0
  let mut namedAddr : Std.HashMap Lean.Name Address := {}
  for (n, _) in env.constants.toList do
    if let some named := produced.named[Ix.Name.fromLeanName n]? then
      names := names.push n
      namedAddr := namedAddr.insert n named.addr
    else notInArtifact := notInArtifact + 1
  return (names.qsort (fun a b => toString a < toString b), notInArtifact, namedAddr)

/-- `--receipts-only`: the raw-projection measurement and the receipt census,
without the W check (no record store, no admission, no association). -/
def runReceiptsOnly (cfg : Config) : IO UInt32 := do
  let t0 ← IO.monoMsNow
  let bytes ← IO.FS.readBinFile cfg.ixe
  say s!"[certify] ixe {cfg.ixe}: {bytes.size} bytes, Blake3 {Address.blake3 bytes}; receipts only (no W check)"
  let produced ← IO.ofExcept (Ixon.deEnv bytes)
  let env ← loadLean cfg.lean
  let (names, notInArtifact, _) := namedConstants env produced
  say s!"[certify] Lean environment: {names.size} constants named in the artifact, {notInArtifact} not; \
    {(← IO.monoMsNow) - t0} ms"
  let mut refs : Std.HashMap Lean.Name (Array Lean.Name) := {}
  for n in names do
    if let some ci := env.find? n then refs := refs.insert n (refsOf ci)
  let (projRows, projJson) := measureProjections env names refs {}
  IO.FS.writeFile s!"{cfg.out}.proj.tsv" projRows
  say s!"[certify] raw projections: {projJson.compress}"
  let (refused, receiptJson) ← projectionReceipts env names refs cfg.out
  IO.FS.writeFile s!"{cfg.out}.json" (Lean.Json.mkObj [
    ("ixe", Lean.toJson cfg.ixe), ("names", Lean.toJson names.size),
    ("rawProjections", projJson), ("projectionReceipts", receiptJson)]).pretty
  say s!"[certify] receipts only: total {(← IO.monoMsNow) - t0} ms"
  if refused != 0 then
    IO.eprintln s!"[certify] FAIL: {refused} constants with a raw projection on a non-direct structure-like have no accepted receipt"
    return 1
  return 0

def run (cfg : Config) : IO UInt32 := do
  if cfg.receiptsOnly then return (← runReceiptsOnly cfg)
  let t0 ← IO.monoMsNow
  let bytes ← IO.FS.readBinFile cfg.ixe
  say s!"[certify] ixe {cfg.ixe}: {bytes.size} bytes, Blake3 {Address.blake3 bytes}"
  let produced ← IO.ofExcept (Ixon.deEnv bytes)
  let mut store : RecordStore := {}
  for (address, lazy) in produced.consts.toList do
    store := store.insert address (← IO.ofExcept lazy.get)
  let pins ← IO.ofExcept Kernel.Reader.defaultPins
  let pre ← IO.ofExcept Kernel.Reader.builtinPrelude
  let readerHints := Benchmarks.Kernel.CheckIxeStep.Hints.ofStore store produced.anonHints
  let s := setup store (produced.blobs[·]?) pins pre readerHints.lookup
  let (records, recordFailures) := selectRecords s
  let kept : Std.HashSet Address := records.foldl (fun acc (a, _) => acc.insert a) {}
  let t1 ← IO.monoMsNow
  say s!"[certify] {store.size} records; {records.size} selected, {recordFailures.size} \
    declined or blocked by the reader; {t1 - t0} ms"
  -- the Lean side
  let env ← loadLean cfg.lean
  let mut names : Array Lean.Name := #[]
  let mut notInArtifact := 0
  let mut namedAddr : Std.HashMap Lean.Name Address := {}
  for (n, _) in env.constants.toList do
    if let some named := produced.named[Ix.Name.fromLeanName n]? then
      names := names.push n
      namedAddr := namedAddr.insert n named.addr
    else notInArtifact := notInArtifact + 1
  names := names.qsort (fun a b => toString a < toString b)
  let t2 ← IO.monoMsNow
  say s!"[certify] Lean environment: {names.size} constants named in the artifact, \
    {notInArtifact} not; {t2 - t1} ms"
  -- triage: unsupported source, records not admitted, size budget
  let mut verdicts : Std.HashMap Lean.Name Verdict := {}
  let mut refs : Std.HashMap Lean.Name (Array Lean.Name) := {}
  let mut entries : Std.HashMap Lean.Name MapEntry := {}
  let mut candidates : Array Lean.Name := #[]
  let mut big1M := 0
  let mut big4M := 0
  let mut big16M := 0
  let mut sizeTotal := 0
  for n in names do
    let some ci := env.find? n | continue
    refs := refs.insert n (refsOf ci)
    let some addr := namedAddr[n]? | continue
    let some ownerRecord := store[addr]? | do
      verdicts := verdicts.insert n (.unsupported "target record missing from the artifact")
    let ownerAddr := owner addr ownerRecord
    if let some (own, reason) := recordFailures[ownerAddr]? then
      verdicts := verdicts.insert n (if own then .unsupported reason
        else .unsupported s!"target record blocked by the reader ({reason})")
      continue
    unless kept.contains addr do
      verdicts := verdicts.insert n (.unsupported "target record not selected")
      continue
    -- the size budget first: every later step (including `unsupportedSource`) walks trees
    let size := declTreeSize cfg.budget ci
    if size ≥ 1000000 then big1M := big1M + 1
    if size ≥ 4000000 then big4M := big4M + 1
    if size ≥ 16000000 then big16M := big16M + 1
    sizeTotal := sizeTotal + size
    if size ≥ cfg.budget then
      verdicts := verdicts.insert n (.unsupported s!"expression tree over budget ({cfg.budget} nodes)")
      continue
    if let some feature := unsupportedSource ci then
      verdicts := verdicts.insert n (.unsupported s!"source: {feature}")
      continue
    let some target := Kernel.Reader.resolve s.cx.store addr | do
      verdicts := verdicts.insert n (.unsupported "target does not resolve")
    entries := entries.insert n ⟨n, addr, target⟩
    candidates := candidates.push n
  let (v1, closed) := closeCandidates refs verdicts candidates
  candidates := closed
  verdicts := v1
  let t3 ← IO.monoMsNow
  say s!"[certify] triage: {candidates.size} candidates; {t3 - t2} ms; tree sizes (capped at the budget): \
    total {sizeTotal}, ≥1M {big1M}, ≥4M {big4M}, ≥16M {big16M}"
  -- admission of the selected records (once; the source does not enter it)
  let recordBytes := records.toList.map fun (a, c) => (a, Ixon.serConstant c)
  let blobs := produced.blobs.toList
  let limits : Kernel.Admission.Limits := ⟨recordBytes.length + 1, blobs.length + 1,
    recordBytes.foldl (fun n (_, b) => n + b.size) 0 + blobs.foldl (fun n (_, b) => n + b.size) 0 + 1,
    recordBytes.foldl (fun n (_, b) => max n b.size) 0 + 1, 1 <<< 24⟩
  let ai : ArtifactInput := { limits, records := recordBytes, blobs, hint := readerHints.lookup }
  -- on a dedicated thread: a fresh allocator heap, as the environment check runs its fold
  -- (`CheckIxeFold`); the main heap is fragmented by the Lean environment and the store
  let admitted := (Task.spawn (prio := .dedicated) fun _ => prepareArtifact ai).get
  let artifact ← match admitted with
    | .ok a => pure a
    | .error e =>
      let msg := match e with
        | .admission err => s!"admission: {err}"
        | .reading err => s!"reading: {err}"
        | .decoding err => s!"decoding: {repr err}"
        | .setup r => s!"setup: {r}"
        | .malformedInput r => s!"malformed input: {r}"
        | _ => "other"
      IO.eprintln s!"[certify] admission of the selected records failed: {msg}"
      return 1
  let t4 ← IO.monoMsNow
  say s!"[certify] admission (checkBytes) of {recordBytes.length} records: \
    {artifact.declarations.size} declarations; {t4 - t3} ms"
  let queriesOf (n : Lean.Name) : Array Lean.Name := Id.run do
    let some ci := env.find? n | return #[n]
    let mut out : Std.HashSet Lean.Name := ({} : Std.HashSet Lean.Name).insert n
    let block : Array Lean.Name := match ci with
      | .inductInfo v => Id.run do
        let mut ms : Array Lean.Name := #[n]
        for m in v.all do
          ms := ms.push m
          if let some (.inductInfo iv) := env.find? m then ms := ms ++ iv.ctors.toArray
          ms := ms.push (m.str "rec")
        for i in [0:v.numNested] do
          if let some h := v.all.head? then ms := ms.push (h.str s!"rec_{i + 1}")
        return ms
      | _ => #[n]
    for d in block do
      out := out.insert d
      for r in refs.getD d #[] do
        out := (out.insert r).insert r.getPrefix
    return out.toArray
  let makeInput (members : Array Lean.Name) : Input :=
    { toArtifactInput := ai
      source := ⟨members.toList.filterMap env.find?⟩
      roots := members.toList
      map := members.toList.filterMap (entries[·]?) }
  -- the certified check over all candidates; only if it refuses, the pre-pass runs every
  -- candidate's own checks, classifies the failures, and the check runs again without them
  let decline (e : Decline) : String := match e with
    | .sourceDomain => "source domain" | .mapMismatch => "map"
    | .correspondence => "correspondence" | .blockCorrespondence => "blocks"
    | .definitionGroupCorrespondence => "definition groups"
    | .setup r => s!"setup: {r}" | _ => "other"
  let mut finalNames := candidates
  let mut input := makeInput candidates
  let mut sh := Shared.ofArtifact input artifact
  let mut hints := buildHints input sh queriesOf cfg.workers
  let mut refusal : Option Decline := match checkIndexed input artifact hints with
    | .ok _ => none
    | .error e => some e
  let t5 ← IO.monoMsNow
  if let some e := refusal then
    say s!"[certify] certified check over {candidates.size} candidates refused ({decline e}); \
      {t5 - t4} ms; pre-pass"
    let mut failures := 0
    -- the same per-declaration checks, on `workers` tasks
    let shP := sh
    let hintsP := hints
    let decls := input.source.declarations
    let w := max cfg.workers 1
    let tasks := (List.range w).map fun i => Task.spawn fun _ =>
      (strideOf w i 0 decls).filterMap fun ci =>
        let entry := entries[ci.name]?
        if shP.declCheck hintsP ci && (entry.map (shP.entryCheck hintsP)).getD false then none
        else some (ci.name, diagnose shP hintsP ci entry)
    for t in tasks do
      for (n, v) in t.get do
        failures := failures + 1
        verdicts := verdicts.insert n v
    say s!"[certify] pre-pass: {failures} of {candidates.size} fail their own checks; \
      {(← IO.monoMsNow) - t5} ms"
    let survivors := candidates.filter (fun n => !verdicts.contains n)
    let (v2, closed2) := closeCandidates refs verdicts survivors
    verdicts := v2
    finalNames := closed2
    input := makeInput finalNames
    sh := Shared.ofArtifact input artifact
    hints := buildHints input sh queriesOf cfg.workers
    refusal := match checkIndexed input artifact hints with
      | .ok _ => none
      | .error e => some e
  match refusal with
  | some e =>
    IO.eprintln s!"[certify] the certified check refused the final input ({finalNames.size} \
      declarations): {decline e}"
    return 1
  | none =>
    -- `checkIndexed` returned an `AcceptedAssociation` for `input`; by `checkIndexed_sound`
    -- every member of `input.source` is certified.
    for n in finalNames do verdicts := verdicts.insert n .certified
  let t6 ← IO.monoMsNow
  say s!"[certify] certified check over {finalNames.size} declarations: accepted; {t6 - t4} ms \
    since admission"
  -- diagnostics: the export and the reader entries of the requested names, in the
  -- context of all candidates
  unless cfg.explain.isEmpty do
    let inputE := makeInput candidates
    let shE := Shared.ofArtifact inputE artifact
    let hintsE := buildHints inputE shE queriesOf cfg.workers
    for n in cfg.explain do
      let some ci := env.find? n | say s!"[explain] {n}: not in the environment"
      let cy := shE.small hintsE n
      say s!"[explain] {n}: verdict {(verdicts.getD n (.unsupported "none")).word}"
      match directExport cy ci with
      | .error e => say s!"[explain]   export error: {e}"
      | .ok e =>
        say s!"[explain]   export: {repr e.withoutHint}"
        for a in shE.entries do
          if entryName a == entryName e then say s!"[explain]   reader: {repr a}"
      if let .inductInfo iv := ci then
        match exportBlock cy iv, cy.name iv.name with
        | .ok b, .ok k =>
          say s!"[explain]   export block: {repr b}"
          match shE.state.indBlocks[k]? with
          | some actual => say s!"[explain]   reader block: {repr (readerBlock actual)}"
          | none => say "[explain]   no reader block"
        | .error e, _ | _, .error e => say s!"[explain]   block export error: {e}"
  -- report: per name, per address, per class
  let mut tsv := "name\taddress\tverdict\tcause\n"
  let mut byWord : Std.HashMap String Nat := {}
  let mut byClass : Std.HashMap (String × String) Nat := {}
  let mut addrVerdict : Std.HashMap Address String := {}
  for n in names do
    let v := verdicts.getD n (.unsupported "no verdict")
    let addr := match namedAddr[n]? with
      | some a => toString a
      | none => ""
    tsv := tsv ++ s!"{n}\t{addr}\t{v.word}\t{v.cause}\n"
    byWord := byWord.insert v.word (byWord.getD v.word 0 + 1)
    unless v.isCertified do
      byClass := byClass.insert (v.word, v.cls) (byClass.getD (v.word, v.cls) 0 + 1)
    if let some a := namedAddr[n]? then
      let old := addrVerdict.getD a "certified"
      addrVerdict := addrVerdict.insert a (if old == "certified" then v.word else old)
  let mut byAddr : Std.HashMap String Nat := {}
  for (_, w) in addrVerdict.toList do byAddr := byAddr.insert w (byAddr.getD w 0 + 1)
  IO.FS.writeFile s!"{cfg.out}.tsv" tsv
  let words := #["certified", "unsupported", "blocked", "rejected"]
  let classes := byClass.toArray.qsort (fun a b => a.2 > b.2 || (a.2 == b.2 && toString a.1 < toString b.1))
  let mut classText := "verdict\tclass\tcount\n"
  for ((w, c), k) in classes do classText := classText ++ s!"{w}\t{c}\t{k}\n"
  IO.FS.writeFile s!"{cfg.out}.classes.tsv" classText
  let (projRows, projJson) := measureProjections env names refs verdicts
  IO.FS.writeFile s!"{cfg.out}.proj.tsv" projRows
  say s!"[certify] raw projections: {projJson.compress}"
  let (receiptRefused, receiptJson) ← projectionReceipts env names refs cfg.out
  let json := Lean.Json.mkObj [
    ("ixe", Lean.toJson cfg.ixe), ("names", Lean.toJson names.size),
    ("notInArtifact", Lean.toJson notInArtifact),
    ("perName", Lean.Json.mkObj (words.toList.map fun w => (w, Lean.toJson (byWord.getD w 0)))),
    ("perAddress", Lean.Json.mkObj (words.toList.map fun w => (w, Lean.toJson (byAddr.getD w 0)))),
    ("classes", Lean.Json.arr (classes.map fun ((w, c), k) => Lean.Json.mkObj
      [("verdict", Lean.toJson w), ("class", Lean.toJson c), ("count", Lean.toJson k)])),
    ("rawProjections", projJson), ("projectionReceipts", receiptJson)]
  IO.FS.writeFile s!"{cfg.out}.json" json.pretty
  let counts := " ".intercalate (words.toList.map fun w => s!"{w}={byWord.getD w 0}")
  let addrCounts := " ".intercalate (words.toList.map fun w => s!"{w}={byAddr.getD w 0}")
  say s!"[certify] per name: {counts}; per address: {addrCounts}; total {(← IO.monoMsNow) - t0} ms"
  if byWord.getD "certified" 0 == 0 then
    IO.eprintln "[certify] FAIL: nothing certified"
    return 1
  if byWord.getD "rejected" 0 != 0 then
    IO.eprintln s!"[certify] FAIL: {byWord.getD "rejected" 0} rejected"
    return 1
  if receiptRefused != 0 then
    IO.eprintln s!"[certify] FAIL: {receiptRefused} constants with a raw projection on a non-direct structure-like have no accepted receipt"
    return 1
  return 0

end Ix.CompileCert.Certifier
