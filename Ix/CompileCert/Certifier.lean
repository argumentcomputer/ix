import Ix.CompileCert.Changed
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

/-! ## Expression size and source features on the DAG (M5 WP-B; untrusted triage)

Since M5 WP-B the certified check walks expressions on the DAG: the export
(`exportExprWithShared`, through `@[csimp]`), the reference walk
(`refsInShared`) and the entry comparison (`DirectEntry.decEqShared`, through
`Kernel.Expr.beqMemo`) visit a node shared by pointer once per expression. The
budget therefore bounds the number of distinct `Expr` objects
(`Lean.Expr.numObjs`, core's pointer-set count), summed over the declaration's
expressions; the tree size (`treeSizeShared`, exact, computed on the DAG) is
reported for the large ones (`<prefix>.sizes.tsv`), not budgeted. -/

/-- Distinct `Expr` objects of a declaration's type, value and rule right-hand
sides, each expression counted separately (a bound on the shared walks). -/
def declDagSize (ci : Lean.ConstantInfo) : IO Nat := do
  let exprs : Array Lean.Expr := #[ci.type] ++ match ci with
    | .defnInfo v => #[v.value]
    | .thmInfo v => #[v.value]
    | .opaqueInfo v => #[v.value]
    | .recInfo v => v.rules.toArray.map (·.rhs)
    | _ => #[]
  exprs.foldlM (fun acc e => return acc + (← e.numObjs)) 0

/-- A map from expressions under core's pointer-first equality, as `ExprSet`. -/
abbrev ExprNatMap := @Std.HashMap Lean.Expr Nat ⟨Lean.Expr.eqv⟩ _

/-- The exact tree size (the measure of `treeSize`, uncapped), computed on the
DAG: each distinct subterm once. -/
def treeSizeShared (memo : ExprNatMap) (e : Lean.Expr) : Nat × ExprNatMap :=
  match @Std.HashMap.get? Lean.Expr Nat ⟨Lean.Expr.eqv⟩ _ memo e with
  | some n => (n, memo)
  | none =>
    let (n, memo) : Nat × ExprNatMap := match e with
      | .app f a =>
        let (x, m) := treeSizeShared memo f
        let (y, m) := treeSizeShared m a
        (x + y + 1, m)
      | .lam _ t b _ | .forallE _ t b _ =>
        let (x, m) := treeSizeShared memo t
        let (y, m) := treeSizeShared m b
        (x + y + 1, m)
      | .letE _ t v b _ =>
        let (x, m) := treeSizeShared memo t
        let (y, m) := treeSizeShared m v
        let (z, m) := treeSizeShared m b
        (x + y + z + 1, m)
      | .mdata _ b | .proj _ _ b =>
        let (x, m) := treeSizeShared memo b
        (x + 1, m)
      | _ => (1, memo)
    (n, @Std.HashMap.insert Lean.Expr Nat ⟨Lean.Expr.eqv⟩ _ memo e n)

/-- `declTreeSize` without the cap, computed on the DAG. -/
def declTreeSizeShared (ci : Lean.ConstantInfo) : Nat :=
  let exprs : List Lean.Expr := ci.type :: match ci with
    | .defnInfo v => [v.value]
    | .thmInfo v => [v.value]
    | .opaqueInfo v => [v.value]
    | .recInfo v => v.rules.map (·.rhs)
    | _ => []
  (exprs.foldl (fun (acc, m) e => let (n, m) := treeSizeShared m e; (acc + n, m))
    (0, (@Std.HashMap.emptyWithCapacity Lean.Expr Nat ⟨Lean.Expr.eqv⟩ _ 1024))).1

/-- `unsupportedExpr` on the DAG: the same first feature of the same
left-to-right pre-order traversal, each distinct subterm visited once. A
revisited subterm was explored completely without a feature (in a DAG it is
not an ancestor, and a feature ends the walk), so skipping it changes nothing. -/
def unsupportedExprShared (seen : ExprSet) (e : Lean.Expr) : Option String × ExprSet :=
  if seen.has e then (none, seen) else
  let seen := seen.add e
  match e with
  | .fvar _ => (some "free variable in closed source", seen)
  | .mvar _ => (some "expression metavariable", seen)
  | .mdata _ b => unsupportedExprShared seen b
  | .sort u => (if u.hasMVar then some "universe metavariable" else none, seen)
  | .const _ us => (if us.any Lean.Level.hasMVar then some "universe metavariable" else none, seen)
  | .app f a =>
    match unsupportedExprShared seen f with
    | (some x, s) => (some x, s)
    | (none, s) => unsupportedExprShared s a
  | .lam _ t b _ | .forallE _ t b _ =>
    match unsupportedExprShared seen t with
    | (some x, s) => (some x, s)
    | (none, s) => unsupportedExprShared s b
  | .letE _ t v b _ =>
    match unsupportedExprShared seen t with
    | (some x, s) => (some x, s)
    | (none, s) =>
      match unsupportedExprShared s v with
      | (some x, s) => (some x, s)
      | (none, s) => unsupportedExprShared s b
  | .proj _ _ b => unsupportedExprShared seen b
  | _ => (none, seen)

/-- `unsupportedSource` on the DAG (same result, same order). -/
def unsupportedSourceShared (ci : Lean.ConstantInfo) : Option String :=
  if !sourceSupported ci then some "unsafe or partial source declaration"
  else
    let exprs : List Lean.Expr := ci.type :: match ci with
      | .defnInfo v => [v.value]
      | .thmInfo v => [v.value]
      | .opaqueInfo v => [v.value]
      | .recInfo v => v.rules.map (·.rhs)
      | _ => []
    (exprs.foldl (fun (found, seen) e => match found with
      | some x => (some x, seen)
      | none => unsupportedExprShared seen e) (none, ExprSet.empty)).1

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

/-! ## W+ (M5): changed constants (untrusted orchestration)

What the certifier proposes for W+ (`Ix/CompileCert/Changed.lean`) and how it
classifies; nothing here is trusted. **Image claims**: the Lean recursors whose
named record is a singleton definition (a changed block's recursor holds its
image, Def 3.4); the map check refuses a wrong claim. **Support rows**: for a
recursor claimed an image whose correspondence fails, one theorem per
computation rule (`ruleStatements`), proof `Eq.refl` under the rule's
telescope; for a definition with a definition header whose value differs, the
row `@Eq.{ℓ} T c value`, `ℓ` computed by `Meta.getLevel` (the fold validates
it). Rows are named `<target name>._ix_eq.<k>` (D14 keeps `_ix` components out
of Lean names, the fold checks freshness), **pre-screened** one by one with the
stepping checker over the admitted environment, and folded by the certified
checker once (`foldSupport`, inside `checkIndexed'`). A definition whose `rfl`
row the checker refuses falls back to Lean's `c.eq_def` (a row of the artifact
under the map). Routes (`direct`, `raw`, `theorem`, `equations:rfl`,
`equations:eq_def`, `changed-block`) recompute the same Boolean checks the
decision uses and only label the TSV. -/

/-- The certifier's image claims (untrusted). -/
def imageClaims (env : Lean.Environment) (store : RecordStore) (names : Array Lean.Name)
    (namedAddr : Std.HashMap Lean.Name Address) : Std.HashSet Lean.Name := Id.run do
  let mut out : Std.HashSet Lean.Name := {}
  for n in names do
    let some (.recInfo _) := env.find? n | continue
    let some a := namedAddr[n]? | continue
    let some c := store[a]? | continue
    if let .defn d := c.info then
      if d.kind == .defn then out := out.insert n
  return out

/-- `λ telescope, @Eq.refl.{ℓ} carrier left` for `∀ telescope, @Eq.{ℓ} carrier left right`. -/
def rflProof : Kernel.Expr → Option Kernel.Expr
  | .forallE t b m => (rflProof b).map fun body => .lam t body m
  | e => (eqParts e).map fun (level, carrier, left, _) =>
    .app (.app (.const Kernel.eqReflName [level]) carrier) left

/-- Append `i` to a support row's name (rows of the constants of one alias
fiber would otherwise share a name, and the fold refuses a duplicate). -/
def renameRow (i : Nat) : Kernel.Declaration → Kernel.Declaration
  | .thmDecl cv v => .thmDecl { cv with name := cv.name.num i } v
  | d => d

/-- A support row `name : statement := rflProof statement`. -/
def supportRow (name : Kernel.Name) (levels : List Kernel.Name) (statement : Kernel.Expr) :
    Option Kernel.Declaration :=
  (rflProof statement).map fun proof => .thmDecl ⟨name, levels, statement⟩ proof

/-- A Lean level evaluated at a valuation of its parameters (metavariables at 0). -/
def evalSourceLevel (val : Lean.Name → Nat) : Lean.Level → Nat
  | .zero => 0
  | .succ u => evalSourceLevel val u + 1
  | .max u v => max (evalSourceLevel val u) (evalSourceLevel val v)
  | .imax u v => if evalSourceLevel val v == 0 then 0 else max (evalSourceLevel val u) (evalSourceLevel val v)
  | .param p => val p
  | .mvar _ => 0

/-- The largest `succ` offset in a level. -/
def levelOffset : Lean.Level → Nat
  | .succ u => levelOffset u + 1
  | .max u v | .imax u v => max (levelOffset u) (levelOffset v)
  | _ => 0

/-- A small level equal to `l` at every valuation of `params` in `0 … offset + 2`
(untrusted: the fold validates the row it goes into), or `none`. `Meta.getLevel`
returns long `imax` chains (one per binder) that `Level.normalize` keeps and
that the export (`Ixon.canonUniv` under `exportLevel`) does not finish on. -/
def smallEquivalentLevel (params : List Lean.Name) (l : Lean.Level) : Option Lean.Level := Id.run do
  let bound := levelOffset l + 3
  if params.length > 4 || bound ^ params.length > 4096 then return none
  let rec valuations : List Lean.Name → List (List (Lean.Name × Nat))
    | [] => [[]]
    | p :: ps => (valuations ps).flatMap fun v => (List.range bound).map fun k => (p, k) :: v
  let points := valuations params
  let agrees (c : Lean.Level) : Bool := points.all fun v =>
    let val := fun n => (v.lookup n).getD 0
    evalSourceLevel val c == evalSourceLevel val l
  let ps := params.map Lean.Level.param
  let base : List Lean.Level :=
    [.zero, .succ .zero] ++ ps ++ ps.map .succ ++ ps.map (Lean.Level.max (.succ .zero)) ++
      (match ps with
        | [] => []
        | p :: rest => [rest.foldl Lean.Level.max p, Lean.Level.max (.succ .zero) (rest.foldl Lean.Level.max p)])
  -- a Π-type's sort is `imax` of its binders' and its body's: `imax c p` vanishes with `p`
  let candidates := base ++ base.flatMap fun c => ps.map fun p => Lean.Level.imax c p
  return candidates.find? agrees

/-- The rows proposed for one changed constant (each with what it states:
`type`, `rule <k>` or `rfl`), or why none could be formed. -/
structure RowProposal where
  owner : Lean.Name
  rows : Array (String × Kernel.Declaration) := #[]
  failure : Option String := none
  deriving Inhabited

/-- Propose the rows of a failing theorem, definition or recursor claimed an
image: a **type row** when the reader entry of the right kind has the exported
name and universes but another (convertible) type, and the **equation rows**
of a recursor (one per rule) or a definition (`rfl`). -/
def proposeRows (env : Lean.Environment) (sh : SharedW) (hints : HintsW) (ci : Lean.ConstantInfo) :
    IO RowProposal := do
  let trace := (← IO.getEnv "IX_CERTIFY_TRACE").isSome
  let t0 ← IO.monoMsNow
  let step (what : String) : IO Unit := do
    if trace then IO.println s!"[certify]   {ci.name}: {what} at {(← IO.monoMsNow) - t0} ms"; (← IO.getStdout).flush
  let cy := sh.small hints.toHints ci.name
  match directHeader cy ci with
  | .error e => return { owner := ci.name, failure := some s!"header export: {e}" }
  | .ok header =>
    step "header exported"
    let actualType : Option Kernel.Expr := match ci, sh.entries[hints.entryAt ci.name]? with
      | .thmInfo _, some (.thm cv _) | .defnInfo _, some (.defn cv _ _) | .recInfo _, some (.defn cv _ _) =>
        if cv.name == header.name && cv.levelParams == header.levelParams then some cv.type else none
      | _, _ => none
    let some ixType := actualType
      | return { owner := ci.name, failure := some "no reader entry of the required kind under the exported name and universes" }
    let typeDiffers := ixType != header.type
    step s!"types compared (differ: {typeDiffers})"
    let tc : TermContext := ⟨cy, ci.levelParams, header.levelParams⟩
    -- the universe of Lean's type, for a type row and for a definition's `rfl` row
    let level? ← if typeDiffers || (match ci with | .defnInfo _ => true | _ => false) then
        match ← LoweringLean.runMeta env (Lean.Meta.getLevel ci.type) with
        | .error e => pure (Except.error s!"universe of the type: {oneLine e}")
        -- a small equivalent level: `getLevel`'s long `imax` chains are kept by `normalize`
        -- and the export (`Ixon.canonUniv`) does not finish on them
        | .ok level =>
          match smallEquivalentLevel ci.levelParams level.normalize with
          | some small => pure (exportLevel tc small)
          | none =>
            if levelOffset level < 16 && level.normalize.depth < 24 then pure (exportLevel tc level.normalize)
            else pure (.error "universe of the type: no small equivalent level")
      else pure (.error "not needed")
    step "universe computed"
    let mut rows : Array (String × Kernel.Declaration) := #[]
    if typeDiffers then
      match level? with
      | .error e => return { owner := ci.name, failure := some s!"type row: {e}" }
      | .ok ℓ =>
        match supportRow (header.name.str "_ix_type") header.levelParams
            (kernelEq (.succ ℓ) (.sort ℓ) ixType header.type) with
        | some row => rows := rows.push ("type", row); step "type row built"
        | none => return { owner := ci.name, failure := some "type row shape" }
    let base := header.name.str "_ix_eq"
    match ci with
    | .recInfo r =>
      match ruleStatements cy r with
      | .error e => return { owner := ci.name, rows, failure := some s!"rule statement export: {e}" }
      | .ok statements =>
        for (s, k) in statements.zipIdx do
          match supportRow (base.num k) header.levelParams s with
          | some d => rows := rows.push (s!"rule {k}", d)
          | none => return { owner := ci.name, rows, failure := some "rule statement is not an Eq telescope" }
        return { owner := ci.name, rows }
    | .defnInfo d =>
      match level?, definitionSides cy d header.levelParams with
      | .ok ℓ, .ok (left, right) =>
        match supportRow (base.num 0) header.levelParams (kernelEq ℓ header.type left right) with
        | some row => return { owner := ci.name, rows := rows.push ("rfl", row) }
        | none => return { owner := ci.name, rows, failure := some "rfl statement shape" }
      | .error e, _ | _, .error e => return { owner := ci.name, rows, failure := some s!"rfl statement: {e}" }
    | .thmInfo _ =>
      if rows.isEmpty then return { owner := ci.name, failure := some "the statement is the exported one" }
      return { owner := ci.name, rows }
    | _ => return { owner := ci.name, failure := some "not a theorem, recursor or definition" }

/-- Pre-screen rows (untrusted): each against the admitted environment with the
stepping checker; `none` when accepted, the checker's message otherwise. -/
def prescreen (pins : List Ix.Kernel.NatOpPinSet) (base : Benchmarks.Kernel.CheckIxeStep.Checker)
    (rows : Array Kernel.Declaration) : Array (Option String) :=
  let tasks := rows.map fun row => Task.spawn fun _ =>
    match (base.step pins row).2 with
    | none => none
    | some e => let (w, m) := checkOutcome e; some s!"{w}: {m}"
  tasks.map Task.get

/-- A row's pre-screen outcome: accepted, refused by the stepping checker (its
message), or over its time budget (**not decided**: it was not run, or it was
still running when its budget ran out). -/
inductive Screened where
  | accepted
  | refused (message : String)
  | overBudget (budgetMs : Nat)
  deriving Inhabited

def Screened.text : Screened → String
  | .accepted => "accepted"
  | .refused m => m
  | .overBudget b => s!"over the pre-screen time budget ({b} ms)"

/-- The class of a changed constant that would pass if its rows over the
pre-screen time budget were accepted (a resource limit, like the size budget). -/
def overBudgetClass : String := "changed constant: a type or equation row over the pre-screen time budget"

/-- What `prescreenTimed` returns: each row's outcome and time (ms), and how
many rows were left running past their budget. -/
structure Prescreened where
  results : Array (Screened × Nat)
  abandoned : Nat

/-- `prescreen` on at most `workers` active dedicated threads, with each row's
time (diagnostics) and a time budget per row (`budgetOf j`, ms): a row still
running after its budget is reported `overBudget` and no longer waited for (the
checker's pure code cannot be cancelled: its thread runs on in the background
until it finishes or the process exits, which `compile-certify` does at once
after its report); a row whose budget is `0` is not run. -/
def prescreenTimed (pins : List Ix.Kernel.NatOpPinSet) (base : Benchmarks.Kernel.CheckIxeStep.Checker)
    (rows : Array Kernel.Declaration) (workers : Nat) (budgetOf : Nat → Nat)
    (labels : Array String := #[]) (log : String → IO Unit := fun _ => pure ()) (trace : Bool := false) :
    IO Prescreened := do
  let w := max workers 1
  let label (j : Nat) : String := labels.getD j s!"row {j}"
  let mut results : Array (Screened × Nat) := Array.replicate rows.size (.refused "pre-screen: not run", 0)
  let mut next := 0
  let mut active : Array (Nat × Nat × Task (Except IO.Error (Screened × Nat))) := #[]
  let mut abandoned := 0
  while next < rows.size || !active.isEmpty do
    while active.size < w && next < rows.size do
      let j := next
      next := next + 1
      if budgetOf j == 0 then
        -- a zero budget admits no checking time: the row is not run (not decided)
        results := results.set! j (.overBudget 0, 0)
        continue
      let row := rows[j]!
      if trace then log s!"[certify] W+ pre-screen start {label j}"
      let started ← IO.monoMsNow
      let task ← IO.asTask (prio := .dedicated) do
        let t0 ← IO.monoMsNow
        let outcome : Screened := match (base.step pins row).2 with
          | none => .accepted
          | some e => let (word, m) := checkOutcome e; .refused s!"{word}: {m}"
        -- the match forces the outcome before the clock is read again
        match outcome with
        | .accepted => return (.accepted, (← IO.monoMsNow) - t0)
        | o => return (o, (← IO.monoMsNow) - t0)
      active := active.push (j, started, task)
    if active.isEmpty then continue
    -- wait until a row finishes, at most a second (the budgets are polled)
    let waited ← IO.monoMsNow
    repeat
      if ← active.anyM (fun (_, _, t) => do return (← IO.hasFinished t)) then break
      if (← IO.monoMsNow) - waited ≥ 1000 then break
      IO.sleep 5
    let now ← IO.monoMsNow
    let mut still : Array (Nat × Nat × Task (Except IO.Error (Screened × Nat))) := #[]
    for (j, started, task) in active do
      if ← IO.hasFinished task then
        match ← IO.wait task with
        | .ok (verdict, ms) =>
          if trace || ms > 10000 then
            log s!"[certify] W+ pre-screen {label j}: {ms} ms, {verdict.text.take 120}"
          results := results.set! j (verdict, ms)
        | .error e => results := results.set! j (.refused s!"pre-screen task failed: {e}", now - started)
      else if now - started > budgetOf j then
        abandoned := abandoned + 1
        log s!"[certify] W+ pre-screen {label j}: {(Screened.overBudget (budgetOf j)).text}; left running"
        results := results.set! j (.overBudget (budgetOf j), now - started)
      else still := still.push (j, started, task)
    active := still
  if abandoned > 0 then log s!"[certify] W+ pre-screen: {abandoned} rows left running over their time budget"
  return { results, abandoned }

/-- The route a declaration passes by (the decision's own Boolean checks,
recomputed to label the report), or `none`. `, type-row` marks a header whose
type matched through a type row. -/
def routeOf (sh : SharedW) (hints : HintsW) (ci : Lean.ConstantInfo) : Option String :=
  let cy := sh.small hints.toHints ci.name
  let position := hints.entryAt ci.name
  let header? := match directHeader cy ci with
    | .ok h => some h
    | .error _ => none
  let typeRow : String := match header?, sh.entries[position]? with
    | some h, some (.defn cv _ _) | some h, some (.thm cv _) => if cv.type == h.type then "" else ", type-row"
    | _, _ => ""
  let corr : Option String :=
    if directAt cy sh.entries position ci then some "direct"
    else if rawAt cy sh.constants (hints.recordAt ci.name) sh.reader ci then some "raw"
    else if thmAt cy sh.entries sh.rows position (hints.rowsAt ci.name) ci then some s!"theorem{typeRow}"
    else if equationsAt cy sh.entries sh.rows position (hints.rowsAt ci.name) ci then
      match ci, header? with
      | .defnInfo d, some h =>
        match definitionSides cy d h.levelParams with
        | .ok (left, right) =>
          if rflAt sh.rows (hints.rowsAt ci.name) h.levelParams h.type left right then
            some s!"equations:rfl{typeRow}"
          else some s!"equations:eq_def{typeRow}"
        | .error _ => some s!"equations:eq_def{typeRow}"
      | _, _ => some s!"equations:rfl{typeRow}"
    else none
  match corr with
  | none => none
  | some c =>
    let block : Option String :=
      if decide (BlockMatch cy sh.state ci) then some c
      else if decide (ChangedBlockMatch cy sh.state ci) then some s!"{c}, changed-block"
      else none
    match block with
    | none => none
    | some b => if (definitionGroupImage cy ci).isSome then some b else none

/-- Stream positions by reader name (first occurrence). -/
def entryPositions (entries : Array DirectEntry) : Std.HashMap Kernel.Name Nat := Id.run do
  let mut m : Std.HashMap Kernel.Name Nat := {}
  for i in [0:entries.size] do
    let n := match entries[i]? with
      | some e => entryName e
      | none => .anonymous
    unless m.contains n do m := m.insert n i
  return m

/-- `buildHints` with the row positions of W+. -/
def buildHintsW (input : Input) (sh : SharedW) (entryPos : Std.HashMap Kernel.Name Nat)
    (queries : Lean.Name → Array Lean.Name) (workers : Nat)
    (rowsAt : Lean.Name → List Nat) : HintsW :=
  let pos : Std.HashMap Lean.Name Nat := Id.run do
    let mut m : Std.HashMap Lean.Name Nat := {}
    for (ci, i) in input.source.declarations.zipIdx do m := m.insert ci.name i
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
  { sourceAt := at_, mapAt := at_, workers, rowsAt
    entryAt := fun n => match targets[n]? with
      | some e => (entryPos[sh.reader.nameOf e.target]?).getD 0
      | none => 0
    recordAt := fun n => match targets[n]? with
      | some e => (recordPos[e.record]?).getD 0
      | none => 0 }

/-- A kernel name as dotted text (diagnostics). -/
def kernelNameStr : Kernel.Name → String
  | .anonymous => ""
  | .str .anonymous s => s
  | .num .anonymous n => toString n
  | .str p s => s!"{kernelNameStr p}.{s}"
  | .num p n => s!"{kernelNameStr p}.{n}"

/-- A one-line head of an expression (diagnostics). -/
def exprHead : Kernel.Expr → String
  | .bvar i => s!"#{i}"
  | .fvar i _ => s!"fvar {i}"
  | .sort u => s!"Sort {repr u}"
  | .const n us => s!"const {kernelNameStr n} {us.length} levels"
  | .app f _ => s!"app ({exprHead f})"
  | .lam .. => "lam"
  | .forallE .. => "forall"
  | .letE .. => "let"
  | .lit (.natVal n) => s!"nat {n}"
  | .lit (.strVal _) => "string"
  | .proj n i _ => s!"proj {kernelNameStr n} {i}"

/-- The path to the first difference of two expressions and their heads there (diagnostics). -/
partial def firstDiff (path : String) : Kernel.Expr → Kernel.Expr → Option String
  | .app f a, .app g b => (firstDiff s!"{path}.fn" f g).orElse fun _ => firstDiff s!"{path}.arg" a b
  | .lam t b _, .lam u c _ | .forallE t b _, .forallE u c _ =>
    (firstDiff s!"{path}.dom" t u).orElse fun _ => firstDiff s!"{path}.body" b c
  | .letE t v b, .letE u w c =>
    ((firstDiff s!"{path}.type" t u).orElse fun _ => firstDiff s!"{path}.val" v w).orElse fun _ =>
      firstDiff s!"{path}.body" b c
  | .proj n i e, .proj m j f =>
    if n == m && i == j then firstDiff s!"{path}.proj" e f else some s!"{path}: proj differs"
  | x, y => if x == y then none else some s!"{path}: {exprHead x} vs {exprHead y}"

/-- A W+ diagnosis of a declaration that fails every route (untrusted). -/
def diagnoseW (sh : SharedW) (hints : HintsW) (ci : Lean.ConstantInfo) (entry : Option MapEntry)
    (rowRefusal : Option String) : Verdict :=
  let cy := sh.small hints.toHints ci.name
  match directHeader cy ci with
  | .error e =>
    if (e.splitOn "missing source").length > 1 then .rejected s!"certifier: small context incomplete: {e}"
    else if (e.splitOn "unsupported").length > 1 then .unsupported s!"export: {e}"
    else .rejected s!"export: {e}"
  | .ok header =>
    let actual := sh.entries[hints.entryAt ci.name]?
    let headerDetail : String := match actual with
      | none => "no reader entry under the target's name"
      | some a =>
        let (kind, cv) : String × Kernel.ConstantVal := match a with
          | .defn cv .. => ("definition", cv) | .thm cv _ => ("theorem", cv)
          | .opaque cv _ => ("opaque", cv) | .axiom cv => ("axiom", cv) | .quot _ cv => ("quotient", cv)
          | .induct cv _ => ("inductive", cv) | .ctor cv .. => ("constructor", cv)
          | .recursor cv .. => ("recursor", cv)
        if cv.name != header.name then s!"name differs ({kind})"
        else if cv.levelParams != header.levelParams then s!"universe parameters differ ({kind})"
        else if cv.type != header.type then s!"type differs ({kind})"
        else s!"{kind}"
    let corrOk := directAt cy sh.entries (hints.entryAt ci.name) ci ||
      rawAt cy sh.constants (hints.recordAt ci.name) sh.reader ci ||
      thmAt cy sh.entries sh.rows (hints.entryAt ci.name) (hints.rowsAt ci.name) ci ||
      equationsAt cy sh.entries sh.rows (hints.entryAt ci.name) (hints.rowsAt ci.name) ci
    if !corrOk then
      let refusal := match rowRefusal with
        | some r => s!"; equation row: {r}"
        | none => ""
      match ci with
      | .thmInfo _ => .rejected s!"correspondence: theorem: reader entry {headerDetail}{refusal}"
      | .recInfo _ =>
        if headerDetail == "definition" then .rejected s!"correspondence: recursor image: equations fail{refusal}"
        else .rejected s!"correspondence: recursor: reader entry {headerDetail}{refusal}"
      | .defnInfo d =>
        if headerDetail == "definition" then
          let clique := d.all.length > 1 || (d.value.getUsedConstants.contains ``WellFounded.fix)
          let eqDef := sh.cx.source.find (d.name.str "eq_def")
          if clique && eqDef.isNone then
            .unsupported "changed definition: transported clique member without eq_def"
          else .rejected s!"correspondence: definition: value differs, no equation row accepted{refusal}"
        else .rejected s!"correspondence: definition: reader entry {headerDetail}{refusal}"
      | _ => .rejected s!"correspondence: reader entry {headerDetail}"
    else if !(decide (BlockMatch cy sh.state ci) || decide (ChangedBlockMatch cy sh.state ci)) then
      .rejected "inductive block differs (whole and changed)"
    else if !(definitionGroupImage cy ci).isSome then .rejected "definition group member unmapped"
    else match entry with
      | none => .rejected "no map entry"
      | some e =>
        if !decide (Kernel.Reader.resolve sh.reader.store e.record = some e.target) then
          .rejected "map: record does not resolve to the proposed member"
        else if !decide (NameAgrees cy e.source (sh.reader.nameOf e.target)) then
          .rejected "map: reader name differs from the exported name"
        else .rejected "map: recursor flags or image claim differ"

/-- The positions in the row pool (`SharedW.rows`) of a name's rows: its own
support rows (after the `offset` stream entries), then Lean's `eq_def` entry. -/
def rowsAtWith (entries : Std.HashMap Lean.Name MapEntry) (entryPos : Std.HashMap Kernel.Name Nat)
    (reader : Kernel.Reader.Ctx) (rowsOf : Std.HashMap Lean.Name (Array Nat)) (offset : Nat)
    (n : Lean.Name) : List Nat :=
  ((rowsOf.getD n #[]).map (offset + ·)).toList ++
    (match entries[n.str "eq_def"]? with
      | some e => (entryPos[reader.nameOf e.target]?).toList
      | none => [])

/-- What the W+ pre-pass learns over one input (untrusted): each declaration's
route or diagnosis, and the pre-screened support rows. -/
structure PrePass where
  routes : Std.HashMap Lean.Name String := {}
  failed : Std.HashMap Lean.Name Verdict := {}
  support : Array Kernel.Declaration := #[]
  rowsOf : Std.HashMap Lean.Name (Array Nat) := {}
  /-- Per constant, the first definite refusal of one of its rows (by the
  stepping checker) or why its rows could not be formed. -/
  refusals : Std.HashMap Lean.Name String := {}
  entryPos : Std.HashMap Kernel.Name Nat := {}
  passOneFailures : Nat := 0
  proposedRows : Nat := 0
  proposedFor : Nat := 0
  refusedRows : Nat := 0
  /-- Rows over their pre-screen time budget (not decided; never folded). -/
  overBudgetRows : Nat := 0
  /-- Of those, rows left running in the background. -/
  abandonedRows : Nat := 0

/-- The default time budget of one row in the pre-screen (ms). -/
def defaultRowBudget : Nat := 60000

/-- The W+ pre-pass: every declaration's own checks (pass 1), rows for the
failing theorems, definitions and recursors claimed images, the row-by-row
pre-screen (each row within its time budget `rowBudget owner what`, ms), and
the failing declarations again with their rows and Lean's `eq_def` (pass 2),
diagnosing what still fails. A row over its budget is not decided: it is never
folded, and a constant that fails is classified `overBudgetClass` (Unsupported)
only if it passes with its rows over the budget taken as accepted, that is, if
those rows are all it lacks; otherwise it keeps its diagnosis (a definite
refusal of another row stays Rejected). -/
def wPrePass (env : Lean.Environment) (entries : Std.HashMap Lean.Name MapEntry) (input : Input)
    (images : Std.HashSet Lean.Name) (artifact : AdmittedArtifact input.toArtifactInput)
    (queries : Lean.Name → Array Lean.Name) (workers : Nat) (log : String → IO Unit)
    (rowsLog : String → IO Unit := fun _ => pure ())
    (rowBudget : Lean.Name → String → Nat := fun _ _ => defaultRowBudget) : IO PrePass := do
  let imagesFn : Lean.Name → Bool := fun n => images.contains n
  let w := max workers 1
  let pass (sh : SharedW) (hints : HintsW) (decls : List Lean.ConstantInfo) :
      Array (Lean.ConstantInfo × Option String) :=
    let tasks := (List.range w).map fun i => Task.spawn fun _ =>
      (strideOf w i 0 decls).map fun ci =>
        let ok := ((entries[ci.name]?).map (sh.entryCheck hints.toHints)).getD false
        (ci, if ok then routeOf sh hints ci else none)
    tasks.toArray.flatMap fun t => t.get.toArray
  let t5 ← IO.monoMsNow
  let mut out : PrePass := {}
  -- pass 1: every declaration's own W+ checks, no support yet
  let sh1 := SharedW.ofArtifact input imagesFn artifact #[]
  let entryPos := entryPositions sh1.entries
  out := { out with entryPos }
  let hints1 := buildHintsW input sh1 entryPos queries workers (fun _ => [])
  let r1 := pass sh1 hints1 input.source.declarations
  let mut failing : Array Lean.ConstantInfo := #[]
  for (ci, route) in r1 do
    match route with
    | some r => out := { out with routes := out.routes.insert ci.name r }
    | none => failing := failing.push ci
  out := { out with passOneFailures := failing.size }
  let t6 ← IO.monoMsNow
  log s!"[certify] W+ pass 1 (no support): {r1.size - failing.size} of {r1.size} pass their own checks, \
    {failing.size} fail; {t6 - t5} ms"
  -- rows for the failing theorems, definitions and recursors claimed images
  let proposable := failing.filter fun ci => match ci with
    | .recInfo _ => images.contains ci.name
    | .defnInfo _ | .thmInfo _ => true
    | _ => false
  let mut proposals : Array RowProposal := #[]
  let tp ← IO.monoMsNow
  let trace := (← IO.getEnv "IX_CERTIFY_TRACE").isSome
  for ci in proposable do
    let t0 ← IO.monoMsNow
    if trace then log s!"[certify] W+ rows of {ci.name}: …"
    let p ← proposeRows env sh1 hints1 ci
    let t1 ← IO.monoMsNow
    if trace || t1 - t0 > 5000 then log s!"[certify] W+ rows of {ci.name}: {t1 - t0} ms ({p.rows.size} rows)"
    proposals := proposals.push p
  let natPins ← IO.ofExcept Ix.Kernel.Reader.builtinNatOpPins
  let base : Benchmarks.Kernel.CheckIxeStep.Checker := { fe := Ix.Kernel.mkFEnv artifact.env }
  let allRows := proposals.flatMap fun p => p.rows.map (·.2)
  let tq ← IO.monoMsNow
  log s!"[certify] W+ rows: {allRows.size} proposed for {proposals.size} constants; {tq - tp} ms"
  let rowLabels := proposals.flatMap fun p => p.rows.map fun (what, _) => (p.owner, what)
  let labels := rowLabels.map fun (owner, what) => s!"{owner} {what}"
  let budgets := rowLabels.map fun (owner, what) => rowBudget owner what
  let screened ← prescreenTimed natPins base allRows workers (budgets.getD · defaultRowBudget) labels log trace
  -- per row: owner, what, time, verdict (diagnostics)
  let mut rowText := "owner\trow\tms\tverdict\n"
  for ((owner, what), (verdict, ms)) in rowLabels.zip screened.results do
    rowText := rowText ++ s!"{owner}\t{what}\t{ms}\t{oneLine verdict.text}\n"
  rowsLog rowText
  let mut k := 0
  let mut support : Array Kernel.Declaration := #[]
  let mut rowsOf : Std.HashMap Lean.Name (Array Nat) := {}
  let mut refusals : Std.HashMap Lean.Name String := {}
  let mut refusedRows := 0
  -- the rows over their budget, kept apart (never folded), by owner
  let mut overRows : Array Kernel.Declaration := #[]
  let mut overOf : Std.HashMap Lean.Name (Array Nat) := {}
  for p in proposals do
    -- every row the pre-screen accepts is kept; a refusal is recorded for the diagnosis
    let mut idx : Array Nat := #[]
    let mut overIdx : Array Nat := #[]
    for (what, row) in p.rows do
      match screened.results[k]? with
      | some (Screened.accepted, _) =>
        idx := idx.push support.size
        -- the index makes the name unique: an alias fiber shares one reader name
        support := support.push (renameRow support.size row)
      | some (Screened.refused refusal, _) =>
        refusedRows := refusedRows + 1
        unless refusals.contains p.owner do
          refusals := refusals.insert p.owner s!"{what} row refused by the checker: {oneLine refusal}"
      | some (Screened.overBudget _, _) =>
        overIdx := overIdx.push overRows.size
        overRows := overRows.push row
      | none => pure ()
      k := k + 1
    if let some f := p.failure then
      unless refusals.contains p.owner do refusals := refusals.insert p.owner f
    unless idx.isEmpty do rowsOf := rowsOf.insert p.owner idx
    unless overIdx.isEmpty do overOf := overOf.insert p.owner overIdx
  out := { out with support, rowsOf, refusals, refusedRows, proposedRows := allRows.size,
                    proposedFor := proposals.size, overBudgetRows := overRows.size,
                    abandonedRows := screened.abandoned }
  let t7 ← IO.monoMsNow
  log s!"[certify] W+ support: {allRows.size} rows proposed for {proposals.size} constants; \
    {support.size} accepted by the pre-screen, {refusedRows} refused, {overRows.size} over the time budget; \
    {t7 - t6} ms"
  -- pass 2: the failing declarations again, with their rows and Lean's `eq_def` as the fallback
  let sh2 := SharedW.ofArtifact input imagesFn artifact support
  let hints2 := buildHintsW input sh2 entryPos queries workers
    (rowsAtWith entries entryPos sh2.reader rowsOf sh2.entries.size)
  let r2 := pass sh2 hints2 failing.toList
  let mut stillFailing : Array Lean.ConstantInfo := #[]
  for (ci, route) in r2 do
    match route with
    | some r => out := { out with routes := out.routes.insert ci.name r }
    | none => stillFailing := stillFailing.push ci
  -- the constants with rows over the budget, again, with those rows taken as accepted
  -- (a hypothesis for the classification only: these rows are never folded)
  let mut undecided : Std.HashSet Lean.Name := {}
  let withOver := stillFailing.filter fun ci => overOf.contains ci.name
  unless withOver.isEmpty do
    let mut supportH := support
    for row in overRows do supportH := supportH.push (renameRow supportH.size row)
    let mut rowsOfH := rowsOf
    for (n, idxs) in overOf.toList do
      rowsOfH := rowsOfH.insert n (rowsOf.getD n #[] ++ idxs.map (support.size + ·))
    let shH := SharedW.ofArtifact input imagesFn artifact supportH
    let hintsH := buildHintsW input shH entryPos queries workers
      (rowsAtWith entries entryPos shH.reader rowsOfH shH.entries.size)
    for (ci, route) in pass shH hintsH withOver.toList do
      if route.isSome then undecided := undecided.insert ci.name
  for ci in stillFailing do
    let verdict : Verdict := if undecided.contains ci.name then .unsupported overBudgetClass
      else diagnoseW sh2 hints2 ci entries[ci.name]? refusals[ci.name]?
    out := { out with failed := out.failed.insert ci.name verdict }
  let t8 ← IO.monoMsNow
  log s!"[certify] W+ pass 2: {failing.size - stillFailing.size} of {failing.size} pass by theorem statement or \
    equations, {stillFailing.size} fail ({undecided.size} of them only for rows over the time budget); {t8 - t7} ms"
  return out

/-- The support rows of the final members, in their order, with each row's
owner and each member's row indices. -/
def finalSupport (finalNames : Array Lean.Name) (pre : PrePass) :
    Array Kernel.Declaration × Array Lean.Name × Std.HashMap Lean.Name (Array Nat) := Id.run do
  let mut sup : Array Kernel.Declaration := #[]
  let mut owners : Array Lean.Name := #[]
  let mut rowsFinal : Std.HashMap Lean.Name (Array Nat) := {}
  for n in finalNames do
    if let some idx := pre.rowsOf[n]? then
      let start := sup.size
      for i in idx do
        sup := sup.push pre.support[i]!
        owners := owners.push n
      rowsFinal := rowsFinal.insert n ((List.range idx.size).toArray.map (start + ·))
  return (sup, owners, rowsFinal)

/-- The source names whose positions a declaration's small context needs
(untrusted hints): the declaration, its block, its references and their
prefixes; for W+ also `Eq` and a recursor's rule constructors or a
definition's `eq_def`. -/
def queriesFor (env : Lean.Environment) (refs : Std.HashMap Lean.Name (Array Lean.Name))
    (n : Lean.Name) : Array Lean.Name := Id.run do
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
    | .recInfo v => #[n, ``Eq] ++ (v.rules.map (·.ctor)).toArray
    | .defnInfo _ => #[n, ``Eq, n.str "eq_def"]
    | _ => #[n]
  for d in block do
    out := out.insert d
    for r in refs.getD d #[] do
      out := (out.insert r).insert r.getPrefix
  return out.toArray

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
  /-- Size budget per declaration: distinct `Expr` objects of its type, value and rules, each
  expression counted separately (`declDagSize`; since M5 WP-B the certified walks run on the DAG). -/
  budget : Nat := 268435456
  /-- Tasks for the per-declaration checks. -/
  workers : Nat := 16
  /-- Names whose export and reader entries to print in full (diagnostics). -/
  explain : Array Lean.Name := #[]
  /-- W+: the time budget of one type or equation row in the pre-screen (ms; `0`: no row is
  checked, so no changed constant that needs a row is certified). -/
  rowBudget : Nat := defaultRowBudget
  /-- Only the raw-projection measurement and the receipt census (no W check). -/
  receiptsOnly : Bool := false
  /-- After W, decide the strong-model endpoint S per cone (`Ix/CompileCert/StrongCertifier.lean`). -/
  strong : Bool := false
  /-- S only on the cones of these roots (in this order), not on every constant. -/
  strongRoots : Array Lean.Name := #[]
  /-- S on a deterministic sample: every `strongEvery`-th W-certified constant
  in name order, plus the constants with a raw projection on a non-direct
  structure-like (0: every constant). -/
  strongEvery : Nat := 0
  /-- Cones with more source declarations than this are S-Unsupported (over budget). -/
  strongMaxCone : Nat := 20000
  /-- Cones decided at once (one task each). -/
  strongTasks : Nat := 32
  /-- Skip the global W check (probing): every constant the reader keeps is offered to S. -/
  strongOnly : Bool := false

/-- What the S path reuses from the W run. -/
structure WState where
  env : Lean.Environment
  produced : Ixon.Env
  store : RecordStore
  names : Array Lean.Name
  namedAddr : Std.HashMap Lean.Name Address
  refs : Std.HashMap Lean.Name (Array Lean.Name)
  verdicts : Std.HashMap Lean.Name Verdict
  /-- Each certified constant's route (`direct`, `theorem`, `equations:rfl`, …; M5). -/
  routes : Std.HashMap Lean.Name String := {}
  /-- Whether the global W check ran (`--strong-only` skips it). -/
  wRun : Bool := true

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

def runW (cfg : Config) : IO (UInt32 × Option WState) := do
  if cfg.receiptsOnly then return ((← runReceiptsOnly cfg), none)
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
  if cfg.strongOnly then
    -- no global W: every constant whose record the reader keeps is offered to S, whose
    -- cones run their own W association (`Strong.runCone`)
    let mut refs : Std.HashMap Lean.Name (Array Lean.Name) := {}
    let mut verdicts : Std.HashMap Lean.Name Verdict := {}
    for n in names do
      let some ci := env.find? n | continue
      refs := refs.insert n (refsOf ci)
      let some addr := namedAddr[n]? | continue
      let some ownerRecord := store[addr]? | continue
      match recordFailures[owner addr ownerRecord]? with
      | some (own, reason) => verdicts := verdicts.insert n (if own then .unsupported reason
          else .unsupported s!"target record blocked by the reader ({reason})")
      | none => verdicts := verdicts.insert n (if kept.contains addr then .certified
          else .unsupported "target record not selected")
    say s!"[certify] strong only: no global W check"
    return (0, some { env, produced, store, names, namedAddr, refs, verdicts, wRun := false })
  -- triage: unsupported source, records not admitted, size budget
  let mut verdicts : Std.HashMap Lean.Name Verdict := {}
  let mut refs : Std.HashMap Lean.Name (Array Lean.Name) := {}
  let mut entries : Std.HashMap Lean.Name MapEntry := {}
  let mut candidates : Array Lean.Name := #[]
  let mut big1M := 0
  let mut big4M := 0
  let mut big16M := 0
  let mut sizeTotal := 0
  let mut sizeRows := "name\tdagNodes\ttreeNodes\n"
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
    -- the size budget first, on the DAG (M5 WP-B): the certified walks visit a shared
    -- subterm once; the tree size is measured (on the DAG) and reported, not budgeted
    let size ← declDagSize ci
    if size ≥ 4096 then
      sizeRows := sizeRows ++ s!"{n}\t{size}\t{declTreeSizeShared ci}\n"
    if size ≥ 1000000 then big1M := big1M + 1
    if size ≥ 4000000 then big4M := big4M + 1
    if size ≥ 16000000 then big16M := big16M + 1
    sizeTotal := sizeTotal + size
    if size ≥ cfg.budget then
      verdicts := verdicts.insert n (.unsupported s!"expression DAG over budget ({cfg.budget} nodes)")
      continue
    if let some feature := unsupportedSourceShared ci then
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
  say s!"[certify] triage: {candidates.size} candidates; {t3 - t2} ms; sizes (distinct Expr objects): \
    total {sizeTotal}, ≥1M {big1M}, ≥4M {big4M}, ≥16M {big16M}"
  IO.FS.writeFile s!"{cfg.out}.sizes.tsv" sizeRows
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
      return (1, none)
  let t4 ← IO.monoMsNow
  say s!"[certify] admission (checkBytes) of {recordBytes.length} records: \
    {artifact.declarations.size} declarations; {t4 - t3} ms"
  let queriesOf := queriesFor env refs
  let makeInput (members : Array Lean.Name) : Input :=
    { toArtifactInput := ai
      source := ⟨members.toList.filterMap env.find?⟩
      roots := members.toList
      map := members.toList.filterMap (entries[·]?) }
  let decline (e : Decline) : String := match e with
    | .sourceDomain => "source domain" | .mapMismatch => "map"
    | .correspondence => "correspondence" | .blockCorrespondence => "blocks"
    | .definitionGroupCorrespondence => "definition groups"
    | .setup r => s!"setup: {r}" | _ => "other"
  -- W+ (M5): the recursors claimed images (untrusted; the map check refuses a wrong claim)
  let images := imageClaims env store names namedAddr
  let imagesFn : Lean.Name → Bool := fun n => images.contains n
  say s!"[certify] image claims: {images.size} recursors whose named record is a definition"
  let mut finalNames := candidates
  let mut routes : Std.HashMap Lean.Name String := {}
  let mut support : Array Kernel.Declaration := #[]
  let mut rowsOf : Std.HashMap Lean.Name (Array Nat) := {}
  let mut proposedRows := 0
  let mut proposedFor := 0
  let mut overBudgetRows := 0
  let mut abandonedRows := 0
  let mut accepted := false
  let mut entryPos : Std.HashMap Kernel.Name Nat := {}
  let mut usedSupport := 0
  if images.isEmpty then
    -- no changed block: W's own decision first (`checkIndexed`, `checkIndexed_sound`)
    let input := makeInput candidates
    let sh := Shared.ofArtifact input artifact
    let hints := buildHints input sh queriesOf cfg.workers
    match checkIndexed input artifact hints with
    | .ok _ =>
      -- `checkIndexed_sound`: every member of `input.source` is certified with W's meaning
      accepted := true
      for n in candidates do routes := routes.insert n "direct/raw"
    | .error e =>
      say s!"[certify] certified check (W) over {candidates.size} candidates refused ({decline e}); \
        {(← IO.monoMsNow) - t4} ms; W+ pre-pass"
  if !accepted then
    let pre ← wPrePass env entries (makeInput candidates) images artifact queriesOf cfg.workers say
      (fun text => IO.FS.writeFile s!"{cfg.out}.rows.tsv" text) (fun _ _ => cfg.rowBudget)
    for (n, r) in pre.routes.toList do routes := routes.insert n r
    for (n, v) in pre.failed.toList do verdicts := verdicts.insert n v
    support := pre.support
    rowsOf := pre.rowsOf
    entryPos := pre.entryPos
    proposedRows := pre.proposedRows
    proposedFor := pre.proposedFor
    overBudgetRows := pre.overBudgetRows
    abandonedRows := pre.abandonedRows
    let survivors := candidates.filter (fun n => !verdicts.contains n)
    let (v2, closed2) := closeCandidates refs verdicts survivors
    verdicts := v2
    finalNames := closed2
    -- the final decision; a support row the certified fold refuses (after an accepting
    -- pre-screen) takes its constant out, and the decision runs again
    let mut attempts := 0
    while !accepted && attempts < 4 do
      attempts := attempts + 1
      let input := makeInput finalNames
      let (sup, owners, rowsFinal) := finalSupport finalNames { support, rowsOf }
      let oldRoutes := finalNames.all fun n => match routes[n]? with
        | some "direct" | some "raw" => true
        | _ => false
      if images.isEmpty && sup.isEmpty && oldRoutes then
        let sh := Shared.ofArtifact input artifact
        let hints := buildHints input sh queriesOf cfg.workers
        match checkIndexed input artifact hints with
        | .ok _ =>
          -- `checkIndexed_sound`: W's meaning, every member of `input.source` certified
          accepted := true
        | .error e =>
          IO.eprintln s!"[certify] the certified check (W) refused the final input ({finalNames.size} \
            declarations): {decline e}"
          return (1, none)
      else
        let shF := SharedW.ofArtifact input imagesFn artifact sup
        let hintsF := buildHintsW input shF entryPos queriesOf cfg.workers
          (rowsAtWith entries entryPos shF.reader rowsFinal shF.entries.size)
        let decision := (Task.spawn (prio := .dedicated) fun _ =>
          checkIndexed' input imagesFn artifact sup hintsF).get
        match decision with
        | .ok _ =>
          -- `checkIndexed'_sound`: every member of `input.source` is certified with W+'s meaning
          accepted := true
          usedSupport := sup.size
        | .error (.fold (.checking err position)) =>
          let prepared := (Kernel.Frontend.preparePrelude artifact.prelude.ix artifact.declarations).size
          let (word, message) := checkOutcome err
          if prepared ≤ position && position - prepared < owners.size then
            let owner := owners[position - prepared]!
            say s!"[certify] the certified fold refused support row {position - prepared} of {owner}: \
              {word}: {oneLine message}; deciding again without it"
            verdicts := verdicts.insert owner
              (.rejected s!"correspondence: equation row refused by the certified fold: {word}: {oneLine message}")
            let (v3, closed3) := closeCandidates refs verdicts (finalNames.filter (· != owner))
            verdicts := v3
            finalNames := closed3
          else
            IO.eprintln s!"[certify] the certified fold refused the artifact and support at {position}: \
              {word}: {oneLine message}"
            return (1, none)
        | .error (.fold (.setup r)) =>
          IO.eprintln s!"[certify] support fold setup: {r}"
          return (1, none)
        | .error (.base e) =>
          IO.eprintln s!"[certify] the certified check (W+) refused the final input ({finalNames.size} \
            declarations): {decline e}"
          return (1, none)
    unless accepted do
      IO.eprintln "[certify] the certified fold kept refusing support rows; giving up"
      return (1, none)
  for n in finalNames do verdicts := verdicts.insert n .certified
  let t9 ← IO.monoMsNow
  let wOnly := usedSupport == 0 && images.isEmpty &&
    routes.toList.all (fun (_, r) => r == "direct" || r == "raw" || r == "direct/raw")
  let mode := if wOnly then "W" else s!"W+, {usedSupport} support rows"
  say s!"[certify] certified check over {finalNames.size} declarations: accepted ({mode}); \
    {t9 - t4} ms since admission"
  -- diagnostics: the export and the reader entries of the requested names, in the
  -- context of all candidates
  unless cfg.explain.isEmpty do
    let inputE := makeInput candidates
    let shE := SharedW.ofArtifact inputE imagesFn artifact #[]
    let entryPosE := entryPositions shE.entries
    let hintsE := buildHintsW inputE shE entryPosE queriesOf cfg.workers (fun _ => [])
    for n in cfg.explain do
      let some ci := env.find? n | say s!"[explain] {n}: not in the environment"
      let cy := shE.small hintsE.toHints n
      let verdictE := verdicts.getD n (.unsupported "none")
      let routeE := match routes[n]? with
        | some r => s!"route {r}"
        | none => ""
      say s!"[explain] {n}: verdict {verdictE.word}; {verdictE.cause}{routeE}; image claim {images.contains n}"
      match directExport cy ci with
      | .error e => say s!"[explain]   export error: {e}"
      | .ok e =>
        say s!"[explain]   export: {repr e.withoutHint}"
        for a in shE.entries do
          if entryName a == entryName e then
            say s!"[explain]   reader: {repr a}"
            let parts : DirectEntry → Option (Kernel.ConstantVal × Option Kernel.Expr)
              | .defn cv v _ | .thm cv v | .opaque cv v => some (cv, some v)
              | .axiom cv | .quot _ cv | .induct cv _ | .ctor cv .. | .recursor cv .. => some (cv, none)
            match parts e.withoutHint, parts a with
            | some (x, xv), some (y, yv) =>
              say s!"[explain]   type: {(firstDiff "type" x.type y.type).getD "equal"}"
              match xv, yv with
              | some u, some v => say s!"[explain]   value: {(firstDiff "value" u v).getD "equal"}"
              | _, _ => pure ()
            | _, _ => pure ()
      if let .inductInfo iv := ci then
        match exportBlock cy iv, cy.name iv.name with
        | .ok b, .ok k =>
          say s!"[explain]   export block: {repr b}"
          match shE.state.indBlocks[k]? with
          | some actual => say s!"[explain]   reader block: {repr (readerBlock actual)}"
          | none => say "[explain]   no reader block"
        | .error e, _ | _, .error e => say s!"[explain]   block export error: {e}"
      -- W+: the type and equation rows and the checker's verdict on each
      match ci with
      | .recInfo _ | .defnInfo _ | .thmInfo _ =>
        let p ← proposeRows env shE hintsE ci
        if let some f := p.failure then say s!"[explain]   rows: {f}"
        let natPins ← IO.ofExcept Ix.Kernel.Reader.builtinNatOpPins
        let base : Benchmarks.Kernel.CheckIxeStep.Checker := { fe := Ix.Kernel.mkFEnv artifact.env }
        let screened := prescreen natPins base (p.rows.map (·.2))
        for ((what, row), verdict) in p.rows.zip screened do
          if let .thmDecl cv _ := row then
            say s!"[explain]   {what} row {kernelNameStr cv.name}: {repr cv.type}"
          say s!"[explain]     checker: {verdict.getD "accepted"}"
        if let .defnInfo d := ci then
          say s!"[explain]   Lean eq_def: {(env.find? (d.name.str "eq_def")).isSome}"
      | _ => pure ()
  -- report: per name, per address, per class; a certified row's cause column is its route
  let mut tsv := "name\taddress\tverdict\tcause\n"
  let mut byWord : Std.HashMap String Nat := {}
  let mut byClass : Std.HashMap (String × String) Nat := {}
  let mut byRoute : Std.HashMap String Nat := {}
  let mut addrVerdict : Std.HashMap Address String := {}
  for n in names do
    let v := verdicts.getD n (.unsupported "no verdict")
    let addr := match namedAddr[n]? with
      | some a => toString a
      | none => ""
    let cause := if v.isCertified then routes.getD n "" else v.cause
    tsv := tsv ++ s!"{n}\t{addr}\t{v.word}\t{cause}\n"
    byWord := byWord.insert v.word (byWord.getD v.word 0 + 1)
    if v.isCertified then byRoute := byRoute.insert cause (byRoute.getD cause 0 + 1)
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
  let routeList := byRoute.toArray.qsort (fun a b => a.2 > b.2 || (a.2 == b.2 && a.1 < b.1))
  for (r, k) in routeList do classText := classText ++ s!"certified\troute: {r}\t{k}\n"
  IO.FS.writeFile s!"{cfg.out}.classes.tsv" classText
  -- the artifact's names with no Lean constant: the canonical `_ix` constants (and any other)
  let hasIxComponent (n : Lean.Name) : Bool :=
    n.components.any fun c => match c with
      | .str _ s => s.startsWith "_ix"
      | _ => false
  let mut ixOnly := 0
  let mut ixOnlyIx := 0
  let mut ixOnlyRows : Array String := #[]
  for (n, named) in produced.named.toList do
    let ln := ixName n
    unless env.contains ln do
      ixOnly := ixOnly + 1
      let ix := hasIxComponent ln
      if ix then ixOnlyIx := ixOnlyIx + 1
      ixOnlyRows := ixOnlyRows.push s!"{ln}\t{named.addr}\t{if ix then "_ix" else "other"}"
  IO.FS.writeFile s!"{cfg.out}.ixonly.tsv"
    ("name\taddress\tkind\n" ++ String.join ((ixOnlyRows.qsort (· < ·)).toList.map (· ++ "\n")))
  say s!"[certify] W+: image claims {images.size}; equation rows proposed {proposedRows} for {proposedFor} \
    constants, folded {usedSupport}, over the pre-screen time budget {overBudgetRows} ({abandonedRows} left running); routes {String.intercalate ", " (routeList.toList.map fun (r, k) => s!"{r}={k}")}; \
    artifact names with no Lean constant {ixOnly} ({ixOnlyIx} with an `_ix` component)"
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
    ("routes", Lean.Json.mkObj (routeList.toList.map fun (r, k) => (r, Lean.toJson k))),
    ("imageClaims", Lean.toJson images.size),
    ("equationRows", Lean.Json.mkObj [("proposed", Lean.toJson proposedRows),
      ("proposedFor", Lean.toJson proposedFor), ("folded", Lean.toJson usedSupport),
      ("overBudget", Lean.toJson overBudgetRows), ("leftRunning", Lean.toJson abandonedRows),
      ("rowBudgetMs", Lean.toJson cfg.rowBudget)]),
    ("ixOnly", Lean.Json.mkObj [("total", Lean.toJson ixOnly), ("withIxComponent", Lean.toJson ixOnlyIx)]),
    ("rawProjections", projJson), ("projectionReceipts", receiptJson)]
  IO.FS.writeFile s!"{cfg.out}.json" json.pretty
  let counts := " ".intercalate (words.toList.map fun w => s!"{w}={byWord.getD w 0}")
  let addrCounts := " ".intercalate (words.toList.map fun w => s!"{w}={byAddr.getD w 0}")
  say s!"[certify] per name: {counts}; per address: {addrCounts}; total {(← IO.monoMsNow) - t0} ms"
  let w : WState := { env, produced, store, names, namedAddr, refs, verdicts, routes }
  if byWord.getD "certified" 0 == 0 then
    IO.eprintln "[certify] FAIL: nothing certified"
    return (1, some w)
  if byWord.getD "rejected" 0 != 0 then
    IO.eprintln s!"[certify] FAIL: {byWord.getD "rejected" 0} rejected"
    return (1, some w)
  if receiptRefused != 0 then
    IO.eprintln s!"[certify] FAIL: {receiptRefused} constants with a raw projection on a non-direct structure-like have no accepted receipt"
    return (1, some w)
  return (0, some w)

def run (cfg : Config) : IO UInt32 := do
  return (← runW cfg).1

end Ix.CompileCert.Certifier
