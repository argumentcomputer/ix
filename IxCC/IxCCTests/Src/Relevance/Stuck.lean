import IxCCTests.Src.StuckEval
import IxCC.Src.Load
import Lean.Data.Json

/-! The stuck-cause census (D18).

For each pack (`k1.ixe`, the five bench-k1 closures and the sort-polymorphism
fixture `src-sortpoly`) it runs two sets of roots through SrcEval and through
the instrumented `StuckEval`, requires the same outcome from both, and
classifies every `stuck` run by cause (relevance, missing primitive, declined
form, other):

* **roots**: the pack's own roots on small arguments;
* **first-order constants**: every constant of the closure with no universe
  parameters whose type is `Nat → … → Nat` or `… → Bool` (at most three
  arguments) over the pinned `Nat` and `Bool`, run as an extra root on small
  arguments.

The annotation comes from the default annotator. The relevance checker's
verdict is recorded but does not gate the runs: a rejected annotation is
installed and lazified anyway, so its runs show what the checker prevents.
`Admit` is not run, because SrcEval is stuck on everything it rejects and
those runs are what the census classifies. -/

namespace IxCCTests.Src.Relevance.Stuck

open IxCC IxCC.Src IxCC.Src.Relevance IxCCTests.Src
open IxCCTests.Src.StuckEval (Cause Stop Out)
open Lean (Json toJson)

/-- Counts per outcome and per stuck cause. -/
structure Tally where
  runs : Nat := 0
  ok : Nat := 0
  timeout : Nat := 0
  trap : Nat := 0
  stuck : Array (String × Nat) := #[]
  /-- Stuck runs by cause, with one example each. -/
  causes : Array (String × Nat × String) := #[]
  deriving Inhabited

namespace Tally

def bump (xs : Array (String × Nat)) (k : String) : Array (String × Nat) :=
  match xs.findIdx? (·.1 == k) with
  | some i => xs.modify i fun (k, n) => (k, n + 1)
  | none => xs.push (k, 1)

def add (t : Tally) (label : String) : Out Value → Tally
  | .ok _ => { t with runs := t.runs + 1, ok := t.ok + 1 }
  | .error .timeout => { t with runs := t.runs + 1, timeout := t.timeout + 1 }
  | .error .trap => { t with runs := t.runs + 1, trap := t.trap + 1 }
  | .error (.stuck c) =>
    let causes := match t.causes.findIdx? (·.1 == c.name) with
      | some i => t.causes.modify i fun (k, n, ex) => (k, n + 1, ex)
      | none => t.causes.push (c.name, 1, label)
    { t with runs := t.runs + 1, stuck := bump t.stuck c.group, causes }

def stuckIn (t : Tally) (group : String) : Nat :=
  ((t.stuck.find? (·.1 == group)).map (·.2)).getD 0

def stuckTotal (t : Tally) : Nat := t.stuck.foldl (· + ·.2) 0

def render (t : Tally) : String :=
  let groups := ["relevance", "missing primitive", "declined form", "other"].map fun g =>
    s!"{g} {t.stuckIn g}"
  s!"{t.runs} runs: ok {t.ok}, timeout {t.timeout}, trap {t.trap}, stuck {t.stuckTotal} " ++
    s!"({String.intercalate ", " groups})"

def json (t : Tally) : Json :=
  Json.mkObj [("runs", toJson t.runs), ("ok", toJson t.ok), ("timeout", toJson t.timeout),
    ("trap", toJson t.trap),
    ("stuck", Json.mkObj (["relevance", "missing primitive", "declined form", "other"].map fun g =>
      (g, toJson (t.stuckIn g)))),
    ("causes", Json.arr (t.causes.map fun (k, n, ex) =>
      Json.mkObj [("cause", toJson k), ("runs", toJson n), ("example", toJson ex)]))]

end Tally

/-- One census pack: a closure, its sidecar and the arguments of its roots
(`none`: the root is not a first-order function; it is skipped). -/
structure Pack where
  name : String
  ixe : System.FilePath
  equations : System.FilePath
  args : String → List (List Nat)

/-- Small arguments by root sidecar name. -/
def rootArgs : String → List (List Nat)
  | "K1.fib" => [[0], [1], [10]]
  | "K1.sumLoop" => [[0], [20]]
  | "K1.ack" => [[0, 0], [2, 2]]
  | "K1.tak" => [[6, 4, 2, 1]]
  | "K1.gcd" => [[30, 12], [0, 5]]
  | "entry" => []
  | _ => [[0], [3]]

def benchArgs : String → List (List Nat)
  | "fib" => [[10]]
  | "sum-loop" => [[20]]
  | "ackermann" => [[2, 2]]
  | "tak" => [[6, 4, 2, 1]]
  | "gcd" => [[30, 12]]
  | _ => []

def benchPack (n : String) : Pack :=
  { name := n, ixe := fixtures / "bench-k1" / s!"{n}.ixe",
    equations := fixtures / "bench-k1" / s!"{n}.equations.json", args := fun _ => benchArgs n }

def packs : List Pack :=
  [{ name := "k1", ixe := fixtures / "k1/k1.ixe", equations := fixtures / "k1/equations.json",
     args := rootArgs }] ++
  benchNames.map benchPack ++
  [{ name := "sortpoly", ixe := fixtures / "src-sortpoly/sortpoly.ixe",
     equations := fixtures / "src-sortpoly/sortpoly.equations.json", args := rootArgs }]

/-- `Nat → … → Nat` or `… → Bool` over the pinned types: the arity. -/
def firstOrderArity (p : Program) (t : Term) : Option Nat := do
  let nat ← p.known.nat
  let bool := p.known.bool
  let (binders, result) := t.pis
  unless binders.length ≥ 1 && binders.length ≤ 3 do none
  unless binders.all (fun (_, d) => d == .const nat []) do none
  match result with
  | .const r [] => if r == nat || some r == bool then some binders.length else none
  | _ => none

/-- Every argument tuple of the given arity over `{0, 1, 2}` (larger values
make closure functions such as `K1.ack` astronomically slow). -/
def smallTuples : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 => (smallTuples n).flatMap fun xs => [0, 1, 2].map (· :: xs)

/-- Constants of the whole closure run as first-order roots. -/
def firstOrderConsts (p : Program) : Array (CId × Nat) :=
  (Array.range p.size).filterMap fun c =>
    match p.decl? c with
    | some (.defn .defn .safe 0 ty _) => (firstOrderArity p ty).map (c, ·)
    | _ => none

def clock : Nat := 10000

/-- What level-exact relevance changes in a closure (D18): positions whose
class is a proof under a proper universe condition (neither never nor
always), and the instances the checker reaches. -/
structure LevelStats where
  condTags : Nat := 0
  tags : Nat := 0
  condParams : Nat := 0
  condFields : Nat := 0
  condRecKinds : Nat := 0
  instances : Nat := 0
  constants : Nat := 0
  splits : Nat := 0

def isCond (w : PropWhen) : Bool :=
  match w with
  | .allZero (_ :: _) => true
  | _ => false

def LevelStats.render (s : LevelStats) : String :=
  s!"level-exact: {s.condTags} of {s.tags} tags conditional, {s.condParams} conditional parameter \
    classes, {s.condFields} conditional field classes, {s.condRecKinds} conditional recursor kinds; \
    {s.instances} instances of {s.constants} constants, {s.splits} at two or more profiles"

def LevelStats.json (s : LevelStats) : Json :=
  Json.mkObj [("conditional_tags", toJson s.condTags), ("tags", toJson s.tags),
    ("conditional_params", toJson s.condParams), ("conditional_fields", toJson s.condFields),
    ("conditional_rec_kinds", toJson s.condRecKinds), ("instances", toJson s.instances),
    ("constants", toJson s.constants), ("profile_split", toJson s.splits)]

def levelStats (p : Program) (ann : Ann) (ch : Checked) : LevelStats :=
  let tags := ann.nodes.foldl (fun acc (_, ts) => acc ++ ts) ([] : List Tag)
  let tagCond : Tag → Bool
    | .lam r pw => isCond r.irrWhen || isCond pw
    | .arg r | .letE r => isCond r.irrWhen
  let params := ch.reached.foldl (fun n c => match ann.constRel? c with
    | some rel => n + (rel.params.filter (isCond ·.irrWhen)).length
    | none => n) 0
  let fields := ann.ctors.toList.foldl (fun n (_, rel) =>
    n + (rel.fields.filter (isCond ·.dropWhen)).length) 0
  let recKinds := ch.reached.foldl (fun n c => match p.table.recKindOf c with
    | some (.subsingleton w _) => if isCond w then n + 1 else n
    | _ => n) 0
  { condTags := (tags.filter tagCond).length, tags := tags.length, condParams := params
    condFields := fields, condRecKinds := recKinds, instances := ch.instances.length
    constants := ch.reached.length, splits := ch.profileSplit.length }

/-- What happened to one pack's annotation. -/
structure Verdict where
  checker : String
  roots : Tally := {}
  firstOrder : Tally := {}
  firstOrderConsts : Nat := 0
  level : LevelStats := {}

/-- Annotate, install, check (recording the verdict) and lazify `p`. -/
def prepareRuns (env : IxCC.Ixon.V3.Env) (p : Program) : Except String (Program × String) := do
  let ann ← annotate env p
  let pI ← install p ann
  let verdict := match check pI ann with
    | .ok _ => "accepted"
    | .error es => s!"rejected {(es.toList.map (·.rule)).eraseDups}"
  return (Lazify.run pI (ann.nodes.map (·.1)), verdict)

/-- Run one root on each argument tuple through both evaluators. -/
def runRoot (a : Assert) (p : Program) (root : CId) (label : String) (argss : List (List Nat))
    (t : Tally) : IO Tally := do
  let mut t := t
  for args in argss do
    let xs := args.map Value.lit
    let r := Src.run p clock root xs
    let s := StuckEval.run p clock root xs
    expect a (outcome r == s.outcome)
      s!"stuck census: {label} {args}: SrcEval {outcome r}, StuckEval {s.outcome}"
    t := t.add s!"{label} {args}" s
  return t

def names (h : Hints) (p : Program) (c : CId) : String :=
  (Loaded.names h (p.addr c)).getD (p.short c)

def censusPack (a : Assert) (pack : Pack) : IO Verdict := do
  let bytes ← IO.FS.readBinFile pack.ixe
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile pack.equations))
  let hints ← IO.ofExcept (Hints.ofK1Json json)
  let env ← IO.ofExcept (IxCC.Ixon.V3.decodeAnonymousEnv bytes)
  let (p0, _, _) ← IO.ofExcept ((prepare { typecheck := false } env hints).mapError toString)
  -- The pack's own roots, each prepared alone, so that one rejected root does
  -- not hide the others.
  let mut v : Verdict := { checker := "" }
  let mut verdicts : Array String := #[]
  let mut accepted : Array (IxCC.Ixon.Address × CId) := #[]
  for (addr, c) in p0.roots do
    let label := (Loaded.names hints addr).getD (p0.short c)
    let argss := pack.args label
    if argss.isEmpty then continue
    let (p, verdict) ← IO.ofExcept (prepareRuns env { p0 with roots := [(addr, c)] })
    if verdict == "accepted" then accepted := accepted.push (addr, c)
    else verdicts := verdicts.push s!"{label}: {verdict}"
    v := { v with roots := ← runRoot a p c label argss v.roots }
  -- First-order constants of the closure, as extra roots.
  let fo := firstOrderConsts p0
  let extra := fo.map fun (c, _) => (p0.addr c, c)
  let (p, verdict) ← IO.ofExcept (prepareRuns env { p0 with roots := p0.roots ++ extra.toList })
  unless verdict == "accepted" do verdicts := verdicts.push s!"first-order roots: {verdict}"
  let mut t : Tally := {}
  for (c, arity) in fo do
    t ← runRoot a p c (names hints p c) (smallTuples arity) t
  let checker := if verdicts.isEmpty then "accepted" else String.intercalate "; " verdicts.toList
  -- Level-exact statistics of the closure of the roots the checker accepts.
  let pa := { p0 with roots := accepted.toList }
  let ann ← IO.ofExcept (annotate env pa)
  let pI ← IO.ofExcept (install pa ann)
  let level := match check pI ann with
    | .ok ch => levelStats pI ann ch
    | .error _ => {}
  return { v with firstOrder := t, firstOrderConsts := fo.size, checker, level }

def run (a : Assert) (reportPath : Option System.FilePath) : IO (Array String) := do
  let mut out := #[]
  let mut rows : Array (String × Json) := #[]
  for pack in packs do
    let v ← censusPack a pack
    out := out.push s!"{pack.name}: checker {v.checker}"
    out := out.push s!"  roots: {v.roots.render}"
    out := out.push s!"  {v.firstOrderConsts} first-order constants: {v.firstOrder.render}"
    out := out.push s!"  {v.level.render}"
    for (k, n, ex) in v.roots.causes ++ v.firstOrder.causes do
      out := out.push s!"    {n} × {k} (e.g. {ex})"
    rows := rows.push (pack.name, Json.mkObj [("checker", toJson v.checker),
      ("roots", v.roots.json), ("first_order_constants", toJson v.firstOrderConsts),
      ("first_order", v.firstOrder.json), ("level_exact", v.level.json)])
  if let some path := reportPath then
    IO.FS.writeFile path ((Json.mkObj rows.toList).pretty ++ "\n")
    out := out.push s!"stuck census written to {path}"
  return out

end IxCCTests.Src.Relevance.Stuck
