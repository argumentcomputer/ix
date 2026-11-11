import IxCC.Recheck.Produce
import IxCC.Ixon.V3.Tc.Driver
import IxCC.Src.Relevance.Annotate
import IxCC.Recheck.Json

/-! # The front end over the kernel, against the erased checker's parts

Since the switch the front end over the certified kernel is the only one
(`Recheck.ingress`: the kernel's acceptance; `Recheck.produce`: its annotator;
`Recheck.checkCanonicalRelevance`: Stage A over it). Until the erased checker
and the earlier annotator are deleted, this compares, for one closure and its
sidecar, what each of them would have decided:

* **acceptance**: the erased checker's `Tc.checkEnv` against the kernel's
  acceptance (`KernelFront.accept`), each with its reason;
* **the program**: the earlier reading (`Src.Ingress.ofEnv`, its pins from
  IxCC's binding decoder) against ingress's (`Src.Ingress.readConsts` with the
  pins of the kernel's admitted table): the pins, their resolution, the roots,
  the resource context and every constant's identity;
* **the annotation**: per root, the earlier annotator's output
  (`Src.Relevance.annotate`) against the kernel annotator's, exactly, and up to
  the order of the parameters in a zero condition;
* **downstream**: the root produced, Stage A on its own certificate, and
  `Recheck.run`'s object.

Times are wall-clock milliseconds of each phase in this process. -/
namespace IxCCTests.KernelFront

open IxCC IxCC.Src
open IxCC.Src.Relevance
open Lean (Json)

/-- A zero condition with its parameters sorted and deduplicated. -/
def normWhen : PropWhen → PropWhen
  | .never => .never
  | .allZero ps => .allZero (ps.eraseDups.mergeSort (· ≤ ·))

def normRel : Rel → Rel
  | .proof w => .proof (normWhen w)
  | r => r

def normTag : Tag → Tag
  | .lam r pw => .lam (normRel r) (normWhen pw)
  | .arg r => .arg (normRel r)
  | .letE r => .letE (normRel r)

def normField : FieldClass → FieldClass
  | .proof w => .proof (normWhen w)
  | f => f

/-- An annotation with every zero condition's parameters sorted. -/
def normAnn (a : Ann) : Ann :=
  { consts := a.consts.map fun r => { result := normRel r.result, params := r.params.map normRel }
    ctors := a.ctors.map fun r => { fields := r.fields.map normField }
    nodes := a.nodes.map fun (k, ts) => (k, ts.map normTag) }

def tagStr (t : Tag) : String := toString (repr t)

/-- The differences between two annotations, at most `limit` of them. -/
def annDiffs (size : Nat) (old new : Ann) (limit : Nat := 12) : Array String := Id.run do
  let mut out : Array String := #[]
  for c in [0:size] do
    if out.size ≥ limit then break
    let o := old.constRel? c
    let n := new.constRel? c
    if o != n then out := out.push s!"constant {c}: {repr o} / {repr n}"
    let o := old.ctorRel? c
    let n := new.ctorRel? c
    if o != n then out := out.push s!"constructor {c}: {repr o} / {repr n}"
  if old.nodes.length != new.nodes.length then
    out := out.push s!"{old.nodes.length} runtime terms / {new.nodes.length}"
  for ((ko, to), (kn, tn)) in old.nodes.zip new.nodes do
    if out.size ≥ limit then break
    if ko != kn then
      out := out.push s!"term {repr ko} / {repr kn}"
    else if to != tn then
      let i := ((to.zip tn).findIdx? fun (x, y) => x != y).getD (min to.length tn.length)
      out := out.push s!"{repr ko}, tag {i} of {to.length}/{tn.length}: \
        {(to[i]?.map tagStr).getD "-"} / {(tn[i]?.map tagStr).getD "-"}"
  return out

/-- What one root compiled to. -/
structure RootRun where
  ann : Option Ann := none
  cert : Option String := none
  object : Option ByteArray := none
  error : Option String := none
  produceMs : Nat := 0
  runMs : Nat := 0
  stageA : Option Bool := none

def ms (t0 : Nat) : IO Nat := return (← IO.monoMsNow) - t0

/-- One root's input, from an input that holds every sidecar root. -/
def restrict (inp : Recheck.Input) (i : Nat) : Recheck.Input :=
  { inp with
    hints := { inp.hints with roots := (inp.hints.roots[i]?).toArray }
    program := { inp.program with roots := (inp.program.roots[i]?).toList }
    names := (inp.names[i]?).toList }

/-- The producer, Stage A on its certificate, and `Recheck.run`. -/
def runNew (cfg : Recheck.Config) (inp : Recheck.Input) : IO RootRun := do
  let t0 ← IO.monoMsNow
  match ← IO.lazyPure fun _ => Recheck.produceWith cfg inp with
  | .error e => return { error := some e.render, produceMs := ← ms t0 }
  | .ok pr =>
    let produceMs ← ms t0
    let stageA ← IO.lazyPure fun _ => Recheck.checkCanonicalRelevance cfg inp pr.cert.table pr.cert.relevance
    let t1 ← IO.monoMsNow
    match ← IO.lazyPure fun _ => IxCC.Recheck.run cfg inp.program pr.cert with
    | .error e => return { ann := some pr.cert.relevance, cert := some pr.cert.toText,
                           error := some e.render, produceMs, runMs := ← ms t1, stageA }
    | .ok a => return { ann := some pr.cert.relevance, cert := some pr.cert.toText,
                        object := some a.object, produceMs, runMs := ← ms t1, stageA }

/-- The earlier front end's reading of the same bytes: IxCC's ingress with the
pins its own binding decoder reads (`Src.Ingress.ofEnv`), every sidecar root. -/
def oldProgram (env : Ixon.V3.Env) (sidecar : Json) : Except String Src.Program := do
  let hints ← Src.Hints.ofK1Json sidecar
  let p ← Src.Ingress.ofEnv env (hints.roots.map (·.1))
  pure { p with known := Src.Pinned.known p, resource := hints.resource }

/-- What each reading adds agrees: the pins, their resolution, the roots and
the resource context, and each constant's identity and kind. The constants'
declarations and terms come from the same conversion of the same
environment. -/
def sameProgram (o n : Src.Program) : List String := Id.run do
  let mut out := []
  if o.size != n.size then out := out ++ [s!"{o.size} constants / {n.size}"]
  if o.roots != n.roots then out := out ++ ["the roots differ"]
  if toString (repr o.known) != toString (repr n.known) then
    out := out ++ [s!"pins or pinned identities differ: {repr o.known} / {repr n.known}"]
  if o.resource.isSome != n.resource.isSome then out := out ++ ["the resource contexts differ"]
  for c in [0:o.size] do
    if o.addr c != n.addr c || toString (repr (o.cref c)) != toString (repr (n.cref c)) ||
        ((o.decl? c).map (·.kindName)) != ((n.decl? c).map (·.kindName)) then
      out := out ++ [s!"constant {c} differs"]
      break
  return out

/-- The report for one closure. -/
structure Report where
  name : String
  bytes : Nat
  bound : Bool
  records : Nat := 0
  oldAccept : String := ""
  newAccept : String := ""
  oldTypingMs : Nat := 0
  newIngressMs : Nat := 0
  newAcceptMs : Nat := 0
  program : List String := []
  roots : Array Json := #[]
  findings : Array String := #[]

def Report.toJson (r : Report) : Json :=
  Json.mkObj [("name", Lean.toJson (r.name)), ("bytes", Lean.toJson (r.bytes)), ("bound", Lean.toJson (r.bound)), ("records", Lean.toJson (r.records)),
    ("old_accept", Lean.toJson (r.oldAccept)), ("new_accept", Lean.toJson (r.newAccept)),
    ("old_typing_ms", Lean.toJson (r.oldTypingMs)),
    ("new_ingress_ms", Lean.toJson (r.newIngressMs)), ("new_accept_ms", Lean.toJson (r.newAcceptMs)),
    ("program", Lean.toJson r.program), ("roots", Json.arr r.roots),
    ("findings", Lean.toJson r.findings)]

/-- The comparison on one closure, every sidecar root. -/
def diff (name : String) (bytes : ByteArray) (sidecar : Json) : IO Report := do
  let env? := Ixon.V3.decodeAnonymousEnv bytes
  let bound := match env? with | .ok e => e.isBound | .error _ => false
  let records := match env? with | .ok e => e.consts.size | .error _ => 0
  let mut r : Report := { name, bytes := bytes.size, bound, records }
  -- the erased checker's acceptance, alone
  let t0 ← IO.monoMsNow
  let oldAccept ← IO.lazyPure fun _ => match env? with
    | .ok e => match Ixon.V3.Tc.checkEnv e with
      | .ok () => "accepted"
      | .error m => s!"refused: {m}"
    | .error m => s!"undecodable: {m}"
  r := { r with oldAccept, oldTypingMs := ← ms t0 }
  -- the kernel's acceptance, alone
  let t0 ← IO.monoMsNow
  let newAccept ← IO.lazyPure fun _ => match env? with
    | .ok e => match KernelFront.accept e with
      | .ok a => s!"accepted ({a.decls.size} declarations, {a.env.consts.length} constants)"
      | .error m => s!"refused: {m.render}"
    | .error m => s!"undecodable: {m}"
  r := { r with newAccept, newAcceptMs := ← ms t0 }
  -- ingress, every root
  let t0 ← IO.monoMsNow
  let new ← IO.lazyPure fun _ => Recheck.ingress bytes sidecar []
  r := { r with newIngressMs := ← ms t0 }
  match new with
  | .error e => return { r with findings := r.findings.push s!"new ingress: {e.render}" }
  | .ok inp =>
    match oldProgram inp.env sidecar with
    | .error e => r := { r with findings := r.findings.push s!"old reading: {e}" }
    | .ok op => r := { r with program := sameProgram op inp.program }
    for i in [0:inp.names.length] do
      let name := inp.names[i]!
      let cfg : Recheck.Config := { names := [name] }
      let ki := restrict inp i
      -- the two annotators directly, on the program with the producer's table
      -- (before the admission policy, which may decline the root)
      let (table, _, _) := Src.Table.build cfg.table ki.program ki.hints.proposals
      let p0 := { ki.program with table }
      let t0 ← IO.monoMsNow
      let oa ← IO.lazyPure fun _ => Src.Relevance.annotate ki.env p0
      let oldAnnotateMs ← ms t0
      let t0 ← IO.monoMsNow
      let na ← IO.lazyPure fun _ => ki.kernel.annotateChecked p0
      let newAnnotateMs ← ms t0
      let (annSame, annNorm, diffs, annErrors) := match oa, na with
        | .ok a, .ok b =>
          (a == b, (normAnn a).eqb (normAnn b), if a == b then #[] else annDiffs inp.program.size a b, "")
        | .error x, .error y => (x == y, false, #[], s!"both annotators refused: {x} / {y}")
        | .error x, .ok _ => (false, false, #[], s!"old annotator refused: {x}")
        | .ok _, .error y => (false, false, #[], s!"kernel annotator refused: {y}")
      let n ← runNew cfg ki
      unless (annSame || annErrors.startsWith "both") && (n.object.isNone || n.stageA == some true) do
        r := { r with findings := r.findings.push s!"root {name}: annotation {annSame} \
          (up to parameter order {annNorm}) {annErrors} {diffs}, stage A {n.stageA}; error {n.error}" }
      r := { r with roots := r.roots.push (Json.mkObj [
        ("root", Lean.toJson (name)), ("annotation_same", Lean.toJson (annSame)), ("annotation_same_up_to_order", Lean.toJson (annNorm)),
        ("annotation_diffs", Lean.toJson diffs), ("annotation_errors", Lean.toJson annErrors),
        ("old_annotate_ms", Lean.toJson oldAnnotateMs), ("new_annotate_ms", Lean.toJson newAnnotateMs),
        ("object_bytes", Lean.toJson ((n.object.map (·.size)).getD 0)),
        ("stage_a", Lean.toJson n.stageA), ("error", Lean.toJson n.error),
        ("produce_ms", Lean.toJson (n.produceMs)), ("run_ms", Lean.toJson (n.runMs))]) }
    return r

/-- The front end alone on one closure (for timing and peak memory in a
process of its own): ingress, then every root produced and run. -/
def single (bytes : ByteArray) (sidecar : Json) : IO Json := do
  let t0 ← IO.monoMsNow
  match ← IO.lazyPure fun _ => Recheck.ingress bytes sidecar [] with
  | .error e => return Json.mkObj [("error", Lean.toJson (e.render)), ("ingress_ms", Lean.toJson (← ms t0))]
  | .ok inp =>
    let ingressMs ← ms t0
    let mut out := #[]
    for i in [0:inp.names.length] do
      let n ← runNew { names := (inp.names[i]?).toList } (restrict inp i)
      out := out.push (Json.mkObj [("root", Lean.toJson ((inp.names[i]?).getD "")), ("error", Lean.toJson n.error),
        ("produce_ms", Lean.toJson (n.produceMs)), ("run_ms", Lean.toJson (n.runMs)), ("stage_a", Lean.toJson n.stageA)])
    return Json.mkObj [("ingress_ms", Lean.toJson (ingressMs)), ("roots", Json.arr out)]

end IxCCTests.KernelFront

namespace IxCCTests.KernelFront

open IxCC

/-- One front end's acceptance alone (the erased checker's `Tc.checkEnv`, or
the kernel's `accept`), for its time on a closure that may take long. -/
def acceptOnly (front : String) (bytes : ByteArray) : IO Lean.Json := do
  let env ← IO.ofExcept (Ixon.V3.decodeAnonymousEnv bytes)
  let t0 ← IO.monoMsNow
  let verdict ← IO.lazyPure fun _ => match front with
    | "old" =>
      match Ixon.V3.Tc.checkEnv env with
      | .ok () => "accepted"
      | .error m => s!"refused: {m}"
    -- the kernel's logical entry alone, on the same prepared inputs: it declines
    -- every tier record (`partial` and `unsafe` definitions)
    | "logical" =>
      match Src.KernelFront.prepare env Src.KernelFront.defaultLimits with
      | .error m => s!"refused: {m.render}"
      | .ok p =>
        match Ix.Kernel.Admission.checkBytesWith Src.KernelFront.hash p.binding p.pre
            Src.KernelFront.defaultLimits p.records (Src.KernelFront.blobsOf env) with
        | .ok e => s!"accepted ({e.consts.length} constants)"
        | .error e => s!"refused: {e}"
    -- the tiered entry behind the committed prelude (`checkBytesTiered`)
    | "committed" =>
      match Src.KernelFront.prepare env Src.KernelFront.defaultLimits with
      | .error m => s!"refused: {m.render}"
      | .ok p =>
        match Ix.Kernel.Admission.checkBytesTiered Src.KernelFront.hash p.binding
            Src.KernelFront.defaultLimits p.records (Src.KernelFront.blobsOf env) with
        | .ok (e, _) => s!"accepted ({e.consts.length} constants)"
        | .error e => s!"refused: {e}"
    | _ =>
      match Src.KernelFront.accept env with
      | .ok a => s!"accepted ({a.decls.size} declarations, {a.tier.length} tier constants)"
      | .error m => s!"refused: {m.render}"
  let t := (← IO.monoMsNow) - t0
  return Lean.Json.mkObj [("front", Lean.toJson front), ("records", Lean.toJson env.consts.size),
    ("verdict", Lean.toJson verdict), ("ms", Lean.toJson t)]

end IxCCTests.KernelFront
