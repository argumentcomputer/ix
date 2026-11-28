import IxCC.Recheck.Produce
import IxCC.Recheck.Json

/-! # The front end over the kernel on one closure

The front end over the certified kernel is IxCC's only one
(`Recheck.ingress`: the kernel's acceptance; `Recheck.produce`: its annotator;
`Recheck.checkCanonicalRelevance`: Stage A over it). For one closure and its
sidecar this reports:

* **acceptance**: the kernel's (`KernelFront.accept`), alone, with its reason;
* **ingress**, every sidecar root;
* **each root**: the root produced, Stage A on its own certificate, and
  `Recheck.run`'s object.

Until the switch's step 4 this also ran the erased checker, the earlier
reading and the earlier annotator on the same bytes and compared them with
these; they agreed on every committed closure they could read, and were
deleted. Times are wall-clock milliseconds of each phase in this process. -/
namespace IxCCTests.KernelFront

open IxCC IxCC.Src
open IxCC.Src.Relevance
open Lean (Json)

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
def runRoot (cfg : Recheck.Config) (inp : Recheck.Input) : IO RootRun := do
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

/-- The report for one closure. -/
structure Report where
  name : String
  bytes : Nat
  bound : Bool
  records : Nat := 0
  accept : String := ""
  ingressMs : Nat := 0
  acceptMs : Nat := 0
  roots : Array Json := #[]
  findings : Array String := #[]

def Report.toJson (r : Report) : Json :=
  Json.mkObj [("name", Lean.toJson (r.name)), ("bytes", Lean.toJson (r.bytes)), ("bound", Lean.toJson (r.bound)), ("records", Lean.toJson (r.records)),
    ("accept", Lean.toJson (r.accept)),
    ("ingress_ms", Lean.toJson (r.ingressMs)), ("accept_ms", Lean.toJson (r.acceptMs)),
    ("roots", Json.arr r.roots), ("findings", Lean.toJson r.findings)]

/-- The front end on one closure, every sidecar root: a finding for an ingress
refusal and for each root whose certificate Stage A refuses. -/
def report (name : String) (bytes : ByteArray) (sidecar : Json) : IO Report := do
  let env? := Ixon.V3.decodeAnonymousEnv bytes
  let bound := match env? with | .ok e => e.isBound | .error _ => false
  let records := match env? with | .ok e => e.consts.size | .error _ => 0
  let mut r : Report := { name, bytes := bytes.size, bound, records }
  -- the kernel's acceptance, alone
  let t0 ← IO.monoMsNow
  let accept ← IO.lazyPure fun _ => match env? with
    | .ok e => match KernelFront.accept e with
      | .ok a => s!"accepted ({a.decls.size} declarations, {a.env.consts.length} constants)"
      | .error m => s!"refused: {m.render}"
    | .error m => s!"undecodable: {m}"
  r := { r with accept, acceptMs := ← ms t0 }
  -- ingress, every root
  let t0 ← IO.monoMsNow
  let inp? ← IO.lazyPure fun _ => Recheck.ingress bytes sidecar []
  r := { r with ingressMs := ← ms t0 }
  match inp? with
  | .error e => return { r with findings := r.findings.push s!"ingress: {e.render}" }
  | .ok inp =>
    for i in [0:inp.names.length] do
      let name := inp.names[i]!
      let n ← runRoot { names := [name] } (restrict inp i)
      unless n.object.isNone || n.stageA == some true do
        r := { r with findings := r.findings.push s!"root {name}: stage A {n.stageA}; error {n.error}" }
      r := { r with roots := r.roots.push (Json.mkObj [
        ("root", Lean.toJson (name)),
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
      let n ← runRoot { names := (inp.names[i]?).toList } (restrict inp i)
      out := out.push (Json.mkObj [("root", Lean.toJson ((inp.names[i]?).getD "")), ("error", Lean.toJson n.error),
        ("produce_ms", Lean.toJson (n.produceMs)), ("run_ms", Lean.toJson (n.runMs)), ("stage_a", Lean.toJson n.stageA)])
    return Json.mkObj [("ingress_ms", Lean.toJson (ingressMs)), ("roots", Json.arr out)]

end IxCCTests.KernelFront

namespace IxCCTests.KernelFront

open IxCC

/-- One acceptance alone (the kernel front end's `accept`, the kernel's
logical entry, or its tiered entry behind the committed prelude), for its time
on a closure that may take long. -/
def acceptOnly (front : String) (bytes : ByteArray) : IO Lean.Json := do
  let env ← IO.ofExcept (Ixon.V3.decodeAnonymousEnv bytes)
  let t0 ← IO.monoMsNow
  let verdict ← IO.lazyPure fun _ => match front with
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
