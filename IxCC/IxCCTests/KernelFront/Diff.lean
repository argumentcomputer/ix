import IxCC.Src.KernelFront.Front
import IxCC.Ixon.V3.Tc.Driver
import IxCC.Recheck.Json

/-! # The two front ends, side by side

For one closure and its sidecar: the front end over IxCC's erased type checker
(`Recheck.ingress` with typing, `Recheck.produce`) and the front end over the
certified kernel (`Src.KernelFront.ingress`, `Src.KernelFront.produce`), each
followed by `Recheck.run`, compared:

* **acceptance**: the erased checker's `Tc.checkEnv` against the kernel's
  acceptance (`KernelFront.accept`), each with its reason;
* **the program**: both are `Src.Ingress.readConsts` of the same decoded
  environment for the same roots, so their constants, declarations and terms
  are the same by construction; what is compared is what each front end adds:
  the pins (IxCC's binding decoder against the kernel's admitted table), their
  resolution, the roots and the resource context, and every constant's
  identity;
* **the annotation**: per root, the two annotators' outputs, exactly, and up
  to the order of the parameters in a zero condition (the one representation
  choice a level's form can move);
* **downstream**: the certificate each producer makes (its JSON text) and the
  object `Recheck.run` makes from it, byte for byte, and the kernel front end's
  Stage A on its own certificate.

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

/-- What one root compiled to on one front end. -/
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

def runOld (cfg : Recheck.Config) (inp : Recheck.Input) : IO RootRun := do
  let t0 ← IO.monoMsNow
  match ← IO.lazyPure fun _ => Recheck.produceWith cfg inp with
  | .error e => return { error := some e.render, produceMs := ← ms t0 }
  | .ok pr =>
    let produceMs ← ms t0
    let t1 ← IO.monoMsNow
    match ← IO.lazyPure fun _ => IxCC.Recheck.run cfg inp.program pr.cert with
    | .error e => return { ann := some pr.cert.relevance, cert := some pr.cert.toText,
                           error := some e.render, produceMs, runMs := ← ms t1 }
    | .ok a => return { ann := some pr.cert.relevance, cert := some pr.cert.toText,
                        object := some a.object, produceMs, runMs := ← ms t1 }

def runNew (cfg : Recheck.Config) (k : KernelFront.KInput) : IO RootRun := do
  let t0 ← IO.monoMsNow
  match ← IO.lazyPure fun _ => KernelFront.produceWith cfg k with
  | .error e => return { error := some e.render, produceMs := ← ms t0 }
  | .ok pr =>
    let produceMs ← ms t0
    let stageA ← IO.lazyPure fun _ => KernelFront.checkCanonicalRelevance cfg k pr.cert.table pr.cert.relevance
    let t1 ← IO.monoMsNow
    match ← IO.lazyPure fun _ => IxCC.Recheck.run cfg k.inp.program pr.cert with
    | .error e => return { ann := some pr.cert.relevance, cert := some pr.cert.toText,
                           error := some e.render, produceMs, runMs := ← ms t1, stageA }
    | .ok a => return { ann := some pr.cert.relevance, cert := some pr.cert.toText,
                        object := some a.object, produceMs, runMs := ← ms t1, stageA }

/-- What each front end adds to IxCC's reading agrees: the pins, their
resolution, the roots and the resource context, and each constant's identity
and kind. The constants' declarations and terms come from the same call on the
same environment. -/
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
  oldIngressMs : Nat := 0
  oldTypingMs : Nat := 0
  newIngressMs : Nat := 0
  newAcceptMs : Nat := 0
  program : List String := []
  roots : Array Json := #[]
  findings : Array String := #[]

def Report.toJson (r : Report) : Json :=
  Json.mkObj [("name", Lean.toJson (r.name)), ("bytes", Lean.toJson (r.bytes)), ("bound", Lean.toJson (r.bound)), ("records", Lean.toJson (r.records)),
    ("old_accept", Lean.toJson (r.oldAccept)), ("new_accept", Lean.toJson (r.newAccept)),
    ("old_ingress_ms", Lean.toJson (r.oldIngressMs)), ("old_typing_ms", Lean.toJson (r.oldTypingMs)),
    ("new_ingress_ms", Lean.toJson (r.newIngressMs)), ("new_accept_ms", Lean.toJson (r.newAcceptMs)),
    ("program", Lean.toJson r.program), ("roots", Json.arr r.roots),
    ("findings", Lean.toJson r.findings)]

/-- Both front ends on one closure, every sidecar root. -/
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
  -- the two ingresses, every root
  let t0 ← IO.monoMsNow
  let old ← IO.lazyPure fun _ => Recheck.ingress bytes sidecar [] (typecheck := false)
  let oldIngressMs ← ms t0
  let t0 ← IO.monoMsNow
  let new ← IO.lazyPure fun _ => KernelFront.ingress bytes sidecar []
  let newIngressMs ← ms t0
  r := { r with oldIngressMs := oldIngressMs + r.oldTypingMs, newIngressMs }
  match old, new with
  | .error e, _ => return { r with findings := r.findings.push s!"old ingress: {e.render}" }
  | _, .error e => return { r with findings := r.findings.push s!"new ingress: {e.render}" }
  | .ok inp, .ok k =>
    r := { r with program := sameProgram inp.program k.inp.program }
    for i in [0:inp.names.length] do
      let name := inp.names[i]!
      let cfg : Recheck.Config := { names := [name] }
      let oi := restrict inp i
      let ki := { k with inp := restrict k.inp i }
      -- the two annotators directly, on the program with the producer's table
      -- (before the admission policy, which may decline the root)
      let (table, _, _) := Src.Table.build cfg.table oi.program oi.hints.proposals
      let p0 := { oi.program with table }
      let t0 ← IO.monoMsNow
      let oa ← IO.lazyPure fun _ => Src.Relevance.annotate oi.env p0
      let oldAnnotateMs ← ms t0
      let t0 ← IO.monoMsNow
      let na ← IO.lazyPure fun _ => KernelFront.annotateChecked ki p0
      let newAnnotateMs ← ms t0
      let (annSame, annNorm, diffs, annErrors) := match oa, na with
        | .ok a, .ok b =>
          (a == b, (normAnn a).eqb (normAnn b), if a == b then #[] else annDiffs inp.program.size a b, "")
        | .error x, .error y => (false, false, #[], s!"both annotators refused: {x} / {y}")
        | .error x, .ok _ => (false, false, #[], s!"old annotator refused: {x}")
        | .ok _, .error y => (false, false, #[], s!"kernel annotator refused: {y}")
      let o ← runOld cfg oi
      let n ← runNew cfg ki
      let bothRan := o.object.isSome && n.object.isSome
      let certSame := o.cert == n.cert
      let objSame := o.object == n.object
      unless annSame && certSame && objSame && (!bothRan || n.stageA == some true) &&
          (o.error.isSome == n.error.isSome) do
        r := { r with findings := r.findings.push s!"root {name}: annotation {annSame} \
          (up to parameter order {annNorm}) {annErrors} {diffs}, certificate {certSame}, object {objSame}, \
          stage A {n.stageA}; old error {o.error}; new error {n.error}" }
      r := { r with roots := r.roots.push (Json.mkObj [
        ("root", Lean.toJson (name)), ("annotation_same", Lean.toJson (annSame)), ("annotation_same_up_to_order", Lean.toJson (annNorm)),
        ("annotation_diffs", Lean.toJson diffs), ("annotation_errors", Lean.toJson annErrors),
        ("old_annotate_ms", Lean.toJson oldAnnotateMs), ("new_annotate_ms", Lean.toJson newAnnotateMs),
        ("certificate_same", Lean.toJson (certSame)), ("object_same", Lean.toJson (objSame)),
        ("object_bytes", Lean.toJson ((o.object.map (·.size)).getD 0)),
        ("stage_a", Lean.toJson n.stageA),
        ("old_error", Lean.toJson o.error), ("new_error", Lean.toJson n.error),
        ("old_produce_ms", Lean.toJson (o.produceMs)), ("new_produce_ms", Lean.toJson (n.produceMs)),
        ("old_run_ms", Lean.toJson (o.runMs)), ("new_run_ms", Lean.toJson (n.runMs))]) }
    return r

/-- One front end alone on one closure (for timing and peak memory in a
process of its own): ingress, then every root produced and run. -/
def single (front : String) (bytes : ByteArray) (sidecar : Json) : IO Json := do
  let t0 ← IO.monoMsNow
  if front == "old" then
    match ← IO.lazyPure fun _ => Recheck.ingress bytes sidecar [] (typecheck := true) with
    | .error e => return Json.mkObj [("front", Lean.toJson (front)), ("error", Lean.toJson (e.render)), ("ingress_ms", Lean.toJson (← ms t0))]
    | .ok inp =>
      let ingressMs ← ms t0
      let mut out := #[]
      for i in [0:inp.names.length] do
        let o ← runOld { names := (inp.names[i]?).toList } (restrict inp i)
        out := out.push (Json.mkObj [("root", Lean.toJson ((inp.names[i]?).getD "")), ("error", Lean.toJson o.error),
          ("produce_ms", Lean.toJson (o.produceMs)), ("run_ms", Lean.toJson (o.runMs))])
      return Json.mkObj [("front", Lean.toJson (front)), ("ingress_ms", Lean.toJson (ingressMs)), ("roots", Json.arr out)]
  else
    match ← IO.lazyPure fun _ => KernelFront.ingress bytes sidecar [] with
    | .error e => return Json.mkObj [("front", Lean.toJson (front)), ("error", Lean.toJson (e.render)), ("ingress_ms", Lean.toJson (← ms t0))]
    | .ok k =>
      let ingressMs ← ms t0
      let mut out := #[]
      for i in [0:k.inp.names.length] do
        let n ← runNew { names := (k.inp.names[i]?).toList } { k with inp := restrict k.inp i }
        out := out.push (Json.mkObj [("root", Lean.toJson ((k.inp.names[i]?).getD "")), ("error", Lean.toJson n.error),
          ("produce_ms", Lean.toJson (n.produceMs)), ("run_ms", Lean.toJson (n.runMs)), ("stage_a", Lean.toJson n.stageA)])
      return Json.mkObj [("front", Lean.toJson (front)), ("ingress_ms", Lean.toJson (ingressMs)), ("roots", Json.arr out)]

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
