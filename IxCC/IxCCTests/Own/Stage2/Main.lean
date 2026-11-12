import IxCCTests.Own.Stage2.Owned
import IxCCTests.Own.Stage2.Live
import IxCCTests.Own.Stage2.Interp
import IxCCTests.Own.Stage2.Mutate
import IxCCTests.Own.Stage2.Hostile
import IxCCTests.Own.Stage2.Oracle
import IxCCTests.Own.Stage2.Sites
import IxCC.Own.Plain.Certificate
import IxCC.Recheck.Rc.Produce
import IxCC.Cfg.Rc.Run
import IxCC.Rt.Readback

/-! # Heap stage 2, step 0: the probe driver

* `corpus LIST`: each line `closure equations root label`: the root's Fir program and canonical
  map as the production producer makes them; `checkPlainMap` and `checkOwned` on the canonical
  map; the liveness map, its certificate round trip, `checkOwned` on it, Cfg generation of it;
  static `inc`/`dec` counts of both; the negative controls on both maps.
* `bench closure equations root label N...`: both placements run on the production
  `Own.Plain.run`, the instrumented interpreter and the Cfg RC machine (`Cfg.Rc.run` of the
  generated program); results compared; events and the peak counted.
* `hostile`: `checkOwned` and `checkPlainMap` timed on maps built to be expensive. -/

open IxCC IxCC.Own.Plain IxCCTests.Own.Stage2

namespace IxCCTests.Own.Stage2.Main

mutual
def countActs : Code → Nat × Nat
  | .act (.inc _ _) k => let (i, d) := countActs k; (i + 1, d)
  | .act (.dec _) k => let (i, d) := countActs k; (i, d + 1)
  | .bind _ _ k => countActs k
  | .jp _ _ _ _ b k => let (i, d) := countActs b; let (i', d') := countActs k; (i + i', d + d')
  | .case _ alts d => let (i, e) := countAlts alts; let (i', e') := countOpt d; (i + i', e + e')
  | _ => (0, 0)
def countAlts : List Alt → Nat × Nat
  | [] => (0, 0)
  | .mk _ b :: rest => let (i, d) := countActs b; let (i', d') := countAlts rest; (i + i', d + d')
def countOpt : Option Code → Nat × Nat
  | none => (0, 0)
  | some c => countActs c
end

def mapActs (F : Fir.Program) (m : Src.NatMap Code) : Nat × Nat :=
  (List.range F.size).foldl (fun (i, d) f => match m.get? f with
    | some c => let (i', d') := countActs c; (i + i', d + d')
    | none => (i, d)) (0, 0)

def timed {α : Type} (f : Unit → α) : IO (α × Nat) := do
  let t0 ← IO.monoNanosNow
  let a ← IO.lazyPure f
  let t1 ← IO.monoNanosNow
  return (a, (t1 - t0) / 1000)

def errOf (e : Except String Unit) : String := match e with | .ok () => "ok" | .error m => m

structure Front where
  fir : Fir.Program
  canonical : Src.NatMap Code

def front (closure eqs root : String) : IO Front := do
  let bytes ← IO.FS.readBinFile closure
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile eqs))
  let inp ← IO.ofExcept ((Recheck.ingress bytes json [root]).mapError (·.render))
  let cfg := Recheck.Config.forInput {} inp
  let fr ← IO.ofExcept ((Recheck.RcReplay.produceFir cfg inp).mapError (·.render))
  return { fir := fr.fir, canonical := (Program.canonicalForSrc fr.src fr.fir).bodies }

/-- Negative controls on one map: per kind, sites tried, refused for the stated reason, refused
for another reason (with the first such message), accepted. -/
def controls (F : Fir.Program) (m : Src.NatMap Code) (cap : Nat) : IO (List String) := do
  let mut out := []
  for kind in Kind.all do
    let mut tried := 0; let mut stated := 0; let mut other := 0; let mut accepted := 0
    let mut otherMsg := ""
    for f in List.range F.size do
      if tried ≥ cap then break
      let some fd := F.fun? f | continue
      let some body := m.get? f | continue
      for t in List.range cap do
        if tried ≥ cap then break
        let some body' := mutant kind t (fd.params.map (·.1)) body | break
        tried := tried + 1
        match checkBodyE fd body' with
        | .ok () => accepted := accepted + 1
        | .error e =>
          if kind.expected e then stated := stated + 1
          else
            other := other + 1
            if otherMsg.isEmpty then otherMsg := e
    out := out ++ [s!"{kind.name}={tried}/{stated}/{other}/{accepted}" ++
      (if otherMsg.isEmpty then "" else s!" [other: {otherMsg}]")]
  return out

def corpus (list : String) : IO UInt32 := do
  let lines := (← IO.FS.lines list).toList.filter (!·.isEmpty)
  IO.println "label\tfuns\tnodes\tplain(canon)\towned(canon)\tus(owned canon)\tus(plain canon)\towned(live)\tus(owned live)\twire(live)\tcfg(live)\tinc/dec canon\tinc/dec live"
  for line in lines do
    let [closure, eqs, root, label] := line.splitOn "\t" | IO.println s!"bad line: {line}"
    try
      let fr ← front closure eqs root
      let F := fr.fir
      let (plainOk, tPlain) ← timed fun _ => checkPlainMap F fr.canonical
      let (canonE, tCanon) ← timed fun _ => checkMapE F fr.canonical
      let canonOwned := programDomain F && checkBoolPins F && canonE.isOk
      let live := liveMap F
      let (liveE, tLive) ← timed fun _ => checkMapE F live
      let liveOwned := programDomain F && checkBoolPins F && liveE.isOk
      let wire := match Certificate.decode F (Certificate.encode live) with
        | .ok back => if bodyMapEq back live then "ok" else "differs"
        | .error e => e
      let cfg := if (Cfg.Rc.generate F live).isSome then "ok" else "declined"
      let (ci, cd) := mapActs F fr.canonical
      let (li, ld) := mapActs F live
      IO.println s!"{label}\t{F.size}\t{F.nodes}\t{plainOk}\t{canonOwned}\t{tCanon}\t{tPlain}\t{liveOwned}\t{tLive}\t{wire}\t{cfg}\t{ci}/{cd}\t{li}/{ld}"
      unless canonE.isOk do IO.println s!"  CANONICAL REFUSED: {errOf canonE}"
      unless liveE.isOk do IO.println s!"  LIVE REFUSED: {errOf liveE}"
      if canonOwned then
        IO.println s!"  controls canonical: {" ".intercalate (← controls F fr.canonical 12)}"
      if liveOwned then
        IO.println s!"  controls live: {" ".intercalate (← controls F live 12)}"
      (← IO.getStdout).flush
    catch e => IO.println s!"{label}\tERROR {e}"
  return 0

def short (s : String) : String := String.mk (s.toList.take 60)

def renderResult (r : Sem.Result (Own.RVal × Own.Heap)) : String :=
  match r with
  | .ok (v, H) => (H.readback v).map Rt.renderObs |>.getD "?"
  | .timeout => "timeout"
  | .resource _ => "resource"
  | .trap => "trap"
  | .stuck => "stuck"

def renderI (r : Except String (Own.RVal × Own.Heap)) : String :=
  match r with
  | .ok (v, H) => (H.readback v).map Rt.renderObs |>.getD "?"
  | .error e => s!"error: {e}"

def bench (closure eqs root label : String) (ns : List Nat) (prodMax : Nat) : IO UInt32 := do
  let fr ← front closure eqs root
  let F := fr.fir
  let some f := F.exports.head? | throw (IO.userError "no export")
  let live := liveMap F
  IO.println s!"{label}: checkOwned canonical {checkOwned F fr.canonical}, live {checkOwned F live}"
  let placements : List (String × Src.NatMap Code) := [("canonical", fr.canonical), ("liveness", live)]
  IO.println "label\tn\tplacement\tresult\tprod\tcfg\tsteps\tcalls\tallocs\tincs\tincImm\tdecs\tdecImm\tfrees\tliveEnd\tpeak\tms"
  for n in ns do
    let mut results : List String := []
    for (name, m) in placements do
      let P : Program := { source := F, bodies := m }
      let args := [Own.RVal.lit (.nat n)]
      let t0 ← IO.monoMsNow
      let (r, c) ← IO.lazyPure fun _ => runI P 4000000000 f args
      let t1 ← IO.monoMsNow
      let prod ← if n ≤ prodMax then
          pure (renderResult (← IO.lazyPure fun _ => run P 100000000 f args))
        else pure "-"
      let cfgR ← if n ≤ prodMax then
          match Cfg.Rc.generate F m with
          | some C => pure (renderResult (← IO.lazyPure fun _ => Cfg.Rc.run C 100000000 f args))
          | none => pure "declined"
        else pure "-"
      let res := renderI r
      results := results ++ [res]
      let res' := if res.length > 60 then short res ++ "…" else res
      let prod' := if prod == "-" then "-" else if prod == res then "same" else s!"DIFFERS {short prod}"
      let cfg' := if cfgR == "-" then "-" else if cfgR == res then "same" else s!"DIFFERS {short cfgR}"
      IO.println s!"{label}\t{n}\t{name}\t{res'}\t{prod'}\t{cfg'}\t{c.steps}\t{c.calls}\t{c.allocs}\t{c.incs}\t{c.incImm}\t{c.decs}\t{c.decImm}\t{c.frees}\t{c.live}\t{c.peak}\t{t1 - t0}"
      (← IO.getStdout).flush
    match results with
    | [a, b] => IO.println s!"{label}\t{n}\tequal-results\t{a == b}"
    | _ => pure ()
  return 0

def hostileRow (name : String) (F : Fir.Program) (m : Src.NatMap Code) (plain : Bool) : IO Unit := do
  let (ok, t) ← timed fun _ => checkOwned F m
  let (p, tp) ← if plain then timed fun _ => checkPlainMap F m else pure (false, 0)
  let (i, d) := mapActs F m
  let size := (Certificate.toText m).length
  IO.println s!"{name}\tnodes {F.nodes}\tcert {size} chars\tacts {i + d}\tcheckOwned {ok} {t} us\tcheckPlainMap {if plain then s!"{p} {tp} us" else "-"}"
  (← IO.getStdout).flush

def hostile (big : Bool) : IO UInt32 := do
  for v in [100, 300, 1000, 3000] do
    let F := Hostile.wideCase v v
    hostileRow s!"wideCase V={v} B={v}" F (Program.canonical F).bodies (v ≤ 1000)
  for v in [100, 300, 1000, 3000] ++ (if big then [10000] else []) do
    let F := Hostile.joinFan v v
    hostileRow s!"joinFan V={v} K={v}" F (Program.canonical F).bodies (v ≤ 300)
    hostileRow s!"joinFan-live V={v} K={v}" F (liveMap F) false
  for v in [100, 300, 1000] do
    let F := Hostile.deepJoins v v
    hostileRow s!"deepJoins D={v} V={v}" F (Program.canonical F).bodies (v ≤ 300)
  for m in [10000, 100000, 1000000] do
    let (F, c) := Hostile.chain 10 m
    hostileRow s!"chain M={m}" F c false
  -- a hostile captured list: one variable repeated
  let F := Hostile.joinFan 100 10
  let bad := (Program.canonical F).bodies.map fun
    | .jp j ps _ rec b k => .jp j ps (List.replicate 100000 0) rec b k
    | c => c
  hostileRow "joinFan captured=[v0 x 100000]" F bad false
  IO.println s!"  refusal: {errOf (checkMapE F bad)}"
  return 0

def inputsFor (F : Fir.Program) (f : Nat) (ns : List Nat) : List (List Own.RVal) :=
  let arity := ((F.fun? f).map (·.params.length)).getD 0
  ns.map fun n => List.replicate arity (.lit (.nat n))

/-- References: each input's result on the unmutated map; inputs where it fails are skipped. -/
def references (P : Program) (f : Nat) (inputs : List (List Own.RVal)) : List (List Own.RVal × String × (Nat × Nat × Nat)) :=
  inputs.filterMap fun args =>
    let (r, c) := runI P 200000000 f args
    match r with
    | .ok _ => some (args, readOf r, (c.incs - c.incImm, c.decs - c.decImm, c.peak))
    | .error _ => none

/-- Run the oracle on every input; `(runs, reached, failures)`. -/
def judge (P : Program) (f watch : Nat) (refs : List (List Own.RVal × String × (Nat × Nat × Nat))) :
    Nat × Bool × Bool × List String :=
  refs.foldl (fun (runs, reached, eff, fails) (args, ref, sig) =>
    let (v, hits, sig') := oracle P f args ref watch
    (runs + 1, reached || hits > 0, eff || sig != sig',
      match v with | some e => fails ++ [e] | none => fails)) (0, false, false, [])

def borrowed (closure eqs root label : String) (ns : List Nat) : IO UInt32 := do
  let fr ← front closure eqs root
  let F := fr.fir
  let some f := F.exports.head? | throw (IO.userError "no export")
  let inputs := inputsFor F f ns
  for (name, m) in [("canonical", fr.canonical), ("liveness", liveMap F)] do
    let refs := references { source := F, bodies := m } f inputs
    let mut tried := 0; let mut accepted := 0; let mut clean := 0
    for g in List.range F.size do
      let some fd := F.fun? g | continue
      let some body := m.get? g | continue
      for t in List.range 200 do
        let some body' := mutant .borrowedConsumed t (fd.params.map (·.1)) body | break
        tried := tried + 1
        if (checkBodyE fd body').isOk then
          accepted := accepted + 1
          let (runs, reached, _, fails) := judge { source := F, bodies := m.insert g body' } f g refs
          if fails.isEmpty then clean := clean + 1
          IO.println s!"{label}\t{name}\tf{g} site {t}\taccepted\truns {runs}\treached {reached}\t{if fails.isEmpty then "clean" else s!"FAIL {fails.head!}"}"
    IO.println s!"{label}\t{name}\tsites {tried}\taccepted {accepted}\tclean {clean}\tinputs with a reference {refs.length}/{inputs.length}"
    (← IO.getStdout).flush
  return 0

def campaign (closure eqs root label : String) (count seed : Nat) (ns : List Nat) : IO UInt32 := do
  let fr ← front closure eqs root
  let F := fr.fir
  let some f := F.exports.head? | throw (IO.userError "no export")
  let inputs := inputsFor F f ns
  let funs := (List.range F.size).filter fun g => (F.fun? g).isSome
  for (name, m) in [("canonical", fr.canonical), ("liveness", liveMap F)] do
    let refs := references { source := F, bodies := m } f inputs
    let mut r : Rng := ⟨UInt64.ofNat (seed + name.length)⟩
    let mut stats : List (String × Nat × Nat × Nat × Nat × Nat × Nat) := Op.all.map fun op => (op.name, 0, 0, 0, 0, 0, 0)
    let mut failures : List String := []
    for _ in List.range count do
      let (g, r1) := r.pick funs
      let (op, r2) := r1.pick Op.all
      r := r2
      let some fd := F.fun? g | continue
      let some body := m.get? g | continue
      let params := fd.params.map (·.1)
      let (res, r3) := applyOp op params body r
      r := r3
      let some (body1, what1) := res | continue
      -- a second edit, a third of the time
      let (coin, r4) := r.next 3
      let (op2, r5) := r4.pick Op.all
      let (res2, r6) := applyOp op2 params body1 r5
      r := r6
      let (body', what) := if coin == 0 then
          (match res2 with
            | some (b2, w2) => (b2, what1 ++ "; " ++ w2)
            | none => (body1, what1))
        else (body1, what1)
      let ok := (checkBodyE fd body').isOk
      let (runs, reached, eff, fails) := if ok then judge { source := F, bodies := m.insert g body' } f g refs
        else (0, false, false, [])
      stats := stats.map fun (n, gen, acc, run, rea, ef, bad) =>
        if n == op.name then (n, gen + 1, acc + (if ok then 1 else 0), run + runs,
          rea + (if reached then 1 else 0), ef + (if eff then 1 else 0), bad + (if fails.isEmpty then 0 else 1))
        else (n, gen, acc, run, rea, ef, bad)
      unless fails.isEmpty do
        failures := failures ++ [s!"f{g}: {what}: {fails.head!}"]
    IO.println s!"{label}\t{name}\tinputs with a reference {refs.length}/{inputs.length}"
    IO.println "op\tgenerated\taccepted\toracle runs\taccepted and reached\taccepted with changed heap RC traffic\taccepted and misbehaving"
    for (n, gen, acc, run, rea, ef, bad) in stats do
      IO.println s!"{label}\t{name}\t{n}\t{gen}\t{acc}\t{run}\t{rea}\t{ef}\t{bad}"
    for e in failures.take 20 do IO.println s!"COUNTEREXAMPLE {label} {name}: {e}"
    (← IO.getStdout).flush
  return 0

structure SiteRef where
  args : List Own.RVal
  value : String
  sig : Nat × Nat × Nat
  heapHash : UInt64
  fullHash : UInt64

def siteRefs (P : Program) (f : Nat) (inputs : List (List Own.RVal)) : List SiteRef :=
  inputs.filterMap fun args =>
    let (r, c) := runI P 200000000 f args
    match r with
    | .ok _ => some { args, value := readOf r, sig := (c.incs - c.incImm, c.decs - c.decImm, c.peak),
                      heapHash := c.heapHash, fullHash := c.fullHash }
    | .error _ => none

/-- Per kind: generated, accepted, oracle runs, accepted that change the cell RC sequence (of
which: change the counts or the peak), accepted that ran but left the cell RC sequence unchanged,
accepted on paths no input ran, misbehaving. -/
structure SiteStats where
  gen : Nat := 0
  acc : Nat := 0
  runs : Nat := 0
  heap : Nat := 0
  counts : Nat := 0
  ranSame : Nat := 0
  unrun : Nat := 0
  bad : Nat := 0

def SiteStats.add (a b : SiteStats) : SiteStats :=
  { gen := a.gen + b.gen, acc := a.acc + b.acc, runs := a.runs + b.runs, heap := a.heap + b.heap,
    counts := a.counts + b.counts, ranSame := a.ranSame + b.ranSame, unrun := a.unrun + b.unrun,
    bad := a.bad + b.bad }

def SiteStats.row (s : SiteStats) : String :=
  s!"{s.gen}\t{s.acc}\t{s.runs}\t{s.heap}\t{s.counts}\t{s.ranSame}\t{s.unrun}\t{s.bad}"

/-- The site-directed campaign on one program, both maps. -/
def sites (closure eqs root label : String) (count seed : Nat) (ns : List Nat) : IO UInt32 := do
  let fr ← front closure eqs root
  let F := fr.fir
  let some f := F.exports.head? | throw (IO.userError "no export")
  let inputs := inputsFor F f ns
  let funs := (List.range F.size).filter fun g => (F.fun? g).isSome
  for (name, m) in [("canonical", fr.canonical), ("liveness", liveMap F)] do
    let refs := siteRefs { source := F, bodies := m } f inputs
    let mut r : Rng := ⟨UInt64.ofNat (seed * 7919 + name.length)⟩
    let mut stats : List (SiteKind × SiteStats) := SiteKind.all.map (·, {})
    let mut failures : List String := []
    for _ in List.range count do
      let (g, r1) := r.pick funs
      let (kind, r2) := r1.pick SiteKind.all
      r := r2
      let some fd := F.fun? g | continue
      let some body := m.get? g | continue
      let params := fd.params.map (·.1)
      let (res, r3) := siteEdit kind params body r
      r := r3
      let some (body1, what1) := res | continue
      let (coin, r4) := r.next 3
      let (kind2, r5) := r4.pick SiteKind.all
      let (res2, r6) := if coin == 0 then siteEdit kind2 params body1 r5 else (none, r5)
      r := r6
      let (body', what) := match res2 with
        | some (b2, w2) => (b2, what1 ++ "; " ++ w2)
        | none => (body1, what1)
      let ok := (checkBodyE fd body').isOk
      let mut s : SiteStats := { gen := 1, acc := if ok then 1 else 0 }
      if ok then
        let P : Program := { source := F, bodies := m.insert g body' }
        let vs := refs.map fun ref => (ref, oracleV P f ref.args ref.value g)
        let heap := vs.any fun (ref, v) => v.heapHash != ref.heapHash
        let counts := vs.any fun (ref, v) => v.sig != ref.sig
        let ran := vs.any fun (ref, v) => v.fullHash != ref.fullHash
        let fails := vs.filterMap fun (_, v) => v.failure
        s := { s with runs := vs.length, heap := if heap then 1 else 0,
                      counts := if counts then 1 else 0,
                      ranSame := if !heap && ran then 1 else 0,
                      unrun := if !ran then 1 else 0, bad := if fails.isEmpty then 0 else 1 }
        unless fails.isEmpty do
          failures := failures ++ [s!"f{g}: {what}: {fails.head!}\n  MUTANT {repr body'}"]
      stats := stats.map fun (k, t) => if k == kind then (k, t.add s) else (k, t)
    IO.println s!"{label}\t{name}\tinputs with a reference {refs.length}/{inputs.length}"
    IO.println "label\tmap\tkind\tgenerated\taccepted\toracle runs\taccepted, cell RC sequence changed\tof which counts or peak changed\taccepted, ran, cell RC sequence unchanged\taccepted, not run\tmisbehaving"
    for (k, t) in stats do
      IO.println s!"{label}\t{name}\t{k.name}\t{t.row}"
    let tot := stats.foldl (fun a (_, t) => a.add t) {}
    IO.println s!"{label}\t{name}\tTOTAL\t{tot.row}"
    for e in failures.take 20 do IO.println s!"COUNTEREXAMPLE {label} {name}: {e}"
    (← IO.getStdout).flush
  return 0

end IxCCTests.Own.Stage2.Main

def main (args : List String) : IO UInt32 := do
  match args with
  | ["corpus", list] => IxCCTests.Own.Stage2.Main.corpus list
  | "bench" :: closure :: eqs :: root :: label :: prodMax :: ns =>
    IxCCTests.Own.Stage2.Main.bench closure eqs root label (ns.map String.toNat!) prodMax.toNat!
  | "borrowed" :: closure :: eqs :: root :: label :: ns =>
    IxCCTests.Own.Stage2.Main.borrowed closure eqs root label (ns.map String.toNat!)
  | "campaign" :: closure :: eqs :: root :: label :: count :: seed :: ns =>
    IxCCTests.Own.Stage2.Main.campaign closure eqs root label count.toNat! seed.toNat! (ns.map String.toNat!)
  | "sites" :: closure :: eqs :: root :: label :: count :: seed :: ns =>
    IxCCTests.Own.Stage2.Main.sites closure eqs root label count.toNat! seed.toNat! (ns.map String.toNat!)
  | ["hostile"] => IxCCTests.Own.Stage2.Main.hostile false
  | ["hostile", "big"] => IxCCTests.Own.Stage2.Main.hostile true
  | _ =>
    IO.eprintln "usage: probe-own-stage2 corpus LIST | bench CLOSURE EQ ROOT LABEL PRODMAX N... | hostile [big]"
    return 2
