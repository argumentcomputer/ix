import IxCCTests.Own.Stage2.Owned
import IxCCTests.Own.Owned.Live
import IxCCTests.Own.Owned.Mutate
import IxCCTests.Own.Stage2.Random
import IxCCTests.Own.Owned.Sites
import IxCCTests.Own.Stage2.Hostile
import IxCC.Own.Plain.Owned
import IxCC.Recheck.Rc.Produce

/-! # Heap stage 2, milestone 1: the library checker against the prototype (differential run)

`probe-own-diff list LIST SITES RANDOM CAP SITESEED RANDSEED`: for each line of LIST
(`closure equations root label`), on both maps (the production canonical map and the liveness
map), compare the library checker (`IxCC.Own.Plain`) with the prototype
(`IxCCTests.Own.Stage2`): `checkMapE` with its message, `checkOwned` and `checkContractOwned`, on
the map itself, on two map-level perturbations (one function's entry erased; one body replaced by
`trap`), on every negative-control mutant (up to CAP per kind, as the probe's `corpus` command
chooses them), on RANDOM random mutants (as `campaign`, seed RANDSEED) and SITES site-directed
mutants (as `sites`, seed SITESEED: the first SITES attempts of that campaign). Each mutant is
compared body by body (`checkBodyE`), and every tenth also on the whole mutated map.
`probe-own-diff hostile`: the same on the hostile maps at sizes 100 and 300.
Same verdict and same message are required everywhere; prints counts and the first differences. -/

set_option autoImplicit false

namespace IxCCTests.Own.Stage2.Diff

open IxCC
open IxCC.Own.Plain (Code Program)
open IxCCTests.Own.Owned

def render (e : Except String Unit) : String :=
  match e with | .ok () => "ok" | .error m => s!"error: {m}"

structure Tally where
  n : Nat := 0
  acc : Nat := 0
  diff : Nat := 0
  firsts : List String := []

def Tally.add (t : Tally) (what lib proto : String) : Tally :=
  let d := lib != proto
  { n := t.n + 1, acc := t.acc + (if lib.startsWith "ok" then 1 else 0),
    diff := t.diff + (if d then 1 else 0),
    firsts := if d && t.firsts.length < 10 then t.firsts ++ [s!"{what}: lib [{lib}] proto [{proto}]"]
      else t.firsts }

def Tally.merge (a b : Tally) : Tally :=
  { n := a.n + b.n, acc := a.acc + b.acc, diff := a.diff + b.diff,
    firsts := (a.firsts ++ b.firsts).take 10 }

def mapLib (F : Fir.Program) (m : Src.NatMap Code) : String :=
  s!"{render (IxCC.Own.Plain.checkMapE F m)} owned={IxCC.Own.Plain.checkOwned F m} contract={IxCC.Own.Plain.checkContractOwned F m}"

def mapProto (F : Fir.Program) (m : Src.NatMap Code) : String :=
  s!"{render (IxCCTests.Own.Stage2.checkMapE F m)} owned={IxCCTests.Own.Stage2.checkOwned F m} contract={IxCCTests.Own.Stage2.checkContractOwned F m}"

def cmpMap (t : Tally) (what : String) (F : Fir.Program) (m : Src.NatMap Code) : Tally :=
  t.add what (mapLib F m) (mapProto F m)

/-- A mutant of function `g`'s body: compared body by body, and on the whole map when `whole`. -/
def cmpMutant (t : Tally) (what : String) (F : Fir.Program) (m : Src.NatMap Code) (g : Nat)
    (fd : Fir.Fun) (b : Code) (whole : Bool) : Tally :=
  let lib := render (IxCC.Own.Plain.checkBodyE fd b)
  let proto := render (IxCCTests.Own.Stage2.checkBodyE fd b)
  let (lib, proto) := if whole then
      let m' := m.insert g b
      (lib ++ " | " ++ mapLib F m', proto ++ " | " ++ mapProto F m')
    else (lib, proto)
  t.add what lib proto

def front (closure eqs root : String) : IO (Fir.Program × Src.NatMap Code) := do
  let bytes ← IO.FS.readBinFile closure
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile eqs))
  let inp ← IO.ofExcept ((Recheck.ingress bytes json [root]).mapError (·.render))
  let cfg := Recheck.Config.forInput {} inp
  let fr ← IO.ofExcept ((Recheck.RcReplay.produceFir cfg inp).mapError (·.render))
  return (fr.fir, (IxCC.Own.Plain.Program.canonicalForSrc fr.src fr.fir).bodies)

/-- Every comparison on one map; returns (maps, controls, random, sites) tallies. -/
def onMap (F : Fir.Program) (m : Src.NatMap Code) (sites random cap siteSeed randSeed : Nat)
    (name : String) : Tally × Tally × Tally × Tally := Id.run do
  let funs := (List.range F.size).filter fun g => (F.fun? g).isSome
  -- the map and two perturbations
  let mut tm : Tally := cmpMap {} "map" F m
  if let some g := funs.head? then
    tm := cmpMap tm s!"map without f{g}" F (m.erase g)
    tm := cmpMap tm s!"map with f{g} := trap" F (m.insert g .trap)
  -- the negative controls
  let mut tc : Tally := {}
  for kind in Kind.all do
    let mut tried := 0
    for g in funs do
      if tried ≥ cap then break
      let some fd := F.fun? g | continue
      let some body := m.get? g | continue
      for i in List.range cap do
        if tried ≥ cap then break
        let some body' := mutant kind i (fd.params.map (·.1)) body | break
        tc := cmpMutant tc s!"control {kind.name} f{g} site {i}" F m g fd body' (tried % 10 == 0)
        tried := tried + 1
  -- the random campaign's mutants
  let mut tr : Tally := {}
  let mut r : Rng := ⟨UInt64.ofNat (randSeed + name.length)⟩
  for i in List.range random do
    let (g, r1) := r.pick funs
    let (op, r2) := r1.pick Op.all
    r := r2
    let some fd := F.fun? g | continue
    let some body := m.get? g | continue
    let params := fd.params.map (·.1)
    let (res, r3) := applyOp op params body r
    r := r3
    let some (body1, what1) := res | continue
    let (coin, r4) := r.next 3
    let (op2, r5) := r4.pick Op.all
    let (res2, r6) := applyOp op2 params body1 r5
    r := r6
    let (body', what) := if coin == 0 then
        (match res2 with
          | some (b2, w2) => (b2, what1 ++ "; " ++ w2)
          | none => (body1, what1))
      else (body1, what1)
    tr := cmpMutant tr s!"random {i} f{g}: {what}" F m g fd body' (i % 10 == 0)
  -- the site-directed campaign's mutants
  let mut ts : Tally := {}
  r := ⟨UInt64.ofNat (siteSeed * 7919 + name.length)⟩
  for i in List.range sites do
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
    ts := cmpMutant ts s!"sites {i} f{g}: {what}" F m g fd body' (i % 10 == 0)
  return (tm, tc, tr, ts)

def row (label name : String) (t : Tally) (kind : String) : String :=
  s!"{label}\t{name}\t{kind}\tcompared {t.n}\taccepted {t.acc}\trefused {t.n - t.acc}\tdiffer {t.diff}"

def list (path : String) (sites random cap siteSeed randSeed : Nat) : IO UInt32 := do
  let lines := (← IO.FS.lines path).toList.filter (!·.isEmpty)
  let mut tot : Tally × Tally × Tally × Tally := ({}, {}, {}, {})
  let mut errors := 0
  for line in lines do
    let [closure, eqs, root, label] := line.splitOn "\t" | IO.println s!"bad line: {line}"
    try
      let (F, canonical) ← front closure eqs root
      for (name, m) in [("canonical", canonical), ("liveness", liveMap F)] do
        let (tm, tc, tr, ts) := onMap F m sites random cap siteSeed randSeed name
        for (k, t) in [("maps", tm), ("controls", tc), ("random", tr), ("sites", ts)] do
          IO.println (row label name t k)
          for e in t.firsts do IO.println s!"DIFFERENCE {label} {name}: {e}"
        tot := (tot.1.merge tm, tot.2.1.merge tc, tot.2.2.1.merge tr, tot.2.2.2.merge ts)
        (← IO.getStdout).flush
    catch e =>
      errors := errors + 1
      IO.println s!"{label}\tERROR {e}"
  for (k, t) in [("maps", tot.1), ("controls", tot.2.1), ("random", tot.2.2.1), ("sites", tot.2.2.2)] do
    IO.println (row "TOTAL" "both" t k)
  let d := tot.1.diff + tot.2.1.diff + tot.2.2.1.diff + tot.2.2.2.diff
  IO.println s!"TOTAL differing {d}, front-end errors {errors}"
  return if d == 0 then 0 else 1

def hostile : IO UInt32 := do
  let mut t : Tally := {}
  for v in [100, 300] do
    let F := Hostile.wideCase v v
    t := cmpMap t s!"wideCase {v}" F (IxCC.Own.Plain.Program.canonical F).bodies
    let F := Hostile.joinFan v v
    t := cmpMap t s!"joinFan {v}" F (IxCC.Own.Plain.Program.canonical F).bodies
    t := cmpMap t s!"joinFan-live {v}" F (liveMap F)
    let F := Hostile.deepJoins v v
    t := cmpMap t s!"deepJoins {v}" F (IxCC.Own.Plain.Program.canonical F).bodies
  let (F, c) := Hostile.chain 10 10000
  t := cmpMap t "chain" F c
  let F := Hostile.joinFan 100 10
  let bad := (IxCC.Own.Plain.Program.canonical F).bodies.map fun
    | .jp j ps _ rec b k => .jp j ps (List.replicate 1000 0) rec b k
    | c => c
  t := cmpMap t "repeated captured" F bad
  IO.println (row "hostile" "-" t "maps")
  for e in t.firsts do IO.println s!"DIFFERENCE hostile: {e}"
  return if t.diff == 0 then 0 else 1

end IxCCTests.Own.Stage2.Diff

def main (args : List String) : IO UInt32 := do
  match args with
  | ["list", path, sites, random, cap, siteSeed, randSeed] =>
    IxCCTests.Own.Stage2.Diff.list path sites.toNat! random.toNat! cap.toNat! siteSeed.toNat!
      randSeed.toNat!
  | ["hostile"] => IxCCTests.Own.Stage2.Diff.hostile
  | _ =>
    IO.eprintln "usage: probe-own-diff list LIST SITES RANDOM CAP SITESEED RANDSEED | hostile"
    return 2
