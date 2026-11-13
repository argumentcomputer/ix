import IxCCTests.Own.Owned.Live
import IxCCTests.Own.Owned.Sites
import IxCCTests.Own.Owned.ScopeSet
import IxCCTests.Own.Owned.KeyIndex
import IxCCTests.Xv.StackingLinear
import IxCCTests.Corpus.Manifest
import IxCC.Own.Plain.Certificate
import IxCC.Recheck.Rc.Produce
import IxCC.Cfg.Rc.Run

/-! # `tests-own-owned`: the ownership checker's focused suite

The library checker `IxCC.Own.Plain.checkOwned` (heap stage 2, milestone 1; nothing in production
calls it yet) on every root of the registered corpus families that the manifest does not decline
(`IxCCTests.Corpus.families`, committed fixtures), each through the production front end
(`RcReplay.produceFir`) and the production canonical producer (`Program.canonicalForSrc`), and on
a second placement of every root made by the liveness producer (`Live`, untrusted):

* **acceptance**: where `checkPlainMap` accepts the canonical map, `checkOwned` accepts it
  (`checkPlainMap_checkOwned`, run); `checkOwned` accepts the liveness map of every root in the
  plain domain, which round-trips the certificate format and lowers to Cfg; both maps, run on the
  instrumented interpreter (`Interp`) on each input, pass the oracle (`Oracle`: no error, the same
  value, exact counts at return, everything reclaimed) and give the same value;
* **negative controls** (`Mutate`, up to `CAP` sites per kind and map): a double decrement, a
  missing decrement on one branch, a use after the last decrement, a borrowed value consumed
  without an increment, an increment missing before a second constructor use, a value moved into a
  call and used after. A control of the four kinds that can never be a correct placement must be
  refused; one of the other two that is accepted (a borrowed value only a primitive reads; a
  decrement missing on a path that ends in `trap`, which may leak) must pass the oracle; and each
  kind must be refused for its stated reason somewhere;
* **the site-directed campaign** (`Sites`, `COUNT` attempts per root and map, seed 29, as the
  heap stage 2 campaign of step 0): every accepted mutant must pass the oracle on every input with a
  reference; and some accepted mutant must change the cell reference-count traffic;
* three fixed maps: a repeated captured variable is refused; a map that leaks before `trap` is
  accepted (a trap ends the run); an increment by two is refused;
* **the source scope check** (`ScopeSet`): on every root, then on synthetic programs and a call of
  an entry past `size`, `programDomain`'s set forms against its former list forms, and one
  ill-scoped edit per kind per function refused by both;
* **policy selection** (`KeyIndex`): on every root with its source, then on synthetic programs,
  `enrichFirContracts` (a key index built once, merges in one pass) against its former list form
  and the production list form: the same enriched program, the same policy, and the index's
  function for every key looked up;
* **stacking's reads and placements** (`IxCCTests.Xv.StackingLinear`): on every root's Xl on the
  immortal route and on the plain-RC route under the canonical map, then on the backend suite's
  hand-written programs and generated programs of many functions, `Stacking.run` and the reads and
  placements it makes against their first forms.

Arguments: `[COUNT [CAP]]` (defaults 100 and 12). Run from the `IxCC` directory (the manifests'
paths are relative to it). -/

set_option autoImplicit false

namespace IxCCTests.Own.Owned.Main

open IxCC IxCC.Own.Plain IxCCTests.Own.Owned

/-- The inputs: every argument `n`, for each `n` (as the step-0 campaign on the corpus). -/
def inputValues : List Nat := [0, 1, 3, 7]

structure Totals where
  roots : Nat := 0
  plainAccepted : Nat := 0
  ownedAccepted : Nat := 0
  liveAccepted : Nat := 0
  runs : Nat := 0
  controls : List (String × Nat × Nat × Nat × Nat) := Kind.all.map fun k => (k.name, 0, 0, 0, 0)
  generated : Nat := 0
  accepted : Nat := 0
  oracleRuns : Nat := 0
  heapChanging : Nat := 0
  scope : ScopeSet.Tally := {}
  policy : KeyIndex.Tally := {}
  stacking : IxCCTests.Xv.StackingLinear.Tally := {}
  failures : Array String := #[]

def Totals.fail (t : Totals) (msg : String) : Totals :=
  { t with failures := t.failures.push msg }

def front (closure eqs : System.FilePath) (root : String) :
    IO (Fir.Program × Src.NatMap Code × Src.Program × Recheck.Config) := do
  let bytes ← IO.FS.readBinFile closure
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile eqs))
  let inp ← IO.ofExcept ((Recheck.ingress bytes json [root]).mapError (·.render))
  let cfg := Recheck.Config.forInput {} inp
  let fr ← IO.ofExcept ((Recheck.RcReplay.produceFir cfg inp).mapError (·.render))
  return (fr.fir, (Program.canonicalForSrc fr.src fr.fir).bodies, fr.src, cfg)

/-- A reference run of an accepted map on one input. -/
structure Ref where
  args : List Own.RVal
  value : String
  sig : Nat × Nat × Nat
  heapHash : UInt64

def refsOf (P : Program) (f : Nat) (inputs : List (List Own.RVal)) : List Ref :=
  inputs.filterMap fun args =>
    let (r, c) := runI P 200000000 f args
    match r with
    | .ok _ => some { args, value := readOf r, sig := (c.incs - c.incImm, c.decs - c.decImm, c.peak),
                      heapHash := c.heapHash }
    | .error _ => none

/-- The oracle on every reference input: the first failure, and whether the cell RC traffic
changed against the reference. -/
def judge (P : Program) (f g : Nat) (refs : List Ref) : Option String × Bool × Nat :=
  refs.foldl (fun (fail, changed, n) ref =>
    let v := oracleV P f ref.args ref.value g
    (fail <|> v.failure, changed || v.heapHash != ref.heapHash || v.sig != ref.sig, n + 1))
    (none, false, 0)

def canNeverBeCorrect : Kind → Bool
  | .doubleDec | .useAfterDec | .missingIncCtor | .movedIntoCall => true
  | .missingDec | .borrowedConsumed => false

/-- The negative controls on one map. -/
def controls (t : Totals) (label name : String) (F : Fir.Program) (m : Src.NatMap Code) (f : Nat)
    (refs : List Ref) (cap : Nat) : Totals := Id.run do
  let mut t := t
  for kind in Kind.all do
    let mut tried := 0; let mut stated := 0; let mut other := 0; let mut accepted := 0
    for g in List.range F.size do
      if tried ≥ cap then break
      let some fd := F.fun? g | continue
      let some body := m.get? g | continue
      for i in List.range cap do
        if tried ≥ cap then break
        let some body' := mutant kind i (fd.params.map (·.1)) body | break
        tried := tried + 1
        match checkBodyE fd body' with
        | .error e => if kind.expected e then stated := stated + 1 else other := other + 1
        | .ok () =>
          accepted := accepted + 1
          if canNeverBeCorrect kind then
            t := t.fail s!"{label} {name}: control {kind.name} f{g} site {i} accepted"
          else
            let (fail, _, n) := judge { source := F, bodies := m.insert g body' } f g refs
            t := { t with oracleRuns := t.oracleRuns + n }
            if let some e := fail then
              t := t.fail s!"{label} {name}: accepted control {kind.name} f{g} site {i} misbehaves: {e}"
    t := { t with controls := t.controls.map fun (k, a, b, c, d) =>
      if k == kind.name then (k, a + tried, b + stated, c + other, d + accepted) else (k, a, b, c, d) }
  return t

/-- The site-directed campaign on one map (seeded as the step-0 campaign). -/
def campaign (t : Totals) (label name : String) (F : Fir.Program) (m : Src.NatMap Code) (f : Nat)
    (refs : List Ref) (count seed : Nat) : Totals := Id.run do
  let mut t := t
  let funs := (List.range F.size).filter fun g => (F.fun? g).isSome
  let mut r : Rng := ⟨UInt64.ofNat (seed * 7919 + name.length)⟩
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
    t := { t with generated := t.generated + 1 }
    if (checkBodyE fd body').isOk then
      let (fail, changed, n) := judge { source := F, bodies := m.insert g body' } f g refs
      t := { t with accepted := t.accepted + 1, oracleRuns := t.oracleRuns + n,
                    heapChanging := t.heapChanging + (if changed then 1 else 0) }
      if let some e := fail then
        t := t.fail s!"{label} {name}: accepted mutant of f{g} misbehaves ({what}): {e}"
  return t

/-- Every check on one root. -/
def root (t : Totals) (label : String) (F : Fir.Program) (canonical : Src.NatMap Code)
    (count cap : Nat) : Totals := Id.run do
  let mut t := { t with roots := t.roots + 1, scope := ScopeSet.checkProgram t.scope label F }
  let plain := checkPlainMap F canonical
  let owned := checkOwned F canonical
  if plain then t := { t with plainAccepted := t.plainAccepted + 1 }
  if owned then t := { t with ownedAccepted := t.ownedAccepted + 1 }
  if plain && !owned then
    t := t.fail s!"{label}: checkPlainMap accepts the canonical map, checkOwned refuses it"
  unless owned do return t
  let live := liveMap F
  match checkMapE F live with
  | .error e => return t.fail s!"{label}: the liveness map is refused: {e}"
  | .ok () => t := { t with liveAccepted := t.liveAccepted + 1 }
  match Certificate.decode F (Certificate.encode live) with
  | .ok back => unless bodyMapEq back live do t := t.fail s!"{label}: liveness certificate round trip differs"
  | .error e => t := t.fail s!"{label}: liveness certificate does not decode: {e}"
  if (Cfg.Rc.generate F live).isNone then t := t.fail s!"{label}: Cfg declines the liveness map"
  let some f := F.exports.head? | return t.fail s!"{label}: no export"
  let arity := ((F.fun? f).map (·.params.length)).getD 0
  let inputs := inputValues.map fun n => List.replicate arity (Own.RVal.lit (.nat n))
  let canonRefs := refsOf { source := F, bodies := canonical } f inputs
  let liveRefs := refsOf { source := F, bodies := live } f inputs
  if canonRefs.map (·.args) != liveRefs.map (·.args) then
    t := t.fail s!"{label}: the two placements succeed on different inputs"
  for (a, b) in canonRefs.zip liveRefs do
    if a.value != b.value then t := t.fail s!"{label}: placements differ on {repr a.args}"
  for (name, m, refs) in [("canonical", canonical, canonRefs), ("liveness", live, liveRefs)] do
    for ref in refs do
      let v := oracleV { source := F, bodies := m } f ref.args ref.value 0
      t := { t with runs := t.runs + 1 }
      if let some e := v.failure then t := t.fail s!"{label} {name}: the oracle refuses the map: {e}"
    t := controls t label name F m f refs cap
    t := campaign t label name F m f refs count 29
  return t

/-! ## Three fixed maps -/

def mkProg (params : List Fir.Var) (body : Fir.Code) (vars : Nat) : Fir.Program :=
  let fd : Fir.Fun := { (default : Fir.Fun) with params := params.map (·, .tobj), body, vars }
  { funs := Src.NatMap.ofList [(0, fd)], size := 1, exports := [0], ctors := [], known := {} }

def fixed (t : Totals) : Totals := Id.run do
  let mut t := t
  -- a join capturing one variable a thousand times
  let F := mkProg [0, 1] (.jp 0 [2] false (.ret (.var 2)) (.jmp 0 [.lit (.nat 0)])) 3
  let bad := (Program.canonical F).bodies.map fun
    | .jp j ps _ rec b k => .jp j ps (List.replicate 1000 0) rec b k
    | c => c
  match checkMapE F bad with
  | .error e => unless (e.splitOn "repeated captured variable").length > 1 do
      t := t.fail s!"fixed: repeated captured list refused for another reason: {e}"
  | .ok () => t := t.fail "fixed: a repeated captured list is accepted"
  -- a leak before `trap`: the canonical map with the parameter's decrement deleted
  let F := mkProg [0] .trap 1
  let leak : Src.NatMap Code := Src.NatMap.ofList [(0, .trap)]
  unless checkOwned F (Program.canonical F).bodies do t := t.fail "fixed: canonical trap map refused"
  unless checkOwned F leak do t := t.fail "fixed: a leak before trap is refused"
  -- an increment by two
  let F := mkProg [0] (.ret (.var 0)) 1
  let two : Src.NatMap Code := Src.NatMap.ofList [(0, .act (.inc 0 2) (.act (.dec 0) (.act (.dec 0) (.ret (.var 0)))))]
  if checkOwned F two then t := t.fail "fixed: an increment by two is accepted"
  return t

def run (count cap : Nat) : IO UInt32 := do
  let mut t : Totals := fixed {}
  let mut errors := 0
  for path in IxCCTests.Corpus.families do
    let fam ← IxCCTests.Corpus.Family.read path
    let dir : System.FilePath := fam.directory
    for fx in fam.fixtures do
      for r in fx.roots do
        if r.decline.isSome then continue
        let label := s!"{fam.family}/{fx.name}/{r.name}"
        try
          let (F, canonical, src, cfg) ← front (dir / fx.closure.path) (dir / fx.equations.path) r.name
          t := { t with policy := KeyIndex.checkProgram t.policy label src F }
          t := { t with stacking := IxCCTests.Xv.StackingLinear.checkRoot t.stacking label cfg.names cfg.env F canonical }
          t ← IO.lazyPure fun _ => root t label F canonical count cap
        catch e =>
          errors := errors + 1
          t := t.fail s!"{label}: front end: {e}"
  IO.println s!"roots {t.roots}: checkPlainMap accepts the canonical map {t.plainAccepted}, checkOwned {t.ownedAccepted}; checkOwned accepts the liveness map {t.liveAccepted}"
  IO.println s!"oracle runs of the unmutated maps {t.runs}"
  IO.println "control\tsites\trefused, stated reason\trefused, other reason\taccepted (oracle-checked)"
  for (k, a, b, c, d) in t.controls do IO.println s!"{k}\t{a}\t{b}\t{c}\t{d}"
  IO.println s!"site-directed campaign (COUNT {count} per root and map): generated {t.generated}, accepted {t.accepted}, accepted that change the cell RC traffic {t.heapChanging}; oracle runs {t.oracleRuns}"
  for (k, _, b, _, _) in t.controls do
    if b == 0 then t := t.fail s!"control {k}: never refused for its stated reason"
  if t.heapChanging == 0 then t := t.fail "the campaign accepted no mutant that changes the cell RC traffic"
  if t.roots == 0 then t := t.fail "no roots"
  let (scopeLines, scope) := ScopeSet.report (ScopeSet.synthetic t.scope)
  for l in scopeLines do IO.println l
  t := { t with failures := t.failures ++ scope.failures }
  let (policyLines, policy) := KeyIndex.report (KeyIndex.synthetic t.policy)
  for l in policyLines do IO.println l
  t := { t with failures := t.failures ++ policy.failures }
  let (stackLines, stackFailures) := IxCCTests.Xv.StackingLinear.report (IxCCTests.Xv.StackingLinear.synthetic t.stacking)
  for l in stackLines do IO.println l
  t := { t with failures := t.failures ++ stackFailures.toArray }
  for e in t.failures.toList.take 50 do IO.println s!"FAIL {e}"
  IO.println s!"{t.failures.size} failure(s), front-end errors {errors}"
  return if t.failures.isEmpty then 0 else 1

end IxCCTests.Own.Owned.Main

def main (args : List String) : IO UInt32 :=
  match args with
  | [] => IxCCTests.Own.Owned.Main.run 100 12
  | [count] => IxCCTests.Own.Owned.Main.run count.toNat! 12
  | [count, cap] => IxCCTests.Own.Owned.Main.run count.toNat! cap.toNat!
  | _ => do
    IO.eprintln "usage: tests-own-owned [COUNT [CAP]]"
    return 2
