import IxCC.Recheck.Rc.Produce
import IxCCTests.Recheck.Rc.ReplayIO
import IxCCTests.Own.Owned.Live
import IxCCTests.Own.Owned.Mutate

/-! # Ownership certificates other than the canonical one, through the verifier

Since heap stage 2's second milestone, certificate admission (`Own.Plain.Certificate.admit`) runs the
ownership checker (`Own.Plain.checkOwned`), which judges any placement of `inc`/`dec`, behind the
captured-work budget (`Anf.maxCapturedWork`). Against the complete verifier (`RcReplay.run`) and
native runs of the objects it validates:

* **a correct placement other than the canonical one** (the liveness producer's, `Live`, untrusted)
  of each RC real-source root: the old check (`checkPlainMap`) refuses it, the verifier admits it,
  its object differs from the canonical certificate's and returns every expected value (each case's
  heap high water printed beside the canonical object's);
* **each of the six kinds of wrong placement** (`Mutate`): refused at admission with the checker's
  own reason, `own.cert.check: ownership proposal refused: <reason>`;
* **the two cases the canonical producer never emits**, each in an admitted certificate whose
  object runs correctly: an `inc`/`dec` pair on an immediate, and the `inc` of a projected
  (borrowed) variable moved past the next binding;
* **the budget** (`fixtures/rc/budget`): past the limit, the plain-RC producer refuses with
  `own.cert.budget` (the measured work and the limit in the message), a certificate made by hand
  is refused by the verifier with it, and the automatic policy compiles under the immortal policy
  carrying that reason; within the limit, plain RC compiles, verifies and runs; acceptance at two
  budgets around the measured work (`admit_mono`, `checkBudget_ok`). -/

set_option autoImplicit false
namespace IxCCTests.Recheck.Rc.OwnedIO
open IxCC Lean System
open IxCC.Own.Plain (Code Alt Ctx bindCtx)
open IxCCTests.Recheck.Rc.Fixtures

def fail {α : Type} (msg : String) : IO α := throw (IO.userError msg)

/-- The plain-RC certificate for any ownership map: `finishPlainRcCert` with `bodies` in place of
the canonical map and without its admission (test-only and untrusted: the verifier decides). -/
def finishWith (cfg : Recheck.Config) (front : Recheck.RcReplay.ProducedFir)
    (bodies : Src.NatMap Code) : Except Recheck.Err Recheck.RcReplay.Cert := do
  let some candidate := Cfg.Rc.generate front.fir bodies |
    throw { stage := .rt, code := "rc.cfg", message := "ownership candidate lowering declined" }
  let lowered ← (Cfg.Rc.Public.lower { names := cfg.names } front.fir bodies candidate).mapError
    fun message => { stage := .rt, code := "rc.lower", message }
  let reps : Lir.FunId → Option (List Xv.Stacking.ArgRep) :=
    (⟨lowered.runtime, lowered.drop⟩ : Cfg.Rc.Public.Lowered).reps
  let layout : Cfg.Rc.Native.Layout :=
    ⟨candidate.base.size, candidate.base.ctors.filter (fun c => c.arity > 0)⟩
  let rcEnv := layout.env cfg.env
  let (xv, _) ← (Xv.Select.run lowered.runtime.program).mapError Recheck.Err.ofSelect
  let allocated ← (Xv.Alloc.runProducer rcEnv xv).mapError fun message =>
    { stage := .alloc, code := "alloc.fallback", message }
  let frames := Xv.Stacking.produce allocated.program
  let stacked ← (Xv.Stacking.run allocated.program frames reps rcEnv).mapError
    (Recheck.Err.ofBackend ∘ .stacking)
  let order := X86.Layout.Order.produce (X86.Layout.tunnel stacked.program) stacked.shape
  pure { base := { table := front.tableCert, relevance := front.relevance, mid := front.mid
                   alloc := allocated.outs, frames, order }
         own := Own.Plain.Certificate.encode bodies }

/-! ## Edits at the first site the checker's context allows (threaded as `Mutate` threads it) -/

mutual
/-- The first node, in order, for which `edit` (given the checker's context there) proposes a
replacement; the map with that one node replaced. -/
partial def editCode (edit : Ctx → Code → Option Code) (Γ : Ctx) (c : Code) : Option Code :=
  match edit Γ c with
  | some c' => some c'
  | none =>
    match c with
    | .act (.inc x n) k => match Γ.inc x n with
      | .ok Γ' => (editCode edit Γ' k).map (.act (.inc x n))
      | .error _ => none
    | .act (.dec x) k => match Γ.dec x with
      | .ok Γ' => (editCode edit Γ' k).map (.act (.dec x))
      | .error _ => none
    | .bind x r k => match bindCtx Γ x r with
      | .ok Γ' => (editCode edit Γ' k).map (.bind x r)
      | .error _ => none
    | .jp j ps captured rec body k =>
      match editCode edit (Γ.enter captured ps) body with
      | some body' => some (.jp j ps captured rec body' k)
      | none => (editCode edit Γ k).map fun k' => .jp j ps captured rec body k'
    | .case x alts d =>
      match editAlts edit Γ alts with
      | some alts' => some (.case x alts' d)
      | none => match d with
        | some dc => (editCode edit Γ dc).map fun dc' => .case x alts (some dc')
        | none => none
    | _ => none
partial def editAlts (edit : Ctx → Code → Option Code) (Γ : Ctx) : List Alt → Option (List Alt)
  | [] => none
  | .mk key b :: rest => match editCode edit Γ b with
    | some b' => some (.mk key b' :: rest)
    | none => (editAlts edit Γ rest).map (.mk key b :: ·)
end

/-- `inc y; dec y` before the first binding that reads an immediate `y` (no heap effect). -/
def immediatePair (Γ : Ctx) : Code → Option Code
  | c@(.bind _ r _) =>
    ((IxCCTests.Own.Owned.rhsUses r).find? Γ.isImm).map fun y => .act (.inc y 1) (.act (.dec y) c)
  | _ => none

/-- `x := proj y; inc x; z := r; k` becomes `x := proj y; z := r; inc x; k` when `r` is not a call
and does not read `x`: `x` stays borrowed across the binding of `z`, then is incremented. -/
def borrowedLate (_ : Ctx) : Code → Option Code
  | .bind x (.proj y i n) (.act (.inc x' 1) (.bind z r k)) =>
    let isCall := match r with | .call .. => true | _ => false
    if x' == x && !isCall && !(IxCCTests.Own.Owned.rhsUses r).contains x then
      some (.bind x (.proj y i n) (.bind z r (.act (.inc x 1) k)))
    else none
  | _ => none

/-- The map with the first edit of the first function, in function order, that has one. -/
def editMap (F : Fir.Program) (m : Src.NatMap Code) (edit : Ctx → Code → Option Code) :
    Option (Src.NatMap Code) :=
  (List.range F.size).findSome? fun f => do
    let fd ← F.fun? f
    let body ← m.get? f
    let body' ← editCode edit (Ctx.entry (fd.params.map (·.1))) body
    return m.insert f body'

/-! ## Native runs -/

/-- Link an admitted certificate's object and run its root on `cases`: every value must be
`want`'s, by the printed observation and by the memory readback. Returns each case's heap high
water (the bump pointer past the arena's start, in bytes). -/
def runNative (logs : FilePath) (label : String) (artifact : Recheck.RcReplay.Artifact)
    (cases : List (List Nat)) (want : List Nat → Sem.Obs) : IO (List Nat) := do
  let some entry := artifact.roots.head? | fail s!"{label}: missing root"
  let some (sig, ty) := entry.ty | fail s!"{label}: missing result signature"
  let exe ← IxCCTests.Rt.Native.link { work := logs } s!"owned-{label}" artifact.backend.object
    entry.symbol
  let rows ← IxCCTests.Rt.Native.run exe
    { region := 131072, stack := 1048576, ty := some (sig, ty), dump := true } cases
  unless rows.length == cases.length do fail s!"{label}: {rows.length} rows for {cases.length} cases"
  for (args, row) in cases.zip rows do
    let w := want args
    unless row.status == 0 && row.ok && row.obs == some (Rt.renderObs w) &&
        row.readback 131072 sig ty == some w do
      fail s!"{label} {args}: native value differs from the reference"
  return rows.map fun row => (row.dump.map fun d => (d.bump - d.start).toNat).getD 0

def listCases (root : String) : List (List Nat) :=
  if root == "reverseRepeated" then [[0, 9], [1, 2], [5, 7], [64, 3]]
  else [[0, 7], [1, 42], [4, 3], [7, 0], [32, 11], [128, 100]]

def listWant (root : String) : List Nat → Sem.Obs
  | [n, seed] => ReplayIO.expected root n seed
  | _ => .ctor 0 []

structure Front where
  input : Recheck.Input
  cfg : Recheck.Config
  front : Recheck.RcReplay.ProducedFir
  canonical : Src.NatMap Code

def front (root : String) : IO Front := do
  let input ← source root
  let cfg := (ReplayIO.config root).forInput input
  let front ← IO.ofExcept ((Recheck.RcReplay.produceFir cfg input).mapError (·.render))
  return { input, cfg, front, canonical := (Own.Plain.Program.canonicalForSrc front.src front.fir).bodies }

/-- Admit `m` through the complete verifier and run its object; returns the artifact. -/
def admitAndRun (logs : FilePath) (label root : String) (fr : Front) (m : Src.NatMap Code) :
    IO Recheck.RcReplay.Artifact := do
  let cert ← IO.ofExcept ((finishWith fr.cfg fr.front m).mapError (·.render))
  let artifact ← IO.ofExcept ((Recheck.RcReplay.run fr.cfg fr.input.program cert).mapError
    fun e => s!"{label}: the verifier refused: {e.render}")
  let _ ← runNative logs label artifact (listCases root) (listWant root)
  return artifact

/-! ## The tests -/

/-- A correct placement other than the canonical one: refused by the old check, admitted, and its
object (another than the canonical certificate's) returns every value; each case's heap high water
is printed beside the canonical object's. -/
def liveness (logs : FilePath) : IO Unit := do
  for root in roots do
    let fr ← front root
    let live := IxCCTests.Own.Owned.liveMap fr.front.fir
    if Own.Plain.bodyMapEq live fr.canonical then fail s!"{root}: the liveness map is the canonical map"
    if Own.Plain.checkPlainMap fr.front.fir live then
      fail s!"{root}: the canonical check accepts the liveness map"
    let cert ← IO.ofExcept ((finishWith fr.cfg fr.front live).mapError (·.render))
    let artifact ← IO.ofExcept ((Recheck.RcReplay.run fr.cfg fr.input.program cert).mapError
      fun e => s!"{root}: the verifier refused the liveness placement: {e.render}")
    let (_, canonicalArt) ← IO.ofExcept ((Recheck.RcReplay.produce (ReplayIO.config root) fr.input).mapError
      (·.render))
    if canonicalArt.backend.object == artifact.backend.object then
      fail s!"{root}: the liveness certificate's object is the canonical certificate's"
    let liveHigh ← runNative logs s!"live-{root}" artifact (listCases root) (listWant root)
    let canonHigh ← runNative logs s!"canonical-{root}" canonicalArt (listCases root) (listWant root)
    IO.println s!"PASS liveness placement {root}: refused by the old check, admitted, another object, {(listCases root).length} values; heap high water (bytes) {liveHigh}, canonical {canonHigh}"

/-- Each kind of wrong placement is refused at admission with the checker's reason. -/
def wrongPlacements : IO Unit := do
  let fronts ← roots.mapM fun root => return (root, ← front root)
  for kind in IxCCTests.Own.Owned.Kind.all do
    let mut found : Option String := none
    for (root, fr) in fronts do
      if found.isSome then break
      let F := fr.front.fir
      let live := IxCCTests.Own.Owned.liveMap F
      for (mname, m) in [("canonical", fr.canonical), ("liveness", live)] do
        if found.isSome then break
        for f in List.range F.size do
          if found.isSome then break
          let some fd := F.fun? f | continue
          let some body := m.get? f | continue
          for target in List.range 64 do
            let some body' := IxCCTests.Own.Owned.mutant kind target (fd.params.map (·.1)) body | break
            let m' := m.insert f body'
            let .error reason := Own.Plain.checkMapE F m' | continue
            unless kind.expected reason do continue
            let canonicalCert ← IO.ofExcept ((Recheck.RcReplay.produce (ReplayIO.config root) fr.input).mapError
              (·.render))
            let cert := { canonicalCert.1 with own := Own.Plain.Certificate.encode m' }
            match Recheck.RcReplay.run fr.cfg fr.input.program cert with
            | .ok _ => fail s!"{kind.name} ({root}, {mname}, f{f}, site {target}): the verifier accepted a wrong placement"
            | .error e =>
              let want := s!"own.cert.check: ownership proposal refused: {reason}"
              unless e.stage == .cert && e.code == "own.plain" && e.message == want do
                fail s!"{kind.name}: expected {want}, got {e.render}"
              found := some s!"{root} {mname} f{f} site {target}: {reason}"
            break
    match found with
    | some what => IO.println s!"PASS wrong placement {kind.name} refused at admission ({what})"
    | none => fail s!"{kind.name}: no site of the RC real-source roots gives this refusal"

/-- The two placements the canonical producer never emits, admitted, and their objects run. -/
def neverEmitted (logs : FilePath) : IO Unit := do
  for (label, edit) in [("immediate-inc-dec", immediatePair), ("borrowed-late-inc", borrowedLate)] do
    let mut done := false
    for root in roots do
      if done then break
      let fr ← front root
      for (mname, m) in [("canonical", fr.canonical),
          ("liveness", IxCCTests.Own.Owned.liveMap fr.front.fir)] do
        if done then break
        let some m' := editMap fr.front.fir m edit | continue
        unless Own.Plain.checkOwned fr.front.fir m' do continue
        let artifact ← admitAndRun logs s!"{label}-{root}" root fr m'
        let base ← IO.ofExcept ((finishWith fr.cfg fr.front m).mapError (·.render))
        let baseArt ← IO.ofExcept ((Recheck.RcReplay.run fr.cfg fr.input.program base).mapError (·.render))
        let same := baseArt.backend.object == artifact.backend.object
        IO.println s!"PASS {label} ({root}, {mname} map edited): admitted, {(listCases root).length} values; object {if same then "identical to" else "differs from"} the unedited map's"
        done := true
    unless done do fail s!"{label}: no site of the RC real-source roots is accepted"

/-! ## The budget -/

def budgetDir : FilePath := "fixtures/rc/budget"

/-- `fanUnder` and `fanOver` (`Fan.lean`): each the sum of forty-one fan functions whose `C`
parameters (197 and 198), all passed `n`, are live across a tree of 127 leaves on `s`, leaf `lo` of
the `j`-th returning `lo + 10000·j`; the pair of that sum and `s`. -/
def fanFunctions : Nat := 41
def fanLeaves : Nat := 127
def fanBindings (root : String) : Nat := if root == "fanOver" then 198 else 197

def fanWant (root : String) : List Nat → Sem.Obs
  | [n, s] =>
    .ctor 0 [.nat (fanFunctions * (min s (fanLeaves - 1) + fanBindings root * n) + 8610000), .nat s]
  | _ => .ctor 0 []

def fanCases : List (List Nat) := [[0, 0], [1, 5], [7, 100], [100, 126], [3, 5000]]

def budgetSource (root : String) : IO Recheck.Input := do
  let bytes ← IO.FS.readBinFile (budgetDir / "anonymous.ixe")
  let equations ← IO.ofExcept (Json.parse (← IO.FS.readFile (budgetDir / "consumer.equations.json")))
  IO.ofExcept ((Recheck.ingress bytes equations ["IxCCTests.Own.Budget." ++ root]).mapError (·.message))

def budget (logs : FilePath) : IO Unit := do
  let guard ← IO.Process.output {
    cmd := "sha256sum", args := #["--status", "--check", (budgetDir / "manifest.sha256").toString] }
  unless guard.exitCode == 0 do fail "RC budget input fixture identity changed"
  let limit := Anf.maxCapturedWork
  -- past the limit
  let input ← budgetSource "fanOver"
  let cfg0 : Recheck.Config := { names := ["fanOver"] }
  let cfg := cfg0.forInput input
  let fr ← IO.ofExcept ((Recheck.RcReplay.produceFir cfg input).mapError (·.render))
  let canonical := (Own.Plain.Program.canonicalForSrc fr.src fr.fir).bodies
  let work := Own.Plain.Certificate.capturedWork canonical
  unless work > limit do fail s!"fanOver: captured work {work} is within the limit {limit}"
  let .error want := Own.Plain.Certificate.checkBudget limit canonical | fail "fanOver: within budget"
  unless (want.splitOn s!"take {work} captured tokens").length > 1 &&
      (want.splitOn s!"past the limit {limit}").length > 1 do
    fail s!"fanOver: the budget refusal does not name the work and the limit: {want}"
  let refusedWith (label : String) (r : Except Recheck.Err Unit) : IO Unit := do
    match r with
    | .ok () => fail s!"{label}: accepted past the budget"
    | .error e =>
      unless e.stage == .cert && e.code == "own.plain" && e.message == want do
        fail s!"{label}: expected cert/own.plain: {want}, got {e.render}"
  refusedWith "fanOver --rc on" ((Recheck.RcReplay.produce cfg0 input).map fun _ => ())
  let handMade ← IO.ofExcept ((finishWith cfg fr canonical).mapError (·.render))
  refusedWith "fanOver hand-made certificate" ((Recheck.RcReplay.run cfg input.program handMade).map fun _ => ())
  match ← IO.ofExcept ((Recheck.RcReplay.produceAuto cfg0 input).mapError (·.render)) with
  | .immortal _ artifact _ reason =>
    unless reason.stage == .cert && reason.code == "own.plain" && reason.message == want do
      fail s!"fanOver --rc auto: fell back for another reason: {reason.render}"
    let some entry := artifact.roots.head? | fail "fanOver: missing root"
    let some (sig, ty) := entry.ty | fail "fanOver: missing result signature"
    let exe ← IxCCTests.Rt.Native.link { work := logs } "budget-fanOver-immortal" artifact.backend.object
      entry.symbol
    let rows ← IxCCTests.Rt.Native.run exe
      { region := 131072, stack := 1048576, ty := some (sig, ty), dump := true } fanCases
    for (args, row) in fanCases.zip rows do
      unless row.status == 0 && row.ok && row.obs == some (Rt.renderObs (fanWant "fanOver" args)) do
        fail s!"fanOver immortal {args}: native value differs"
  | .plainRc .. | .zeroRc .. => fail "fanOver --rc auto: did not fall back to the immortal policy"
  IO.println s!"PASS budget past the limit (fanOver, work {work} > {limit}): plain RC refused, hand-made certificate refused, auto immortal with the reason and correct values"
  -- within the limit
  let input ← budgetSource "fanUnder"
  let cfg0 : Recheck.Config := { names := ["fanUnder"] }
  let cfg := cfg0.forInput input
  let (cert, artifact) ← IO.ofExcept ((Recheck.RcReplay.produce cfg0 input).mapError (·.render))
  let fr ← IO.ofExcept ((Recheck.RcReplay.produceFir cfg input).mapError (·.render))
  let bodies ← IO.ofExcept (Own.Plain.Certificate.decode fr.fir cert.own)
  let work := Own.Plain.Certificate.capturedWork bodies
  unless work ≤ limit && work + fanFunctions * (fanLeaves + 1) > limit do
    fail s!"fanUnder: captured work {work} is not just within the limit {limit}"
  let _ ← runNative logs "budget-fanUnder" artifact fanCases (fanWant "fanUnder")
  match Own.Plain.Certificate.admit fr.fir cert.own (work - 1) with
  | .ok _ => fail "fanUnder: admitted under a budget below its work"
  | .error e => unless e.startsWith "own.cert.budget: " do fail s!"fanUnder: budget {work - 1}: {e}"
  let some p := (Own.Plain.Certificate.admit fr.fir cert.own work).toOption |
    fail "fanUnder: refused at a budget equal to its work"
  let some p' := (Own.Plain.Certificate.admit fr.fir cert.own limit).toOption |
    fail "fanUnder: refused at the default budget"
  unless Own.Plain.bodyMapEq p.bodies p'.bodies && Own.Plain.bodyMapEq p.bodies bodies do
    fail "fanUnder: admitted as different programs at two budgets"
  IO.println s!"PASS budget within the limit (fanUnder, work {work} ≤ {limit}): compiles, verifies, {fanCases.length} values; refused at budget {work - 1}, the same program admitted at {work} and {limit}"

/-! ## A join's captured list reordered -/

/-- The first join whose captured list has two or more variables, with that list reversed. -/
def capturedReversed (_ : Ctx) : Code → Option Code
  | .jp j ps captured rec body k =>
    if captured.length ≥ 2 then some (.jp j ps captured.reverse rec body k) else none
  | _ => none

/-- The checker treats a join's captured list as a set, so a certificate whose captured list is
reordered is admitted. End to end, on the first program with such a join (the RC real-source roots,
then the budget input's `fanUnder`): with the canonical certificate's backend decisions the verifier
either validates an object or refuses at a backend stage (the decisions were made for the other
order); with decisions made for the reordered map it validates an object; every validated object
returns every expected value. Which of these happens is printed; observed (2026-11-12): the RC
real-source roots have no join capturing two variables, and on `fanUnder` the reordered certificate is
validated with the canonical decisions and with its own, the object identical to the canonical one's
each time (the captured order does not reach the lowered code), every value right. -/
def capturedOrder (logs : FilePath) : IO Unit := do
  let mut programs : List (String × Front × List (List Nat) × (List Nat → Sem.Obs)) := []
  for root in roots do
    programs := programs ++ [(root, ← front root, listCases root, listWant root)]
  let input ← budgetSource "fanUnder"
  let cfg := ({ names := ["fanUnder"] } : Recheck.Config).forInput input
  let fr ← IO.ofExcept ((Recheck.RcReplay.produceFir cfg input).mapError (·.render))
  let budgetFront : Front :=
    { input := input, cfg := cfg, front := fr,
      canonical := (Own.Plain.Program.canonicalForSrc fr.src fr.fir).bodies }
  programs := programs ++ [("fanUnder", budgetFront, fanCases, fanWant "fanUnder")]
  let mut done := false
  for (root, fr, cases, want) in programs do
    if done then break
    let some m' := editMap fr.front.fir fr.canonical capturedReversed | continue
    unless Own.Plain.checkOwned fr.front.fir m' do
      fail s!"{root}: a reordered captured list is refused by the checker"
    let cfg0 : Recheck.Config := { names := fr.cfg.names }
    let (canonicalCert, canonicalArt) ← IO.ofExcept ((Recheck.RcReplay.produce cfg0 fr.input).mapError
      (·.render))
    let swapped := { canonicalCert with own := Own.Plain.Certificate.encode m' }
    let withCanonicalDecisions ← match Recheck.RcReplay.run fr.cfg fr.input.program swapped with
      | .ok art => do
        let _ ← runNative logs s!"order-canonical-decisions-{root}" art cases want
        pure s!"validated, object {if art.backend.object == canonicalArt.backend.object then "identical to" else "different from"} the canonical one, values right"
      | .error e => pure s!"refused at {e.stage.name}/{e.code}"
    let fresh ← IO.ofExcept ((finishWith fr.cfg fr.front m').mapError (·.render))
    let art ← IO.ofExcept ((Recheck.RcReplay.run fr.cfg fr.input.program fresh).mapError
      fun e => s!"{root}: the reordered map with its own decisions was refused: {e.render}")
    let _ ← runNative logs s!"order-fresh-decisions-{root}" art cases want
    IO.println s!"PASS reordered captured list ({root}): admitted; with the canonical backend decisions {withCanonicalDecisions}; with its own decisions validated, object {if art.backend.object == canonicalArt.backend.object then "identical to" else "different from"} the canonical one, {cases.length} values right"
    done := true
  unless done do fail "no program with a join capturing two or more variables"

def run (logs : FilePath) : IO Unit := do
  IO.FS.createDirAll logs
  liveness logs
  wrongPlacements
  neverEmitted logs
  budget logs
  capturedOrder logs
  IO.FS.writeFile (logs / "owned-result.txt")
    "Ownership certificates other than the canonical one: a liveness placement admitted and run, six wrong placements refused with the checker's reason, the two never-emitted cases admitted and run, the captured-work budget past and within the limit, a reordered captured list admitted and run.\n"

end IxCCTests.Recheck.Rc.OwnedIO
