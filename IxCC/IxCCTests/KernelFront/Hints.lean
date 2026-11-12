import IxCCTests.Src.Support
import IxCCTests.Support.Envelope
import IxCC.Recheck.Produce
import IxCC.Recheck.Json

/-! # The artifact's reducibility hints at the kernel front end

The front end hands the kernel's tiered entry and its reading the artifact's
own reducibility hints (`KernelFront.HintTable.of`, `AcceptedFrom`). Hints are
advice about unfolding order: no theorem depends on them, and the kernel's
work does. On `fixtures/ixon-v4/kernel-hints/` (`KernelHints.lean`):

* **the regression**: the closure holding the minimal reproducer
  (`allOnesXor`: `(allOnes 16 ^^^ y).toNat = Nat.xor 65535 y.toNat := rfl`)
  and the `complement` word equations at widths 16, 32 and 64, which the
  kernel checks in time exponential in the width without the hints
  (`IxCC/plans/aiur-backend/KERNEL-NOTES.md`, section 10), is accepted within
  `acceptBoundMs` (measured: about half a second);
* **the hint function the statements name is the one the code runs**: on
  every constant reference of the closure (every definition, every member of
  every block, a constructor of every block), `HintTable.lookup` of the
  accepted hints agrees with a second reading (`independentHint`: the
  projection records found by IxCC's own decoder instead of the kernel's, the
  hints section searched as a list), a block member's hint found under its
  projection record's address (the fixture's `partial` pair); and every
  definition the kernel's reader produced carries the hint that second reading
  gives its address, wherever it gives one.

Then **hostile and missing hints, through the front end** (`Recheck.ingress`,
`produce`, `run`, each case in a child process with a time limit): the hints
section removed, every hint regular at height 0, every hint `abbrev`, every
hint `opaque`, and the regular heights inverted, on `phase1-scalar`'s `tuple`,
`bench-k1`'s `fib` and the kernel-hints fixture. Each case ends in the honest
case's object and certificate (byte for byte) or in a clean decline at the
kernel (outcome *declined*, never *rejected*), and on the kernel-hints
fixture it may also run out of its time limit, where the kernel without good
hints is exponential (the kernel's to bound): a hint never produces a
different acceptance. The times are printed. -/

namespace IxCCTests.KernelFront.Hints

open IxCC IxCC.Src
open IxCCTests.Src (Assert expect)

abbrev KAddr := KernelFront.KAddr

/-- The kernel-hints fixture's stem and root. -/
def fixtureStem : String := "fixtures/ixon-v4/kernel-hints/hints"
def fixtureRoot : String := "KernelHints.root"

/-- The bound on the kernel-hints fixture's acceptance with its hints (measured about 0.5 s on
the build box; the room is for a loaded runner). -/
def acceptBoundMs : Nat := 30000

/-- The hint of a constant reference, read a second way: the definition projection records found
by IxCC's own decoder (`Ixon.V3.decodeConstant`; `HintTable.of` reads the kernel's canonical
decoding), the hints section searched as a list, its code read by cases. -/
def independentHint (projections : List (Ixon.Address × Ixon.Address × Nat))
    (hints : List (Ixon.Address × UInt64)) (r : Ix.Kernel.ConstRef KAddr) :
    Option Ix.Kernel.ReducibilityHint := do
  let target : KAddr := match r with
    | .member b i =>
      match projections.find? fun (_, blk, j) => KernelFront.kaddr blk == b && j == i with
      | some (p, _, _) => KernelFront.kaddr p
      | none => b
    | .ctor b _ _ => b
  let (_, code) ← hints.find? fun (a, _) => KernelFront.kaddr a == target
  match code.toNat with
  | 0 => some .opaque
  | 1 => some .abbrev
  | n + 2 => some (.regular n)

/-- The definition projection records of an environment, by IxCC's own decoder:
`(projection, block, index)`. -/
def projectionsOf (env : Ixon.V3.Env) : List (Ixon.Address × Ixon.Address × Nat) :=
  env.consts.toList.filterMap fun (a, bytes) =>
    match Ixon.V3.decodeConstant bytes with
    | .ok c => match c.value.info with
      | .dPrj q => some (a, q.block, q.idx.toNat)
      | _ => none
    | .error _ => none

/-- Every constant reference of the closure: each record as a block's member `0`, each member of
each block, and a constructor of each block. -/
def refsOf (env : Ixon.V3.Env) : List (Ix.Kernel.ConstRef KAddr) :=
  env.consts.toList.flatMap fun (a, bytes) =>
    let b := KernelFront.kaddr a
    match Ixon.V3.decodeConstant bytes with
    | .ok c => match c.value.info with
      | .muts ms => (List.range ms.size).map (Ix.Kernel.ConstRef.member b) ++ [Ix.Kernel.ConstRef.ctor b 0 0]
      | _ => [Ix.Kernel.ConstRef.member b 0]
    | .error _ => [Ix.Kernel.ConstRef.member b 0]

def showRef : Ix.Kernel.ConstRef KAddr → String
  | .member b i => s!"member {i} of {b}"
  | .ctor b i c => s!"constructor {c} of member {i} of {b}"

/-! ## Hostile hints -/

/-- The hints section rewritten: `removed`, every hint `zero` (regular at height 0), `abbrev`,
`opaque`, or `inverted` (regular heights mirrored, the others kept); `honest` unchanged. -/
def mutate (m : String) (env : Ixon.V3.Env) : Ixon.V3.Env :=
  let top := env.hints.foldl (fun t (_, h) => if h ≥ 2 then max t h else t) 2
  match m with
  | "removed" => { env with hints := #[] }
  | "zero" => { env with hints := env.hints.map fun (a, _) => (a, 2) }
  | "abbrev" => { env with hints := env.hints.map fun (a, _) => (a, 1) }
  | "opaque" => { env with hints := env.hints.map fun (a, _) => (a, 0) }
  | "inverted" => { env with hints := env.hints.map fun (a, h) => (a, if h ≥ 2 then top + 2 - h else h) }
  | _ => env

def mutations : List String := ["removed", "zero", "abbrev", "opaque", "inverted"]

/-- One case (the child process): the closure at `stem` with its hints mutated, through
ingress, the producer and `Recheck.run` for `root`; one JSON line. -/
def caseMain (stem root mutation : String) : IO UInt32 := do
  let bytes ← IO.FS.readBinFile s!"{stem}.ixe"
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile s!"{stem}.equations.json"))
  let env ← IO.ofExcept (Ixon.V3.decodeAnonymousEnv bytes)
  let some b := env.binding | throw (IO.userError s!"{stem}: not role-bound")
  let env' := mutate mutation env
  let bytes' := if mutation == "original" then bytes
    else IxCCTests.Support.Envelope.envelope env' (some (b.address, b.bytes))
  let t0 ← IO.monoMsNow
  let hash := fun (x : ByteArray) => toString (Ixon.Address.blake3Pure x)
  let out : List (String × Lean.Json) ← match Recheck.ingress bytes' json [root] with
    | .error e =>
      let outcome := if e.code != "kernel" then "-" else
        match KernelFront.accept env' with
        | .error r => match r.outcome with
          | some .declined => "declined" | some .rejected => "rejected" | none => "none"
        | .ok _ => "accepted"
      pure [("status", .str "refused"), ("stage", .str e.stage.name), ("code", .str e.code),
        ("outcome", .str outcome), ("message", .str (toString (e.message.take 300)))]
    | .ok k =>
      let cfg : Recheck.Config := { names := [root] }
      match Recheck.produce cfg k with
      | .error e => pure [("status", .str "produce-refused"), ("code", .str e.code)]
      | .ok cert =>
        match Recheck.run cfg k.program cert with
        | .error e => pure [("status", .str "run-refused"), ("code", .str e.code)]
        | .ok a => pure [("status", .str "compiled"), ("object", .str (hash a.object)),
            ("cert", .str (hash cert.toText.toUTF8))]
  let ms := (← IO.monoMsNow) - t0
  IO.println (Lean.Json.mkObj (out ++ [("ms", Lean.toJson ms)])).compress
  return 0

/-- Run one case in a child process (`tests-kernel-front hint-case …`), killed after `limitMs`:
its JSON line, or `none` when it ran out of time. -/
def runCase (stem root mutation : String) (limitMs : Nat) : IO (Option Lean.Json × Nat) := do
  let t0 ← IO.monoMsNow
  let self ← IO.appPath
  let child ← IO.Process.spawn
    { cmd := self.toString, args := #["hint-case", stem, root, mutation], stdout := .piped,
      stderr := .null }
  let mut done := false
  while !done do
    if (← child.tryWait).isSome then done := true
    else if (← IO.monoMsNow) - t0 ≥ limitMs then
      child.kill
      let _ ← child.wait
      return (none, (← IO.monoMsNow) - t0)
    else IO.sleep 50
  let out ← child.stdout.readToEnd
  let line := (out.splitOn "\n").find? (·.startsWith "{")
  let some line := line | throw (IO.userError s!"{stem} {mutation}: no result from the child: {out}")
  return (some (← IO.ofExcept (Lean.Json.parse line)), (← IO.monoMsNow) - t0)

def str (j : Lean.Json) (k : String) : String := (j.getObjValAs? String k).toOption.getD ""

/-- The cases: the closure, its root, the time limit per case, and whether a case may run out of
it (only where the kernel is exponential without good hints). -/
def cases : List (String × String × Nat × Bool) :=
  [("fixtures/corpus/phase1-scalar/tuple", "entry", 300000, false),
   ("fixtures/ixon-v4/bench-k1/fib", "entry", 300000, false),
   (fixtureStem, fixtureRoot, 20000, true)]

def run (a : Assert) : IO Unit := do
  -- the regression
  let bytes ← IO.FS.readBinFile s!"{fixtureStem}.ixe"
  let env ← IO.ofExcept (Ixon.V3.decodeAnonymousEnv bytes)
  let t0 ← IO.monoMsNow
  let acc ← match KernelFront.accept env with
    | .ok acc => pure acc
    | .error e => throw (IO.userError s!"kernel-hints: the kernel refused the closure: {e}")
  let ms := (← IO.monoMsNow) - t0
  expect a (ms ≤ acceptBoundMs)
    s!"kernel-hints: the kernel's acceptance took {ms} ms, over the bound of {acceptBoundMs} ms"
  expect a (acc.records.length == env.consts.size)
    s!"kernel-hints: the kernel's entry did not receive every record"
  IO.println s!"  kernel-hints: accepted with its hints in {ms} ms ({acc.records.length} records, \
    {env.hints.size} hints)"
  -- the hint function, read a second way
  let projections := projectionsOf env
  let hints := env.hints.toList
  let refs := refsOf env
  let mut withHint := 0
  let mut viaProjection := 0
  for r in refs do
    let mine := acc.hints.lookup r
    let theirs := independentHint projections hints r
    expect a (mine == theirs) s!"kernel-hints: the hint of {showRef r} is {repr mine}, read again {repr theirs}"
    if mine.isSome then withHint := withHint + 1
    if let .member blk i := r then
      if mine.isSome && projections.any (fun (_, b, j) => KernelFront.kaddr b == blk && j == i) then
        viaProjection := viaProjection + 1
  expect a (viaProjection ≥ 2)
    s!"kernel-hints: {viaProjection} block members' hints found under their projection records, expected the partial pair's two"
  -- the reader's declarations carry those hints
  let hintAt := fun (k : KAddr) => (hints.find? fun (x, _) => KernelFront.kaddr x == k).map fun (_, c) =>
    KernelFront.hintOfCode c
  let mut carried := 0
  for d in acc.readDecls do
    if let .defnDecl cv _ h := d then
      if let .id k := cv.name then
        if let some h' := hintAt k then
          expect a (h == h') s!"kernel-hints: the reader gave {k} the hint {repr h}, the artifact's is {repr h'}"
          carried := carried + 1
  expect a (carried ≥ 1) "kernel-hints: no definition of the reading carries an artifact hint"
  IO.println s!"  hint lookups agree with a second reading on {refs.length} references ({withHint} with a \
    hint, {viaProjection} through a projection record); {carried} definitions read with the artifact's hint"
  -- hostile and missing hints, through the front end
  for (stem, root, limit, mayTimeOut) in cases do
    let (honest?, hms) ← runCase stem root "honest" limit
    let some honest := honest? | throw (IO.userError s!"{stem}: the honest case ran out of {limit} ms")
    expect a (str honest "status" == "compiled") s!"{stem}: the honest case did not compile: {honest.compress}"
    let (orig?, _) ← runCase stem root "original" limit
    expect a ((orig?.map fun o => (str o "object", str o "cert")) == some (str honest "object", str honest "cert"))
      s!"{stem}: the re-encoded closure compiles to another object or certificate than the committed one"
    let mut line := s!"  {stem}: honest {hms} ms"
    for m in mutations do
      let (r?, rms) ← runCase stem root m limit
      match r? with
      | none =>
        expect a mayTimeOut s!"{stem}, hints {m}: no answer in {limit} ms"
        line := line ++ s!"; {m} over {limit} ms (no answer)"
      | some r =>
        match str r "status" with
        | "compiled" =>
          expect a (str r "object" == str honest "object" && str r "cert" == str honest "cert")
            s!"{stem}, hints {m}: a different acceptance: {r.compress} against {honest.compress}"
          line := line ++ s!"; {m} the same object and certificate in {rms} ms"
        | "refused" =>
          expect a (str r "code" == "kernel" && str r "outcome" == "declined")
            s!"{stem}, hints {m}: not a clean decline: {r.compress}"
          line := line ++ s!"; {m} declined by the kernel in {rms} ms"
        | _ => throw (IO.userError s!"{stem}, hints {m}: refused after ingress: {r.compress}")
    IO.println line

end IxCCTests.KernelFront.Hints
