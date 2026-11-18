import Ix.IxVM.ClaimHarness
import Ix.ClaimContext
import Ix.CompileCertified
import Lean.Replay
import Ix.EnvScope
import Ix.Shard.Environment
import Tests.Ix.IxVM.Harness

/-!
# Differential harness: IxVM against Lean's official kernel on a real corpus

For each constant of a corpus, compare IxVM's verdict (a `check` claim through
the program in circuit-verdict mode, `Tests.Ix.IxVM.Harness`) with Lean's
official kernel's. The records come from the certified compiler
(`Ix.CompileM.compileCertified`, which `ix compile` and `loadSharedIxonEnv`
use). The kernel is driven from this `Tests` module, by
`Lean.Kernel.Environment.replay`, which sends each declaration to the kernel
and checks that constructors and recursors match those it regenerates.

A corpus is a set of source-module prefixes (`IX_DIFF_MODULES`, comma-separated;
default `Init`), selecting the constants whose source module has one of those
prefixes, closed under dependencies. `IX_DIFF_LIMIT` caps how many constants the
IxVM side submits (0 = all), so a run fits a budget; the Lean side replays the
whole set regardless. `IX_DIFF_SEED` and `IX_DIFF_LIMIT` together take an evenly
spaced sample when the corpus exceeds the cap.

Output: a per-constant verdict table (printed by the host per case and
summarized here) and a summary line. Expected: agreement everywhere except the
known divergences — none for an honest corpus, since every constant Lean
accepts IxVM should accept, and the corpus holds nothing Lean rejects. An IxVM
rejection of a Lean-accepted constant, or the reverse, is a finding, recorded
with its Ixon fixture.

Lean's kernel replay skips unsafe and partial constants (it cannot check them);
those are reported as `lean-skipped` and compared only when IxVM also declines
to treat them as checked.
-/

namespace Tests.Ix.IxVM.Differential

open IxVM.ClaimHarness

/-- The corpus module prefixes (`IX_DIFF_MODULES`, default `Init`). -/
def corpusPrefixes : IO (List Lean.Name) := do
  let raw := (← IO.getEnv "IX_DIFF_MODULES").getD "Init"
  return (raw.splitOn ",").filterMap fun s =>
    let s := s.trimAscii.toString
    if s.isEmpty then none else some s.toName

/-- The constants of `leanEnv` whose source module has one of `prefixes`,
closed under dependencies (`collectSelectedDeps`). -/
def corpusConstants (leanEnv : Lean.Environment) (prefixes : List Lean.Name) :
    List (Lean.Name × Lean.ConstantInfo) := Id.run do
  let moduleNames := leanEnv.allImportedModuleNames
  let mut seeds : List Lean.Name := []
  for (n, _) in leanEnv.constants.toList do
    if let some idx := leanEnv.getModuleIdxFor? n then
      let mod := moduleNames[idx.toNat]!
      if prefixes.any (·.isPrefixOf mod) then seeds := n :: seeds
  return Ix.EnvScope.collectSelectedDeps leanEnv seeds

/-- Lean's official verdict on the corpus, by replay into a fresh kernel env:
`accept` for each installed constant, `skip` for the unsafe and partial ones
replay omits. Replay throws on the first rejection, naming the constant. -/
def leanVerdicts (_leanEnv : Lean.Environment)
    (constants : List (Lean.Name × Lean.ConstantInfo)) :
    IO (Std.HashMap Lean.Name Bool × Except String Unit) := do
  let newConstants : Std.HashMap Lean.Name Lean.ConstantInfo := constants.foldl
    (fun m (n, ci) => m.insert n ci) {}
  let verdicts : Std.HashMap Lean.Name Bool := constants.foldl
    (fun m (n, ci) => m.insert n (!ci.isUnsafe && !ci.isPartial)) {}
  let base := (← Lean.mkEmptyEnvironment).toKernelEnv
  try
    let _ ← Lean.Kernel.Environment.replay newConstants base
    return (verdicts, .ok ())
  catch e =>
    return (verdicts, .error (toString e))

/-- A constant is a leaf IxVM checks with a `check` claim (not a projection
wrapper: those are checked transitively with their block). -/
def isCheckTarget (c : Ixon.Constant) : Bool :=
  match c.info with
  | .iPrj _ | .cPrj _ | .rPrj _ | .dPrj _ => false
  | _ => true

/-- An evenly spaced sample of `xs` of size at most `limit` (0 = all). -/
def sample [Inhabited α] (xs : Array α) (limit seed : Nat) : Array α :=
  if limit == 0 || xs.size ≤ limit then xs
  else
    let step := xs.size / limit
    (Array.range limit).map fun i => xs[(seed + i * step) % xs.size]!

def run (leanEnv : Lean.Environment) : IO UInt32 := do
  let prefixes ← corpusPrefixes
  let limit := ((← IO.getEnv "IX_DIFF_LIMIT").bind String.toNat?).getD 0
  let seed := ((← IO.getEnv "IX_DIFF_SEED").bind String.toNat?).getD 0
  let constants := corpusConstants leanEnv prefixes
  IO.println s!"[ixvm-differential] corpus {prefixes}: {constants.length} constants (closed)"
  let started ← IO.monoMsNow
  let (lean, replayed) ← leanVerdicts leanEnv constants
  let leanOk ← match replayed with
    | .ok _ => pure true
    | .error e => do
      IO.eprintln s!"[ixvm-differential] Lean replay rejected a corpus constant: {e}"
      pure false
  let names := constants.map Prod.fst
  let ixon ← loadSharedIxonEnv names.toArray leanEnv
  IO.println s!"[ixvm-differential] compiled and replayed in {(← IO.monoMsNow) - started} ms"
  let ctx ← IO.ofExcept (Ix.ClaimContext.ofEnv ixon true)
  -- The check targets whose address is known and whose Lean verdict is accept.
  let mut targets : Array (Lean.Name × Address) := #[]
  for n in names do
    match ixon.getAddr? (Ix.Name.fromLeanName n) with
    | none => pure ()
    | some a =>
      match ixon.getConst? a with
      | some c => if isCheckTarget c && lean.getD n false then targets := targets.push (n, a)
      | none => pure ()
  let chosen := sample targets limit seed
  IO.println s!"[ixvm-differential] IxVM checks {chosen.size} of {targets.size} Lean-accepted check targets"
  -- A rejection by IxVM is a divergence: build each as a REQUIRED acceptance,
  -- so the host reports every constant it refuses.
  let builders : Array Builder := chosen.map fun (n, a) => fun _ => do
    return { label := s!"diff {n}", accept := true, witness := ← buildClaimWitness ixon (.check ctx a none) }
  let code ← Tests.Ix.IxVM.runCases "ixvm-differential" (circuit := some true) builders
  if code != 0 then
    IO.eprintln "[ixvm-differential] FINDING: IxVM diverged from Lean on a corpus constant \
      (an IxVM rejection of a Lean-accepted constant); see the FAILED lines above. Its fixture is \
      the compiled Ixon of the named constant's closure."
  IO.println s!"[ixvm-differential] summary: corpus {constants.length}, \
    Lean-accepted check targets {targets.size}, IxVM-checked {chosen.size}, \
    Lean replay {if leanOk then "ok" else "REJECTED"}, IxVM divergences {if code == 0 then 0 else 1}+"
  return if code == 0 && leanOk then 0 else 1

/-! ## On sharded `checkEnv` claims

Checking every constant as its own claim carries the constant's whole closure
in each witness, so a corpus the size of `Init` takes hours. The shard form
judges the corpus the way `ix check` and `ix prove` do: one `checkEnv` claim per
shard of a `.ixes` partition, its frontier assumed. The report gives the status of
every part each shard ran in (a shard that does not fit the budget is split into
parts). A part's owned constants pass when its status is `0`. Otherwise:

- a resource status (`resourceStatus`: 75, the plan does not fit the budget, or above
  128, the host was killed by a signal) establishes nothing: the part's blocks are
  `inconclusive`;
- any other status is a failure. The part's blocks are run again here, by halving, down
  to the single blocks IxVM rejects on their own (`reject`) or to the smallest set that
  fails while its halves each pass (`interaction`). What only the report says failed is
  run again before anything is attributed to it, a single block included: if it then
  passes, its blocks are `inconclusive`.

The blocks of a shard that no part of the report covers (a run without `--keep-going`
stops at a failure) are `inconclusive` as well. The outcomes stay distinct through the
table and the summary.

Inputs, from the environment:
- `IX_DIFF_IXE`, `IX_DIFF_IXES`: the compiled corpus and its partition;
- `IX_DIFF_REPORT`: the `ix-formal-run/1` report of
  `IX_AIUR_CIRCUIT_VERDICT=1 ix check --ixe … --ixes … --assume-binding --keep-going`
  on them (the IxVM verdict per shard, under the circuit verdict), or a
  comma-separated list of reports over disjoint `--shards` ranges;
- `IX_DIFF_LEAN=skip` (optional): no Lean verdicts, for a corpus that passed
  Lean's kernel when it was built (Mathlib): the run then reports IxVM's
  acceptance and the constants of the blocks it rejects;
- `IX_DIFF_OUT`: a directory for `table.tsv` (one row per named constant:
  name, address, shard, IxVM outcome, Lean verdict) and `summary.txt`.

Lean's verdict is the kernel's replay of the named constants' closure, as in
the per-constant form. A constant is a divergence when IxVM rejects its block on its
own and Lean accepts it; `unsafe` and `partial` constants, which replay does not check,
are `lean-skipped` and not compared, and names the test binary lacks are
`lean-absent`. With `IX_DIFF_LEAN=skip` every constant of a block IxVM rejects on its
own is reported. An interaction set or an inconclusive block fails the run as well; the
summary lists the sets and the inconclusive parts, and no constant of theirs is a
divergence. -/

def ixToLeanName : Ix.Name → Lean.Name
  | .anonymous _ => .anonymous
  | .str p s _ => .str (ixToLeanName p) s
  | .num p n _ => .num (ixToLeanName p) n

/-- A part status that establishes nothing about the claim: 75, the host's status when the
resource plan does not fit the budget (`Ix.Cli.FormalAiur.one`, and the resident prover's
record limit), or above 128, a host killed by a signal (the out-of-memory killer's, for
one). -/
def resourceStatus (status : Nat) : Bool := status == 75 || status > 128

/-- What the sharded differential concludes about a block that did not pass. -/
inductive Outcome where
  /-- IxVM rejects the block on its own: a run here rejected it alone. -/
  | reject
  /-- The block is in an interaction set: a set that a run here rejected, whose halves
  each pass. -/
  | interaction
  /-- Nothing is established: its part ran out of resources or was not run, or what the
  report says failed passed when it was run again. -/
  | inconclusive
  deriving BEq, Repr, Inhabited

def Outcome.label : Outcome → String
  | .reject => "reject"
  | .interaction => "interaction"
  | .inconclusive => "inconclusive"

/-- What a failing set of blocks comes to when it is run again by halving. -/
inductive Finding where
  | rejected (block : Address)
  | interaction (blocks : Array Address)
  | unreproduced (blocks : Array Address)
  deriving Inhabited

/-- IxVM's verdict on one owned set, under the circuit verdict: `ok` when the
program accepts the shard claim. -/
def shardAccepted (env : Ixon.Env) (label : String) (owned : Array Address) : IO Bool := do
  let code ← Tests.Ix.IxVM.runCases "ixvm-differential (bisect)" (circuit := some true) #[fun _ => do
    let (_, witness) ← buildShardCheckEnvWitness env owned (assumeBinding := true)
    return { label, accept := true, witness }]
  return code == 0

/-- `blocks`, a failing set of shard `k` that owns `owned`, run again by halving, with
`accepts` deciding an owned set. A set that failed in this process (`failed`) is not run
again. One that only the report says failed is, before anything is attributed to it:
when it is a single block, and when both its halves pass. -/
partial def bisect (env : Ixon.Env) (accepts : String → Array Address → IO Bool) (k : Nat)
    (blocks owned : Array Address) (failed : Bool) : IO (Array Finding) := do
  let some first := blocks[0]? | return #[]
  let label (part : Array Address) : String :=
    s!"shard {k} part {part.size} blocks from {part[0]!}"
  if blocks.size == 1 then
    if failed then return #[.rejected first]
    if ← accepts s!"{label blocks}, again" owned then return #[.unreproduced blocks]
    return #[.rejected first]
  let half := blocks.size / 2
  let parts := #[blocks.extract 0 half, blocks.extract half blocks.size]
  let owners := Ix.Shard.partitionOwned env owned parts
  let mut out : Array Finding := #[]
  for (part, i) in parts.zipIdx do
    let mine := owners[i]!
    if mine.isEmpty then continue
    unless ← accepts (label part) mine do
      out := out ++ (← bisect env accepts k part mine true)
  unless out.isEmpty do return out
  if failed then return #[.interaction blocks]
  if ← accepts s!"{label blocks}, again" owned then return #[.unreproduced blocks]
  return #[.interaction blocks]

/-- The parts of a report's leaves: per shard, each part's blocks and status. -/
def reportParts (leaves : Array Lean.Json) :
    Except String (Array (Nat × Array (Array Address × Nat))) :=
  leaves.mapM fun leaf => do
    let k ← leaf.getObjValAs? Nat "shard"
    let parts ← leaf.getObjValAs? (Array Lean.Json) "parts"
    let parts ← parts.mapM fun p => do
      let blocks ← (← p.getObjValAs? (Array String) "blocks").mapM fun s =>
        match Address.fromString s with
        | some a => pure a
        | none => throw s!"shard {k}: a part names the block {s}, which is not an address"
      return (blocks, ← p.getObjValAs? Nat "status")
    return (k, parts)

/-- What the parts of a report come to, by block. -/
structure Attribution where
  /-- every block that did not pass, with its outcome -/
  outcomes : Std.HashMap Address Outcome := {}
  /-- the shards with a part that did not pass, or with blocks no part covers -/
  shards : Array Nat := #[]
  /-- the interaction sets, with their shard -/
  interactions : Array (Nat × Array Address) := #[]
  /-- the parts with a resource status: their shard, blocks and status -/
  resource : Array (Nat × Array Address × Nat) := #[]
  /-- the failing sets that passed when run again, with their shard -/
  unreproduced : Array (Nat × Array Address) := #[]
  /-- the blocks no part covers, with their shard -/
  notRun : Array (Nat × Array Address) := #[]

/-- The number of blocks with outcome `o`. -/
def Attribution.count (a : Attribution) (o : Outcome) : Nat :=
  a.outcomes.fold (fun n _ x => if x == o then n + 1 else n) 0

/-- `a` with `blocks` given outcome `o`. -/
def Attribution.mark (a : Attribution) (blocks : Array Address) (o : Outcome) : Attribution :=
  { a with outcomes := blocks.foldl (fun m b => m.insert b o) a.outcomes }

/-- The outcome of every block of the report's `parts` (`reportParts`) that did not pass,
over the manifest's `shards` and their owned constants `owners`
(`Ix.Shard.ownedConstsPer`), with `accepts` running an owned set again. -/
def attribute (env : Ixon.Env) (accepts : String → Array Address → IO Bool)
    (shards owners : Array (Array Address)) (parts : Array (Nat × Array (Array Address × Nat))) :
    IO Attribution := do
  let mut a : Attribution := {}
  for (k, leaf) in parts do
    let (some shard, some owned) := (shards[k]?, owners[k]?)
      | throw (IO.userError s!"the report names shard {k}, which the manifest does not have")
    let covered : Std.HashSet Address := leaf.foldl (fun s (bs, _) => bs.foldl (·.insert ·) s) {}
    let notRun := shard.filter (!covered.contains ·)
    let mut passed := notRun.isEmpty
    unless notRun.isEmpty do
      a := { a.mark notRun .inconclusive with notRun := a.notRun.push (k, notRun) }
    for (blocks, status) in leaf do
      if status == 0 then continue
      passed := false
      if resourceStatus status then
        a := { a.mark blocks .inconclusive with resource := a.resource.push (k, blocks, status) }
        continue
      let mine := (Ix.Shard.partitionOwned env owned #[blocks])[0]!
      if mine.isEmpty then
        -- a part that owns nothing has nothing to run again
        a := { a.mark blocks .inconclusive with unreproduced := a.unreproduced.push (k, blocks) }
        continue
      for f in ← bisect env accepts k blocks mine false do
        match f with
        | .rejected b => a := a.mark #[b] .reject
        | .interaction bs =>
          a := { a.mark bs .interaction with interactions := a.interactions.push (k, bs) }
        | .unreproduced bs =>
          a := { a.mark bs .inconclusive with unreproduced := a.unreproduced.push (k, bs) }
    unless passed do a := { a with shards := a.shards.push k }
  return a

/-- The block of the record at `a`: a projection's block, or `a`. -/
def blockOf (env : Ixon.Env) (a : Address) : Address :=
  match env.getConst? a with
  | some c =>
    match (c.info : Ixon.ConstantInfo) with
    | .iPrj p => p.block
    | .cPrj p => p.block
    | .rPrj p => p.block
    | .dPrj p => p.block
    | _ => a
  | none => a

/-- A sharded run's table (`table.tsv`), its divergences, and its summary with the
interaction sets and the inconclusive parts (`summary.txt`). `names` are the named
constants; `lean` is Lean's verdict by name with whether its replay passed, or none when
Lean was not run. A divergence is a constant of a block IxVM rejects on its own that Lean
accepts, or, without Lean, any constant of such a block. -/
structure Tabulated where
  rows : Array String
  divergences : Array String
  summary : String
  details : Array String

def tabulate (env : Ixon.Env) (names : Array (Lean.Name × Address)) (owners : Array (Array Address))
    (a : Attribution) (lean : Option (Std.HashMap String String × Bool)) : Tabulated := Id.run do
  let mut shardOf : Std.HashMap Address Nat := {}
  for (owned, k) in owners.zipIdx do
    for x in owned do shardOf := shardOf.insert x k
  let mut rows : Array String := #["name\taddress\tshard\tixvm\tlean"]
  let mut divergences : Array String := #[]
  let mut skipped := 0
  let mut absent := 0
  let mut compared := 0
  let mut notOwned := 0
  for (n, x) in names do
    let shard := shardOf.get? x
    if shard.isNone then notOwned := notOwned + 1
    let ixvm := match shard with
      | none => "not-owned"
      | some _ => ((a.outcomes.get? (blockOf env x)).map Outcome.label).getD "accept"
    let leanV := match lean with
      | none => "not-checked"
      | some (table, _) => table.getD n.toString "lean-absent"
    match leanV with
    | "lean-skipped" => skipped := skipped + 1
    | "lean-absent" => absent := absent + 1
    | "not-checked" =>
      if ixvm == "reject" then divergences := divergences.push s!"{n}\t{x}\t{ixvm}\t{leanV}"
    | _ =>
      compared := compared + 1
      if ixvm == "reject" && leanV == "accept" then
        divergences := divergences.push s!"{n}\t{x}\t{ixvm}\t{leanV}"
    let shardS := match shard with | some k => toString k | none => "-"
    rows := rows.push s!"{n}\t{x}\t{shardS}\t{ixvm}\t{leanV}"
  let blocks (bs : Array Address) : String := ",".intercalate (bs.map toString).toList
  let mut details : Array String := #[]
  for (k, bs) in a.interactions do
    details := details.push s!"interaction\tshard {k}\t{bs.size} blocks\t{blocks bs}"
  for (k, bs, status) in a.resource do
    details := details.push s!"inconclusive\tshard {k}\tstatus {status}\t{blocks bs}"
  for (k, bs) in a.unreproduced do
    details := details.push s!"inconclusive\tshard {k}\tpassed when run again\t{blocks bs}"
  for (k, bs) in a.notRun do
    details := details.push s!"inconclusive\tshard {k}\tnot run\t{blocks bs}"
  let leanSummary := match lean with
    | none => "not run"
    | some (_, ok) => if ok then "ok" else "rejected"
  let summary := s!"shards {owners.size}; named constants {names.size} ({notOwned} not owned by \
    a shard); compared {compared}; lean-skipped {skipped}; lean-absent {absent}; shards with a \
    part that did not pass {a.shards.size}; blocks IxVM rejects on their own \
    {a.count .reject}; interaction sets {a.interactions.size} ({a.count .interaction} \
    blocks); inconclusive blocks {a.count .inconclusive} (parts with a resource status \
    {a.resource.size}, failing sets that passed when run again {a.unreproduced.size}, parts \
    not run {a.notRun.size}); {if lean.isNone then "IxVM-rejected constants" else "divergences"} \
    {divergences.size}; Lean replay {leanSummary}"
  return { rows, divergences, summary, details }

def runShards (leanEnv : Lean.Environment) : IO UInt32 := do
  let need (v : String) : IO String := do
    let some x ← IO.getEnv v | throw (IO.userError s!"{v} is not set")
    pure x
  let ixe ← need "IX_DIFF_IXE"
  let ixes ← need "IX_DIFF_IXES"
  let reportPath ← need "IX_DIFF_REPORT"
  let outDir := System.FilePath.mk (← need "IX_DIFF_OUT")
  IO.FS.createDirAll outDir
  let env ← IO.ofExcept (withDefaultRoleBinding (← IO.ofExcept (Ixon.deEnvAnon (← IO.FS.readBinFile ixe))))
  let view ← IO.ofExcept (Ix.Shard.parseIxesManifest (← IO.FS.readBinFile ixes))
  let owners := Ix.Shard.ownedConstsPer env view.shards
  -- IxVM: the status of every part of every leaf of the report.
  let mut leaves : Array Lean.Json := #[]
  for path in reportPath.splitOn "," do
    let report ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile path))
    leaves := leaves ++ (← IO.ofExcept (report.getObjValAs? (Array Lean.Json) "leaves"))
  let parts ← IO.ofExcept (reportParts leaves)
  let seen : Std.HashSet Nat := parts.foldl (fun s (k, _) => s.insert k) {}
  let missing := (List.range view.shards.size).filter (!seen.contains ·)
  unless missing.isEmpty do
    throw (IO.userError s!"the report has no verdict for shards {missing}")
  let a ← attribute env (shardAccepted env) view.shards owners parts
  IO.println s!"[ixvm-differential] {view.shards.size} shards, {owners.foldl (· + ·.size) 0} owned \
    constants; shards with a part that did not pass {a.shards}"
  -- Lean: a replay of the named constants' closure, unless `IX_DIFF_LEAN=skip`.
  let names : Array (Lean.Name × Address) := env.named.toArray.map fun (n, named) => (ixToLeanName n, named.addr)
  let skipLean := (← IO.getEnv "IX_DIFF_LEAN") == some "skip"
  let started ← IO.monoMsNow
  let mut lean : Option (Std.HashMap String String × Bool) := none
  unless skipLean do
    let present := names.filter fun (n, _) => leanEnv.constants.contains n
    let closure := Ix.EnvScope.collectSelectedDeps leanEnv (present.map (·.1)).toList
    let (verdicts, replayed) ← leanVerdicts leanEnv closure
    let leanOk := match replayed with | .ok _ => true | .error _ => false
    if let .error e := replayed then
      IO.eprintln s!"[ixvm-differential] Lean replay rejected a corpus constant: {e}"
    let mut table : Std.HashMap String String := {}
    for (n, _) in closure do
      table := table.insert n.toString
        (if verdicts.getD n false then (if leanOk then "accept" else "accept?") else "lean-skipped")
    IO.println s!"[ixvm-differential] Lean verdicts for {table.size} constants in \
      {(← IO.monoMsNow) - started} ms: {if leanOk then "replay ok" else "REPLAY REJECTED"}"
    lean := some (table, leanOk)
  let t := tabulate env names owners a lean
  IO.FS.writeFile (outDir / "table.tsv") ("\n".intercalate t.rows.toList ++ "\n")
  IO.FS.writeFile (outDir / "summary.txt")
    (t.summary ++ "\n" ++ "\n".intercalate (t.divergences ++ t.details).toList ++ "\n")
  IO.println s!"[ixvm-differential] summary: {t.summary}"
  for d in t.divergences.toList.take 20 do IO.println s!"  DIVERGENCE {d}"
  for d in t.details.toList.take 20 do IO.println s!"  {d}"
  let leanOk := (lean.map (·.2)).getD true
  return if t.divergences.isEmpty && leanOk && a.interactions.isEmpty &&
    a.count .inconclusive == 0 then 0 else 1

/-! ## The attribution, on a hand-made report

Eight standalone records `a` to `h`, each its own block, in a manifest of three shards:
`[a, b, c]`, `[d, e, f]` and `[g, h]`, and a fourth, `[i, j]`, of which the report
covers only `i`. The report's parts and statuses, and the verdicts of the runs here
(`accepts`: an owned set is rejected when it holds `d` or `f`, or both `a` and `b`):

- `[a, b]` failed, while `a` and `b` each pass: an interaction set, `a` and `b`
  `interaction`, after the pair failed again;
- `[c]` has status 75: `inconclusive`, and it is not run;
- `[d]` failed and fails again: `reject`;
- `[e, f]` failed: its half `[f]` is rejected, `f` `reject` and `e` passes;
- `[g]` failed but passes when run again: `inconclusive`;
- `[h]` and `[i]` passed; `j` was not run: `inconclusive`.

Lean accepts every constant, so the divergences are `d` and `f` alone. -/

/-- The attribution of the hand-made report, through the table and the summary. Throws on
the first difference. -/
def attributionChecks : IO Unit := do
  let fail (message : String) : IO Unit := throw (IO.userError message)
  let record (i : Nat) : Ixon.Constant :=
    ⟨.defn ⟨.defn, .safe, {}, i.toUInt64, .sort 0, .sort 0⟩, #[], #[], #[.zero], #[]⟩
  let env : Ixon.Env := (List.range 10).foldl (init := {}) fun env i =>
    env.storeConst (Address.blake3 (Ixon.ser (record i))) (record i)
  let addr (i : Nat) : Address := Address.blake3 (Ixon.ser (record i))
  let (ra, rb, rc, rd, re, rf, rg, rh, ri, rj) :=
    (addr 0, addr 1, addr 2, addr 3, addr 4, addr 5, addr 6, addr 7, addr 8, addr 9)
  let shards := #[#[ra, rb, rc], #[rd, re, rf], #[rg, rh], #[ri, rj]]
  let owners := Ix.Shard.ownedConstsPer env shards
  let part (blocks : Array Address) (status : Nat) : Lean.Json := Lean.Json.mkObj [
    ("blocks", Lean.toJson (blocks.map toString)), ("status", Lean.toJson status)]
  let leaf (k : Nat) (parts : Array Lean.Json) : Lean.Json :=
    Lean.Json.mkObj [("shard", Lean.toJson k), ("parts", Lean.toJson parts)]
  let report := #[
    leaf 0 #[part #[ra, rb] 1, part #[rc] 75],
    leaf 1 #[part #[rd] 1, part #[re, rf] 1],
    leaf 2 #[part #[rg] 1, part #[rh] 0],
    leaf 3 #[part #[ri] 0]]
  let runs ← IO.mkRef (#[] : Array (Array Address))
  let accepts (_ : String) (owned : Array Address) : IO Bool := do
    runs.modify (·.push owned)
    return !(owned.contains rd || owned.contains rf || (owned.contains ra && owned.contains rb))
  let parts ← IO.ofExcept (reportParts report)
  let a ← attribute env accepts shards owners parts
  let names : Array (Lean.Name × Address) :=
    #[(`a, ra), (`b, rb), (`c, rc), (`d, rd), (`e, re), (`f, rf), (`g, rg), (`h, rh), (`i, ri), (`j, rj)]
  let lean : Std.HashMap String String := names.foldl (fun m (n, _) => m.insert n.toString "accept") {}
  let t := tabulate env names owners a (some (lean, true))
  let expected := #[("a", "interaction"), ("b", "interaction"), ("c", "inconclusive"),
    ("d", "reject"), ("e", "accept"), ("f", "reject"), ("g", "inconclusive"), ("h", "accept"),
    ("i", "accept"), ("j", "inconclusive")]
  unless t.rows.size == expected.size + 1 do fail s!"the table has {t.rows.size} rows"
  for ((n, outcome), row) in expected.zip (t.rows.extract 1 t.rows.size) do
    match row.splitOn "\t" with
    | [name, _, _, ixvm, "accept"] =>
      unless name == n && ixvm == outcome do
        fail s!"the table says {ixvm} for {name}, expected {outcome} for {n}"
    | _ => fail s!"a row of the table does not read: {row}"
  let diverging := t.divergences.map fun d => (d.splitOn "\t").headD ""
  unless diverging == #["d", "f"] do
    fail s!"the divergences are {diverging}, expected d and f"
  unless a.interactions.map (·.2) == #[#[ra, rb]] && a.resource.map (·.2.2) == #[75] &&
      a.unreproduced.map (·.2) == #[#[rg]] && a.notRun.map (·.2) == #[#[rj]] &&
      a.shards == #[0, 1, 2, 3] do
    fail "the attribution's sets are not the expected ones"
  -- `[c]` is not run; `[d]` and `[g]` are run again; the pair is run again after its halves
  let ran ← runs.get
  if ran.contains #[rc] then fail "the part with status 75 was run"
  unless ran.contains #[rd] && ran.contains #[rg] && ran.contains #[ra] && ran.contains #[rb] &&
      ran.any (fun r => r.size == 2 && r.contains ra && r.contains rb) do
    fail s!"{ran.size} runs, without a run again of each failing set"
  for s in ["blocks IxVM rejects on their own 2", "interaction sets 1 (2 blocks)",
      "inconclusive blocks 3", "divergences 2"] do
    unless (t.summary.splitOn s).length > 1 do
      fail s!"the summary does not say {s}: {t.summary}"
  for s in ["interaction\tshard 0", "inconclusive\tshard 0\tstatus 75",
      "inconclusive\tshard 2\tpassed when run again", "inconclusive\tshard 3\tnot run"] do
    unless t.details.any (·.startsWith s) do
      fail s!"the summary's details have no line {s}"

def runAttribution : IO UInt32 := do
  try
    attributionChecks
    IO.println "[ixvm-differential-attribution] an isolated rejection, an interaction set and \
      inconclusive parts stay distinct through the table and the summary"
    return 0
  catch e =>
    IO.eprintln s!"[ixvm-differential-attribution] {e}"
    return 1

end Tests.Ix.IxVM.Differential
