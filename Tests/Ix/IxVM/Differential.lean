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
shard of a `.ixes` partition, its frontier assumed. A shard's verdict is its
owned constants' verdict. A shard IxVM rejects is bisected by blocks, down to
the single blocks it rejects (or to the smallest set whose halves each pass,
an interaction), and only those are reported per constant.

Inputs, from the environment:
- `IX_DIFF_IXE`, `IX_DIFF_IXES`: the compiled corpus and its partition;
- `IX_DIFF_REPORT`: the `ix-formal-run/1` report of
  `IX_AIUR_CIRCUIT_VERDICT=1 ix check --ixe … --ixes … --assume-binding --keep-going`
  on them (the IxVM verdict per shard, under the circuit verdict);
- `IX_DIFF_OUT`: a directory for `table.tsv` (one row per named constant:
  name, address, shard, IxVM verdict, Lean verdict) and `summary.txt`.

Lean's verdict is the kernel's replay of the named constants' closure, as in
the per-constant form. A constant is a divergence when IxVM's verdict differs
from Lean's; `unsafe` and `partial` constants, which replay does not check, are
`lean-skipped` and not compared, and names the test binary lacks are
`lean-absent`. -/

def ixToLeanName : Ix.Name → Lean.Name
  | .anonymous _ => .anonymous
  | .str p s _ => .str (ixToLeanName p) s
  | .num p n _ => .num (ixToLeanName p) n

/-- IxVM's verdict on one owned set, under the circuit verdict: `ok` when the
program accepts the shard claim. -/
def shardAccepted (env : Ixon.Env) (label : String) (owned : Array Address) : IO Bool := do
  let code ← Tests.Ix.IxVM.runCases "ixvm-differential (bisect)" (circuit := some true) #[fun _ => do
    let (_, witness) ← buildShardCheckEnvWitness env owned (assumeBinding := true)
    return { label, accept := true, witness }]
  return code == 0

/-- The blocks of a rejected block list that IxVM rejects on their own, by
halving; when both halves pass, the whole list is reported (an interaction). -/
partial def bisect (env : Ixon.Env) (k : Nat) (blocks : Array Address) (owned : Array Address) :
    IO (Array (Array Address)) := do
  if blocks.size ≤ 1 then return #[blocks]
  let half := blocks.size / 2
  let parts := #[blocks.extract 0 half, blocks.extract half blocks.size]
  let owners := Ix.Shard.partitionOwned env owned parts
  let mut out := #[]
  for (part, i) in parts.zipIdx do
    let mine := owners[i]!
    if mine.isEmpty then continue
    unless (← shardAccepted env s!"shard {k} part {part.size} blocks from {part[0]!}" mine) do
      out := out ++ (← bisect env k part mine)
  return if out.isEmpty then #[blocks] else out

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
  let report ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile reportPath))
  let leaves ← IO.ofExcept (report.getObjValAs? (Array Lean.Json) "leaves")
  let mut rejectedShards : Array Nat := #[]
  let mut seen : Std.HashSet Nat := {}
  for leaf in leaves do
    let k ← IO.ofExcept (leaf.getObjValAs? Nat "shard")
    seen := seen.insert k
    let parts ← IO.ofExcept (leaf.getObjValAs? (Array Lean.Json) "parts")
    let ok := parts.all fun p => (p.getObjValAs? Nat "status").toOption == some 0
    unless ok do rejectedShards := rejectedShards.push k
  let missing := (List.range view.shards.size).filter (!seen.contains ·)
  unless missing.isEmpty do
    throw (IO.userError s!"the report has no verdict for shards {missing}")
  IO.println s!"[ixvm-differential] {view.shards.size} shards, {owners.foldl (· + ·.size) 0} owned \
    constants; IxVM rejected shards {rejectedShards}"
  -- Bisect the rejected shards.
  let mut rejectedBlocks : Std.HashSet Address := {}
  let mut interactions : Array (Nat × Nat) := #[]
  for k in rejectedShards do
    let found ← bisect env k view.shards[k]! owners[k]!
    for bs in found do
      if bs.size > 1 then interactions := interactions.push (k, bs.size)
      for b in bs do rejectedBlocks := rejectedBlocks.insert b
  -- The block each owned constant belongs to, and its shard.
  let blockOf (a : Address) : Address :=
    match env.getConst? a with
    | some c =>
      match (c.info : Ixon.ConstantInfo) with
      | .iPrj p => p.block
      | .cPrj p => p.block
      | .rPrj p => p.block
      | .dPrj p => p.block
      | _ => a
    | none => a
  let mut shardOf : Std.HashMap Address Nat := {}
  for (owned, k) in owners.zipIdx do
    for a in owned do shardOf := shardOf.insert a k
  -- Lean: replay the named constants' closure.
  let names : Array (Lean.Name × Address) := env.named.toArray.map fun (n, named) => (ixToLeanName n, named.addr)
  let present := names.filter fun (n, _) => leanEnv.constants.contains n
  let closure := Ix.EnvScope.collectSelectedDeps leanEnv (present.map (·.1)).toList
  let started ← IO.monoMsNow
  let (lean, replayed) ← leanVerdicts leanEnv closure
  let leanOk := match replayed with | .ok _ => true | .error _ => false
  if let .error e := replayed then
    IO.eprintln s!"[ixvm-differential] Lean replay rejected a corpus constant: {e}"
  IO.println s!"[ixvm-differential] Lean replayed {closure.length} constants in \
    {(← IO.monoMsNow) - started} ms: {if leanOk then "all accepted" else "REJECTED"}"
  -- Join.
  let mut rows : Array String := #["name\taddress\tshard\tixvm\tlean"]
  let mut divergences : Array String := #[]
  let mut skipped := 0
  let mut absent := 0
  let mut compared := 0
  let mut notOwned := 0
  for (n, a) in names do
    let shard := shardOf.get? a
    let shardS := match shard with | some k => toString k | none => "-"
    if shard.isNone then notOwned := notOwned + 1
    let ixvm := match shard with
      | none => "not-owned"
      | some k => if rejectedShards.contains k && rejectedBlocks.contains (blockOf a) then "reject"
        else "accept"
    let leanV := if !leanEnv.constants.contains n then "lean-absent"
      else match lean.get? n with
        | some true => if leanOk then "accept" else "accept?"
        | some false => "lean-skipped"
        | none => "lean-absent"
    match leanV with
    | "lean-skipped" => skipped := skipped + 1
    | "lean-absent" => absent := absent + 1
    | _ =>
      compared := compared + 1
      if ixvm != "not-owned" && leanV != "accept?" && ixvm != leanV then divergences := divergences.push s!"{n}\t{a}\t{ixvm}\t{leanV}"
    rows := rows.push s!"{n}\t{a}\t{shardS}\t{ixvm}\t{leanV}"
  IO.FS.writeFile (outDir / "table.tsv") ("\n".intercalate rows.toList ++ "\n")
  let summary := s!"shards {view.shards.size}; named constants {names.size} ({notOwned} not owned by a shard); compared {compared}; \
    lean-skipped {skipped}; lean-absent {absent}; IxVM-rejected shards {rejectedShards.size}; \
    interaction sets {interactions.size}; divergences {divergences.size}; Lean replay \
    {if leanOk then "ok" else "rejected"}"
  IO.FS.writeFile (outDir / "summary.txt") (summary ++ "\n" ++ "\n".intercalate divergences.toList ++ "\n")
  IO.println s!"[ixvm-differential] summary: {summary}"
  for d in divergences.toList.take 20 do IO.println s!"  DIVERGENCE {d}"
  return if divergences.isEmpty && leanOk && interactions.isEmpty then 0 else 1

end Tests.Ix.IxVM.Differential
