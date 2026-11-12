import MultiStark.BN.Program
import Aiur.Optimized.Grouping.Snapshot

/-! Profile-guided grouping uses only function names as a policy. Every exported
layout is certified against the freshly compiled source program. -/
open Aiur Aiur.Optimized Lean
private abbrev F := MultiStark.BN.F
private instance : ToJson F := ⟨fun value => toJson value.val⟩

private def ident (snapshot : Grouping.Snapshot F) (name : String) : Except String Nat :=
  if snapshot.callables.contains name then .ok (snapshot.callables.idxOf name)
  else .error s!"unknown callable {name}"

private def maxDegree (ps : List (Optimized.Polynomial F)) : Nat :=
  ps.foldl (fun n p => max n p.simplify.degree) 0

private def metrics (snapshot : Grouping.Snapshot F) (origin : Circuit.Chip F) : Except String Json := do
  let chip := Activation.compile origin
  let (provided, required) ← Grouping.messages (ident snapshot) chip
  let privateCols ← Grouping.privateColumns chip origin.numVars (provided ++ required.flatMap (·.args))
  let select := Grouping.selectArgument origin.numVars privateCols
  let lifted := ((provided ++ required.flatMap (·.args)).filter fun p => (select p).degree > 2).dedup
  let degree := fun ps => maxDegree (ps.map fun p => if (select p).degree > 2 then .var 0 else select p)
  let constraints := (Grouping.member chip origin.numVars privateCols).constraints
  return Json.mkObj [
    ("name", toJson origin.name), ("width", toJson chip.numVars),
    ("private", toJson privateCols.length), ("shared", toJson (chip.numVars - privateCols.length)),
    ("lifted", toJson lifted.length), ("private_columns", toJson privateCols),
    ("constraint_degree", toJson (max (maxDegree constraints) (if lifted.isEmpty then 2 else 3))),
    ("lookups", toJson ((degree provided, (1 : Nat)) :: required.map (fun s => (degree s.args, s.enable.degree))))]

def main (args : List String) : IO Unit := do
  let entries := if args.contains "--compress" then [MultiStark.BN.compressionEntry] else [MultiStark.BN.verifierEntry]
  match args with
  | "prepare" :: snapshotPath :: metricsPath :: artifactPath :: _ =>
    let prepared ← IO.ofExcept (Modules.prepare MultiStark.BN.program entries)
    let exported ← IO.ofExcept prepared.exportExecution
    let specialized ← IO.ofExcept (Generic.specialize prepared.environment.source prepared.entries)
    let inlined ← IO.ofExcept (Inlining.prepare specialized.program specialized.inlineNames prepared.entries)
    let artifact ← IO.ofExcept (Trace.compileParallel inlined.program prepared.entries {})
    let physical ← IO.ofExcept (Physical.prepare artifact)
    let cfg ← IO.ofExcept (Trace.depthConfig MultiStark.BN.modulus physical)
    let snapshot := Grouping.Snapshot.capture artifact physical cfg
      (exported.bytecode.functions.map (·.name) ++ exported.bytecode.maps.map (·.name)) []
    IO.FS.writeFile snapshotPath ((toJson snapshot).compress ++ "\n")
    let chips ← IO.ofExcept (snapshot.chips.mapM (metrics snapshot))
    IO.FS.writeFile metricsPath ((Json.mkObj [("chips", toJson chips), ("groups", toJson snapshot.groups),
      ("entries", toJson snapshot.entries), ("representatives", toJson snapshot.representatives)]).compress ++ "\n")
    let (exported, trace) ← IO.ofExcept (Trace.exportPreparedPlanWithEncoding .wide
      MultiStark.BN.modulus ZMod.val inlined.program artifact physical exported)
    let bytes ← IO.ofExcept (Artifact.packageWide exported MultiStark.BN.modulus ZMod.val (some trace))
    Artifact.write artifactPath bytes
    IO.println s!"BN254 grouping baseline: {snapshot.chips.length} chips; {bytes.size} bytes"
  | "export" :: artifactPath :: policyPath :: _ =>
    let policy : List (String × List String) ← IO.ofExcept (fromJson? (← IO.ofExcept (Json.parse (← IO.FS.readFile policyPath))))
    let bytes ← MultiStark.BN.compilePackage true entries policy
    Artifact.write artifactPath bytes
    IO.println s!"Certified BN254 grouping export: {bytes.size} bytes"
  | _ => throw (IO.userError "usage: bn_grouping prepare SNAPSHOT METRICS ARTIFACT [--compress] | export ARTIFACT POLICY [--compress]")
