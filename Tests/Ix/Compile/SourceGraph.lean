import Ix.Meta
import Ix.EnvScope
import Ix.CompileDriver
import Ix.Cert.SourcePrepass
import Tests.Ix.Compile.GroundRefusal
import Tests.Ix.Compile.SourceAccounting
import Lean.Elab.Command

namespace Tests.Ix.Compile.SourceGraph
open _root_.Ix.Compile.SourceGraph

-- The live wrapper must use the proved producer, not a duplicate inline loop.
run_cmd do
  let some (.defnInfo d) := (← Lean.getEnv).find? `Ix.CompileM.compileDecoratedConsts
    | throwError "IO compiler definition unavailable"
  let used := d.value.getUsedConstantsAsSet
  for n in [`Ix.Compile.SourceGraph.Prepass.run, `Ix.Compile.SourceGraph.Stream.runLabelled] do
    unless used.contains n do throwError "IO compiler does not call {n}"
  if used.contains `Ix.CanonM.chunks then throwError "IO compiler retained the unproved partition"

private def need (ok : Bool) (why : String) : IO Unit := unless ok do throw (IO.userError why)
private def groupEq : Grouping → Grouping → Bool
  | .plain, .plain => true
  | .induct a, .induct b | .recursor a, .recursor b => a.isEqv b _root_.Ix.Name.beqRaw
  | _, _ => false
private def nodeEq (a b : Node) : Bool :=
  a.literals == b.literals && groupEq a.grouping b.grouping &&
    a.direct.size == b.direct.size && a.direct.toArray.all b.direct.contains
private def compile (raw : List (Lean.Name × Lean.ConstantInfo)) (workers : Nat) :
    IO _root_.Ix.CompileM.LeanPipelineOut := do
  IO.ofExcept (← _root_.Ix.CompileM.compileLeanConsts raw (numWorkers := workers))

private def facts (raw : List (Lean.Name × Lean.ConstantInfo)) (workers : Nat)
    (out : _root_.Ix.CompileM.LeanPipelineOut) : IO Unit := do
  let input ← IO.ofExcept ((_root_.Ix.Compile.CompileInput.fromAnnotations raw).mapError toString)
  let prepared ← IO.ofExcept input.prepare
  let (_, expected) := Prepass.produce prepared.toArray workers
  let some actual := out.sourceNodes? | throw (IO.userError "successful IO result omitted source facts")
  need (actual.size == expected.facts.nodes.size) "source graph domain size differs"
  for (n, expectedNode) in expected.facts.nodes do
    let some node := actual.get? n | throw (IO.userError s!"source graph omitted {n.pretty}")
    need (nodeEq node expectedNode && decide (actual.getKey? n = expected.facts.nodes.getKey? n))
      s!"source graph changed facts or representative at {n.pretty}"
  need (out.cenv.env.consts.size == expected.facts.code.size) "kept fields differ"
  need (out.digests.size == expected.digests.size && expected.digests.toList.all
    (fun (n, d) => out.digests.get? n == some d)) "input digests differ"

private def reference (raw : List (Lean.Name × Lean.ConstantInfo))
    (out : _root_.Ix.CompileM.LeanPipelineOut) : IO Unit := do
  let input ← IO.ofExcept ((_root_.Ix.Compile.CompileInput.fromAnnotations raw).mapError toString)
  let prepared ← IO.ofExcept input.prepare
  let consts := (_root_.Ix.CanonM.canonChunk prepared.toArray).foldl
    (fun m (n, ci) => m.insert n ci) ({} : _root_.Ix.Map _root_.Ix.Name _root_.Ix.ConstantInfo)
  let (expected, failures) ← IO.ofExcept (_root_.Ix.Cert.compileReport { consts })
  let bytes ← IO.ofExcept (Ixon.serEnv expected)
  need (out.bytes == bytes && failures.toMap.size == out.cenv.ungrounded.size &&
    failures.toMap.toList.all (fun (n, e) => out.cenv.ungrounded.get? n == some e))
    "public pipeline differs from materialized reference"

private def simple (name : Lean.Name) : Lean.ConstantInfo := .defnInfo
  { name, levelParams := [], type := .sort (.succ .zero), value := .sort .zero,
    hints := .abbrev, safety := .safe, all := [name] }
private def opaqueNat : Lean.ConstantInfo := .opaqueInfo
  { name := `SourceFacts.o, levelParams := [], type := .const `Nat [], value := .lit (.natVal 7),
    isUnsafe := false, all := [`SourceFacts.o] }
private def theoremTrue : Lean.ConstantInfo := .thmInfo
  { name := `SourceFacts.t, levelParams := [], type := .const `True [], value := .const `True.intro [],
    all := [`SourceFacts.t] }
private def failedDef : Lean.ConstantInfo := .defnInfo
  { name := `SourceFacts.bad, levelParams := [], type := .sort (.succ .zero),
    value := .const `SourceFacts.absent [], hints := .abbrev, safety := .safe, all := [`SourceFacts.bad] }

def run : IO UInt32 := do
  let empty ← compile [] 0
  facts [] 0 empty
  reference [] empty
  need (empty.sourceNodes?.any (·.isEmpty)) "empty input was confused with unavailable facts"
  let unavailable : _root_.Ix.CompileM.LeanPipelineOut :=
    { bytes := empty.bytes, env := empty.env, cenv := empty.cenv,
      ungroundedCount := 0, blockCount := 0 }
  need unavailable.sourceNodes?.isNone "missing facts became an empty graph"
  let env ← getCompileEnv #[`Init]
  let support := _root_.Ix.EnvScope.collectDeps env [`True.rec, `Nat.rec]
  let d := simple `SourceFacts.d
  let raw := support ++ [(d.name, d), (opaqueNat.name, opaqueNat), (theoremTrue.name, theoremTrue)]
  let base ← compile raw 1
  facts raw 1 base
  reference raw base
  need base.cenv.ungrounded.isEmpty "ordinary source-facts fixture failed compilation"
  let some nodes := base.sourceNodes? | throw (IO.userError "source facts absent")
  let opaqueName := _root_.Ix.Name.fromLeanName opaqueNat.name
  need ((nodes.get? opaqueName).any (·.literals == .nat) && !base.cenv.env.consts.contains opaqueName &&
    (base.cenv.env.get? opaqueName).any (fun | .opaqueInfo _ => true | _ => false))
    "streamed opaque facts/fallback retention differs"
  let theoremName := _root_.Ix.Name.fromLeanName theoremTrue.name
  need (nodes.contains theoremName && !base.cenv.env.consts.contains theoremName &&
    (base.cenv.env.get? theoremName).any (fun | .thmInfo _ => true | _ => false))
    "streamed theorem facts/fallback retention differs"
  let natName := _root_.Ix.Name.fromLeanName `Nat
  need ((nodes.get? natName).any (fun n => groupEq n.grouping (.induct #[natName])) &&
    (nodes.get? (_root_.Ix.Name.fromLeanName `Nat.rec)).any
      (fun n => groupEq n.grouping (.recursor #[natName]))) "inductive/recursor grouping changed"
  for workers in [0, 2, 8] do
    let out ← compile raw workers
    facts raw workers out
    need (out.bytes == base.bytes && out.cenv.ungrounded.isEmpty) s!"public pipeline differs at {workers} workers"
  -- Forced labels exercise stored representatives at the helper seam;
  -- they do not claim a collision among canonName outputs.
  let h : Address := ⟨⟨Array.replicate 32 7⟩⟩
  let first : _root_.Ix.Name := .str (.anonymous h) "first" h
  let last : _root_.Ix.Name := .str (.anonymous h) "last" h
  for workers in [0, 1, 2, 8] do
    let out := Stream.runLabelled { consts := (Prepass.run raw.toArray).thinConsts }
      #[(first, d), (last, opaqueNat)] workers
    need (decide (out.facts.nodes.getKey? first = some last) &&
      decide (out.outRefs.getKey? first = some last) && decide (out.digests.getKey? first = some last) &&
      out.facts.code.isEmpty) "streamed alias winner or stored representative changed"
  let brokenRaw := [(failedDef.name, failedDef)]
  let broken ← compile brokenRaw 2
  facts brokenRaw 2 broken
  let bad := _root_.Ix.Name.fromLeanName failedDef.name
  let absent := _root_.Ix.Name.fromLeanName `SourceFacts.absent
  need (broken.cenv.ungrounded.get? bad == some
    "UNGROUNDED-INPUT: references SourceFacts.absent, which is not in the input") "ground refusal changed"
  let some badNodes := broken.sourceNodes? | throw (IO.userError "failure lost original facts")
  need ((badNodes.get? bad).any (·.direct.contains absent) && !badNodes.contains absent)
    "failed input or missing endpoint was erased/fabricated"
  let refusalEnv ← getCompileEnv #[`Tests.Ix.Compile.GroundRefusal]
  let refusalRaw := GroundRefusal.closure refusalEnv (· == `Nat.add)
  let refusal ← compile refusalRaw 2
  facts refusalRaw 2 refusal
  let some refusalNodes := refusal.sourceNodes? | throw (IO.userError "transitive failure lost facts")
  for (name, message) in GroundRefusal.expected do
    let key := _root_.Ix.Name.fromLeanName name.toName
    need (refusal.cenv.ungrounded.get? key == some message && refusalNodes.contains key)
      s!"ground refusal or original facts changed at {name}"
  need (!refusalNodes.contains (_root_.Ix.Name.fromLeanName `Nat.add)) "missing dependency acquired a node"
  -- A native prepared-input control with many streamed bodies. The shared
  -- original Lean body is intentional; only the compact facts survive canon.
  let body := (List.range 64).foldl (fun e _ =>
    Lean.Expr.letE `x (.sort (.succ .zero)) (.sort .zero) e false) (.sort .zero)
  let many := (List.range 128).map fun i =>
    let name := Lean.Name.num `SourceFacts.stream i
    let ci : Lean.ConstantInfo := .opaqueInfo
      { name, levelParams := [], type := .sort (.succ .zero), value := body,
        isUnsafe := false, all := [name] }
    (name, ci)
  let streamed ← compile many 8
  facts many 8 streamed
  need (streamed.cenv.ungrounded.isEmpty && streamed.cenv.env.consts.isEmpty)
    "streamed-body control retained canonical code or failed"
  SourceAccounting.run
  IO.println "source graph IO: complete/empty/failure facts; materialized reference; worker bytes; streamed fallback; digests/counts"
  return 0

end Tests.Ix.Compile.SourceGraph
