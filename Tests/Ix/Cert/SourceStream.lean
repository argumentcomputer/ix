import Ix.Cert.SourceStream

/-! Pure producer controls. Labelled aliases test the collector, not a
claimed collision among canonName outputs or Source acceptance. -/
namespace Tests.Ix.Cert.SourceStream
open _root_.Ix
open _root_.Ix.Compile.SourceGraph
open _root_.Ix.Compile.SourceGraph.Stream

private def workers := [0, 1, 2, 3, 8]
#guard (List.range 8).all fun n => workers.all fun w => (partition (Array.range n) w).flatten == Array.range n
#guard (partition (Array.range 5) 0).size == 5
#guard (partition (Array.range 5) 1).size == 1
#guard (partition (Array.range 5) 2).map (·.size) == #[3, 2]
#guard (partition (Array.range 5) 8).size == 5
private def bad : Lean.ConstantInfo := .defnInfo
  { name := `Stream.bad, levelParams := [], type := .sort (.succ .zero),
    value := .const `Stream.missing [], hints := .abbrev, safety := .safe, all := [`Stream.bad] }
private def good : Lean.ConstantInfo := .opaqueInfo
  { name := `Stream.good, levelParams := [], type := .sort (.succ .zero),
    value := .sort .zero, isUnsafe := false, all := [`Stream.good] }
private def other : Lean.ConstantInfo := .axiomInfo
  { name := `Stream.other, levelParams := [], type := .sort (.succ .zero), isUnsafe := false }
private def addr (n : Nat) : Address := ⟨⟨Array.replicate 32 n.toUInt8⟩⟩
private def key : Name := .str (.anonymous (addr 0)) "first" (addr 1)
private def sameHash : Name := .str (.anonymous (addr 0)) "last" (addr 1)
private def otherKey : Name := .str (.anonymous (addr 0)) "other" (addr 9)
private def input := #[(key, bad), (otherKey, other), (sameHash, good)]
private def rows (w : Nat) := ((tasks { consts := {} } input w).map Task.get).flatten
#guard key == sameHash && !Name.beqRaw key sameHash
#guard workers.all fun w => decide ((rows w).map (·.graph.name) = input.map (·.1))
#guard workers.all fun w => (rows w).map (·.immediate.isSome) == #[true, false, false]
#guard workers.all fun w => (rows w).map (·.digest) == input.map (fun p => hash (_root_.Ix.Cert.Canon.constS p.2))
private def expected (out : Output) : Bool :=
  out.facts.nodes.size == 2 && out.facts.code.size == 1 &&
  !out.facts.code.contains key && out.facts.code.contains otherKey &&
  (out.outRefs.getD key {}).isEmpty &&
  (out.immediate.get? sameHash).any (fun | .ref n => n == Name.fromLeanName `Stream.missing | _ => false) &&
  out.digests.get? key == some (hash (_root_.Ix.Cert.Canon.constS good))
#guard workers.all fun w => expected (runLabelled { consts := {} } input w)
-- The later successful opaque erases stale code, but the earlier error is not
-- erased by the existing collection policy.
#guard (runLabelled { consts := {} } input 0).immediate.contains sameHash
private def emptyOut := runLabelled { consts := {} } #[] 0
#guard emptyOut.facts.nodes.isEmpty && emptyOut.outRefs.isEmpty
private def one := chunk { consts := {} } #[(key, bad)]
#guard one.size == 1 && one[0]?.any (fun r => r.graph.kept.isSome && r.immediate.isSome)
private def proofSource : Lean.ConstantInfo := .thmInfo
  { name := `Stream.proof, levelParams := [], type := .sort (.succ .zero),
    value := .lit (.strVal "captured"), all := [`Stream.proof] }
private def raw := #[(bad.name, bad), (good.name, good), (other.name, other), (proofSource.name, proofSource)]
private def noNode : Node := ⟨{}, .none, .plain⟩
#guard workers.all fun w =>
  let out := runSource { consts := {} } raw w
  out.facts.nodes.size == 4 && out.facts.code.size == 2 &&
  (raw.map fun p => Name.fromLeanName p.1).all out.facts.nodes.contains &&
  !out.facts.code.contains (Name.fromLeanName `Stream.proof) &&
  ((out.facts.nodes.get? (Name.fromLeanName `Stream.proof)).getD noNode).literals == .string
#guard (label raw).map (·.1) == raw.map (fun p => Name.fromLeanName p.1)

/-- info: 'Ix.Cert.SourceStream.chunk_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.SourceStream.chunk_spec
/-- info: 'Ix.Cert.SourceStream.partition_flatten' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.SourceStream.partition_flatten
/-- info: 'Ix.Cert.SourceStream.tasks_flatten' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.SourceStream.tasks_flatten
/-- info: 'Ix.Cert.SourceStream.join_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.SourceStream.join_eq
/-- info: 'Ix.Cert.SourceStream.runSource_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.SourceStream.runSource_facts
/-- info: 'Ix.Cert.SourceStream.runSource_workers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.SourceStream.runSource_workers
/-- info: 'Ix.Cert.SourceStream.runSource_nodes_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.SourceStream.runSource_nodes_get
/-- info: 'Ix.Cert.SourceStream.runSource_code_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.SourceStream.runSource_code_get
/-- info: 'Ix.Cert.SourceStream.runSource_contains' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.SourceStream.runSource_contains
/-- info: 'Ix.Cert.SourceStream.runSource_hybrid_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.SourceStream.runSource_hybrid_get

end Tests.Ix.Cert.SourceStream
