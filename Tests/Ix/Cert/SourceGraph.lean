import Ix.Cert.SourceGraph

/-! Capture and collector controls. Synthetic records test exact data flow;
they do not claim Source acceptance or execution of the streaming compiler. -/
namespace Tests.Ix.Cert.SourceGraph

open _root_.Ix.Compile.SourceGraph
open _root_.Ix.Cert.SourceGraph

private def addr (n : Nat) : Address := ⟨⟨Array.replicate 32 n.toUInt8⟩⟩
private def name (n : Nat) : _root_.Ix.Name := .str (.anonymous (addr 0)) s!"n{n}" (addr n)
private def sameHash : _root_.Ix.Name := .str (.anonymous (addr 0)) "alias1" (addr 1)
private def sort : _root_.Ix.Expr := .sort (.zero (addr 50)) (addr 51)
private def ref (n : Nat) : _root_.Ix.Expr := .const (name n) #[] (addr (n + 100))
private def cv (n : _root_.Ix.Name) : _root_.Ix.ConstantVal := ⟨n, #[], sort⟩
private def code : _root_.Ix.ConstantInfo := .defnInfo ⟨cv (name 1), ref 2, .abbrev, .safe, #[name 1]⟩
private def streamed : _root_.Ix.ConstantInfo := .opaqueInfo ⟨cv sameHash, ref 3, false, #[sameHash]⟩
private def proof : _root_.Ix.ConstantInfo := .thmInfo ⟨cv sameHash, ref 4, #[sameHash]⟩
private def other : _root_.Ix.ConstantInfo := .axiomInfo ⟨cv (name 9), false⟩
private def raw := [(name 1, code), (name 9, other), (sameHash, streamed)]
private def result := collect (raw.map fun (n, ci) => rowOfCanonical n ci)
private def hybrid : _root_.Ix.Environment := { consts := result.code, fallback? := some (full raw).get? }
private def noNode : Node := ⟨{}, .none, .plain⟩
private def node := (result.nodes.get? (name 1)).getD noNode
private def legacy := raw.foldl (fun m p => match keep p.2 with
  | some ci => m.insert p.1 ci | none => m) ({} : _root_.Ix.Map _root_.Ix.Name _root_.Ix.ConstantInfo)

-- The real insertion-seam countercase: all maps must follow the final hash-key winner.
#guard sameHash == name 1 && !_root_.Ix.Name.beqRaw sameHash (name 1)
#guard legacy.contains sameHash && !result.code.contains sameHash
#guard result.nodes.size == 2 && result.code.size == 1
#guard node.direct.contains (name 3) && !node.direct.contains (name 2)
#guard (hybrid.get? (name 1)).any (fun | .opaqueInfo _ => true | _ => false)
#guard result.code.contains (name 9)
#guard !(result.nodes.contains (name 8)) && !(result.code.contains (name 8))
#guard (rowOfCanonical sameHash streamed).kept.isNone
#guard (rowOfCanonical sameHash proof).kept.isNone
#guard (rowOfCanonical (name 1) code).kept.isSome
#guard (collect []).nodes.isEmpty && (collect []).code.isEmpty
private def backToCode := collect ([streamed, code].map fun ci => rowOfCanonical ci.getCnst.name ci)
#guard (backToCode.code.get? sameHash).any (fun | .defnInfo _ => true | _ => false)
#guard ((backToCode.nodes.get? sameHash).getD noNode).direct.contains (name 2)
private def toProof := collect ([code, proof].map fun ci => rowOfCanonical ci.getCnst.name ci)
#guard !(toProof.code.contains sameHash) && ((toProof.nodes.get? sameHash).getD noNode).direct.contains (name 4)
private def unsafeCode : _root_.Ix.ConstantInfo := match code with
  | .defnInfo v => .defnInfo { v with safety := .unsafe }
  | ci => ci
#guard (keep unsafeCode).isSome

private def natLit : _root_.Ix.Expr := .lit (.natVal 7) (addr 60)
private def strLit : _root_.Ix.Expr := .lit (.strVal "sample") (addr 61)
private def withBody (body : _root_.Ix.Expr) : _root_.Ix.ConstantInfo :=
  .opaqueInfo ⟨cv sameHash, body, false, #[sameHash]⟩
#guard (capture code).literals == .none
#guard (capture (withBody natLit)).literals == .nat
#guard (capture (withBody (.app natLit strLit (addr 62)))).literals == .string
#guard (rowOfCanonical sameHash (withBody strLit)).kept.isNone
#guard (dependencies {} (capture (withBody strLit))).contains (_root_.Ix.Name.fromLeanName `String)
#guard (dependencies {} (capture (withBody strLit))).contains (_root_.Ix.Name.fromLeanName `Nat)
private def ind : _root_.Ix.ConstantInfo :=
  .inductInfo ⟨cv (name 4), 0, 0, #[name 4, name 6], #[], 0, false, false, false⟩
private def recursor : _root_.Ix.ConstantInfo :=
  .recInfo ⟨cv (name 5), #[name 4], 0, 0, 1, 0, #[⟨name 6, 0, strLit⟩], false, false⟩
private def recIndex : _root_.Ix.Map _root_.Ix.Name (Array (_root_.Ix.Name × _root_.Ix.Name)) :=
  .ofList [(name 4, #[(name 4, name 5), (name 4, name 5)])]
#guard (capture recursor).literals == .string
#guard (dependencies recIndex (capture ind)).contains (name 5)
#guard (dependencies recIndex (capture ind)).contains (name 6)
#guard (dependencies {} (capture recursor)).contains (name 4)
#guard (dependencies {} (capture recursor)).contains (name 6)
#guard (keep ind).isSome && (keep recursor).isSome
private def alias4 : _root_.Ix.Name := .str (.anonymous (addr 0)) "alias4" (addr 4)
#guard !(dependencies (.ofList [(name 4, #[(alias4, name 5)])]) (capture ind)).contains (name 5)
#guard decide (dependencies recIndex (capture ind) = _root_.Ix.Cert.dependencies recIndex ind)
-- Universe numbering and actual canonical conversion are exercised without retention assumptions.
private def leanCi : Lean.ConstantInfo := .opaqueInfo
  { name := `StreamRow.poly, levelParams := [`u], type := .sort (.succ (.param `u)),
    value := .sort (.param `u), isUnsafe := false, all := [`StreamRow.poly] }
private def canonical := _root_.Ix.CanonM.canonChunk #[(`StreamRow.poly, leanCi)]
#guard canonical.size == 1
#guard canonical[0]?.any fun (n, ci) => (rowOfCanonical n ci).kept.isNone
#guard canonical[0]?.any fun (n, ci) => (rowOfCanonical n ci).node.literals == .none

/-- info: 'Ix.Cert.SourceGraph.captureUsing_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.SourceGraph.captureUsing_eq
/-- info: 'Ix.Cert.SourceGraph.dependencies_capture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.SourceGraph.dependencies_capture
/-- info: 'Ix.Cert.SourceGraph.collect_nodes_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.SourceGraph.collect_nodes_get
/-- info: 'Ix.Cert.SourceGraph.collect_code_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.SourceGraph.collect_code_get
/-- info: 'Ix.Cert.SourceGraph.collected_hybrid_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.SourceGraph.collected_hybrid_get
/-- info: 'Ix.Cert.SourceGraph.rowOfCanonical_canon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Cert.SourceGraph.rowOfCanonical_canon

end Tests.Ix.Cert.SourceGraph
