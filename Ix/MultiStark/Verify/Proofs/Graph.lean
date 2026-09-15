module
public import Ix.MultiStark.Verify.Protocol.Graph
public import Ix.MultiStark.Verify.Proofs.Basic

public section

namespace MultiStark.Verify.Proofs

theorem getAt_ok_iff {α : Type} (values : Array α) (index : Nat) (value : α) :
    Ood.getAt values index = .ok value ↔ values[index]? = some value := by
  unfold Ood.getAt
  cases values[index]? <;> simp

theorem evalNode_refines (view : Ood.View) (previous : Array Ext) (node : Node) (value : Ext) :
    Ood.evalNode view previous node = .ok value ↔ Protocol.NodeValue view previous node value := by
  cases node <;>
    simp [Ood.evalNode, Protocol.NodeValue, bind_ok_iff, map_ok_iff, getAt_ok_iff] <;> rfl

theorem sweepFrom_refines (view : Ood.View) (previous : Array Ext) (nodes : List Node) (final : Array Ext) :
    Ood.sweepFrom view previous nodes = .ok final ↔ Protocol.GraphValues view previous nodes final := by
  induction nodes generalizing previous with
  | nil =>
    constructor
    · intro equal
      have equal := Except.ok.inj equal
      cases equal
      exact .nil _
    · intro derivation
      cases derivation
      rfl
  | cons node nodes ih =>
    rw [Ood.sweepFrom, bind_ok_iff]
    constructor
    · rintro ⟨value, evaluated, rest⟩
      exact .cons ((evalNode_refines view previous node value).mp evaluated) ((ih _).mp rest)
    · intro derivation
      cases derivation with
      | cons value rest =>
        exact ⟨_, (evalNode_refines view previous node _).mpr value, (ih _).mpr rest⟩

/-- Soundness and completeness for every finite graph derivation. In
particular, a successful sweep cannot read a future/missing graph node. -/
theorem sweep_refines (view : Ood.View) (final : Array Ext) :
    Ood.sweep view = .ok final ↔ Protocol.GraphValues view #[] view.values.circuit.nodes.toList final :=
  sweepFrom_refines view #[] view.values.circuit.nodes.toList final

end MultiStark.Verify.Proofs
