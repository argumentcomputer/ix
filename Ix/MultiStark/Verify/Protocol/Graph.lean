module
public import Ix.MultiStark.Verify.Ood.Basic

/-! Independent relational semantics of the key's AIR expression graph.
The relation states the value of each expression and the order of available
references; it does not mention `evalNode`, `sweep`, or verifier acceptance.
Field operations and the supplied OOD frame are explicit semantic inputs. -/

public section
@[expose] section

namespace MultiStark.Verify.Protocol

def NodeValue (view : Ood.View) (previous : Array Ext) : Node → Ext → Prop
  | .const constant, value => Arithmetic.embed constant = value
  | .var source next column, value =>
    let rows := match source with
      | .preprocessed => view.values.preprocessed
      | .main => view.values.stage1
      | .stage2 => view.values.stage2
    (if next then rows.2 else rows.1)[column]? = some value
  | .public index, value => view.publics[index]? = some value
  | .first, value => view.selectors.first = value
  | .last, value => view.selectors.last = value
  | .transition, value => view.selectors.transition = value
  | .add left right, value => ∃ a b, previous[left]? = some a ∧ previous[right]? = some b ∧ a.add b = value
  | .sub left right, value => ∃ a b, previous[left]? = some a ∧ previous[right]? = some b ∧ a.sub b = value
  | .mul left right, value => ∃ a b, previous[left]? = some a ∧ previous[right]? = some b ∧ a.mul b = value
  | .neg child, value => ∃ a, previous[child]? = some a ∧ Arithmetic.neg a = value

inductive GraphValues (view : Ood.View) : Array Ext → List Node → Array Ext → Prop where
  | nil (previous : Array Ext) : GraphValues view previous [] previous
  | cons (value : NodeValue view previous node result)
      (rest : GraphValues view (previous.push result) nodes final) :
      GraphValues view previous (node :: nodes) final

end MultiStark.Verify.Protocol
