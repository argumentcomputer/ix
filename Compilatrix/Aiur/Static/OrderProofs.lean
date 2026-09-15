import Compilatrix.Aiur.Static.Assignment

namespace Compilatrix.Aiur.Static

theorem FunctionPlan.order_positive (plan : FunctionPlan) : 0 < plan.order := by
  unfold FunctionPlan.order
  split <;> omega

theorem FunctionPlan.ranked_order (plan : FunctionPlan) :
    rankedOrder plan.order = plan.component.ranked := by
  unfold FunctionPlan.order rankedOrder
  cases plan.component.ranked <;> simp [Nat.add_mod]

theorem FunctionPlan.order_lt_of_component (parent child : FunctionPlan)
    (advance : parent.component.order < child.component.order) : parent.order < child.order := by
  unfold FunctionPlan.order
  split <;> split <;> omega

theorem FunctionPlan.order_lt_leaf (plan : FunctionPlan) (count : Nat)
    (bound : plan.component.order < count) : plan.order < 2 * count + 1 := by
  unfold FunctionPlan.order
  split <;> omega

theorem FunctionPlan.same_order (parent child : FunctionPlan)
    (order : parent.component.order = child.component.order)
    (mode : parent.component.ranked = child.component.ranked) : parent.order = child.order := by
  simp only [FunctionPlan.order, order, mode]

end Compilatrix.Aiur.Static
