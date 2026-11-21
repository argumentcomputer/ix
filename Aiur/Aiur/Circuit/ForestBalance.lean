import Aiur.Circuit.Balance

namespace Aiur.Circuit.Balance

def Forest (static : α → Bool) (roots : List α) (rules : List (RuleClaims α)) : Prop :=
  ((roots ++ rules.flatMap Prod.snd).filter (fun c => !static c)).Perm (rules.map Prod.fst)

theorem forest_nil (static : α → Bool) : Forest static [] [] := .nil

theorem forest_static {static : α → Bool} {root : α} (known : static root = true) :
    Forest static [root] [] := by simp [Forest, known]

theorem forest_node {static : α → Bool} {conclusion : α} {premises : List α}
    {rules : List (RuleClaims α)} (dynamic : static conclusion = false)
    (children : Forest static premises rules) :
    Forest static [conclusion] ((conclusion, premises) :: rules) := by
  simpa [Forest, dynamic] using List.Perm.cons conclusion children

theorem forest_append [DecidableEq α] {static : α → Bool} {leftRoots rightRoots : List α}
    {left right : List (RuleClaims α)} (a : Forest static leftRoots left)
    (b : Forest static rightRoots right) : Forest static (leftRoots ++ rightRoots) (left ++ right) := by
  simp only [Forest, List.perm_iff_count] at a b ⊢
  intro claim
  have ha := a claim
  have hb := b claim
  simp only [List.filter_append, List.count_append, List.flatMap_append, List.map_append] at ha hb ⊢
  omega

end Aiur.Circuit.Balance
