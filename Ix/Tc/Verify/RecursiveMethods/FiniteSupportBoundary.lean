import Ix.Tc.Verify.Infer.Dispatcher

/-!
# Finite-support boundary for recursive inference

`RunSupport` deliberately describes the finite set of expressions whose
content addresses are observed by one concrete checker run.  It must not also
be used as an all-depth recursive call domain.

The distinction is already forced by sort inference.  If one finite support
contains `sort u` and is closed under every successful sort-inference result,
then it contains `sort (succ^[n] u)` for every `n`.  Their universe syntax
sizes are unbounded, contradicting finiteness.  The theorems below make that
interface failure explicit so a recursive-method closure cannot accidentally
hide it behind an uninhabitable premise.
-/

namespace Ix.Tc

namespace FiniteSupportBoundary

/-- Iterate the production universe-successor constructor. -/
private def iterSucc (u : KUniv .anon) : Nat → KUniv .anon
  | 0 => u
  | n + 1 => KUniv.mkSucc (iterSucc u n)

private theorem iterSucc_size (u : KUniv .anon) (n : Nat) :
    (iterSucc u n).size = u.size + n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hstep : (KUniv.mkSucc (iterSucc u n)).size
          = (iterSucc u n).size + 1 := rfl
      simp only [iterSucc, hstep, ih]
      omega

/-- A measure that observes precisely the universe carried by a sort. -/
private def sortLevelSize : KExpr .anon → Nat
  | .sort u _ => u.size
  | _ => 0

/-- A simple upper bound for all sort-level sizes in a concrete list. -/
private def sortLevelBound : List (KExpr .anon) → Nat
  | [] => 0
  | e :: es => max (sortLevelSize e) (sortLevelBound es)

private theorem sortLevelSize_le_bound_of_mem
    {e : KExpr .anon} {es : List (KExpr .anon)} (h : e ∈ es) :
    sortLevelSize e ≤ sortLevelBound es := by
  induction es with
  | nil => simp at h
  | cons head tail ih =>
      rcases List.mem_cons.mp h with rfl | htail
      · exact Nat.le_max_left ..
      · exact Nat.le_trans (ih htail) (Nat.le_max_right ..)

private theorem iterSucc_supported
    (support : RunSupport)
    (closed : ∀ {u : KUniv .anon} {info : ExprInfo .anon},
      support (.sort u info) → support (KExpr.mkSort (KUniv.mkSucc u)))
    {u : KUniv .anon} (seed : support (KExpr.mkSort u)) (n : Nat) :
    support (KExpr.mkSort (iterSucc u n)) := by
  induction n with
  | zero => exact seed
  | succ n ih =>
      rw [KExpr.mkSort_shape (iterSucc u n) ()] at ih
      exact closed ih

/-- No finite run support containing a sort can be closed under arbitrarily
many applications of the production sort-inference result operation. -/
theorem no_finite_sort_successor_closure
    (support : RunSupport)
    (closed : ∀ {u : KUniv .anon} {info : ExprInfo .anon},
      support (.sort u info) → support (KExpr.mkSort (KUniv.mkSucc u)))
    {u : KUniv .anon} (seed : support (KExpr.mkSort u)) : False := by
  obtain ⟨es, hes⟩ := support.exprFinite
  let n := sortLevelBound es + 1
  have hsupported : support (KExpr.mkSort (iterSucc u n)) :=
    iterSucc_supported support closed seed n
  have hmem : KExpr.mkSort (iterSucc u n) ∈ es := hes hsupported
  have hbounded := sortLevelSize_le_bound_of_mem hmem
  rw [KExpr.mkSort_shape (iterSucc u n) ()] at hbounded
  change (iterSucc u n).size ≤ sortLevelBound es at hbounded
  rw [iterSucc_size] at hbounded
  dsimp [n] at hbounded
  omega

/-- The current all-depth syntax-inference resource is therefore
uninhabitable for every finite run support that contains a sort source. -/
theorem SyntaxInferenceResources.no_sort_source
    {support : RunSupport} (resources : SyntaxInferenceResources support)
    {u : KUniv .anon} : ¬ support (KExpr.mkSort u) := by
  intro seed
  exact no_finite_sort_successor_closure support resources.sortResult seed

end FiniteSupportBoundary

end Ix.Tc
