import Ix.Compiler.IxIR2.CreditRelation

/-! Counters untouched by retain and recursive destruction. -/

namespace Ix.Compiler.IxIR2.CreditRefinement

open Eval

/-- Recursive heap traversal changes RC and free counts; every other counter
is preserved. Live nodes are tracked separately by the heap relation. -/
def passiveCounters (store : Store) : Counters :=
  { store.counters with frees := 0, rcops := 0 }

theorem retain_passive {store output : Store} {value : RVal}
    (run : retainShared store value = .ok output) :
    passiveCounters output = passiveCounters store := by
  cases value with
  | lit => cases run; rfl
  | erased => cases run; rfl
  | loc location =>
      cases found : store.get? location with
      | none => simp [retainShared, found] at run
      | some box =>
          by_cases shared : box.world = .shared
          · simp [retainShared, found, shared] at run
            subst output
            rfl
          · simp [retainShared, found, shared] at run

theorem retainMany_passive {store output : Store} {values : Array RVal}
    (run : RetainSharedMany store values output) :
    passiveCounters output = passiveCounters store := by
  change values.foldlM retainShared store = .ok output at run
  rw [← Array.foldlM_toList] at run
  have loop : ∀ (values : List RVal) {store output : Store},
      values.foldlM retainShared store = .ok output →
      passiveCounters output = passiveCounters store := by
    intro values
    induction values with
    | nil => intro store output run; cases run; rfl
    | cons head tail ih =>
        intro store output run
        rw [List.foldlM_cons] at run
        cases first : retainShared store head with
        | error error => simp [first, bind, Except.bind] at run
        | ok middle =>
            simp only [first, bind, Except.bind] at run
            exact (ih run).trans (retain_passive first)
  exact loop values.toList run

theorem releaseWork_passive {fuel remaining : Nat} {store output : Store} {values : List RVal}
    (run : releaseSharedWork fuel store values = .ok (output, remaining)) :
    passiveCounters output = passiveCounters store := by
  induction fuel generalizing store values with
  | zero =>
      cases values with
      | nil => cases run; rfl
      | cons => simp [releaseSharedWork] at run
  | succ fuel ih =>
      cases values with
      | nil => cases run; rfl
      | cons value rest =>
          cases value with
          | lit => exact ih run
          | erased => exact ih run
          | loc location =>
              cases found : store.get? location with
              | none => simp [releaseSharedWork, found] at run
              | some box =>
                  by_cases shared : box.world = .shared
                  · by_cases zero : box.rc = 0
                    · simp [releaseSharedWork, found, shared, zero] at run
                    · by_cases unit : box.rc = 1
                      · simp only [releaseSharedWork, found, shared, bne_self_eq_false,
                          Bool.false_eq_true, ↓reduceIte, unit, beq_self_eq_true,
                          Nat.reduceBEq] at run
                        have preserved := ih run
                        exact preserved
                      · simp [releaseSharedWork, found, shared, zero, unit] at run
                        have preserved := ih run
                        exact preserved
                  · simp [releaseSharedWork, found, shared] at run

theorem dropWork_passive {fuel remaining : Nat} {store output : Store} {values : List RVal}
    (run : dropUniqueWork fuel store values = .ok (output, remaining)) :
    passiveCounters output = passiveCounters store := by
  induction fuel generalizing store values with
  | zero =>
      cases values with
      | nil => cases run; rfl
      | cons => simp [dropUniqueWork] at run
  | succ fuel ih =>
      cases values with
      | nil => cases run; rfl
      | cons value rest =>
          cases value with
          | lit => exact ih run
          | erased => exact ih run
          | loc location =>
              cases found : store.get? location with
              | none => simp [dropUniqueWork, found] at run
              | some box =>
                  by_cases unique : box.world = .unique
                  · cases node : box.node with
                    | papN => simp [dropUniqueWork, found, unique, node] at run
                    | ctorN cid fields =>
                        simp only [dropUniqueWork, found, unique, bne_self_eq_false,
                          Bool.false_eq_true, ↓reduceIte, node] at run
                        have preserved := ih run
                        exact preserved
                  · simp [dropUniqueWork, found, unique] at run

end Ix.Compiler.IxIR2.CreditRefinement
