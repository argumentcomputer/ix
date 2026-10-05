import IxC.Ixon.Verify.Work
import IxC.Ixon.Verify.BoundedConstant

namespace Ixon.Verify.Work

open Ixon

/-- Each successful element pays one iteration and one append. The reader's
own work is also counted, including when it fails after partial consumption.
No allocation or accounting credit is based on the claimed element count. -/
def arrayLoop (reader : M α) : Nat → Array α → M (Array α)
  | 0, values => pure values
  | count + 1, values => do
    let value ← reader
    charged 2 (arrayLoop reader count (values.push value))

def array (reader : M α) (count : Nat) : M (Array α) := arrayLoop reader count #[]

theorem arrayLoop_erases {metered : M α} {reader : GetM α} (same : Erases metered reader)
    (count : Nat) (values : Array α) :
    Erases (arrayLoop metered count values) (do
      let added ← getArray reader count
      return values ++ added) := by
  induction count generalizing values with
  | zero =>
    rw [BoundedConstant.getArray_zero]
    simpa only [arrayLoop, pure_bind, Array.append_empty] using pure_erases values
  | succ count ih =>
    unfold arrayLoop
    rw [BoundedConstant.getArray_succ]
    simp only [bind_assoc, pure_bind]
    apply same.bind
    intro value
    simpa only [Array.push_eq_append, Array.append_assoc] using
      (ih (values.push value)).charged 2

theorem array_erases {metered : M α} {reader : GetM α} (same : Erases metered reader)
    (count : Nat) : Erases (array metered count) (getArray reader count) := by
  simpa only [array, Array.empty_append, bind_pure] using arrayLoop_erases same count #[]

theorem arrayLoop_bound {reader : M α} (bound : Bound reader 16 0 (fun _ => 2))
    (count : Nat) (values : Array α) : Bound (arrayLoop reader count values) 16 0 (fun _ => 0) := by
  induction count generalizing values with
  | zero => exact pure_bound _ _ _ _ (Nat.le_refl _)
  | succ count ih =>
    unfold arrayLoop
    exact bound.bind fun value => (ih (values.push value)).charged 2

theorem array_bound {reader : M α} (bound : Bound reader 16 0 (fun _ => 2)) (count : Nat) :
    Bound (array reader count) 16 0 (fun _ => 0) := arrayLoop_bound bound count #[]

theorem bytes_positive_bound (count : Nat) (positive : 0 < count) :
    Bound (bytes count) 16 0 (fun _ => 8) := by
  intro start valid
  by_cases fits : start.idx + count ≤ start.bytes.size
  · simp only [bytes, getBytes_run, ite_eq_left fits, Costs, finish]
    exact ⟨⟨rfl, by simp, fits⟩, by dsimp; omega⟩
  · simp only [bytes, getBytes_run, ite_eq_right fits, Costs, finish]
    exact ⟨Progress.refl start valid, by simp⟩

def address : M Address := do
  let value ← bytes 32
  charged 1 (pure ⟨value⟩)

theorem address_erases : Erases address (Serialize.get : GetM Address) :=
  (bytes_erases 32).bind fun _ => (pure_erases _).charged 1

theorem address_bound : Bound address 16 0 (fun _ => 2) :=
  (bytes_positive_bound 32 (by decide)).bind fun _ =>
    charged_pure_bound _ _ _ _ _ (by decide)

end Ixon.Verify.Work
