import Ix.Ixon.Verify.WorkConstant

namespace Ixon.Verify.Work

open Ixon

/-- Account for a framing attempt, conservatively also on reader failure. -/
def exact (reader : M α) (input : ByteArray) : Except String α × Nat :=
  let parsed := reader { bytes := input }
  let result := match parsed.1 with
    | .ok value state =>
      if state.idx = input.size then .ok value
      else .error s!"trailing bytes: consumed {state.idx} of {input.size}"
    | .error reason _ => .error reason
  (result, parsed.2 + 1)

/-- Byte admission is checked before any grammar work; the universe budget
is shared across the entire record. The extra unit counts the byte check. -/
def record (maxBytes budget : Nat) (input : ByteArray) : Except String Constant × Nat :=
  if input.size ≤ maxBytes then
    let parsed := exact (constant budget) input
    (parsed.1, parsed.2 + 1)
  else (.error "getConstantBounded: byte budget exhausted", 1)

theorem exact_erases {metered : M α} {reader : GetM α} (same : Erases metered reader)
    (input : ByteArray) : (exact metered input).1 = runGetExact reader input := by
  have read := congrFun same { bytes := input }
  change (metered { bytes := input }).1 = reader { bytes := input } at read
  simp only [exact, runGetExact, EStateM.run, read]
  rfl

theorem record_erases (maxBytes budget : Nat) (input : ByteArray) :
    (record maxBytes budget input).1 = Bounded.deConstant maxBytes budget input := by
  unfold record Bounded.deConstant
  split
  · exact exact_erases (constant_erases budget) input
  · rfl

theorem exact_work_le {reader : M α} {rate credit : Nat} {remaining : α → Nat}
    (bound : Bound reader rate credit remaining) (input : ByteArray) :
    (exact reader input).2 ≤ rate * input.size + credit + 2 := by
  have work := bound.work_le { bytes := input } (Nat.zero_le _)
  simp only [exact]
  dsimp only at work
  simp only [Nat.sub_zero] at work
  omega

/-- Every bounded record parse, including failed and noncanonical inputs.
The bound counts byte attempts/copies, tag reconstruction, structural and
collection work, reserved universe expansion, and record framing/checks. -/
theorem record_work_le (maxBytes budget : Nat) (input : ByteArray) :
    (record maxBytes budget input).2 ≤ 16 * input.size + 2 * budget + 3 := by
  unfold record
  split
  · have work := exact_work_le (constant_bound budget) input
    dsimp only
    omega
  · dsimp only
    omega

/-- The complete production outcome is unchanged, while the accounted work
is bounded independently of all untrusted declared table/telescope counts. -/
theorem record_accounted (maxBytes budget : Nat) (input : ByteArray) :
    (record maxBytes budget input).1 = Bounded.deConstant maxBytes budget input ∧
      (record maxBytes budget input).2 ≤ 16 * input.size + 2 * budget + 3 :=
  ⟨record_erases maxBytes budget input, record_work_le maxBytes budget input⟩

end Ixon.Verify.Work
