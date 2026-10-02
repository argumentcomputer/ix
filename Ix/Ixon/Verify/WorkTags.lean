import Ix.Ixon.Verify.Work

namespace Ixon.Verify.Work

open _root_.Ixon

/-- One byte read and one word-reconstruction step per completed limb. On
failure the unfinished suffix does not reconstruct words on its way out. -/
def trimmedAux : Nat → M UInt64
  | 0 => pure 0
  | n + 1 => do
    let low ← u8
    let high ← trimmedAux n
    charged 1 (pure (low.toUInt64 ||| (high <<< 8)))

def trimmed (width : Nat) : M UInt64 :=
  if width > 8 then fail "getU64TrimmedLE: len > 8" else trimmedAux width

def payload (large : Bool) (small : UInt8) : M UInt64 :=
  if large then trimmed (small.toNat + 1) else pure small.toUInt64

/-- An Ixon v3 validation step: canonical integer widths and flag bytes. The
comparison is not charged; it follows a read whose bytes were. -/
def reject (bad : Prop) [Decidable bad] (reason : String) : M Unit :=
  if bad then fail reason else pure ()

def tag0 : M Tag0 := do
  let b ← u8
  let large := b &&& 0x80 != 0
  let small := b &&& 0x7F
  let value ← payload large small
  reject (large && (decide (value < 128) || u64ByteCount value != small + 1))
    "noncanonical Tag0 integer"
  charged 1 (pure ⟨value⟩)

def tag2 : M Tag2 := do
  let b ← u8
  let large := b &&& 0x20 != 0
  let small := b &&& 0x1F
  let value ← payload large small
  reject (large && (decide (value < 32) || u64ByteCount value != small + 1))
    "noncanonical Tag2 integer"
  charged 1 (pure ⟨b >>> 6, value⟩)

def tag4 : M Tag4 := do
  let b ← u8
  let large := b &&& 0x08 != 0
  let small := b &&& 0x07
  let value ← payload large small
  reject (large && (decide (value < 8) || u64ByteCount value != small + 1))
    "noncanonical Tag4 integer"
  charged 1 (pure ⟨b >>> 4, value⟩)

theorem trimmedAux_erases (width : Nat) : Erases (trimmedAux width) (getU64TrimmedLEAux width) := by
  induction width with
  | zero => unfold trimmedAux getU64TrimmedLEAux; exact pure_erases 0
  | succ width ih =>
    unfold trimmedAux getU64TrimmedLEAux
    exact u8_erases.bind fun low => ih.bind fun high => (pure_erases _).charged 1

theorem trimmed_erases (width : Nat) : Erases (trimmed width) (getU64TrimmedLE width) := by
  unfold trimmed getU64TrimmedLE
  split
  · exact fail_erases _
  · exact trimmedAux_erases width

theorem payload_erases (large : Bool) (small : UInt8) : Erases (payload large small)
    (if large then getU64TrimmedLE (small.toNat + 1) else Pure.pure small.toUInt64) := by
  cases large
  · exact pure_erases _
  · exact trimmed_erases _

/-- The production check's join point: a rejected payload stops before the
continuation, and an accepted one continues with it. -/
theorem reject_erases {α : Type} (bad : Prop) [Decidable bad] (reason : String)
    {next : M α} {rest : GetM α} (h : Erases next rest) :
    Erases (reject bad reason >>= fun _ => next)
      (if bad then (throw reason : GetM PUnit) >>= (fun _ => rest) else rest) := by
  unfold reject
  by_cases hb : bad
  · simp only [ite_eq_left hb]
    funext state
    rfl
  · simp only [ite_eq_right hb]
    show Erases (Work.bind (pure ()) fun _ => next) rest
    rw [bind_pure_left]; exact h

theorem tag0_erases : Erases tag0 getTag0 := by
  unfold tag0 getTag0
  refine u8_erases.bind fun b => ?_
  cases b &&& 0x80 != 0
  · exact (pure_erases _).bind fun _ => reject_erases _ _ ((pure_erases _).charged 1)
  · exact (trimmed_erases _).bind fun _ => reject_erases _ _ ((pure_erases _).charged 1)

theorem tag2_erases : Erases tag2 getTag2 := by
  unfold tag2 getTag2
  refine u8_erases.bind fun b => ?_
  cases b &&& 0x20 != 0
  · exact (pure_erases _).bind fun _ => reject_erases _ _ ((pure_erases _).charged 1)
  · exact (trimmed_erases _).bind fun _ => reject_erases _ _ ((pure_erases _).charged 1)

theorem tag4_erases : Erases tag4 getTag4 := by
  unfold tag4 getTag4
  refine u8_erases.bind fun b => ?_
  cases b &&& 0x08 != 0
  · exact (pure_erases _).bind fun _ => reject_erases _ _ ((pure_erases _).charged 1)
  · exact (trimmed_erases _).bind fun _ => reject_erases _ _ ((pure_erases _).charged 1)

/-- The bound includes truncated reads, invalid widths, and nonminimal wire
spellings; it does not assume success or canonical re-encoding. -/
theorem trimmedAux_bound (rate : Nat) (enough : 2 ≤ rate) (width : Nat) :
    Bound (trimmedAux width) rate 0 (fun _ => 0) := by
  induction width with
  | zero => exact pure_bound rate 0 _ 0 (Nat.le_refl _)
  | succ width ih =>
    unfold trimmedAux
    apply (u8_bound rate (by omega)).bind
    intro low
    have carried : Bound (trimmedAux width) rate (rate - 1) (fun _ => rate - 1) := by
      simpa using ih.frame (rate - 1)
    apply carried.bind
    intro high
    exact ((pure_bound rate 0 _ _ (Nat.le_refl 0)).charged 1).weaken
      (by omega) (fun _ => Nat.le_refl 0)

theorem trimmed_bound (rate : Nat) (enough : 2 ≤ rate) (width : Nat) :
    Bound (trimmed width) rate 0 (fun _ => 0) := by
  unfold trimmed
  split
  · exact fail_bound _ _ _ _
  · exact trimmedAux_bound rate enough width

theorem payload_bound (rate : Nat) (enough : 2 ≤ rate) (large : Bool) (small : UInt8) :
    Bound (payload large small) rate 0 (fun _ => 0) := by
  cases large
  · exact pure_bound rate 0 _ _ (Nat.le_refl 0)
  · exact trimmed_bound rate enough _

theorem reject_bound (rate credit : Nat) (bad : Prop) [Decidable bad] (reason : String) :
    Bound (reject bad reason) rate credit (fun _ => credit) := by
  unfold reject
  split
  · exact fail_bound _ _ _ _
  · exact pure_bound rate credit _ _ (Nat.le_refl credit)

theorem tag0_bound (rate : Nat) (enough : 2 ≤ rate) :
    Bound tag0 rate 0 (fun _ => rate - 2) := by
  unfold tag0
  apply (u8_bound rate (by omega)).bind
  intro b
  have carried : Bound (payload (b &&& 0x80 != 0) (b &&& 0x7F)) rate (rate - 1) (fun _ => rate - 1) := by
    simpa using (payload_bound rate enough _ _).frame (rate - 1)
  apply carried.bind
  intro value
  exact (reject_bound rate (rate - 1) _ _).bind fun _ =>
    ((pure_bound rate (rate - 2) _ _ (Nat.le_refl (rate - 2))).charged 1).weaken
      (by omega) (fun _ => Nat.le_refl _)

theorem tag2_bound (rate : Nat) (enough : 2 ≤ rate) :
    Bound tag2 rate 0 (fun _ => rate - 2) := by
  unfold tag2
  apply (u8_bound rate (by omega)).bind
  intro b
  have carried : Bound (payload (b &&& 0x20 != 0) (b &&& 0x1F)) rate (rate - 1) (fun _ => rate - 1) := by
    simpa using (payload_bound rate enough _ _).frame (rate - 1)
  apply carried.bind
  intro value
  exact (reject_bound rate (rate - 1) _ _).bind fun _ =>
    ((pure_bound rate (rate - 2) _ _ (Nat.le_refl (rate - 2))).charged 1).weaken
      (by omega) (fun _ => Nat.le_refl _)

theorem tag4_bound (rate : Nat) (enough : 2 ≤ rate) :
    Bound tag4 rate 0 (fun _ => rate - 2) := by
  unfold tag4
  apply (u8_bound rate (by omega)).bind
  intro b
  have carried : Bound (payload (b &&& 0x08 != 0) (b &&& 0x07)) rate (rate - 1) (fun _ => rate - 1) := by
    simpa using (payload_bound rate enough _ _).frame (rate - 1)
  apply carried.bind
  intro value
  exact (reject_bound rate (rate - 1) _ _).bind fun _ =>
    ((pure_bound rate (rate - 2) _ _ (Nat.le_refl (rate - 2))).charged 1).weaken
      (by omega) (fun _ => Nat.le_refl _)

end Ixon.Verify.Work
