import IxKernel.Ixon.Verify.Work

namespace Ixon.Verify.Work

open Ixon

/-- One byte read and one word-reconstruction step per completed limb. On
failure the unfinished suffix does not reconstruct words on its way out. -/
def trimmedAux : Nat → M UInt64
  | 0 => pure 0
  | n + 1 => do
    let low ← u8
    let high ← trimmedAux n
    charged 1 (pure (low.toUInt64 ||| (high <<< 8)))

/-- The multi-byte TagN rungs, selected by the header code `c`: a fixed number
of little-endian bytes, then one charged construction. An invalid code and an
8-byte payload whose value reaches `2^64` are rejected; the comparison is not
charged, since it follows reads whose bytes were. -/
def tagNWide (f : Nat) (flag : UInt8) (c : Nat) : M TagN :=
  if c = 0 then do
    let x ← trimmedAux 2
    charged 1 (pure ⟨flag, (tagNEnd2 f + x.toNat).toUInt64⟩)
  else if c = 1 then do
    let x ← trimmedAux 3
    charged 1 (pure ⟨flag, (tagNEnd3 f + x.toNat).toUInt64⟩)
  else if c = 2 then do
    let x ← trimmedAux 4
    charged 1 (pure ⟨flag, (tagNEnd4 f + x.toNat).toUInt64⟩)
  else if c = 3 then do
    let x ← trimmedAux 8
    if tagNEnd5 f + x.toNat < 2 ^ 64 then
      charged 1 (pure ⟨flag, (tagNEnd5 f + x.toNat).toUInt64⟩)
    else
      fail "TagN value exceeds UInt64"
  else
    fail s!"invalid TagN code {c}"

/-- A TagN integer with an `f`-bit flag: the header byte, then the bytes its
rung selects, then one charged construction. -/
def tagN (f : Nat) : M TagN := do
  let b ← u8
  let flag := (b.toNat / 2 ^ (8 - f)).toUInt8
  let p := b.toNat % 2 ^ (8 - f)
  if p < 2 ^ (8 - f - 1) then
    charged 1 (pure ⟨flag, p.toUInt64⟩)
  else if p - 2 ^ (8 - f - 1) < 2 ^ (8 - f - 2) then do
    let lo ← u8
    charged 1 (pure ⟨flag, (tagNEnd1 f + (p - 2 ^ (8 - f - 1)) * 256 + lo.toNat).toUInt64⟩)
  else
    tagNWide f flag (p - 2 ^ (8 - f - 1) - 2 ^ (8 - f - 2))

/-- A wire validation step (flag bytes). The comparison is not charged; it
follows a read whose bytes were. -/
def reject (bad : Prop) [Decidable bad] (reason : String) : M Unit :=
  if bad then fail reason else pure ()

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

theorem reject_bound (rate credit : Nat) (bad : Prop) [Decidable bad] (reason : String) :
    Bound (reject bad reason) rate credit (fun _ => credit) := by
  unfold reject
  split
  · exact fail_bound _ _ _ _
  · exact pure_bound rate credit _ _ (Nat.le_refl credit)

theorem trimmedAux_erases (width : Nat) : Erases (trimmedAux width) (getU64TrimmedLEAux width) := by
  induction width with
  | zero => unfold trimmedAux getU64TrimmedLEAux; exact pure_erases 0
  | succ width ih =>
    unfold trimmedAux getU64TrimmedLEAux
    exact u8_erases.bind fun low => ih.bind fun high => (pure_erases _).charged 1

theorem tagNWide_erases (f : Nat) (flag : UInt8) (c : Nat) :
    Erases (tagNWide f flag c) (getTagNWide f flag c) := by
  unfold tagNWide getTagNWide
  split
  · exact (trimmedAux_erases 2).bind fun _ => (pure_erases _).charged 1
  split
  · exact (trimmedAux_erases 3).bind fun _ => (pure_erases _).charged 1
  split
  · exact (trimmedAux_erases 4).bind fun _ => (pure_erases _).charged 1
  split
  · refine (trimmedAux_erases 8).bind fun x => ?_
    split
    · exact (pure_erases _).charged 1
    · exact fail_erases _
  · exact fail_erases _

theorem tagN_erases (f : Nat) : Erases (tagN f) (getTagN f) := by
  unfold tagN getTagN
  refine u8_erases.bind fun b => ?_
  simp only
  split
  · exact (pure_erases _).charged 1
  split
  · exact u8_erases.bind fun _ => (pure_erases _).charged 1
  · exact tagNWide_erases _ _ _

/-- The bound includes truncated reads, invalid codes and overflowing
payloads; it does not assume success. -/
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

theorem tagNWide_bound (rate : Nat) (enough : 2 ≤ rate) (f : Nat) (flag : UInt8) (c : Nat) :
    Bound (tagNWide f flag c) rate (rate - 1) (fun _ => rate - 2) := by
  have rung (width : Nat) (value : UInt64 → TagN) :
      Bound (do let x ← trimmedAux width; charged 1 (pure (value x)))
        rate (rate - 1) (fun _ => rate - 2) := by
    have carried : Bound (trimmedAux width) rate (rate - 1) (fun _ => rate - 1) := by
      simpa using (trimmedAux_bound rate enough width).frame (rate - 1)
    exact carried.bind fun _ =>
      ((pure_bound rate (rate - 2) _ _ (Nat.le_refl (rate - 2))).charged 1).weaken
        (by omega) (fun _ => Nat.le_refl _)
  unfold tagNWide
  split
  · exact rung 2 _
  split
  · exact rung 3 _
  split
  · exact rung 4 _
  split
  · have carried : Bound (trimmedAux 8) rate (rate - 1) (fun _ => rate - 1) := by
      simpa using (trimmedAux_bound rate enough 8).frame (rate - 1)
    refine carried.bind fun x => ?_
    split
    · exact ((pure_bound rate (rate - 2) _ _ (Nat.le_refl (rate - 2))).charged 1).weaken
        (by omega) (fun _ => Nat.le_refl _)
    · exact fail_bound _ _ _ _
  · exact fail_bound _ _ _ _

/-- Every TagN read, successful or not, is paid by its consumed bytes at any
rate of at least two units per byte, leaving `rate - 2` units of output credit
(each read consumes at least its header byte). -/
theorem tagN_bound (f : Nat) (rate : Nat) (enough : 2 ≤ rate) :
    Bound (tagN f) rate 0 (fun _ => rate - 2) := by
  unfold tagN
  apply (u8_bound rate (by omega)).bind
  intro b
  simp only
  split
  · exact ((pure_bound rate (rate - 2) _ _ (Nat.le_refl (rate - 2))).charged 1).weaken
      (by omega) (fun _ => Nat.le_refl _)
  split
  · have carried : Bound u8 rate (rate - 1) (fun _ => rate - 1 + (rate - 1)) := by
      simpa using (u8_bound rate (by omega)).frame (rate - 1)
    exact carried.bind fun _ =>
      ((pure_bound rate (rate - 2) _ _ (Nat.le_refl (rate - 2))).charged 1).weaken
        (by omega) (fun _ => Nat.le_refl _)
  · exact tagNWide_bound rate enough _ _ _

end Ixon.Verify.Work
