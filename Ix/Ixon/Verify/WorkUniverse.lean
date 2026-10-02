import Ix.Ixon.Verify.WorkTags
import Ix.Ixon.Bounded.Constant

namespace Ixon.Verify.Work

open _root_.Ixon

/-! Universe work reserves two units per expanded constructor before descending
into children: one expansion step and one constructed node. This upper estimate
also charges a reserved node when a child subsequently fails, so failure cannot
hide partial expansion or restart its budget. A successful universe returns the
unused budget and four byte-funded credits for its enclosing reader.
-/

def univBody (recur : Nat → M (Univ × Nat)) (remaining : Nat) (tag : Tag2) : M (Univ × Nat) :=
  match tag.flag with
  | 0 =>
    if tag.size == 0 then charged 1 (pure (.zero, remaining))
    else do
      let (base, remaining) ← recur remaining
      charged 1 (pure (base.addSucc tag.size.toNat, remaining))
  | 1 => do
    let (left, remaining) ← recur remaining
    let (right, remaining) ← recur remaining
    charged 1 (pure (.max left right, remaining))
  | 2 => do
    let (left, remaining) ← recur remaining
    let (right, remaining) ← recur remaining
    charged 1 (pure (.imax left right, remaining))
  | 3 => charged 1 (pure (.var tag.size, remaining))
  | flag => fail s!"getUniv: invalid flag {flag}"

def univFromTag (recur : Nat → M (Univ × Nat)) (budget : Nat) (tag : Tag2) : M (Univ × Nat) :=
  let amount := Bounded.univTagCharge tag
  if amount ≤ budget then
    charged (2 * amount) (univBody recur (budget - amount) tag)
  else fail "getUnivBounded: expanded-node budget exhausted"

def univFuel : Nat → Nat → M (Univ × Nat)
  | 0, _ => fail "getUniv: recursion budget exhausted"
  | fuel + 1, budget => bind tag2 (univFromTag (univFuel fuel) budget)

def univ (budget : Nat) : M (Univ × Nat) := fun state =>
  univFuel (state.bytes.size - state.idx + 1) budget state

def univArrayLoop : Nat → Nat → Array Univ → M (Array Univ × Nat)
  | 0, budget, values => pure (values, budget)
  | count + 1, budget, values => do
    let (value, remaining) ← univ budget
    charged 2 (univArrayLoop count remaining (values.push value))

def univArray (count budget : Nat) : M (Array Univ × Nat) := univArrayLoop count budget #[]

theorem univFromTag_erases {recur : Nat → M (Univ × Nat)} {reader : Nat → GetM (Univ × Nat)}
    (same : ∀ budget, Erases (recur budget) (reader budget)) (budget : Nat) (tag : Tag2) :
    Erases (univFromTag recur budget tag) (Bounded.getUnivFromTag reader budget tag) := by
  unfold univFromTag Bounded.getUnivFromTag
  dsimp only
  split
  · apply Erases.charged
    unfold univBody
    split <;> simp_all only
    · split
      · exact (pure_erases _).charged 1
      · apply (same _).bind
        rintro ⟨base, remaining⟩
        exact (pure_erases _).charged 1
    · apply (same _).bind
      rintro ⟨left, remaining⟩
      apply (same _).bind
      rintro ⟨right, remaining⟩
      exact (pure_erases _).charged 1
    · apply (same _).bind
      rintro ⟨left, remaining⟩
      apply (same _).bind
      rintro ⟨right, remaining⟩
      exact (pure_erases _).charged 1
    · exact (pure_erases _).charged 1
    · exact fail_erases _
  · exact fail_erases _

theorem univFuel_erases (fuel budget : Nat) :
    Erases (univFuel fuel budget) (Bounded.getUnivFuel fuel budget) := by
  induction fuel generalizing budget with
  | zero => exact fail_erases _
  | succ fuel ih => exact tag2_erases.bind (univFromTag_erases ih budget)

theorem univ_erases (budget : Nat) : Erases (univ budget) (Bounded.getUniv budget) := by
  funext state
  exact congrFun (univFuel_erases _ budget) state

theorem univArrayLoop_erases (count budget : Nat) (values : Array Univ) :
    Erases (univArrayLoop count budget values) (Bounded.getUnivArrayLoop count budget values) := by
  induction count generalizing budget values with
  | zero => exact pure_erases _
  | succ count ih =>
    unfold univArrayLoop Bounded.getUnivArrayLoop
    apply (univ_erases budget).bind
    rintro ⟨value, remaining⟩
    exact (ih remaining (values.push value)).charged 2

theorem univArray_erases (count budget : Nat) :
    Erases (univArray count budget) (Bounded.getUnivArray count budget) :=
  univArrayLoop_erases count budget #[]

theorem univBody_bound {recur : Nat → M (Univ × Nat)}
    (bound : ∀ budget, Bound (recur budget) 16 (2 * budget) (fun value => 2 * value.2 + 4))
    (remaining : Nat) (tag : Tag2) :
    Bound (univBody recur remaining tag) 16 (2 * remaining + 14) (fun value => 2 * value.2 + 4) := by
  unfold univBody
  split
  · split
    · exact charged_pure_bound _ _ _ _ _ (by omega)
    · apply ((bound remaining).frame 14).bind
      rintro ⟨base, remaining⟩
      exact charged_pure_bound _ _ _ _ _ (by omega)
  · apply ((bound remaining).frame 14).bind
    rintro ⟨left, remaining⟩
    apply Bound.bind (intermediate := fun value => 2 * value.2 + 22)
    · exact ((bound remaining).frame 18).weaken (by omega) (fun _ => by omega)
    · rintro ⟨right, remaining⟩
      exact charged_pure_bound _ _ _ _ _ (by omega)
  · apply ((bound remaining).frame 14).bind
    rintro ⟨left, remaining⟩
    apply Bound.bind (intermediate := fun value => 2 * value.2 + 22)
    · exact ((bound remaining).frame 18).weaken (by omega) (fun _ => by omega)
    · rintro ⟨right, remaining⟩
      exact charged_pure_bound _ _ _ _ _ (by omega)
  · exact charged_pure_bound _ _ _ _ _ (by omega)
  · exact fail_bound _ _ _ _

theorem univFromTag_bound {recur : Nat → M (Univ × Nat)}
    (bound : ∀ budget, Bound (recur budget) 16 (2 * budget) (fun value => 2 * value.2 + 4))
    (budget : Nat) (tag : Tag2) :
    Bound (univFromTag recur budget tag) 16 (14 + 2 * budget) (fun value => 2 * value.2 + 4) := by
  unfold univFromTag
  dsimp only
  split
  · exact ((univBody_bound bound _ _).charged _).weaken (by omega) (fun _ => Nat.le_refl _)
  · exact fail_bound _ _ _ _

theorem univFuel_bound (fuel budget : Nat) :
    Bound (univFuel fuel budget) 16 (2 * budget) (fun value => 2 * value.2 + 4) := by
  induction fuel generalizing budget with
  | zero => exact fail_bound _ _ _ _
  | succ fuel ih =>
    exact ((tag2_bound 16 (by decide)).carry (2 * budget)).bind (univFromTag_bound ih budget)

theorem univ_bound (budget : Nat) :
    Bound (univ budget) 16 (2 * budget) (fun value => 2 * value.2 + 4) := by
  intro state valid
  exact univFuel_bound _ budget state valid

theorem univArrayLoop_bound (count budget : Nat) (values : Array Univ) :
    Bound (univArrayLoop count budget values) 16 (2 * budget) (fun value => 2 * value.2) := by
  induction count generalizing budget values with
  | zero => exact pure_bound _ _ _ _ (Nat.le_refl _)
  | succ count ih =>
    unfold univArrayLoop
    apply (univ_bound budget).bind
    rintro ⟨value, remaining⟩
    exact ((ih remaining (values.push value)).charged 2).weaken (by omega) (fun _ => Nat.le_refl _)

/-- One expansion budget is shared across all elements, also when a later
element fails after earlier elements or descendants have consumed work. -/
theorem univArray_bound (count budget : Nat) :
    Bound (univArray count budget) 16 (2 * budget) (fun value => 2 * value.2) :=
  univArrayLoop_bound count budget #[]

end Ixon.Verify.Work
