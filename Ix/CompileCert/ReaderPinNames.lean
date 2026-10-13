import Ix.CompileCert.ReaderAdmissionRecords
import Ix.CompileCert.Canon.Loop

/-! The actual pin-table checks establish name separation and injection.
These are internal anonymous-reference identities, not presentation metadata. -/

namespace Ix.CompileCert.ReaderPinNames

open Ix Kernel.Reader
open _root_.Ix.Kernel (ConstRef)

abbrev Names := Std.HashMap (ConstRef Address) Kernel.Name
abbrev PinState := Names × Std.HashSet Kernel.Name

def Safe (names : Names) : Prop :=
  ∀ (ref : ConstRef Address) (name : Kernel.Name), names[ref]? = some name →
    rootComponent name ≠ some "ix" ∧ derivedShape name = false

def Injective (names : Names) : Prop :=
  ∀ (left right : ConstRef Address) (name : Kernel.Name),
    names[left]? = some name → names[right]? = some name → left = right

structure Valid (state : PinState) : Prop where
  safe : Safe state.1
  injective : Injective state.1
  seen : ∀ (ref : ConstRef Address) (name : Kernel.Name), state.1[ref]? = some name → state.2.contains name = true

theorem valid_empty : Valid (({} : Names), ({} : Std.HashSet Kernel.Name)) := by
  constructor
  · intro ref name found; simp at found
  · intro left right name first; simp at first
  · intro ref name found; simp at found

theorem valid_insert (before : PinState) (pin : Pin) (valid : Valid before)
    (reserved : rootComponent pin.name ≠ some "ix") (derived : derivedShape pin.name = false)
    (fresh : before.2.contains pin.name = false) :
    Valid (before.1.insert pin.ref pin.name, before.2.insert pin.name) := by
  constructor
  · intro ref name found
    rw [Std.HashMap.getElem?_insert] at found
    split at found
    · cases Option.some.inj found
      exact ⟨reserved, derived⟩
    · exact valid.safe ref name found
  · intro left right name first second
    by_cases sameLeft : pin.ref == left <;> by_cases sameRight : pin.ref == right
    · exact (beq_iff_eq.mp sameLeft).symm.trans (beq_iff_eq.mp sameRight)
    · simp only [Std.HashMap.getElem?_insert, sameLeft, sameRight, Bool.false_eq_true, ↓reduceIte] at first second
      have nameEq := Option.some.inj first
      have seen := valid.seen right name second
      rw [← nameEq, fresh] at seen
      cases seen
    · simp only [Std.HashMap.getElem?_insert, sameLeft, sameRight, Bool.false_eq_true, ↓reduceIte] at first second
      have nameEq := Option.some.inj second
      have seen := valid.seen left name first
      rw [← nameEq, fresh] at seen
      cases seen
    · simp only [Std.HashMap.getElem?_insert, sameLeft, sameRight, Bool.false_eq_true, ↓reduceIte] at first second
      exact valid.injective left right name first second
  · intro ref name found
    rw [Std.HashMap.getElem?_insert] at found
    split at found
    · cases Option.some.inj found
      simp
    · have seen := valid.seen ref name found
      simp [seen]

def step (pin : Pin) (before : PinState) : Except String (ForInStep PinState) := do
  if rootComponent pin.name == some "ix" then throw s!"pin {pin.name} is under the reserved root"
  if derivedShape pin.name then throw s!"pin {pin.name} has a derived shape"
  if before.2.contains pin.name then throw s!"pin {pin.name} is assigned twice"
  if before.1.contains pin.ref then throw s!"pin {pin.name}: its reference is pinned twice"
  pure (.yield (before.1.insert pin.ref pin.name, before.2.insert pin.name))

def run (pins : Array Pin) : Except String Names := do
  let after ← forIn pins (({} : Names), ({} : Std.HashSet Kernel.Name)) step
  pure after.1

theorem run_eq (pins : Array Pin) : run pins = pinMap pins := by
  unfold run step pinMap
  rfl

theorem step_valid (pin : Pin) (before : PinState) (valid : Valid before)
    (result : ForInStep PinState) (ran : step pin before = .ok result) :
    ∃ after, result = .yield after ∧ Valid after := by
  by_cases reserved : (rootComponent pin.name == some "ix") = true
  · simp [step, reserved, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at ran
  · by_cases derived : derivedShape pin.name = true
    · simp [step, reserved, derived, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at ran
    · by_cases fresh : before.2.contains pin.name = true
      · simp [step, reserved, derived, fresh, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at ran
      · by_cases refFresh : before.1.contains pin.ref = true
        · simp [step, reserved, derived, fresh, refFresh, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at ran
        · simp only [step, reserved, derived, fresh, refFresh, pure, Except.pure, bind, Except.bind] at ran
          cases Except.ok.inj ran
          exact ⟨_, rfl, valid_insert before pin valid
            (fun same => reserved (beq_iff_eq.mpr same))
            (Bool.eq_false_iff.mpr derived) (Bool.eq_false_iff.mpr fresh)⟩

/-- Successful production pin validation supplies injection and excludes both
the encoded-address namespace and generated recursor/projection shapes. -/
theorem pinMap_valid (pins : Array Pin) (names : Names) (ran : pinMap pins = .ok names) :
    Safe names ∧ Injective names := by
  rw [← run_eq] at ran
  unfold run at ran
  obtain ⟨after, loop, returned⟩ := Sharing.Verify.except_bind_eq_ok ran
  have valid := Canon.forIn_except_array step (fun _ state => Valid state)
    (fun _ pin before result good ran => step_valid pin before good result ran) pins valid_empty loop
  cases Except.ok.inj returned
  exact ⟨valid.safe, valid.injective⟩

theorem defaultPins_valid (pins : Pins) (ran : defaultPins = .ok pins) : Safe pins.names ∧ Injective pins.names := by
  unfold defaultPins at ran
  generalize tableEq : pinTable = tableResult at ran
  generalize levelsEq : levelTable = levelResult at ran
  cases tableResult with
  | error reason => simp [bind, Except.bind] at ran
  | ok pinRows =>
    simp only [bind, Except.bind] at ran
    cases checked : pinMap pinRows with
    | error reason => simp [checked] at ran
    | ok names =>
      cases levelResult with
      | error reason => simp [checked] at ran
      | ok levels =>
        simp only [checked, pure, Except.pure, Except.ok.injEq] at ran
        cases ran
        exact pinMap_valid pinRows names checked

end Ix.CompileCert.ReaderPinNames
