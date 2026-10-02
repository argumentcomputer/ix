import Ix.Ixon.Codec

/-! Work accounting for the executed record grammar.

The accounting interpreter keeps work on both success and failure. Erasure
lemmas relate it to the production reader, including the error text, buffer,
and cursor. A resource bound composes a byte potential with input/output
credits, so a successful prefix can pay for collection or constructor work
in its continuation. Exactly one terminal read failure receives the extra
unit; nested binds cannot reset that allowance.

Units describe parser operations and explicitly charged bulk work, not heap
bytes or wall-clock time. The production decoder does not execute counters.
Primitive byte access charges an attempt; a successful bulk read additionally
charges each copied byte. Grammar-specific construction/iteration charges
are introduced with `charge` and must be funded in the bound proof.
-/

namespace Ixon.Verify.Work

open _root_.Ixon

abbrev Outcome (α : Type) := EStateM.Result String GetState α
abbrev M (α : Type) := GetState → Outcome α × Nat

def pure (value : α) : M α := fun state => (.ok value state, 0)
def fail (reason : String) : M α := fun state => (.error reason state, 0)

def bind (first : M α) (next : α → M β) : M β := fun start =>
  let (head, spent) := first start
  match head with
  | .error reason finish => (.error reason finish, spent)
  | .ok value middle =>
    let (tail, more) := next value middle
    (tail, spent + more)

instance : Monad M where
  pure := pure
  bind := bind

theorem bind_pure_left (value : α) (next : α → M β) : bind (pure value) next = next value := by
  funext state
  simp [bind, pure]

theorem bind_fail_left (reason : String) (next : α → M β) :
    bind (fail reason) next = fail reason := rfl

def charge (amount : Nat) : M Unit := fun state => (.ok () state, amount)

def charged (amount : Nat) (reader : M α) : M α := bind (charge amount) fun _ => reader

def erase (reader : M α) : GetM α := fun state => (reader state).1

/-- Relate the complete result, including failures and their exact cursor. -/
def Erases (metered : M α) (production : GetM α) : Prop := erase metered = production

theorem pure_erases (value : α) : Erases (pure value) (Pure.pure value) := rfl
theorem fail_erases (reason : String) : Erases (fail (α := α) reason) (throw reason) := rfl
theorem charge_erases (amount : Nat) : Erases (charge amount) (Pure.pure ()) := rfl

theorem Erases.charged {metered : M α} {production : GetM α}
    (h : Erases metered production) (amount : Nat) : Erases (charged amount metered) production := by
  funext state
  have same := congrFun h state
  simpa [erase, Work.charged, Work.bind, charge] using same

theorem Erases.bind {first : M α} {next : α → M β} {reader : GetM α} {rest : α → GetM β}
    (head : Erases first reader) (tail : ∀ value, Erases (next value) (rest value)) :
    Erases (bind first next) (reader >>= rest) := by
  funext state
  have h := congrFun head state
  cases parsed : first state with
  | mk result spent =>
    cases result with
    | error reason finish =>
      simp only [erase, parsed] at h
      simp [erase, Work.bind, parsed, ← h, Bind.bind, EStateM.bind]
    | ok value middle =>
      simp only [erase, parsed] at h
      have t := congrFun (tail value) middle
      cases continued : next value middle with
      | mk result more =>
        simp only [erase, continued] at t
        simp [erase, Work.bind, parsed, continued, ← h, ← t, Bind.bind, EStateM.bind]

def finish : Outcome α → GetState
  | .ok _ state | .error _ state => state

/-- Cursor progress for all results, not just successful decoded values. -/
structure Progress (start stop : GetState) : Prop where
  bytes : stop.bytes = start.bytes
  monotone : start.idx ≤ stop.idx
  within : stop.idx ≤ start.bytes.size

theorem Progress.valid {start stop} (h : Progress start stop) : stop.idx ≤ stop.bytes.size := by
  simpa [h.bytes] using h.within

theorem Progress.refl (state : GetState) (valid : state.idx ≤ state.bytes.size) :
    Progress state state := ⟨rfl, Nat.le_refl _, valid⟩

theorem Progress.trans {start middle stop} (first : Progress start middle)
    (second : Progress middle stop) : Progress start stop :=
  ⟨second.bytes.trans first.bytes, Nat.le_trans first.monotone second.monotone,
    by simpa [first.bytes] using second.within⟩

theorem Progress.distance {start middle stop} (first : Progress start middle)
    (second : Progress middle stop) :
    stop.idx - start.idx = (middle.idx - start.idx) + (stop.idx - middle.idx) := by
  have := first.monotone
  have := second.monotone
  omega

def Costs (start : GetState) (result : Outcome α) (spent rate credit : Nat)
    (remaining : α → Nat) : Prop :=
  Progress start (finish result) ∧
    match result with
    | .ok value stop => spent + remaining value ≤ rate * (stop.idx - start.idx) + credit
    | .error _ stop => spent ≤ rate * (stop.idx - start.idx) + credit + 1

def Bound (reader : M α) (rate credit : Nat) (remaining : α → Nat) : Prop :=
  ∀ start, start.idx ≤ start.bytes.size →
    Costs start (reader start).1 (reader start).2 rate credit remaining

theorem pure_bound (rate credit : Nat) (remaining : α → Nat) (value : α)
    (paid : remaining value ≤ credit) : Bound (pure value) rate credit remaining := by
  intro state valid
  exact ⟨Progress.refl state valid, by simpa [pure] using paid⟩

theorem fail_bound (rate credit : Nat) (remaining : α → Nat) (reason : String) :
    Bound (fail reason) rate credit remaining := by
  intro state valid
  exact ⟨Progress.refl state valid, by simp [fail]⟩

theorem charge_bound (rate amount remaining : Nat) :
    Bound (charge amount) rate (amount + remaining) (fun _ => remaining) := by
  intro state valid
  exact ⟨Progress.refl state valid, by simp [charge]⟩

/-- The continuation receives exactly the credit produced by the prefix.
On a continuation failure, the prefix's successful bound contributes no
extra terminal allowance; there is only one failure in the combined run. -/
theorem Bound.bind {first : M α} {next : α → M β} {rate credit : Nat}
    {intermediate : α → Nat} {remaining : β → Nat}
    (head : Bound first rate credit intermediate)
    (tail : ∀ value, Bound (next value) rate (intermediate value) remaining) :
    Bound (bind first next) rate credit remaining := by
  intro start valid
  have h := head start valid
  cases parsed : first start with
  | mk result spent =>
    cases result with
    | error reason stop =>
      simpa [Costs, Work.bind, parsed, finish] using h
    | ok value middle =>
      simp only [Costs, parsed, finish] at h
      have t := tail value middle h.1.valid
      cases continued : next value middle with
      | mk result more =>
        cases result with
        | error reason stop =>
          simp only [Costs, continued, finish] at t
          have distance := h.1.distance t.1
          have sum := congrArg (rate * ·) distance
          rw [Nat.mul_add] at sum
          exact ⟨by simpa [Work.bind, parsed, continued, finish] using h.1.trans t.1,
            by simpa [Work.bind, parsed, continued] using (show spent + more ≤ rate * (stop.idx - start.idx) + credit + 1 by omega)⟩
        | ok output stop =>
          simp only [Costs, continued, finish] at t
          have distance := h.1.distance t.1
          have sum := congrArg (rate * ·) distance
          rw [Nat.mul_add] at sum
          exact ⟨by simpa [Work.bind, parsed, continued, finish] using h.1.trans t.1,
            by simpa [Work.bind, parsed, continued] using (show spent + more + remaining output ≤ rate * (stop.idx - start.idx) + credit by omega)⟩

/-- Raising input credit or lowering promised output credit preserves a
bound. This is resource weakening, not a new parser operation. -/
theorem Bound.weaken {reader : M α} {rate credit larger : Nat} {remaining smaller : α → Nat}
    (h : Bound reader rate credit remaining) (before : credit ≤ larger)
    (after : ∀ value, smaller value ≤ remaining value) : Bound reader rate larger smaller := by
  intro start valid
  have bound := h start valid
  cases parsed : reader start with
  | mk result spent =>
    cases result with
    | error reason stop =>
      simp only [Costs, parsed] at bound ⊢
      exact ⟨bound.1, by have := bound.2; omega⟩
    | ok value stop =>
      simp only [Costs, parsed] at bound ⊢
      exact ⟨bound.1, by have := bound.2; have := after value; omega⟩

/-- Carry unused credit through a parser; a failure retains the prefix's
spent work and discards the unused output credit. -/
theorem Bound.frame {reader : M α} {rate credit : Nat} {remaining : α → Nat}
    (h : Bound reader rate credit remaining) (extra : Nat) :
    Bound reader rate (credit + extra) (fun value => remaining value + extra) := by
  intro start valid
  have bound := h start valid
  cases parsed : reader start with
  | mk result spent =>
    cases result with
    | error reason stop =>
      simp only [Costs, parsed] at bound ⊢
      exact ⟨bound.1, by have := bound.2; omega⟩
    | ok value stop =>
      simp only [Costs, parsed] at bound ⊢
      exact ⟨bound.1, by have := bound.2; omega⟩

theorem Bound.charged {reader : M α} {rate credit : Nat} {remaining : α → Nat}
    (h : Bound reader rate credit remaining) (amount : Nat) :
    Bound (charged amount reader) rate (amount + credit) remaining :=
  (charge_bound rate amount credit).bind fun _ => h

theorem Bound.carry {reader : M α} {rate : Nat} {remaining : α → Nat}
    (h : Bound reader rate 0 remaining) (extra : Nat) :
    Bound reader rate extra (fun value => remaining value + extra) := by
  simpa only [Nat.zero_add] using h.frame extra

/-- A continuation needing no incoming credit can discard prefix surplus. -/
theorem Bound.bind_zero {first : M α} {next : α → M β} {rate credit : Nat}
    {intermediate : α → Nat} {remaining : β → Nat}
    (head : Bound first rate credit intermediate)
    (tail : ∀ value, Bound (next value) rate 0 remaining) :
    Bound (Work.bind first next) rate credit remaining :=
  head.bind fun value => (tail value).weaken (Nat.zero_le _) (fun _ => Nat.le_refl _)

theorem charged_pure_bound (rate credit : Nat) (remaining : α → Nat)
    (amount : Nat) (value : α) (paid : amount + remaining value ≤ credit) :
    Bound (charged amount (pure value)) rate credit remaining :=
  ((pure_bound rate (remaining value) remaining value (Nat.le_refl _)).charged amount).weaken
    paid (fun _ => Nat.le_refl _)

theorem Bound.work_le {reader : M α} {rate credit : Nat} {remaining : α → Nat}
    (bound : Bound reader rate credit remaining) (start : GetState)
    (valid : start.idx ≤ start.bytes.size) :
    (reader start).2 ≤ rate * (start.bytes.size - start.idx) + credit + 1 := by
  have h := bound start valid
  cases parsed : reader start with
  | mk result spent =>
    cases result with
    | error reason stop =>
      simp only [Costs, parsed, finish] at h
      have limit := Nat.mul_le_mul_left rate (Nat.sub_le_sub_right h.1.within start.idx)
      have := h.2
      omega
    | ok value stop =>
      simp only [Costs, parsed, finish] at h
      have limit := Nat.mul_le_mul_left rate (Nat.sub_le_sub_right h.1.within start.idx)
      have := h.2
      omega

def u8 : M UInt8 := fun state => (getU8 state, 1)

def bytes (count : Nat) : M ByteArray := fun state =>
  let result := getBytes count state
  (result, match result with | .ok .. => count + 1 | .error .. => 1)

theorem u8_erases : Erases u8 getU8 := rfl
theorem bytes_erases (count : Nat) : Erases (bytes count) (getBytes count) := rfl

theorem getU8_run (state : GetState) : getU8 state =
    if state.idx < state.bytes.size then
      .ok state.bytes[state.idx]! { state with idx := state.idx + 1 }
    else .error "EOF" state := by
  unfold getU8
  change (EStateM.bind (EStateM.get : GetM GetState) _) state = _
  simp only [EStateM.bind, EStateM.get]
  split <;> rfl

theorem getBytes_run (count : Nat) (state : GetState) : getBytes count state =
    if state.idx + count ≤ state.bytes.size then
      .ok (state.bytes.extract state.idx (state.idx + count)) { state with idx := state.idx + count }
    else .error s!"EOF: need {count} bytes at index {state.idx}, but size is {state.bytes.size}" state := by
  unfold getBytes
  change (EStateM.bind (EStateM.get : GetM GetState) _) state = _
  simp only [EStateM.bind, EStateM.get]
  split <;> rfl

theorem u8_bound (rate : Nat) (positive : 0 < rate) :
    Bound u8 rate 0 (fun _ => rate - 1) := by
  intro start valid
  by_cases fits : start.idx < start.bytes.size
  · simp only [u8, getU8_run, ite_eq_left fits, Costs, finish]
    exact ⟨⟨rfl, by simp, by dsimp; omega⟩, by dsimp; simp; omega⟩
  · simp only [u8, getU8_run, ite_eq_right fits, Costs, finish]
    exact ⟨Progress.refl start valid, by simp⟩

theorem bytes_bound (count : Nat) : Bound (bytes count) 1 1 (fun _ => 0) := by
  intro start valid
  by_cases fits : start.idx + count ≤ start.bytes.size
  · simp only [bytes, getBytes_run, ite_eq_left fits, Costs, finish]
    exact ⟨⟨rfl, by simp, fits⟩, by simp⟩
  · simp only [bytes, getBytes_run, ite_eq_right fits, Costs, finish]
    exact ⟨Progress.refl start valid, by simp⟩

end Ixon.Verify.Work
