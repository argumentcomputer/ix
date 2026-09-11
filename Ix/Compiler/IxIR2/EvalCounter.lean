import Ix.Compiler.IxIR1.Sim
import Ix.Compiler.IxIR2.Eval

/-!
# IxIR₂ credit-counter algebra

`CounterLaw` is the numeric projection of the logical/physical heap relation.
The local lemmas below cover every operation that can change the number of
present credits.  They are intentionally independent of a particular CFG;
the later heap-isomorphism simulation composes these deltas along machine
steps.
-/

namespace Ix.Compiler.IxIR2.Eval

/-! ## Credit-local heap relation -/

/-- Runtime credits agree in layout and presence.  A present physical credit
additionally owns an actual empty in-bounds slot; the logical credit carries
layout only because its corresponding node has already been freed. -/
inductive CreditIso (physical : Store) : Option Credit → Option Credit → Prop
  | consumed : CreditIso physical none none
  | absent (layout : LayoutId) :
      CreditIso physical
        (some { layout, presence := .absent })
        (some { layout, presence := .absent })
  | present (layout : LayoutId) (slot : Nat)
      (reserved : (physical.heap.nodes)[slot]? = some none) :
      CreditIso physical
        (some { layout, presence := .present none })
        (some { layout, presence := .present (some slot) })

inductive CreditsIso (physical : Store) :
    List (Option Credit) → List (Option Credit) → Prop
  | nil : CreditsIso physical [] []
  | cons {logicalCredit physicalCredit logicalCredits physicalCredits} :
      CreditIso physical logicalCredit physicalCredit →
      CreditsIso physical logicalCredits physicalCredits →
      CreditsIso physical (logicalCredit :: logicalCredits)
        (physicalCredit :: physicalCredits)

/-- Counter state plus the derived live-node observation. -/
structure Snapshot where
  counters : Counters
  live : Nat
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

def Store.snapshot (store : Store) : Snapshot :=
  { counters := store.counters, live := store.live }

/-- The advertised intermediate relation, extended with the reset observations
that both interpretations share. -/
structure CounterLaw (logical physical : Snapshot) (presentCredits : Nat) :
    Prop where
  allocs : logical.counters.allocs =
    physical.counters.allocs + physical.counters.reuses
  frees : logical.counters.frees =
    physical.counters.frees + physical.counters.reuses + presentCredits
  rcops : logical.counters.rcops = physical.counters.rcops
  live : logical.live = physical.live
  resetAttempts : logical.counters.resetAttempts =
    physical.counters.resetAttempts
  hotResets : logical.counters.hotResets = physical.counters.hotResets
  coldResets : logical.counters.coldResets = physical.counters.coldResets

instance (logical physical : Snapshot) (presentCredits : Nat) :
    Decidable (CounterLaw logical physical presentCredits) :=
  if allocs : logical.counters.allocs =
      physical.counters.allocs + physical.counters.reuses then
    if frees : logical.counters.frees =
        physical.counters.frees + physical.counters.reuses + presentCredits then
      if rcops : logical.counters.rcops = physical.counters.rcops then
        if live : logical.live = physical.live then
          if attempts : logical.counters.resetAttempts =
              physical.counters.resetAttempts then
            if hot : logical.counters.hotResets = physical.counters.hotResets then
              if cold : logical.counters.coldResets =
                  physical.counters.coldResets then
                isTrue ⟨allocs, frees, rcops, live, attempts, hot, cold⟩
              else isFalse fun relation => cold relation.coldResets
            else isFalse fun relation => hot relation.hotResets
          else isFalse fun relation => attempts relation.resetAttempts
        else isFalse fun relation => live relation.live
      else isFalse fun relation => rcops relation.rcops
    else isFalse fun relation => frees relation.frees
  else isFalse fun relation => allocs relation.allocs

/-- The interface used by the later logical/physical step simulation: a live
heap bijection, pointwise credit authority, and the numeric counter law. -/
structure CreditHeapIso (logical physical : Store)
    (logicalCredits physicalCredits : Array (Option Credit)) where
  heap : IxIR1.Sim.HeapIso logical.heap physical.heap
  credits : CreditsIso physical logicalCredits.toList physicalCredits.toList
  counters : CounterLaw logical.snapshot physical.snapshot
    (creditPresentCount physicalCredits)

namespace Snapshot

def logicalTake (state : Snapshot) : Snapshot :=
  { state with
    counters := { state.counters with frees := state.counters.frees + 1 }
    live := state.live - 1 }

def physicalTake (state : Snapshot) : Snapshot :=
  { state with live := state.live - 1 }

def logicalHotReset (state : Snapshot) : Snapshot :=
  { logicalTake state with
    counters :=
      { (logicalTake state).counters with
        resetAttempts := state.counters.resetAttempts + 1
        hotResets := state.counters.hotResets + 1 } }

def physicalHotReset (state : Snapshot) : Snapshot :=
  { physicalTake state with
    counters :=
      { (physicalTake state).counters with
        resetAttempts := state.counters.resetAttempts + 1
        hotResets := state.counters.hotResets + 1 } }

def logicalReuse (state : Snapshot) : Snapshot :=
  { state with
    counters := { state.counters with allocs := state.counters.allocs + 1 }
    live := state.live + 1 }

def physicalReuse (state : Snapshot) (payloadUnits : Nat) : Snapshot :=
  { state with
    counters :=
      { state.counters with
        reuses := state.counters.reuses + 1
        reusedPayloadUnits := state.counters.reusedPayloadUnits + payloadUnits }
    live := state.live + 1 }

def logicalDiscard (state : Snapshot) : Snapshot := state

def physicalDiscard (state : Snapshot) : Snapshot :=
  { state with
    counters := { state.counters with frees := state.counters.frees + 1 } }

def freshAlloc (state : Snapshot) : Snapshot :=
  { state with
    counters := { state.counters with allocs := state.counters.allocs + 1 }
    live := state.live + 1 }

def coldReset (state : Snapshot) (rcDelta : Nat) : Snapshot :=
  { state with
    counters :=
      { state.counters with
        rcops := state.counters.rcops + rcDelta
        resetAttempts := state.counters.resetAttempts + 1
        coldResets := state.counters.coldResets + 1 } }

end Snapshot

namespace CounterLaw

theorem empty : CounterLaw (default : Snapshot) (default : Snapshot) 0 := by
  constructor <;> rfl

theorem afterTake {logical physical : Snapshot} {presentCredits : Nat}
    (relation : CounterLaw logical physical presentCredits) :
    CounterLaw logical.logicalTake physical.physicalTake
      (presentCredits + 1) := by
  rcases relation with ⟨allocs, frees, rcops, live, attempts, hot, cold⟩
  constructor
  · exact allocs
  · simp only [Snapshot.logicalTake, Snapshot.physicalTake]
    omega
  · exact rcops
  · simp only [Snapshot.logicalTake, Snapshot.physicalTake]
    omega
  · exact attempts
  · exact hot
  · exact cold

theorem afterHotReset {logical physical : Snapshot} {presentCredits : Nat}
    (relation : CounterLaw logical physical presentCredits) :
    CounterLaw logical.logicalHotReset physical.physicalHotReset
      (presentCredits + 1) := by
  rcases relation with ⟨allocs, frees, rcops, live, attempts, hot, cold⟩
  constructor
  · exact allocs
  · simp only [Snapshot.logicalHotReset, Snapshot.physicalHotReset,
      Snapshot.logicalTake, Snapshot.physicalTake]
    omega
  · exact rcops
  · simp only [Snapshot.logicalHotReset, Snapshot.physicalHotReset,
      Snapshot.logicalTake, Snapshot.physicalTake]
    omega
  · simp only [Snapshot.logicalHotReset, Snapshot.physicalHotReset,
      Snapshot.logicalTake, Snapshot.physicalTake]
    omega
  · simp only [Snapshot.logicalHotReset, Snapshot.physicalHotReset,
      Snapshot.logicalTake, Snapshot.physicalTake]
    omega
  · exact cold

theorem afterReuse {logical physical : Snapshot} {presentCredits : Nat}
    (payloadUnits : Nat)
    (relation : CounterLaw logical physical (presentCredits + 1)) :
    CounterLaw logical.logicalReuse (physical.physicalReuse payloadUnits)
      presentCredits := by
  rcases relation with ⟨allocs, frees, rcops, live, attempts, hot, cold⟩
  constructor
  · simp only [Snapshot.logicalReuse, Snapshot.physicalReuse]
    omega
  · simp only [Snapshot.logicalReuse, Snapshot.physicalReuse]
    omega
  · exact rcops
  · simp only [Snapshot.logicalReuse, Snapshot.physicalReuse]
    omega
  · exact attempts
  · exact hot
  · exact cold

theorem afterDiscard {logical physical : Snapshot} {presentCredits : Nat}
    (relation : CounterLaw logical physical (presentCredits + 1)) :
    CounterLaw logical.logicalDiscard physical.physicalDiscard
      presentCredits := by
  rcases relation with ⟨allocs, frees, rcops, live, attempts, hot, cold⟩
  constructor
  · exact allocs
  · simp only [Snapshot.logicalDiscard, Snapshot.physicalDiscard]
    omega
  · exact rcops
  · exact live
  · exact attempts
  · exact hot
  · exact cold

theorem afterFreshAlloc {logical physical : Snapshot} {presentCredits : Nat}
    (relation : CounterLaw logical physical presentCredits) :
    CounterLaw logical.freshAlloc physical.freshAlloc presentCredits := by
  rcases relation with ⟨allocs, frees, rcops, live, attempts, hot, cold⟩
  constructor
  · simp only [Snapshot.freshAlloc]
    omega
  · simpa only [Snapshot.freshAlloc] using frees
  · exact rcops
  · simp only [Snapshot.freshAlloc]
    omega
  · exact attempts
  · exact hot
  · exact cold

theorem afterColdReset {logical physical : Snapshot} {presentCredits rcDelta : Nat}
    (relation : CounterLaw logical physical presentCredits) :
    CounterLaw (logical.coldReset rcDelta) (physical.coldReset rcDelta)
      presentCredits := by
  rcases relation with ⟨allocs, frees, rcops, live, attempts, hot, cold⟩
  constructor
  · exact allocs
  · exact frees
  · simp only [Snapshot.coldReset]
    omega
  · exact live
  · simp only [Snapshot.coldReset]
    omega
  · exact hot
  · simp only [Snapshot.coldReset]
    omega

/-- At a validated terminal state there are no present credits, yielding the
terminal free equation directly. -/
theorem terminalFrees {logical physical : Snapshot}
    (relation : CounterLaw logical physical 0) :
    logical.counters.frees =
      physical.counters.frees + physical.counters.reuses := by
  simpa using relation.frees

end CounterLaw

end Ix.Compiler.IxIR2.Eval
