import IxCC.Cfg.Rc.Proof.Native.TrapActivation
import IxCC.Sem.Forward

/-! The result relation for the physical whole-code induction. Successful
returns retain one owned value, the complete initialized heap invariant,
historical register meanings and external caller denotations. Timeouts use
actual charged prefixes, including time spent inside reclamation routines. -/
set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native.Spec
open IxCC.Cfg.Rc.Proof.Physical.Bridge IxCC.Rt.Rc.Procs IxCC.Own.Rc

structure Returned (P : Program) (pairs : List (Nat × Cfg.Fun)) (lp : Lir.Program)
    (origin : Own.Heap) (originAddresses : AddressMap) (external : Nat → Nat)
    (context base limit : Lir.Word) (regionBytes : Nat) (logical : Fir.Val) where
  heap : Own.Heap
  addresses : AddressMap
  memory : X86.Memory
  bump : Lir.Word
  slots : List Slot
  lists : Nat → List Lir.Word
  frame : Lir.Frame
  value : Own.RVal
  word : Lir.Word
  den : Own.Proof.Den heap value logical
  balance : Balance heap external [value]
  state : HeapState P pairs heap addresses memory external [value]
    context base bump limit regionBytes slots lists
  terminator : Rt.Proof.RetAt lp frame word
  represented : valueWord addresses value = some word
  bounded : Own.Plain.Bounded heap.size value
  compatible : ValueCtorOk (tablesOf P pairs) value
  preserved : Own.Plain.ExternalPreserved origin heap external
  history : HeapHistory origin.size originAddresses heap.size addresses

variable {P : Program} {pairs : List (Nat × Cfg.Fun)} {lp : Lir.Program}
  {H₀ H₁ : Own.Heap} {addresses₀ addresses₁ : AddressMap} {external : Nat → Nat}
  {context base limit : Lir.Word} {regionBytes : Nat}

def Returned.preheap {logical : Fir.Val}
    (after : Returned P pairs lp H₁ addresses₁ external context base limit regionBytes logical)
    (preserved : Own.Plain.ExternalPreserved H₀ H₁ external)
    (history : HeapHistory H₀.size addresses₀ H₁.size addresses₁) :
    Returned P pairs lp H₀ addresses₀ external context base limit regionBytes logical := {
  heap := after.heap
  addresses := after.addresses
  memory := after.memory
  bump := after.bump
  slots := after.slots
  lists := after.lists
  frame := after.frame
  value := after.value
  word := after.word
  den := after.den
  balance := after.balance
  state := after.state
  terminator := after.terminator
  represented := after.represented
  bounded := after.bounded
  compatible := after.compatible
  preserved := fun root value externalRoot den =>
    after.preserved root value externalRoot (preserved root value externalRoot den)
  history := history.trans after.history }

def ResultAt (P : Program) (pairs : List (Nat × Cfg.Fun)) (lp : Lir.Program)
    (origin : Own.Heap) (originAddresses : AddressMap) (external : Nat → Nat)
    (context base limit : Lir.Word) (regionBytes clock : Nat)
    (initial : Lir.State) (callers : List Lir.Frame) : Sem.Result Fir.Val → Prop
  | .ok logical =>
      (∃ after : Returned P pairs lp origin originAddresses external context base limit regionBytes logical,
        ∃ cost, Sem.Star (Lir.semStep lp) initial cost
          {mem := after.memory, ctx := context, stack := after.frame :: callers}) ∨
      Sem.Fails (Lir.semStep lp) initial
  | .trap =>
      (∃ cost final, Sem.Star (Lir.semStep lp) initial cost final ∧ Lir.step lp final = .trap) ∨
      Sem.Fails (Lir.semStep lp) initial
  | .timeout => Sem.Forward.TimeoutOrFail (Lir.semStep lp) initial clock
  | .resource _ => Sem.Fails (Lir.semStep lp) initial
  | .stuck => True

theorem ResultAt.of_fails {clock : Nat} {initial : Lir.State} {callers : List Lir.Frame}
    {result : Sem.Result Fir.Val} (failed : Sem.Fails (Lir.semStep lp) initial) :
    ResultAt P pairs lp H₀ addresses₀ external context base limit regionBytes clock initial callers result := by
  cases result with
  | ok _ | trap => exact .inr failed
  | timeout => exact Sem.Forward.TimeoutOrFail.of_fails failed clock
  | resource _ => exact failed
  | stuck => trivial

theorem fails_prefix {initial middle : Lir.State} {cost : Nat}
    (trace : Sem.Star (Lir.semStep lp) initial cost middle)
    (failed : Sem.Fails (Lir.semStep lp) middle) : Sem.Fails (Lir.semStep lp) initial := by
  obtain ⟨more, final, resource, rest, failure⟩ := failed
  exact ⟨cost + more, final, resource, trace.trans rest, failure⟩

/-- Prefix costs may depend on the heap. The inequality is sufficient for
the original source-clock timeout guarantee; no fixed reclamation cost or
idle-state invariant inside a partially executed release is required. -/
theorem ResultAt.prefix {clock₀ clock₁ cost : Nat} {initial middle : Lir.State}
    {callers : List Lir.Frame} {result : Sem.Result Fir.Val}
    (trace : Sem.Star (Lir.semStep lp) initial cost middle)
    (preserved : Own.Plain.ExternalPreserved H₀ H₁ external)
    (history : HeapHistory H₀.size addresses₀ H₁.size addresses₁)
    (clockBound : clock₀ ≤ clock₁ + cost)
    (execution : ResultAt P pairs lp H₁ addresses₁ external context base limit regionBytes
      clock₁ middle callers result) :
    ResultAt P pairs lp H₀ addresses₀ external context base limit regionBytes clock₀ initial callers result := by
  cases result with
  | ok logical =>
    rcases execution with ⟨after, more, rest⟩ | failed
    · exact .inl ⟨after.preheap preserved history, cost + more, trace.trans rest⟩
    · exact .inr (fails_prefix trace failed)
  | trap =>
    rcases execution with ⟨more, final, rest, trapped⟩ | failed
    · exact .inl ⟨cost + more, final, trace.trans rest, trapped⟩
    · exact .inr (fails_prefix trace failed)
  | timeout =>
    exact Sem.Forward.TimeoutOrFail.star trace fun enough => execution.down (by omega)
  | resource resource => exact fails_prefix trace execution
  | stuck => trivial

theorem ResultAt.charge {clock cost : Nat} {initial middle : Lir.State}
    {callers : List Lir.Frame} {body : Nat → Sem.Result Fir.Val}
    (trace : Sem.Star (Lir.semStep lp) initial cost middle) (charged : 1 ≤ cost)
    (preserved : Own.Plain.ExternalPreserved H₀ H₁ external)
    (history : HeapHistory H₀.size addresses₀ H₁.size addresses₁)
    (next : ∀ smaller, clock = smaller + 1 →
      ResultAt P pairs lp H₁ addresses₁ external context base limit regionBytes smaller middle callers (body smaller)) :
    ResultAt P pairs lp H₀ addresses₀ external context base limit regionBytes clock initial callers
      (Sem.later clock body) := by
  cases clock with
  | zero => exact .inl (Sem.Reaches.timeout_of_star trace (by omega))
  | succ smaller =>
    exact ResultAt.prefix trace preserved history (by omega) (next smaller rfl)






end IxCC.Cfg.Rc.Native.Spec
