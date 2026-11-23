import IxCC.Cfg.Rc.Proof.Native.Activation
import IxCC.Cfg.Rc.Proof.Native.HeapHistory
import IxCC.Own.Plain.Proof.Results
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
    (context base limit : Lir.Word) (regionBytes : Nat) (logical : Fir.Val)
    (ctors : List Lam.CtorInfo := []) (retUniq : Bool := false)
    (priv : Nat → Prop := fun _ => False) where
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
  reachable : Own.Plain.ReachablePreserved origin heap external
  history : HeapHistory origin.size originAddresses heap.size addresses
  privPreserved : Own.Plain.PrivPreserved origin heap priv
  retNoPriv : ∀ k, priv k → value ≠ .loc k
  uniqRet : retUniq = true → Own.Plain.UniqVal ctors heap external [value] value

variable {P : Program} {pairs : List (Nat × Cfg.Fun)} {lp : Lir.Program}
  {H₀ H₁ : Own.Heap} {addresses₀ addresses₁ : AddressMap} {external : Nat → Nat}
  {context base limit : Lir.Word} {regionBytes : Nat}
  {ctors ctors' : List Lam.CtorInfo} {retUniq retUniq' : Bool} {priv priv' : Nat → Prop}

def Returned.preheap {logical : Fir.Val}
    (after : Returned P pairs lp H₁ addresses₁ external context base limit regionBytes logical
      ctors retUniq priv)
    (reachable : Own.Plain.ReachablePreserved H₀ H₁ external)
    (hpriv : Own.Plain.PrivPreserved H₀ H₁ priv)
    (history : HeapHistory H₀.size addresses₀ H₁.size addresses₁) :
    Returned P pairs lp H₀ addresses₀ external context base limit regionBytes logical
      ctors retUniq priv := {
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
  preserved := (reachable.trans after.reachable).externalPreserved
  reachable := reachable.trans after.reachable
  history := history.trans after.history
  privPreserved := hpriv.trans after.privPreserved
  retNoPriv := after.retNoPriv
  uniqRet := after.uniqRet }

def Returned.weaken {logical : Fir.Val}
    (after : Returned P pairs lp H₀ addresses₀ external context base limit regionBytes logical
      ctors retUniq priv)
    (hret : retUniq' = true → retUniq = true ∧ ctors' = ctors)
    (hpriv : ∀ l, priv' l → priv l) :
    Returned P pairs lp H₀ addresses₀ external context base limit regionBytes logical
      ctors' retUniq' priv' := {
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
  preserved := after.preserved
  reachable := after.reachable
  history := after.history
  privPreserved := after.privPreserved.mono hpriv
  retNoPriv := fun k hk => after.retNoPriv k (hpriv k hk)
  uniqRet := fun hr => by
    obtain ⟨hr1, hc⟩ := hret hr
    subst hc
    exact after.uniqRet hr1 }

def ResultAt (P : Program) (pairs : List (Nat × Cfg.Fun)) (lp : Lir.Program)
    (origin : Own.Heap) (originAddresses : AddressMap) (external : Nat → Nat)
    (context base limit : Lir.Word) (regionBytes clock : Nat)
    (initial : Lir.State) (callers : List Lir.Frame) (result : Sem.Result Fir.Val)
    (ctors : List Lam.CtorInfo := []) (retUniq : Bool := false)
    (priv : Nat → Prop := fun _ => False) : Prop :=
  match result with
  | .ok logical =>
      (∃ after : Returned P pairs lp origin originAddresses external context base limit regionBytes
          logical ctors retUniq priv,
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
    ResultAt P pairs lp H₀ addresses₀ external context base limit regionBytes clock initial callers
      result ctors retUniq priv := by
  cases result with
  | ok _ | trap => exact .inr failed
  | timeout => exact Sem.Forward.TimeoutOrFail.of_fails failed clock
  | resource _ => exact failed
  | stuck => trivial

theorem ResultAt.weaken {clock : Nat} {initial : Lir.State} {callers : List Lir.Frame}
    {result : Sem.Result Fir.Val}
    (hret : retUniq' = true → retUniq = true ∧ ctors' = ctors)
    (hpriv : ∀ l, priv' l → priv l)
    (execution : ResultAt P pairs lp H₀ addresses₀ external context base limit regionBytes clock
      initial callers result ctors retUniq priv) :
    ResultAt P pairs lp H₀ addresses₀ external context base limit regionBytes clock initial callers
      result ctors' retUniq' priv' := by
  cases result with
  | ok logical =>
    rcases execution with ⟨after, cost, trace⟩ | failed
    · exact .inl ⟨after.weaken hret hpriv, cost, trace⟩
    · exact .inr failed
  | trap | timeout | resource _ | stuck => exact execution

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
    (reachable : Own.Plain.ReachablePreserved H₀ H₁ external)
    (hpriv : Own.Plain.PrivPreserved H₀ H₁ priv)
    (history : HeapHistory H₀.size addresses₀ H₁.size addresses₁)
    (clockBound : clock₀ ≤ clock₁ + cost)
    (execution : ResultAt P pairs lp H₁ addresses₁ external context base limit regionBytes
      clock₁ middle callers result ctors retUniq priv) :
    ResultAt P pairs lp H₀ addresses₀ external context base limit regionBytes clock₀ initial callers
      result ctors retUniq priv := by
  cases result with
  | ok logical =>
    rcases execution with ⟨after, more, rest⟩ | failed
    · exact .inl ⟨after.preheap reachable hpriv history, cost + more, trace.trans rest⟩
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
    (reachable : Own.Plain.ReachablePreserved H₀ H₁ external)
    (hpriv : Own.Plain.PrivPreserved H₀ H₁ priv)
    (history : HeapHistory H₀.size addresses₀ H₁.size addresses₁)
    (next : ∀ smaller, clock = smaller + 1 →
      ResultAt P pairs lp H₁ addresses₁ external context base limit regionBytes smaller middle
        callers (body smaller) ctors retUniq priv) :
    ResultAt P pairs lp H₀ addresses₀ external context base limit regionBytes clock initial callers
      (Sem.later clock body) ctors retUniq priv := by
  cases clock with
  | zero => exact .inl (Sem.Reaches.timeout_of_star trace (by omega))
  | succ smaller =>
    exact ResultAt.prefix trace reachable hpriv history (by omega) (next smaller rfl)






end IxCC.Cfg.Rc.Native.Spec
