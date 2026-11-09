import IxCC.Recheck.Rc.Proof.PublicRelease
import IxCC.Cfg.Rc.Proof.Physical.NumericInputs
import IxCC.Cfg.Rc.Proof.Physical.PublicEntry

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native.Spec
open IxCC.Cfg.Rc.Proof.Physical.Bridge IxCC.Own IxCC.Own.Rc IxCC.Rt.Rc.Procs

/-- Numeric arguments own no heap edges, even in an arena with a nonempty
allocation history and recycled slots. No initializer is invoked here. -/
theorem HeapState.numeric_reentry {P : Program} {pairs : List (Nat × Cfg.Fun)}
    {H : Heap} {addresses : AddressMap} {memory : X86.Memory} {external : Nat → Nat}
    {context base bump limit : Lir.Word} {regionBytes : Nat}
    {slots : List Slot} {lists : Nat → List Lir.Word}
    (heap : HeapState P pairs H addresses memory external []
      context base bump limit regionBytes slots lists) (numbers : List Nat) :
    HeapState P pairs H addresses memory external (Own.litArgs numbers)
      context base bump limit regionBytes slots lists ∧
      Balance H external (Own.litArgs numbers) := by
  have roots : holdRoots external (Own.litArgs numbers) = holdRoots external [] := by
    funext location
    simp [holdRoots, numeric_refs, refsIn]
  refine ⟨⟨?_, heap.ordered, heap.compatible, heap.extent⟩, ?_⟩
  · rw [roots]
    exact heap.ready
  · intro location
    have counted := heap.ready.idle.balance location
    simpa [Balance, holdRoots, refsIn, numeric_refs, cursorTokens, flattenPending] using counted

/-- Start another actual public root from the heap left by release, retaining
bump/free-list history. Its physical simulation is the existing checked
whole-code theorem instantiated at this reached idle boundary. -/
theorem recycled_entry {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code}
    {P : Program} {config : Rt.Config} {pairs : List (Nat × Cfg.Fun)} {functions : List Lir.Func}
    {lowered : Public.Lowered} (admission : CodeAdmission F bodies P config pairs functions)
    (accepted : Public.lower config F bodies P = .ok lowered)
    {H : Heap} {addresses : AddressMap} {memory : X86.Memory} {external : Nat → Nat}
    {context base bump limit : Lir.Word} {regionBytes : Nat}
    {slots : List Slot} {lists : Nat → List Lir.Word}
    (heap : HeapState P pairs H addresses memory external []
      context base bump limit regionBytes slots lists)
    {root : Nat} {source : Fir.Fun} (sourceLookup : F.fun? root = some source)
    {numbers : List Nat} {words : List Lir.Word} (encoded : Rt.natWords numbers = some words)
    (arity : numbers.length = source.params.length) :
    let raw := Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) root
    Sem.Sim (ReturnedOutput P pairs raw H addresses external context base limit regionBytes)
      Nat.succ (fun clock => Fir.run F clock root (Fir.litArgs numbers))
      (fun clock => Lir.eval {lowered.runtime.program with main := root} clock words memory context) := by
  obtain ⟨ready, balance⟩ := heap.numeric_reentry numbers
  exact public_entry_eval_sim admission accepted sourceLookup (Own.dens_lits H numbers) balance
    (numeric_words encoded) (numeric_compatible _ numbers)
    (by simpa only [Own.litArgs, List.length_map] using arity) ready

/-- Execute a public root call from an idle heap state and immediately release
its returned word through `lowered.drop`, either hitting a physical resource
bound during the call or producing both the `Returned` call witness and the
restored idle `HeapState` after `lowered.drop`. -/
theorem recycled_call_and_release {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code}
    {P : Program} {config : Rt.Config} {pairs : List (Nat × Cfg.Fun)} {functions : List Lir.Func}
    {lowered : Public.Lowered} (admission : CodeAdmission F bodies P config pairs functions)
    (accepted : Public.lower config F bodies P = .ok lowered)
    {H : Heap} {addresses : AddressMap} {memory : X86.Memory} {external : Nat → Nat}
    {context base bump limit : Lir.Word} {regionBytes : Nat}
    {slots : List Slot} {lists : Nat → List Lir.Word}
    (heap : HeapState P pairs H addresses memory external []
      context base bump limit regionBytes slots lists)
    {root : Nat} {source : Fir.Fun} (sourceLookup : F.fun? root = some source)
    {numbers : List Nat} {words : List Lir.Word} (encoded : Rt.natWords numbers = some words)
    (arity : numbers.length = source.params.length)
    {sourceClock : Nat} {logical : Fir.Val}
    (success : Fir.run F sourceClock root (Fir.litArgs numbers) = .ok logical) :
    let raw := Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) root
    (∃ (callClock : Nat)
        (returned : Returned P pairs raw H addresses external context base limit regionBytes logical)
        (H' : Heap) (memory' : X86.Memory) (slots' : List Slot)
        (lists' : Nat → List Lir.Word) (dropClock : Nat),
      Lir.eval {lowered.runtime.program with main := root} callClock words memory context =
        .ok ([returned.word], returned.memory) ∧
      dropAll returned.heap [returned.value] = some H' ∧
      HeapState P pairs H' returned.addresses memory' external []
        context base returned.bump limit regionBytes slots' lists' ∧
      ProtectedFrame returned.memory memory' context base returned.bump ∧
      Lir.eval {lowered.runtime.program with main := lowered.drop} dropClock
        [returned.word] returned.memory context = .ok ([1], memory')) ∨
    ∃ callClock resource,
      Lir.eval {lowered.runtime.program with main := root} callClock words memory context =
        .resource resource := by
  dsimp only
  have sim := recycled_entry admission accepted heap sourceLookup encoded arity
  obtain ⟨callClock, refined⟩ := sim.forward sourceClock (by rw [success]; intro h; cases h)
  rw [success] at refined
  cases hcall : Lir.eval {lowered.runtime.program with main := root} callClock words memory context with
  | ok output =>
    rw [hcall] at refined
    cases refined with
    | ok retained =>
      obtain ⟨returned, rfl⟩ := retained
      obtain ⟨H', memory', slots', lists', dropClock, released, ready, frame, dropEval⟩ :=
        returned.release_public admission accepted
      exact .inl ⟨callClock, returned, H', memory', slots', lists', dropClock,
        hcall, released, ready, frame, dropEval⟩
  | resource resource =>
    exact .inr ⟨callClock, resource, hcall⟩
  | timeout | trap | stuck =>
    rw [hcall] at refined
    cases refined

/-- Top-level specialization of `recycled_call_and_release` with empty external
reference counts `fun _ => 0`. -/
theorem recycled_call_and_release_idle {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code}
    {P : Program} {config : Rt.Config} {pairs : List (Nat × Cfg.Fun)} {functions : List Lir.Func}
    {lowered : Public.Lowered} (admission : CodeAdmission F bodies P config pairs functions)
    (accepted : Public.lower config F bodies P = .ok lowered)
    {H : Heap} {addresses : AddressMap} {memory : X86.Memory}
    {context base bump limit : Lir.Word} {regionBytes : Nat}
    {slots : List Slot} {lists : Nat → List Lir.Word}
    (heap : HeapState P pairs H addresses memory (fun _ => 0) []
      context base bump limit regionBytes slots lists)
    {root : Nat} {source : Fir.Fun} (sourceLookup : F.fun? root = some source)
    {numbers : List Nat} {words : List Lir.Word} (encoded : Rt.natWords numbers = some words)
    (arity : numbers.length = source.params.length)
    {sourceClock : Nat} {logical : Fir.Val}
    (success : Fir.run F sourceClock root (Fir.litArgs numbers) = .ok logical) :
    let raw := Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) root
    (∃ (callClock : Nat)
        (returned : Returned P pairs raw H addresses (fun _ => 0) context base limit regionBytes logical)
        (H' : Heap) (memory' : X86.Memory) (slots' : List Slot)
        (lists' : Nat → List Lir.Word) (dropClock : Nat),
      Lir.eval {lowered.runtime.program with main := root} callClock words memory context =
        .ok ([returned.word], returned.memory) ∧
      dropAll returned.heap [returned.value] = some H' ∧
      HeapState P pairs H' returned.addresses memory' (fun _ => 0) []
        context base returned.bump limit regionBytes slots' lists' ∧
      ProtectedFrame returned.memory memory' context base returned.bump ∧
      Lir.eval {lowered.runtime.program with main := lowered.drop} dropClock
        [returned.word] returned.memory context = .ok ([1], memory')) ∨
    ∃ callClock resource,
      Lir.eval {lowered.runtime.program with main := root} callClock words memory context =
        .resource resource :=
  recycled_call_and_release admission accepted heap sourceLookup encoded arity success

/-- A public root call `(root, numbers)` with valid arity, word encoding, and a
successful source `Fir.run` evaluation. -/
def ValidSessionCall (F : Fir.Program) (call : Nat × List Nat) : Prop :=
  ∃ source words clock logical,
    F.fun? call.1 = some source ∧
    Rt.natWords call.2 = some words ∧
    call.2.length = source.params.length ∧
    Fir.run F clock call.1 (Fir.litArgs call.2) = .ok logical

/-- A completed multi-call prefix of public root calls and `lowered.drop`
releases, threading the physical arena state `(H, addresses, memory, bump,
slots, lists)` from an initial idle state to a final idle state. -/
inductive RecycledPrefix (F : Fir.Program) (P : Program) (config : Rt.Config)
    (pairs : List (Nat × Cfg.Fun)) (lowered : Public.Lowered)
    (external : Nat → Nat) (context base limit : Lir.Word) (regionBytes : Nat) :
    List (Nat × List Nat) →
    Heap → AddressMap → X86.Memory → Lir.Word → List Slot → (Nat → List Lir.Word) →
    Heap → AddressMap → X86.Memory → Lir.Word → List Slot → (Nat → List Lir.Word) → Prop where
  | nil {H addresses memory bump slots lists} :
      HeapState P pairs H addresses memory external []
        context base bump limit regionBytes slots lists →
      RecycledPrefix F P config pairs lowered external context base limit regionBytes []
        H addresses memory bump slots lists H addresses memory bump slots lists
  | cons {call : Nat × List Nat} {calls : List (Nat × List Nat)}
      {H addresses memory bump slots lists}
      {H₁ addresses₁ memory₁ bump₁ slots₁ lists₁}
      {H₂ addresses₂ memory₂ bump₂ slots₂ lists₂}
      {source : Fir.Fun} {words : List Lir.Word} {sourceClock callClock dropClock : Nat}
      {logical : Fir.Val}
      {returned : Returned P pairs
        (Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) call.1)
        H addresses external context base limit regionBytes logical} :
      HeapState P pairs H addresses memory external []
        context base bump limit regionBytes slots lists →
      F.fun? call.1 = some source →
      Rt.natWords call.2 = some words →
      call.2.length = source.params.length →
      Fir.run F sourceClock call.1 (Fir.litArgs call.2) = .ok logical →
      Lir.eval {lowered.runtime.program with main := call.1} callClock words memory context =
        .ok ([returned.word], returned.memory) →
      dropAll returned.heap [returned.value] = some H₁ →
      addresses₁ = returned.addresses →
      bump₁ = returned.bump →
      HeapState P pairs H₁ addresses₁ memory₁ external []
        context base bump₁ limit regionBytes slots₁ lists₁ →
      ProtectedFrame returned.memory memory₁ context base bump₁ →
      Lir.eval {lowered.runtime.program with main := lowered.drop} dropClock
        [returned.word] returned.memory context = .ok ([1], memory₁) →
      RecycledPrefix F P config pairs lowered external context base limit regionBytes calls
        H₁ addresses₁ memory₁ bump₁ slots₁ lists₁
        H₂ addresses₂ memory₂ bump₂ slots₂ lists₂ →
      RecycledPrefix F P config pairs lowered external context base limit regionBytes (call :: calls)
        H addresses memory bump slots lists
        H₂ addresses₂ memory₂ bump₂ slots₂ lists₂

theorem RecycledPrefix.final_heapState {F : Fir.Program} {P : Program} {config : Rt.Config}
    {pairs : List (Nat × Cfg.Fun)} {lowered : Public.Lowered}
    {external : Nat → Nat} {context base limit : Lir.Word} {regionBytes : Nat}
    {calls : List (Nat × List Nat)}
    {H addresses memory bump slots lists}
    {H' addresses' memory' bump' slots' lists'}
    (trace : RecycledPrefix F P config pairs lowered external context base limit regionBytes calls
      H addresses memory bump slots lists H' addresses' memory' bump' slots' lists') :
    HeapState P pairs H' addresses' memory' external []
      context base bump' limit regionBytes slots' lists' := by
  induction trace with
  | nil heap => exact heap
  | cons _ _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ih

theorem RecycledPrefix.append {F : Fir.Program} {P : Program} {config : Rt.Config}
    {pairs : List (Nat × Cfg.Fun)} {lowered : Public.Lowered}
    {external : Nat → Nat} {context base limit : Lir.Word} {regionBytes : Nat}
    {calls₁ calls₂ : List (Nat × List Nat)}
    {H₀ addresses₀ memory₀ bump₀ slots₀ lists₀}
    {H₁ addresses₁ memory₁ bump₁ slots₁ lists₁}
    {H₂ addresses₂ memory₂ bump₂ slots₂ lists₂}
    (first : RecycledPrefix F P config pairs lowered external context base limit regionBytes calls₁
      H₀ addresses₀ memory₀ bump₀ slots₀ lists₀
      H₁ addresses₁ memory₁ bump₁ slots₁ lists₁)
    (second : RecycledPrefix F P config pairs lowered external context base limit regionBytes calls₂
      H₁ addresses₁ memory₁ bump₁ slots₁ lists₁
      H₂ addresses₂ memory₂ bump₂ slots₂ lists₂) :
    RecycledPrefix F P config pairs lowered external context base limit regionBytes (calls₁ ++ calls₂)
      H₀ addresses₀ memory₀ bump₀ slots₀ lists₀
      H₂ addresses₂ memory₂ bump₂ slots₂ lists₂ := by
  induction first with
  | nil _ => exact second
  | cons heap lookup encoded arity run callEval released haddr hbump ready frame dropEval _ ih =>
    exact .cons heap lookup encoded arity run callEval released haddr hbump ready frame dropEval
      (ih second)

/-- After any completed prefix of call+release cycles, the reached state still
satisfies the full idle `HeapState` invariant, so the next public root call
simulates `Fir.run` via `recycled_entry`. -/
theorem RecycledPrefix.next_entry {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code}
    {P : Program} {config : Rt.Config} {pairs : List (Nat × Cfg.Fun)} {functions : List Lir.Func}
    {lowered : Public.Lowered} (admission : CodeAdmission F bodies P config pairs functions)
    (accepted : Public.lower config F bodies P = .ok lowered)
    {external : Nat → Nat} {context base limit : Lir.Word} {regionBytes : Nat}
    {calls : List (Nat × List Nat)}
    {H addresses memory bump slots lists}
    {H' addresses' memory' bump' slots' lists'}
    (trace : RecycledPrefix F P config pairs lowered external context base limit regionBytes calls
      H addresses memory bump slots lists H' addresses' memory' bump' slots' lists')
    {root : Nat} {source : Fir.Fun} (sourceLookup : F.fun? root = some source)
    {numbers : List Nat} {words : List Lir.Word} (encoded : Rt.natWords numbers = some words)
    (arity : numbers.length = source.params.length) :
    let raw := Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) root
    Sem.Sim (ReturnedOutput P pairs raw H' addresses' external context base limit regionBytes)
      Nat.succ (fun clock => Fir.run F clock root (Fir.litArgs numbers))
      (fun clock => Lir.eval {lowered.runtime.program with main := root} clock words memory' context) :=
  recycled_entry admission accepted trace.final_heapState sourceLookup encoded arity

/-- Outcome of executing an arbitrary session `calls : List (Nat × List Nat)` of
public root calls and `lowered.drop` releases from an idle heap state: either
every call+release in `calls` completes and restores the idle `HeapState`
invariant, or some call in the session hits a physical `.resource` bound after a
completed prefix. -/
inductive RecycledSession (F : Fir.Program) (P : Program) (config : Rt.Config)
    (pairs : List (Nat × Cfg.Fun)) (lowered : Public.Lowered)
    (external : Nat → Nat) (context base limit : Lir.Word) (regionBytes : Nat) :
    List (Nat × List Nat) →
    Heap → AddressMap → X86.Memory → Lir.Word → List Slot → (Nat → List Lir.Word) → Prop where
  | done {H addresses memory bump slots lists} :
      HeapState P pairs H addresses memory external []
        context base bump limit regionBytes slots lists →
      RecycledSession F P config pairs lowered external context base limit regionBytes []
        H addresses memory bump slots lists
  | resource {call : Nat × List Nat} {calls : List (Nat × List Nat)}
      {H addresses memory bump slots lists}
      {source : Fir.Fun} {words : List Lir.Word} {callClock : Nat} {res : Sem.Resource} :
      HeapState P pairs H addresses memory external []
        context base bump limit regionBytes slots lists →
      F.fun? call.1 = some source →
      Rt.natWords call.2 = some words →
      call.2.length = source.params.length →
      Lir.eval {lowered.runtime.program with main := call.1} callClock words memory context =
        .resource res →
      RecycledSession F P config pairs lowered external context base limit regionBytes (call :: calls)
        H addresses memory bump slots lists
  | step {call : Nat × List Nat} {calls : List (Nat × List Nat)}
      {H addresses memory bump slots lists}
      {H' memory' slots' lists'}
      {source : Fir.Fun} {words : List Lir.Word} {sourceClock callClock dropClock : Nat}
      {logical : Fir.Val}
      {returned : Returned P pairs
        (Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) call.1)
        H addresses external context base limit regionBytes logical} :
      HeapState P pairs H addresses memory external []
        context base bump limit regionBytes slots lists →
      F.fun? call.1 = some source →
      Rt.natWords call.2 = some words →
      call.2.length = source.params.length →
      Fir.run F sourceClock call.1 (Fir.litArgs call.2) = .ok logical →
      Lir.eval {lowered.runtime.program with main := call.1} callClock words memory context =
        .ok ([returned.word], returned.memory) →
      dropAll returned.heap [returned.value] = some H' →
      HeapState P pairs H' returned.addresses memory' external []
        context base returned.bump limit regionBytes slots' lists' →
      ProtectedFrame returned.memory memory' context base returned.bump →
      Lir.eval {lowered.runtime.program with main := lowered.drop} dropClock
        [returned.word] returned.memory context = .ok ([1], memory') →
      RecycledSession F P config pairs lowered external context base limit regionBytes calls
        H' returned.addresses memory' returned.bump slots' lists' →
      RecycledSession F P config pairs lowered external context base limit regionBytes (call :: calls)
        H addresses memory bump slots lists

/-- Multi-call session theorem composing `public_entry_eval_sim`,
`Returned.release_public`, and `recycled_entry` across an arbitrary list of
valid public root calls `calls : List (Nat × List Nat)`. -/
theorem recycled_session {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code}
    {P : Program} {config : Rt.Config} {pairs : List (Nat × Cfg.Fun)} {functions : List Lir.Func}
    {lowered : Public.Lowered} (admission : CodeAdmission F bodies P config pairs functions)
    (accepted : Public.lower config F bodies P = .ok lowered)
    {external : Nat → Nat} {context base limit : Lir.Word} {regionBytes : Nat}
    (calls : List (Nat × List Nat))
    (valid : ∀ call ∈ calls, ValidSessionCall F call)
    {H : Heap} {addresses : AddressMap} {memory : X86.Memory} {bump : Lir.Word}
    {slots : List Slot} {lists : Nat → List Lir.Word}
    (heap : HeapState P pairs H addresses memory external []
      context base bump limit regionBytes slots lists) :
    RecycledSession F P config pairs lowered external context base limit regionBytes calls
      H addresses memory bump slots lists := by
  induction calls generalizing H addresses memory bump slots lists with
  | nil => exact .done heap
  | cons call rest ih =>
    have hcall : ValidSessionCall F call := valid call List.mem_cons_self
    obtain ⟨source, words, sourceClock, logical, lookup, encoded, arity, run⟩ := hcall
    have hrest : ∀ c ∈ rest, ValidSessionCall F c :=
      fun c hc => valid c (List.mem_cons_of_mem call hc)
    rcases recycled_call_and_release admission accepted heap lookup encoded arity run with
      ⟨callClock, returned, H', memory', slots', lists', dropClock,
        callEval, released, ready, frame, dropEval⟩ |
      ⟨callClock, res, resEval⟩
    · exact .step heap lookup encoded arity run callEval released ready frame dropEval
        (ih hrest ready)
    · exact .resource heap lookup encoded arity resEval

/-- Top-level specialization of `recycled_session` starting from an idle
`HeapState` with `external = fun _ => 0`. -/
theorem recycled_session_idle {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code}
    {P : Program} {config : Rt.Config} {pairs : List (Nat × Cfg.Fun)} {functions : List Lir.Func}
    {lowered : Public.Lowered} (admission : CodeAdmission F bodies P config pairs functions)
    (accepted : Public.lower config F bodies P = .ok lowered)
    {context base limit : Lir.Word} {regionBytes : Nat}
    (calls : List (Nat × List Nat))
    (valid : ∀ call ∈ calls, ValidSessionCall F call)
    {H : Heap} {addresses : AddressMap} {memory : X86.Memory} {bump : Lir.Word}
    {slots : List Slot} {lists : Nat → List Lir.Word}
    (heap : HeapState P pairs H addresses memory (fun _ => 0) []
      context base bump limit regionBytes slots lists) :
    RecycledSession F P config pairs lowered (fun _ => 0) context base limit regionBytes calls
      H addresses memory bump slots lists :=
  recycled_session admission accepted calls valid heap

end IxCC.Cfg.Rc.Native.Spec
