import IxCC.X86.DriverSession
import IxCC.X86.Memory

set_option autoImplicit false
namespace IxCC.X86.DriverSession
open Sem (Result ClockMono)
namespace Session

theorem dropCall_mono (s : Session) (word : Word) (bytes : Word → UInt8) :
    ClockMono (s.dropCall word bytes) := ObjectEval.call_mono _ _ _ _ _

theorem one_mono (s : Session) (input : Input) (bytes : Word → UInt8) :
    ClockMono (s.one input bytes) := by
  unfold one
  split
  · exact ClockMono.const _
  · split
    · split
      · apply ClockMono.bind (ObjectEval.call_mono _ _ _ _ _)
        intro live
        split
        · exact ClockMono.const _
        · exact ClockMono.bind (s.dropCall_mono _ _) fun _ => ClockMono.const _
      · exact ClockMono.const _
    · exact ClockMono.const _

theorem runCalls_mono (s : Session) (inputs : List Input) (bytes : Word → UInt8) :
    ClockMono (s.runCalls inputs bytes) := by
  induction inputs generalizing bytes with
  | nil => exact ClockMono.const _
  | cons input rest ih =>
    exact ClockMono.bind (s.one_mono input bytes) fun event =>
      ClockMono.bind (ih event.released.bytes) fun _ => ClockMono.const _

theorem run_mono (s : Session) (inputs : List Input) : ClockMono (s.run inputs) :=
  ClockMono.bind (ObjectEval.call_mono _ _ _ _ _) fun initialized =>
    s.runCalls_mono inputs initialized.2.bytes

/-- No Nat decoding/tagging of the owned result word occurs at the boundary. -/
theorem rawWord_argument (d : Driver) (word : Word) :
    d.regs [word] .rsi = word := rfl

theorem dropCall_exact (s : Session) (word : Word) (bytes : Word → UInt8) (k : Nat) :
    s.dropCall word bytes k = ObjectEval.call s.linked.object s.drop s.linked.driver.base
      (s.linked.driver.core [word] bytes) s.linked.driver.flags k := rfl

/-- The only inter-call memory preparation is the standard return-slot write.
The existing Driver.Ok stack/region separation must justify this premise at
each region address when composing with the physical ownership theorem. -/
theorem setup_bytes_outside_return (d : Driver) (bytes : Word → UInt8) (a : Word)
    (outside : ∀ offset < 8, a ≠ d.sp + UInt64.ofNat offset) :
    (d.mem bytes).bytes a = bytes a := by
  exact Memory.writeLittle_bytes_outside _ _ _ _ 8 outside

theorem continuation_bytes (s : Session) (input : Input) (rest : List Input)
    (bytes : Word → UInt8) (k : Nat) :
    s.runCalls (input :: rest) bytes k =
      (s.one input bytes k).bind (fun event =>
        (s.runCalls rest event.released.bytes k).map fun output =>
          { output with events := event :: output.events }) := rfl

theorem validTrace_nil (ownedToken : Word → Memory → Prop) :
    ValidTrace ownedToken [] := by
  intro _ h
  cases h

theorem validTrace_cons (ownedToken : Word → Memory → Prop)
    (event : Event) (events : List Event) :
    ValidTrace ownedToken (event :: events) ↔
      ReleasePermitted ownedToken event.word event.live ∧ ValidTrace ownedToken events := by
  constructor
  · intro h
    exact ⟨h event (by simp), fun e he => h e (List.mem_cons_of_mem _ he)⟩
  · rintro ⟨hhead, htail⟩ e he
    rcases List.mem_cons.mp he with rfl | hmem
    · exact hhead
    · exact htail e hmem

theorem validTrace_append (ownedToken : Word → Memory → Prop)
    (xs ys : List Event) :
    ValidTrace ownedToken (xs ++ ys) ↔
      ValidTrace ownedToken xs ∧ ValidTrace ownedToken ys := by
  constructor
  · intro h
    exact ⟨fun e he => h e (List.mem_append_left ys he),
      fun e he => h e (List.mem_append_right xs he)⟩
  · rintro ⟨hx, hy⟩ e he
    rcases List.mem_append.mp he with hx' | hy'
    · exact hx e hx'
    · exact hy e hy'

theorem one_ok_parts {s : Session} {input : Input} {bytes : Word → UInt8}
    {k : Nat} {event : Event} (accepted : s.one input bytes k = .ok event) :
    ∃ root,
      s.linked.roots[input.root]? = some root ∧
      root.params ≤ 5 ∧
      input.args.length = root.params ∧
      input.args.all (· < 2^64) = true ∧
      s.linked.rootCall root input.args bytes k = .ok (event.word, event.live) ∧
      s.linked.observe root event.word event.live = some event.observation ∧
      s.dropCall event.word event.live.bytes k = .ok (1, event.released) ∧
      event.input = input := by
  unfold one at accepted
  cases hroot : s.linked.roots[input.root]? with
  | none => simp [hroot] at accepted
  | some root =>
    simp only [hroot] at accepted
    split at accepted
    · next harity =>
      split at accepted
      · next hbounds =>
        cases hcall : s.linked.rootCall root input.args bytes k with
        | ok live =>
          rcases live with ⟨w, liveMem⟩
          simp only [hcall, Result.bind] at accepted
          cases hobs : s.linked.observe root w liveMem with
          | none => simp [hobs] at accepted
          | some obs =>
            simp only [hobs] at accepted
            cases hdrop : s.dropCall w liveMem.bytes k with
            | ok released =>
              rcases released with ⟨rw, relMem⟩
              simp only [hdrop] at accepted
              split at accepted
              · next hrw =>
                subst hrw
                simp only [Result.ok.injEq] at accepted
                subst accepted
                exact ⟨root, rfl, harity.1, harity.2, hbounds, hcall, hobs, hdrop, rfl⟩
              · simp at accepted
            | timeout | trap | resource _ | stuck => simp [hdrop] at accepted
        | timeout | trap | resource _ | stuck => simp [hcall, Result.bind] at accepted
      · simp at accepted
    · simp at accepted

theorem runCalls_ok_cons {s : Session} {input : Input} {rest : List Input}
    {bytes : Word → UInt8} {k : Nat} {output : Output}
    (accepted : s.runCalls (input :: rest) bytes k = .ok output) :
    ∃ event tail,
      s.one input bytes k = .ok event ∧
      s.runCalls rest event.released.bytes k = .ok tail ∧
      output = { tail with events := event :: tail.events } := by
  rw [continuation_bytes] at accepted
  cases hone : s.one input bytes k with
  | ok event =>
    simp only [hone, Result.bind] at accepted
    cases hrest : s.runCalls rest event.released.bytes k with
    | ok tail =>
      simp only [hrest, Result.map, Result.bind, Result.ok.injEq] at accepted
      exact ⟨event, tail, rfl, hrest, accepted.symm⟩
    | timeout | trap | resource _ | stuck => simp [hrest, Result.map, Result.bind] at accepted
  | timeout | trap | resource _ | stuck => simp [hone, Result.bind] at accepted

theorem runCalls_ok_inputs {s : Session} {inputs : List Input}
    {bytes : Word → UInt8} {k : Nat} {output : Output}
    (accepted : s.runCalls inputs bytes k = .ok output) :
    output.events.map Event.input = inputs ∧ output.events.length = inputs.length := by
  induction inputs generalizing bytes output with
  | nil =>
    simp only [runCalls, Result.ok.injEq] at accepted
    subst accepted
    simp
  | cons input rest ih =>
    obtain ⟨event, tail, hone, hrest, rfl⟩ := runCalls_ok_cons accepted
    obtain ⟨_, _, _, _, _, _, _, _, hinput⟩ := one_ok_parts hone
    obtain ⟨hmap, hlen⟩ := ih hrest
    simp [hinput, hmap, hlen]

/-- Invariant-threading composition across `Session.runCalls`: if an idle-memory
invariant `Inv` holds initially and every successful `s.one` call from an `Inv`
state establishes `ReleasePermitted` on the live result and restores `Inv` on the
released bytes, then any successful `runCalls` trace satisfies `ValidTrace` and
leaves the final bytes in `Inv`. -/
theorem runCalls_validTrace {s : Session} {ownedToken : Word → Memory → Prop}
    {Inv : (Word → UInt8) → Prop} {inputs : List Input} {bytes : Word → UInt8}
    {k : Nat} {output : Output}
    (initial : Inv bytes)
    (step : ∀ input ∈ inputs, ∀ b event,
      Inv b → s.one input b k = .ok event →
      ReleasePermitted ownedToken event.word event.live ∧ Inv event.released.bytes)
    (accepted : s.runCalls inputs bytes k = .ok output) :
    ValidTrace ownedToken output.events ∧ Inv output.bytes := by
  induction inputs generalizing bytes output with
  | nil =>
    simp only [runCalls, Result.ok.injEq] at accepted
    subst accepted
    exact ⟨validTrace_nil ownedToken, initial⟩
  | cons input rest ih =>
    obtain ⟨event, tail, hone, hrest, rfl⟩ := runCalls_ok_cons accepted
    obtain ⟨hperm, hnext⟩ := step input (by simp) bytes event initial hone
    obtain ⟨htrace, hfinal⟩ := ih hnext
      (fun i hi b ev hb hev => step i (List.mem_cons_of_mem _ hi) b ev hb hev) hrest
    exact ⟨(validTrace_cons ownedToken event tail.events).mpr ⟨hperm, htrace⟩, hfinal⟩

theorem runCalls_validTrace_of_one {s : Session} {ownedToken : Word → Memory → Prop}
    {inputs : List Input} {bytes : Word → UInt8} {k : Nat} {output : Output}
    (permitted : ∀ input ∈ inputs, ∀ b event,
      s.one input b k = .ok event → ReleasePermitted ownedToken event.word event.live)
    (accepted : s.runCalls inputs bytes k = .ok output) :
    ValidTrace ownedToken output.events :=
  (runCalls_validTrace (Inv := fun _ => True) trivial
    (fun input hi b event _ hone => ⟨permitted input hi b event hone, trivial⟩) accepted).1

theorem run_validTrace {s : Session} {ownedToken : Word → Memory → Prop}
    {Inv : (Word → UInt8) → Prop} {inputs : List Input} {k : Nat} {output : Output}
    (initInv : ∀ initialized, s.linked.initCall k = .ok initialized → Inv initialized.2.bytes)
    (step : ∀ input ∈ inputs, ∀ b event,
      Inv b → s.one input b k = .ok event →
      ReleasePermitted ownedToken event.word event.live ∧ Inv event.released.bytes)
    (accepted : s.run inputs k = .ok output) :
    ValidTrace ownedToken output.events ∧ Inv output.bytes := by
  unfold run at accepted
  cases hinit : s.linked.initCall k with
  | ok initialized =>
    simp only [hinit, Result.bind] at accepted
    exact runCalls_validTrace (initInv initialized hinit) step accepted
  | timeout | trap | resource _ | stuck => simp [hinit, Result.bind] at accepted

end Session
end IxCC.X86.DriverSession
