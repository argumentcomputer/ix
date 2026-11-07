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

end Session
end IxCC.X86.DriverSession
