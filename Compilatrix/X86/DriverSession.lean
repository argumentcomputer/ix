import Compilatrix.X86.Linked

/-! Scratch driver session semantics. This is the actual object-call evaluator,
not a source/native simulation. One init precedes a finite sequence. Each
successful root result is completely observed before its unchanged word is
released, and the next root receives the release call's memory bytes. -/
set_option autoImplicit false
namespace Compilatrix.X86.DriverSession
open Sem (Result Obs ClockMono)

structure Input where
  root : Nat
  args : List Nat

structure Session where
  linked : Linked
  drop : String := "cx_drop"

/-- Historical evidence only: the driver never reuses an event's released
word as an argument to another machine call. -/
structure Event where
  input : Input
  word : Word
  observation : Obs
  live : Memory
  released : Memory

structure Output where
  events : List Event
  bytes : Word → UInt8

/-- The caller must establish this at every release boundary, with the actual
runtime ownership interpretation. It is not checked by the raw-word ABI and
is not derived from readback or from a zero reference-count header. -/
def ReleasePermitted (ownedToken : Word → Memory → Prop) (word : Word)
    (live : Memory) : Prop := ownedToken word live

/-- This records a validity obligation for a successful trace; it is not a
claim of safe execution for arbitrary words, failing prefixes or foreign code. -/
def ValidTrace (ownedToken : Word → Memory → Prop) (events : List Event) : Prop :=
  ∀ event ∈ events, ReleasePermitted ownedToken event.word event.live

namespace Session

def dropCall (s : Session) (word : Word) (bytes : Word → UInt8) (k : Nat) :
    Result (Word × Memory) :=
  ObjectEval.call s.linked.object s.drop s.linked.driver.base
    (s.linked.driver.core [word] bytes) s.linked.driver.flags k

/-- This finite session accepts exact-arity calls supported by the five-word
external ABI. Invalid root/arity/readback/protocol values are stuck. Nat values
outside UInt64 fail before conversion; wrappers retain their own overflow
checks. All non-success machine outcomes propagate unchanged. -/
def one (s : Session) (input : Input) (bytes : Word → UInt8) (k : Nat) : Result Event :=
  match s.linked.roots[input.root]? with
  | none => .stuck
  | some root =>
    if root.params ≤ 5 ∧ input.args.length = root.params then
      if input.args.all (· < 2^64) then
        (s.linked.rootCall root input.args bytes k).bind fun live =>
          match s.linked.observe root live.1 live.2 with
          | none => .stuck
          | some observation =>
            (s.dropCall live.1 live.2.bytes k).bind fun released =>
              if released.1 = 1 then
                .ok ⟨input, live.1, observation, live.2, released.2⟩
              else .stuck
      else .resource .natOverflow
    else .stuck

def runCalls (s : Session) : List Input → (Word → UInt8) → Nat → Result Output
  | [], bytes, _ => .ok ⟨[], bytes⟩
  | input :: rest, bytes, k =>
    (s.one input bytes k).bind fun event =>
      (s.runCalls rest event.released.bytes k).map fun output =>
        { output with events := event :: output.events }

/-- Only this outer function initializes. Continuation and release never
reinitialize memory or insert allocator/object metadata writes. The standard
Driver.core still writes the call's return slot, as the real trampoline does. -/
def run (s : Session) (inputs : List Input) (k : Nat) : Result Output :=
  (s.linked.initCall k).bind fun initialized => s.runCalls inputs initialized.2.bytes k

end Session
end Compilatrix.X86.DriverSession
