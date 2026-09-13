module
import Tests.Ixby.Common
import Ix.Ixby.Flock.Trace
import Ix.Ixby.Commitment

/-! Independent reference fixtures for the revision-1 native Nat executor.
The trace theorems cover the logical control boundary, not native matrices. -/

namespace Tests.Ixby.Flock.Nats

open Ix.Ixby
open Ix.Ixby.FlockBackend.ControlModel

private def profile : Profile := {
  revision := .cryptoNatV1
  limits := {
    functions := 2, constructors := 2, blocks := 3, locals := 4
    operands := 2, continuations := 2, inputNodes := 7
    natBits := 192, stringBytes := 0, byteArrayBytes := 33 }
  programBytes := 256, valueBytes := 192, valueDepth := 3, maxSteps := 8 }

private def n (value : Nat) : Value := .scalar (.nat value)
private def a : Nat := 2 ^ 160 + 2 ^ 64 + 137
private def b : Nat := 2 ^ 79 + 3
private def small : Nat := 2 ^ 95 + 7
private def primitive (op : Primitive) : Program := { functions := #[{
  arity := 2, blocks := #[
    ⟨2, .letOp (.primitive op [.local 0, .local 1]) 1⟩,
    ⟨3, .ret (.local 2)⟩] }] }
private def caseNat : Program := { functions := #[{
  arity := 1, blocks := #[
    ⟨1, .caseNat (.local 0) 1 2⟩,
    ⟨1, .ret (.local 0)⟩,
    ⟨2, .ret (.local 1)⟩] }] }
private def walk : Program := { functions := #[{
  arity := 1, blocks := #[
    ⟨1, .caseNat (.local 0) 1 2⟩,
    ⟨1, .ret (.local 0)⟩,
    ⟨2, .tailCallSelf [.local 1]⟩] }] }
private def id : CtorId := {
  block := 0xb7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7, member := 0xffffffff, tag := 0x80000000 }
private def object : Value := .ctor id #[n a, .scalar (.bytes #[1, 2, 3])]
private def ctorCase : Program := {
  constructors := #[⟨id, 2⟩]
  functions := #[{ arity := 1, blocks := #[
    ⟨1, .caseCtor (.local 0) [⟨0, 1⟩]⟩,
    ⟨3, .letOp (.primitive .natAdd [.local 1, .literal (.nat 1)]) 2⟩,
    ⟨4, .ret (.local 3)⟩] }] }

private def artifacts (code : Program) (args : Array Value) (expected : Value) :
    Except Codec.Error (Codec.Bytes × Codec.Bytes × Codec.Bytes) := do
  return (← Codec.encodeProgram profile code, ← Codec.encodeInput profile code args,
    ← Codec.encodeOutput profile code expected)
private def agrees (code : Program) (args : Array Value) (expected : Value) : Bool :=
  match artifacts code args expected with
  | .error _ => false
  | .ok (code, input, output) => match Codec.execute profile code input profile.maxSteps with
    | .error _ => false
    | .ok execution => execution.output == expected && execution.outputBytes == output
private def digestWords (digest : Commitment.Digest) : List Nat :=
  (List.range 4).map fun word =>
    (List.range 8).foldl (fun n byte =>
      n + digest.bytes[word * 8 + byte]!.toNat * 2 ^ (8 * byte)) 0
private def golden (code : Program) (args : Array Value) (expected : Value)
    (words : List Nat) : Bool :=
  match artifacts code args expected with
  | .error _ => false
  | .ok (code, input, output) => match Commitment.ofArtifacts profile code input output with
    | .error _ => false
    | .ok statement => digestWords statement.digest == words

namespace CaseTrace

private def first (value : Nat) : Frame := ⟨0, 0, #[n value]⟩
private def successor : Frame := append (first 1) 2 (n 0)
private def zero : Frame := { first 0 with block := 1 }

private theorem successor_step : Step profile.limits caseNat ⟨.eval (first 1), #[]⟩
    (.next ⟨.eval successor, #[]⟩) :=
  .caseNatSucc (operand := .local 0) (ifZero := 1) (ifSucc := 2)
    (pred := 0) (declared := 1) (next := ⟨2, .ret (.local 1)⟩) rfl rfl rfl

private theorem zero_step : Step profile.limits caseNat ⟨.eval (first 0), #[]⟩
    (.next ⟨.eval zero, #[]⟩) :=
  .caseNatZero (operand := .local 0) (ifZero := 1) (ifSucc := 2)
    (declared := 1) (next := ⟨1, .ret (.local 0)⟩) rfl rfl rfl

private theorem successor_trace : Trace profile.limits caseNat 3
    (.active 3 ⟨.eval (first 1), #[]⟩) (.halted 0 (n 0)) :=
  .cons (.next successor_step) (.cons (.next
    (.ret (operand := .local 1) (declared := 2) rfl rfl))
      (.cons (.halt (.halt (n 0))) (.nil _)))
private theorem zero_trace : Trace profile.limits caseNat 3
    (.active 3 ⟨.eval (first 0), #[]⟩) (.halted 0 (n 0)) :=
  .cons (.next zero_step) (.cons (.next
    (.ret (operand := .local 0) (declared := 1) rfl rfl))
      (.cons (.halt (.halt (n 0))) (.nil _)))

example : Ix.Ixby.execute profile.limits caseNat #[n 1] 3 = .ok (n 0) :=
  successor_trace.reference_execution (by
    simp only [Machine.decode, ActiveControl.decode, Array.map_empty]
    rfl)
example : Ix.Ixby.execute profile.limits caseNat #[n 0] 3 = .ok (n 0) :=
  zero_trace.reference_execution (by
    simp only [Machine.decode, ActiveControl.decode, Array.map_empty]
    rfl)
example : Ix.Ixby.execute profile.limits caseNat #[n 1] 2 = .error .outOfFuel := rfl

end CaseTrace

private def checks : IO (List Check) := pure [
  ("192-bit native fixture addition", agrees (primitive .natAdd) #[n a, n b] (n (a + b))),
  ("192-bit native fixture subtraction", agrees (primitive .natSub) #[n a, n b] (n (a - b))),
  ("192-bit native fixture multiplication", agrees (primitive .natMul) #[n small, n b] (n (small * b))),
  ("192-bit native fixture quotient", agrees (primitive .natDiv) #[n a, n b] (n (a / b))),
  ("192-bit native fixture remainder", agrees (primitive .natMod) #[n a, n b] (n (a % b))),
  ("192-bit equality is Bool", agrees (primitive .natEq) #[n a, n a] (.scalar (.bool true))),
  ("192-bit comparison is Bool", agrees (primitive .natLt) #[n b, n a] (.scalar (.bool true))),
  ("subtraction saturates at zero", agrees (primitive .natSub) #[n b, n a] (n 0)),
  ("division by zero returns zero", agrees (primitive .natDiv) #[n a, n 0] (n 0)),
  ("modulo zero preserves dividend", agrees (primitive .natMod) #[n a, n 0] (n a)),
  ("zero case keeps frame", agrees caseNat #[n 0] (n 0)),
  ("successor case appends exact predecessor", agrees caseNat #[n a] (n (a - 1))),
  ("constructor case carries Nat and byte fields", agrees ctorCase #[object] (n (a + 1))),
  ("tail recursion consumes exact Nat predecessors", agrees walk #[n 2] (n 0)),
  ("native addition whole-statement golden", golden (primitive .natAdd) #[n a, n b] (n (a + b))
    [10543937101595496891, 13067204517167037398, 14111677314597180777, 11101863275982993741]),
  ("native constructor/Nat whole-statement golden", golden ctorCase #[object] (n (a + 1))
    [6431930672498536397, 8633735064928880919, 14192929670046353702, 520228631706350942]),
  ("native Nat recursion whole-statement golden", golden walk #[n 2] (n 0)
    [12256219420089308533, 2944215410467354441, 4031868974126339541, 9999387711666983146])
]

public def suite : IO UInt32 := runChecks "ixby-flock-nats" checks

end Tests.Ixby.Flock.Nats
