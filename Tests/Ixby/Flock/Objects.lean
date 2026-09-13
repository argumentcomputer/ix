module
import Tests.Ixby.Common
import Ix.Ixby.Flock.Trace
import Ix.Ixby.Commitment

/-! Independent pure reference fixtures for native immutable constructor Exec.
The shared statement goldens bind the whole profile/program/input/output chain.
The checked trace is a reference theorem, not native matrix refinement. -/

namespace Tests.Ixby.Flock.Objects

open Ix.Ixby
open Ix.Ixby.FlockBackend.ControlModel

private def profile : Profile := {
  limits := {
    functions := 2, constructors := 2, blocks := 3, locals := 4,
    operands := 2, continuations := 2, inputNodes := 7,
    natBits := 0, stringBytes := 0, byteArrayBytes := 33 }
  programBytes := 256, valueBytes := 192, valueDepth := 3, maxSteps := 8 }

private def emptyId : CtorId := {
  block := 0x1111111111111111111111111111111111111111111111111111111111111111, member := 0xffffffff, tag := 0x80000000 }
private def pairId : CtorId := {
  block := 0x9191919191919191919191919191919191919191919191919191919191919191, member := 0xffffffff, tag := 0x80000000 }
private def declarations : Array CtorDecl := #[⟨emptyId, 0⟩, ⟨pairId, 2⟩]
private def w (value : UInt32) : Value := .scalar (.word32 value)
private def b (data : Array UInt8) : Value := .scalar (.bytes data)
private def ext : Value := .scalar (.extField ⟨Goldilocks.reduce 17, Goldilocks.reduce 19⟩)
private def empty : Value := .ctor emptyId #[]
private def pair (a b : Value) : Value := .ctor pairId #[a, b]
private def bytes : Value := b ((List.range 33).toArray.map fun i => (i * 73 + 19).toUInt8)
private def program (arity : Nat) (blocks : Array Block) : Program := {
  constructors := declarations, functions := #[{ arity, blocks }] }
private def identity : Program := program 1 #[⟨1, .ret (.local 0)⟩]
private def construct : Program := program 2 #[
  ⟨2, .letOp (.construct 1 [.local 0, .local 1]) 1⟩,
  ⟨3, .ret (.local 2)⟩]
private def constructCase : Program := program 0 #[
  ⟨0, .letOp (.construct 1 [.literal (.word32 11), .literal (.word32 22)]) 1⟩,
  ⟨1, .caseCtor (.local 0) [⟨1, 2⟩]⟩,
  ⟨3, .ret (.local 2)⟩]
private def walk : Program := program 1 #[
  ⟨1, .caseCtor (.local 0) [⟨0, 1⟩, ⟨1, 2⟩]⟩,
  ⟨1, .ret (.literal (.word32 42))⟩,
  ⟨3, .tailCallSelf [.local 2]⟩]

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

namespace ConstructCaseTrace

private def first : Frame := ⟨0, 0, #[]⟩
private def second : Frame := append first 1 (pair (w 11) (w 22))
private def third : Frame := ⟨0, 2, #[pair (w 11) (w 22), w 11, w 22]⟩

private theorem construct_step : Step profile.limits constructCase ⟨.eval first, #[]⟩
    (.next ⟨.eval second, #[]⟩) :=
  .bind (op := .construct 1 [.literal (.word32 11), .literal (.word32 22)])
    (declared := 0) (next := ⟨1, .caseCtor (.local 0) [⟨1, 2⟩]⟩) rfl
    (.construct (declaration := ⟨pairId, 2⟩) (fields := [w 11, w 22]) rfl rfl rfl) rfl

private theorem case_step : Step profile.limits constructCase ⟨.eval second, #[]⟩
    (.next ⟨.eval third, #[]⟩) :=
  .caseCtor (operand := .local 0) (alternatives := [⟨1, 2⟩])
    (id := pairId) (fields := #[w 11, w 22]) (declared := 1)
    (next := ⟨3, .ret (.local 2)⟩) rfl rfl rfl rfl

private theorem return_step : Step profile.limits constructCase ⟨.eval third, #[]⟩
    (.next ⟨.ret (w 22), #[]⟩) :=
  .ret (operand := .local 2) (declared := 3) rfl rfl

private theorem four_steps : Trace profile.limits constructCase 4
    (.active 4 ⟨.eval first, #[]⟩) (.halted 0 (w 22)) :=
  .cons (.next construct_step) (.cons (.next case_step)
    (.cons (.next return_step) (.cons (.halt (.halt (w 22))) (.nil _))))

example : Ix.Ixby.execute profile.limits constructCase #[] 4 = .ok (w 22) :=
  four_steps.reference_execution (by
    simp only [Machine.decode, ActiveControl.decode, Array.map_empty]
    rfl)

example : Ix.Ixby.execute profile.limits constructCase #[] 3 = .error .outOfFuel := rfl

end ConstructCaseTrace

private def checks : IO (List Check) := pure [
  ("nullary construction", agrees (program 0 #[
    ⟨0, .letOp (.construct 0 []) 1⟩, ⟨1, .ret (.local 0)⟩]) #[] empty),
  ("ordered byte/word constructor fields", agrees construct #[bytes, w 17] (pair bytes (w 17))),
  ("nested constructors retain finite-tree encoding", let value := pair (pair (w 11) (w 22)) .erased
    agrees identity #[value] value),
  ("shared immutable value is serialized twice", let value := pair (w 11) (w 22)
    agrees (program 1 #[⟨1, .letOp (.construct 1 [.local 0, .local 0]) 1⟩,
      ⟨2, .ret (.local 1)⟩]) #[value] (pair value value)),
  ("projection returns first byte field", agrees (program 1 #[
    ⟨1, .letOp (.project (.local 0) 0) 1⟩, ⟨2, .ret (.local 1)⟩])
    #[pair bytes ext] bytes),
  ("projection returns second extension field", agrees (program 1 #[
    ⟨1, .letOp (.project (.local 0) 1) 1⟩, ⟨2, .ret (.local 1)⟩])
    #[pair bytes ext] ext),
  ("Erased projection ignores even maximum u32 field index", agrees (program 1 #[
    ⟨1, .letOp (.project (.local 0) 0xffffffff) 1⟩, ⟨2, .ret (.local 1)⟩]) #[.erased] .erased),
  ("project a newly constructed value", agrees (program 2 #[
    ⟨2, .letOp (.construct 1 [.local 0, .local 1]) 1⟩,
    ⟨3, .letOp (.project (.local 2) 1) 2⟩, ⟨4, .ret (.local 3)⟩]) #[w 11, ext] ext),
  ("case of freshly constructed value preserves field order", agrees constructCase #[] (w 22)),
  ("tail-recursive empty traversal", agrees walk #[empty] (w 42)),
  ("tail-recursive one-node traversal", agrees walk #[pair (w 11) empty] (w 42)),
  ("tail-recursive two-node traversal", agrees walk #[pair (w 11) (pair (w 22) empty)] (w 42)),
  ("shared native construct/case statement golden", golden constructCase #[] (w 22)
    [13973111836034229465, 15659412292072259085, 17218498890851642343, 10094572489215979567]),
  ("shared native recursive traversal statement golden", golden walk #[pair (w 11) (pair (w 22) empty)] (w 42)
    [6894069929495142598, 13159459254287799980, 12762327979321263514, 8108651417668358157])
]

public def suite : IO UInt32 := runChecks "ixby-flock-objects" checks

end Tests.Ixby.Flock.Objects
