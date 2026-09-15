module
import Tests.Ixby.Common
import Ix.Ixby.Codec
import Ix.Ixby.Commitment

/-! Independent reference fixtures for the native application setup. These
check canonical bytes, higher-order execution and exact fuel. They are not a
proof that native Boolean rows refine the reference application machine. -/

namespace Tests.Ixby.Flock.Applications

open Ix.Ixby

private def profile : Profile := {
  limits := {
    functions := 3, constructors := 2, blocks := 3, locals := 4
    operands := 2, continuations := 3, inputNodes := 7
    natBits := 0, stringBytes := 0, byteArrayBytes := 33 }
  programBytes := 256, valueBytes := 192, valueDepth := 3, maxSteps := 12 }
private def pairId : CtorId := {
  block := 0x9191919191919191919191919191919191919191919191919191919191919191
  member := 0xffffffff, tag := 0x80000000 }
private def w (n : UInt32) : Value := .scalar (.word32 n)
private def lit (n : UInt32) : Operand := .literal (.word32 n)
private def bytes (data : Array UInt8) : Value := .scalar (.bytes data)
private def pair (a b : Value) : Value := .ctor pairId #[a, b]
private def f (arity : Nat) (blocks : Array Block) : Function := { arity, blocks }
private def identity (arity index : Nat) : Function := f arity #[⟨arity, .ret (.local index)⟩]
private def add : Function := f 2 #[
  ⟨2, .letOp (.primitive .word32Add [.local 0, .local 1]) 1⟩, ⟨3, .ret (.local 2)⟩]
private def program (functions : Array Function) : Program := {
  constructors := #[⟨pairId, 2⟩], functions }
private def over (tail : Bool) : Program := program #[
  f 1 (if tail then #[⟨1, .tailApply (.local 0) [lit 11, lit 22]⟩]
    else #[⟨1, .letOp (.apply (.local 0) [lit 11, lit 22]) 1⟩, ⟨2, .ret (.local 1)⟩]),
  f 1 #[⟨1, .letOp (.closure 2 []) 1⟩, ⟨2, .ret (.local 1)⟩], identity 1 0]

private structure Case where
  code : Program
  input : Array Value
  output : Value
  fuel : Nat
private def c (functions : Array Function) (input : Array Value) (output : Value)
    (fuel : Nat) : Case := ⟨program functions, input, output, fuel⟩

private def cases : Array Case := Id.run do
  let mut result := #[
    c #[f 0 #[⟨0, .letOp (.closure 1 [lit 11]) 1⟩, ⟨1, .ret (.local 0)⟩], identity 2 1]
      #[] (.pap 1 #[w 11]) 3,
    c #[f 0 #[⟨0, .letOp (.closure 1 []) 1⟩, ⟨1, .ret (.local 0)⟩], identity 1 0]
      #[] (.pap 1 #[]) 3]
  for value in #[w 42, .erased, pair (w 11) (w 22), .pap 1 #[w 11], bytes #[0, 255]] do
    result := result.push (c #[f 1 #[⟨1, .tailApply (.local 0) []⟩], identity 2 1] #[value] value 3)
  result := result ++ #[
    c #[f 0 #[⟨0, .tailApply .erased [lit 11, lit 22]⟩]] #[] .erased 3,
    c #[f 1 #[⟨1, .tailApply (.local 0) [lit 11]⟩], identity 2 1] #[.pap 1 #[]] (.pap 1 #[w 11]) 3,
    c #[f 1 #[⟨1, .tailApply (.local 0) [lit 42]⟩], identity 1 0] #[.pap 1 #[]] (w 42) 4,
    c #[f 1 #[⟨1, .tailApply (.local 0) [lit 31]⟩], add] #[.pap 1 #[w 11]] (w 42) 5,
    c #[f 1 #[⟨1, .letOp (.apply (.local 0) [lit 30]) 1⟩,
      ⟨2, .letOp (.primitive .word32Add [.local 1, lit 1]) 2⟩, ⟨3, .ret (.local 2)⟩], add]
      #[.pap 1 #[w 11]] (w 42) 8]
  for tail in #[false, true] do
    let blocks := #[⟨0, .letOp (.closure 1 [lit 11]) 1⟩] ++
      (if tail then #[⟨1, .tailApply (.local 0) [lit 31]⟩] else
        #[⟨1, .letOp (.apply (.local 0) [lit 31]) 2⟩, ⟨2, .ret (.local 1)⟩])
    result := result.push (c #[f 0 blocks, add] #[] (w 42) (if tail then 6 else 8))
  for tail in #[false, true] do
    result := result.push ⟨over tail, #[.pap 1 #[]], w 22, if tail then 8 else 10⟩
  result := result ++ #[
    c #[f 0 #[⟨0, .letOp (.call 1 []) 1⟩, ⟨1, .tailApply (.local 0) [lit 11, lit 22]⟩],
      f 0 #[⟨0, .letOp (.closure 2 []) 1⟩, ⟨1, .ret (.local 0)⟩], f 1 #[⟨1, .ret .erased⟩]]
      #[] .erased 10,
    c #[f 1 #[⟨1, .letOp (.project (.local 0) 0) 1⟩, ⟨2, .tailApply (.local 1) [lit 31]⟩], add]
      #[pair (.pap 1 #[w 11]) .erased] (w 42) 6]
  for captured in #[.pap 2 #[], pair (w 11) .erased, bytes #[3, 2, 1]] do
    result := result.push (c #[f 1 #[⟨1, .tailApply (.local 0) [lit 0]⟩], identity 2 0, identity 1 0]
      #[.pap 1 #[captured]] captured 4)
  result := result ++ #[
    c #[f 1 #[⟨1, .tailApply (.local 0) [lit 0]⟩], f 2 #[
      ⟨2, .letOp (.primitive .blake3 [.local 0]) 1⟩, ⟨3, .ret (.local 2)⟩]]
      #[.pap 1 #[bytes #[3, 2, 1]]] (bytes (Blake3.hash #[3, 2, 1])) 5,
    c #[f 0 #[⟨0, .letOp (.closure 1 []) 1⟩, ⟨1, .letOp (.construct 0 [.local 0, .local 0]) 2⟩,
      ⟨2, .ret (.local 1)⟩], identity 1 0] #[] (pair (.pap 1 #[]) (.pap 1 #[])) 4,
    c #[f 2 #[⟨2, .letOp (.closure 1 [.local 0]) 1⟩, ⟨3, .ret (.local 2)⟩], identity 2 0]
      #[pair (w 11) .erased, w 99] (.pap 1 #[pair (w 11) .erased]) 3,
    c #[f 0 #[⟨0, .tailApply (.literal (.bytes #[0x80, 3, 0xff])) []⟩]]
      #[] (bytes #[0x80, 3, 0xff]) 3,
    c #[f 1 #[⟨1, .tailApply (.local 0) [lit 9]⟩], f 2 #[
      ⟨2, .letOp (.primitive .word32Sub [.local 0, .local 1]) 1⟩, ⟨3, .ret (.local 2)⟩]]
      #[.pap 1 #[w 41]] (w 32) 5,
    c #[f 1 #[⟨1, .letOp (.apply (.local 0) [lit 11]) 1⟩,
      ⟨2, .tailApply (.local 1) [lit 22]⟩], identity 2 0] #[.pap 1 #[]] (w 11) 7]
  return result

private def artifacts (fixture : Case) : Except Codec.Error (Codec.Bytes × Codec.Bytes × Codec.Bytes) := do
  return (← Codec.encodeProgram profile fixture.code, ← Codec.encodeInput profile fixture.code fixture.input,
    ← Codec.encodeOutput profile fixture.code fixture.output)
private def agrees (fixture : Case) : Bool :=
  match artifacts fixture with
  | .error _ => false
  | .ok (code, input, output) => match Codec.execute profile code input profile.maxSteps with
    | .error _ => false
    | .ok execution => execution.output == fixture.output && execution.outputBytes == output &&
      (match Ix.Ixby.execute profile.limits fixture.code fixture.input fixture.fuel with
        | .ok value => value == fixture.output | .error _ => false) &&
      (match Ix.Ixby.execute profile.limits fixture.code fixture.input (fixture.fuel - 1) with
        | .error .outOfFuel => true | _ => false)
private def digestWords (digest : Commitment.Digest) : List Nat :=
  (List.range 4).map fun word =>
    (List.range 8).foldl (fun n byte =>
      n + digest.bytes[word * 8 + byte]!.toNat * 2 ^ (8 * byte)) 0
private def golden (index : Nat) : List Nat :=
  match cases[index]? with
  | none => []
  | some fixture => match artifacts fixture with
    | .error _ => []
    | .ok (code, input, output) => match Commitment.ofArtifacts profile code input output with
      | .error _ => []
      | .ok statement => digestWords statement.digest

-- These kernel-checked examples also pin the empty-stack terminal transition.
example : Ix.Ixby.execute profile.limits (over false) #[.pap 1 #[]] 10 = .ok (w 22) := rfl
example : Ix.Ixby.execute profile.limits (over false) #[.pap 1 #[]] 9 = .error .outOfFuel := rfl
example : Ix.Ixby.execute profile.limits (over true) #[.pap 1 #[]] 8 = .ok (w 22) := rfl
example : Ix.Ixby.execute profile.limits (over true) #[.pap 1 #[]] 7 = .error .outOfFuel := rfl

private def checks : IO (List Check) := do
  pure <| [
    ("native closure statement golden", golden 0 ==
      [14687990384083634, 5830356504901387565, 14359430384946980301, 11454731321620998259]),
    ("native over-application statement golden", golden 14 ==
      [16522776896425344640, 1119810387505576751, 6309516584285128144, 8596517101313489382]),
    ("native empty byte-literal application golden", golden 24 ==
      [1846894401329383370, 878564278452078894, 337315515468421852, 2613245647962240889]),
    ("27 independent native application fixtures", cases.size == 27)] ++
    cases.toList.zipIdx.map fun (fixture, index) =>
      (s!"native application {index}: canonical bytes, result and exact fuel", agrees fixture)

public def suite : IO UInt32 := runChecks "ixby-flock-applications" checks

end Tests.Ixby.Flock.Applications
