module
public import Tests.Ixby.Common
public import Ix.Ixby.Aiur.Objects.Parser
public import Ix.Ixby.Aiur.Objects.Identity
public import Ix.Ixby.Aiur.Objects.Unique
public import Ix.Ixby.Aiur.Objects.Declarations
public import Ix.Ixby.Aiur.Objects.Admission
public import Ix.Ixby.Aiur.Objects.ProgramPrefix
public import Ix.Ixby.Aiur.Objects.CodeHeaders
public import Ix.Ixby.Aiur.Objects.Operands
public import Ix.Ixby.Aiur.Objects
public import Ix.Aiur.Compiler

/-! Shared byte streams, memory observations and wire fixtures. No interpreter
is compiled here; the facade compiles full and pruned contexts once per run. -/

public section

namespace Tests.Ixby.Aiur.Objects.Parser

open Ix.Ixby Ix.Ixby.AiurBackend
open Ix.Ixby.AiurBackend.Objects.Memory Ix.Ixby.AiurBackend.Objects.Table Ix.Ixby.AiurBackend.Objects.Parser
open Ix.Ixby.AiurBackend.Objects.Identity
open Ix.Ixby.AiurBackend.Objects.Equality Ix.Ixby.AiurBackend.Objects.Unique
open Ix.Ixby.AiurBackend.Objects.Declarations
open Ix.Ixby.AiurBackend.Objects.Admission
open Aiur.Bytecode.Eval

def function (compiled : Aiur.CompiledToplevel) (name : Lean.Name) :
    Except String (Nat × Aiur.Bytecode.Function) := do
  let some index := compiled.getFuncIdx name | throw s!"missing function {name}"
  let some f := compiled.bytecode.functions[index]? | throw s!"missing index {index}"
  return (index, f)

def snapshot (compiled : Aiur.CompiledToplevel) (name : Lean.Name)
    (args : Array Aiur.G) (initial : EvalState) (fuel := 8) :
    Except String (Array Aiur.G × EvalState) := do
  let (_, f) ← function compiled name
  unless f.layout.inputSize == args.size do throw "input arity"
  match evalBlock compiled.bytecode fuel f.body { initial with map := args } with
  | .ok (flat, state) | .error (.earlyReturn flat state) => return (flat, state)
  | .error error => throw (reprStr error)

def initial : EvalState := {
  map := #[123, 456],
  ioBuffer := (default : Aiur.IOBuffer).extend 7 #[8, 9] #[10, 11, 12] }

def memoryView (state : EvalState) : Array (Nat × Array (Array Aiur.G)) :=
  state.memory.pairs.map fun (width, bucket) => (width, bucket.pairs.map Prod.fst)
def sameIo (before after : EvalState) : Bool :=
  before.ioBuffer.data.toList == after.ioBuffer.data.toList &&
    before.ioBuffer.map.toList == after.ioBuffer.map.toList
def unchanged (before after : EvalState) : Bool :=
  memoryView before == memoryView after && sameIo before after
def preservesReads (before after : EvalState) : Bool :=
  before.memory.pairs.all fun (width, bucket) =>
    bucket.pairs.toList.zipIdx.all fun ((flat, _), pointer) =>
      match memLoad after width pointer with | .ok found => found == flat | _ => false

def storePrefix (st : EvalState) (bytes : Array Aiur.G) (tail : Aiur.G) : EvalState × Aiur.G :=
  bytes.foldr (fun byte state =>
    let next := memStore state.1 #[0, byte, state.2]
    (next.1, .ofNat next.2)) (st, tail)
def storeStream (st : EvalState) (bytes : Array Aiur.G) : EvalState × Aiur.G :=
  let (st, pointer) := memStore st #[1, 1, 1]
  storePrefix st bytes (.ofNat pointer)

def success (result : Except String (Array Aiur.G × EvalState))
    (out : Array Aiur.G) (before : EvalState) : Bool :=
  match result with | .ok (actual, after) => actual == out && unchanged before after | _ => false
def failed (result : Except String (Array Aiur.G × EvalState))
    (error : BytecodeError) : Bool :=
  match result with | .error actual => actual == reprStr error | _ => false

def wordBytes (n : Nat) : WordBytes :=
  ⟨.ofNat n, .ofNat (n / 256), .ofNat (n / 65536), .ofNat (n / 16777216)⟩

def wireDeclaration (n fields : Nat) : DeclarationBytes := {
  a := wordBytes 0x01020304, b := wordBytes 0x05060708, c := wordBytes 0x11121314,
  d := wordBytes 0x15161718, e := wordBytes 0x21222324, f := wordBytes 0x25262728,
  g := wordBytes 0x31323334, h := wordBytes (2 ^ 32 - 1),
  member := wordBytes (0x41424340 + n), tag := wordBytes (0x45464740 + n), fields := wordBytes fields }

def wireDeclarations (count : Nat) : List DeclarationBytes :=
  (List.range count).map fun i => wireDeclaration i (if i % 2 == 0 then 0 else 16)

def declarationPayload (decls : List DeclarationBytes) : Array Aiur.G :=
  (decls.flatMap DeclarationBytes.bytes).toArray.map Aiur.G.ofUInt8

def streamMatches (st : EvalState) (pointer : Aiur.G) : List Aiur.G → Bool
  | [] => match memLoad st 3 pointer.n with | .ok cell => cell == #[1, 1, 1] | _ => false
  | value :: values =>
    match memLoad st 3 pointer.n with
    | .ok cell => match cell.toList with
      | [tag, head, tail] => tag == 0 && head == value && streamMatches st tail values
      | _ => false
    | _ => false

def skipStream (st : EvalState) (pointer : Aiur.G) : Nat → Option Aiur.G
  | 0 => some pointer
  | count + 1 => do
    let .ok cell := memLoad st 3 pointer.n | none
    let [tag, _, tail] := cell.toList | none
    if tag == 0 then skipStream st tail count else none

def rawAdvice (st : EvalState) (channel : Aiur.G) (start length : Nat) (values : Array Aiur.G) : EvalState :=
  { st with ioBuffer := {
      data := st.ioBuffer.data.insert channel values,
      map := st.ioBuffer.map.insert (channel, #[0]) ⟨start, length⟩ } }

end Tests.Ixby.Aiur.Objects.Parser
