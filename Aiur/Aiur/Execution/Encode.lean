import Aiur.Execution.Hints
import Aiur.Ixon
import Std.Data.HashMap

/-! Ixon encodings of execution bytecode and data hints. The grammar is
documented with its Rust reader, `aiur::artifact`; `Aiur.Artifact` frames the
complete files. -/

namespace Aiur.Execution
open Aiur.Ixon

/-- The bytecode semantics version. Version 2 adds named hint channels. -/
def bytecodeVersion : Nat := 2

partial def putTy : Ty → PutM Unit
  | .field => u8 0
  | .tuple items => do u8 1; list items putTy
  | .ptr type => do u8 2; putTy type
  | .enum name => do u8 3; str name

/-- Read a type written by `putTy`. -/
partial def getTy : GetM Ty := do
  match ← getTag "type" 4 with
  | 0 => return .field
  | 1 => return .tuple (← getArray getTy).toList
  | 2 => return .ptr (← getTy)
  | _ => return .enum (← getString)

partial def putIOType : IOType → PutM Unit
  | .field => u8 0
  | .tuple items => do u8 1; list items putIOType
  | .array element length => do u8 2; putIOType element; nat length
  | .record name fields => do
      u8 3; str name
      list fields fun (field, type) => do str field; putIOType type
  | .enum name constructors => do
      u8 4; str name
      list constructors fun (constructor, fields) => do str constructor; list fields putIOType

private def putTests (encode : F → Nat) (tests : List (Register × F)) : PutM Unit :=
  list tests fun (register, value) => do nat register; nat (encode value)

def putInstruction (encode : F → Nat) : Instruction F → PutM Unit
  | .literal dest value => do u8 0; nat dest; nat (encode value)
  | .copy dest source => do u8 1; nats dest; nats source
  | .neg dest source => do u8 2; nat dest; nat source
  | .binary dest op left right => do
      u8 3; nat dest
      u8 (match op with | .add => 0 | .sub => 1 | .mul => 2 | .div => 3)
      nat left; nat right
  | .guard tests message => do u8 4; putTests encode tests; str message
  | .branch tests target => do u8 5; putTests encode tests; nat target
  | .jump target => do u8 6; nat target
  | .call function args dest => do u8 7; nat function; nats args; nats dest
  | .store type value dest => do u8 8; putTy type; nats value; nat dest
  | .load type pointer dest => do u8 9; putTy type; nat pointer; nats dest
  | .hint type keyType key dest channel => do
      u8 10; str channel; putTy type; putTy keyType; nats key; nats dest
  | .assertEq left right assertion => do
      u8 11; nats left; nats right
      option assertion.message str
      bool assertion.runtimeCheck
  | .ret value => do u8 12; nats value
  | .fail message => do u8 13; str message

def putHint (encode : F → Nat) (entry : FlatHintEntry F) : PutM Unit := do
  str entry.channel
  putTy entry.type
  putTy entry.keyType
  nats (entry.key.map encode)
  nats (entry.output.map encode)

/-- Prepared data hints, as the in-process FFI and execution packages carry
them. -/
def putHints (encode : F → Nat) (entries : Array (FlatHintEntry F)) : PutM Unit :=
  array entries (putHint encode)

/-- The distinct rows of `tables`, in the order the tables first name them,
and each table's rows as indices into them. -/
def rowPool (tables : List (List (List Nat))) : Array (List Nat) × List (List Nat) := Id.run do
  let mut rows : Array (List Nat) := #[]
  let mut index : Std.HashMap (List Nat) Nat := {}
  let mut indices : Array (List Nat) := #[]
  for table in tables do
    let mut refs : Array Nat := #[]
    for row in table do
      match index[row]? with
      | some i => refs := refs.push i
      | none =>
        refs := refs.push rows.size
        index := index.insert row rows.size
        rows := rows.push row
    indices := indices.push refs.toList
  return (rows, indices.toList)

/-- The program section of an artifact. The Rust field backend supports
primes fitting UInt64; the bytecode compiler itself is field-generic. -/
def Export.putProgram (exported : Export F) (modulus : Nat) (encode : F → Nat) :
    PutM Unit := do
  if modulus < 2 || modulus ≥ 2^64 then throw "execution requires a prime modulus fitting UInt64"
  let code := exported.bytecode
  nat bytecodeVersion
  nat modulus
  list code.functions fun fn => do
    str fn.name
    list fn.params putTy
    putTy fn.result
    nat fn.registers
    array fn.code (putInstruction encode)
  list code.enums fun decl => do
    str decl.name
    list decl.constructors fun c => do str c.name; list c.fields putTy
  let (rows, indices) := rowPool (code.tables.map fun table => table.rows.map (·.map encode))
  array rows nats
  list (code.tables.zip indices) fun (table, indices) => do
    str table.name
    putTy table.type
    nats indices
  list code.maps fun map => do
    str map.name
    list map.params putTy
    putTy map.result
    nat map.input
    nat map.output
  list code.entries fun (name, function) => do
    let some interface := exported.interfaces.find? (·.name == name)
      | throw s!"missing entry IO interface {name}"
    str name
    nat function
    list interface.inputs putIOType
    option interface.output putIOType

end Aiur.Execution
