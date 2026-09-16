module

public import Ix.Aiur.Stages.Bytecode
public import Blake3.Rust

public section

namespace Aiur.TraceContract
open Bytecode

/-- The wire format uses explicit variant tags, little-endian u64 lengths and
indices, single-byte flags, and length-prefixed UTF-8 strings. Arm order is
preserved because it determines default-arm inverse columns. -/
private abbrev Encode := StateM ByteArray
private def byte (n : Nat) : Encode Unit := modify (·.push n.toUInt8)
private def word (n : Nat) : Encode Unit := do
  for i in [:8] do byte ((n >>> (8*i)) &&& 255)
private def array (write : α → Encode Unit) (xs : Array α) : Encode Unit := do
  word xs.size
  for x in xs do write x
private def optional (write : α → Encode Unit) (x : Option α) : Encode Unit := do
  match x with
  | none => byte 0
  | some x => byte 1; write x
private def text (s : String) : Encode Unit := do
  let bytes := s.toUTF8
  word bytes.size
  modify (· ++ bytes)
private def indices := array word
private def unary (tag a : Nat) : Encode Unit := byte tag *> word a
private def binary (tag a b : Nat) : Encode Unit := unary tag a *> word b

private def operation : Op → Encode Unit
  | .const x => unary 0 x.n
  | .add a b => binary 1 a b
  | .sub a b => binary 2 a b
  | .mul a b => binary 3 a b
  | .eqZero a => unary 4 a
  | .call f args n u => do byte 5; word f; indices args; word n; byte (if u then 1 else 0)
  | .store xs => byte 6 *> indices xs
  | .load n p => binary 7 n p
  | .assertEq a b msg => do byte 8; indices a; indices b; optional text msg
  | .ioGetInfo c key => do unary 9 c; indices key
  | .ioSetInfo c key i n => do unary 10 c; indices key; word i; word n
  | .ioRead c i n => do binary 11 c i; word n
  | .ioWrite c xs => unary 12 c *> indices xs
  | .u8BitDecomposition a => unary 13 a
  | .u8ShiftLeft a => unary 14 a
  | .u8ShiftRight a => unary 15 a
  | .u8Xor a b => binary 16 a b
  | .u8Add a b => binary 17 a b
  | .u8Mul a b => binary 18 a b
  | .u8Sub a b => binary 19 a b
  | .u8And a b => binary 20 a b
  | .u8Or a b => binary 21 a b
  | .u8LessThan a b => binary 22 a b
  | .u32LessThan a b => binary 23 a b
  | .u8XorSplit7 a b => binary 24 a b
  | .u8XorSplit4 a b => binary 25 a b
  | .debug msg args => do byte 26; text msg; optional indices args
  | .u8RangeCheck a b => binary 27 a b
  | .unconstrainedBigUintDivMod a b => binary 28 a b
  | .unconstrainedGToBytes a => unary 29 a
  | .unconstrainedGInverse a => unary 30 a
  | .unconstrainedU32Add a b => do byte 31; indices a; indices b
  | .unconstrainedU32Add3 a b c => do byte 32; indices a; indices b; indices c
  | .u32ToField a => byte 33 *> indices a

mutual
  private partial def block (b : Block) : Encode Unit := array operation b.ops *> control b.ctrl
  private partial def arms (xs : Array (G × Block)) : Encode Unit :=
    array (fun (value, body) => word value.n *> block body) xs
  private partial def control : Ctrl → Encode Unit
    | .match d xs fallback => do unary 0 d; arms xs; optional block fallback
    | .return s xs => unary 1 s *> indices xs
    | .yield s xs => unary 2 s *> indices xs
    | .matchContinue d xs fallback n aux lookup continuation => do
      unary 3 d; arms xs; optional block fallback
      word n; word aux; word lookup; block continuation
end

private def layout (l : FunctionLayout) : Encode Unit := do
  word l.inputSize; word l.selectors; word l.auxiliaries; word l.lookups

def bytes (top : Toplevel) : ByteArray := Id.run do
  let write : Encode Unit := do
    array (fun f => do
      layout f.layout; byte (if f.entry then 1 else 0); byte (if f.constrained then 1 else 0)
      block f.body) top.functions
    indices top.memorySizes
  return (write.run "aiur-trace-library-v1/seed-v1/writer-v1\x00".toUTF8).2

def fingerprint (top : Toplevel) : ByteArray := (Blake3.Rust.hash (bytes top)).val

def fingerprintLiteral (top : Toplevel) : String :=
  ", ".intercalate ((fingerprint top).data.toList.map toString)

end Aiur.TraceContract
end
