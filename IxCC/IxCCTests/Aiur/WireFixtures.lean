import IxCC.Aiur.Wire.ComponentCheck

/-! Handwritten wire oracles. Expected bytes below do not call the encoder.
The corpus exercises representation, including semantically invalid indices
and circuit partitions; it is not an executable-program correctness fixture. -/

namespace IxCCTests.Aiur.WireFixtures

open _root_.IxCC.Vendor.Aiur (G)
open _root_.IxCC.Vendor.Aiur.Bytecode

def bytes (values : List UInt8) : ByteArray := ⟨values.toArray⟩

def concat (parts : List ByteArray) : ByteArray := parts.foldl (· ++ ·) ByteArray.empty

def expectedHeader : ByteArray :=
  "aiur-bytecode/1\x00".toUTF8 ++ bytes [40] ++
    "a8c4d2d21eaf45ee9160bdd103dfbcefe31f7f03".toUTF8

def opcodes : List (String × Op × List UInt8) := [
  ("const", .const 42, [0, 42, 0, 0, 0, 0, 0, 0, 0]),
  ("add", .add 1 2, [1, 1, 2]),
  ("sub", .sub 1 2, [2, 1, 2]),
  ("mul", .mul 1 2, [3, 1, 2]),
  ("eqZero", .eqZero 128, [4, 128, 1]),
  ("call", .call 3 #[1, 128] 2 true, [5, 3, 2, 1, 128, 1, 2, 1]),
  ("store", .store #[1, 2], [6, 2, 1, 2]),
  ("load", .load 128 2, [7, 128, 1, 2]),
  ("assertEq", .assertEq #[1] #[2] (some "é"), [8, 1, 1, 1, 2, 1, 2, 195, 169]),
  ("ioGetInfo", .ioGetInfo 1 #[2, 3], [9, 1, 2, 2, 3]),
  ("ioSetInfo", .ioSetInfo 1 #[2] 3 4, [10, 1, 1, 2, 3, 4]),
  ("ioRead", .ioRead 1 2 3, [11, 1, 2, 3]),
  ("ioWrite", .ioWrite 1 #[2, 3], [12, 1, 2, 2, 3]),
  ("u8BitDecomposition", .u8BitDecomposition 1, [13, 1]),
  ("u8ShiftLeft", .u8ShiftLeft 1, [14, 1]),
  ("u8ShiftRight", .u8ShiftRight 1, [15, 1]),
  ("u8Xor", .u8Xor 1 2, [16, 1, 2]),
  ("u8Add", .u8Add 1 2, [17, 1, 2]),
  ("u8Mul", .u8Mul 1 2, [18, 1, 2]),
  ("u8Sub", .u8Sub 1 2, [19, 1, 2]),
  ("u8And", .u8And 1 2, [20, 1, 2]),
  ("u8Or", .u8Or 1 2, [21, 1, 2]),
  ("u8LessThan", .u8LessThan 1 2, [22, 1, 2]),
  ("u32LessThan", .u32LessThan 1 2, [23, 1, 2]),
  ("u8XorSplit7", .u8XorSplit7 1 2, [24, 1, 2]),
  ("u8XorSplit4", .u8XorSplit4 1 2, [25, 1, 2]),
  ("debug", .debug "λ\x00" (some #[1, 128]), [26, 3, 206, 187, 0, 1, 2, 1, 128, 1]),
  ("u8RangeCheck", .u8RangeCheck 1 2, [27, 1, 2]),
  ("unconstrainedBigUintDivMod", .unconstrainedBigUintDivMod 1 2, [28, 1, 2]),
  ("unconstrainedGToBytes", .unconstrainedGToBytes 1, [29, 1]),
  ("unconstrainedGInverse", .unconstrainedGInverse 1, [30, 1]),
  ("unconstrainedU32Add", .unconstrainedU32Add #[1, 2] #[3, 4], [31, 2, 1, 2, 2, 3, 4]),
  ("unconstrainedU32Add3", .unconstrainedU32Add3 #[1] #[2] #[3], [32, 1, 1, 1, 2, 1, 3]),
  ("u32ToField", .u32ToField #[1, 2, 3, 4], [33, 4, 1, 2, 3, 4])]

def empty : Toplevel := ⟨#[], #[], #[], #[]⟩

def counterLayout : FunctionLayout := ⟨1, 2, 4, 2⟩

def counterBody : Block := ⟨#[], .match 0 #[(0, ⟨#[.const 0], .return 0 #[1]⟩)]
  (some ⟨#[.const 1, .sub 0 1, .call 0 #[2] 1 false], .return 1 #[3]⟩)⟩

def counter : Toplevel :=
  ⟨#[⟨counterBody, counterLayout, true, true⟩], #[1, 2, 8],
    #[⟨"count", #[0], counterLayout⟩], #[⟨0, false⟩]⟩

def counterExpected : ByteArray := expectedHeader ++ concat [
  bytes [1, 0, 0, 0, 1], -- function, empty root ops, match value zero, one case
  bytes [0, 0, 0, 0, 0, 0, 0, 0], -- case key
  bytes [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1], -- const zero, return
  bytes [1, 3, 0, 1, 0, 0, 0, 0, 0, 0, 0], -- fallback, three ops, const one
  bytes [2, 0, 1, 5, 0, 1, 2, 1, 0, 1, 1, 1, 3], -- sub, call, return
  bytes [1, 2, 4, 2, 1, 1, 3, 1, 2, 8], -- layout, flags, memory buckets
  bytes [1, 5, 99, 111, 117, 110, 116, 1, 0, 1, 2, 4, 2], -- circuit
  bytes [1, 0, 0]] -- unranked component

def mutualFunction (callee : Nat) (entry : Bool) : Function :=
  ⟨⟨#[.call callee #[0] 1 false], .return 0 #[1]⟩, ⟨1, 1, 2, 2⟩, entry, true⟩

def rankedMutual : Toplevel :=
  ⟨#[mutualFunction 1 true, mutualFunction 0 false], #[], #[], #[⟨0, true⟩, ⟨0, true⟩]⟩

def rankedExpected : ByteArray := expectedHeader ++ bytes [
  2, 1, 5, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 2, 2, 1, 1,
  1, 5, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 2, 2, 0, 1,
  0, 0, 2, 0, 1, 0, 1]

def corpusBody : Block :=
  ⟨(opcodes.map (·.2.1)).toArray,
    .matchContinue 1 #[(9, ⟨#[], .yield 2 #[0, 1]⟩), (7, ⟨#[], .match 0 #[] none⟩)]
      (some ⟨#[], .yield 3 #[]⟩) 4 5 6 ⟨#[], .return 4 #[0, 1, 2, 3]⟩⟩

def corpus : Toplevel :=
  ⟨#[⟨corpusBody, ⟨7, 8, 9, 10⟩, false, false⟩,
      ⟨⟨#[], .match 0 #[] none⟩, ⟨0, 0, 1, 0⟩, true, true⟩],
    #[0, 1, 255, 65536, 2 ^ 64],
    #[⟨"α\x00", #[1, 0, 1], ⟨11, 12, 13, 14⟩⟩, ⟨"", #[], ⟨0, 0, 0, 0⟩⟩],
    #[⟨1, false⟩, ⟨0, true⟩]⟩

def corpusExpected : ByteArray := expectedHeader ++ concat [
  bytes [2, 34], concat (opcodes.map (fun entry => bytes entry.2.2)),
  bytes [3, 1, 2, 9, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 0, 1],
  bytes [7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  bytes [1, 0, 2, 3, 0, 4, 5, 6, 0, 1, 4, 4, 0, 1, 2, 3],
  bytes [7, 8, 9, 10, 0, 0],
  bytes [0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1],
  bytes [5, 0, 1, 255, 1, 128, 128, 4, 128, 128, 128, 128, 128, 128, 128, 128, 128, 2],
  bytes [2, 3, 206, 177, 0, 3, 1, 0, 1, 11, 12, 13, 14],
  bytes [0, 0, 0, 0, 0, 0],
  bytes [2, 1, 0, 0, 1]]

def fixtures : List (String × Toplevel × ByteArray) := [
  ("empty", empty, expectedHeader ++ bytes [0, 0, 0, 0]),
  ("unit-counter", counter, counterExpected),
  ("ranked-mutual", rankedMutual, rankedExpected),
  ("wire-corpus", corpus, corpusExpected)]

end IxCCTests.Aiur.WireFixtures
