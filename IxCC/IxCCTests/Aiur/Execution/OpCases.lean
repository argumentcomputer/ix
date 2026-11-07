import IxCCTests.Aiur.Execution.Support
import IxCC.Aiur.Wire.Op

/-! Literal operation oracles. Expected outputs, logical tags, messages,
and advice records do not call the evaluator or primitive implementation. -/

namespace IxCCTests.Aiur.Execution

open IxCC.Aiur
open IxCC.Aiur.OracleEval
open _root_.IxCC.Vendor.Aiur.Bytecode (Op Toplevel)

structure OpCase where
  name : String
  op : Op
  inputs : Values := []
  replies : List Values := []
  outputs : Values := []
  demands : List Message := []
  advice : List AdviceObservation := []

def callTarget : Toplevel :=
  ⟨#[mkFunction 0 ⟨#[], .return 0 #[]⟩,
      mkFunction 2 ⟨#[.add 0 1], .return 0 #[2]⟩], #[], #[], #[]⟩

def opCases : List OpCase := [
  { name := "const", op := .const 42, outputs := [42] },
  { name := "field add wraps at p", op := .add 0 1,
    inputs := [0xffffffff00000000, 1], outputs := [0] },
  { name := "field subtraction", op := .sub 0 1,
    inputs := [0, 1], outputs := [0xffffffff00000000] },
  { name := "field product does not wrap at u64", op := .mul 0 1,
    inputs := [4294967296, 4294967296], outputs := [4294967295] },
  { name := "eqZero zero", op := .eqZero 0, inputs := [0], outputs := [1] },
  { name := "eqZero nonzero", op := .eqZero 0, inputs := [9], outputs := [0] },
  { name := "constrained call", op := .call 1 #[0, 1] 1 false,
    inputs := [20, 22], replies := [[42]], outputs := [42],
    demands := [.function 1 [20, 22] [42]] },
  { name := "unconstrained call", op := .call 1 #[0, 1] 1 true,
    inputs := [20, 22], replies := [[99]], outputs := [99],
    advice := [⟨.call 1 [20, 22] 1, [99]⟩] },
  { name := "store arbitrary pointer", op := .store #[0], inputs := [42],
    replies := [[7]], outputs := [7], demands := [.memory 1 7 [42]] },
  { name := "load witness cell", op := .load 1 0, inputs := [7],
    replies := [[42]], outputs := [42], demands := [.memory 1 7 [42]] },
  { name := "assertEq", op := .assertEq #[0] #[1] (some "checked"), inputs := [5, 5] },
  { name := "ioGetInfo is advice", op := .ioGetInfo 0 #[1], inputs := [7, 9],
    replies := [[12, 2]], outputs := [12, 2], advice := [⟨.ioGetInfo 7 [9], [12, 2]⟩] },
  { name := "ioSetInfo has no constrained effect", op := .ioSetInfo 0 #[1] 2 3,
    inputs := [7, 9, 12, 2] },
  { name := "ioRead is advice", op := .ioRead 0 1 2, inputs := [7, 12],
    replies := [[88, 99]], outputs := [88, 99], advice := [⟨.ioRead 7 12 2, [88, 99]⟩] },
  { name := "ioWrite has no constrained effect", op := .ioWrite 0 #[1, 2], inputs := [7, 5, 6] },
  { name := "byte decomposition LE", op := .u8BitDecomposition 0, inputs := [165],
    replies := [[1, 0, 1, 0, 0, 1, 0, 1]], outputs := [1, 0, 1, 0, 0, 1, 0, 1],
    demands := [.gadget 0 [165, 1, 0, 1, 0, 0, 1, 0, 1]] },
  { name := "byte shift left", op := .u8ShiftLeft 0, inputs := [200],
    replies := [[144]], outputs := [144], demands := [.gadget 1 [200, 144]] },
  { name := "byte shift right", op := .u8ShiftRight 0, inputs := [201],
    replies := [[100]], outputs := [100], demands := [.gadget 2 [201, 100]] },
  { name := "byte xor", op := .u8Xor 0 1, inputs := [172, 85],
    replies := [[249]], outputs := [249], demands := [.gadget 3 [172, 85, 249]] },
  { name := "byte add carry", op := .u8Add 0 1, inputs := [250, 9],
    replies := [[3, 1]], outputs := [3, 1], demands := [.gadget 4 [250, 9, 3, 1]] },
  { name := "byte multiply high", op := .u8Mul 0 1, inputs := [200, 3],
    replies := [[88, 2]], outputs := [88, 2], demands := [.gadget 5 [200, 3, 88, 2]] },
  { name := "byte subtract borrow", op := .u8Sub 0 1, inputs := [3, 9],
    replies := [[250, 1]], outputs := [250, 1], demands := [.gadget 6 [3, 9, 250, 1]] },
  { name := "byte and", op := .u8And 0 1, inputs := [172, 85],
    replies := [[4]], outputs := [4], demands := [.gadget 7 [172, 85, 4]] },
  { name := "byte or", op := .u8Or 0 1, inputs := [172, 85],
    replies := [[253]], outputs := [253], demands := [.gadget 8 [172, 85, 253]] },
  { name := "byte less than", op := .u8LessThan 0 1, inputs := [3, 9],
    replies := [[1]], outputs := [1], demands := [.gadget 9 [3, 9, 1]] },
  { name := "u32 less than", op := .u32LessThan 0 1, inputs := [4294967294, 4294967295],
    replies := [[1]], outputs := [1], demands := [.gadget 10 [4294967294, 4294967295, 1]] },
  { name := "xor split 7", op := .u8XorSplit7 0 1, inputs := [172, 85],
    replies := [[1, 242]], outputs := [1, 242], demands := [.gadget 11 [172, 85, 1, 242]] },
  { name := "xor split 4", op := .u8XorSplit4 0 1, inputs := [172, 85],
    replies := [[15, 144]], outputs := [15, 144], demands := [.gadget 12 [172, 85, 15, 144]] },
  { name := "debug has no constrained effect", op := .debug "λ\x00" (some #[999]) },
  { name := "byte range pair", op := .u8RangeCheck 0 1, inputs := [0, 255],
    replies := [[]], demands := [.gadget 13 [0, 255]] },
  { name := "divmod pointer hints are arbitrary", op := .unconstrainedBigUintDivMod 0 1,
    inputs := [7, 8], replies := [[123, 456]], outputs := [123, 456],
    advice := [⟨.bigUintDivMod 7 8, [123, 456]⟩] },
  { name := "field byte hints are arbitrary", op := .unconstrainedGToBytes 0,
    inputs := [42], replies := [[9, 9, 9, 9, 9, 9, 9, 9]], outputs := [9, 9, 9, 9, 9, 9, 9, 9],
    advice := [⟨.gToBytes 42, [9, 9, 9, 9, 9, 9, 9, 9]⟩] },
  { name := "inverse hint is arbitrary", op := .unconstrainedGInverse 0,
    inputs := [0], replies := [[17]], outputs := [17], advice := [⟨.gInverse 0, [17]⟩] },
  { name := "u32 add virtual carry", op := .unconstrainedU32Add #[0, 1, 2, 3] #[4, 5, 6, 7],
    inputs := [255, 255, 255, 255, 1, 0, 0, 0], replies := [[0, 0, 0, 0]], outputs := [0, 0, 0, 0, 1],
    advice := [⟨.u32Add [255, 255, 255, 255] [1, 0, 0, 0], [0, 0, 0, 0]⟩] },
  { name := "u32 add3 virtual carry", op := .unconstrainedU32Add3 #[0, 1, 2, 3] #[4, 5, 6, 7] #[8, 9, 10, 11],
    inputs := [255, 255, 255, 255, 255, 255, 255, 255, 2, 0, 0, 0],
    replies := [[0, 0, 0, 0]], outputs := [0, 0, 0, 0, 2],
    advice := [⟨.u32Add3 [255, 255, 255, 255] [255, 255, 255, 255] [2, 0, 0, 0], [0, 0, 0, 0]⟩] },
  { name := "u32 packing LE", op := .u32ToField #[0, 1, 2, 3],
    inputs := [120, 86, 52, 18], outputs := [305419896] },
  { name := "packing does not invent byte ranges", op := .u32ToField #[0, 1, 2, 3],
    inputs := [256, 0, 0, 0], outputs := [256] }]

def runOps (count : IO.Ref Nat) : IO Unit := do
  need count "all 34 pinned opcode tags exercised" ((List.range 34).all fun tag =>
    opCases.any fun test => (IxCC.Aiur.Wire.opBytes test.op).data[0]? == some tag.toUInt8)
  for test in opCases do
    let result := evalOp callTarget 128 test.op { values := test.inputs.toArray, replies := test.replies }
    match result with
    | .error error => throw (IO.userError s!"Aiur operation {test.name}: {repr error}")
    | .ok state =>
        need count (test.name ++ " outputs") (decide (state.values.toList = test.inputs ++ test.outputs))
        need count (test.name ++ " exact demands") (decide (state.demandsRev.reverse = test.demands))
        need count (test.name ++ " advice") (decide (state.adviceRev.reverse = test.advice))
        need count (test.name ++ " complete reply consumption") state.replies.isEmpty
    for message in test.demands do
      if let .gadget channel payload := message then
        need count (test.name ++ " primitive meaning") (Gadget.check channel payload)
  for (name, channel, payload) in [
      ("byte input cannot truncate", 3, [256, 0, 0]),
      ("negative field value is not a byte", 13, [0xffffffff00000000, 0]),
      ("u32 input cannot truncate", 10, [4294967296, 0, 0]),
      ("wrong carry", 4, [250, 9, 3, 0]),
      ("wrong borrow", 6, [3, 9, 250, 0]),
      ("wrong xor", 3, [1, 2, 9]),
      ("missing byte output", 3, [1, 2]),
      ("extra byte output", 3, [1, 2, 3, 4]),
      ("nonboolean decomposition", 0, [0, 2, 0, 0, 0, 0, 0, 0, 0]),
      ("unknown logical gadget channel", 14, [])] do
    need count name (!(Gadget.check channel payload))
  need count "equal u32 inputs compare false" (Gadget.check 10 [4294967295, 4294967295, 0])
  need count "equal byte inputs compare false" (Gadget.check 9 [255, 255, 0])

end IxCCTests.Aiur.Execution
