import Ix.Aiur.Compiler
import Ix.Aggr
import Ix.IxVM.Toplevel
import Ix.IxVM.FunctionGroups

set_option maxRecDepth 65536
set_option maxHeartbeats 0
open Aiur.Bytecode

def vec (xs : Array Nat) : String := "vec![" ++ String.intercalate "," (xs.toList.map toString) ++ "]"
def op (o : Op) : String := Id.run do
  let s := match o with
    | .const g => s!"Const(G::from_u64({g.val.toNat}))"
    | .add a b => s!"Add({a},{b})"
    | .sub a b => s!"Sub({a},{b})"
    | .mul a b => s!"Mul({a},{b})"
    | .u8Xor a b => s!"U8Xor({a},{b})"
    | .u8XorSplit7 a b => s!"U8XorSplit7({a},{b})"
    | .u8XorSplit4 a b => s!"U8XorSplit4({a},{b})"
    | .u8RangeCheck a b => s!"U8RangeCheck({a},{b})"
    | .u32ToField a => s!"U32ToField({vec a})"
    | .unconstrainedU32Add a b => s!"UnconstrainedU32Add({vec a},{vec b})"
    | .unconstrainedU32Add3 a b c => s!"UnconstrainedU32Add3({vec a},{vec b},{vec c})"
    | .assertEq a b msg => s!"AssertEq({vec a},{vec b},{msg.map (fun m => "Some(" ++ (Lean.Json.str m).compress ++ ".into())") |>.getD "None"})"
    | .call _ a n unc => s!"Call(fun_idx,{vec a},{n},{unc})"
    | _ => panic! s!"unsupported op {repr o}"
  return "Op::" ++ s

partial def block (b : Block) : String :=
  "Block { ops: vec![" ++ String.intercalate ",\n" (b.ops.toList.map op) ++ "], ctrl: " ++
  (match b.ctrl with
  | .return sel vals => s!"Ctrl::Return({sel},{vec vals})"
  | .match v cases d =>
    s!"Ctrl::Match({v}, FxIndexMap::from_iter([" ++
    String.intercalate "," (cases.toList.map fun (g,b) => s!"(G::from_u64({g.val.toNat})," ++ block b ++ ")") ++
    " ])," ++ (d.map (fun b => "Some(Box::new(" ++ block b ++ "))") |>.getD "None") ++ ")"
  | _ => panic! "unsupported ctrl") ++ "}"

def exportBody (source : Except Aiur.Global Aiur.Source.Toplevel)
    (groups : Array (String × Array String)) : IO String := do
  let .ok top := source | throw (IO.userError "source")
  let .ok compiled := top.compileWithGroups groups | throw (IO.userError "compile")
  let some c := compiled.bytecode.circuits.find? (·.name == "blake3_compress") | throw (IO.userError "circuit")
  if c.members.size != 1 then throw (IO.userError "grouped blake3")
  let f := compiled.bytecode.functions[c.members[0]!]!
  IO.eprintln s!"blake3 layout: {repr f.layout}"
  return block f.body

def main (arguments : List String) : IO Unit := do
  let ix := ← exportBody IxVM.ixVM IxVM.functionGroups
  let aggr := ← exportBody Aggr.ixAggr Aggr.functionGroups
  if ix != aggr then throw (IO.userError "IxVM and aggregation bytecode differ")
  let path := arguments.head?.getD "crates/aiur/src/gpu_trace/blake3_body.rs"
  IO.FS.writeFile path (
    "// Exact bytecode contract for cuda/blake3_trace.cu. The self-call index\n" ++
    "// varies between compiled systems; every other operation and operand must match.\n" ++
    "use crate::{G, FxIndexMap, bytecode::{Block, Ctrl, Op}};\n" ++
    "use multi_stark::p3_field::PrimeCharacteristicRing;\n" ++
    "pub(super) fn body(fun_idx: usize) -> Block {\n" ++ ix ++ "\n}\n")
