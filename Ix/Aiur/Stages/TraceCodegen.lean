module

public import Ix.Aiur.Stages.Codegen
public import Ix.Aiur.Stages.TracePlan
public import Ix.Aiur.Stages.TraceContract

public section

namespace Aiur.TraceCodegen

open Bytecode TracePlan Codegen

private inductive Mode where
  | row | pack | packed | checked
  deriving BEq

private def number (n : Nat) : RustExpr := .lit (toString n)
private def valueExpr (id : ValueId) : RustExpr := .var s!"v_{id}"
private def call (name : String) (args : Array RustExpr) : RustExpr := .call (.var name) args
private def method (value : RustExpr) (name : String) (args : Array RustExpr := #[]) : RustExpr :=
  .call (.field value name) args
private def canonical (value : RustExpr) : RustExpr := method value "as_canonical_u64"
private def indexExpr (name : String) (index : Nat) : RustExpr := .index (.var name) (number index)
private def declaration (name : String) (value : RustExpr) : RustStmt := .letStmt false name none value
private def values (ids : Array ValueId) : RustExpr := .arrayLit (ids.map valueExpr)
private def ok : RustStmt := .returnStmt (call "Ok" #[.lit "()"])

private def Mode.operations (mode : Mode) (plan : FunctionPlan) : Array Nat :=
  match mode with
  | .row => plan.rowOperations
  | .pack | .packed => plan.preparationOperations
  | .checked => plan.aliasCheckOperations

private def Mode.values (mode : Mode) (plan : FunctionPlan) : Array ValueId :=
  match mode with
  | .row => plan.rowValues
  | .pack | .packed => plan.preparationValues
  | .checked => plan.aliasCheckValues

private def rowWrite (region : String) (index : Nat) (value : RustExpr) : RustStmt :=
  .assign (.index (.var "row") (.binop "+" (.field (.var "offsets") region) (number index)))
    (canonical value)

private def readExpression (mode : Mode) (op : Operation) (read : ExternalRead) : RustExpr :=
  let args := op.inputs.map valueExpr
  let site := number op.index
  let name := fun (s : String) => s!"context.{s}::<{op.outputs.size}>"
  .tryExpr <| match read.kind with
  | .callResult callee => call (name "call") #[site, number callee, .ref (.arrayLit args)]
  | .returnedCall callee =>
    if mode == .checked then
      call (name "check_returned") #[site, number callee, .ref (.arrayLit args)]
    else call (name "returned") #[site]
  | .storePointer _ => call "context.store" #[site, .ref (.arrayLit args)]
  | .loadValues _ => call (name "load") #[site, args[0]!]
  | .ioInfo => call "context.io_info" #[site, args[0]!, .ref (.arrayLit (args.extract 1 args.size))]
  | .ioValues _ => call (name "io_read") #[site, args[0]!, args[1]!]
  | .bigUintResults => call "context.big_uint" #[site, args[0]!, args[1]!]

private def emitOperation (mode : Mode) (op : Operation) : Except String (Array RustStmt) := do
  let inputs := op.inputs.map valueExpr
  let a := inputs[0]?.getD gZero
  let b := inputs[1]?.getD gZero
  let unary := fun name => call name #[.ref a]
  let binary := fun name => call name #[.ref a, .ref b]
  let single := fun value => RustExpr.arrayLit #[value]
  let temp := s!"op_{op.index}"
  let mut stmts := #[]
  let mut auxiliary : Option (Array RustExpr) := none
  let expression ← match op.externalRead with
    | some read =>
      if mode == .row then
        pure (.arrayLit ((Array.range read.seed.size).map fun i =>
          call "G::from_u64" #[indexExpr "seed" (read.seed.start + i)]))
      else pure (readExpression mode op read)
    | none =>
      match op.opcode with
      | .const value => pure (single (gFromU64 value.n))
      | .add .. => pure (single (.binop "+" a b))
      | .sub .. => pure (single (.binop "-" a b))
      | .mul .. => pure (single (.binop "*" a b))
      | .eqZero .. =>
        if op.auxiliaries.size != 0 then
          auxiliary := some #[call "g_inverse_value" #[a], valueExpr op.outputs[0]!]
        pure (single (gFromBool (method a "is_zero")))
      | .unconstrainedGInverse .. => pure (single (call "g_inverse_value" #[a]))
      | .unconstrainedGToBytes .. =>
        pure (method (method (canonical a) "to_le_bytes") "map" #[.var "G::from_u8"])
      | .u8BitDecomposition .. =>
        pure (.arrayLit ((Array.range 8).map fun i => gFromBool
          (.binop "!=" (.binop "&" (.binop ">>" (canonical a) (number i)) (number 1)) (number 0))))
      | .u8ShiftLeft .. => pure (single (unary "Bytes1::shift_left"))
      | .u8ShiftRight .. => pure (single (unary "Bytes1::shift_right"))
      | .u8Xor .. => pure (single (binary "Bytes2::xor"))
      | .u8And .. => pure (single (binary "Bytes2::and"))
      | .u8Or .. => pure (single (binary "Bytes2::or"))
      | .u8LessThan .. => pure (single (binary "Bytes2::less_than"))
      | .u8Add .. | .u8Sub .. | .u8Mul .. | .u8XorSplit4 .. | .u8XorSplit7 .. =>
        let name := match op.opcode with
          | .u8Add .. => "add" | .u8Sub .. => "sub" | .u8Mul .. => "mul"
          | .u8XorSplit4 .. => "xor_split4" | _ => "xor_split7"
        stmts := stmts.push (declaration temp (binary s!"Bytes2::{name}"))
        pure (.arrayLit #[.field (.var temp) "0", .field (.var temp) "1"])
      | .u32LessThan .. =>
        stmts := stmts.push (declaration temp (call "u32_less_than" #[a, b]))
        auxiliary := some ((Array.range 12).map fun i => .index (.field (.var temp) "1") (number i))
        pure (single (.field (.var temp) "0"))
      | .unconstrainedU32Add .. | .unconstrainedU32Add3 .. =>
        let words := (Array.range (inputs.size / 4)).map fun i =>
          call "u32_word" #[.arrayLit (inputs.extract (4*i) (4*i+4))]
        pure (call "u32_add" #[.ref (.arrayLit words)])
      | .u32ToField .. => pure (single (call "G::from_u64" #[call "u32_word" #[.arrayLit inputs]]))
      | .assertEq .. | .ioSetInfo .. | .ioWrite .. | .debug .. | .u8RangeCheck .. =>
        pure (.arrayLit #[])
      | .call .. | .load .. | .ioRead .. =>
        if op.outputs.isEmpty then pure (.arrayLit #[])
        else throw s!"operation {op.index}: missing external read"
      | .store .. | .ioGetInfo .. | .unconstrainedBigUintDivMod .. =>
        throw s!"operation {op.index}: missing external read"
  if !op.outputs.isEmpty then
    let names := ", ".intercalate (op.outputs.toList.map fun id => s!"v_{id}")
    stmts := stmts.push (.letStmt false s!"[{names}]" (some s!"[G; {op.outputs.size}]") expression)
  if mode == .row then
    let columns := auxiliary.getD ((op.outputs.extract 0 op.auxiliaries.size).map valueExpr)
    unless columns.size == op.auxiliaries.size do
      throw s!"operation {op.index}: scalar writer auxiliary count differs from plan"
    for i in [:columns.size] do
      stmts := stmts.push (rowWrite "auxiliaries" (op.auxiliaries.start + i) columns[i]!)
  else if let some read := op.externalRead then
    for i in [:op.outputs.size] do
      if mode == .packed then
        stmts := stmts.push (.exprStmt (call "seed.set" #[number (read.seed.start + i), valueExpr op.outputs[i]!]))
      else
        stmts := stmts.push (.assign (indexExpr "seed" (read.seed.start + i)) (canonical (valueExpr op.outputs[i]!)))
  pure stmts

private structure YieldTarget where
  label : String
  indices : Array Nat

mutual
  private partial def emitBlock (plan : FunctionPlan) (mode : Mode) (block : BlockPlan)
      (target : Option YieldTarget) (depth : Nat) : Except String (Array RustStmt) := do
    let mut result := #[]
    for index in block.operations do
      if (mode.operations plan).contains index then
        let some operation := plan.operations[index]? | throw "missing planned operation"
        result := result ++ (← emitOperation mode operation)
    pure (result ++ (← emitControl plan mode block.control target depth))

  private partial def emitArms (plan : FunctionPlan) (mode : Mode) (discriminant : ValueId)
      (arms : Array (G × BlockPlan)) (fallback : Option BlockPlan) (inverses : Span)
      (target : Option YieldTarget) (depth : Nat) : Except String RustStmt := do
    let mut result := #[]
    for (value, block) in arms do
      result := result.push {
        pat := .litU64 value.n
        body := ← emitBlock plan mode block target depth }
    let defaultBody ← match fallback with
      | none => pure #[.returnStmt (call "Err" #[call "no_match" #[number plan.index, valueExpr discriminant]])]
      | some block => do
        let mut writes := #[]
        if mode == .row then
          for ((value, _), i) in arms.zipIdx do
            let difference := RustExpr.binop "-" (valueExpr discriminant) (gFromU64 value.n)
            writes := writes.push (rowWrite "auxiliaries" (inverses.start + i) (method difference "inverse"))
        pure (writes ++ (← emitBlock plan mode block target depth))
    result := result.push { pat := .wildcard, body := defaultBody }
    pure (.matchStmt (canonical (valueExpr discriminant)) result)

  private partial def emitControl (plan : FunctionPlan) (mode : Mode) (control : Control)
      (target : Option YieldTarget) (depth : Nat) : Except String (Array RustStmt) := do
    let selector := fun index => if mode == .row then #[rowWrite "selectors" index gOne] else #[]
    match control with
    | .returnRow index _ => pure (selector index |>.push ok)
    | .yieldRow index ids =>
      let some target := target | throw "yield has no scalar continuation"
      pure (selector index |>.push (.breakWith target.label (.arrayLit (target.indices.map fun i => valueExpr ids[i]!))))
    | .branch discriminant arms fallback inverses _ =>
      if mode != .row && !(mode.values plan).contains discriminant then return #[ok]
      pure #[← emitArms plan mode discriminant arms fallback inverses target depth]
    | .continueWith discriminant arms fallback inverses _ merges columns continuation =>
      if mode != .row && !(mode.values plan).contains discriminant then return #[ok]
      let indices := (Array.range merges.size).filter fun i => mode == .row || (mode.values plan).contains merges[i]!
      let label := s!"yield_{depth}"
      let body ← emitArms plan mode discriminant arms fallback inverses (some ⟨label, indices⟩) (depth + 1)
      let names := ", ".intercalate (indices.toList.map fun i => s!"v_{merges[i]!}")
      let mut result := #[RustStmt.letStmt false s!"[{names}]" (some s!"[G; {indices.size}]") (.labeledBlock label #[body])]
      if mode == .row then
        for i in [:merges.size] do
          result := result.push (rowWrite "auxiliaries" (columns.start + i) (valueExpr merges[i]!))
      pure (result ++ (← emitBlock plan mode continuation target depth))
end

private def emitFunction (plan : FunctionPlan) (mode : Mode) : Except String String := do
  let mut body := #[]
  for i in [:plan.layout.inputSize] do
    let value := if mode == .row then call "G::from_u64" #[indexExpr "seed" (1+i)]
      else .index (.field (.var "context") "inputs") (number i)
    body := body.push (declaration s!"v_{i}" value)
  body := body ++ (← emitBlock plan mode plan.body none 0)
  let (name, params) := if mode == .row then
    (s!"write_{plan.index}", #[("seed", "&[u64]"), ("offsets", "RowOffsets"), ("row", "&mut [u64]")])
    else (s!"pack_{plan.index}" ++ (if mode == .checked then "_checked" else if mode == .packed then "_u8" else ""),
      #[("context", "&SeedContext<'_>"), ("seed", if mode == .packed then "&mut PackedSeed<'_>" else "&mut [u64]")])
  pure (RustItem.function name params "TraceResult<()>" body).toStr

private def vector (xs : Array String) : String := "vec![" ++ ", ".intercalate xs.toList ++ "]"
private def indices (xs : Array Nat) : String := vector (xs.map toString)
private def app (name : String) (args : Array String) : String := name ++ "(" ++ ", ".intercalate args.toList ++ ")"
private def quoted (s : String) : String := (repr s).pretty
private def stringOption (s : Option String) : String :=
  (s.map fun s => s!"Some({quoted s}.into())").getD "None"

private def bytecodeOp : Op → String
  | .const v => app "Op::Const" #[s!"G::from_u64({v.n})"]
  | .add a b => app "Op::Add" #[toString a, toString b]
  | .sub a b => app "Op::Sub" #[toString a, toString b]
  | .mul a b => app "Op::Mul" #[toString a, toString b]
  | .eqZero a => app "Op::EqZero" #[toString a]
  | .call f args size unc => app "Op::Call" #[toString f, indices args, toString size, toString unc]
  | .store args => app "Op::Store" #[indices args]
  | .load size a => app "Op::Load" #[toString size, toString a]
  | .assertEq a b msg => app "Op::AssertEq" #[indices a, indices b, stringOption msg]
  | .ioGetInfo c key => app "Op::IOGetInfo" #[toString c, indices key]
  | .ioSetInfo c key i n => app "Op::IOSetInfo" #[toString c, indices key, toString i, toString n]
  | .ioRead c i n => app "Op::IORead" #[toString c, toString i, toString n]
  | .ioWrite c args => app "Op::IOWrite" #[toString c, indices args]
  | .u8BitDecomposition a => app "Op::U8BitDecomposition" #[toString a]
  | .u8ShiftLeft a => app "Op::U8ShiftLeft" #[toString a]
  | .u8ShiftRight a => app "Op::U8ShiftRight" #[toString a]
  | .u8Xor a b => app "Op::U8Xor" #[toString a, toString b]
  | .u8Add a b => app "Op::U8Add" #[toString a, toString b]
  | .u8Sub a b => app "Op::U8Sub" #[toString a, toString b]
  | .u8Mul a b => app "Op::U8Mul" #[toString a, toString b]
  | .u8And a b => app "Op::U8And" #[toString a, toString b]
  | .u8Or a b => app "Op::U8Or" #[toString a, toString b]
  | .u8LessThan a b => app "Op::U8LessThan" #[toString a, toString b]
  | .u32LessThan a b => app "Op::U32LessThan" #[toString a, toString b]
  | .u8XorSplit7 a b => app "Op::U8XorSplit7" #[toString a, toString b]
  | .u8XorSplit4 a b => app "Op::U8XorSplit4" #[toString a, toString b]
  | .debug msg args => app "Op::Debug" #[s!"{quoted msg}.into()", (args.map fun a => s!"Some({indices a})").getD "None"]
  | .u8RangeCheck a b => app "Op::U8RangeCheck" #[toString a, toString b]
  | .unconstrainedBigUintDivMod a b => app "Op::UnconstrainedBigUintDivMod" #[toString a, toString b]
  | .unconstrainedGToBytes a => app "Op::UnconstrainedGToBytes" #[toString a]
  | .unconstrainedGInverse a => app "Op::UnconstrainedGInverse" #[toString a]
  | .unconstrainedU32Add a b => app "Op::UnconstrainedU32Add" #[indices a, indices b]
  | .unconstrainedU32Add3 a b c => app "Op::UnconstrainedU32Add3" #[indices a, indices b, indices c]
  | .u32ToField a => app "Op::U32ToField" #[indices a]

mutual
  private partial def bytecodeBlock (block : Bytecode.Block) : String :=
    "Block { ops: " ++ vector (block.ops.map bytecodeOp) ++ ", ctrl: " ++ bytecodeControl block.ctrl ++ " }"
  private partial def bytecodeArms (arms : Array (G × Bytecode.Block)) : String :=
    "[" ++ ", ".intercalate (arms.toList.map fun (v, b) =>
      s!"(G::from_u64({v.n}), {bytecodeBlock b})") ++ "].into_iter().collect()"
  private partial def bytecodeFallback (block : Option Bytecode.Block) : String :=
    (block.map fun block => s!"Some(Box::new({bytecodeBlock block}))").getD "None"
  private partial def bytecodeControl : Ctrl → String
    | .return s xs => app "Ctrl::Return" #[toString s, indices xs]
    | .yield s xs => app "Ctrl::Yield" #[toString s, indices xs]
    | .match d arms fallback => app "Ctrl::Match" #[toString d, bytecodeArms arms, bytecodeFallback fallback]
    | .matchContinue d arms fallback n aux lookup continuation => app "Ctrl::MatchContinue"
        #[toString d, bytecodeArms arms, bytecodeFallback fallback, toString n, toString aux,
          toString lookup, s!"Box::new({bytecodeBlock continuation})"]
end

private def layout (l : Bytecode.FunctionLayout) : String :=
  "FunctionLayout { " ++ s!"input_size: {l.inputSize}, selectors: {l.selectors}, auxiliaries: {l.auxiliaries}, lookups: {l.lookups}" ++ " }"

private def expected (top : Bytecode.Toplevel) : String :=
  -- Keep bytecode constructors separate so LLVM does not optimize the entire
  -- function library as one allocation-heavy function.
  let definitions := top.functions.zipIdx.map fun (f, index) =>
    s!"#[inline(never)]\nfn expected_function_{index}() -> Function " ++ "{\n" ++
      "  Function { body: " ++ bytecodeBlock f.body ++ ", layout: " ++ layout f.layout ++
      s!", entry: {f.entry}, constrained: {f.constrained}" ++ " }\n}\n"
  let functions := (Array.range top.functions.size).map fun index => s!"expected_function_{index}()"
  let circuits := top.circuits.map fun c =>
    "Circuit { members: " ++ indices c.members ++ ", layout: " ++ layout c.layout ++ " }"
  "\n".intercalate definitions.toList ++ "\nfn expected_program() -> Toplevel {\n  Toplevel { functions: " ++ vector functions ++
    ", memory_sizes: " ++ indices top.memorySizes ++ ", circuits: " ++ vector circuits ++ " }\n}\n"

/-- Scalar and seed writers share the planned SSA values and fixed column spans.
The complete expected bytecode guards runtime binding, including partial coverage. -/
def emit (top : Bytecode.Toplevel) (cratePath : String := "aiur")
    (selected : Option (Array FunIdx) := none) : Except String String := do
  let plan ← TracePlan.program top
  if let some indices := selected then
    for index in indices do
      unless (plan.functions[index]?.join).isSome do
        throw s!"function {index} is missing or unconstrained"
    unless indices.toList.eraseDups.length == indices.size do
      throw "duplicate selected function"
  let mut source := "// Generated by Aiur.TraceCodegen; regenerate from Aiur bytecode.\n" ++
    "#![allow(unused_imports, unused_variables, unused_parens, unreachable_code, unused_labels)]\n" ++
    s!"use {cratePath}::" ++ "{G, bytecode::{Toplevel, Function, FunctionLayout, Circuit, Block, Op, Ctrl},\n" ++
    "  execute::{g_inverse_value, CodegenBytes1 as Bytes1, CodegenBytes2 as Bytes2}, trace_codegen::*};\n" ++
    "use multi_stark::p3_field::{Field, PrimeCharacteristicRing, PrimeField64};\n\n"
  let mut descriptors := #[]
  for entry in plan.functions do
    match entry with
    | none => descriptors := descriptors.push "None"
    | some f =>
      if !(selected.map (·.contains f.index)).getD true then
        descriptors := descriptors.push "None"
        continue
      for mode in #[Mode.pack, .packed, .checked, .row] do source := source ++ (← emitFunction f mode) ++ "\n"
      descriptors := descriptors.push ("Some(FunctionWriter { layout: " ++ layout f.layout ++
        s!", output_size: {f.outputSize.getD 0}, seed_words: {f.seedWords}, pack: pack_{f.index}, pack_u8: pack_{f.index}_u8, " ++
        s!"pack_checked: pack_{f.index}_checked, write: write_{f.index}" ++ " })")
  source := source ++ expected top
  pure (source ++ "pub static PROGRAM: GeneratedProgram = GeneratedProgram { fingerprint: [" ++ TraceContract.fingerprintLiteral top ++ s!"], complete: {selected.isNone}, expected: expected_program, functions: &[\n" ++
    ",\n".intercalate descriptors.toList ++ "\n] };\n")

end Aiur.TraceCodegen

end
