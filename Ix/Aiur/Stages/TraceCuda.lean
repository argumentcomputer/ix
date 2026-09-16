module

public import Ix.Aiur.Stages.TracePlan
public import Ix.Aiur.Stages.TraceContract

public section

namespace Aiur.TraceCuda

open Bytecode TracePlan

private def literal (n : Nat) : String := s!"{n}ULL"
private def valueName (id : ValueId) : String := s!"v_{id}"
private def call (name : String) (args : Array String) : String :=
  name ++ "(" ++ ", ".intercalate args.toList ++ ")"
private def line (depth : Nat) (text : String) : String :=
  String.ofList (List.replicate (2*depth) ' ') ++ text ++ "\n"
private def column (region : String) (index : Nat) (value : String) : String :=
  s!"row[layout.{region} + {index}] = {value};"

private structure Emission where
  counter : Nat := 0
  tables : Array String := #[]

private abbrev EmitM := StateT Emission (Except String)

private def fresh (stem : String) : EmitM String := do
  let n := (← get).counter
  modify fun state => { state with counter := n+1 }
  pure s!"{stem}_{n}"

private def emitOperation (operation : Operation) (depth : Nat) : Except String String := do
  let args := operation.inputs.map valueName
  let a := args[0]?.getD "0ULL"
  let b := args[1]?.getD "0ULL"
  let temp := s!"op_{operation.index}"
  let mut source := ""
  let mut auxiliary : Option (Array String) := none
  let outputs ← match operation.externalRead with
    | some read => pure ((Array.range read.seed.size).map fun i => s!"seed.word({read.seed.start+i})")
    | none =>
      match operation.opcode with
      | .const g => pure #[literal g.n]
      | .add .. => pure #[call "goldilocks_add" #[a, b]]
      | .sub .. => pure #[call "goldilocks_sub" #[a, b]]
      | .mul .. => pure #[call "goldilocks_mul" #[a, b]]
      | .eqZero .. =>
        if operation.auxiliaries.size != 0 then
          auxiliary := some #[s!"inverse({a})", valueName operation.outputs[0]!]
        pure #[s!"uint64_t({a} == 0)"]
      | .unconstrainedGInverse .. => pure #[s!"inverse({a})"]
      | .unconstrainedGToBytes .. =>
        pure ((Array.range 8).map fun i => s!"(({a} >> {8*i}) & 255ULL)")
      | .u8BitDecomposition .. =>
        pure ((Array.range 8).map fun i => s!"(({a} >> {i}) & 1ULL)")
      | .u8ShiftLeft .. => pure #[s!"(({a} << 1) & 255ULL)"]
      | .u8ShiftRight .. => pure #[s!"({a} >> 1)"]
      | .u8Xor .. | .u8Add .. | .u8Sub .. | .u8Mul .. | .u8And ..
      | .u8Or .. | .u8LessThan .. | .u8XorSplit4 .. | .u8XorSplit7 .. =>
        source := source ++ line depth s!"if ({a} > 255 || {b} > 255) return 1;"
        match operation.opcode with
        | .u8Xor .. => pure #[s!"({a} ^ {b})"]
        | .u8And .. => pure #[s!"({a} & {b})"]
        | .u8Or .. => pure #[s!"({a} | {b})"]
        | .u8LessThan .. => pure #[s!"uint64_t({a} < {b})"]
        | .u8Add .. => pure #[s!"(({a} + {b}) & 255ULL)", s!"(({a} + {b}) >> 8)"]
        | .u8Sub .. => pure #[s!"(({a} - {b}) & 255ULL)", s!"uint64_t({a} < {b})"]
        | .u8Mul .. => pure #[s!"(({a} * {b}) & 255ULL)", s!"(({a} * {b}) >> 8)"]
        | .u8XorSplit4 .. => pure #[s!"(({a} ^ {b}) >> 4)", s!"((({a} ^ {b}) << 4) & 255ULL)"]
        | _ => pure #[s!"(({a} ^ {b}) >> 7)", s!"((({a} ^ {b}) << 1) & 255ULL)"]
      | .u32LessThan .. =>
        source := source ++ line depth s!"if ({a} > 0xffffffffULL || {b} > 0xffffffffULL) return 3;"
        source := source ++ line depth s!"const uint32_t {temp} = uint32_t({b}) - uint32_t({a}) - 1U;"
        auxiliary := some ((#[a, s!"uint64_t({temp})", b]).flatMap fun word =>
          (Array.range 4).map fun i => s!"(({word} >> {8*i}) & 255ULL)")
        pure #[s!"uint64_t({a} < {b})"]
      | .unconstrainedU32Add .. | .unconstrainedU32Add3 .. =>
        let words := (Array.range (args.size / 4)).map fun i => call "word" (args.extract (4*i) (4*i+4))
        source := source ++ line depth s!"const WordSum {temp} = {call "add_words" words};"
        pure (((Array.range 4).map fun i => s!"(({temp}.low >> {8*i}) & 255ULL)").push s!"{temp}.carry")
      | .u32ToField .. => pure #[call "canonicalize" #[call "word" args]]
      | .assertEq .. | .ioSetInfo .. | .ioWrite .. | .debug .. | .u8RangeCheck .. => pure #[]
      | .call .. | .load .. | .ioRead .. =>
        if operation.outputs.isEmpty then pure #[] else throw "missing CUDA external read"
      | .store .. | .ioGetInfo .. | .unconstrainedBigUintDivMod .. => throw "missing CUDA external read"
  unless outputs.size == operation.outputs.size do throw "CUDA logical output count differs from plan"
  for i in [:outputs.size] do
    source := source ++ line depth s!"const uint64_t {valueName operation.outputs[i]!} = {outputs[i]!};"
  let columns := auxiliary.getD ((operation.outputs.extract 0 operation.auxiliaries.size).map valueName)
  unless columns.size == operation.auxiliaries.size do throw "CUDA auxiliary count differs from plan"
  for i in [:columns.size] do
    source := source ++ line depth (column "auxiliaries" (operation.auxiliaries.start+i) columns[i]!)
  pure source

private structure YieldTarget where
  label : String
  merges : Array ValueId

mutual
  private partial def emitBlock (plan : FunctionPlan) (block : BlockPlan)
      (target : Option YieldTarget) (depth : Nat) : EmitM String := do
    let mut source := ""
    for index in block.operations do
      if plan.rowOperations.contains index then
        let some operation := plan.operations[index]? | throw "missing CUDA operation"
        source := source ++ (← emitOperation operation depth)
    pure (source ++ (← emitControl plan block.control target depth))

  private partial def emitArms (plan : FunctionPlan) (discriminant : ValueId)
      (arms : Array (G × BlockPlan)) (fallback : Option BlockPlan) (inverses : Span)
      (target : Option YieldTarget) (depth : Nat) : EmitM String := do
    let d := valueName discriminant
    let mut source := line depth (s!"switch ({d}) " ++ "{")
    for (value, block) in arms do
      source := source ++ line (depth+1) (s!"case {literal value.n}: " ++ "{")
      source := source ++ (← emitBlock plan block target (depth+2))
      source := source ++ line (depth+1) "}"
    source := source ++ line (depth+1) "default: {"
    match fallback with
    | none => source := source ++ line (depth+2) "return 2;"
    | some block =>
      let maximum := arms.foldl (fun maximum (g, _) => max maximum g.n) 0
      for ((value, _), i) in arms.zipIdx do
        let generic := s!"inverse(goldilocks_sub({d}, {literal value.n}))"
        let expression ← if maximum < 16 then do
          let table ← fresh s!"inverse_{plan.index}"
          let items := (Array.range (maximum+1)).map fun n => literal ((G.ofNat n - value).inverse.n)
          let declaration := s!"__device__ __constant__ uint64_t {table}[] = " ++
            "{" ++ ", ".intercalate items.toList ++ "};\n"
          modify fun state => { state with tables := state.tables.push declaration }
          pure s!"({d} <= {literal maximum} ? {table}[{d}] : {generic})"
        else pure generic
        source := source ++ line (depth+2) (column "auxiliaries" (inverses.start+i) expression)
      source := source ++ (← emitBlock plan block target (depth+2))
    pure (source ++ line (depth+1) "}" ++ line depth "}")

  private partial def emitControl (plan : FunctionPlan) (control : Control)
      (target : Option YieldTarget) (depth : Nat) : EmitM String := do
    match control with
    | .returnRow selector _ =>
      pure (line depth (column "selectors" selector "1") ++ line depth "return 0;")
    | .yieldRow selector values =>
      let some target := target | throw "CUDA yield has no continuation"
      let mut source := line depth (column "selectors" selector "1")
      for i in [:values.size] do
        source := source ++ line depth s!"{valueName target.merges[i]!} = {valueName values[i]!};"
      pure (source ++ line depth s!"goto {target.label};")
    | .branch discriminant arms fallback inverses _ =>
      emitArms plan discriminant arms fallback inverses target depth
    | .continueWith discriminant arms fallback inverses _ merges columns continuation =>
      let label ← fresh "continuation"
      let mut source := ""
      for id in merges do source := source ++ line depth s!"uint64_t {valueName id};"
      source := source ++ (← emitArms plan discriminant arms fallback inverses (some ⟨label, merges⟩) depth)
      source := source ++ line depth s!"{label}:;"
      for i in [:merges.size] do
        source := source ++ line depth (column "auxiliaries" (columns.start+i) (valueName merges[i]!))
      pure (source ++ (← emitBlock plan continuation target depth))
end

private def emitFunction (plan : FunctionPlan) (unit : String) : Except String String := do
  let name := s!"{unit}_{plan.index}"
  let (body, state) ← (emitBlock plan plan.body none 1).run {}
  let mut source := "".intercalate state.tables.toList
  source := source ++ s!"template<bool Packed> __device__ __forceinline__ uint32_t row_{name}(Seed<Packed> seed, Layout layout, uint64_t* row) " ++ "{\n"
  for i in [:plan.layout.inputSize] do
    source := source ++ line 1 s!"const uint64_t v_{i} = seed.word({i+1});"
    source := source ++ line 1 s!"row[{i}] = v_{i};"
  source := source ++ body ++ "}\n"
  source := source ++ s!"template<bool Packed> __global__ void kernel_{name}(const uint8_t* __restrict__ seeds, size_t real, size_t rows, Layout layout, uint64_t* __restrict__ output, uint32_t* error) " ++ "{\n" ++
    "  const size_t r = size_t(blockIdx.x) * blockDim.x + threadIdx.x;\n" ++
    "  if (r >= rows) return;\n" ++
    "  uint64_t* row = output + r * layout.width;\n" ++
    "  for (size_t col = 0; col < layout.width; ++col) row[col] = 0;\n" ++
    "  if (r >= real) return;\n" ++
    s!"  constexpr size_t stride = Packed ? {plan.guardedU8SeedBytes} : {plan.canonicalSeedBytes};\n" ++
    "  const Seed<Packed> seed{seeds + r * stride};\n" ++
    "  row[layout.auxiliaries] = seed.word(0);\n" ++
    s!"  const uint32_t status = row_{name}(seed, layout, row);\n" ++
    "  if (status) atomicCAS(error, 0U, status);\n}\n"
  source := source ++ s!"cudaError_t launch_{name}(const uint8_t* seeds, uint32_t encoding, size_t real, size_t rows, Layout layout, uint64_t* output, uint32_t* error) " ++ "{\n" ++
    s!"  if (encoding == 1) kernel_{name}<true><<<unsigned((rows+127)/128), 128, 0, cudaStreamPerThread>>>(seeds, real, rows, layout, output, error);\n" ++
    s!"  else kernel_{name}<false><<<unsigned((rows+127)/128), 128, 0, cudaStreamPerThread>>>(seeds, real, rows, layout, output, error);\n" ++
    "  return cudaGetLastError();\n}\n"
  source := source ++ s!"extern \"C\" int aiur_trace_{name}(int device, const uint8_t* seeds, uint32_t encoding, size_t real, size_t rows, size_t width, size_t selectors, size_t auxiliaries, uint64_t* output) " ++ "{\n" ++
    s!"  if (selectors < {plan.layout.inputSize} || auxiliaries < selectors || auxiliaries - selectors < {plan.layout.selectors} || width < auxiliaries || width - auxiliaries < {plan.layout.auxiliaries}) return int(cudaErrorInvalidValue);\n" ++
    s!"  return upload(device, seeds, encoding, {plan.seedWords}, real, rows, " ++ "{width, selectors, auxiliaries}, " ++ s!"output, launch_{name});\n" ++ "}\n\n"
  pure source

def validUnit (unit : String) : Bool :=
  !unit.isEmpty && unit.toList.all (fun c => c.isAlphanum && c.toNat < 128 || c == '_') &&
    !(unit.toList.head!).isDigit

def emit (top : Toplevel) (unit : String) (selected : Option (Array FunIdx) := none) : Except String String := do
  unless validUnit unit do throw "CUDA unit must be an ASCII identifier"
  let plan ← TracePlan.program top
  if let some indices := selected then
    let mut seen := #[]
    for index in indices do
      unless (plan.functions[index]?).join.isSome do
        throw s!"function {index} has no constrained trace writer"
      if seen.contains index then throw s!"duplicate CUDA function {index}"
      seen := seen.push index
  let mut source := "// Generated by Aiur.TraceCuda; regenerate from Aiur bytecode.\n" ++
    "#include \"trace_primitives.cuh\"\nstatic_assert(aiur_trace::ABI_VERSION == 1, \"trace writer ABI mismatch\");\n" ++ s!"namespace trace_{unit} " ++ "{\nusing namespace aiur_trace;\n\n"
  for entry in plan.functions do
    if let some function := entry then
      if (selected.map (·.contains function.index)).getD true then
        source := source ++ (← emitFunction function unit)
  pure (source ++ s!"extern \"C\" const uint8_t* aiur_trace_{unit}_contract() " ++ "{\n" ++
    "  static const uint8_t hash[32] = {" ++ TraceContract.fingerprintLiteral top ++ "};\n  return hash;\n}\n}\n")

/-- Rust registration for the CUDA unit; absent entries remain explicit. -/
def registry (top : Toplevel) (unit : String) (cratePath : String := "aiur")
    (selected : Option (Array FunIdx) := none) : Except String String := do
  unless validUnit unit do throw "CUDA unit must be an ASCII identifier"
  let plan ← TracePlan.program top
  if let some indices := selected then
    let mut seen := #[]
    for index in indices do
      unless (plan.functions[index]?).join.isSome do
        throw s!"function {index} has no constrained trace writer"
      if seen.contains index then throw s!"duplicate CUDA function {index}"
      seen := seen.push index
  let mut source := "// Generated by Aiur.TraceCuda; regenerate from Aiur bytecode.\n" ++
    s!"use {cratePath}::trace_codegen::cuda::CudaLibrary;\nunsafe extern \"C\" " ++ "{\n" ++
    s!"  fn aiur_trace_{unit}_contract() -> *const u8;\n"
  let mut entries := #[]
  let mut words := #[]
  for entry in plan.functions do
    words := words.push (toString ((entry.map (·.seedWords)).getD 0))
    match entry with
    | some f =>
      if (selected.map (·.contains f.index)).getD true then
        let name := s!"aiur_trace_{unit}_{f.index}"
        source := source ++ s!"  pub(super) fn {name}(device: i32, seeds: *const u8, encoding: u32, real: usize, rows: usize, width: usize, selectors: usize, auxiliaries: usize, output: *mut u64) -> i32;\n"
        entries := entries.push s!"Some({name})"
      else entries := entries.push "None"
    | none => entries := entries.push "None"
  pure (source ++ "}\n" ++
    "pub static CUDA: CudaLibrary = unsafe { CudaLibrary::new([" ++ TraceContract.fingerprintLiteral top ++
    s!"], aiur_trace_{unit}_contract, &[\n" ++ ",\n".intercalate entries.toList ++ "\n], &[" ++ ", ".intercalate words.toList ++ "]) };\n")

end Aiur.TraceCuda

end
