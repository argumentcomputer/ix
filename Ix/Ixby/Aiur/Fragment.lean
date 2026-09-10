module
public import Ix.Ixby

/-! Admission for the experimental fixed-profile constrained backend slices:
straight-line scalars, scalar CEK control, and immutable constructors. Each is
a strict subset of crypto semantic revision 0, not a replacement execution
semantics. Unsupported code must also be rejected inside each circuit. -/

public section
@[expose] section

namespace Ix.Ixby.AiurBackend

/-- Experimental local proving capacities, not production security policy.
The circuit's constants and profile digest are derived from this definition.
Changing them changes the interpreter key, independently of guest code. -/
def profile : Profile := {
  limits := {
    functions := 1, constructors := 0, blocks := 64, locals := 64,
    operands := 16, continuations := 0, inputNodes := 16, natBits := 0,
    stringBytes := 0, byteArrayBytes := 0 },
  programBytes := 4096, valueBytes := 1024, valueDepth := 1, maxSteps := 65 }

def scalarSupported : Scalar → Bool
  | .bool _ | .word32 _ | .field _ | .extField _ => true
  | _ => false

def valueSupported : Value → Bool
  | .scalar scalar => scalarSupported scalar
  | .erased => true
  | _ => false

def operandSupported : Operand → Bool
  | .literal scalar => scalarSupported scalar
  | _ => true

def primitiveSupported : Primitive → Bool
  | .word32Add | .word32And | .word32Or | .word32Xor | .word32Eq | .word32Lt
  | .word32ToField | .fieldAdd | .fieldSub | .fieldMul | .fieldInverse | .fieldEq
  | .extAdd | .extSub | .extMul | .extInverse | .extEq | .extPack | .extFst | .extSnd => true
  | _ => false

def opSupported : Op → Bool
  | .copy value => operandSupported value
  | .primitive primitive args => primitiveSupported primitive && args.all operandSupported
  | _ => false

/-- Host convenience check only. Proof verification must not trust this check
or an independently supplied execution transcript in place of circuit checks. -/
def validateFragment (program : Program) : Except String Unit := do
  profile.validateProgram program |>.mapError (fun e => s!"profile: {repr e}")
  unless program.entry == 0 && program.constructors.isEmpty && program.functions.size == 1 do
    throw "scalar slice requires one entry-zero function and no constructors"
  let function := program.functions[0]!
  unless function.entry == 0 && function.blocks.size + 1 ≤ profile.maxSteps do
    throw "scalar slice requires block-zero entry and bounded terminal execution"
  for h : i in [:function.blocks.size] do
    let block := function.blocks[i]
    unless block.locals == function.arity + i do throw "nonsequential local frame"
    match block.instruction with
    | .letOp op next =>
      unless i + 1 < function.blocks.size && next == i + 1 && opSupported op do
        throw "unsupported operation or nonsequential successor"
    | .ret value =>
      unless i + 1 == function.blocks.size && operandSupported value do
        throw "return must be the final block with a supported operand"
    | _ => throw "unsupported control instruction"

/-- The control-flow slice keeps the scalar vocabulary but admits multiple
functions, arbitrary valid block layout, and a bounded explicit return stack.
This is another experimental profile/key, not a wire or semantic revision. -/
def controlProfile : Profile := {
  limits := {
    functions := 8, constructors := 0, blocks := 64, locals := 64,
    operands := 16, continuations := 16, inputNodes := 16, natBits := 0,
    stringBytes := 0, byteArrayBytes := 0 },
  programBytes := 16384, valueBytes := 1024, valueDepth := 1, maxSteps := 256 }

def controlOpSupported : Op → Bool
  | .call _ args | .callSelf args => args.all operandSupported
  | op => opSupported op

def controlInstrSupported : Instr → Bool
  | .letOp op _ => controlOpSupported op
  | .ret value | .branch value _ _ => operandSupported value
  | .tailCall _ args | .tailCallSelf args => args.all operandSupported
  | _ => false

/-- Convenience admission only: the control circuit checks the complete image
itself, including unsupported instructions and bad references in dead code. -/
def validateControlFragment (program : Program) : Except String Unit := do
  controlProfile.validateProgram program |>.mapError (fun e => s!"profile: {repr e}")
  unless program.constructors.isEmpty && program.functions.all (fun function =>
      function.blocks.all (fun block => controlInstrSupported block.instruction)) do
    throw "unsupported control-slice code"

/-- Immutable constructors extend the control slice without changing crypto
v0 semantics. I/O bounds do not bound temporary values during execution. -/
def objectsProfile : Profile := {
  limits := {
    functions := 8, constructors := 16, blocks := 64, locals := 64,
    operands := 16, continuations := 16, inputNodes := 128, natBits := 0,
    stringBytes := 0, byteArrayBytes := 0 },
  programBytes := 16384, valueBytes := 8192, valueDepth := 32, maxSteps := 256 }

def objectsOpSupported : Op → Bool
  | .construct _ args => args.all operandSupported
  | .project value _ => operandSupported value
  | op => controlOpSupported op

def objectsInstrSupported : Instr → Bool
  | .letOp op _ => objectsOpSupported op
  | .caseCtor value _ => operandSupported value
  | instr => controlInstrSupported instr

def validateObjectsFragment (program : Program) : Except String Unit := do
  objectsProfile.validateProgram program |>.mapError (fun e => s!"profile: {repr e}")
  unless program.functions.all (fun function =>
      function.blocks.all (fun block => objectsInstrSupported block.instruction)) do
    throw "unsupported object-slice code"

end Ix.Ixby.AiurBackend
