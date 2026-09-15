module
public import Ix.Ixby.Primitive

/-! Whole-image and input admission for the functional reference machine.
Admission is structural and kernel-reducible; it does not prove termination,
source correctness, content addressing, or cryptographic execution soundness. -/

public section
@[expose] section

namespace Ix.Ixby

def Program.getFunction (program : Program) (id : FunctionId) : Except Error Function :=
  match program.functions[id]? with
  | some function => .ok function
  | none => .error (.invalidFunction id)

def Program.getConstructor (program : Program) (id : Constructor) : Except Error CtorDecl :=
  match program.constructors[id]? with
  | some ctor => .ok ctor
  | none => .error (.invalidConstructor id)

def Program.findConstructor (program : Program) (id : CtorId) : Option CtorDecl :=
  program.constructors.toList.find? (fun ctor => ctor.id == id)

def Operand.valid (limits : Limits) (locals : Nat) : Operand → Bool
  | .local slot => slot < locals
  | .literal value => match value.validate limits with
    | .ok _ => true
    | .error _ => false
  | .erased => true

def operandsValid (limits : Limits) (locals : Nat) (args : List Operand) : Bool :=
  args.length ≤ limits.operands && args.all (·.valid limits locals)

def Function.targetValid (function : Function) (target : BlockId) (locals : Nat) : Bool :=
  match function.blocks[target]? with
  | some block => block.locals == locals
  | none => false

def directCallValid (limits : Limits) (program : Program) (locals : Nat)
    (callee : FunctionId) (args : List Operand) : Bool :=
  operandsValid limits locals args &&
    match program.functions[callee]? with
    | some function => args.length == function.arity
    | none => false

def Op.valid (limits : Limits) (program : Program) (self : FunctionId) (locals : Nat) :
    Op → Bool
  | .copy value | .project value _ => value.valid limits locals
  | .primitive prim args =>
    operandsValid limits locals args && args.length == prim.arity
  | .construct ctor args =>
    operandsValid limits locals args &&
      match program.constructors[ctor]? with
      | some decl => args.length == decl.fields
      | none => false
  | .closure callee args =>
    operandsValid limits locals args &&
      match program.functions[callee]? with
      | some function => args.length < function.arity
      | none => false
  | .call callee args => directCallValid limits program locals callee args
  | .callSelf args => directCallValid limits program locals self args
  | .apply value args => value.valid limits locals && operandsValid limits locals args

/-- Constructor IDs are globally unique after admission, so rejecting repeated
table indices also rejects ambiguous cases for one semantic constructor. -/
def alternativesValid (program : Program) (function : Function) (locals : Nat) :
    List Constructor → List Alternative → Bool
  | _, [] => true
  | seen, alternative :: rest =>
    !seen.contains alternative.ctor &&
      (match program.constructors[alternative.ctor]? with
      | some ctor => function.targetValid alternative.target (locals + ctor.fields)
      | none => false) &&
      alternativesValid program function locals (alternative.ctor :: seen) rest

def Block.valid (limits : Limits) (program : Program) (self : FunctionId)
    (function : Function) (block : Block) : Bool :=
  block.locals ≤ limits.locals &&
    match block.instruction with
    | .letOp op next =>
      op.valid limits program self block.locals &&
        function.targetValid next (block.locals + 1)
    | .ret value => value.valid limits block.locals
    | .tailCall callee args => directCallValid limits program block.locals callee args
    | .tailCallSelf args => directCallValid limits program block.locals self args
    | .tailApply value args =>
      value.valid limits block.locals && operandsValid limits block.locals args
    | .caseCtor value alternatives =>
      value.valid limits block.locals && alternatives.length ≤ limits.constructors &&
        alternativesValid program function block.locals [] alternatives
    | .caseNat value ifZero ifSucc =>
      value.valid limits block.locals && function.targetValid ifZero block.locals &&
        function.targetValid ifSucc (block.locals + 1)
    | .branch value yes no =>
      value.valid limits block.locals && function.targetValid yes block.locals &&
        function.targetValid no block.locals

def validateConstructors (limits : Limits) : List CtorId → List CtorDecl → Except Error Unit
  | _, [] => .ok ()
  | seen, ctor :: rest => do
    if seen.contains ctor.id then throw (.duplicateConstructor ctor.id)
    if ctor.fields > limits.operands then throw (.limit .operands)
    validateConstructors limits (ctor.id :: seen) rest

def validateBlocks (limits : Limits) (program : Program) (self : FunctionId)
    (function : Function) : Nat → List Block → Except Error Unit
  | _, [] => .ok ()
  | index, block :: rest =>
    if block.valid limits program self function then
      validateBlocks limits program self function (index + 1) rest
    else .error (.invalidInstruction self index)

def validateFunctions (limits : Limits) (program : Program) :
    FunctionId → List Function → Except Error Unit
  | _, [] => .ok ()
  | self, function :: rest => do
    if function.arity > limits.operands then throw (.limit .operands)
    if function.arity > limits.locals then throw (.limit .locals)
    if function.blocks.size > limits.blocks then throw (.limit .blocks)
    unless function.targetValid function.entry function.arity do
      throw (.invalidBlock self function.entry)
    validateBlocks limits program self function 0 function.blocks.toList
    validateFunctions limits program (self + 1) rest

/-- Checks every function and block, including dead code and unused declarations.
Local-frame contracts make forward reads and inconsistent branch bindings
admission failures; semantic type errors remain checked at execution time. -/
def validateProgram (limits : Limits) (program : Program) : Except Error Unit := do
  if program.functions.size > limits.functions then throw (.limit .functions)
  if program.constructors.size > limits.constructors then throw (.limit .constructors)
  validateConstructors limits [] program.constructors.toList
  validateFunctions limits program 0 program.functions.toList
  let _ ← program.getFunction program.entry

/-- One shared node budget covers the entire input forest, including nested
constructor fields and PAP captures. Fuel cannot reset at every child. Values
are finite Lean objects; an eventual pointer codec must separately prove this
representation and exclude invalid cyclic witnesses. -/
def validateInputValues (limits : Limits) (program : Program) :
    Nat → List Value → Except Error Unit
  | _, [] => .ok ()
  | 0, _ :: _ => .error (.limit .inputNodes)
  | remaining + 1, value :: rest => do
    let children ← match value with
      | .scalar scalar => do
        scalar.validate limits
        pure #[]
      | .erased => pure #[]
      | .ctor id fields => do
        let some ctor := program.findConstructor id | throw .invalidValue
        if fields.size != ctor.fields then throw .invalidValue
        pure fields
      | .pap callee captured => do
        let function ← program.getFunction callee
        if captured.size ≥ function.arity then throw (.invalidClosure callee)
        pure captured
    validateInputValues limits program remaining (children.toList ++ rest)

end Ix.Ixby
