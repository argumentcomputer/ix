import Aiur.Circuit.Basic
import Aiur.Typecheck

namespace Aiur.Circuit

inductive CompileError where
  | invalidProgram (error : CheckError)
  | duplicatePattern (function : String)
  | tagCollision (enumName : String)
  | invalidShape
  deriving Repr, BEq

namespace Compiler

structure BuildState (F : Type) where
  nextVar : Nat := 0
  constraints : Array (Constraint F) := #[]
  sends : Array (Send F) := #[]
  memory : Array (MemoryLookup F) := #[]

abbrev Build (F : Type) := StateT (BuildState F) (Except CompileError)
abbrev Symbolic (F : Type) := WireValue (ArithExpr F)
abbrev Locals (F : Type) := List (String × Symbolic F)

theorem enumParts_denote [Field F] {count : Nat} {words payload : List (ArithExpr F)}
    {tag : ArithExpr F}
    (parts : Layout.enumParts count (.const 0) words = some (tag, payload)) (assignment : Var → F) :
    Layout.enumParts count (0 : F) (words.map (ArithExpr.denote assignment)) =
      some (tag.denote assignment, payload.map (ArithExpr.denote assignment)) := by
  simpa only [Scalar.Circuit.ArithExpr.denote, Nat.cast_zero] using
    Layout.enumParts_map_of (ArithExpr.denote assignment) parts

def fresh : Build F Var := do
  let state ← get
  set { state with nextVar := state.nextVar + 1 }
  return state.nextVar

def constrain (polynomial : ArithExpr F) : Build F Unit :=
  modify fun state => { state with constraints := state.constraints.push polynomial }

def guarded (enable polynomial : ArithExpr F) : Build F Unit := constrain (.mul enable polynomial)

def boolean [Field F] (selector : ArithExpr F) : Build F Unit :=
  constrain (.mul selector (.sub selector (.const 1)))

def requireCell (enable address : ArithExpr F) (value : Symbolic F) : Build F Unit :=
  modify fun state => { state with memory := state.memory.push ⟨address, value, enable⟩ }

def getLayout (decls : Declarations) (type : Ty) : Build F Layout :=
  liftM ((decls.layout type).mapError (CompileError.invalidProgram ∘ CheckError.invalidDeclarations))

def freshWords (count : Nat) : Build F (List Var) := do
  let state ← get
  set { state with nextVar := state.nextVar + count }
  return List.range' state.nextVar count

/-- An opaque result gets a variable for every column, including enum tags and padding. -/
def freshValue (decls : Declarations) (type : Ty) : Build F (WireValue Var) := do
  let layout ← getLayout decls type
  return ⟨type, ← freshWords layout.width⟩

def freshValues (decls : Declarations) (types : List Ty) : Build F (List (WireValue Var)) :=
  types.mapM (freshValue decls)

/-- Split a flat tuple/payload using its static types; no witness-dependent slicing occurs. -/
def splitValues (decls : Declarations) : List Ty → List α → Build F (List (WireValue α))
  | [], [] => pure []
  | type :: types, words => do
      let layout ← getLayout decls type
      if words.length < layout.width then throw .invalidShape
      return ⟨type, words.take layout.width⟩ ::
        (← splitValues decls types (words.drop layout.width))
  | [], _ :: _ => throw .invalidShape

/-- A zero test is exact in every field; inverses are auxiliary witnesses. -/
def equalIndicator [Field F] (difference : ArithExpr F) : Build F (ArithExpr F) := do
  let equal := ArithExpr.var (← fresh)
  let inverse := ArithExpr.var (← fresh)
  boolean equal
  constrain (.mul difference equal)
  constrain (.sub (.mul difference inverse) (.sub (.const 1) equal))
  return equal

def zeroWords (enable : ArithExpr F) : List (ArithExpr F) → Build F Unit
  | [] => pure ()
  | word :: words => do
      guarded enable word
      zeroWords enable words

mutual
  /-- Only the selected constructor's payload view is required to be canonical. -/
  def validate [Field F] : Layout → ArithExpr F → List (ArithExpr F) → Build F Unit
    | .field, _, [_] | .ptr _, _, [_] => pure ()
    | .tuple layouts, enable, words => validateList layouts enable words
    | .enum _ constructors, enable, words => do
        let some (tag, payload) := Layout.enumParts constructors.length (.const 0) words
          | throw .invalidShape
        if payload.length != Layout.payloadWidth constructors then throw .invalidShape
        let tests ← validateConstructors constructors enable tag payload 0
        guarded enable (.sub (tests.foldl ArithExpr.add (.const 0)) (.const 1))
    | _, _, _ => throw .invalidShape
  termination_by layout _ _ => sizeOf layout

  def validateList [Field F] : List Layout → ArithExpr F → List (ArithExpr F) → Build F Unit
    | [], _, [] => pure ()
    | layout :: layouts, enable, words => do
        if words.length < layout.width then throw .invalidShape
        validate layout enable (words.take layout.width)
        validateList layouts enable (words.drop layout.width)
    | [], _, _ :: _ => throw .invalidShape
  termination_by layouts _ _ => sizeOf layouts

  def validateConstructors [Field F] : List (String × Layout) → ArithExpr F → ArithExpr F →
      List (ArithExpr F) → Nat → Build F (List (ArithExpr F))
    | [], _, _, _, _ => pure []
    | (_, layout) :: constructors, enable, tag, payload, index => do
        let test ← equalIndicator (.sub tag (.const (index : F)))
        let selected := ArithExpr.mul enable test
        validate layout selected (payload.take layout.width)
        zeroWords selected (payload.drop layout.width)
        return test :: (← validateConstructors constructors enable tag payload (index + 1))
  termination_by constructors _ _ _ _ => sizeOf constructors
end

def validateValue [Field F] (decls : Declarations) (enable : ArithExpr F) (value : Symbolic F) :
    Build F Unit := do
  validate (← getLayout decls value.type) enable value.words

def validateValues [Field F] (decls : Declarations) (enable : ArithExpr F) :
    List (Symbolic F) → Build F Unit
  | [] => pure ()
  | value :: values => do
      validateValue decls enable value
      validateValues decls enable values

def checkPatterns [DecidableEq F] (decls : Declarations) (function : String) :
    List (Pattern F × Expr F) → List (Pattern F) → Except CompileError Unit
  | [], _ => pure ()
  | (pattern, _) :: rest, seen => do
      if seen.any (fun other => decide (pattern.condition = other)) then
        throw (.duplicatePattern function)
      if pattern.irrefutable decls then return ()
      checkPatterns decls function rest (pattern.condition :: seen)

mutual
  def lowerPattern [Field F] (decls : Declarations) (pattern : Pattern F) (value : Symbolic F) :
      Build F (ArithExpr F × Locals F) := do
    match pattern with
    | .wildcard => return (.const 1, [])
    | .bind name => return (.const 1, [(name, value)])
    | .literal literal =>
        let ⟨.field, [word]⟩ := value | throw .invalidShape
        return (← equalIndicator (.sub word (.const literal)), [])
    | .tuple patterns =>
        let .tuple types := value.type | throw .invalidShape
        lowerPatterns decls patterns (← splitValues decls types value.words)
    | .construct name ctor patterns =>
        if value.type ≠ .enum name then throw .invalidShape
        let some definition := decls.findEnum? name | throw .invalidShape
        let index := definition.constructors.findIdx (·.name == ctor)
        let some constructor := definition.constructors[index]? | throw .invalidShape
        let some (tag, payload) := Layout.enumParts definition.constructors.length (.const 0) value.words
          | throw .invalidShape
        let layout ← getLayout decls (.tuple constructor.fields)
        let values ← splitValues decls constructor.fields (payload.take layout.width)
        let tagTest ← equalIndicator (.sub tag (.const (index : F)))
        let (payloadTest, bindings) ← lowerPatterns decls patterns values
        return (.mul tagTest payloadTest, bindings)
  termination_by sizeOf pattern

  def lowerPatterns [Field F] (decls : Declarations) (patterns : List (Pattern F))
      (values : List (Symbolic F)) : Build F (ArithExpr F × Locals F) := do
    match patterns, values with
    | [], [] => return (.const 1, [])
    | pattern :: patterns, value :: values =>
        let (test, bindings) ← lowerPattern decls pattern value
        let (tests, rest) ← lowerPatterns decls patterns values
        return (.mul test tests, bindings ++ rest)
    | _, _ => throw .invalidShape
  termination_by sizeOf patterns
end

def constrainWords (enable : ArithExpr F) : List (ArithExpr F) → List (ArithExpr F) → Build F Unit
  | [], [] => pure ()
  | x :: xs, y :: ys => do
      guarded enable (.sub x y)
      constrainWords enable xs ys
  | _, _ => throw .invalidShape

/-- Equality is componentwise on the entire canonical encoding. -/
def constrainValue (enable : ArithExpr F) (left right : Symbolic F) : Build F Unit := do
  if left.type ≠ right.type then throw .invalidShape
  constrainWords enable left.words right.words

def asField : Symbolic F → Build F (ArithExpr F)
  | ⟨.field, [word]⟩ => pure word
  | _ => throw .invalidShape

def excludePairs (selectors : List (ArithExpr F)) : Build F Unit := do
  match selectors with
  | [] => return ()
  | selector :: rest =>
      for other in rest do constrain (.mul selector other)
      excludePairs rest

mutual
  def lowerExpr [Field F] [DecidableEq F] (program : Program F) (function : String)
      (locals : Locals F) (enable : ArithExpr F) (expr : Expr F) : Build F (Symbolic F) := do
    match expr with
    | .literal value => return .field (.const value)
    | .var name =>
        let some (_, value) := locals.find? (·.1 == name)
          | throw (.invalidProgram (.unboundVariable function name))
        return value
    | .tuple items => return .tuple (← lowerArgs program function locals enable items)
    | .construct name ctor args =>
        let some definition := program.enums.findEnum? name | throw .invalidShape
        let index := definition.constructors.findIdx (·.name == ctor)
        let some constructor := definition.constructors[index]? | throw .invalidShape
        let values ← lowerArgs program function locals enable args
        if values.map WireValue.type ≠ constructor.fields then throw .invalidShape
        let layout ← getLayout program.enums (.enum name)
        let payload := values.flatMap WireValue.words
        let tagWidth := Layout.tagWidth definition.constructors.length
        if payload.length + tagWidth > layout.width then throw .invalidShape
        return ⟨.enum name, Layout.enumWords definition.constructors.length (.const (index : F))
          (payload ++ List.replicate (layout.width - tagWidth - payload.length) (.const 0))⟩
    | .project value index =>
        let value ← lowerExpr program function locals enable value
        let .tuple types := value.type | throw .invalidShape
        let items ← splitValues program.enums types value.words
        let some result := items[index]? | throw .invalidShape
        return result
    | .letValue pattern value body =>
        let value ← lowerExpr program function locals enable value
        let (test, bindings) ← lowerPattern program.enums pattern value
        guarded enable (.sub test (.const 1))
        lowerExpr program function (bindings ++ locals) enable body
    | .store operand =>
        let value ← lowerExpr program function locals enable operand
        let address ← fresh
        boolean enable
        validateValue program.enums enable value
        requireCell enable (.var address) value
        return .ptr value.type (.var address)
    | .load operand =>
        let pointer ← lowerExpr program function locals enable operand
        let ⟨.ptr target, [address]⟩ := pointer | throw .invalidShape
        let result ← freshValue program.enums target
        let value := result.map ArithExpr.var
        boolean enable
        validateValue program.enums enable value
        requireCell enable address value
        return value
    | .neg value =>
        return .field (.sub (.const 0) (← asField (← lowerExpr program function locals enable value)))
    | .hint type key channel =>
        let _ ← lowerExpr program function locals enable key
        if !type.pointerFree program.enums then throw .invalidShape
        let result ← freshValue program.enums type
        validateValue program.enums enable (result.map ArithExpr.var)
        return result.map ArithExpr.var
    | .assertEq _ left right =>
        let left ← lowerExpr program function locals enable left
        let right ← lowerExpr program function locals enable right
        if !left.type.pointerFree program.enums then throw .invalidShape
        constrainValue enable left right
        return .tuple []
    | .binary op left right =>
        let left ← asField (← lowerExpr program function locals enable left)
        let right ← asField (← lowerExpr program function locals enable right)
        match op with
        | .add => return .field (.add left right)
        | .sub => return .field (.sub left right)
        | .mul => return .field (.mul left right)
        | .div =>
            let inverse ← fresh
            guarded enable (.sub (.mul right (.var inverse)) (.const 1))
            return .field (.mul left (.var inverse))
    | .call name args =>
        let some callee := program.findSignature? name
          | throw (.invalidProgram (.unknownFunction function name))
        let args ← lowerArgs program function locals enable args
        if args.map WireValue.type ≠ callee.params.map Prod.snd then throw .invalidShape
        let result ← freshValue program.enums callee.result
        boolean enable
        validateValues program.enums enable args
        validateValue program.enums enable (result.map ArithExpr.var)
        modify fun state => { state with sends := state.sends.push ⟨name, args, result, enable⟩ }
        return result.map ArithExpr.var
    | .matchValue scrutinee arms =>
        liftM (checkPatterns program.enums function arms [])
        let type ← liftM ((inferType program function
          (locals.map fun (name, value) => (name, value.type)) expr).mapError CompileError.invalidProgram)
        let scrutinee ← lowerExpr program function locals enable scrutinee
        let result ← freshValue program.enums type
        validateValue program.enums enable (result.map ArithExpr.var)
        let selectors ← lowerArms program function locals scrutinee
          (result.map ArithExpr.var) enable arms
        excludePairs selectors
        constrain (.sub (selectors.foldl ArithExpr.add (.const 0)) enable)
        return result.map ArithExpr.var
  termination_by sizeOf expr

  def lowerArgs [Field F] [DecidableEq F] (program : Program F) (function : String)
      (locals : Locals F) (enable : ArithExpr F) (args : List (Expr F)) :
      Build F (List (Symbolic F)) := do
    match args with
    | [] => return []
    | arg :: rest =>
        return (← lowerExpr program function locals enable arg) ::
          (← lowerArgs program function locals enable rest)
  termination_by sizeOf args

  def lowerArms [Field F] [DecidableEq F] (program : Program F) (function : String)
      (locals : Locals F) (scrutinee result : Symbolic F) (remaining : ArithExpr F)
      (arms : List (Pattern F × Expr F)) : Build F (List (ArithExpr F)) := do
    match arms with
    | [] => return []
    | (pattern, body) :: rest =>
        let (test, bindings) ← lowerPattern program.enums pattern scrutinee
        let selector := ArithExpr.var (← fresh)
        boolean selector
        constrain (.sub selector (.mul remaining test))
        let body ← lowerExpr program function (bindings ++ locals) selector body
        constrainValue selector result body
        if pattern.irrefutable program.enums then return [selector]
        let rest ← lowerArms program function locals scrutinee result
          (.mul remaining (.sub (.const 1) test)) rest
        return selector :: rest
  termination_by sizeOf arms
end

def lowerFunction [Field F] [DecidableEq F] (program : Program F) (fn : Function F) :
    Except CompileError (Chip F) := do
  let build : Build F (List (WireValue Var) × WireValue Var) := do
    let inputs ← freshValues program.enums (fn.params.map Prod.snd)
    let output ← freshValue program.enums fn.result
    validateValues program.enums (.const 1) (inputs.map (WireValue.map ArithExpr.var))
    validateValue program.enums (.const 1) (output.map ArithExpr.var)
    let locals := (fn.params.map Prod.fst).zip (inputs.map (WireValue.map ArithExpr.var))
    let body ← lowerExpr program fn.name locals (.const 1) fn.body
    constrainValue (.const 1) (output.map ArithExpr.var) body
    return (inputs, output)
  let ((inputs, output), state) ← build.run {}
  return ⟨fn.name, inputs, output.map ArithExpr.var, state.nextVar, state.constraints.toList, state.sends.toList,
    state.memory.toList⟩

end Compiler

def checkEnumTags (F : Type) [NatCast F] [DecidableEq F] (declaration : EnumDecl) :
    Except CompileError Unit :=
  if ((List.range declaration.constructors.length).map (fun i : Nat => (i : F))).Nodup then
    pure ()
  else throw (.tagCollision declaration.name)

def compile [Field F] [DecidableEq F] (program : Program F) : Except CompileError (System F) := do
  let _ ← (typecheck program).mapError CompileError.invalidProgram
  for declaration in program.enums do checkEnumTags F declaration
  let chips ← program.functions.mapM (Compiler.lowerFunction program)
  let _ ← (checkChips [] chips).mapError (fun _ => CompileError.invalidShape)
  return ⟨chips, program.enums, program.tables, program.maps⟩

end Aiur.Circuit
