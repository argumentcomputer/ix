import Aiur.Optimized.Program
import Aiur.Execution.Encode

/-! Untrusted, executable witness advice. This module does not change the
certified compiler. Its companion lowering must reproduce the source chip
exactly, and its placement must reproduce the certified final chip exactly. -/
namespace Aiur.Trace
open Optimized

inductive Operation (F : Type) where
  | assign (dest : List Witness) (values : List (Polynomial F))
  | inverse (dest : Witness) (value : Polynomial F)
  | choose (dest : List Witness) (tests : List (List (Polynomial F)))
  | failure (dest : List Witness) (differences : List (Polynomial F))
  | call (name : String) (args : List (Polynomial F)) (dest : List Witness)
  | store (type : Ty) (values : List (Polynomial F)) (dest : Witness)
  | load (type : Ty) (address : Polynomial F) (dest : List Witness)
  | hint (site : Nat) (type keyType : Ty) (key : List (Polynomial F)) (dest : List Witness) (channel : String := "")

structure Step (F : Type) where
  scope : ScopeId
  operation : Operation F

namespace Compiler
abbrev Symbolic := Optimized.Compiler.Symbolic
abbrev Locals := Optimized.Compiler.Locals

structure State (F : Type) where
  core : Optimized.Compiler.State F
  steps : Array (Step F) := #[]
  nextHint : Nat := 0

abbrev Build (F : Type) := StateT (State F) (Except String)

def core (action : Optimized.Compiler.Build F α) : Build F α := do
  let state ← get
  let (value, next) ← liftM (action.run state.core)
  set { state with core := next }
  return value

def emit (scope : ScopeId) (operation : Operation F) : Build F Unit :=
  modify fun state => { state with steps := state.steps.push ⟨scope, operation⟩ }

def capture (action : Build F α) : Build F (α × Array (Step F)) := do
  let previous := (← get).steps
  modify fun state => { state with steps := #[] }
  let result ← action
  let steps := (← get).steps
  modify fun state => { state with steps := previous }
  return (result, steps)

def append (steps : Array (Step F)) : Build F Unit :=
  modify fun state => { state with steps := state.steps ++ steps }

def fresh (role : Role) : Build F Witness := core (Optimized.Compiler.fresh role)
def equation (scope : ScopeId) (p : Polynomial F) : Build F Unit :=
  core (Optimized.Compiler.equation scope p)
def getLayout (decls : Declarations) (type : Ty) : Build F Layout :=
  core (Optimized.Compiler.getLayout decls type)
def freshValue (decls : Declarations) (role : Role) (type : Ty) : Build F (WireValue Witness) :=
  core (Optimized.Compiler.freshValue decls role type)
def splitValues (decls : Declarations) (types : List Ty) (words : List α) :
    Build F (List (WireValue α)) := core (Optimized.Compiler.splitValues decls types words)
def pattern [Field F] (decls : Declarations) (pat : Pattern F) (value : Symbolic F) :
    Build F (List (Polynomial F) × Locals F) := core (Optimized.Compiler.pattern decls pat value)
def equalValue (scope : ScopeId) (left right : Symbolic F) : Build F Unit :=
  core (Optimized.Compiler.equalValue scope left right)
def asField (value : Symbolic F) : Build F (Polynomial F) := core (Optimized.Compiler.asField value)
def destination (decls : Declarations) (scope : ScopeId) (type : Ty)
    (target : Option (WireValue Witness)) : Build F (WireValue Witness) :=
  core (Optimized.Compiler.destination decls scope type target)

def choice [Field F] (scope : ScopeId) (tests : List (List (Polynomial F))) : Build F (List ScopeId) := do
  let first := (← get).core.roles.size
  let children ← core (Optimized.Compiler.choice scope tests.length)
  emit scope (.choose ((List.range tests.length).map (first + ·)) tests)
  return children

mutual
  def validate [Field F] (scope : ScopeId) : Layout → List (Polynomial F) → Build F Unit
    | .field, [_] | .ptr _, [_] => pure ()
    | .tuple layouts, words => validateList scope layouts words
    | .enum _ constructors, words => do
        let some (tag, payload) := Layout.enumParts constructors.length (.const 0) words
          | throw "invalid enum shape"
        if payload.length != Layout.payloadWidth constructors then throw "invalid enum width"
        let branches ← choice scope ((List.range constructors.length).map fun i => [.sub tag (.const (i : F))])
        validateConstructors constructors branches tag payload 0
    | _, _ => throw "invalid value shape"
  termination_by layout _ => sizeOf layout

  def validateList [Field F] (scope : ScopeId) : List Layout → List (Polynomial F) → Build F Unit
    | [], [] => pure ()
    | layout :: layouts, words => do
        if words.length < layout.width then throw "invalid tuple width"
        validate scope layout (words.take layout.width)
        validateList scope layouts (words.drop layout.width)
    | [], _ :: _ => throw "invalid tuple width"
  termination_by layouts _ => sizeOf layouts

  def validateConstructors [Field F] : List (String × Layout) → List ScopeId →
      Polynomial F → List (Polynomial F) → Nat → Build F Unit
    | [], [], _, _, _ => pure ()
    | (_, layout) :: rest, branch :: branches, tag, payload, index => do
        equation branch (.sub tag (.const (index : F)))
        validate branch layout (payload.take layout.width)
        for word in payload.drop layout.width do equation branch word
        validateConstructors rest branches tag payload (index + 1)
    | _, _, _, _, _ => throw "constructor scope mismatch"
  termination_by constructors _ _ _ _ => sizeOf constructors
end

def validateValue [Field F] (decls : Declarations) (scope : ScopeId) (value : Symbolic F) : Build F Unit := do
  validate scope (← getLayout decls value.type) value.words

def failure [Field F] (scope : ScopeId) (conditions : List (Polynomial F)) : Build F Unit := do
  let first := (← get).core.roles.size
  core (Optimized.Compiler.failure scope conditions)
  emit scope (.failure ((List.range conditions.length).map (first + ·)) conditions)

/-- Execution lowers even unreachable arms. Count their hint sites so that a
later live site's ordinal still binds to the exact execution instruction PC. -/
def hintCount : Expr F → Nat
  | .literal _ | .var _ => 0
  | .tuple xs | .construct _ _ xs | .call _ xs => (xs.map hintCount).sum
  | .project x _ | .load x | .store x | .neg x => hintCount x
  | .hint _ key channel => hintCount key + 1
  | .binary _ a b | .assertEq _ a b | .letValue _ a b => hintCount a + hintCount b
  | .matchValue x arms => hintCount x + (arms.map fun arm => hintCount arm.2).sum
termination_by expr => sizeOf expr
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | have h := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega
    | have h := List.sizeOf_lt_of_mem ‹_ ∈ _›
      cases arm
      simp_all only [Prod.mk.sizeOf_spec]
      omega

mutual
  def lower [Field F] [DecidableEq F] (program : Program F) (function : String)
      (locals : Locals F) (scope : ScopeId) (expr : Expr F)
      (target : Option (WireValue Witness) := none) : Build F (Symbolic F) := do
    let step : Build F (Symbolic F) := do
      match expr with
      | .literal value => pure (WireValue.field (.const value))
      | .var name => do
          let some (_, value) := locals.find? (·.1 == name) | throw s!"unbound variable {name}"
          pure value
      | .tuple items => do
          pure (.tuple (← lowerArgs program function locals scope items))
      | .construct name ctor args => do
          let some definition := program.enums.findEnum? name | throw "unknown enum"
          let index := definition.constructors.findIdx (·.name == ctor)
          let some constructor := definition.constructors[index]? | throw "unknown constructor"
          let values ← lowerArgs program function locals scope args
          if values.map WireValue.type ≠ constructor.fields then throw "constructor argument types"
          let layout ← getLayout program.enums (.enum name)
          let payload := values.flatMap WireValue.words
          let tagWidth := Layout.tagWidth definition.constructors.length
          if payload.length + tagWidth > layout.width then throw "constructor payload width"
          pure ⟨.enum name, Layout.enumWords definition.constructors.length (.const (index : F))
            (payload ++ List.replicate (layout.width - tagWidth - payload.length) (.const 0))⟩
      | .project operand index => do
          let value ← lower program function locals scope operand
          let .tuple types := value.type | throw "non-tuple projection"
          let items ← splitValues program.enums types value.words
          let some result := items[index]? | throw "projection out of bounds"
          pure result
      | .letValue pat value body => do
          let value ← lower program function locals scope value
          let (conditions, bindings) ← pattern program.enums pat value
          for condition in conditions do equation scope condition
          lower program function (bindings ++ locals) scope body target
      | .store operand => do
          let value ← lower program function locals scope operand
          let result ← destination program.enums scope (.ptr value.type) target
          let [address] := result.words | throw "pointer width"
          emit scope (.store value.type value.words address)
          -- Match the proved compiler: the operand already establishes validity.
          core <| modify fun state => { state with cells := state.cells.push ⟨scope, .var address, value⟩ }
          pure (result.map Polynomial.var)
      | .load operand => do
          let pointer ← lower program function locals scope operand
          let ⟨.ptr type, [address]⟩ := pointer | throw "non-pointer load"
          let result ← destination program.enums scope type target
          let value := result.map Polynomial.var
          emit scope (.load type address result.words)
          -- Finite entry derivations supply validity through store provenance
          -- and ROM address uniqueness; reads require only the cell lookup.
          core <| modify fun state => { state with cells := state.cells.push ⟨scope, address, value⟩ }
          pure value
      | .neg operand => do
          pure (.field (.sub (.const 0) (← asField (← lower program function locals scope operand))))
      | .hint type key channel => do
          let key ← lower program function locals scope key
          let site := (← get).nextHint
          modify fun state => { state with nextHint := site + 1 }
          if !type.pointerFree program.enums then throw "hint result contains pointers"
          let result ← destination program.enums scope type target
          emit scope (.hint site type key.type key.words result.words channel)
          validateValue program.enums scope (result.map Polynomial.var)
          pure (result.map Polynomial.var)
      | .assertEq _ left right => do
          let left ← lower program function locals scope left
          let right ← lower program function locals scope right
          if !left.type.pointerFree program.enums then throw "assertion contains pointers"
          equalValue scope left right
          pure (.tuple [])
      | .binary op left right => do
          let left ← asField (← lower program function locals scope left)
          let right ← asField (← lower program function locals scope right)
          match op with
          | .add => pure (.field (.add left right))
          | .sub => pure (.field (.sub left right))
          | .mul => pure (.field (.mul left right))
          | .div =>
              match right.constantInverse? with
              | some inverse => pure (.field (.mul left (.const inverse)))
              | none => do
                  let inverse ← fresh (.auxiliary scope)
                  emit scope (.inverse inverse right)
                  equation scope (.sub (.mul right (.var inverse)) (.const 1))
                  pure (.field (.mul left (.var inverse)))
      | .call name args => do
          let some callee := program.findSignature? name | throw s!"unknown function {name}"
          let args ← lowerArgs program function locals scope args
          if args.map WireValue.type ≠ callee.params.map Prod.snd then throw "call argument types"
          let result ← destination program.enums scope callee.result target
          emit scope (.call name (args.flatMap WireValue.words) result.words)
          core <| modify fun state => { state with calls := state.calls.push ⟨scope, name, args, result⟩ }
          pure (result.map Polynomial.var)
      | .matchValue scrutinee arms => do
          let _ ← liftM ((Circuit.Compiler.checkPatterns program.enums function arms []).mapError reprStr)
          let type ← liftM ((inferType program function
            (locals.map fun (name, value) => (name, value.type)) expr).mapError reprStr)
          let scrutinee ← lower program function locals scope scrutinee
          let result ← destination program.enums scope type target
          let retained := Optimized.Compiler.retainArms program.enums arms
          let tests ← retained.mapM fun (pat, _) => return (← pattern program.enums pat scrutinee).1
          let branches ← choice scope tests
          lowerArms program function locals scrutinee result branches arms []
          pure (result.map Polynomial.var)
    let value ← step
    if let some result := target then
      emit scope (.assign result.words value.words)
      equalValue scope (result.map Polynomial.var) value
      return result.map Polynomial.var
    return value
  termination_by sizeOf expr

  def lowerArgs [Field F] [DecidableEq F] (program : Program F) (function : String)
      (locals : Locals F) (scope : ScopeId) (args : List (Expr F)) : Build F (List (Symbolic F)) := do
    match args with
    | [] => return []
    | arg :: rest => return (← lower program function locals scope arg) ::
        (← lowerArgs program function locals scope rest)
  termination_by sizeOf args

  def lowerArms [Field F] [DecidableEq F] (program : Program F) (function : String)
      (locals : Locals F) (scrutinee : Symbolic F) (result : WireValue Witness)
      (scopes : List ScopeId) (arms : List (Pattern F × Expr F))
      (previous : List (List (Polynomial F))) : Build F Unit := do
    match scopes, arms with
    | [], [] => pure ()
    | scope :: scopes, (pat, body) :: rest => do
        let (conditions, bindings) ← pattern program.enums pat scrutinee
        for condition in conditions do equation scope condition
        for earlier in previous do failure scope earlier
        let _ ← lower program function (bindings ++ locals) scope body (some result)
        if pat.irrefutable program.enums then
          modify fun state => { state with nextHint := state.nextHint + (rest.map fun (_, body) => hintCount body).sum }
        else lowerArms program function locals scrutinee result scopes rest (previous ++ [conditions])
    | _, _ => throw "branch scope mismatch"
  termination_by sizeOf arms
end

structure Result (F : Type) where
  chip : ScopedChip F
  steps : Array (Step F)
  hints : Nat

def function [Field F] [DecidableEq F] (program : Program F) (config : Config)
    (fn : Function F) (validateInputs : Bool := true) : Except String (Result F) := do
  let build : Build F (List (WireValue Witness) × WireValue Witness) := do
    let inputs ← (fn.params.map Prod.snd).mapM (freshValue program.enums .input)
    let output ← freshValue program.enums .output fn.result
    if validateInputs then
      for value in inputs do validateValue program.enums 0 (value.map Polynomial.var)
    let locals := (fn.params.map Prod.fst).zip (inputs.map (WireValue.map Polynomial.var))
    let _ ← lower program fn.name locals 0 fn.body (some output)
    return (inputs, output)
  let ((inputs, output), state) ← build.run { core := { config, scopes := #[⟨.const 1, []⟩] } }
  let c := state.core
  let chip := ScopedChip.mk fn.name inputs output c.roles c.aliases c.scopes c.equations c.calls c.cells c.choices
  let original ← Optimized.Compiler.function program config fn validateInputs
  unless chip == original do throw s!"trace lowering differs from certified lowering in {fn.name}"
  return ⟨chip, state.steps, state.nextHint⟩

end Compiler
end Aiur.Trace
