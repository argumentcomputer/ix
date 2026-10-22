import Aiur.Optimized.ConstantDivision

namespace Aiur.Optimized
namespace Compiler

abbrev Symbolic (F : Type) := WireValue (Polynomial F)
abbrev Locals (F : Type) := List (String × Symbolic F)

structure State (F : Type) where
  roles : Array Role := #[]
  aliases : Array (Option (Polynomial F)) := #[]
  scopes : Array (Scope F) := #[]
  nextChoice : Nat := 0
  equations : Array (Equation F) := #[]
  calls : Array (Call F) := #[]
  cells : Array (Cell F) := #[]
  choices : Array Choice := #[]
  config : Config := {}

abbrev Build (F : Type) := StateT (State F) (Except String)

def fresh (role : Role) : Build F Witness := do
  let state ← get
  set { state with roles := state.roles.push role, aliases := state.aliases.push none }
  return state.roles.size

def equation (scope : ScopeId) (polynomial : Polynomial F) : Build F Unit :=
  modify fun state => { state with equations := state.equations.push ⟨scope, polynomial⟩ }

def getScope (scope : ScopeId) : Build F (Scope F) := do
  let some value := (← get).scopes[scope]? | throw "invalid activation scope"
  return value

def getLayout (decls : Declarations) (type : Ty) : Build F Layout :=
  liftM ((decls.layout type).mapError reprStr)

def freshValue (decls : Declarations) (role : Role) (type : Ty) : Build F (WireValue Witness) := do
  let layout ← getLayout decls type
  return ⟨type, ← (List.range layout.width).mapM fun _ => fresh role⟩

def splitValues (decls : Declarations) : List Ty → List α → Build F (List (WireValue α))
  | [], [] => pure []
  | type :: types, words => do
      let layout ← getLayout decls type
      if words.length < layout.width then throw "invalid flat value shape"
      return ⟨type, words.take layout.width⟩ ::
        (← splitValues decls types (words.drop layout.width))
  | [], _ :: _ => throw "invalid flat value shape"

/-- Logical selector variables allocated by a choice, in arm order. -/
def choiceSelectors (before : State F) (count : Nat) : List (Polynomial F) :=
  (List.range count).map fun arm => .var (before.roles.size + arm)

def choiceChildren (before : State F) (count : Nat) : List ScopeId :=
  (List.range count).map fun arm => before.scopes.size + arm

/-- Booleanity and pairwise exclusion are emitted before the coverage equation,
with the same ordering as the incremental selector allocator. -/
def choiceEquations [Field F] (before : State F) (enclosing : Scope F) (count : Nat) :
    List (Equation F) :=
  (List.range count).flatMap (fun arm =>
    let selector : Polynomial F := .var (before.roles.size + arm)
    ⟨0, .mul selector (.sub selector (.const 1))⟩ ::
      (List.range arm).map fun previous =>
        ⟨0, .mul selector (.var (before.roles.size + previous))⟩) ++
    [⟨0, .sub ((choiceSelectors before count).foldl Polynomial.add (.const 0)) enclosing.activation⟩]

/-- Resolve only the optional parent alias; control equations remain present. -/
def choiceAliases [Field F] (before : State F) (enclosing : Scope F) (count : Nat) :
    Array (Option (Polynomial F)) :=
  let aliases := before.aliases ++ (List.replicate count none).toArray
  let roles := before.roles ++ (List.replicate count Role.selector).toArray
  if before.config.eliminateSelectors && count > 0 then
    if let .var id := enclosing.activation then
      if roles[id]? == some .selector && (aliases[id]?.getD none).isNone then
        aliases.set! id (some ((choiceSelectors before count).foldl Polynomial.add (.const 0)))
      else aliases
    else aliases
  else aliases

/-- The fresh block of selectors and scopes can be allocated in bulk because
all indices are determined by the original state and the number of arms. -/
def choiceState [Field F] (before : State F) (parent : ScopeId) (enclosing : Scope F)
    (count : Nat) : State F :=
  { before with
    roles := before.roles ++ (List.replicate count Role.selector).toArray
    aliases := choiceAliases before enclosing count
    scopes := before.scopes ++ ((List.range count).map fun arm =>
      ⟨.var (before.roles.size + arm), enclosing.path ++ [(before.nextChoice, arm)]⟩).toArray
    nextChoice := before.nextChoice + 1
    equations := before.equations ++ (choiceEquations before enclosing count).toArray
    choices := before.choices.push ⟨parent, choiceChildren before count⟩ }

/-- All control equations are global. Branch payload equations use the new scopes. -/
def choice [Field F] (parent : ScopeId) (count : Nat) : Build F (List ScopeId) := do
  let enclosing ← getScope parent
  let before ← get
  set (choiceState before parent enclosing count)
  return choiceChildren before count

mutual
  def validate [Field F] (scope : ScopeId) : Layout → List (Polynomial F) → Build F Unit
    | .field, [_] | .ptr _, [_] => pure ()
    | .tuple layouts, words => validateList scope layouts words
    | .enum _ constructors, words => do
        let some (tag, payload) := Layout.enumParts constructors.length (.const 0) words
          | throw "invalid enum shape"
        if payload.length != Layout.payloadWidth constructors then throw "invalid enum width"
        let branches ← choice scope constructors.length
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

def validateParameters [Field F] (decls : Declarations) (enabled : Bool)
    (inputs : List (WireValue Witness)) : Build F Unit := do
  if enabled then
    for value in inputs do validateValue decls 0 (value.map Polynomial.var)

mutual
  /-- Core patterns are conjunctions of scalar equalities. Source pattern loads
  have already been translated to ordinary core expressions by preparation. -/
  def pattern [Field F] (decls : Declarations) (pat : Pattern F) (value : Symbolic F) :
      Build F (List (Polynomial F) × Locals F) := do
    match pat with
    | .wildcard => return ([], [])
    | .bind name => return ([], [(name, value)])
    | .literal literal =>
        let ⟨.field, [word]⟩ := value | throw "non-field literal pattern"
        return ([.sub word (.const literal)], [])
    | .tuple patterns =>
        let .tuple types := value.type | throw "non-tuple pattern"
        patternList decls patterns (← splitValues decls types value.words)
    | .construct name ctor patterns =>
        if value.type ≠ .enum name then throw "constructor pattern type mismatch"
        let some definition := decls.findEnum? name | throw "unknown enum"
        let index := definition.constructors.findIdx (·.name == ctor)
        let some constructor := definition.constructors[index]? | throw "unknown constructor"
        let some (tag, payload) := Layout.enumParts definition.constructors.length (.const 0) value.words
          | throw "invalid constructor shape"
        let layout ← getLayout decls (.tuple constructor.fields)
        let values ← splitValues decls constructor.fields (payload.take layout.width)
        let (conditions, bindings) ← patternList decls patterns values
        return (.sub tag (.const (index : F)) :: conditions, bindings)
  termination_by sizeOf pat

  def patternList [Field F] (decls : Declarations) (patterns : List (Pattern F))
      (values : List (Symbolic F)) : Build F (List (Polynomial F) × Locals F) := do
    match patterns, values with
    | [], [] => return ([], [])
    | pat :: patterns, value :: values =>
        let (head, bindings) ← pattern decls pat value
        let (tail, rest) ← patternList decls patterns values
        return (head ++ tail, bindings ++ rest)
    | _, _ => throw "pattern arity mismatch"
  termination_by sizeOf patterns
end

/-- A conjunction fails exactly when its differences generate one in the field.
The coefficients are branch-owned witnesses; no global equality indicators. -/
def failure [Field F] (scope : ScopeId) (conditions : List (Polynomial F)) : Build F Unit := do
  let terms ← conditions.mapM fun difference => do
    return Polynomial.mul difference (.var (← fresh (.auxiliary scope)))
  equation scope (.sub (terms.foldl Polynomial.add (.const 0)) (.const 1))

def equalValue (scope : ScopeId) (left right : Symbolic F) : Build F Unit := do
  if left.type ≠ right.type ∨ left.words.length ≠ right.words.length then
    throw "value equality shape mismatch"
  for (a, b) in left.words.zip right.words do equation scope (.sub a b)

def asField : Symbolic F → Build F (Polynomial F)
  | ⟨.field, [word]⟩ => pure word
  | _ => throw "expected a field"

def destination (decls : Declarations) (scope : ScopeId) (type : Ty)
    (target : Option (WireValue Witness)) : Build F (WireValue Witness) := do
  if let some target := target then
    if target.type ≠ type then throw "destination type mismatch"
    return target
  freshValue decls (.auxiliary scope) type

def retainArms (decls : Declarations) : List (Pattern F × Expr F) → List (Pattern F × Expr F)
  | [] => []
  | arm :: rest => arm :: if arm.1.irrefutable decls then [] else retainArms decls rest

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
          -- The operand's soundness already supplies a canonical encoding.
          -- Storing it preserves the provenance used to justify later loads.
          modify fun state => { state with cells := state.cells.push ⟨scope, .var address, value⟩ }
          pure (result.map Polynomial.var)
      | .load operand => do
          let pointer ← lower program function locals scope operand
          let ⟨.ptr type, [address]⟩ := pointer | throw "non-pointer load"
          let result ← destination program.enums scope type target
          let value := result.map Polynomial.var
          -- Finite entry derivations supply validity through store provenance
          -- and ROM address uniqueness; reads require only the cell lookup.
          modify fun state => { state with cells := state.cells.push ⟨scope, address, value⟩ }
          pure value
      | .neg operand => do
          pure (.field (.sub (.const 0) (← asField (← lower program function locals scope operand))))
      | .hint type key channel => do
          let _ ← lower program function locals scope key
          if !type.pointerFree program.enums then throw "hint result contains pointers"
          let result ← destination program.enums scope type target
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
                  equation scope (.sub (.mul right (.var inverse)) (.const 1))
                  pure (.field (.mul left (.var inverse)))
      | .call name args => do
          let some callee := program.findSignature? name | throw s!"unknown function {name}"
          let args ← lowerArgs program function locals scope args
          if args.map WireValue.type ≠ callee.params.map Prod.snd then throw "call argument types"
          let result ← destination program.enums scope callee.result target
          -- Canonical arguments follow from expression soundness; the callee's
          -- induction hypothesis supplies a canonical result.
          modify fun state => { state with calls := state.calls.push ⟨scope, name, args, result⟩ }
          pure (result.map Polynomial.var)
      | .matchValue scrutinee arms => do
          let _ ← liftM ((Circuit.Compiler.checkPatterns program.enums function arms []).mapError reprStr)
          let type ← liftM ((inferType program function
            (locals.map fun (name, value) => (name, value.type)) expr).mapError reprStr)
          let scrutinee ← lower program function locals scope scrutinee
          let result ← destination program.enums scope type target
          let retained := retainArms program.enums arms
          let branches ← choice scope retained.length
          lowerArms program function locals scrutinee result branches arms []
          pure (result.map Polynomial.var)
    let value ← step
    if let some result := target then
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
        if pat.irrefutable program.enums then pure ()
        else lowerArms program function locals scrutinee result scopes rest (previous ++ [conditions])
    | _, _ => throw "branch scope mismatch"
  termination_by sizeOf arms
end

def function [Field F] [DecidableEq F] (program : Program F) (config : Config)
    (fn : Function F) (validateInputs : Bool := true) : Except String (ScopedChip F) := do
  let build : Build F (List (WireValue Witness) × WireValue Witness) := do
    let inputs ← (fn.params.map Prod.snd).mapM (freshValue program.enums .input)
    let output ← freshValue program.enums .output fn.result
    -- Only entry arguments and fresh hints cross the canonical-value boundary.
    validateParameters program.enums validateInputs inputs
    let locals := (fn.params.map Prod.fst).zip (inputs.map (WireValue.map Polynomial.var))
    let _ ← lower program fn.name locals 0 fn.body (some output)
    return (inputs, output)
  let ((inputs, output), state) ← build.run { config, scopes := #[⟨.const 1, []⟩] }
  return ⟨fn.name, inputs, output, state.roles, state.aliases, state.scopes,
    state.equations, state.calls, state.cells, state.choices⟩

end Compiler
end Aiur.Optimized
