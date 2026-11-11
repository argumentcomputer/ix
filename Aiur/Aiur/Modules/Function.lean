import Aiur.Modules.Frontend

/-! Individually named function quotations, assembled into modules by Lean. -/

namespace Aiur.Modules

/-- A module assembled from named function definitions and an optional declaration
fragment. Function quotations require named parameters, so their parameter
patterns are bindings. The ordinary module checker still checks every body. -/
def ofFunctions (name : String) (functions : List (Generic.Function α))
    (declarations : Definitions α := { program := { functions := [] } }) : Program α :=
  { modules := [{ name, body := .definitions {
      declarations with
      program := { declarations.program with functions := declarations.program.functions ++ functions }
      parameterPatterns := declarations.parameterPatterns ++
        functions.map fun f => (f.name, f.params.map fun p => .bind p.1) } }] }

namespace Frontend
open Lean Elab Term
open Aiur.Frontend Aiur.Generic.Frontend

/-- A declaration fragment for `ofFunctions` and function quotations. The module
wrapper provides the usual local type and qualified-name syntax. -/
syntax (name := declarationsTerm) "aiur_decls⟦" declsText "⟧" : term

@[term_elab declarationsTerm]
def elabDeclarations : TermElab := fun stx _ => uncounted do
  let result := ofBlockText (← getEnv) stx[1].getAtomVal
  match result with
  | .error e => throwErrorAt stx "{e}"
  | .ok { signatures := [], modules := [m] } =>
    let .definitions d := m.body | throwErrorAt stx "expected module declarations, not an alias"
    unless m.parameters.isEmpty && m.signature.isNone && d.program.functions.isEmpty do
      throwErrorAt stx "expected declarations without functions, module parameters, or a signature"
    return Lean.toExpr d
  | .ok _ => throwErrorAt stx "expected declarations of exactly one module"

def functionTextFn : Lean.Parser.ParserFn := fun c s =>
  let iniSz := s.stackSize
  let startPos := s.pos
  let s := (Lean.Parser.categoryParser `aiur_function 0).fn c s
  if s.hasError then s else
  let stopPos := s.pos
  let info := SourceInfo.original (c.mkEmptySubstringAt startPos) startPos
    (c.mkEmptySubstringAt stopPos) stopPos
  (s.shrinkStack iniSz).pushSyntax (Syntax.atom info (c.extract startPos stopPos))

def functionText : Lean.Parser.Parser where
  «fn» := functionTextFn
  info := (Lean.Parser.categoryParser `aiur_function 0).info

@[combinator_formatter functionText]
def functionText.formatter : PrettyPrinter.Formatter := PrettyPrinter.Formatter.visitAtom Name.anonymous

@[combinator_parenthesizer functionText]
def functionText.parenthesizer : PrettyPrinter.Parenthesizer := PrettyPrinter.Parenthesizer.visitToken

/-- Quote a single function, leaving linking and type inference to module
preparation. `aiur_fn (in declarations)⟦ … ⟧` recognizes constructors of local
types declared in that fragment. Calls may refer to later or recursive functions. -/
syntax (name := functionTerm) "aiur_fn" ("(" &"in" term ")")? "⟦" functionText "⟧" : term

@[term_elab functionTerm]
def elabFunction : TermElab := fun stx _ => uncounted do
  let declarations ← if stx[1].getArgs.isEmpty then
      pure ({ program := { functions := [] } } : Definitions Nat) else
    unsafe evalTerm (Definitions Nat) (mkApp (mkConst ``Definitions) (mkConst ``Nat)) stx[1][2]
  let locals := declarations.program.enums.map (·.name) ++ declarations.program.structs.map (·.name) ++
    declarations.program.aliases.map (·.name)
  let env ← getEnv
  let result : Except String (Generic.Function Nat) := do
    let s ← Parser.runParserCategory env `aiur_function stx[3].getAtomVal "<aiur_fn>"
    let s ← splitDotted s
    checkIdentifiers s
    let s ← normalize [] locals s
    let f ← lowerFunction [] [] [] s false
    if f.params.any (fun p => p.1.startsWith "$arg") then
      throw "function quotations require named parameters; destructure with `let` in the body"
    return f
  match result with
  | .error e => throwErrorAt stx "{e}"
  | .ok f => return Lean.toExpr f

end Frontend
end Aiur.Modules

namespace Aiur.Modules
open Lean Elab Command

/-- A module's declarations, retained in the importing environment until the
whole program is elaborated. No executable function constants are emitted yet. -/
structure FunctionModule where
  leanNamespace : Name
  module : Module Nat
  deriving Inhabited

private def addFunctionModule (state : NameMap (Array FunctionModule)) (m : FunctionModule) :=
  state.insert m.leanNamespace ((state.find? m.leanNamespace |>.getD #[]).push m)

initialize functionModules : SimplePersistentEnvExtension FunctionModule (NameMap (Array FunctionModule)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := addFunctionModule
    addImportedFn := mkStateFromImportedEntries addFunctionModule {} }

/-- Select modules explicitly and preserve their order, including across imports.
Conflicting registrations are rejected rather than depending on import order. -/
def declaredModules (env : Lean.Environment) (names : List Name) : Except String (Program Nat) := do
  let modules ← names.mapM fun name => do
    match (functionModules.getState env).find? name with
    | some #[m] => pure m.module
    | some _ => throw s!"conflicting Aiur module declarations: {name}"
    | none => throw s!"unknown Aiur module: {name}"
  return { modules }

namespace Frontend
open Aiur.Frontend Aiur.Generic.Frontend

declare_syntax_cat aiur_module_declarations
declare_syntax_cat aiur_module_function

syntax (name := moduleDeclarations) "aiur_decls⟦" declsText "⟧" : aiur_module_declarations
syntax (name := moduleFunction) "def" ident ":=" "aiur_fn" "⟦" functionText "⟧" : aiur_module_function

/-- Declare named Aiur functions without prematurely fixing unresolved types.
A program elaborator resolves the selected modules together, then emits each
function exactly once at its declared Lean name. This supports forward calls,
mutual recursion, and imports without runtime source-file access. -/
syntax (name := functionModule) "aiur_module" ident (&"as" ident)? "where"
  (aiur_module_declarations)? (aiur_module_function)* "end" : command

@[command_elab functionModule]
def elabFunctionModule : CommandElab := fun stx => uncounted do
  let leanNamespace := (← getCurrNamespace) ++ stx[1].getId
  let moduleName := if stx[2].getArgs.isEmpty then stx[1].getId.toString else stx[2][1].getId.toString
  if (functionModules.getState (← getEnv)).contains leanNamespace then
    throwErrorAt stx[1] "duplicate Aiur module: {leanNamespace}"
  let mut declarations : Definitions Nat := { program := { functions := [] } }
  unless stx[4].getArgs.isEmpty do
    let text := stx[4][0][1].getAtomVal
    let parsed ← ofExcept (ofBlockText (← getEnv) text)
    let { signatures := [], modules := [m] } := parsed
      | throwErrorAt stx[4] "expected declarations of exactly one module"
    let .definitions d := m.body | throwErrorAt stx[4] "expected module declarations"
    unless m.name == moduleName && m.parameters.isEmpty && m.signature.isNone && d.program.functions.isEmpty do
      throwErrorAt stx[4] "expected type declarations for module {moduleName}"
    declarations := d
  let locals := declarations.program.enums.map (·.name) ++ declarations.program.structs.map (·.name) ++
    declarations.program.aliases.map (·.name)
  let mut functions := []
  for member in stx[5].getArgs do
    let parsed ← ofExcept (Parser.runParserCategory (← getEnv) `aiur_function member[5].getAtomVal "<aiur_fn>")
    let parsed ← ofExcept (splitDotted parsed)
    ofExcept (checkIdentifiers parsed)
    let parsed ← ofExcept (normalize [] locals parsed)
    let f ← ofExcept (lowerFunction [] [] [] parsed false)
    unless member[1].getId.toString == f.name do
      throwErrorAt member[1] "declaration name must match Aiur function name {f.name}"
    if functions.any (fun g => g.name == f.name) then
      throwErrorAt member[1] "duplicate Aiur function: {f.name}"
    if f.params.any (fun p => p.1.startsWith "$arg") then
      throwErrorAt member "function declarations require named parameters; destructure with `let` in the body"
    functions := functions ++ [f]
  let program := ofFunctions moduleName functions declarations
  modifyEnv fun env => functionModules.addEntry env ⟨leanNamespace, program.modules.head!⟩

end Frontend
end Aiur.Modules
