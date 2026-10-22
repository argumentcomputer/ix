import Aiur.AST
import Lean

/-! The source language keeps type parameters; the existing `Aiur.Program` is
the concrete language consumed by the circuit compiler. -/
deriving instance Lean.ToExpr for Aiur.BinOp
deriving instance Lean.ToExpr for Aiur.Assertion

namespace Aiur.Generic

inductive Ty where
  | field
  | tuple (items : List Ty)
  | array (element : Ty) (length : Nat)
  | ptr (target : Ty)
  | param (name : String)
  | named (name : String) (args : List Ty)
  deriving Repr, BEq, Inhabited, Lean.ToExpr, Lean.ToJson, Lean.FromJson

def Ty.subst (env : List (String × Ty)) : Ty → Ty
  | .field => .field
  | .tuple items => .tuple (items.map (Ty.subst env))
  | .array t n => .array (t.subst env) n
  | .ptr target => .ptr (target.subst env)
  | .param name => (env.lookup name).getD (.param name)
  | .named name args => .named name (args.map (Ty.subst env))
termination_by type => sizeOf type

def Ty.parameters : Ty → List String
  | .field => []
  | .tuple items | .named _ items => items.flatMap Ty.parameters
  | .ptr target | .array target _ => target.parameters
  | .param name => [name]
termination_by type => sizeOf type

def Ty.concrete (type : Ty) : Bool := type.parameters.isEmpty

/-- A computational size bound, independent of identifier spelling. -/
def Ty.nodes : Ty → Nat
  | .field | .param _ => 1
  | .ptr t => 1 + t.nodes
  | .array t n => 1 + (n + 1) * t.nodes
  | .tuple ts | .named _ ts => 1 + (ts.map Ty.nodes).sum
termination_by t => sizeOf t

/-- Names are nominal. Type arguments are part of an instance's identity. -/
structure Instance where
  name : String
  types : List Ty := []
  deriving Repr, BEq, Inhabited, Lean.ToExpr, Lean.ToJson, Lean.FromJson

/-- `$` is reserved for generated names; source identifiers cannot contain it.
JSON gives an unambiguous encoding of nested types, including empty tuples. -/
def Instance.symbol (key : Instance) : String :=
  if key.types.isEmpty then key.name else "$" ++ (Lean.toJson key).compress

def Instance.ofSymbol (name : String) : Except String Instance :=
  if name.startsWith "$" then do
    Lean.fromJson? (← Lean.Json.parse (name.drop 1).toString)
  else return ⟨name, []⟩

def Ty.toCore : Ty → Aiur.Ty
  | .field => .field
  | .tuple items => .tuple (items.map Ty.toCore)
  | .array t n => .tuple (List.replicate n t.toCore)
  | .ptr target => .ptr target.toCore
  | .param name => .enum ("$param:" ++ name)
  | .named name args => .enum (Instance.symbol ⟨name, args⟩)
termination_by type => sizeOf type

/-- Named fields stay in source order. The checker records their positions in
  declaration order as type/layout information; `none` slots are omitted fields
  in a pattern with `..`. An unannotated head is used only before checking. -/
structure RecordHead where
  type : Ty
  fields : List String
  rest : Bool := false
  params : List String := []
  slots : Option (List (Option Nat)) := none
  deriving Repr, BEq, Inhabited, Lean.ToExpr

def RecordHead.positions (head : RecordHead) (length : Nat) : List (Option Nat) :=
  head.slots.getD ((List.range length).map some)

def RecordHead.order (head : RecordHead) (items : List A) (fallback : A) : List A :=
  (head.positions items.length).map fun slot => (slot.bind (items[·]?)).getD fallback

def RecordHead.subst (types : List (String × Ty)) (head : RecordHead) : RecordHead :=
  { head with type := head.type.subst types }

/-- A checked named projection retains its source spelling and nominal owner. -/
structure FieldRef where
  name : String
  owner : Option Ty := none
  index : Nat := 0
  arity : Nat := 0
  deriving Repr, BEq, Inhabited, Lean.ToExpr

def FieldRef.subst (types : List (String × Ty)) (field : FieldRef) : FieldRef :=
  { field with owner := field.owner.map (Ty.subst types) }

/-- A source update selector. Widths and nominal owners are checker annotations;
indices remain natural numbers, never field literals. -/
inductive UpdateStep where
  | member (field : FieldRef)
  | project (index : Nat) (arity : Nat := 0)
  | index (index : Nat) (length : Nat := 0)
  deriving Repr, BEq, Inhabited, Lean.ToExpr

def UpdateStep.subst (types : List (String × Ty)) : UpdateStep → UpdateStep
  | .member field => .member (field.subst types)
  | .project i n => .project i n
  | .index i n => .index i n

def UpdateStep.position : UpdateStep → Nat
  | .member field => field.index
  | .project i _ | .index i _ => i

def UpdateStep.width : UpdateStep → Nat
  | .member field => field.arity
  | .project _ n | .index _ n => n

def UpdateStep.owner : UpdateStep → Option Ty
  | .member field => some (field.owner.getD (.named "$invalid" []))
  | .project _ _ | .index _ _ => none

abbrev UpdatePath := List UpdateStep

/-- Internal semantic constructor for a nominal product. -/
def structConstructor : String := "$struct"

/-- Binding layout for an ordered pattern alternative. The left alternative
sets the canonical order; the checker records the right alternative's positions.
Renaming bindings leaves these positions unchanged. -/
structure OrBindings where
  names : List String
  rightOrder : List Nat := []
  deriving Repr, BEq, Inhabited, Lean.ToExpr

inductive Pattern (α : Type) where
  | literal (value : α)
  | wildcard
  | bind (name : String)
  /-- A rooted const reference. Checking records its inferred use type. -/
  | global (name : String) (type : Option Ty := none)
  /-- Load the matched pointer, then match its contents. -/
  | load (pattern : Pattern α)
  /-- Ordered alternatives. Each alternative binds the same names and types. -/
  | orElse (left right : Pattern α) (bindings : OrBindings)
  | tuple (items : List (Pattern α))
  | array (items : List (Pattern α))
  | repeat (item : Pattern α) (length : Nat)
  | record (head : RecordHead) (items : List (Pattern α))
  | construct (type : Ty) (constructor : String) (args : List (Pattern α))
  /-- An expanded constructor qualifier; `params` bind inference slots in `type`.
  Elaboration replaces this with an ordinary nominal constructor pattern. -/
  | constructAs (params : List String) (type : Ty) (constructor : String) (args : List (Pattern α))
  deriving Repr, BEq, Inhabited, Lean.ToExpr

/-- Targets are lexical. A function call always establishes a fresh function
boundary; labels never refer into a caller. -/
inductive ExitTarget where
  | function
  | block (label : String)
  deriving Repr, BEq, DecidableEq, ReflBEq, LawfulBEq, Inhabited, Lean.ToExpr

inductive Control where
  | block (label : String)
  | exit (target : ExitTarget)
  deriving Repr, BEq, DecidableEq, Inhabited, Lean.ToExpr

/-- Source operations with an ordered argument list. Diagnostics are metadata;
their operands remain ordinary expressions throughout source evaluation. -/
inductive Builtin where
  | ascribe (type : Ty)
  | debug (message : String)
  | assertEq (assertion : Assertion)
  deriving Repr, BEq, Inhabited, Lean.ToExpr

def Builtin.subst (types : List (String × Ty)) : Builtin → Builtin
  | .ascribe t => .ascribe (t.subst types)
  | .debug message => .debug message
  | .assertEq message => .assertEq message

def Builtin.mapTypesM [Monad m] (f : Ty → m Ty) : Builtin → m Builtin
  | .ascribe t => return .ascribe (← f t)
  | .debug message => return .debug message
  | .assertEq message => return .assertEq message

def Builtin.types : Builtin → List Ty
  | .ascribe t => [t]
  | .debug _ => []
  | .assertEq _ => []

inductive Expr (α : Type) where
  | literal (value : α)
  | var (name : String)
  /-- A rooted source reference, independent of local variable bindings. -/
  | global (name : String) (type : Option Ty := none)
  | tuple (items : List (Expr α))
  | array (items : List (Expr α))
  /-- Evaluate the element once, then copy its value, including when length is zero. -/
  | repeat (value : Expr α) (length : Nat)
  | index (value : Expr α) (index : Nat)
  /-- Half-open bounds. Inference replaces an omitted end by the array length. -/
  | slice (value : Expr α) (start : Nat) (stop : Option Nat)
  | construct (name : String) (types : Option (List Ty)) (constructor : String) (args : List (Expr α))
  /-- Alias-free constructor template, consumed by generic inference. -/
  | constructAs (params : List String) (type : Ty) (constructor : String) (args : List (Expr α))
  | record (head : RecordHead) (items : List (Expr α))
  | member (value : Expr α) (field : FieldRef)
  /-- Functional updates retain their paths. Operands are the base followed by
  replacements in written order; checking enforces one operand per path. -/
  | update (paths : List UpdatePath) (operands : List (Expr α))
  | builtin (operation : Builtin) (operands : List (Expr α))
  | project (value : Expr α) (index : Nat)
  | letValue (pattern : Pattern α) (value body : Expr α)
  | store (value : Expr α)
  | load (pointer : Expr α)
  | hint (type : Ty) (key : Expr α) (channel : String := "")
  | neg (value : Expr α)
  | binary (op : BinOp) (left right : Expr α)
  | call (name : String) (types : Option (List Ty)) (args : List (Expr α))
  | matchValue (scrutinee : Expr α) (arms : List (Pattern α × Expr α))
  /-- Named blocks and exits remain explicit through checking and evaluation. -/
  | control (kind : Control) (body : Expr α)
  deriving Repr, BEq, Inhabited, Lean.ToExpr

structure Function (α : Type) where
  name : String
  typeParams : List String := []
  params : List (String × Ty)
  result : Ty
  body : Expr α
  /-- Mandatory circuit-only expansion; execution still makes an ordinary call. -/
  isInline : Bool := false
  deriving Repr, BEq, Inhabited, Lean.ToExpr

structure ConstructorDecl where
  name : String
  fields : List Ty
  deriving Repr, BEq, Inhabited, Lean.ToExpr

structure EnumDecl where
  name : String
  typeParams : List String := []
  constructors : List ConstructorDecl
  deriving Repr, BEq, Inhabited, Lean.ToExpr

structure StructDecl where
  name : String
  typeParams : List String := []
  fields : List (String × Ty)
  deriving Repr, BEq, Inhabited, Lean.ToExpr

/-- Struct signatures reuse the nominal-product part of the type/layout model.
The source declaration itself remains a `StructDecl`. -/
def StructDecl.signature (decl : StructDecl) : EnumDecl :=
  ⟨decl.name, decl.typeParams, [⟨structConstructor, decl.fields.map Prod.snd⟩]⟩

structure Table (α : Type) where
  name : String
  rowType : Ty
  rows : List (Expr α)
  deriving Repr, BEq, Inhabited, Lean.ToExpr

structure MapDecl where
  name : String
  params : List (String × Ty)
  result : Ty
  input : String
  output : String
  deriving Repr, BEq, Inhabited, Lean.ToExpr

structure AliasDecl where
  name : String
  typeParams : List String := []
  target : Ty
  deriving Repr, BEq, Inhabited, Lean.ToExpr

/-- A value/pattern template. Checking excludes binders and wildcards; `load`
denotes a read in patterns and a store in expressions. -/
structure ConstDecl (α : Type) where
  name : String
  value : Pattern α
  deriving Repr, BEq, Inhabited, Lean.ToExpr

structure Program (α : Type) where
  functions : List (Function α)
  enums : List EnumDecl := []
  structs : List StructDecl := []
  tables : List (Table α) := []
  maps : List MapDecl := []
  /-- Transparent type declarations retained in the source program. -/
  aliases : List AliasDecl := []
  /-- Source value/pattern declarations; references remain through evaluation. -/
  consts : List (ConstDecl α) := []
  deriving Repr, BEq, Inhabited, Lean.ToExpr

def Program.findFunction? (p : Program α) (name : String) := p.functions.find? (·.name == name)
def Program.nominals (p : Program α) : List EnumDecl := p.enums ++ p.structs.map StructDecl.signature
def Program.findStruct? (p : Program α) (name : String) := p.structs.find? (·.name == name)
def Program.findEnum? (p : Program α) (name : String) := p.nominals.find? (·.name == name)

/-- Gather binding values using checker-recorded positions, assigning their
canonical names. No value comparison or memory read occurs here. -/
def reorderBindings (names : List String) (positions : List Nat) (bindings : List (String × V)) :
    Option (List (String × V)) :=
  match names, positions with
  | [], [] => some []
  | name :: names, index :: positions => do
      let (_, value) ← bindings[index]?
      return (name, value) :: (← reorderBindings names positions bindings)
  | _, _ => none


def Pattern.bindingNames : Pattern α → List String
  | .literal _ | .wildcard | .global _ _ => []
  | .bind n => [n]
  | .record head ps => (head.order (ps.map Pattern.bindingNames) []).flatten
  | .orElse _ _ layout => layout.names
  | .load p => p.bindingNames
  | .repeat p n => (List.replicate n p.bindingNames).flatten
  | .tuple ps | .array ps | .construct _ _ ps | .constructAs _ _ _ ps => ps.flatMap Pattern.bindingNames
termination_by p => sizeOf p

def Pattern.hasLoads : Pattern α → Bool
  | .literal _ | .wildcard | .bind _ | .global _ _ => false
  | .orElse left right _ => left.hasLoads || right.hasLoads
  | .load _ => true
  | .record head ps => (head.order (ps.map Pattern.hasLoads) false).any id
  | .repeat p n => n != 0 && p.hasLoads
  | .tuple ps | .array ps | .construct _ _ ps | .constructAs _ _ _ ps => (ps.map Pattern.hasLoads).any id
termination_by p => sizeOf p

def Pattern.irrefutable (enums : List EnumDecl) : Pattern α → Bool
  | .literal _ | .global _ _ => false
  | .record head ps => (head.order (ps.map (Pattern.irrefutable enums)) true).all id
  | .wildcard | .bind _ => true
  | .orElse left right _ => left.irrefutable enums || right.irrefutable enums
  | .load p => p.irrefutable enums
  | .tuple ps | .array ps => (ps.map (Pattern.irrefutable enums)).all id
  | .repeat p n => n == 0 || p.irrefutable enums
  | .construct (.named n _) c ps | .constructAs _ (.named n _) c ps =>
      (enums.find? (·.name == n)).any (fun d => d.constructors.length == 1 && d.constructors.any (·.name == c)) &&
        (ps.map (Pattern.irrefutable enums)).all id
  | .construct _ _ _ | .constructAs _ _ _ _ => false
termination_by p => sizeOf p

/-- Binder spelling does not change a pattern's matching condition. -/
def Pattern.condition : Pattern α → Pattern α
  | .literal x => .literal x
  | .global n t => .global n t
  | .wildcard | .bind _ => .wildcard
  | .orElse left right _ => .orElse left.condition right.condition ⟨[], []⟩
  | .load p => .load p.condition
  | .record head ps => .construct head.type structConstructor (head.order (ps.map Pattern.condition) .wildcard)
  | .tuple ps | .array ps => .tuple (ps.map Pattern.condition)
  | .repeat p n => .tuple (List.replicate n p.condition)
  | .construct t c ps => .construct t c (ps.map Pattern.condition)
  | .constructAs params t c ps => .constructAs params t c (ps.map Pattern.condition)
termination_by p => sizeOf p

def Pattern.map (f : α → β) : Pattern α → Pattern β
  | .literal x => .literal (f x)
  | .wildcard => .wildcard
  | .bind n => .bind n
  | .global n t => .global n t
  | .orElse left right names => .orElse (left.map f) (right.map f) names
  | .load p => .load (p.map f)
  | .record head xs => .record head (xs.map (Pattern.map f))
  | .tuple xs => .tuple (xs.map (Pattern.map f))
  | .array xs => .array (xs.map (Pattern.map f))
  | .repeat p n => .repeat (p.map f) n
  | .construct t c xs => .construct t c (xs.map (Pattern.map f))
  | .constructAs ps t c xs => .constructAs ps t c (xs.map (Pattern.map f))
termination_by p => sizeOf p

def Expr.map (f : α → β) : Expr α → Expr β
  | .literal x => .literal (f x)
  | .var n => .var n
  | .global n t => .global n t
  | .tuple xs => .tuple (xs.map (Expr.map f))
  | .array xs => .array (xs.map (Expr.map f))
  | .repeat x n => .repeat (x.map f) n
  | .index x i => .index (x.map f) i
  | .slice x start stop => .slice (x.map f) start stop
  | .construct n ts c xs => .construct n ts c (xs.map (Expr.map f))
  | .constructAs ps t c xs => .constructAs ps t c (xs.map (Expr.map f))
  | .record head xs => .record head (xs.map (Expr.map f))
  | .update paths xs => .update paths (xs.map (Expr.map f))
  | .builtin op xs => .builtin op (xs.map (Expr.map f))
  | .member x field => .member (x.map f) field
  | .project x i => .project (x.map f) i
  | .letValue p x b => .letValue (p.map f) (x.map f) (b.map f)
  | .store x => .store (x.map f)
  | .load x => .load (x.map f)
  | .hint t k channel => .hint t (k.map f) channel
  | .neg x => .neg (x.map f)
  | .binary op x y => .binary op (x.map f) (y.map f)
  | .call n ts xs => .call n ts (xs.map (Expr.map f))
  | .matchValue x arms => .matchValue (x.map f) (arms.map fun arm => (arm.1.map f, arm.2.map f))
  | .control kind body => .control kind (body.map f)
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first | omega | have h := List.sizeOf_lt_of_mem ‹_ ∈ _›; try simp_all only [Prod.mk.sizeOf_spec]
  all_goals first | omega | cases ‹Pattern α × Expr α›; simp_all only [Prod.mk.sizeOf_spec]; omega

def ConstDecl.map (f : α → β) (d : ConstDecl α) : ConstDecl β :=
  { name := d.name, value := d.value.map f }

def Program.map (f : α → β) (p : Program α) : Program β := {
  functions := p.functions.map fun fn => { fn with body := fn.body.map f }
  enums := p.enums
  structs := p.structs
  tables := p.tables.map fun table => { table with rows := table.rows.map (Expr.map f) }
  maps := p.maps
  aliases := p.aliases
  consts := p.consts.map (ConstDecl.map f)
}

def Program.toField (p : Program Nat) (F : Type) [NatCast F] : Program F := p.map Nat.cast

end Aiur.Generic
