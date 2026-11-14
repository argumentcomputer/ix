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
  deriving Repr, Inhabited, Lean.ToExpr, Lean.ToJson, Lean.FromJson

mutual
  /-- Structural equality of types. Hand-written, unlike a derived instance,
  which would be a `partial def` for this nested type and so opaque to the
  kernel and to proofs. `BEq Ty` is the instance this decision induces. -/
  def Ty.decEq : (left right : Ty) → Decidable (left = right)
    | .field, .field => .isTrue rfl
    | .tuple xs, .tuple ys =>
        match Ty.listDecEq xs ys with
        | .isTrue h => .isTrue (congrArg Ty.tuple h)
        | .isFalse h => .isFalse (fun eq => h (Ty.tuple.inj eq))
    | .array x n, .array y m =>
        match Ty.decEq x y with
        | .isTrue h =>
            if hn : n = m then .isTrue (by cases h; cases hn; rfl)
            else .isFalse (fun eq => hn (Ty.array.inj eq).2)
        | .isFalse h => .isFalse (fun eq => h (Ty.array.inj eq).1)
    | .ptr x, .ptr y =>
        match Ty.decEq x y with
        | .isTrue h => .isTrue (congrArg Ty.ptr h)
        | .isFalse h => .isFalse (fun eq => h (Ty.ptr.inj eq))
    | .param x, .param y =>
        if h : x = y then .isTrue (by cases h; rfl)
        else .isFalse (fun eq => h (Ty.param.inj eq))
    | .named x xs, .named y ys =>
        if h : x = y then
          match Ty.listDecEq xs ys with
          | .isTrue hs => .isTrue (by cases h; cases hs; rfl)
          | .isFalse hs => .isFalse (fun eq => hs (Ty.named.inj eq).2)
        else .isFalse (fun eq => h (Ty.named.inj eq).1)
    | .field, .tuple _ |
      .field, .array _ _ |
      .field, .ptr _ |
      .field, .param _ |
      .field, .named _ _ |
      .tuple _, .field |
      .tuple _, .array _ _ |
      .tuple _, .ptr _ |
      .tuple _, .param _ |
      .tuple _, .named _ _ |
      .array _ _, .field |
      .array _ _, .tuple _ |
      .array _ _, .ptr _ |
      .array _ _, .param _ |
      .array _ _, .named _ _ |
      .ptr _, .field |
      .ptr _, .tuple _ |
      .ptr _, .array _ _ |
      .ptr _, .param _ |
      .ptr _, .named _ _ |
      .param _, .field |
      .param _, .tuple _ |
      .param _, .array _ _ |
      .param _, .ptr _ |
      .param _, .named _ _ |
      .named _ _, .field |
      .named _ _, .tuple _ |
      .named _ _, .array _ _ |
      .named _ _, .ptr _ |
      .named _ _, .param _ => .isFalse (by intro h; cases h)
  termination_by left _ => sizeOf left

  def Ty.listDecEq : (left right : List Ty) → Decidable (left = right)
    | [], [] => .isTrue rfl
    | [], _ :: _ => .isFalse (by intro h; cases h)
    | _ :: _, [] => .isFalse (by intro h; cases h)
    | x :: xs, y :: ys => match Ty.decEq x y, Ty.listDecEq xs ys with
      | .isTrue h, .isTrue hs => .isTrue (by cases h; cases hs; rfl)
      | .isFalse h, _ => .isFalse (fun eq => h (List.cons.inj eq).1)
      | _, .isFalse h => .isFalse (fun eq => h (List.cons.inj eq).2)
  termination_by left _ => sizeOf left
end

instance : DecidableEq Ty := Ty.decEq


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

/-! ## Instance symbols

`Instance.symbol` is the instance's compact JSON (`Lean.Json.compress` of its
derived `ToJson`) behind a `$`. It is written out character by character so
that the kernel computes it and `Instance.ofSymbol` is its proved inverse
(`Aiur.Generic.Instance.ofSymbol_symbol`). `Lean.Json.compress` is a
`partial def`, opaque to the kernel and to proofs. A native test
(`Tests.Ix.InstanceSymbols`) checks that the two agree byte for byte on every
instance of the deployed programs. -/
namespace Symbol

/-- `"field"` -/
def litField : List Char :=
  ['"', 'f', 'i', 'e', 'l', 'd', '"']

/-- `{"tuple":{"items":` -/
def litTuple : List Char :=
  ['{', '"', 't', 'u', 'p', 'l', 'e', '"', ':', '{', '"', 'i', 't', 'e', 'm', 's', '"', ':']

/-- `{"array":{"element":` -/
def litArray : List Char :=
  ['{', '"', 'a', 'r', 'r', 'a', 'y', '"', ':', '{', '"', 'e', 'l', 'e', 'm', 'e', 'n', 't', '"', ':']

/-- `,"length":` -/
def litLength : List Char :=
  [',', '"', 'l', 'e', 'n', 'g', 't', 'h', '"', ':']

/-- `{"ptr":{"target":` -/
def litPtr : List Char :=
  ['{', '"', 'p', 't', 'r', '"', ':', '{', '"', 't', 'a', 'r', 'g', 'e', 't', '"', ':']

/-- `{"param":{"name":` -/
def litParam : List Char :=
  ['{', '"', 'p', 'a', 'r', 'a', 'm', '"', ':', '{', '"', 'n', 'a', 'm', 'e', '"', ':']

/-- `{"named":{"args":` -/
def litNamed : List Char :=
  ['{', '"', 'n', 'a', 'm', 'e', 'd', '"', ':', '{', '"', 'a', 'r', 'g', 's', '"', ':']

/-- `,"name":` -/
def litName : List Char :=
  [',', '"', 'n', 'a', 'm', 'e', '"', ':']

/-- `}}` -/
def litClose2 : List Char :=
  ['}', '}']

/-- `{"name":` -/
def litKeyName : List Char :=
  ['{', '"', 'n', 'a', 'm', 'e', '"', ':']

/-- `,"types":` -/
def litKeyTypes : List Char :=
  [',', '"', 't', 'y', 'p', 'e', 's', '"', ':']

/-- One character of a JSON string's body, escaped as `Lean.Json.escape`
escapes it: `"`, `\`, newline and carriage return by a backslash, other
characters below `0x20` as `\u00xx`, everything else as itself. -/
def escapeChar (c : Char) : List Char :=
  if c = '"' then ['\\', '"']
  else if c = '\\' then ['\\', '\\']
  else if c = '\n' then ['\\', 'n']
  else if c = '\r' then ['\\', 'r']
  else if 0x20 ≤ c.toNat then [c]
  else
    let n := c.toNat
    ['\\', 'u', Nat.digitChar (n / 4096), Nat.digitChar (n % 4096 / 256),
      Nat.digitChar (n % 256 / 16), Nat.digitChar (n % 16)]

/-- A JSON string literal. -/
def string (s : String) : List Char := '"' :: (s.toList.flatMap escapeChar ++ ['"'])

/-- The decimal digits of `n`, most significant first, as `toString n`. -/
def decimal (n : Nat) : List Char :=
  if h : n < 10 then [Nat.digitChar n] else decimal (n / 10) ++ [Nat.digitChar (n % 10)]
termination_by n
decreasing_by omega

mutual
  /-- A type's JSON, as its derived `ToJson`. -/
  def ty : Ty → List Char
    | .field => litField
    | .tuple items => litTuple ++ (tys items ++ litClose2)
    | .array t n => litArray ++ (ty t ++ (litLength ++ (decimal n ++ litClose2)))
    | .ptr t => litPtr ++ (ty t ++ litClose2)
    | .param n => litParam ++ (string n ++ litClose2)
    | .named n args => litNamed ++ (tys args ++ (litName ++ (string n ++ litClose2)))
  termination_by t => sizeOf t

  /-- A JSON array of types. -/
  def tys : List Ty → List Char
    | [] => ['[', ']']
    | t :: ts => '[' :: (ty t ++ elems ts)
  termination_by ts => sizeOf ts

  /-- The rest of a JSON array after an element. -/
  def elems : List Ty → List Char
    | [] => [']']
    | t :: ts => ',' :: (ty t ++ elems ts)
  termination_by ts => sizeOf ts
end

/-- An instance's JSON, as its derived `ToJson`: fields in key order. -/
def key (k : Instance) : List Char :=
  litKeyName ++ (string k.name ++ (litKeyTypes ++ (tys k.types ++ ['}'])))

/-- `s` after the prefix `lit`, if it has it. -/
def expect : List Char → List Char → Option (List Char)
  | [], s => some s
  | c :: cs, d :: ds => if c = d then expect cs ds else none
  | _ :: _, [] => none

/-- A lowercase hexadecimal digit's value. -/
def hexValue (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

/-- The character a one-character escape stands for. -/
def unescape (e : Char) : Option Char :=
  if e = '"' then some '"'
  else if e = '\\' then some '\\'
  else if e = 'n' then some '\n'
  else if e = 'r' then some '\r'
  else none

/-- A JSON string's body up to its closing quote, unescaped, and the rest. -/
def parseString : Nat → List Char → Option (List Char × List Char)
  | 0, _ => none
  | _ + 1, [] => none
  | f + 1, c :: r =>
    if c = '"' then some ([], r)
    else if c = '\\' then
      match r with
      | [] => none
      | e :: r =>
        if e = 'u' then
          match r with
          | a :: b :: c :: d :: r =>
            match hexValue a, hexValue b, hexValue c, hexValue d, parseString f r with
            | some a, some b, some c, some d, some (s, r) =>
                some (Char.ofNat (4096 * a + 256 * b + 16 * c + d) :: s, r)
            | _, _, _, _, _ => none
          | _ => none
        else
          match unescape e, parseString f r with
          | some ch, some (s, r) => some (ch :: s, r)
          | _, _ => none
    else
      match parseString f r with
      | some (s, r) => some (c :: s, r)
      | none => none

/-- A JSON string literal. -/
def parseQuoted (fuel : Nat) : List Char → Option (String × List Char)
  | c :: r => if c = '"' then (parseString fuel r).map fun (cs, r) => (String.ofList cs, r) else none
  | [] => none

/-- A decimal digit. -/
def isDigit (c : Char) : Bool := decide ('0' ≤ c ∧ c ≤ '9')

/-- A run of decimal digits and its value. -/
def parseDecimal (s : List Char) : Option (Nat × List Char) :=
  let ds := s.takeWhile isDigit
  if ds.isEmpty then none
  else some (ds.foldl (fun acc c => 10 * acc + (c.toNat - '0'.toNat)) 0, s.dropWhile isDigit)

mutual
  /-- A type's JSON. -/
  def parseTy : Nat → List Char → Option (Ty × List Char)
    | 0, _ => none
    | f + 1, s =>
      match expect litField s with
      | some r => some (.field, r)
      | none =>
      match expect litTuple s with
      | some r =>
        match parseTys f r with
        | some (items, r) => (expect litClose2 r).map fun r => (.tuple items, r)
        | none => none
      | none =>
      match expect litArray s with
      | some r =>
        match parseTy f r with
        | some (t, r) =>
          match expect litLength r with
          | some r =>
            match parseDecimal r with
            | some (n, r) => (expect litClose2 r).map fun r => (.array t n, r)
            | none => none
          | none => none
        | none => none
      | none =>
      match expect litPtr s with
      | some r =>
        match parseTy f r with
        | some (t, r) => (expect litClose2 r).map fun r => (.ptr t, r)
        | none => none
      | none =>
      match expect litParam s with
      | some r =>
        match parseQuoted f r with
        | some (n, r) => (expect litClose2 r).map fun r => (.param n, r)
        | none => none
      | none =>
      match expect litNamed s with
      | some r =>
        match parseTys f r with
        | some (args, r) =>
          match expect litName r with
          | some r =>
            match parseQuoted f r with
            | some (n, r) => (expect litClose2 r).map fun r => (.named n args, r)
            | none => none
          | none => none
        | none => none
      | none => none

  /-- A JSON array of types. -/
  def parseTys : Nat → List Char → Option (List Ty × List Char)
    | 0, _ => none
    | _ + 1, [] => none
    | f + 1, c :: r =>
      if c = '[' then
        match r with
        | d :: r' => if d = ']' then some ([], r') else parseElems f r
        | [] => none
      else none

  /-- A JSON array's elements and its closing bracket. -/
  def parseElems : Nat → List Char → Option (List Ty × List Char)
    | 0, _ => none
    | f + 1, s =>
      match parseTy f s with
      | some (t, c :: r) =>
        if c = ']' then some ([t], r)
        else if c = ',' then (parseElems f r).map fun (ts, r) => (t :: ts, r)
        else none
      | _ => none
end

/-- An instance's JSON, the whole input. -/
def parseKey (s : List Char) : Option Instance :=
  match expect litKeyName s with
  | none => none
  | some r =>
    match parseQuoted s.length r with
    | none => none
    | some (name, r) =>
      match expect litKeyTypes r with
      | none => none
      | some r =>
        match parseTys s.length r with
        | some (types, ['}']) => some ⟨name, types⟩
        | _ => none

end Symbol

/-- `$` is reserved for generated names; source identifiers cannot contain
it. The JSON form encodes nested types unambiguously, including empty
tuples. -/
def Instance.symbol (key : Instance) : String :=
  if key.types.isEmpty then key.name else String.ofList ('$' :: Symbol.key key)

def Instance.ofSymbol (name : String) : Except String Instance :=
  match name.toList with
  | c :: rest =>
    if c = '$' then
      match Symbol.parseKey rest with
      | some key => .ok key
      | none => .error s!"invalid instance symbol '{name}'"
    else .ok ⟨name, []⟩
  | [] => .ok ⟨name, []⟩

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
