import Std

namespace Aiur

/-- Tuple shape is part of the type, including empty and singleton tuples. -/
inductive Ty where
  | field
  | tuple (items : List Ty)
  | ptr (target : Ty)
  | enum (name : String)
  deriving Repr, BEq

mutual
  def Ty.decEq : (left right : Ty) → Decidable (left = right)
    | .field, .field => .isTrue rfl
    | .tuple xs, .tuple ys =>
        match Ty.listDecEq xs ys with
        | .isTrue h => .isTrue (congrArg Ty.tuple h)
        | .isFalse h => .isFalse (fun eq => h (Ty.tuple.inj eq))
    | .ptr x, .ptr y =>
        match Ty.decEq x y with
        | .isTrue h => .isTrue (congrArg Ty.ptr h)
        | .isFalse h => .isFalse (fun eq => h (Ty.ptr.inj eq))
    | .enum x, .enum y =>
        if h : x = y then .isTrue (by cases h; rfl)
        else .isFalse (fun eq => h (Ty.enum.inj eq))
    | .enum _, .field | .enum _, .tuple _ | .enum _, .ptr _ |
      .field, .enum _ | .tuple _, .enum _ | .ptr _, .enum _ |
      .ptr _, .field | .ptr _, .tuple _ | .field, .ptr _ | .tuple _, .ptr _ =>
        .isFalse (by intro h; cases h)
    | .field, .tuple _ => .isFalse (by intro h; cases h)
    | .tuple _, .field => .isFalse (by intro h; cases h)
  termination_by left _ => sizeOf left

  def Ty.listDecEq : (left right : List (Ty)) → Decidable (left = right)
    | [], [] => .isTrue rfl
    | [], _ :: _ => .isFalse (by intro h; cases h)
    | _ :: _, [] => .isFalse (by intro h; cases h)
    | x :: xs, y :: ys => match Ty.decEq x y, Ty.listDecEq xs ys with
      | .isTrue h, .isTrue hs => .isTrue (by cases h; cases hs; rfl)
      | .isFalse h, _ => .isFalse (fun eq => h (List.cons.inj eq).1)
      | _, .isFalse h => .isFalse (fun eq => h (List.cons.inj eq).2)
  termination_by left _ => sizeOf left
end

instance : DecidableEq (Ty) := Ty.decEq

/-- Constructor identity is nominal and independent of the chosen field. -/
structure ConstructorDecl where
  name : String
  fields : List Ty
  deriving Repr, BEq, DecidableEq

structure EnumDecl where
  name : String
  constructors : List ConstructorDecl
  deriving Repr, BEq, DecidableEq

abbrev Declarations := List EnumDecl

def Declarations.findEnum? (decls : Declarations) (name : String) : Option EnumDecl :=
  decls.find? (·.name == name)

def Declarations.findConstructor? (decls : Declarations) (name constructor : String) :
    Option ConstructorDecl := do
  let decl ← decls.findEnum? name
  decl.constructors.find? (·.name == constructor)

inductive BinOp where
  | add | sub | mul | div
  deriving Repr, BEq, DecidableEq

/-- A structured value whose leaves are field elements (or symbolic field expressions). -/
inductive Value (α : Type) (Address : Type := α) where
  | field (value : α)
  | tuple (items : List (Value α Address))
  | ptr (target : Ty) (address : Address)
  | construct (enumName constructor : String) (args : List (Value α Address))
  deriving Repr, BEq

mutual
  def Value.decEq [DecidableEq α] [DecidableEq Address] :
      (left right : Value α Address) → Decidable (left = right)
    | .field x, .field y =>
        if h : x = y then .isTrue (by cases h; rfl)
        else .isFalse (fun eq => h (Value.field.inj eq))
    | .tuple xs, .tuple ys =>
        match Value.listDecEq xs ys with
        | .isTrue h => .isTrue (congrArg Value.tuple h)
        | .isFalse h => .isFalse (fun eq => h (Value.tuple.inj eq))
    | .ptr t x, .ptr u y =>
        if h : t = u ∧ x = y then .isTrue (by rcases h with ⟨rfl, rfl⟩; rfl)
        else .isFalse (fun eq => h (Value.ptr.inj eq))
    | .construct e c xs, .construct e' c' ys =>
        if h : e = e' ∧ c = c' then
          match Value.listDecEq xs ys with
          | .isTrue hs => .isTrue (by rcases h with ⟨rfl, rfl⟩; cases hs; rfl)
          | .isFalse hs => .isFalse (fun eq => hs (Value.construct.inj eq).2.2)
        else .isFalse (fun eq => h ⟨(Value.construct.inj eq).1, (Value.construct.inj eq).2.1⟩)
    | .construct _ _ _, .field _ | .construct _ _ _, .tuple _ | .construct _ _ _, .ptr _ _ |
      .field _, .construct _ _ _ | .tuple _, .construct _ _ _ | .ptr _ _, .construct _ _ _ |
      .field _, .tuple _ | .field _, .ptr _ _ | .tuple _, .field _ |
      .tuple _, .ptr _ _ | .ptr _ _, .field _ | .ptr _ _, .tuple _ =>
        .isFalse (by intro h; cases h)
  termination_by left _ => sizeOf left

  def Value.listDecEq [DecidableEq α] [DecidableEq Address] :
      (left right : List (Value α Address)) → Decidable (left = right)
    | [], [] => .isTrue rfl
    | [], _ :: _ => .isFalse (by intro h; cases h)
    | _ :: _, [] => .isFalse (by intro h; cases h)
    | x :: xs, y :: ys => match Value.decEq x y, Value.listDecEq xs ys with
      | .isTrue h, .isTrue hs => .isTrue (by cases h; cases hs; rfl)
      | .isFalse h, _ => .isFalse (fun eq => h (List.cons.inj eq).1)
      | _, .isFalse h => .isFalse (fun eq => h (List.cons.inj eq).2)
  termination_by left _ => sizeOf left
end

instance [DecidableEq α] [DecidableEq Address] : DecidableEq (Value α Address) := Value.decEq

/-- Map every circuit leaf, including the field representation of a pointer. -/
def Value.map (f : α → β) : Value α → Value β
  | .field x => .field (f x)
  | .tuple items => .tuple (items.map (Value.map f))
  | .ptr target address => .ptr target (f address)
  | .construct name ctor args => .construct name ctor (args.map (Value.map f))
termination_by value => sizeOf value

/-- Change opaque addresses without changing field data. -/
def Value.mapAddress (f : A → B) : Value F A → Value F B
  | .field x => .field x
  | .tuple items => .tuple (items.map (Value.mapAddress f))
  | .ptr target address => .ptr target (f address)
  | .construct name ctor args => .construct name ctor (args.map (Value.mapAddress f))
termination_by value => sizeOf value

def Value.type : Value α Address → Ty
  | .field _ => .field
  | .tuple items => .tuple (items.map Value.type)
  | .ptr target _ => .ptr target
  | .construct name _ _ => .enum name
termination_by value => sizeOf value

def Value.flatten : Value α → List α
  | .field x => [x]
  | .tuple items => items.flatMap Value.flatten
  | .ptr _ address => [address]
  | .construct _ _ args => args.flatMap Value.flatten
termination_by value => sizeOf value

def Value.addresses : Value α Address → List Address
  | .field _ => []
  | .tuple items => items.flatMap Value.addresses
  | .ptr _ address => [address]
  | .construct _ _ args => args.flatMap Value.addresses
termination_by value => sizeOf value

/-- Only the selected constructor payload is part of an enum value. -/
def Value.pointerFree : Value α Address → Bool
  | .field _ => true
  | .tuple items => (items.map Value.pointerFree).all id
  | .ptr _ _ => false
  | .construct _ _ args => (args.map Value.pointerFree).all id
termination_by value => sizeOf value

instance [OfNat α n] : OfNat (Value α Address) n := ⟨.field (OfNat.ofNat n)⟩

/-- Runtime locations are distinct from field-valued circuit addresses. -/
abbrev SourceValue (F : Type) := Value F Nat

/-- Static values cannot contain an address, including in nested constructor payloads. -/
abbrev Constant (α : Type) := Value α Empty

def Constant.toValue (value : Constant α) : Value α Address :=
  value.mapAddress Empty.elim

def Constant.map (f : α → β) : Constant α → Constant β
  | .field value => .field (f value)
  | .tuple items => .tuple (items.map (Constant.map f))
  | .construct name ctor args => .construct name ctor (args.map (Constant.map f))
  | .ptr _ address => nomatch address
termination_by value => sizeOf value

/-- Forgetting opaque addresses succeeds exactly on pointer-free values. -/
def Value.toConstant? : Value α Address → Option (Constant α)
  | .field value => some (.field value)
  | .tuple items => (.tuple ·) <$> items.mapM Value.toConstant?
  | .construct name ctor args => (.construct name ctor ·) <$> args.mapM Value.toConstant?
  | .ptr _ _ => none
termination_by value => sizeOf value

/-- A named, precommitted trace of typed constant rows. -/
structure Table (α : Type) where
  name : String
  rowType : Ty
  rows : List (Constant α)
  deriving Repr, BEq

/-- The input trace's outer tuple is the argument list; its elements retain their types. -/
structure MapDecl where
  name : String
  params : List (String × Ty)
  result : Ty
  input : String
  output : String
  deriving Repr, BEq, DecidableEq

structure Signature where
  params : List (String × Ty)
  result : Ty
  deriving Repr, BEq, DecidableEq

/-- Patterns can test leaves, discard subtrees, or bind entire subtrees. -/
inductive Pattern (α : Type) where
  | literal (value : α)
  | wildcard
  | bind (name : String)
  | tuple (items : List (Pattern α))
  | construct (enumName constructor : String) (args : List (Pattern α))
  deriving Repr, BEq

mutual
  def Pattern.decEq [DecidableEq α] : (left right : Pattern α) → Decidable (left = right)
    | .literal x, .literal y =>
        if h : x = y then .isTrue (by cases h; rfl)
        else .isFalse (fun eq => h (Pattern.literal.inj eq))
    | .wildcard, .wildcard => .isTrue rfl
    | .bind x, .bind y =>
        if h : x = y then .isTrue (by cases h; rfl)
        else .isFalse (fun eq => h (Pattern.bind.inj eq))
    | .tuple xs, .tuple ys =>
        match Pattern.listDecEq xs ys with
        | .isTrue h => .isTrue (congrArg Pattern.tuple h)
        | .isFalse h => .isFalse (fun eq => h (Pattern.tuple.inj eq))
    | .construct e c xs, .construct e' c' ys =>
        if h : e = e' ∧ c = c' then
          match Pattern.listDecEq xs ys with
          | .isTrue hs => .isTrue (by rcases h with ⟨rfl, rfl⟩; cases hs; rfl)
          | .isFalse hs => .isFalse (fun eq => hs (Pattern.construct.inj eq).2.2)
        else .isFalse (fun eq => h ⟨(Pattern.construct.inj eq).1, (Pattern.construct.inj eq).2.1⟩)
    | .construct _ _ _, .literal _ | .construct _ _ _, .wildcard |
      .construct _ _ _, .bind _ | .construct _ _ _, .tuple _ |
      .literal _, .construct _ _ _ | .wildcard, .construct _ _ _ |
      .bind _, .construct _ _ _ | .tuple _, .construct _ _ _ =>
        .isFalse (by intro h; cases h)
    | .literal _, .wildcard => .isFalse (by intro h; cases h)
    | .literal _, .bind _ => .isFalse (by intro h; cases h)
    | .literal _, .tuple _ => .isFalse (by intro h; cases h)
    | .wildcard, .literal _ => .isFalse (by intro h; cases h)
    | .wildcard, .bind _ => .isFalse (by intro h; cases h)
    | .wildcard, .tuple _ => .isFalse (by intro h; cases h)
    | .bind _, .literal _ => .isFalse (by intro h; cases h)
    | .bind _, .wildcard => .isFalse (by intro h; cases h)
    | .bind _, .tuple _ => .isFalse (by intro h; cases h)
    | .tuple _, .literal _ => .isFalse (by intro h; cases h)
    | .tuple _, .wildcard => .isFalse (by intro h; cases h)
    | .tuple _, .bind _ => .isFalse (by intro h; cases h)
  termination_by left _ => sizeOf left

  def Pattern.listDecEq [DecidableEq α] : (left right : List (Pattern α)) → Decidable (left = right)
    | [], [] => .isTrue rfl
    | [], _ :: _ => .isFalse (by intro h; cases h)
    | _ :: _, [] => .isFalse (by intro h; cases h)
    | x :: xs, y :: ys => match Pattern.decEq x y, Pattern.listDecEq xs ys with
      | .isTrue h, .isTrue hs => .isTrue (by cases h; cases hs; rfl)
      | .isFalse h, _ => .isFalse (fun eq => h (List.cons.inj eq).1)
      | _, .isFalse h => .isFalse (fun eq => h (List.cons.inj eq).2)
  termination_by left _ => sizeOf left
end

instance [DecidableEq α] : DecidableEq (Pattern α) := Pattern.decEq

/-- Equality always holds in the semantics and circuit. `runtimeCheck` only
controls the optional check performed by the Rust execution backend. -/
structure Assertion where
  message : Option String := none
  runtimeCheck : Bool := true
  deriving Repr, BEq, DecidableEq, Inhabited

inductive Expr (α : Type) where
  | literal (value : α)
  | var (name : String)
  | tuple (items : List (Expr α))
  | construct (enumName constructor : String) (args : List (Expr α))
  | project (value : Expr α) (index : Nat)
  | letValue (pattern : Pattern α) (value body : Expr α)
  | store (value : Expr α)
  | load (pointer : Expr α)
  | hint (type : Ty) (key : Expr α) (channel : String := "")
  | neg (value : Expr α)
  | binary (op : BinOp) (left right : Expr α)
  | assertEq (assertion : Assertion) (left right : Expr α)
  | call (function : String) (args : List (Expr α))
  | matchValue (scrutinee : Expr α) (arms : List (Pattern α × Expr α))
  deriving Repr, BEq

/-- A selected table result contains no executable user code or allocations. -/
def Constant.toExpr : Constant α → Expr α
  | .field value => .literal value
  | .tuple items => .tuple (items.map Constant.toExpr)
  | .construct name ctor args => .construct name ctor (args.map Constant.toExpr)
  | .ptr _ address => nomatch address
termination_by value => sizeOf value

structure Function (α : Type) where
  name : String
  params : List (String × Ty)
  result : Ty
  body : Expr α
  deriving Repr, BEq

structure Program (α : Type) where
  functions : List (Function α)
  enums : Declarations := []
  tables : List (Table α) := []
  maps : List MapDecl := []
  deriving Repr, BEq

def Program.findFunction? (program : Program α) (name : String) : Option (Function α) :=
  program.functions.find? (·.name == name)

def Program.findTable? (program : Program α) (name : String) : Option (Table α) :=
  program.tables.find? (·.name == name)

def Program.findMap? (program : Program α) (name : String) : Option MapDecl :=
  program.maps.find? (·.name == name)

def Program.findSignature? (program : Program α) (name : String) : Option Signature :=
  match program.findFunction? name with
  | some fn => some ⟨fn.params, fn.result⟩
  | none => (program.findMap? name).map fun map => ⟨map.params, map.result⟩

/-- Row alignment, rather than independent membership, relates the two traces. -/
def Program.mapRows (program : Program α) (map : MapDecl) : List (Constant α × Constant α) :=
  match program.findTable? map.input, program.findTable? map.output with
  | some inputs, some outputs => inputs.rows.zip outputs.rows
  | _, _ => []

structure MapEntry (α : Type) where
  args : List (Constant α)
  result : Constant α
  deriving Repr, BEq, DecidableEq

/-- A derived view of aligned traces; the program stores each table only once. -/
def Program.mapEntries (program : Program α) (map : MapDecl) : List (MapEntry α) :=
  (program.mapRows map).filterMap fun
    | (.tuple args, result) => some ⟨args, result⟩
    | _ => none

def Pattern.map (f : α → β) : Pattern α → Pattern β
  | .literal x => .literal (f x)
  | .wildcard => .wildcard
  | .bind name => .bind name
  | .tuple items => .tuple (items.map (Pattern.map f))
  | .construct name ctor args => .construct name ctor (args.map (Pattern.map f))
termination_by pattern => sizeOf pattern

/-- Bindings and wildcards accept every value of their checked type. -/
def Pattern.irrefutable (decls : Declarations) : Pattern α → Bool
  | .literal _ => false
  | .wildcard | .bind _ => true
  | .tuple items => (items.map (Pattern.irrefutable decls)).all id
  | .construct name ctor args =>
      match decls.findEnum? name with
      | some ⟨_, [only]⟩ => only.name == ctor && (args.map (Pattern.irrefutable decls)).all id
      | _ => false
termination_by pattern => sizeOf pattern

/-- Ignore binder names when checking duplicate matching conditions. -/
def Pattern.condition : Pattern α → Pattern α
  | .bind _ => .wildcard
  | .tuple items => .tuple (items.map Pattern.condition)
  | .construct name ctor args => .construct name ctor (args.map Pattern.condition)
  | pattern => pattern
termination_by pattern => sizeOf pattern

def Expr.map (f : α → β) : Expr α → Expr β
  | .literal value => .literal (f value)
  | .var name => .var name
  | .tuple items => .tuple (items.map (Expr.map f))
  | .construct name ctor args => .construct name ctor (args.map (Expr.map f))
  | .project value index => .project (value.map f) index
  | .letValue pattern value body => .letValue (pattern.map f) (value.map f) (body.map f)
  | .store value => .store (value.map f)
  | .load pointer => .load (pointer.map f)
  | .hint type key channel => .hint type (key.map f) channel
  | .neg value => .neg (value.map f)
  | .binary op left right => .binary op (left.map f) (right.map f)
  | .assertEq message left right => .assertEq message (left.map f) (right.map f)
  | .call name args => .call name (args.map (Expr.map f))
  | .matchValue scrutinee arms =>
      .matchValue (scrutinee.map f) (arms.map fun arm => (arm.1.map f, arm.2.map f))
termination_by expr => sizeOf expr
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | have h := List.sizeOf_lt_of_mem ‹_ ∈ _›
      first
      | omega
      | cases arm; simp_all only [Prod.mk.sizeOf_spec]; omega

def Function.map (f : α → β) (function : Function α) : Function β :=
  { function with body := function.body.map f }

def Program.map (f : α → β) (program : Program α) : Program β :=
  { program with
    functions := program.functions.map (Function.map f)
    tables := program.tables.map fun table => { table with rows := table.rows.map (Constant.map f) } }

def Program.toField (F : Type) [NatCast F] (program : Program Nat) : Program F :=
  program.map (fun n => (Nat.cast n : F))

/-- A syntactic boundary for the original deterministic fragment. -/
def Expr.noHints : Expr α → Bool
  | .hint _ _ _ => false
  | .literal _ | .var _ => true
  | .tuple items | .construct _ _ items | .call _ items =>
      (items.map Expr.noHints).all id
  | .project value _ | .store value | .load value | .neg value => value.noHints
  | .letValue _ value body | .binary _ value body | .assertEq _ value body => value.noHints && body.noHints
  | .matchValue value arms => value.noHints && (arms.map fun arm => arm.2.noHints).all id
termination_by expr => sizeOf expr
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | have h := List.sizeOf_lt_of_mem ‹_ ∈ _›
      first
      | omega
      | cases arm; simp_all only [Prod.mk.sizeOf_spec]; omega

def Program.noHints (program : Program α) : Bool :=
  (program.functions.map fun function => function.body.noHints).all id

end Aiur
