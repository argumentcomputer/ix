import Ix.Compiler.X86.ScalarNat
import Ix.Compiler.IxIR0.NatRecursors

namespace Ix.Compiler.X86.Scalar.Source
open Ix.Compiler.Ixon (Address)
open Ix.Compiler.IxIR0.Recursion
open Ix.Compiler.IxIR0.NatArithmetic (Represents)
abbrev NatSchema := IxIR0.NatArithmetic.Schema

structure Primitives where
  arithmetic : NatSchema
  addition : Address
  predecessor : Address
  subtraction : Address
  caseRecursor : Address
  caseAlias : Address
  deriving DecidableEq, Repr

structure Primitives.Matches (ctx : IxIR0.Ctx) (primitives : Primitives) : Prop where
  arithmetic : IxIR0.NatArithmetic.Matches ctx primitives.arithmetic
  addition : ctx.env primitives.addition = some (.defn .shared (IxIR0.NatArithmetic.body primitives.arithmetic))
  predecessor : ctx.env primitives.predecessor = some (.defn .shared (IxIR0.NatArithmetic.predBody primitives.arithmetic))
  subtraction : ctx.env primitives.subtraction = some (.defn .shared (IxIR0.NatArithmetic.subBody primitives.arithmetic primitives.predecessor))
  caseRecursor : ctx.env primitives.caseRecursor = some (.recursor 2 true IxIR0.NatArithmetic.caseRules)
  caseAlias : ctx.env primitives.caseAlias = some (.defn .shared (.ref primitives.caseRecursor))

instance (ctx : IxIR0.Ctx) (primitives : Primitives) : Decidable (primitives.Matches ctx) :=
  decidable_of_iff
    (IxIR0.NatArithmetic.Matches ctx primitives.arithmetic ∧
      ctx.env primitives.addition = some (.defn .shared (IxIR0.NatArithmetic.body primitives.arithmetic)) ∧
      ctx.env primitives.predecessor = some (.defn .shared (IxIR0.NatArithmetic.predBody primitives.arithmetic)) ∧
      ctx.env primitives.subtraction = some (.defn .shared (IxIR0.NatArithmetic.subBody primitives.arithmetic primitives.predecessor)) ∧
      ctx.env primitives.caseRecursor = some (.recursor 2 true IxIR0.NatArithmetic.caseRules) ∧
      ctx.env primitives.caseAlias = some (.defn .shared (.ref primitives.caseRecursor)))
    ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩,
      fun h => ⟨h.arithmetic, h.addition, h.predecessor, h.subtraction, h.caseRecursor, h.caseAlias⟩⟩

inductive Binding where
  | var (index : Nat)
  | constant (word : Word)
  deriving DecidableEq, BEq, Repr, Inhabited

def Binding.expression : Binding → IxIR0.Expr
  | .var index => .var index
  | .constant word => IxIR0.NatArithmetic.sharedLiteral word.toNat

def Binding.read (environment : List IxIR0.Value) : Binding → Option IxIR0.Value
  | .var index => environment[index]?
  | .constant word => some (.lit (.nat word.toNat))

def Binding.lift : Binding → Binding
  | .var index => .var (index + 1)
  | .constant word => .constant word

def atom (bindings : Array Binding) : Atom → IxIR0.Expr
  | .var index => (bindings[index]?.map Binding.expression).getD .erased
  | .constant word => IxIR0.NatArithmetic.sharedLiteral word.toNat

def lift (bindings : Array Binding) : Array Binding := bindings.map Binding.lift
def push (bindings : Array Binding) : Array Binding := (lift bindings).push (.var 0)

def expression (primitives : Primitives) (entries : Array Address) : Array Binding → Expr → IxIR0.Expr
  | bindings, .atom value => atom bindings value
  | bindings, .add left right => .app (.app (.ref primitives.addition) (atom bindings left)) (atom bindings right)
  | bindings, .sub left right => .app (.app (.ref primitives.subtraction) (atom bindings left)) (atom bindings right)
  | bindings, .letE value body => .letE .many (expression primitives entries bindings value) (expression primitives entries (push bindings) body)
  | bindings, .branch scrutinee zero successor =>
      .app (.app (.app (.ref primitives.caseAlias)
        (.lam .many (expression primitives entries (lift bindings) zero)))
        (.lam .many (expression primitives entries (lift bindings) successor))) (atom bindings scrutinee)
  | bindings, .call function arguments =>
      match entries[function]? with
      | none => .erased
      | some address => arguments.foldl (fun function argument => .app function (atom bindings argument)) (.ref address)

def parameters : Nat → Array Binding
  | 0 => #[]
  | 1 => #[.var 0]
  | _ + 2 => #[.var 1, .var 0]

def lambda : Nat → IxIR0.Expr → IxIR0.Expr
  | 0, body => body
  | n + 1, body => .lam .many (lambda n body)

def functionBody (primitives : Primitives) (entries : Array Address) (function : Function) : IxIR0.Expr :=
  lambda function.parameters (expression primitives entries (parameters function.parameters) function.body)

structure ProgramMatches (ctx : IxIR0.Ctx) (primitives : Primitives) (entries : Array Address) (program : Program) : Prop where
  matched : primitives.Matches ctx
  size : entries.size = program.functions.size
  functions : ∀ (index : Nat) (function : Function), program.functions[index]? = some function →
    ∃ address, entries[index]? = some address ∧ ctx.env address = some (.defn .shared (functionBody primitives entries function))

structure BindingsRepresent (schema : NatSchema) (environment : List IxIR0.Value) (bindings : Array Binding) (values : Array Nat) : Prop where
  size : bindings.size = values.size
  value : ∀ index (bound : index < values.size),
    ∃ value, (bindings[index]'(by omega)).read environment = some value ∧ Represents schema value values[index]

theorem Binding.evaluates {ctx : IxIR0.Ctx} {environment : List IxIR0.Value} {binding : Binding} {value : IxIR0.Value}
    (read : binding.read environment = some value) : IxIR0.Recursion.Evaluates ctx environment binding.expression value := by
  cases binding with
  | var index => exact evaluatesVar read
  | constant word =>
      cases Option.some.inj read
      exact IxIR0.NatArithmetic.sharedLiteral_evaluates _ _ _

theorem BindingsRepresent.atom {ctx : IxIR0.Ctx} {schema : NatSchema} {environment : List IxIR0.Value}
    {bindings : Array Binding} {values : Array Nat} {source : Atom} {number : Nat}
    (represented : BindingsRepresent schema environment bindings values)
    (found : source.natEval values = some number) :
    ∃ value, IxIR0.Recursion.Evaluates ctx environment (atom bindings source) value ∧ Represents schema value number := by
  cases source with
  | constant word =>
      cases Option.some.inj found
      exact ⟨_, IxIR0.NatArithmetic.sharedLiteral_evaluates _ _ _, .literal _⟩
  | var index =>
      obtain ⟨bound, equal⟩ := Array.getElem?_eq_some_iff.mp found
      obtain ⟨value, read, valueRep⟩ := represented.value index bound
      refine ⟨value, ?_, equal ▸ valueRep⟩
      have bindingBound : index < bindings.size := by have := represented.size; omega
      have located := Array.getElem?_eq_getElem (xs := bindings) bindingBound
      simpa only [Source.atom, located, Option.map_some, Option.getD_some] using (Binding.evaluates (ctx := ctx) read)

theorem BindingsRepresent.lift {schema : NatSchema} {environment : List IxIR0.Value}
    {bindings : Array Binding} {values : Array Nat}
    (represented : BindingsRepresent schema environment bindings values) (newValue : IxIR0.Value) :
    BindingsRepresent schema (newValue :: environment) (lift bindings) values := by
  refine ⟨by simpa [Source.lift] using represented.size, ?_⟩
  intro index bound
  obtain ⟨value, read, valueRep⟩ := represented.value index bound
  refine ⟨value, ?_, valueRep⟩
  simp only [Source.lift, Array.getElem_map]
  cases binding : bindings[index]'(by have := represented.size; omega) <;>
    simpa only [binding, Binding.lift, Binding.read, List.getElem?_cons_succ] using read

theorem BindingsRepresent.push {schema : NatSchema} {environment : List IxIR0.Value}
    {bindings : Array Binding} {values : Array Nat}
    (represented : BindingsRepresent schema environment bindings values) {value : IxIR0.Value} {number : Nat}
    (valueRep : Represents schema value number) :
    BindingsRepresent schema (value :: environment) (push bindings) (values.push number) := by
  have lifted := represented.lift value
  refine ⟨by simp [Source.push, Source.lift, represented.size], ?_⟩
  intro index bound
  by_cases old : index < values.size
  · obtain ⟨previous, read, previousRep⟩ := lifted.value index old
    refine ⟨previous, ?_, ?_⟩
    · have bindingBound : index < (Source.lift bindings).size := by have := lifted.size; omega
      simpa only [Source.push, Array.getElem_push_lt (xs := Source.lift bindings) bindingBound] using read
    · simpa only [Array.getElem_push_lt old] using previousRep
  · have last : index = values.size := by simp only [Array.size_push] at bound; omega
    subst index
    refine ⟨value, ?_, ?_⟩
    · have same : values.size = (Source.lift bindings).size := by simp [Source.lift, represented.size]
      simp only [Source.push, same, Array.getElem_push_eq, Binding.read, List.getElem?_cons_zero]
    · simpa using valueRep

theorem bindings_empty (schema : NatSchema) : BindingsRepresent schema [] (parameters 0) #[] := by
  exact ⟨rfl, by intro index bound; simp at bound⟩

theorem bindings_one {schema : NatSchema} {value : IxIR0.Value} {number : Nat} (represented : Represents schema value number) :
    BindingsRepresent schema [value] (parameters 1) #[number] := by
  refine ⟨rfl, ?_⟩
  intro index bound
  have equal : index = 0 := by simp only [Array.size_singleton] at bound; omega
  subst index
  exact ⟨value, rfl, represented⟩

theorem bindings_two {schema : NatSchema} {left right : IxIR0.Value} {a b : Nat}
    (leftRep : Represents schema left a) (rightRep : Represents schema right b) :
    BindingsRepresent schema [right, left] (parameters 2) #[a, b] := by
  refine ⟨rfl, ?_⟩
  intro index bound
  have alternatives : index = 0 ∨ index = 1 := by change index < 2 at bound; omega
  rcases alternatives with rfl | rfl
  · exact ⟨left, rfl, leftRep⟩
  · exact ⟨right, rfl, rightRep⟩

end Ix.Compiler.X86.Scalar.Source
