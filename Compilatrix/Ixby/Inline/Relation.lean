import Compilatrix.Ixby.Inline.Syntax

/-! Structural evidence for every function and block of a candidate image.
The relation allows only ordinary leaf-call contraction; signatures, frame
sizes, block indices, constructors, and the program entry are preserved. -/

namespace Compilatrix.Ixby.Inline

open Ix.Ixby

def Paired (relation : α → β → Prop) : List α → List β → Prop
  | [], [] => True
  | a :: as, b :: bs => relation a b ∧ Paired relation as bs
  | _, _ => False

def OptionPaired (relation : α → β → Prop) : Option α → Option β → Prop
  | none, none => True
  | some a, some b => relation a b
  | _, _ => False

theorem Paired.get {relation : α → β → Prop} {as : List α} {bs : List β}
    (paired : Paired relation as bs) (index : Nat) :
    OptionPaired relation as[index]? bs[index]? := by
  induction as generalizing bs index with
  | nil =>
    cases bs with
    | nil => simp [OptionPaired]
    | cons => contradiction
  | cons a as ih =>
    cases bs with
    | nil => contradiction
    | cons b bs =>
      cases index with
      | zero => exact paired.1
      | succ index => exact ih paired.2 index

theorem Paired.map_eq {relation : α → β → Prop} {as : List α} {bs : List β}
    (paired : Paired relation as bs) (left : α → γ) (right : β → γ)
    (equal : ∀ a b, relation a b → left a = right b) : as.map left = bs.map right := by
  induction as generalizing bs with
  | nil => cases bs <;> simp_all [Paired]
  | cons a as ih =>
    cases bs with
    | nil => contradiction
    | cons b bs => simp [equal a b paired.1, ih paired.2]

inductive InstructionRelated (limits : Limits) (source : Program) (locals : Nat) : Instr → Instr → Prop
  | same (instruction : Instr) : InstructionRelated limits source locals instruction instruction
  | inlineCall (callee : FunctionId) (args : List Operand) (next : BlockId)
      (leaf : Leaf) (replacement : PureOp)
      (body : source.getFunction callee = .ok leaf.function)
      (arity : args.length = leaf.arity)
      (arguments : operandsBound locals args)
      (room : leaf.arity + 1 ≤ limits.locals)
      (substituted : leaf.operation.substitute args = some replacement) :
      InstructionRelated limits source locals
        (.letOp (.call callee args) next) (.letOp replacement.toOp next)

structure BlockRelated (limits : Limits) (source : Program) (left right : Block) : Prop where
  locals : left.locals = right.locals
  instruction : InstructionRelated limits source left.locals left.instruction right.instruction

structure FunctionRelated (limits : Limits) (source : Program) (left right : Function) : Prop where
  arity : left.arity = right.arity
  entry : left.entry = right.entry
  blocks : Paired (BlockRelated limits source) left.blocks.toList right.blocks.toList

structure ProgramRelated (limits : Limits) (source target : Program) : Prop where
  entry : source.entry = target.entry
  constructors : source.constructors = target.constructors
  functions : Paired (FunctionRelated limits source) source.functions.toList target.functions.toList

/-- Evidence is indexed by both complete images and the exact semantic limits.
The protected prefix is compared as complete functions, including dead blocks. -/
structure Certificate (limits : Limits) (source target : Program) (protectedPrefix : Nat) : Type where
  sourceAdmitted : validateProgram limits source = .ok ()
  targetAdmitted : validateProgram limits target = .ok ()
  relation : ProgramRelated limits source target
  protectedBodies : source.functions.toList.take protectedPrefix = target.functions.toList.take protectedPrefix

end Compilatrix.Ixby.Inline
