import Compilatrix.Ixby.Inline.Relation

namespace Compilatrix.Ixby.Inline

open Ix.Ixby

private instance : DecidableEq Function := fun left right =>
  decidable_of_iff (left.arity = right.arity ∧ left.entry = right.entry ∧ left.blocks = right.blocks)
    (by cases left; cases right; simp [Function.mk.injEq])

private def checkPaired (relation : α → β → Prop)
    (check : (a : α) → (b : β) → Except String (PLift (relation a b))) :
    (as : List α) → (bs : List β) → Except String (PLift (Paired relation as bs))
  | [], [] => .ok ⟨True.intro⟩
  | a :: as, b :: bs => do
    let first ← check a b
    let rest ← checkPaired relation check as bs
    return ⟨first.down, rest.down⟩
  | [], _ :: _ => .error "inline certificate: extra candidate entries"
  | _ :: _, [] => .error "inline certificate: missing candidate entries"

private def checkInstruction (limits : Limits) (source : Program) (locals : Nat)
    (before after : Instr) : Except String (PLift (InstructionRelated limits source locals before after)) := do
  if same : before = after then return ⟨same ▸ .same before⟩
  match original : before, candidate : after with
  | .letOp (.call callee args) next, .letOp operation target =>
    if targetEq : target = next then
      match recognize source callee with
      | none => throw "inline certificate: callee is outside the leaf fragment"
      | some leaf =>
        let body ← match found : source.getFunction callee with
          | .error _ => throw "inline certificate: missing callee"
          | .ok actual =>
            if equal : actual = leaf.function then pure (PLift.up (equal ▸ found))
            else throw "inline certificate: complete callee body differs"
        do
          if arity : args.length = leaf.arity then
            if arguments : operandsBound locals args then
              if room : leaf.arity + 1 ≤ limits.locals then
                match substituted : leaf.operation.substitute args with
                | none => throw "inline certificate: invalid leaf operand substitution"
                | some replacement =>
                  if equal : replacement.toOp = operation then
                    return ⟨by
                      rw [original, candidate]
                      subst target operation
                      exact .inlineCall callee args next leaf replacement body.down arity arguments room substituted⟩
                  else throw "inline certificate: substituted operation differs"
              else throw "inline certificate: callee exceeds the local-frame limit"
            else throw "inline certificate: unreadable call argument"
          else throw "inline certificate: call arity differs"
    else throw "inline certificate: continuation target differs"
  | _, _ => throw "inline certificate: unsupported instruction change"

private def checkBlock (limits : Limits) (source : Program) (before after : Block) :
    Except String (PLift (BlockRelated limits source before after)) := do
  if locals : before.locals = after.locals then
    let instruction ← checkInstruction limits source before.locals before.instruction after.instruction
    return ⟨locals, instruction.down⟩
  else throw "inline certificate: block locals differ"

private def checkFunction (limits : Limits) (source : Program) (before after : Function) :
    Except String (PLift (FunctionRelated limits source before after)) := do
  if arity : before.arity = after.arity then
    if entry : before.entry = after.entry then
      let blocks ← checkPaired (BlockRelated limits source) (checkBlock limits source)
        before.blocks.toList after.blocks.toList
      return ⟨arity, entry, blocks.down⟩
    else throw "inline certificate: function entry differs"
  else throw "inline certificate: function arity differs"

/-- Validate the original and candidate independently, then check every proposed
rewrite. The optimizer, Boolean recognizer, and execution measurements supply
no trusted equality or semantic premise to this checker. -/
def check (limits : Limits) (source target : Program) (protectedPrefix : Nat := 0) :
    Except String (Certificate limits source target protectedPrefix) := do
  match sourceAdmitted : validateProgram limits source with
  | .error error => throw s!"inline certificate: original image admission: {reprStr error}"
  | .ok () =>
    match targetAdmitted : validateProgram limits target with
    | .error error => throw s!"inline certificate: candidate image admission: {reprStr error}"
    | .ok () =>
      if entry : source.entry = target.entry then
        if constructors : source.constructors = target.constructors then
          if protectedBodies : source.functions.toList.take protectedPrefix = target.functions.toList.take protectedPrefix then
            let functions ← checkPaired (FunctionRelated limits source) (checkFunction limits source)
              source.functions.toList target.functions.toList
            return { sourceAdmitted, targetAdmitted, relation := ⟨entry, constructors, functions.down⟩, protectedBodies }
          else throw "inline certificate: protected complete function bodies differ"
        else throw "inline certificate: constructor declarations differ"
      else throw "inline certificate: program entry differs"

end Compilatrix.Ixby.Inline
