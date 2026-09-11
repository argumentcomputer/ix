import Ix.Compiler.IxIR2.ReuseHeapMapResults
import Ix.Compiler.IxIR2.EvalCounter
import Ix.Compiler.IxIR2.ReservationSteps

/-!
# Logical and physical credit states

The program, block, and instruction positions are identical. Allocation
history relates every register, including old names in suspended callers.
Only live heap locations must be injective. Credits agree in layout and
presence; physical reservations are owned separately across the whole stack.
No relation in this module mentions an optimizer or a rewrite trace.
-/

namespace Ix.Compiler.IxIR2.CreditRefinement

open Eval
open Ix.Compiler.IxIR1.Sim (RValIso RValsIso)
open CallReuse.Sim (MapRel HeapMap)

def MapExtends (before after : Array Nat) : Prop :=
  ∀ {left right}, MapRel before left right → MapRel after left right

theorem MapExtends.refl (mapping : Array Nat) : MapExtends mapping mapping := fun h => h

theorem MapExtends.trans {first middle last : Array Nat}
    (one : MapExtends first middle) (two : MapExtends middle last) :
    MapExtends first last := fun h => two (one h)

theorem MapExtends.push (mapping : Array Nat) (location : Nat) :
    MapExtends mapping (mapping.push location) := fun h => h.push location

inductive CreditRel : Credit → Credit → Prop where
  | absent (layout : LayoutId) :
      CreditRel ⟨layout, .absent⟩ ⟨layout, .absent⟩
  | present (layout : LayoutId) (location : Nat) :
      CreditRel ⟨layout, .present none⟩ ⟨layout, .present (some location)⟩

theorem CreditRel.layout {left right : Credit} (related : CreditRel left right) :
    left.layout = right.layout := by cases related <;> rfl

theorem CreditRel.isPresent {left right : Credit} (related : CreditRel left right) :
    left.isPresent = right.isPresent := by cases related <;> rfl

inductive CreditSlotRel : Option Credit → Option Credit → Prop where
  | consumed : CreditSlotRel none none
  | live {left right : Credit} (credit : CreditRel left right) :
      CreditSlotRel (some left) (some right)

inductive CreditsRel : List (Option Credit) → List (Option Credit) → Prop where
  | nil : CreditsRel [] []
  | cons {left right lefts rights} (head : CreditSlotRel left right)
      (tail : CreditsRel lefts rights) : CreditsRel (left :: lefts) (right :: rights)

theorem CreditsRel.lengths {left right : List (Option Credit)}
    (related : CreditsRel left right) : left.length = right.length := by
  induction related with
  | nil => rfl
  | cons _ _ ih => simp only [List.length_cons, ih]

theorem CreditsRel.get? {left right : List (Option Credit)}
    (related : CreditsRel left right) {index : Nat} {credit : Credit}
    (found : left[index]? = some (some credit)) :
    ∃ target, right[index]? = some (some target) ∧ CreditRel credit target := by
  induction related generalizing index with
  | nil => simp at found
  | cons head tail ih =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          subst_vars
          cases head with
          | live credit => exact ⟨_, rfl, credit⟩
      | succ index => exact ih found

theorem CreditsRel.setNone {left right : List (Option Credit)}
    (related : CreditsRel left right) (index : Nat) :
    CreditsRel (left.set index none) (right.set index none) := by
  induction related generalizing index with
  | nil => simp; exact .nil
  | cons head tail ih =>
      cases index with
      | zero => exact .cons .consumed tail
      | succ index => exact .cons head (ih index)

theorem CreditsRel.append {left right moreLeft moreRight : List (Option Credit)}
    (related : CreditsRel left right) (more : CreditsRel moreLeft moreRight) :
    CreditsRel (left ++ moreLeft) (right ++ moreRight) := by
  induction related with
  | nil => exact more
  | cons head tail ih => exact .cons head ih

theorem CreditsRel.any {left right : List (Option Credit)}
    (related : CreditsRel left right) :
    left.any Option.isSome = right.any Option.isSome := by
  induction related with
  | nil => rfl
  | cons head tail ih => cases head <;> simp [List.any_cons, ih]

theorem CreditsRel.weight {left right : List (Option Credit)}
    (related : CreditsRel left right) :
    left.countP (fun c => c.any Credit.isPresent) =
      right.countP (fun c => c.any Credit.isPresent) := by
  induction related with
  | nil => rfl
  | cons head tail ih =>
      cases head with
      | consumed => simpa using ih
      | live credit => simp only [List.countP_cons, Option.any_some, credit.isPresent, ih]

structure FrameRel (mapping : Array Nat) (left right : Frame) : Prop where
  definition : left.definition = right.definition
  block : left.block = right.block
  pc : left.pc = right.pc
  values : RValsIso (MapRel mapping) left.values.toList right.values.toList
  credits : CreditsRel left.credits.toList right.credits.toList

theorem FrameRel.mono {before after : Array Nat} {left right : Frame}
    (related : FrameRel before left right) (extension : MapExtends before after) :
    FrameRel after left right := { related with values := related.values.mono extension }

theorem FrameRel.advance {mapping : Array Nat} {left right : Frame}
    (related : FrameRel mapping left right) :
    FrameRel mapping { left with pc := left.pc + 1 } { right with pc := right.pc + 1 } :=
  { related with pc := congrArg (· + 1) related.pc }

theorem FrameRel.push {mapping : Array Nat} {left right : Frame}
    (related : FrameRel mapping left right) {leftValue rightValue : RVal}
    (value : RValIso (MapRel mapping) leftValue rightValue) :
    FrameRel mapping { left with values := left.values.push leftValue }
      { right with values := right.values.push rightValue } :=
  { related with values := by simpa using related.values.append (.cons value .nil) }

theorem FrameRel.appendCredit {mapping : Array Nat} {left right : Frame}
    (related : FrameRel mapping left right) {leftValues rightValues : Array RVal}
    (values : RValsIso (MapRel mapping) leftValues.toList rightValues.toList)
    {leftCredit rightCredit : Credit} (credit : CreditRel leftCredit rightCredit) :
    FrameRel mapping
      { left with
        values := left.values ++ leftValues
        credits := left.credits.push (some leftCredit) }
      { right with
        values := right.values ++ rightValues
        credits := right.credits.push (some rightCredit) } :=
  { related with
    values := by simpa using related.values.append values
    credits := by simpa using related.credits.append (.cons (.live credit) .nil) }

theorem FrameRel.entry {mapping : Array Nat} (definition : Function)
    {left right : Array RVal} (values : RValsIso (MapRel mapping) left.toList right.toList) :
    FrameRel mapping { definition, values := left } { definition, values := right } :=
  ⟨rfl, rfl, rfl, values, .nil⟩

inductive ContinuationRel (mapping : Array Nat) : Continuation → Continuation → Prop where
  | resume {left right : Frame} (frames : FrameRel mapping left right) :
      ContinuationRel mapping (.resume left) (.resume right)
  | applyMore {left right : Frame} {leftValues rightValues : Array RVal}
      (frames : FrameRel mapping left right)
      (values : RValsIso (MapRel mapping) leftValues.toList rightValues.toList) :
      ContinuationRel mapping (.applyMore leftValues left) (.applyMore rightValues right)

inductive StackRel (mapping : Array Nat) : List Continuation → List Continuation → Prop where
  | nil : StackRel mapping [] []
  | cons {left right lefts rights} (head : ContinuationRel mapping left right)
      (tail : StackRel mapping lefts rights) : StackRel mapping (left :: lefts) (right :: rights)

theorem ContinuationRel.mono {before after : Array Nat} {left right : Continuation}
    (related : ContinuationRel before left right) (extension : MapExtends before after) :
    ContinuationRel after left right := by
  cases related with
  | resume frames => exact .resume (frames.mono extension)
  | applyMore frames values => exact .applyMore (frames.mono extension) (values.mono extension)

theorem StackRel.mono {before after : Array Nat} {left right : List Continuation}
    (related : StackRel before left right) (extension : MapExtends before after) :
    StackRel after left right := by
  induction related with
  | nil => exact .nil
  | cons head tail ih => exact .cons (head.mono extension) ih

inductive ControlRel (mapping : Array Nat) : Control → Control → Prop where
  | halted {left right : RVal} (values : RValIso (MapRel mapping) left right) :
      ControlRel mapping (.halted left) (.halted right)
  | running {left right : Frame} {leftStack rightStack : List Continuation}
      (frames : FrameRel mapping left right) (stack : StackRel mapping leftStack rightStack) :
      ControlRel mapping (.running left leftStack) (.running right rightStack)

theorem ControlRel.mono {before after : Array Nat} {left right : Control}
    (related : ControlRel before left right) (extension : MapExtends before after) :
    ControlRel after left right := by
  cases related with
  | halted values => exact .halted (values.mono extension)
  | running frames stack => exact .running (frames.mono extension) (stack.mono extension)

end Ix.Compiler.IxIR2.CreditRefinement
