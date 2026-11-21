import Aiur.Generic.ValueTyping
import Aiur.Generic.Simulation

namespace Aiur.Generic

abbrev LocalTypes := List (String × Aiur.Ty)

namespace PatternLowering

def typeListWith (run : A → Aiur.Ty → Option LocalTypes) : List A → List Aiur.Ty → Option LocalTypes
  | [], [] => some []
  | child :: children, type :: types => return (← run child type) ++ (← typeListWith run children types)
  | _, _ => none

/-- Recover user-binding types before eliminating pointer patterns. Temporary
names are irrelevant to this check. -/
def PlanTree.bindTypes (decls : Declarations) : PlanTree F → Aiur.Ty → Option LocalTypes
  | .literal _, .field => some []
  | .literal _, _ => none
  | .wildcard, _ => some []
  | .bind name, type => some [(name, type)]
  | .choice _ left right layout, type => do
      let lbs ← left.bindTypes decls type
      let rbs ← right.bindTypes decls type
      let lhs ← reorderBindings layout.names (List.range layout.names.length) lbs
      let rhs ← reorderBindings layout.names layout.rightOrder rbs
      if lhs = rhs then some lhs else none
  | .load _ child, .ptr target => child.bindTypes decls target
  | .load _ _, _ => none
  | .tuple children, .tuple types =>
      typeListWith (fun child type => child.val.2.bindTypes decls type) children.attach types
  | .tuple _, _ => none
  | .construct name ctor children, .enum actual => do
      if actual != name then none else do
        let definition ← decls.findConstructor? name ctor
        typeListWith (fun child type => child.val.2.bindTypes decls type) children.attach definition.fields
  | .construct _ _ _, _ => none
termination_by tree _ => sizeOf tree
decreasing_by
  all_goals simp_wf
  all_goals first | omega | skip
  all_goals rcases child with ⟨⟨name, tree⟩, member⟩
  all_goals have h := List.sizeOf_lt_of_mem member
  all_goals simp_all only [Prod.mk.sizeOf_spec] <;> omega

end PatternLowering

def Pattern.lowerBindingTypes (decls : Declarations) (types : SourceSemantics.Types)
    (pat : Pattern F) (input : Aiur.Ty) : Option LocalTypes :=
  if Consts.dependencies pat = [] then
    (PatternLowering.planTree types "" pat 0).1.bindTypes decls input
  else none

/-- A decidable typing certificate for lowering. The check follows source
subexpressions and user scopes, while using the existing core typechecker for
their representations. In particular, an empty slice still requires an array
operand and valid static bounds. -/
def Expr.checkLowerTypes (program : Aiur.Program F) (types : SourceSemantics.Types)
    (locals : LocalTypes) (expr : Expr F) : Option Aiur.Ty := do
  let result ← (inferType program "$lower" locals (expr.lower types)).toOption
  if !(Engine.inScope (program.functions.map (·.name) ++ program.maps.map (·.name))
      (knownType program.enums) (expr.lower types)) then none else do
    let checks : Option Unit := match expr with
      | .literal _ | .var _ => some ()
      | .global _ _ | .control _ _ => none
      | .builtin _ children | .update _ children | .record _ children | .tuple children | .array children | .construct _ _ _ children | .constructAs _ _ _ children
        | .call _ _ children => do
          let _ ← children.mapM (Expr.checkLowerTypes program types locals)
          some ()
      | .member child _ | .repeat child _ | .index child _ | .project child _ | .store child | .load child
        | .hint _ child channel | .neg child => do
          let _ ← child.checkLowerTypes program types locals
          some ()
      | .slice _ _ none => none
      | .slice child start (some stop) => do
          let .tuple fields ← child.checkLowerTypes program types locals | none
          if start ≤ stop ∧ stop ≤ fields.length then some () else none
      | .binary _ left right => do
          let _ ← left.checkLowerTypes program types locals
          let _ ← right.checkLowerTypes program types locals
          some ()
      | .letValue pat value body => do
          let input ← value.checkLowerTypes program types locals
          let bindings ← pat.lowerBindingTypes program.enums types input
          let _ ← body.checkLowerTypes program types (bindings ++ locals)
          some ()
      | .matchValue value arms => do
          let input ← value.checkLowerTypes program types locals
          let _ ← arms.mapM fun arm => do
            let bindings ← arm.1.lowerBindingTypes program.enums types input
            arm.2.checkLowerTypes program types (bindings ++ locals)
          some ()
    checks.map (fun _ => result)
termination_by sizeOf expr
decreasing_by
  all_goals simp_wf
  all_goals first | omega | have h := List.sizeOf_lt_of_mem ‹_ ∈ _›
  all_goals try cases ‹Pattern F × Expr F›
  all_goals simp_all only [Prod.mk.sizeOf_spec] <;> omega

end Aiur.Generic
