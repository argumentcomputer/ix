import Aiur.Generic.Elaborate

namespace Aiur.Generic

private def checkLoadArms [BEq α] (enums : List EnumDecl) (caller : String) :
    List (Pattern α) → List (Pattern α) → Except String Unit
  | [], _ => pure ()
  | pat :: rest, seen => do
      if seen.any (· == pat.condition) then throw s!"duplicate match pattern in '{caller}'"
      if pat.irrefutable enums then return
      checkLoadArms enums caller rest (pat.condition :: seen)

private def hasChoices : Pattern α → Bool
  | .orElse _ _ _ => true
  | .load pat | .repeat pat _ => hasChoices pat
  | .tuple ps | .array ps | .record _ ps | .construct _ _ ps | .constructAs _ _ _ ps =>
      (ps.map hasChoices).any id
  | _ => false
termination_by pat => sizeOf pat

private def alternatives : Pattern α → List (Pattern α)
  | .orElse left right _ => alternatives left ++ alternatives right
  | pat => [pat]

/-- Alternatives remain in the AST. Check their original conditions before
compilation separates their tests, including collisions after field conversion. -/
def checkPatternChoices [BEq α] (caller : String) : Pattern α → Except String Unit
  | .orElse left right _ => do
      let rec unique : List (Pattern α) → List (Pattern α) → Except String Unit
        | [], _ => pure ()
        | pat :: rest, seen => do
            if seen.any (· == pat.condition) then throw s!"duplicate or-pattern alternative in '{caller}'"
            unique rest (pat.condition :: seen)
      unique (alternatives left ++ alternatives right) []
      checkPatternChoices caller left
      checkPatternChoices caller right
  | .load pat | .repeat pat _ => checkPatternChoices caller pat
  | .tuple ps | .array ps | .record _ ps | .construct _ _ ps | .constructAs _ _ _ ps =>
      ps.attach.forM (fun pat => checkPatternChoices caller pat.val)
  | _ => pure ()
termination_by pat => sizeOf pat
decreasing_by
  all_goals simp_wf
  all_goals first | omega | have := List.sizeOf_lt_of_mem pat.property; omega

/-- Late lowering separates native pointer and or-patterns into ordinary matches.
Check original conditions before that happens, including field-literal collisions
when preparation is repeated after `toField`. Conditions following an
irrefutable arm are discarded, as in the core compiler. -/
def checkLoadPatterns [DecidableEq α] (program : Program α) (caller : String) : Expr α → Except String Unit
  | .literal _ | .var _ => pure ()
  | .global _ _ => pure ()
  | .builtin _ xs | .update _ xs | .record _ xs | .tuple xs | .array xs | .construct _ _ _ xs | .constructAs _ _ _ xs | .call _ _ xs => do
      for x in xs do checkLoadPatterns program caller x
  | .member x _ | .control _ x | .project x _ | .index x _ | .slice x _ _ | .repeat x _ | .store x | .load x | .hint _ x channel | .neg x => checkLoadPatterns program caller x
  | .letValue pat x b => do
      let _ : BEq α := ⟨fun x y => decide (x = y)⟩
      checkPatternChoices caller (← inspectPattern program 4096 pat)
      checkLoadPatterns program caller x
      checkLoadPatterns program caller b
  | .binary _ x b => do
      checkLoadPatterns program caller x
      checkLoadPatterns program caller b
  | .matchValue x arms => do
      let _ : BEq α := ⟨fun x y => decide (x = y)⟩
      let patterns ← arms.mapM fun arm => inspectPattern program 4096 arm.1
      patterns.forM (checkPatternChoices caller)
      if patterns.any (fun pat => pat.hasLoads || hasChoices pat) then
        checkLoadArms program.nominals caller patterns []
      checkLoadPatterns program caller x
      for arm in arms do checkLoadPatterns program caller arm.2
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first | omega | have h := List.sizeOf_lt_of_mem ‹_ ∈ _›; try simp_all only [Prod.mk.sizeOf_spec]
  all_goals first | omega | cases ‹_ × _›; simp_all only [Prod.mk.sizeOf_spec]; omega

end Aiur.Generic
