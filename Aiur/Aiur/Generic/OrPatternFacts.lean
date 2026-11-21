import Aiur.Generic.SourceSemantics
import Aiur.Generic.BindingOrderFacts

namespace Aiur.Generic.SourceSemantics

variable [DecidableEq F] {constant : String → Ty → Except EvalError (Pattern F)}
  {depth : Nat} {types : Types} {heap : Heap F} {value : SourceValue F}
  {left right : Pattern F} {layout : OrBindings} {bindings : Environment F Nat}

/-- First-match choice is local to each or-pattern, including nested choices. -/
theorem match_or_some_iff :
    matchPatternWith constant depth types heap (.orElse left right layout) value = .ok (some bindings) ↔
      (∃ selected,
        matchPatternWith constant depth types heap left value = .ok (some selected) ∧
        reorderBindings layout.names (List.range layout.names.length) selected = some bindings) ∨
      (matchPatternWith constant depth types heap left value = .ok none ∧
        ∃ selected, matchPatternWith constant depth types heap right value = .ok (some selected) ∧
          reorderBindings layout.names layout.rightOrder selected = some bindings) := by
  cases hl : matchPatternWith constant depth types heap left value with
  | error e => simp [matchPatternWith, hl, bind, Except.bind]
  | ok selected =>
      cases selected with
      | some first =>
          cases ordered : reorderBindings layout.names (List.range layout.names.length) first <;>
            simp [matchPatternWith, hl, ordered, bind, Except.bind, pure, Except.pure]
      | none =>
          cases hr : matchPatternWith constant depth types heap right value with
          | error e => simp [matchPatternWith, hl, hr, Except.map, bind, Except.bind]
          | ok selected =>
              cases selected with
              | none => simp [matchPatternWith, hl, hr, Except.map, bind, Except.bind, pure, Except.pure]
              | some second =>
                  cases ordered : reorderBindings layout.names layout.rightOrder second <;>
                    simp [matchPatternWith, hl, hr, ordered, Except.map, bind, Except.bind, pure, Except.pure]

/-- Neither an invalid load nor a malformed binding layout is a failed match. -/
theorem match_or_none_iff :
    matchPatternWith constant depth types heap (.orElse left right layout) value = .ok none ↔
      matchPatternWith constant depth types heap left value = .ok none ∧
      matchPatternWith constant depth types heap right value = .ok none := by
  cases hl : matchPatternWith constant depth types heap left value with
  | error e => simp [matchPatternWith, hl, bind, Except.bind]
  | ok selected =>
      cases selected with
      | some first =>
          cases ordered : reorderBindings layout.names (List.range layout.names.length) first <;>
            simp [matchPatternWith, hl, ordered, bind, Except.bind, pure, Except.pure]
      | none =>
          cases hr : matchPatternWith constant depth types heap right value with
          | error e => simp [matchPatternWith, hl, hr, Except.map, bind, Except.bind]
          | ok selected =>
              cases selected with
              | none => simp [matchPatternWith, hl, hr, Except.map, bind, Except.bind, pure, Except.pure]
              | some second =>
                  cases ordered : reorderBindings layout.names layout.rightOrder second <;>
                    simp [matchPatternWith, hl, hr, ordered, Except.map, bind, Except.bind, pure, Except.pure]

end Aiur.Generic.SourceSemantics
