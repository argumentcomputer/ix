import Aiur.Memory.Operations
import Aiur.Memory.Encoding

namespace Aiur

variable {F : Type} {rom : ROM F}

private theorem option_related_some {R : α → β → Prop} {source : Option α} {target : β}
    (related : Option.Rel R source (some target)) : ∃ value, source = some value ∧ R value target := by
  cases related with
  | some relation => exact ⟨_, rfl, relation⟩

/-- A finite evaluation against a functional ROM can be realized by fresh source allocations.
    The proof preserves values through cell contents, without equating the two address spaces. -/
theorem ROMEvalExpr.realize [Field F] [DecidableEq F] (valid : rom.Valid)
    {program : Program F} {locals : Environment F} {expr : Expr F} {target : Value F}
    (evaluated : ROMEvalExpr rom program locals expr target) :
    ∀ heap sourceLocals, RepresentsEnv rom heap sourceLocals locals →
      ∃ source after, EvalExpr program sourceLocals expr heap source after ∧ heap <+: after ∧
        Represents rom after source target := by
  induction evaluated using ROMEvalExpr.rec
    (motive_2 := fun locals exprs targets _ => ∀ heap sourceLocals,
      RepresentsEnv rom heap sourceLocals locals →
      ∃ sources after, EvalArgs program sourceLocals exprs heap sources after ∧ heap <+: after ∧
        RepresentsArgs rom after sources targets)
    (motive_3 := fun name targets result _ => ∀ heap sources,
      RepresentsArgs rom heap sources targets →
      ∃ source after, EvalFn program name sources heap source after ∧ heap <+: after ∧
        Represents rom after source result) with
  | literal => intro heap locals _; exact ⟨_, heap, .literal, List.prefix_refl _, .field⟩
  | var found =>
      intro heap locals related
      obtain ⟨source, lookup, related⟩ := related.lookup found
      exact ⟨source, heap, .var lookup, List.prefix_refl _, related⟩
  | tuple _ ih =>
      intro heap locals related
      obtain ⟨sources, after, evaluated, grows, results⟩ := ih heap locals related
      exact ⟨.tuple sources, after, .tuple evaluated, grows, .tuple results⟩
  | construct _ ih =>
      intro heap locals related
      obtain ⟨sources, after, evaluated, grows, results⟩ := ih heap locals related
      exact ⟨_, after, .construct evaluated, grows, .construct results⟩
  | project _ projected ih =>
      intro heap locals related
      obtain ⟨source, after, evaluated, grows, result⟩ := ih heap locals related
      obtain ⟨value, projected, result⟩ := result.project projected
      exact ⟨value, after, .project evaluated projected, grows, result⟩
  | letValue _ matched _ valueIH bodyIH =>
      intro heap locals related
      obtain ⟨source, middle, valueEval, first, input⟩ := valueIH heap locals related
      obtain ⟨bindings, matchSource, bindingRep⟩ := option_related_some
        (by rw [← matched]; exact Pattern.represents _ input)
      obtain ⟨result, after, bodyEval, second, output⟩ :=
        bodyIH middle (bindings ++ locals) (List.rel_append bindingRep (related.mono first))
      exact ⟨result, after, .letValue valueEval matchSource bodyEval, first.trans second, output⟩
  | store _ cell ih =>
      intro heap locals related
      obtain ⟨source, middle, evaluated, grows, result⟩ := ih heap locals related
      have appends : middle <+: middle ++ [source] := ⟨[source], rfl⟩
      exact ⟨.ptr source.type middle.length, middle ++ [source], .store evaluated,
        grows.trans appends, .ptr (by simp) cell (result.mono appends)⟩
  | load _ cell shape ih =>
      intro heap locals related
      obtain ⟨pointer, after, evaluated, grows, pointerRep⟩ := ih heap locals related
      cases pointerRep with
      | ptr source stored content =>
          have same := ROM.functional valid stored cell shape.symm
          subst_vars
          exact ⟨_, after, .load evaluated (by simp [loadValue, source, pure, Except.pure, bind, Except.bind]), grows, content⟩
  | neg _ operation ih =>
      intro heap locals related
      obtain ⟨source, after, evaluated, grows, result⟩ := ih heap locals related
      obtain ⟨value, operation, result⟩ := result.neg operation
      exact ⟨value, after, .neg evaluated operation, grows, result⟩
  | @hint locals expr input type channel _ constant typed ih =>
      intro heap sourceLocals related
      obtain ⟨key, after, keyEval, grows, _⟩ := ih heap sourceLocals related
      refine ⟨constant.toValue, after, .hint keyEval typed, grows, ?_⟩
      simpa only [Constant.toValue_mapAddress] using
        (Represents.of_pointerFree (rom := rom) (heap := after) constant.toValue
          (Constant.toValue_pointerFree constant) (fun _ => (0 : F)))
  | assertEq _ _ operation leftIH rightIH =>
      intro heap locals related
      obtain ⟨left, middle, leftEval, first, leftRep⟩ := leftIH heap locals related
      obtain ⟨right, after, rightEval, second, rightRep⟩ := rightIH middle locals (related.mono first)
      obtain ⟨value, operation, result⟩ := (leftRep.mono second).assertEq rightRep operation
      exact ⟨value, after, .assertEq leftEval rightEval operation, first.trans second, result⟩
  | @ptrEq locals lhs target a₁ rhs a₂ _ _ leftIH rightIH =>
      intro heap locals related
      obtain ⟨left, middle, leftEval, first, leftRep⟩ := leftIH heap locals related
      obtain ⟨right, after, rightEval, second, rightRep⟩ := rightIH middle locals (related.mono first)
      have leftRepAfter := leftRep.mono second
      generalize hw₁ : Value.ptr target a₁ = w₁ at leftRepAfter
      cases leftRepAfter with
      | field => cases hw₁
      | tuple => cases hw₁
      | construct => cases hw₁
      | @ptr l₁ s₁ _ e₁ h₁ cell₁ c₁ =>
          obtain ⟨hty₁, rfl⟩ := Value.ptr.inj hw₁
          generalize hw₂ : Value.ptr target a₂ = w₂ at rightRep
          cases rightRep with
          | field => cases hw₂
          | tuple => cases hw₂
          | construct => cases hw₂
          | @ptr l₂ s₂ _ e₂ h₂ cell₂ c₂ =>
              obtain ⟨hty₂, rfl⟩ := Value.ptr.inj hw₂
              have hts₁ : s₁.type = target := c₁.type.trans hty₁.symm
              have hts₂ : s₂.type = target := c₂.type.trans hty₂.symm
              have h1 : l₁ < after.length := (List.getElem?_eq_some_iff.mp h₁).1
              have h2 : l₂ < after.length := (List.getElem?_eq_some_iff.mp h₂).1
              have hsound : decide (a₁ = a₂) = true → HeapValueEq after (.ptr target l₁) (.ptr target l₂) := by
                intro hdec
                have haeq : a₁ = a₂ := of_decide_eq_true hdec
                subst haeq
                have hsame := ROM.functional valid cell₁ cell₂ (hty₁.symm.trans hty₂)
                subst hsame
                exact .ptr h₁ h₂ hts₁ hts₂ (Represents.heapValueEq valid c₁ c₂)
              have hres : (if decide (a₁ = a₂) then (1 : F) else 0) = (if a₁ = a₂ then 1 else 0) := by
                by_cases h : a₁ = a₂ <;> simp [h]
              refine ⟨.field (if decide (a₁ = a₂) then 1 else 0), after,
                .ptrEq (hts₁ ▸ leftEval) (hts₂ ▸ rightEval) h1 h2 hsound,
                first.trans second, ?_⟩
              rw [hres]
              exact .field
  | binary _ _ operation leftIH rightIH =>
      intro heap locals related
      obtain ⟨left, middle, leftEval, first, leftRep⟩ := leftIH heap locals related
      obtain ⟨right, after, rightEval, second, rightRep⟩ := rightIH middle locals (related.mono first)
      obtain ⟨value, operation, result⟩ := (leftRep.mono second).binary rightRep operation
      exact ⟨value, after, .binary leftEval rightEval operation, first.trans second, result⟩
  | call _ _ argsIH callIH =>
      intro heap locals related
      obtain ⟨args, middle, argsEval, first, argsRep⟩ := argsIH heap locals related
      obtain ⟨value, after, callEval, second, result⟩ := callIH middle args argsRep
      exact ⟨value, after, .call argsEval callEval, first.trans second, result⟩
  | matchValue _ selected _ valueIH bodyIH =>
      intro heap locals related
      obtain ⟨source, middle, valueEval, first, input⟩ := valueIH heap locals related
      obtain ⟨⟨bindings, body⟩, selectedSource, bindingRep, same⟩ := option_related_some
        (by rw [← selected]; exact selectArm_represents input _)
      dsimp at same
      subst body
      obtain ⟨result, after, bodyEval, second, output⟩ :=
        bodyIH middle (bindings ++ locals) (List.rel_append bindingRep (related.mono first))
      exact ⟨result, after, .matchValue valueEval selectedSource bodyEval, first.trans second, output⟩
  | nil => rename_i heap locals related; exact ⟨[], heap, .nil, List.prefix_refl _, .nil⟩
  | cons _ _ headIH tailIH =>
      rename_i heap locals related
      obtain ⟨head, middle, headEval, first, headRep⟩ := headIH heap locals related
      obtain ⟨tail, after, tailEval, second, tailRep⟩ := tailIH middle locals (related.mono first)
      exact ⟨head :: tail, after, .cons headEval tailEval, first.trans second,
        .cons (headRep.mono second) tailRep⟩
  | intro prepared _ bodyIH =>
      rename_i heap sources related
      obtain ⟨locals, preparedSource, environment⟩ := prepareCall_represents related prepared
      obtain ⟨value, after, evaluated, grows, result⟩ := bodyIH heap locals environment
      exact ⟨value, after, .intro preparedSource evaluated, grows, result⟩

theorem ROMEvalCall.realize [Field F] [DecidableEq F] (valid : rom.Valid)
    {program : Program F} {name : String} {args : List (Value F)} {result : Value F}
    (evaluated : ROMEvalCall rom program name args result)
    {heap : Heap F} {sources : List (SourceValue F)} (related : RepresentsArgs rom heap sources args) :
    ∃ source after, EvalFn program name sources heap source after ∧ heap <+: after ∧
      Represents rom after source result := by
  cases evaluated with
  | intro prepared body =>
      obtain ⟨locals, prepareSource, environment⟩ := prepareCall_represents related prepared
      obtain ⟨source, after, evaluated, grows, output⟩ := body.realize valid heap locals environment
      exact ⟨source, after, .intro prepareSource evaluated, grows, output⟩

end Aiur
