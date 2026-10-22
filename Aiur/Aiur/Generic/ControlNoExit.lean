import Aiur.Generic.ControlLower
import Aiur.Generic.ConstScopeFacts

namespace Aiur.Generic
open SourceSemantics

theorem Consts.Closed.noControl (closed : Consts.Closed expr) :
    ControlLower.hasControl expr = false := by
  induction closed with
  | literal | global => simp [ControlLower.hasControl]
  | «repeat» _ ih | store _ ih => simpa only [ControlLower.hasControl] using ih
  | record _ ih | tuple _ ih | array _ ih | construct _ ih | constructAs _ ih =>
      simpa [ControlLower.hasControl, List.any_eq_false] using ih

theorem selected_member [DecidableEq F] {world : World F}
    {arms : List (Pattern F × Expr F)}
    (selected : SourceSemantics.selectArm world types heap input arms = .ok (some (bindings, body))) :
    ∃ pat, (pat, body) ∈ arms := by
  induction arms with
  | nil => simp [SourceSemantics.selectArm] at selected
  | cons arm arms ih =>
      rcases arm with ⟨pat, expr⟩
      cases matched : world.matchPattern types heap pat input with
      | error e => simp [SourceSemantics.selectArm, matched, bind, Except.bind] at selected
      | ok bs => cases bs with
        | none =>
            obtain ⟨p, hp⟩ := ih (by simpa [SourceSemantics.selectArm, matched, bind, Except.bind] using selected)
            exact ⟨p, by simp [hp]⟩
        | some bs =>
            have same : bs = bindings ∧ expr = body := by
              simpa [SourceSemantics.selectArm, matched, bind, Except.bind, pure, Except.pure] using selected
            obtain ⟨rfl, rfl⟩ := same
            exact ⟨pat, by simp⟩

namespace OpenSource
variable [Field F] [DecidableEq F] {world : World F} {calls : CallRelation F}

/-- Calls catch their own returns; closed const templates cannot introduce
an exit. Thus only explicit control syntax can exit an expression. -/
theorem EvalExit.hasControl (ev : EvalExit world calls types locals expr before target result after) :
    ControlLower.hasControl expr = false → False := by
  induction ev using EvalExit.rec
    (motive_1 := fun _ _ _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ es _ _ _ _ _ =>
      (∀ e ∈ es, ControlLower.hasControl e = false) → False) with
  | exit | exitPayload | fromBlock => simp [ControlLower.hasControl]
  | fromGlobal _ interpreted _ ih =>
      intro _
      exact ih (Consts.toExpr_closed _ interpreted).noControl
  | fromBuiltin _ ih | fromUpdate _ ih | fromRecord _ ih | fromTuple _ ih | fromArray _ ih | fromConstruct _ ih | fromConstructAs _ ih | fromCall _ ih =>
      intro h
      apply ih
      simpa [ControlLower.hasControl, List.any_eq_false] using h
  | fromMember _ ih | fromRepeat _ ih | fromIndex _ ih | fromSlice _ ih | fromProject _ ih
    | fromStore _ ih | fromLoad _ ih | fromHint _ ih | fromNeg _ ih =>
      simpa only [ControlLower.hasControl] using ih
  | fromLetValue _ ih | binaryLeft _ ih | fromMatchValue _ ih =>
      intro h
      simp only [ControlLower.hasControl, Bool.or_eq_false_iff] at h
      exact ih h.1
  | letBody _ _ _ _ ih | binaryRight _ _ _ ih =>
      intro h
      simp only [ControlLower.hasControl, Bool.or_eq_false_iff] at h
      exact ih h.2
  | matchBody _ selected _ _ ih =>
      intro h
      obtain ⟨pat, member⟩ := selected_member selected
      simp only [ControlLower.hasControl, Bool.or_eq_false_iff,
        List.any_map, List.any_eq_false, Function.comp_def, id_eq] at h
      exact ih (by simpa using h.2 _ member)
  | head _ ih => rename_i h; exact ih (h _ (by simp))
  | tail _ _ _ ih => rename_i h; exact ih (fun e he => h e (by simp [he]))
  | _ => trivial

end OpenSource
end Aiur.Generic
