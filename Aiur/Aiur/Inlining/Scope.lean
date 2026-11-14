import Aiur.Generic.PatternStepFacts
import Aiur.Generic.EnvironmentFacts

namespace Aiur.Inlining
open Generic Generic.Engine Generic.PatternLowering

def hasScope (names : List String) : Aiur.Expr F → Bool
  | .literal _ => true
  | .var n => names.contains n
  | .tuple xs | .construct _ _ xs | .call _ xs => (xs.map (hasScope names)).all id
  | .project x _ | .store x | .load x | .hint _ x channel | .neg x => hasScope names x
  | .binary _ x y | .assertEq _ x y => hasScope names x && hasScope names y
  | .letValue p x b => hasScope names x && hasScope (patternNames p ++ names) b
  | .matchValue x arms => hasScope names x &&
      (arms.map fun a => hasScope (patternNames a.1 ++ names) a.2).all id
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first | omega | have h := List.sizeOf_lt_of_mem ‹_ ∈ _›; first | omega | cases ‹_ × _›; simp_all only [Prod.mk.sizeOf_spec]; omega

theorem agree_prepend (agree : EnvAgrees names (left : Environment F Nat) right)
    (bs : Environment F Nat) :
    EnvAgrees (bs.map Prod.fst ++ names) (bs ++ left) (bs ++ right) := by
  intro n member
  simp only [List.find?_append]
  cases found : bs.find? (·.1 == n) with
  | some b => rfl
  | none =>
      have absent : n ∉ bs.map Prod.fst := by
        intro h
        obtain ⟨b,hb,same⟩ := List.mem_map.mp h
        have := List.find?_eq_none.mp found b hb
        simp [same] at this
      exact agree n ((List.mem_append.mp member).resolve_left absent)

theorem agree_extension (ls extra : Environment F Nat) : EnvAgrees (ls.map Prod.fst) ls (ls ++ extra) := by
  have := agree_prepend (left := ([] : Environment F Nat)) (right := extra)
    (names := []) (by simp [EnvAgrees]) ls
  simpa using this

theorem selected_hasScope [DecidableEq F] {input : SourceValue F} {arms : List (Aiur.Pattern F × Aiur.Expr F)}
    (chosen : selectArm input arms = some (bs,body))
    (all : ∀ a ∈ arms, hasScope (patternNames a.1 ++ names) a.2 = true) :
    hasScope (bs.map Prod.fst ++ names) body = true := by
  induction arms with
  | nil => simp [selectArm] at chosen
  | cons a rest ih =>
      rcases a with ⟨pat,expr⟩
      cases matched : pat.bindings input with
      | none => exact ih (by simpa [selectArm,matched] using chosen) (by intro a h; exact all a (by simp [h]))
      | some found =>
          obtain ⟨rfl,rfl⟩ := (by simpa [selectArm,matched] using chosen : found = bs ∧ expr = body)
          simpa [bindings_names matched] using all (pat,expr) (by simp)

theorem changeLocals [Field F] [DecidableEq F] {world : Engine.World F}
    (ev : OpenCore.EvalExpr world calls locals expr before result after) :
    ∀ names other, hasScope names expr = true → EnvAgrees names locals other →
      OpenCore.EvalExpr world calls other expr before result after := by
  induction ev using OpenCore.EvalExpr.rec
    (motive_2 := fun ls es b vs a _ => ∀ names other,
      (∀ e ∈ es, hasScope names e = true) → EnvAgrees names ls other →
      OpenCore.EvalArgs world calls other es b vs a) with
  | literal => intros; exact .literal
  | var found =>
      intro names other safe agree
      exact .var (by rw [← agree _ (by simpa [hasScope] using safe)]; exact found)
  | tuple _ ih => intro names other safe agree; exact .tuple (ih names other (by simpa [hasScope] using safe) agree)
  | construct _ ih => intro names other safe agree; exact .construct (ih names other (by simpa [hasScope] using safe) agree)
  | project _ op ih => intro names other safe agree; exact .project (ih names other (by simpa only [hasScope] using safe) agree) op
  | store _ ih => intro names other safe agree; exact .store (ih names other (by simpa only [hasScope] using safe) agree)
  | load _ op ih => intro names other safe agree; exact .load (ih names other (by simpa only [hasScope] using safe) agree) op
  | hint _ op ih => intro names other safe agree; exact .hint (ih names other (by simpa only [hasScope] using safe) agree) op
  | neg _ op ih => intro names other safe agree; exact .neg (ih names other (by simpa only [hasScope] using safe) agree) op
  | binary _ _ op ih1 ih2 =>
      intro names other safe agree
      simp only [hasScope, Bool.and_eq_true] at safe
      have h := safe
      exact .binary (ih1 names other h.1 agree) (ih2 names other h.2 agree) op
  | assertEq _ _ op ih1 ih2 =>
      intro names other safe agree
      simp only [hasScope, Bool.and_eq_true] at safe
      have h := safe
      exact .assertEq (ih1 names other h.1 agree) (ih2 names other h.2 agree) op
  | letValue _ matched _ ih1 ih2 =>
      intro names other safe agree
      simp only [hasScope, Bool.and_eq_true] at safe
      have h := safe
      exact .letValue (ih1 names other h.1 agree) matched
        (ih2 _ _ h.2 (by rw [← bindings_names matched]; exact agree_prepend agree _))
  | call _ called ih => intro names other safe agree; exact .call (ih names other (by simpa [hasScope] using safe) agree) called
  | matchValue _ selected _ ih1 ih2 =>
      intro names other safe agree
      simp only [hasScope, Bool.and_eq_true, List.all_map, List.all_eq_true, Function.comp_def, id_eq] at safe
      exact .matchValue (ih1 names other safe.1 agree) selected
        (ih2 _ _ (selected_hasScope selected safe.2) (agree_prepend agree _))
  | nil => exact .nil
  | cons _ _ ih1 ih2 =>
      rename_i names other safe agree
      exact .cons (ih1 names other (safe _ (by simp)) agree)
        (ih2 names other (by intro e h; exact safe e (by simp [h])) agree)

theorem isolated_iff [Field F] [DecidableEq F] {world : Engine.World F}
    (safe : hasScope (locals.map Prod.fst) expr = true) :
    OpenCore.EvalExpr world calls locals expr b v a ↔
      OpenCore.EvalExpr world calls (locals ++ extra) expr b v a :=
  ⟨fun h => changeLocals h _ _ safe (agree_extension _ _),
   fun h => changeLocals h _ _ safe (agree_extension _ _).symm⟩

end Aiur.Inlining
