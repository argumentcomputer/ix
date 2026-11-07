import Aiur.Generic.EnvironmentFacts
import Aiur.Generic.ControlNoExit

namespace Aiur.Generic.OpenSource
open SourceSemantics Engine
variable [Field F] [DecidableEq F] {world : SourceSemantics.World F} {calls : CallRelation F}

theorem EvalExpr.changeLocals (ev : EvalExpr world calls types locals expr before value after) :
    ∀ other, EnvAgrees (ControlLower.names expr) locals other →
      EvalExpr world calls types other expr before value after := by
  induction ev using EvalExpr.rec
    (motive_2 := fun ts ls es b vs h _ => ∀ other,
      EnvAgrees (es.flatMap ControlLower.names) ls other → EvalArgs world calls ts other es b vs h)
    (motive_3 := fun ts ls e b target v h _ => ∀ other,
      EnvAgrees (ControlLower.names e) ls other → EvalExit world calls ts other e b target v h)
    (motive_4 := fun ts ls es b target v h _ => ∀ other,
      EnvAgrees (es.flatMap ControlLower.names) ls other → EvalArgsExit world calls ts other es b target v h) with
  | block _ ih => intro other agree; exact .block (ih other (by simpa only [ControlLower.names] using agree))
  | blockExit _ ih => intro other agree; exact .blockExit (ih other (by simpa only [ControlLower.names] using agree))
  | global found interpreted ev _ => intro _ _; exact .global found interpreted ev
  | literal => intro _ _; exact .literal
  | var lookup =>
      intro other agree
      exact .var (by rw [← agree _ (by simp [ControlLower.names])]; exact lookup)
  | array _ ih => intro other agree; exact .array (ih other (by simpa only [ControlLower.names] using agree))
  | constructAs _ ih => intro other agree; exact .constructAs (ih other (by simpa only [ControlLower.names] using agree))
  | builtin _ op ih => intro other agree; exact .builtin (ih other (by simpa only [ControlLower.names] using agree)) op
  | update _ op ih => intro other agree; exact .update (ih other (by simpa only [ControlLower.names] using agree)) op
  | record _ ih => intro other agree; exact .record (ih other (by simpa only [ControlLower.names] using agree))
  | «repeat» _ ih => intro other agree; exact .repeat (ih other (by simpa only [ControlLower.names] using agree))
  | index _ op ih => intro other agree; exact .index (ih other (by simpa only [ControlLower.names] using agree)) op
  | slice _ op ih => intro other agree; exact .slice (ih other (by simpa only [ControlLower.names] using agree)) op
  | tuple _ ih => intro other agree; exact .tuple (ih other (by simpa only [ControlLower.names] using agree))
  | construct _ ih => intro other agree; exact .construct (ih other (by simpa only [ControlLower.names] using agree))
  | project _ projected ih => intro other agree; exact .project (ih other (by simpa only [ControlLower.names] using agree)) projected
  | member _ membered ih => intro other agree; exact .member (ih other (by simpa only [ControlLower.names] using agree)) membered
  | letValue _ matched _ ih1 ih2 =>
      intro other agree
      apply EvalExpr.letValue (ih1 other (agree.mono ?_)) matched
      · apply ih2 _ ((agree.mono ?_).prepend _)
        intro n hn
        simp [ControlLower.names, hn]
      · intro n hn
        simp [ControlLower.names, hn]
  | store _ ih => intro other agree; exact .store (ih other (by simpa only [ControlLower.names] using agree))
  | load _ loaded ih => intro other agree; exact .load (ih other (by simpa only [ControlLower.names] using agree)) loaded
  | hint _ typed ih => intro other agree; exact .hint (ih other (by simpa only [ControlLower.names] using agree)) typed
  | neg _ op ih => intro other agree; exact .neg (ih other (by simpa only [ControlLower.names] using agree)) op
  | binary _ _ op ih1 ih2 =>
      intro other agree
      exact .binary (ih1 other (agree.mono (by intros; simp [ControlLower.names, *])))
        (ih2 other (agree.mono (by intros; simp [ControlLower.names, *]))) op
  | call _ callee ih => intro other agree; exact .call (ih other (by simpa only [ControlLower.names] using agree)) callee
  | matchValue _ selected _ ih1 ih2 =>
      intro other agree
      apply EvalExpr.matchValue
        (ih1 other (agree.mono (by intros; simp [ControlLower.names, *]))) selected
      apply ih2 _ ((agree.mono ?_).prepend _)
      intro n hn
      obtain ⟨pat, member⟩ := selected_member selected
      simp only [ControlLower.names, List.mem_append, List.mem_flatMap]
      exact Or.inr ⟨(pat, _), member, by simp [hn]⟩
  | nil => exact .nil
  | cons _ _ ih1 ih2 =>
      rename_i other agree
      exact .cons (ih1 other (agree.mono (by intros; simp [*])))
        (ih2 other (agree.mono (by intros; simp [*])))
  | exit _ ih =>
      rename_i other agree
      exact .exit (ih other (by simpa only [ControlLower.names] using agree))
  | exitPayload _ ih =>
      rename_i other agree
      exact .exitPayload (ih other (by simpa only [ControlLower.names] using agree))
  | fromBlock different _ ih =>
      rename_i other agree
      exact .fromBlock different (ih other (by simpa only [ControlLower.names] using agree))
  | fromGlobal found interpreted ev _ => rename_i other _agree; exact .fromGlobal found interpreted ev
  | fromTuple _ ih =>
      rename_i other agree
      exact .fromTuple (ih other (by simpa only [ControlLower.names] using agree))
  | fromArray _ ih =>
      rename_i other agree
      exact .fromArray (ih other (by simpa only [ControlLower.names] using agree))
  | fromRepeat _ ih =>
      rename_i other agree
      exact .fromRepeat (ih other (by simpa only [ControlLower.names] using agree))
  | fromIndex _ ih =>
      rename_i other agree
      exact .fromIndex (ih other (by simpa only [ControlLower.names] using agree))
  | fromSlice _ ih =>
      rename_i other agree
      exact .fromSlice (ih other (by simpa only [ControlLower.names] using agree))
  | fromConstruct _ ih =>
      rename_i other agree
      exact .fromConstruct (ih other (by simpa only [ControlLower.names] using agree))
  | fromConstructAs _ ih =>
      rename_i other agree
      exact .fromConstructAs (ih other (by simpa only [ControlLower.names] using agree))
  | fromBuiltin _ ih =>
      rename_i other agree
      exact .fromBuiltin (ih other (by simpa only [ControlLower.names] using agree))
  | fromUpdate _ ih =>
      rename_i other agree
      exact .fromUpdate (ih other (by simpa only [ControlLower.names] using agree))
  | fromRecord _ ih =>
      rename_i other agree
      exact .fromRecord (ih other (by simpa only [ControlLower.names] using agree))
  | fromProject _ ih =>
      rename_i other agree
      exact .fromProject (ih other (by simpa only [ControlLower.names] using agree))
  | fromMember _ ih =>
      rename_i other agree
      exact .fromMember (ih other (by simpa only [ControlLower.names] using agree))
  | fromStore _ ih =>
      rename_i other agree
      exact .fromStore (ih other (by simpa only [ControlLower.names] using agree))
  | fromLoad _ ih =>
      rename_i other agree
      exact .fromLoad (ih other (by simpa only [ControlLower.names] using agree))
  | fromHint _ ih =>
      rename_i other agree
      exact .fromHint (ih other (by simpa only [ControlLower.names] using agree))
  | fromNeg _ ih =>
      rename_i other agree
      exact .fromNeg (ih other (by simpa only [ControlLower.names] using agree))
  | fromCall _ ih =>
      rename_i other agree
      exact .fromCall (ih other (by simpa only [ControlLower.names] using agree))
  | fromLetValue _ ih =>
      rename_i other agree
      exact .fromLetValue (ih other (agree.mono (by intros; simp [ControlLower.names, *])))
  | binaryLeft _ ih =>
      rename_i other agree
      exact .binaryLeft (ih other (agree.mono (by intros; simp [ControlLower.names, *])))
  | fromMatchValue _ ih =>
      rename_i other agree
      exact .fromMatchValue (ih other (agree.mono (by intros; simp [ControlLower.names, *])))
  | letBody _ matched _ ih1 ih2 =>
      rename_i other agree
      apply EvalExit.letBody (ih1 other (agree.mono ?_)) matched
      · apply ih2 _ ((agree.mono ?_).prepend _)
        intro n hn
        simp [ControlLower.names, hn]
      · intro n hn
        simp [ControlLower.names, hn]
  | binaryRight _ _ ih1 ih2 =>
      rename_i other agree
      exact .binaryRight (ih1 other (agree.mono (by intros; simp [ControlLower.names, *])))
        (ih2 other (agree.mono (by intros; simp [ControlLower.names, *])))
  | matchBody _ selected _ ih1 ih2 =>
      rename_i other agree
      apply EvalExit.matchBody
        (ih1 other (agree.mono (by intros; simp [ControlLower.names, *]))) selected
      apply ih2 _ ((agree.mono ?_).prepend _)
      intro n hn
      obtain ⟨pat, member⟩ := selected_member selected
      simp only [ControlLower.names, List.mem_append, List.mem_flatMap]
      exact Or.inr ⟨(pat, _), member, by simp [hn]⟩
  | head _ ih =>
      rename_i other agree
      exact .head (ih other (agree.mono (by intros; simp [*])))
  | tail _ _ ih1 ih2 =>
      rename_i other agree
      exact .tail (ih1 other (agree.mono (by intros; simp [*])))
        (ih2 other (agree.mono (by intros; simp [*])))

theorem EvalExit.changeLocals (ev : EvalExit world calls types locals expr before target value after) :
    ∀ other, EnvAgrees (ControlLower.names expr) locals other →
      EvalExit world calls types other expr before target value after := by
  induction ev using EvalExit.rec
    (motive_1 := fun ts ls e b v h _ => ∀ other, EnvAgrees (ControlLower.names e) ls other → EvalExpr world calls ts other e b v h)
    (motive_2 := fun ts ls es b vs h _ => ∀ other,
      EnvAgrees (es.flatMap ControlLower.names) ls other → EvalArgs world calls ts other es b vs h)
    (motive_4 := fun ts ls es b target v h _ => ∀ other,
      EnvAgrees (es.flatMap ControlLower.names) ls other → EvalArgsExit world calls ts other es b target v h) with
  | block _ ih => rename_i other agree; exact .block (ih other (by simpa only [ControlLower.names] using agree))
  | blockExit _ ih => rename_i other agree; exact .blockExit (ih other (by simpa only [ControlLower.names] using agree))
  | global found interpreted ev _ => rename_i _other _agree; exact .global found interpreted ev
  | literal => rename_i _other _agree; exact .literal
  | var lookup =>
      rename_i other agree
      exact .var (by rw [← agree _ (by simp [ControlLower.names])]; exact lookup)
  | array _ ih => rename_i other agree; exact .array (ih other (by simpa only [ControlLower.names] using agree))
  | constructAs _ ih => rename_i other agree; exact .constructAs (ih other (by simpa only [ControlLower.names] using agree))
  | builtin _ op ih => rename_i other agree; exact .builtin (ih other (by simpa only [ControlLower.names] using agree)) op
  | update _ op ih => rename_i other agree; exact .update (ih other (by simpa only [ControlLower.names] using agree)) op
  | record _ ih => rename_i other agree; exact .record (ih other (by simpa only [ControlLower.names] using agree))
  | «repeat» _ ih => rename_i other agree; exact .repeat (ih other (by simpa only [ControlLower.names] using agree))
  | index _ op ih => rename_i other agree; exact .index (ih other (by simpa only [ControlLower.names] using agree)) op
  | slice _ op ih => rename_i other agree; exact .slice (ih other (by simpa only [ControlLower.names] using agree)) op
  | tuple _ ih => rename_i other agree; exact .tuple (ih other (by simpa only [ControlLower.names] using agree))
  | construct _ ih => rename_i other agree; exact .construct (ih other (by simpa only [ControlLower.names] using agree))
  | project _ projected ih => rename_i other agree; exact .project (ih other (by simpa only [ControlLower.names] using agree)) projected
  | member _ membered ih => rename_i other agree; exact .member (ih other (by simpa only [ControlLower.names] using agree)) membered
  | letValue _ matched _ ih1 ih2 =>
      rename_i other agree
      apply EvalExpr.letValue (ih1 other (agree.mono ?_)) matched
      · apply ih2 _ ((agree.mono ?_).prepend _)
        intro n hn
        simp [ControlLower.names, hn]
      · intro n hn
        simp [ControlLower.names, hn]
  | store _ ih => rename_i other agree; exact .store (ih other (by simpa only [ControlLower.names] using agree))
  | load _ loaded ih => rename_i other agree; exact .load (ih other (by simpa only [ControlLower.names] using agree)) loaded
  | hint _ typed ih => rename_i other agree; exact .hint (ih other (by simpa only [ControlLower.names] using agree)) typed
  | neg _ op ih => rename_i other agree; exact .neg (ih other (by simpa only [ControlLower.names] using agree)) op
  | binary _ _ op ih1 ih2 =>
      rename_i other agree
      exact .binary (ih1 other (agree.mono (by intros; simp [ControlLower.names, *])))
        (ih2 other (agree.mono (by intros; simp [ControlLower.names, *]))) op
  | call _ callee ih => rename_i other agree; exact .call (ih other (by simpa only [ControlLower.names] using agree)) callee
  | matchValue _ selected _ ih1 ih2 =>
      rename_i other agree
      apply EvalExpr.matchValue
        (ih1 other (agree.mono (by intros; simp [ControlLower.names, *]))) selected
      apply ih2 _ ((agree.mono ?_).prepend _)
      intro n hn
      obtain ⟨pat, member⟩ := selected_member selected
      simp only [ControlLower.names, List.mem_append, List.mem_flatMap]
      exact Or.inr ⟨(pat, _), member, by simp [hn]⟩
  | nil => exact .nil
  | cons _ _ ih1 ih2 =>
      rename_i other agree
      exact .cons (ih1 other (agree.mono (by intros; simp [*])))
        (ih2 other (agree.mono (by intros; simp [*])))
  | exit _ ih =>
      intro other agree
      exact .exit (ih other (by simpa only [ControlLower.names] using agree))
  | exitPayload _ ih =>
      intro other agree
      exact .exitPayload (ih other (by simpa only [ControlLower.names] using agree))
  | fromBlock different _ ih =>
      intro other agree
      exact .fromBlock different (ih other (by simpa only [ControlLower.names] using agree))
  | fromGlobal found interpreted ev _ => intro other _agree; exact .fromGlobal found interpreted ev
  | fromTuple _ ih =>
      intro other agree
      exact .fromTuple (ih other (by simpa only [ControlLower.names] using agree))
  | fromArray _ ih =>
      intro other agree
      exact .fromArray (ih other (by simpa only [ControlLower.names] using agree))
  | fromRepeat _ ih =>
      intro other agree
      exact .fromRepeat (ih other (by simpa only [ControlLower.names] using agree))
  | fromIndex _ ih =>
      intro other agree
      exact .fromIndex (ih other (by simpa only [ControlLower.names] using agree))
  | fromSlice _ ih =>
      intro other agree
      exact .fromSlice (ih other (by simpa only [ControlLower.names] using agree))
  | fromConstruct _ ih =>
      intro other agree
      exact .fromConstruct (ih other (by simpa only [ControlLower.names] using agree))
  | fromConstructAs _ ih =>
      intro other agree
      exact .fromConstructAs (ih other (by simpa only [ControlLower.names] using agree))
  | fromBuiltin _ ih =>
      intro other agree
      exact .fromBuiltin (ih other (by simpa only [ControlLower.names] using agree))
  | fromUpdate _ ih =>
      intro other agree
      exact .fromUpdate (ih other (by simpa only [ControlLower.names] using agree))
  | fromRecord _ ih =>
      intro other agree
      exact .fromRecord (ih other (by simpa only [ControlLower.names] using agree))
  | fromProject _ ih =>
      intro other agree
      exact .fromProject (ih other (by simpa only [ControlLower.names] using agree))
  | fromMember _ ih =>
      intro other agree
      exact .fromMember (ih other (by simpa only [ControlLower.names] using agree))
  | fromStore _ ih =>
      intro other agree
      exact .fromStore (ih other (by simpa only [ControlLower.names] using agree))
  | fromLoad _ ih =>
      intro other agree
      exact .fromLoad (ih other (by simpa only [ControlLower.names] using agree))
  | fromHint _ ih =>
      intro other agree
      exact .fromHint (ih other (by simpa only [ControlLower.names] using agree))
  | fromNeg _ ih =>
      intro other agree
      exact .fromNeg (ih other (by simpa only [ControlLower.names] using agree))
  | fromCall _ ih =>
      intro other agree
      exact .fromCall (ih other (by simpa only [ControlLower.names] using agree))
  | fromLetValue _ ih =>
      intro other agree
      exact .fromLetValue (ih other (agree.mono (by intros; simp [ControlLower.names, *])))
  | binaryLeft _ ih =>
      intro other agree
      exact .binaryLeft (ih other (agree.mono (by intros; simp [ControlLower.names, *])))
  | fromMatchValue _ ih =>
      intro other agree
      exact .fromMatchValue (ih other (agree.mono (by intros; simp [ControlLower.names, *])))
  | letBody _ matched _ ih1 ih2 =>
      intro other agree
      apply EvalExit.letBody (ih1 other (agree.mono ?_)) matched
      · apply ih2 _ ((agree.mono ?_).prepend _)
        intro n hn
        simp [ControlLower.names, hn]
      · intro n hn
        simp [ControlLower.names, hn]
  | binaryRight _ _ ih1 ih2 =>
      intro other agree
      exact .binaryRight (ih1 other (agree.mono (by intros; simp [ControlLower.names, *])))
        (ih2 other (agree.mono (by intros; simp [ControlLower.names, *])))
  | matchBody _ selected _ ih1 ih2 =>
      intro other agree
      apply EvalExit.matchBody
        (ih1 other (agree.mono (by intros; simp [ControlLower.names, *]))) selected
      apply ih2 _ ((agree.mono ?_).prepend _)
      intro n hn
      obtain ⟨pat, member⟩ := selected_member selected
      simp only [ControlLower.names, List.mem_append, List.mem_flatMap]
      exact Or.inr ⟨(pat, _), member, by simp [hn]⟩
  | head _ ih =>
      rename_i other agree
      exact .head (ih other (agree.mono (by intros; simp [*])))
  | tail _ _ ih1 ih2 =>
      rename_i other agree
      exact .tail (ih1 other (agree.mono (by intros; simp [*])))
        (ih2 other (agree.mono (by intros; simp [*])))

theorem evalExpr_env_iff (agree : EnvAgrees (ControlLower.names expr) locals other) :
    EvalExpr world calls types locals expr before value after ↔ EvalExpr world calls types other expr before value after :=
  ⟨fun h => h.changeLocals other agree, fun h => h.changeLocals locals agree.symm⟩

theorem evalExit_env_iff (agree : EnvAgrees (ControlLower.names expr) locals other) :
    EvalExit world calls types locals expr before target value after ↔ EvalExit world calls types other expr before target value after :=
  ⟨fun h => h.changeLocals other agree, fun h => h.changeLocals locals agree.symm⟩

end Aiur.Generic.OpenSource
