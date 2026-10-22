import Aiur.Optimized.Compile
import Aiur.Circuit.PatternEncoding

namespace Aiur.Optimized.Compiler

variable {F : Type}

theorem bind_ok {first : Build F α} {next : α → Build F β}
    {before after : State F} {result : β} :
    (first >>= next) before = .ok (result, after) ↔
      ∃ value middle, first before = .ok (value, middle) ∧ next value middle = .ok (result, after) := by
  cases run : first before with
  | error error => simp [StateT.bind, bind, Except.bind, run]
  | ok output =>
      rcases output with ⟨value, middle⟩
      simp [StateT.bind, bind, Except.bind, run]

@[simp] theorem pure_ok {value result : α} {before after : State F} :
    (pure value : Build F α) before = .ok (result, after) ↔ value = result ∧ before = after := by
  simp [pure, StateT.pure, Except.pure]

@[simp] theorem lift_ok (value : α) (state : State F) :
    (liftM (.ok value : Except String α) : Build F α) state = .ok (value, state) := rfl

@[simp] theorem lift_error (error : String) (state : State F) :
    (liftM (.error error : Except String α) : Build F α) state = .error error := rfl

@[simp] theorem throw_apply (error : String) (state : State F) :
    (throw error : Build F α) state = .error error := rfl

theorem getLayout_eq {decls : Declarations} {type : Ty} {layout : Layout} {before after : State F}
    (compiled : getLayout decls type before = .ok (layout, after)) :
    decls.layout type = .ok layout ∧ before = after := by
  cases expanded : decls.layout type with
  | error error => simp [getLayout, expanded, Except.mapError] at compiled
  | ok result =>
      simp only [getLayout, expanded, Except.mapError, lift_ok, Except.ok.injEq, Prod.mk.injEq] at compiled
      rcases compiled with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩

/-- Both compilers use the same static slicing operation. This bridge reuses
the existing canonical tuple/enum decoding lemmas. -/
theorem splitValues_reference {decls : Declarations} {types : List Ty} {words : List α}
    {values : List (WireValue α)} {before after : State F}
    (compiled : splitValues decls types words before = .ok (values, after)) :
    after = before ∧ ∀ state : Circuit.Compiler.BuildState F,
      Circuit.Compiler.splitValues decls types words state = .ok (values, state) := by
  induction types generalizing words values before with
  | nil => cases words with
    | nil =>
        obtain ⟨rfl, rfl⟩ := pure_ok.mp compiled
        exact ⟨rfl, fun _ => rfl⟩
    | cons => simp [splitValues] at compiled
  | cons type types ih =>
      simp only [splitValues] at compiled
      obtain ⟨layout, middle, expanded, rest⟩ := bind_ok.mp compiled
      obtain ⟨expansion, rfl⟩ := getLayout_eq expanded
      split at rest
      · simp [StateT.bind, bind, Except.bind] at rest
      · rename_i width
        obtain ⟨⟨⟩, middle, unchanged, rest⟩ := bind_ok.mp rest
        obtain ⟨_, rfl⟩ := pure_ok.mp unchanged
        obtain ⟨tail, last, tailRun, finished⟩ := bind_ok.mp rest
        obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
        obtain ⟨rfl, tailReference⟩ := ih tailRun
        refine ⟨rfl, fun state => ?_⟩
        simp [Circuit.Compiler.splitValues, Circuit.Compiler.getLayout, expansion, Except.mapError,
          StateT.bind, bind, Except.bind, width, StateT.pure, pure, Except.pure, tailReference]

end Aiur.Optimized.Compiler
