import Ix.CompileCert.DevelopmentFrames

/-! Actual development calls preserve the conditional cache invariant even
for invalid inputs. This states no output frame validity for those inputs. -/
namespace Ix.CompileCert.DevelopmentState
open Ix (Expr)
open Ix.Compile.Image Ix.Compile.Canon
open SemanticFrames DevelopmentFrames

private def Keeps (action : DevM α) : Prop :=
  ∀ before, InstFrames before → ∀ out after,
    action.run before = .ok (out, after) → InstFrames after

private theorem pureK (value : α) : Keeps (pure value) := by
  intro before good out after run
  cases Except.ok.inj run; exact good

private theorem bindK {first : DevM α} {next : α → DevM β}
    (head : Keeps first) (tail : ∀ value, Keeps (next value)) : Keeps (first >>= next) := by
  intro before good out after run
  rw [StateT.run_bind] at run
  obtain ⟨⟨value, middle⟩, firstRun, nextRun⟩ := Loop.except_bind_ok.mp run
  exact tail value middle (head before good value middle firstRun) out after nextRun

private theorem frameK {action : DevM α} (frame : DevelopmentArity.Frame action) : Keeps action := by
  intro before good out after run
  simpa only [InstFrames, frame run] using good

private theorem getK : Keeps get := by
  intro before good out after run
  cases Except.ok.inj run; exact good

private theorem forInK (xs : List α) (f : α → β → DevM (ForInStep β))
    (step : ∀ x ∈ xs, ∀ b, Keeps (f x b)) : ∀ b, Keeps (forIn xs b f) := by
  induction xs with
  | nil => intro b; exact pureK b
  | cons x xs ih =>
    intro b
    rw [List.forIn_cons]
    apply bindK (step x (by simp) b)
    intro result
    cases result with
    | done value => exact pureK value
    | yield value => exact ih (fun x hx => step x (by simp [hx])) value

private theorem arrayForInK (xs : Array α) (f : α → β → DevM (ForInStep β))
    (step : ∀ x ∈ xs, ∀ b, Keeps (f x b)) (b : β) : Keeps (forIn xs b f) := by
  rw [← Array.forIn_toList]
  exact forInK xs.toList f (by simpa using step) b

private theorem foldK (xs : List α) (f : β → α → DevM β)
    (step : ∀ x ∈ xs, ∀ b, Keeps (f b x)) : ∀ b, Keeps (xs.foldlM f b) := by
  induction xs with
  | nil => intro b; exact pureK b
  | cons x xs ih =>
    intro b
    rw [List.foldlM_cons]
    exact bindK (step x (by simp) b) (fun b => ih (fun x hx => step x (by simp [hx])) b)

private theorem arrayFoldK (xs : Array α) (f : β → α → DevM β)
    (step : ∀ x ∈ xs, ∀ b, Keeps (f b x)) (b : β) : Keeps (xs.foldlM f b) := by
  rw [← Array.foldlM_toList]
  exact foldK xs.toList f (by simpa using step) b

private theorem shareK (e : Expr) : Keeps (share e) :=
  frameK (DevelopmentArity.helperFrames e 0 0).1

private theorem shareAppK (f : Expr) (args : Array Expr) : Keeps (shareAppN f args) := by
  unfold shareAppN
  exact arrayFoldK args _ (fun a _ acc => shareK (Expr.mkApp acc a)) f

/-- Vacuity applies only after identifying the exact stored value/body with
these invalid inputs; an unrelated entry still uses the existing invariant. -/
theorem insert_invalid {state : DevState} (good : InstFrames state) (v e : Expr) (k : Nat)
    (invalid : ¬ (Frames v ∧ Frames e)) (result : Expr × Created) :
    InstFrames { state with insts := state.insts.insert (instBucket v e k) ⟨v, e, k, result⟩ } := by
  intro bucket entry found hv he
  simp only [Std.HashMap.getElem?_insert] at found
  split at found
  · cases Option.some.inj found; exact False.elim (invalid ⟨hv, he⟩)
  · exact good bucket entry found hv he

private theorem doneK (v e : Expr) (k : Nat) (invalid : ¬ (Frames v ∧ Frames e))
    (result : Expr × Created) : Keeps (do
      modify fun state => { state with insts := state.insts.insert (instBucket v e k) ⟨v, e, k, result⟩ }
      pure result) := by
  intro before good out after run
  cases Except.ok.inj run; exact insert_invalid good v e k invalid result

private theorem storeK {v e : Expr} {k : Nat} (invalid : ¬ (Frames v ∧ Frames e))
    {action : DevM Expr} (created : Created) (keep : Keeps action) : Keeps (do
      let out ← action
      modify fun state => { state with insts := state.insts.insert (instBucket v e k) ⟨v, e, k, (out, created)⟩ }
      pure (out, created)) := bindK keep (fun out => doneK v e k invalid (out, created))

private theorem workers (fuel : Nat) :
    (∀ v k e, Keeps (hinst fuel v k e)) ∧ (∀ f args, Keeps (happ fuel f args)) := by
  classical
  induction fuel using Nat.strongRecOn with | ind fuel below =>
  cases fuel with
  | zero =>
    constructor
    · intro _ _ _ _ _ _ _ run; rw [hinst] at run; cases run
    · intro _ _ _ _ _ _ run; rw [happ] at run; cases run
  | succ fuel =>
    have ih := below fuel (Nat.lt_succ_self fuel)
    constructor
    · intro v k e
      by_cases valid : Frames v ∧ Frames e
      · exact fun _ good _ _ run => (DevelopmentFrames.hinst_run _ _ _ _ valid.1 valid.2 good run).1
      · rw [hinst]
        apply bindK (frameK (DevelopmentArity.helperFrames e 0 k).2.2.2.2.1)
        intro range
        split
        · exact pureK _
        · apply bindK getK
          intro state
          cases hit : instProbe state v e k with
          | some result => exact pureK result
          | none =>
            simp only
            cases e with
            | bvar i hash =>
              dsimp only
              split
              · exact storeK valid .direct (frameK (DevelopmentArity.helperFrames v k 0).2.2.1)
              · split
                · exact storeK valid .no (shareK _)
                · exact doneK _ _ _ valid _
            | app f a hash =>
              dsimp only
              rcases getAppFnArgs (.app f a hash) with ⟨head, args⟩
              refine bindK (arrayForInK args _ ?_ #[]) ?_
              · intro a _ es
                exact bindK (ih.1 v k a) (fun _ => pureK _)
              · intro args'
                apply bindK (ih.1 v k head)
                rintro ⟨head', created⟩
                dsimp only
                split
                · exact storeK valid .no (shareAppK _ _)
                · exact storeK valid .reduced (ih.2 _ _)
                · exact storeK valid _ (shareAppK _ _)
            | proj s i x hash =>
              apply bindK (ih.1 v k x)
              rintro ⟨x', created⟩
              dsimp only
              split
              · exact storeK valid .no (shareK _)
              · split
                · exact doneK _ _ _ valid _
                · exact storeK valid .no (shareK _)
            | lam n t b bi hash =>
              apply bindK (ih.1 v k t); rintro ⟨t', created⟩
              apply bindK (ih.1 v (k + 1) b); rintro ⟨b', created⟩
              dsimp only
              split
              · rename_i f hash₁ hash₂
                apply bindK (frameK (DevelopmentArity.helperFrames f 0 0).2.2.2.2.2)
                intro occurs
                split
                · exact storeK valid .direct (frameK (DevelopmentArity.helperFrames f 1 0).2.2.2.1)
                · exact storeK (e := .lam n t b bi hash) valid .no (shareK _)
              · exact storeK (e := .lam n t b bi hash) valid .no (shareK _)
            | forallE n t b bi hash =>
              apply bindK (ih.1 v k t); rintro ⟨t', created⟩
              apply bindK (ih.1 v (k + 1) b); rintro ⟨b', created⟩
              exact storeK valid .no (shareK _)
            | letE n t x b nd hash =>
              apply bindK (ih.1 v k t); rintro ⟨t', created⟩
              apply bindK (ih.1 v k x); rintro ⟨x', created⟩
              apply bindK (ih.1 v (k + 1) b); rintro ⟨b', created⟩
              exact storeK valid .no (shareK _)
            | mdata data x hash =>
              cases x with
              | lam n t b bi hash' =>
                dsimp only
                split
                · cases fuel with
                  | zero => intro _ _ _ _ run; cases run
                  | succ innerFuel =>
                    have inner := (below innerFuel (by omega)).1
                    apply bindK (inner v k t); rintro ⟨t', created⟩
                    apply bindK (inner v (k + 1) b); rintro ⟨b', created⟩
                    apply bindK (shareK _)
                    intro inner'
                    simp only [pure_bind]
                    exact storeK valid .no (shareK _)
                · apply bindK (ih.1 v k _); rintro ⟨inner', created⟩
                  exact storeK valid _ (shareK _)
              | _ =>
                apply bindK (ih.1 v k _); rintro ⟨inner', created⟩
                exact storeK valid _ (shareK _)
            | _ => exact doneK _ _ _ valid _
    · intro f args
      cases f <;> cases args <;> rw [happ.eq_def] <;> dsimp only <;> try exact shareAppK _ _
      rename_i n ty body bi hash a rest
      exact bindK (ih.1 a 0 body) (fun result => ih.2 result.1 rest)

theorem hinst_state (fuel : Nat) (v : Expr) (k : Nat) (e : Expr)
    {before after : DevState} {out : Expr × Created} (good : InstFrames before)
    (run : (hinst fuel v k e).run before = .ok (out, after)) : InstFrames after :=
  (workers fuel).1 v k e before good out after run

theorem happ_state (fuel : Nat) (f : Expr) (args : List Expr)
    {before after : DevState} {out : Expr} (good : InstFrames before)
    (run : (happ fuel f args).run before = .ok (out, after)) : InstFrames after :=
  (workers fuel).2 f args before good out after run

theorem instantiateWith_state (f : Expr) (args : Array Expr)
    {before after : DevState} {out : Expr} (good : InstFrames before)
    (run : instantiateWith before f args = .ok (out, after)) : InstFrames after := by
  have shared : Keeps (args.mapM shareInput) := by
    rw [Array.mapM_eq_foldlM]
    apply arrayFoldK args _ ?_ #[]
    intro a _ acc
    rw [← bind_pure_comp]
    exact bindK (frameK (DevelopmentArity.helperFrames a 0 0).2.1) (fun _ => pureK _)
  exact bindK shared (fun es => (workers developFuel).2 f es.toList) before good out after run

end Ix.CompileCert.DevelopmentState
