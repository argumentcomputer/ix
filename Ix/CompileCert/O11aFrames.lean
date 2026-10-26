import Ix.CompileCert.O11aMinorFrames

/-! Actual O11a output placement and production-hook composition. O2 remains
a concrete unresolved producer call; these results do not assert values. -/
namespace Ix.CompileCert.O11aFrames
open Ix (Name Expr ConstantInfo)
open Ix.CompileM Ix.Compile.Pass Ix.Compile.Pass.Opt
open Ix.Compile.ExactKey (ExactName)
open SemanticFrames OptFrames OptDispatchOrigin

private theorem pattern_ok {α : Type} {input : Option α} {out : α}
    (run : O11aM.pattern input = .ok out) : input = some out := by
  cases input with
  | none => cases run
  | some value => cases Except.ok.inj run; rfl

private theorem push_frames {xs : Array Expr} {x : Expr} (held : ArgsFrames xs) (valid : Frames x) :
    ArgsFrames (xs.push x) := by
  intro y member
  rcases Array.mem_push.mp member with old | rfl
  · exact held y old
  · exact valid

theorem applyWithE_frames (env : OptEnv) (o : Occ) {out : Expr} (held : ArgsFrames o.args)
    (run : O11a.applyWithE env (sizeOfInstanceE env) o = .ok out) : Frames out := by
  unfold O11a.applyWithE at run
  obtain ⟨⟨kind, recName⟩, _, run⟩ := Loop.except_bind_ok.mp run
  dsimp only at run
  by_cases wrong : (kind != AuxKind.kRec) = true
  · rw [ite_eq_left wrong] at run; cases run
  rw [ite_eq_right wrong] at run
  obtain ⟨block, _, run⟩ := Loop.except_bind_ok.mp run
  by_cases wrong : (!block.change.split || block.change.collapse) = true
  · rw [ite_eq_left wrong] at run; cases run
  rw [ite_eq_right wrong] at run
  obtain ⟨shape, _, run⟩ := Loop.except_bind_ok.mp run
  obtain ⟨recursor, _, run⟩ := Loop.except_bind_ok.mp run
  obtain ⟨count, _, run⟩ := Loop.except_bind_ok.mp run
  by_cases short : o.args.size < count
  · rw [ite_eq_left short] at run; cases run
  rw [ite_eq_right short] at run
  obtain ⟨levels, _, run⟩ := Loop.except_bind_ok.mp run
  obtain ⟨motives, selected, run⟩ := Loop.except_bind_ok.mp run
  have motiveGood := pick_frames (extract_frames held shape.np (shape.np + shape.nm)) (pattern_ok selected)
  have minorGood := extract_frames held (shape.np + shape.nm) (shape.np + shape.nm + shape.nmin)
  obtain ⟨result, walked, returned⟩ := Loop.except_bind_ok.mp run
  have adapted : ArgsFrames result.1 := by
    refine Ix.Cert.Claims.forIn_array_inv (fun s : Array Expr × Bool => ArgsFrames s.1) _ _ ?_
      (by simp [ArgsFrames]) walked
    intro item member acc result prior step
    rcases item with ⟨src, term⟩
    cases src
    all_goals simp only [pure_bind] at step
    all_goals try obtain ⟨j, _, step⟩ : ∃ j : Nat, _ := Loop.except_bind_ok.mp step
    all_goals
      obtain ⟨minor, actual, rest⟩ := Loop.except_bind_ok.mp step
      cases minor with
      | some value =>
        have valid := O11aMinorFrames.sizeOfMinor_frames _ _ _ _ _ _ _ _ minorGood actual
        obtain ⟨_, _, rest⟩ := Loop.except_bind_ok.mp rest
        cases rest
        exact push_frames prior valid
      | none =>
        obtain ⟨_, _, rest⟩ := Loop.except_bind_ok.mp rest
        obtain ⟨value, selected, returned⟩ := Loop.except_bind_ok.mp rest
        have valid := minorGood value (Array.mem_of_getElem? (pattern_ok selected))
        cases returned
        exact push_frames prior valid
  split at returned
  · cases returned
  · cases Except.ok.inj returned
    apply mkAppN_frames
    · exact True.intro
    repeat' first | assumption | exact extract_frames held _ _ | apply append_frames

theorem applyWith_frames (env : OptEnv) (o : Occ) {out : Expr} (held : ArgsFrames o.args)
    (run : O11a.applyWith env (sizeOfInstanceE env) o = some out) : Frames out := by
  cases actual : O11a.applyWithE env (sizeOfInstanceE env) o with
  | error error => simp only [O11a.applyWith, actual, Except.toOption] at run; cases run
  | ok value =>
    simp only [O11a.applyWith, actual, Except.toOption] at run
    cases Option.some.inj run
    exact applyWithE_frames env o held actual

theorem O11a_frames (env : OptEnv) (o : Occ) {out : Expr} (held : ArgsFrames o.args)
    (run : O11a.apply env o = some out) : Frames out := by
  unfold O11a.apply at run
  obtain ⟨value, actual, rest⟩ := ImageShape.bind_some run
  split at rest
  · cases rest
  · cases rest; exact applyWith_frames env o held actual

/-- O11a is discharged; the remaining case retains the real recursive O2 call. -/
def OutputCases (fuel : Nat) (env : OptEnv) (o : Occ) (out : Expr) : Prop :=
  Frames out ∨ ∃ reports, O2.apply (OptDispatchOrigin.recur fuel env) env o = some (out, reports)

theorem branch_frames {fuel : Nat} {env : OptEnv} {o : Occ} {tag : String}
    {out : Expr} {reports : Array String} (held : ArgsFrames o.args)
    (branch : Branch fuel env o tag out reports) : OutputCases fuel env o out := by
  rcases OptFrames.branch_frames held branch with valid | actual | pending
  · exact .inl valid
  · exact .inl (O11a_frames env o held actual)
  · exact .inr pending

theorem engineN_frame_cases {fuel : Nat} {env : OptEnv} {o : Occ} {tag : String}
    {out : Expr} {reports : Array String} (held : ArgsFrames o.args)
    (run : engineN (fuel + 1) env o = some (tag, out, reports)) :
    Branch fuel env o tag out reports ∧ OutputCases fuel env o out :=
  ⟨engineN_origin run, branch_frames held (engineN_origin run)⟩

theorem passConfig_frame_cases {cenv : CompileEnv} {views : Std.HashMap ExactName BlockView}
    {sourceAll : Ix.Set Name} {site : Option Name} {name : Name} {levels : Array Ix.Level} {args : Array Expr}
    {out : Expr} {constants : Array ConstantInfo} {proofTag : Option String} {reports : Array String}
    (held : ArgsFrames args)
    (hit : (passConfig cenv views sourceAll).opt? site name levels args = some (out, constants, proofTag, reports)) :
    Ix.AuxGen.SourceIdentity.permitsOptimization cenv.env name = true ∧ constants = #[] ∧ proofTag = none ∧
    ∃ tag, engine (driverEnv cenv views sourceAll) { head := name, us := levels, args, site } = some (tag, out, reports) ∧
      Branch 63 (driverEnv cenv views sourceAll) { head := name, us := levels, args, site } tag out reports ∧
      OutputCases 63 (driverEnv cenv views sourceAll) { head := name, us := levels, args, site } out := by
  obtain ⟨permitted, empty, noProof, tag, actual, branch⟩ := passConfig_origin hit
  exact ⟨permitted, empty, noProof, tag, actual, branch, branch_frames held branch⟩

end Ix.CompileCert.O11aFrames
