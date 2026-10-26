import Ix.CompileCert.SemanticPresence
import Ix.Compile.Pass.Translate

/-! Successful receipts from the literal frontend prefix and development
call. The frame result concerns the same prepared source constants. Current
environment, optimizer/image suppliers and compiled output are separate
obligations. The atomic development receipt supplies no carried history. -/

namespace Ix.CompileCert.FrontendReceipts
open Ix.CompileM
open SemanticPresence

private theorem bind_ok {α β : Type} (first : IO α) (next : α → IO β)
    (world world' : Void IO.RealWorld) (out : β)
    (run : (first >>= next) world = .ok out world') :
    ∃ value middle, first world = .ok value middle ∧ next value middle = .ok out world' := by
  simp only [bind, instMonadEIO._aux_13, EST.bind] at run
  cases step : first world with
  | ok value middle => exact ⟨value, middle, rfl, by simpa only [step] using run⟩
  | error error middle => simp only [step] at run; cases run

private theorem pure_ok {α : Type} {value out : α} {world world' : Void IO.RealWorld}
    (run : (pure value : IO α) world = .ok out world') : value = out ∧ world = world' := by
  simpa only [pure, instMonadEIO._aux_5, EST.pure, EST.Out.ok.injEq] using run

/-- The actual early-return loop either returns a specific inner error or
visits every member successfully. No later IO continuation is constrained. -/
private theorem prefix_loop {α β : Type} (sources : List α) (good : α → Prop)
    (body : α → Option (Except String β) × Unit →
      IO (ForInStep (Option (Except String β) × Unit)))
    (step : ∀ source,
      (good source ∧ body source (none, ()) = pure (.yield (none, ()))) ∨
      ∃ error, body source (none, ()) = pure (.done (some (.error error), ())))
    {world world' : Void IO.RealWorld} {result : Option (Except String β) × Unit}
    (run : (forIn sources (none, ()) body) world = .ok result world') :
    (result = (none, ()) ∧ ∀ source ∈ sources, good source) ∨
    ∃ error, result = (some (.error error), ()) := by
  induction sources generalizing world world' result with
  | nil =>
    rw [List.forIn_nil] at run
    exact .inl ⟨(pure_ok run).1.symm, by simp only [List.not_mem_nil, false_implies, implies_true]⟩
  | cons source sources ih =>
    rw [List.forIn_cons] at run
    obtain ⟨item, middle, head, tail⟩ := bind_ok _ _ _ _ _ run
    rcases step source with ⟨valid, next⟩ | ⟨error, next⟩
    · rw [next] at head
      obtain ⟨rfl, rfl⟩ := pure_ok head
      rcases ih tail with ⟨rfl, all⟩ | refused
      · exact .inl ⟨rfl, by simpa only [List.mem_cons, forall_eq_or_imp] using And.intro valid all⟩
      · exact .inr refused
    · rw [next] at head
      obtain ⟨rfl, rfl⟩ := pure_ok head
      exact .inr ⟨error, (pure_ok tail).1.symm⟩

theorem compileLeanInput_prefix (input : Ix.Compile.CompileInput)
    (rustRef : Option (Std.HashMap Ix.Name Address)) (workers : Nat) (opts : DriverOptions)
    {world world' : Void IO.RealWorld} {out : LeanPipelineOut}
    (run : compileLeanInput input rustRef workers opts world = .ok (.ok out) world') :
    ∃ sources, input.prepare = .ok sources ∧
      compileDecoratedConsts sources rustRef workers opts world = .ok (.ok out) world' := by
  cases validated : (opts.auxIxc.getD {}).validate with
  | error error =>
    simp only [compileLeanInput, validated] at run
    have invalid := (pure_ok run).1
    cases invalid
  | ok valid =>
    cases prepared : input.prepare with
    | error error =>
      simp only [compileLeanInput, validated, prepared] at run
      have invalid := (pure_ok run).1
      cases invalid
    | ok sources =>
      refine ⟨sources, rfl, ?_⟩
      simpa only [compileLeanInput, validated, prepared, bind, pure, instMonadEIO._aux_13,
        instMonadEIO._aux_5, EST.bind, EST.pure] using run

theorem compileDecoratedConsts_guards (sources : List (Lean.Name × Lean.ConstantInfo))
    (rustRef : Option (Std.HashMap Ix.Name Address)) (workers : Nat) (opts : DriverOptions)
    {world world' : Void IO.RealWorld} {out : LeanPipelineOut}
    (run : compileDecoratedConsts sources rustRef workers opts world = .ok (.ok out) world') :
    ∀ name source, (name, source) ∈ sources →
      Ix.Compile.sourceHasAnnotations source = false ∧ inspectSemanticSource source = .ok () := by
  cases validated : (opts.auxIxc.getD {}).validate with
  | error error =>
    simp only [compileDecoratedConsts, validated] at run
    have invalid := (pure_ok run).1
    cases invalid
  | ok valid =>
    simp only [compileDecoratedConsts, validated] at run
    obtain ⟨result, middle, scan, rest⟩ := bind_ok _ _ _ _ _ run
    have visited := prefix_loop sources (fun entry =>
      Ix.Compile.sourceHasAnnotations entry.2 = false ∧ inspectSemanticSource entry.2 = .ok ()) _ ?_ scan
    · rcases visited with ⟨_, all⟩ | ⟨error, rfl⟩
      · exact fun name source member => all (name, source) member
      · have invalid := (pure_ok rest).1
        cases invalid
    · intro ⟨name, source⟩
      cases annotations : Ix.Compile.sourceHasAnnotations source with
      | true => exact .inr ⟨s!"unresolved source binder contracts: {name}", rfl⟩
      | false =>
        cases inspected : inspectSemanticSource source with
        | error error => exact .inr ⟨error, rfl⟩
        | ok result => cases result; exact .inl ⟨⟨rfl, rfl⟩, rfl⟩

theorem compileLeanInput_members (input : Ix.Compile.CompileInput)
    (rustRef : Option (Std.HashMap Ix.Name Address)) (workers : Nat) (opts : DriverOptions)
    {world world' : Void IO.RealWorld} {out : LeanPipelineOut}
    (run : compileLeanInput input rustRef workers opts world = .ok (.ok out) world') :
    ∃ sources, input.prepare = .ok sources ∧ ∀ name source, (name, source) ∈ sources →
      Ix.Compile.sourceHasAnnotations source = false ∧
      ∃ receipt : PreparedMember input name source, receipt.sources = sources := by
  obtain ⟨sources, prepared, compiled⟩ := compileLeanInput_prefix _ _ _ _ run
  refine ⟨sources, prepared, fun name source member => ?_⟩
  obtain ⟨absent, accepted⟩ := compileDecoratedConsts_guards _ _ _ _ compiled name source member
  exact ⟨absent, ⟨⟨sources, prepared, member, accepted⟩, rfl⟩⟩

theorem compileLeanInput_frames (input : Ix.Compile.CompileInput)
    (rustRef : Option (Std.HashMap Ix.Name Address)) (workers : Nat) (opts : DriverOptions)
    {world world' : Void IO.RealWorld} {out : LeanPipelineOut}
    (run : compileLeanInput input rustRef workers opts world = .ok (.ok out) world') :
    ∃ sources, input.prepare = .ok sources ∧ ∀ name source, (name, source) ∈ sources →
      ∀ cache : Ix.CanonM.CanonState,
        ConstFrames (Id.run ((Ix.CanonM.canonConst source).run cache)).1 := by
  obtain ⟨sources, prepared, members⟩ := compileLeanInput_members _ _ _ _ run
  refine ⟨sources, prepared, fun name source member cache => ?_⟩
  obtain ⟨_, receipt, _⟩ := members name source member
  exact prepared_member_frames receipt cache

/-- This is the literal atomic block in `Pass.rw`. The captured `before.dev`
is the helper input; its temporary replacement by `{}` is not a fresh run. -/
theorem development_call (f : Ix.Expr) (args : Array Ix.Expr) (cfg : Ix.Compile.Pass.RwConfig)
    (before after : Ix.Compile.Pass.RwState) (out : Ix.Expr)
    (run : ((do
      let dev0 := (← get).dev
      modify fun st => { st with dev := {} }
      let (body, dev) ← liftM (Ix.Compile.Image.instantiateWith dev0 f args)
      modify fun st => { st with dev }
      pure body : Ix.Compile.Pass.RwM Ix.Expr) cfg).run before = .ok (out, after)) :
    ∃ dev, Ix.Compile.Image.instantiateWith before.dev f args = .ok (out, dev) ∧
      after = { before with dev } := by
  dsimp [StateT.run, bind, ReaderT.bind, StateT.bind, pure, ReaderT.pure,
    StateT.pure, get, getThe, MonadStateOf.get, MonadStateOf.modifyGet,
    modify, modifyGet, liftM, monadLift, MonadLift.monadLift, StateT.get,
    StateT.modifyGet, StateT.lift, Except.bind, Except.pure] at run
  cases call : Ix.Compile.Image.instantiateWith before.dev f args with
  | error error => simp only [call] at run; cases run
  | ok result =>
    rcases result with ⟨body, dev⟩
    simp only [call] at run
    obtain ⟨rfl, rfl⟩ := Except.ok.inj run
    exact ⟨dev, rfl, rfl⟩

end Ix.CompileCert.FrontendReceipts
