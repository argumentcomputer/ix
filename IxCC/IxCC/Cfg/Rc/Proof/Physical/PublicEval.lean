import IxCC.Cfg.Rc.Proof.Native.CodeContract
import IxCC.Lir.Proof.Run

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native.Spec

/-- A genuine label/layout simulation preserves every non-stuck executable
outcome at the same clock, including timeouts and the full returned memory. -/
theorem program_eval_transfer {source target : Lir.Program}
    {labels : Nat → Lir.Label → Lir.Label → Prop}
    (simulation : Lir.ProgSim source target labels)
    (clock : Nat) (words : List Lir.Word) (memory : X86.Memory) (context : Lir.Word)
    (regular : Lir.eval source clock words memory context ≠ .stuck) :
    Lir.eval target clock words memory context = Lir.eval source clock words memory context := by
  cases entered : Lir.enter source source.main words with
  | none =>
    exact False.elim (regular (by simp [Lir.eval, Lir.State.initial, entered]))
  | some callee =>
    have initialized : Lir.State.initial source words memory context =
        some ({mem := memory, ctx := context, stack := [callee]} : Lir.State) := by
      simp [Lir.State.initial, entered]
    obtain ⟨callee', entered', related⟩ := simulation.enter entered
    have initialized' : Lir.State.initial target words memory context =
        some ({mem := memory, ctx := context, stack := [callee']} : Lir.State) := by
      simp [Lir.State.initial, simulation.main, entered']
    have states : Lir.StateRel labels
        {mem := memory, ctx := context, stack := [callee]}
        {mem := memory, ctx := context, stack := [callee']} :=
      ⟨rfl, rfl, .cons related .nil⟩
    exact (Lir.runs_eval initialized').eq
      (simulation.lockStep.reaches ((Lir.runs_eval initialized) clock) regular states)

/-- Same-clock non-stuck preservation transports any retained value relation
without discarding or reconstructing its physical return witness. -/
theorem eval_transfer_sim {source target : Lir.Program}
    {words : List Lir.Word} {memory : X86.Memory} {context : Lir.Word}
    (transfer : ∀ clock, Lir.eval source clock words memory context ≠ .stuck →
      Lir.eval target clock words memory context = Lir.eval source clock words memory context)
    {run : Nat → Sem.Result Fir.Val} {R : Fir.Val → (List Lir.Word × X86.Memory) → Prop}
    {clockMap : Nat → Nat}
    (simulation : Sem.Sim R clockMap run (fun clock => Lir.eval source clock words memory context)) :
    Sem.Sim R clockMap run (fun clock => Lir.eval target clock words memory context) where
  forward clock regular := by
    obtain ⟨targetClock, related⟩ := simulation.forward clock regular
    by_cases stuck : Lir.eval source targetClock words memory context = .stuck
    · have sourceStuck : run clock = .stuck := (stuck ▸ related).of_stuck
      exact ⟨0, sourceStuck ▸ .stuck⟩
    · exact ⟨targetClock, (transfer targetClock stuck).symm ▸ related⟩
  timeout clock timedOut := by
    rcases simulation.timeout clock timedOut with timeout | ⟨resource, failed⟩
    · exact .inl ((transfer clock (by rw [timeout]; intro h; cases h)).trans timeout)
    · exact .inr ⟨resource, (transfer clock (by rw [failed]; intro h; cases h)).trans failed⟩

private theorem inline_main_upd (l : Layout) (p : Lir.Program) (m : Nat) :
    Inline.inlineProgram l { p with main := m } = { Inline.inlineProgram l p with main := m } := rfl

private theorem pruneReuse_main_upd (l : Layout) (p : Lir.Program) (m : Nat) :
    Prune.pruneUnusedReuse l { p with main := m } = { Prune.pruneUnusedReuse l p with main := m } := rfl

private theorem inlineWrap_main_upd (l : Layout) (p : Lir.Program) (m : Nat) :
    InlineWrappers.inlineProgram l { p with main := m } = { InlineWrappers.inlineProgram l p with main := m } := rfl

private theorem fastDec_main_upd (l : Layout) (p : Lir.Program) (m : Nat) :
    FastDec.install l { p with main := m } = { FastDec.install l p with main := m } := rfl

private theorem pruneDead_main_upd (l : Layout) (p : Lir.Program) (m : Nat) :
    Prune.pruneDeadRuntime l { p with main := m } = { Prune.pruneDeadRuntime l p with main := m } := rfl

/-- Composed 4-pass simulation from `rawPublicProgram` to `inlinedPublicProgram`
(`Inline` + `Prune` → `InlineWrappers` → `FastDec` → `pruneDeadRuntime`), indexed by `splitCriticalEdges`. -/
theorem sim_raw_to_inlined {l : Layout} {funcs : List Lir.Func} {main target : Nat}
    (hlen : funcs.length = l.sourceCount)
    (hok : l.ctors.all (fun c => (Rt.Rc.CellLayout.ofFields c.arity c.tag).ok) = true)
    (htarget : target < l.sourceCount)
    {splitProg : Lir.Program}
    (hsplit : splitProg = (Public.Spec.inlinedPublicProgram l funcs main).splitCriticalEdges)
    (words : List Lir.Word) (memory : X86.Memory) (context : Lir.Word) :
    Sem.Sim Eq (Inline.inlineClock splitProg)
      (fun clock => Lir.eval (Public.Spec.rawPublicProgram l funcs target) clock words memory context)
      (fun clock => Lir.eval (Public.Spec.inlinedPublicProgram l funcs target) clock words memory context) := by
  have hr := Public.Spec.rawPublicProgram_runtimeFuncs hlen target
  have hno := Public.Spec.rawPublicProgram_noRuntimeReuseCalls hlen target
  have hwr := Public.Spec.prunedPublicProgram_wrapperRuntime hlen target
  have hdec := Public.Spec.preDecPublicProgram_decProc hlen target
  have hnoDead := Public.Spec.postDecPublicProgram_noDeadRuntimeCalls hlen target
  have hww := Public.Spec.postDecPublicProgram_noWrapperToWrapperCalls hlen target
  have hszBound := Public.Spec.postDecPublicProgram_deadRuntimeSizeBound hlen hok target
  have inlEq := Public.Spec.inlinedPublicProgram_eq_inline l funcs target hlen
  have hnp : Prune.isPrunableReuse l (Public.Spec.rawPublicProgram l funcs target).main = false := by
    dsimp only [Prune.isPrunableReuse, Public.Spec.rawPublicProgram, rawProgram,
      Layout.isUniqueProc, Layout.init, Layout.incProc]
    exact decide_eq_false fun ⟨h1, _⟩ =>
      Nat.not_lt.mpr (Nat.le_trans (Nat.le_of_lt htarget) (by omega)) h1
  have hmainPost : (Public.Spec.postDecPublicProgram l funcs target).main = target := by
    rw [Public.Spec.postDecPublicProgram, FastDec.install_main, InlineWrappers.inlineProgram_main,
      Prune.pruneUnusedReuse_main]
    rfl
  have hlive : Prune.LiveRuntimeFn l (Public.Spec.postDecPublicProgram l funcs target)
      (Public.Spec.postDecPublicProgram l funcs target).main := by
    rw [hmainPost]
    apply Prune.liveRuntimeFn_of_not_prunable
    unfold Prune.isPrunableDeadRuntime
    rw [decide_eq_false_iff_not]
    simp only [Layout.isUniqueProc, Layout.init, Layout.decProc, Layout.incProc]
    intro h; rcases h with ⟨h1, _⟩ | h1 | ⟨h1, _⟩ | h1 <;> omega
  have hmainEq : Public.Spec.inlinedPublicProgram l funcs target =
      { Public.Spec.inlinedPublicProgram l funcs main with main := target } := by
    have hraw : rawProgram l funcs target = { rawProgram l funcs main with main := target } := rfl
    unfold Public.Spec.inlinedPublicProgram inlinedProgram
    rw [hraw, inline_main_upd, pruneReuse_main_upd, inlineWrap_main_upd, fastDec_main_upd,
      pruneDead_main_upd]
  have hfuel4 : ∀ k, Lir.fuelFor
      (Prune.pruneDeadRuntime l (Public.Spec.postDecPublicProgram l funcs target)) k ≤
      Lir.fuelFor splitProg k := fun k => by
    have hle := Inline.fuelFor_le_split (Public.Spec.inlinedPublicProgram l funcs main) k
    have hsame : Lir.fuelFor (Public.Spec.inlinedPublicProgram l funcs target) k =
        Lir.fuelFor (Public.Spec.inlinedPublicProgram l funcs main) k := by
      rw [hmainEq]; rfl
    rw [← hsplit] at hle
    rw [← hsame, inlEq] at hle
    exact hle
  have hfuel3 : ∀ k, Lir.fuelFor (Public.Spec.postDecPublicProgram l funcs target) k ≤
      256 * Lir.fuelFor splitProg k := fun k =>
    Nat.le_trans (Prune.fuelFor_le_mul_pruneDeadRuntime hszBound k)
      (Nat.mul_le_mul_left 256 (hfuel4 k))
  have hfuel2 : ∀ k, Lir.fuelFor
      (InlineWrappers.inlineProgram l
        (Prune.pruneUnusedReuse l (Inline.inlineProgram l (Public.Spec.rawPublicProgram l funcs target)))) k ≤
      256 * Lir.fuelFor splitProg k := fun k =>
    Nat.le_trans (FastDec.fuelFor_le_install hdec k) (hfuel3 k)
  have hfuel1 : ∀ k, Lir.fuelFor
      (Prune.pruneUnusedReuse l (Inline.inlineProgram l (Public.Spec.rawPublicProgram l funcs target))) k ≤
      256 * Lir.fuelFor splitProg k := fun k =>
    Nat.le_trans (InlineWrappers.fuelFor_le_inlineProgram l _ k) (hfuel2 k)
  have hstepBound12 : ∀ {a b : Nat}, a ≤ 256 * b → ∀ k, k + 12 * a ≤ k + 3072 * b := fun h k => by omega
  have hstepBound3 : ∀ {a b : Nat}, a ≤ 256 * b → ∀ k, k + 3 * a ≤ k + 3072 * b := fun h k => by omega
  have hsim1 := Prune.pruneUnusedReuse_inlineProgram_sim_clock hr hno hnp words memory context
    (f := Inline.inlineStepClock splitProg)
    (fun k => hstepBound12 (hfuel1 k) k)
  have hsim2 := InlineWrappers.inlineProgram_sim_clock hwr words memory context
    (f := Inline.inlineStepClock splitProg)
    (fun k => hstepBound3 (hfuel2 k) k)
  have hsim3 := FastDec.install_sim_clock hdec words memory context
    (f := Inline.inlineStepClock splitProg)
    (fun k => hstepBound3 (hfuel3 k) k)
  have hsim12 := (Sem.Sim.comp (Lir.eval_mono _ words memory context) hsim1 hsim2).mono
    (by rintro _ _ ⟨_, rfl, rfl⟩; rfl)
  have hsim123 : Sem.Sim Eq (Inline.inlineClock splitProg)
      (fun clock => Lir.eval (Public.Spec.rawPublicProgram l funcs target) clock words memory context)
      (fun clock => Lir.eval (Public.Spec.postDecPublicProgram l funcs target) clock words memory context) :=
    (Sem.Sim.comp (Lir.eval_mono _ words memory context) hsim12 hsim3).mono
      (by rintro _ _ ⟨_, rfl, rfl⟩; rfl)
  have hev4 : ∀ k, Lir.eval (Public.Spec.inlinedPublicProgram l funcs target) k words memory context =
      Lir.eval (Public.Spec.postDecPublicProgram l funcs target) k words memory context := fun k => by
    rw [inlEq]
    exact Prune.pruneDeadRuntime_eval_eq hnoDead hww hlive k words memory context
  exact {
    forward := fun k hk => by
      obtain ⟨k', hr'⟩ := hsim123.forward k hk
      exact ⟨k', by rw [hev4 k']; exact hr'⟩
    timeout := fun k hk => by
      rcases hsim123.timeout k hk with hto | ⟨r, hfail⟩
      · exact .inl ((hev4 k).trans hto)
      · exact .inr ⟨r, (hev4 k).trans hfail⟩ }

/-- Accepted public output is the actual composition of source pruning,
source edge splitting, inline RC fast paths, and whole-program edge splitting.
The static code admission and exported main are from the same acceptance receipt. -/
theorem accepted_eval_stages {config : Rt.Config} {F : Fir.Program}
    {bodies : Src.NatMap Own.Plain.Code} {P : Program} {lowered : Public.Lowered}
    {borrows : Own.Plain.BorrowSigs} {uniqs : Own.Plain.UniqSigs}
    (checked : checkScopedProgram F bodies P borrows uniqs = true)
    (accepted : Public.lower config F bodies P borrows uniqs = .ok lowered)
    (hmain : ∀ m : Nat, P.base.exports.head? = some m → m < P.base.size) :
    ∃ main pairs functions,
      CodeAdmission F bodies P config pairs functions borrows uniqs ∧ P.base.exports.head? = some main ∧
      ∀ words memory context,
        Sem.Sim Eq (Inline.inlineClock lowered.runtime.program)
          (fun clock => Lir.eval (Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main)
            clock words memory context)
          (fun clock => Lir.eval lowered.runtime.program clock words memory context) := by
  obtain ⟨original, native, equal, _⟩ := Public.Spec.lower_parts accepted
  obtain ⟨main, pairs, functions, _, switches, entry, hok, consuming, lowering, length, program, _⟩ :=
    Native.Spec.lower_parts native
  have splitEq : lowered.runtime.program =
      (Public.Spec.inlinedPublicProgram (layoutOf P) functions main).splitCriticalEdges := by
    rw [equal]
    exact Public.Spec.assemble_split program
  have split : Lir.ProgSim (Public.Spec.inlinedPublicProgram (layoutOf P) functions main)
      lowered.runtime.program
      (Public.Spec.labels (Public.Spec.inlinedPublicProgram (layoutOf P) functions main)) :=
    splitEq ▸ Public.Spec.program_split _
  have hmainLt : main < (layoutOf P).sourceCount := hmain main entry
  refine ⟨main, pairs, functions, ⟨checked, consuming, lowering, switches⟩, entry, ?_⟩
  intro words memory context
  have stage12 : ∀ clock,
      Lir.eval (Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main)
        clock words memory context ≠ .stuck →
      Lir.eval (Public.Spec.rawPublicProgram (layoutOf P) functions main)
        clock words memory context =
        Lir.eval (Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main)
          clock words memory context := by
    intro clock regular
    have first := program_eval_transfer (Public.Spec.source_raw_pruned lowering main)
      clock words memory context regular
    have second := program_eval_transfer (Public.Spec.source_pruned_split lowering main)
      clock words memory context (by rw [first]; exact regular)
    exact second.trans first
  have hsimInl : Sem.Sim Eq (Inline.inlineClock lowered.runtime.program)
      (fun clock => Lir.eval (Public.Spec.rawPublicProgram (layoutOf P) functions main)
        clock words memory context)
      (fun clock => Lir.eval (Public.Spec.inlinedPublicProgram (layoutOf P) functions main)
        clock words memory context) :=
    sim_raw_to_inlined length hok hmainLt splitEq words memory context
  have hsimInl3 : Sem.Sim Eq (Inline.inlineClock lowered.runtime.program)
      (fun clock => Lir.eval (Public.Spec.rawPublicProgram (layoutOf P) functions main)
        clock words memory context)
      (fun clock => Lir.eval lowered.runtime.program clock words memory context) := {
    forward := fun k hk => by
      obtain ⟨k', hr'⟩ := hsimInl.forward k hk
      by_cases hst : Lir.eval (Public.Spec.inlinedPublicProgram (layoutOf P) functions main)
          k' words memory context = .stuck
      · rw [hst] at hr'
        exact ⟨0, by rw [hr'.of_stuck]; exact .stuck⟩
      · have htr := program_eval_transfer split k' words memory context hst
        exact ⟨k', by rw [htr]; exact hr'⟩
    timeout := fun k hk => by
      rcases hsimInl.timeout k hk with hto | ⟨r, hfail⟩
      · exact .inl ((program_eval_transfer split k words memory context (by rw [hto]; intro h; cases h)).trans hto)
      · exact .inr ⟨r, (program_eval_transfer split k words memory context (by rw [hfail]; intro h; cases h)).trans hfail⟩ }
  exact {
    forward := fun k hk => by
      by_cases hst : Lir.eval (Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main)
          k words memory context = .stuck
      · exact ⟨0, hst ▸ .stuck⟩
      · have heq := stage12 k hst
        obtain ⟨k', hr'⟩ := hsimInl3.forward k (by rw [heq]; exact hk)
        exact ⟨k', heq ▸ hr'⟩
    timeout := fun k hk =>
      hsimInl3.timeout k ((stage12 _ (by rw [hk]; intro h; cases h)).trans hk) }




end IxCC.Cfg.Rc.Native.Spec
