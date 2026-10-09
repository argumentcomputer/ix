import Compilatrix.Cfg.Rc.Proof.Native.CodeContract
import Compilatrix.Lir.Proof.Run

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Native.Spec

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

/-- Accepted public output is the actual composition of source pruning,
source edge splitting, and whole-program edge splitting. The static code
admission and exported main are from the same acceptance receipt. -/
theorem accepted_eval_stages {config : Rt.Config} {F : Fir.Program}
    {bodies : Src.NatMap Own.Plain.Code} {P : Program} {lowered : Public.Lowered}
    (checked : checkScopedProgram F bodies P = true)
    (accepted : Public.lower config F bodies P = .ok lowered) :
    ∃ main pairs functions,
      CodeAdmission F bodies P config pairs functions ∧ P.base.exports.head? = some main ∧
      ∀ clock words memory context,
        Lir.eval (Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main)
          clock words memory context ≠ .stuck →
        Lir.eval lowered.runtime.program clock words memory context =
          Lir.eval (Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main)
            clock words memory context := by
  obtain ⟨original, native, equal, _⟩ := Public.Spec.lower_parts accepted
  obtain ⟨main, pairs, functions, _, switches, entry, _, consuming, lowering, length, program, _⟩ :=
    Native.Spec.lower_parts native
  have splitEq : lowered.runtime.program =
      (Public.Spec.rawPublicProgram (layoutOf P) functions main).splitCriticalEdges := by
    rw [equal]
    exact Public.Spec.assemble_split program
  have split : Lir.ProgSim (Public.Spec.rawPublicProgram (layoutOf P) functions main)
      lowered.runtime.program (Public.Spec.labels (Public.Spec.rawPublicProgram (layoutOf P) functions main)) :=
    splitEq ▸ Public.Spec.program_split _
  refine ⟨main, pairs, functions, ⟨checked, consuming, lowering, switches⟩, entry, ?_⟩
  intro clock words memory context regular
  have first := program_eval_transfer (Public.Spec.source_raw_pruned lowering main)
    clock words memory context regular
  have second := program_eval_transfer (Public.Spec.source_pruned_split lowering main)
    clock words memory context (by rw [first]; exact regular)
  have third := program_eval_transfer split clock words memory context
    (by rw [second, first]; exact regular)
  exact third.trans (second.trans first)

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




end Compilatrix.Cfg.Rc.Native.Spec
