import IxCC.Cfg.Rc.Proof.Physical.PublicInit
import IxCC.Cfg.Rc.Proof.Physical.NumericInputs
import IxCC.Cfg.Rc.Proof.Physical.EntryResult
import IxCC.Cfg.Rc.Proof.Native.PhysicalSimulation

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native.Spec
open IxCC.Cfg.Rc.Proof.Physical.Bridge IxCC.Rt.Rc.Procs

theorem numeric_take_arity (source : Fir.Fun) (numbers : List Nat)
    (enough : source.params.length ≤ numbers.length) :
    (Own.litArgs (numbers.take source.params.length)).length = source.params.length := by
  simp only [Own.litArgs, List.length_map, List.length_take, Nat.min_eq_left enough]

/-- Actual public initialization supplies the empty heap. Numeric driver
arguments then construct ownership, denotations and register words, and the
proved whole-code simulation supplies every initialized entry result. -/
theorem numeric_entry {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
    {config : Rt.Config} {lowered : Public.Lowered}
    (checked : checkScopedProgram F bodies P = true)
    (accepted : Public.lower config F bodies P = .ok lowered)
    {f : Nat} {sourceFunction : Fir.Fun} (sourceLookup : F.fun? f = some sourceFunction)
    {numbers : List Nat} {words : List Lir.Word} (encoded : Rt.natWords numbers = some words)
    (arity : numbers.length = sourceFunction.params.length)
    {size budget context : Lir.Word} {memory : X86.Memory}
    (region : Rt.Proof.RegionOk context size) (readable : Rt.Proof.LirRegion memory context size) :
    ∃ pairs functions left initialized base limit,
      CodeAdmission F bodies P config pairs functions ∧
      (∀ clock, Lir.eval {lowered.runtime.program with main := lowered.runtime.init}
        clock [size, budget] memory context = .ok ([left], initialized)) ∧
      Rt.Proof.InitPost context budget memory initialized ∧
      HeapState P pairs {} (fun _ => none) initialized (fun _ => 0) (Own.litArgs numbers)
        context base base limit size.toNat [] (fun _ => []) ∧
      ∀ clock,
        let lp := Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) f
        ∃ callee, Lir.State.initial lp words initialized context =
            some {mem := initialized, ctx := context, stack := [callee]} ∧
          ResultAt P pairs lp {} (fun _ => none) (fun _ => 0) context base limit size.toNat clock
            {mem := initialized, ctx := context, stack := [callee]} []
            (Fir.run F (clock+1) f (Fir.litArgs numbers)) := by
  obtain ⟨main, pairs, functions, admission, _⟩ := CodeAdmission.of_public checked accepted
  obtain ⟨left, initialized, base, limit, execution, post, emptyHeap⟩ :=
    Public.Spec.initialize_heap accepted pairs region readable
  have heap := emptyHeap.numeric_roots numbers
  obtain ⟨den, balance, represented, compatible⟩ := numeric_inputs (P := P) pairs encoded
  refine ⟨pairs, functions, left, initialized, base, limit, admission, execution, post, heap, ?_⟩
  intro clock
  exact main_entry_result admission (checked_physical admission f clock) sourceLookup den balance
    represented compatible (by simpa only [Own.litArgs, List.length_map] using arity) heap

/-- Unrepresentable driver inputs take the actual driver's resource branch
before initialization or source execution. -/
theorem numeric_input_failure (loaded : Rt.Loaded) (entry : Rt.Entry)
    {numbers : List Nat} (unrepresentable : Rt.natWords numbers = none) (clock : Nat) :
    loaded.call entry numbers clock = .resource .natOverflow := by
  simp only [Rt.Loaded.call, unrepresentable]




end IxCC.Cfg.Rc.Native.Spec
