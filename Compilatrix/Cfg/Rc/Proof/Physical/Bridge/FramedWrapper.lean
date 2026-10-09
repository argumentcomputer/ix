import Compilatrix.Cfg.Rc.Proof.Physical.Bridge.Decrement
import Compilatrix.Cfg.Rc.Proof.Physical.DecWrapper
import Compilatrix.Rt.Rc.Proof.FrameReleaseCaller

/-! Draft companion, not registered in the first frozen gate. This extends
the existing exact wrapper trace with H2's protectedBytes-byte frame and derives
the consumed token from the source boundary. It still begins at wrapper entry;
the consumed source instruction/caller cursor binding is a separate interface. -/
set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Proof.Physical.Bridge
open Compilatrix Compilatrix.Own Compilatrix.Own.Rc
open Compilatrix.Rt.Rc.Procs
open Compilatrix.Cfg.Rc.Native

theorem wrapper_framed
    {H : Heap} {addresses : AddressMap} {mem : X86.Memory} {external : Nat → Nat}
    {value : RVal} {context base bump limit : Lir.Word}
    {slots : List Slot} {lists : Nat → List Lir.Word}
    (idle : ReleaseInvariant H addresses mem
      (fun location => external location + refsIn location [value]) none []
      context base bump limit slots lists)
    {word : Lir.Word} (represented : valueWord addresses value = some word)
    {P : Lir.Program} {wrapper procedure dummy : Nat} {env : Lir.Env}
    (wrapperLookup : P.funcs[wrapper]? = some (decrementWrapper procedure))
    (procedureLookup : P.funcs[procedure]? = some dec)
    (argument : env[0]? = some word)
    (caller : Lir.Frame) (callers : List Lir.Frame) (destination : caller.dsts = [dummy]) :
    ∃ H' mem' slots' lists' charges,
      dropAll H [value] = some H' ∧
      ReleaseInvariant H' addresses mem' external none [] context base bump limit slots' lists' ∧
      Sem.Star (Lir.semStep P)
        {mem, ctx := context, stack := {fn := wrapper, label := 0, pos := 0, env} :: caller :: callers}
        (1 + charges)
        {mem := mem', ctx := context,
          stack := {caller with env := caller.env.insert dummy 1, dsts := []} :: callers} ∧
      ProtectedFrame mem mem' context base bump := by
  let continuation : Lir.Frame := {fn := wrapper, label := 0, pos := 1, env, dsts := []}
  have enter : Lir.enter P procedure [word] =
      some {fn := procedure, label := 0, pos := 0, env := decEnv word} := by
    simp [Lir.enter, procedureLookup, dec, Lir.bindParams, decEnv]
  have callStep := decrement_wrapper_call (env := env) (rest := caller :: callers)
    (mem := mem) (ctx := context) wrapperLookup argument enter
  obtain ⟨H', mem', slots', lists', charges, released, restored, trace, protectedBytes⟩ :=
    release_caller_complete_frame idle word represented P procedure procedureLookup
      continuation (caller :: callers) rfl
  have returnStep := marker_return (callee := procedure) (env := env) (caller := caller)
    (rest := callers) (mem := mem') (ctx := context) wrapperLookup rfl destination
  refine ⟨H', mem', slots', lists', charges, released, restored, ?_, protectedBytes⟩
  have composed := (Sem.Star.single (Lir.semStep_next.mpr callStep)).trans
    (trace.trans (Sem.Star.single (Lir.semStep_next.mpr returnStep)))
  simpa [continuation] using composed

/-- Source ownership is the exact H1-projected live root list. The physical
invariant counts that same list plus retained caller tokens. The actual value
and its word are extracted, not supplied as an assumed valid owned argument. -/
theorem decrement_wrapper_tokens
    {H : Heap} {external : Nat → Nat} {held roots : List RVal}
    {x : Fir.Var} {live : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env}
    (before : Tokens H external held (x :: live) ρf ρo roots)
    {addresses : AddressMap} {mem : X86.Memory} {context base bump limit : Lir.Word}
    {slots : List Slot} {lists : Nat → List Lir.Word}
    (idle : ReleaseInvariant H addresses mem (holdRoots external (roots ++ held)) none []
      context base bump limit slots lists)
    {P : Lir.Program} {wrapper procedure dummy bound : Nat} {env : Lir.Env}
    (wrapperLookup : P.funcs[wrapper]? = some (decrementWrapper procedure))
    (procedureLookup : P.funcs[procedure]? = some dec)
    (caller : Lir.Frame) (callers : List Lir.Frame)
    (registers : EnvWordsBelow addresses bound ρo caller.env)
    (real : x < bound) (reserved : bound ≤ dummy)
    (argument : env[0]? = caller.env[x]?) (destination : caller.dsts = [dummy]) :
    ∃ value remaining H' mem' slots' lists' charges,
      ρo.get? x = some value ∧ roots = value :: remaining ∧
      Own.Plain.evalAction ρo H (.dec x) = .ok H' ∧
      Tokens H' external held live ρf ρo remaining ∧
      ReleaseInvariant H' addresses mem' (holdRoots external (remaining ++ held)) none []
        context base bump limit slots' lists' ∧
      Sem.Star (Lir.semStep P)
        {mem, ctx := context, stack := {fn := wrapper, label := 0, pos := 0, env} :: caller :: callers}
        (1 + charges)
        {mem := mem', ctx := context,
          stack := {caller with env := caller.env.insert dummy 1, dsts := []} :: callers} ∧
      ProtectedFrame mem mem' context base bump ∧
      EnvWordsBelow addresses bound ρo (caller.env.insert dummy 1) ∧
      (∀ root ∈ held, H.value? root = H'.value? root) := by
  obtain ⟨value, remaining, Hsource, lookup, equal, action, tokens, _, retained⟩ := before.decrement
  obtain ⟨word, represented, register⟩ := registers x value real lookup
  have argumentWord : env[0]? = some word := argument.trans register
  have rebase : holdRoots external (roots ++ held) =
      fun location => holdRoots external (remaining ++ held) location + refsIn location [value] := by
    funext location
    rw [equal]
    simp only [holdRoots, refsIn_append, refsIn, List.cons_append]
    omega
  rw [rebase] at idle
  obtain ⟨Hphysical, mem', slots', lists', charges, released, restored, trace, protectedBytes⟩ :=
    wrapper_framed idle represented wrapperLookup procedureLookup argumentWord caller callers destination
  have actionPhysical : Own.Plain.evalAction ρo H (.dec x) = .ok Hphysical := by
    simp [Own.Plain.evalAction, lookup, released, Sem.Result.ofOption]
  have same : Hphysical = Hsource := Sem.Result.ok.inj (actionPhysical.symm.trans action)
  subst Hphysical
  exact ⟨value, remaining, Hsource, mem', slots', lists', charges, lookup, equal,
    action, tokens, restored, trace, protectedBytes, registers.marker reserved 1, retained⟩



end Compilatrix.Cfg.Rc.Proof.Physical.Bridge
