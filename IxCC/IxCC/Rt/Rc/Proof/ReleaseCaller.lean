import IxCC.Rt.Rc.Proof.ReleaseEntry
import IxCC.Rt.Rc.Proof.SuccessTransport

namespace IxCC.Rt.Rc.Procs
open Lir
open IxCC.Own IxCC.Own.Rc

theorem dec_call_free : CallFree dec := by
  simp [CallFree, dec]

/-- The validated release procedure embedded at any ambient function index,
above any suspended caller stack. The caller's zero-result continuation is
restored exactly; only the represented heap memory changes. -/
theorem release_caller_complete
    {heap addresses mem external value context base bump limit slots lists}
    (h : ReleaseInvariant heap addresses mem
      (fun location => external location + refsIn location [value]) none []
      context base bump limit slots lists)
    (word : Word) (hw : valueWord addresses value = some word)
    (P : Program) (fn : Nat) (hfn : P.funcs[fn]? = some dec)
    (caller : Frame) (callers : List Frame) (hdsts : caller.dsts = []) :
    ∃ heap' mem' slots' lists' charges,
      dropAll heap [value] = some heap' ∧
      ReleaseInvariant heap' addresses mem' external none [] context base bump limit slots' lists' ∧
      Sem.Star (semStep P)
        { mem, ctx := context, stack := { fn, label := 0, pos := 0, env := decEnv word } :: caller :: callers }
        charges { mem := mem', ctx := context, stack := caller :: callers } := by
  obtain ⟨heap', mem', slots', lists', clock, hs, hi, heval⟩ := release_entry_complete h word hw
  have hinit : State.initial releaseProgram [word] mem context =
      some (releaseState mem context (decEnv word) 0 0) := by
    simpa only [releaseProgram, releaseState, decProgram, decState] using dec_initial mem context word
  have hrun := (runs_eval hinit) clock
  dsimp only at hrun
  rw [heval] at hrun
  let frame : Frame := { fn := 0, label := 0, pos := 0, env := decEnv word }
  have hlocal : Sem.Reaches (semStep (localProgram dec)) (localState mem context frame) clock (.ok ([], mem')) := by
    simpa only [localProgram, releaseProgram, localState, releaseState, frame] using hrun
  obtain ⟨charges, hle, hsteps⟩ := local_success_transport dec dec_call_free P fn hfn mem context frame
    rfl caller callers (env := caller.env) hlocal (by simp [hdsts, bindParams])
  refine ⟨heap', mem', slots', lists', charges, hs, hi, ?_⟩
  have hc : {caller with env := caller.env, dsts := []} = caller := by
    cases caller with
    | mk f l p e ds =>
      change ds = [] at hdsts
      subst ds
      rfl
  simpa only [ambientState, frame, hc] using hsteps



end IxCC.Rt.Rc.Procs
