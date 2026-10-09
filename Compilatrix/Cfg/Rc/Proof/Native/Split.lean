import Compilatrix.Cfg.Rc.Proof.Native.Public
import Compilatrix.Lir.Proof.Split

/-! Actual raw runtime procedures must be related through the native compiler's
whole-program critical-edge split. The public release wrapper has no edges;
its append therefore commutes with that split. -/
set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Public.Spec
open Native.Spec

def labels (p : Lir.Program) (g : Nat) : Lir.Label → Lir.Label → Prop :=
  match p.funcs[g]? with
  | some F => Lir.splitRel F
  | none => Eq

theorem program_split (p : Lir.Program) :
    Lir.ProgSim p p.splitCriticalEdges (labels p) where
  main := rfl
  funcs := by
    intro g F hf
    refine ⟨F.splitCriticalEdges, ?_, ?_⟩
    · simp [Lir.Program.splitCriticalEdges, hf]
    · simpa [labels, hf] using Lir.split_sim F

theorem drop_split (callee : Nat) :
    (dropWrapper callee).splitCriticalEdges = dropWrapper callee := by
  rfl

def rawPublicProgram (l : Native.Layout) (funcs : List Lir.Func) (main : Nat) : Lir.Program :=
  let p := rawProgram l funcs main
  { p with funcs := p.funcs.push (dropWrapper l.decProc) }

theorem assemble_split {original : Rt.Lowered} {l : Native.Layout}
    {funcs : List Lir.Func} {main : Nat}
    (hp : original.program = (rawProgram l funcs main).splitCriticalEdges) :
    (assemble original l).runtime.program = (rawPublicProgram l funcs main).splitCriticalEdges := by
  simp [assemble, rawPublicProgram, hp, Lir.Program.splitCriticalEdges, Array.map_push, drop_split]

theorem accepted_split {config : Rt.Config} {F : Fir.Program}
    {bodies : Src.NatMap Own.Plain.Code} {P : Program} {lowered : Lowered}
    (accepted : Public.lower config F bodies P = .ok lowered) :
    ∃ main pairs funcs,
      consumeAll P = .ok pairs ∧
      Rt.Lower.functions (tablesOf P pairs) (consumed P pairs) (rootsOf config P)
        (List.range P.base.size) = .ok funcs ∧
      funcs.length = P.base.size ∧
      lowered.runtime.program = (rawPublicProgram (layoutOf P) funcs main).splitCriticalEdges ∧
      Lir.ProgSim (rawPublicProgram (layoutOf P) funcs main) lowered.runtime.program
        (labels (rawPublicProgram (layoutOf P) funcs main)) := by
  obtain ⟨original, hn, rfl, _⟩ := lower_parts accepted
  obtain ⟨main, pairs, funcs, _, _, _, _, hc, hf, hlen, hp, _⟩ := Native.Spec.lower_parts hn
  have he := assemble_split hp
  exact ⟨main, pairs, funcs, hc, hf, hlen, he, he ▸ program_split _⟩





end Compilatrix.Cfg.Rc.Public.Spec
