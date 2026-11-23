import IxCC.Cfg.Rc.Proof.Native.Public
import IxCC.Cfg.Rc.Proof.Inline
import IxCC.Lir.Proof.Split

/-! Actual raw runtime procedures must be related through inline RC expansion
and the native compiler's whole-program critical-edge split. The public release
wrapper sits past `sourceCount` and has no edges; its append therefore commutes
with both `inlineProgram` and `splitCriticalEdges`. -/
set_option autoImplicit false
namespace IxCC.Cfg.Rc.Public.Spec
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

def inlinedPublicProgram (l : Native.Layout) (funcs : List Lir.Func) (main : Nat) : Lir.Program :=
  let p := inlinedProgram l funcs main
  { p with funcs := p.funcs.push (dropWrapper l.decProc) }

theorem assemble_split {original : Rt.Lowered} {l : Native.Layout}
    {funcs : List Lir.Func} {main : Nat}
    (hp : original.program = (inlinedProgram l funcs main).splitCriticalEdges) :
    (assemble original l).runtime.program = (inlinedPublicProgram l funcs main).splitCriticalEdges := by
  simp [assemble, inlinedPublicProgram, hp, Lir.Program.splitCriticalEdges, Array.map_push, drop_split]

theorem inlinedPublicProgram_eq_inline (l : Native.Layout) (funcs : List Lir.Func) (main : Nat)
    (hlen : funcs.length = l.sourceCount) :
    inlinedPublicProgram l funcs main = Inline.inlineProgram l (rawPublicProgram l funcs main) := by
  have hge : ¬ (rawProgram l funcs main).funcs.size < l.sourceCount := by
    simp only [rawProgram, List.size_toArray, List.length_append, hlen]
    omega
  simp only [inlinedPublicProgram, inlinedProgram, rawPublicProgram, Inline.inlineProgram,
    Array.mapIdx_push, hge, ↓reduceIte]

theorem rawPublicProgram_runtimeFuncs {l : Native.Layout} {funcs : List Lir.Func}
    (hlen : funcs.length = l.sourceCount) (main : Nat) :
    Inline.RuntimeFuncs l (rawPublicProgram l funcs main) where
  incWrap := by
    have h := raw_inc_wrapper hlen main
    have hlt := (Array.getElem?_eq_some_iff.mp h).1
    simpa [rawPublicProgram, Array.getElem?_push_lt hlt, Array.getElem?_eq_getElem hlt] using h
  decWrap := by
    have h := raw_dec_wrapper hlen main
    have hlt := (Array.getElem?_eq_some_iff.mp h).1
    simpa [rawPublicProgram, Array.getElem?_push_lt hlt, Array.getElem?_eq_getElem hlt] using h
  incProc := by
    have h := raw_inc_proc hlen main
    have hlt := (Array.getElem?_eq_some_iff.mp h).1
    simpa [rawPublicProgram, Array.getElem?_push_lt hlt, Array.getElem?_eq_getElem hlt] using h
  decProc := by
    have h := raw_dec_proc hlen main
    have hlt := (Array.getElem?_eq_some_iff.mp h).1
    simpa [rawPublicProgram, Array.getElem?_push_lt hlt, Array.getElem?_eq_getElem hlt] using h
  allocWrap := fun i c hc => by
    have h := raw_alloc_wrapper hlen main i hc
    have hlt := (Array.getElem?_eq_some_iff.mp h).1
    simpa [rawPublicProgram, Array.getElem?_push_lt hlt, Array.getElem?_eq_getElem hlt] using h
  allocProc := fun i c hc => by
    have h := raw_alloc_proc hlen main i hc
    have hlt := (Array.getElem?_eq_some_iff.mp h).1
    simpa [rawPublicProgram, Array.getElem?_push_lt hlt, Array.getElem?_eq_getElem hlt] using h
  sourceBound := by
    simp only [rawPublicProgram, Array.size_push, rawProgram, List.size_toArray,
      List.length_append, hlen]
    omega

theorem accepted_split {config : Rt.Config} {F : Fir.Program}
    {bodies : Src.NatMap Own.Plain.Code} {P : Program} {lowered : Lowered}
    (accepted : Public.lower config F bodies P = .ok lowered) :
    ∃ main pairs funcs,
      consumeAll P = .ok pairs ∧
      Rt.Lower.functions (tablesOf P pairs) (consumed P pairs) (rootsOf config P)
        (List.range P.base.size) = .ok funcs ∧
      funcs.length = P.base.size ∧
      lowered.runtime.program = (inlinedPublicProgram (layoutOf P) funcs main).splitCriticalEdges ∧
      Lir.ProgSim (inlinedPublicProgram (layoutOf P) funcs main) lowered.runtime.program
        (labels (inlinedPublicProgram (layoutOf P) funcs main)) := by
  obtain ⟨original, hn, rfl, _⟩ := lower_parts accepted
  obtain ⟨main, pairs, funcs, _, _, _, _, hc, hf, hlen, hp, _⟩ := Native.Spec.lower_parts hn
  have he := assemble_split hp
  exact ⟨main, pairs, funcs, hc, hf, hlen, he, he ▸ program_split _⟩

end IxCC.Cfg.Rc.Public.Spec
