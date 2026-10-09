import Compilatrix.Cfg.Rc.Proof.Native.Consume
import Compilatrix.Cfg.Rc.Proof.Native.Split

/-! Recover the concrete unpruned source-function layout and its actual final
prune/split shape from the admitted executable pipeline. This is the layout
input needed by physical instruction proofs, not an assumed simulation. -/
set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Native.Spec

theorem function_receipt {config : Rt.Config} {P : Program}
    {pairs : List (Nat × Cfg.Fun)} {funcs : List Lir.Func}
    (hc : consumeAll P = .ok pairs)
    (hfns : Rt.Lower.functions (tablesOf P pairs) (consumed P pairs) (rootsOf config P)
      (List.range P.base.size) = .ok funcs)
    {f : Nat} (hf : f < P.base.size) :
    ∃ original fd params raw target starts,
      P.base.fun? f = some original ∧
      consumeFunction P (layoutOf P) original = .ok fd ∧
      (consumed P pairs).fun? f = some fd ∧
      Rt.Lower.functionRaw (tablesOf P pairs) f fd = .ok (params, raw) ∧
      Rt.Lower.reachClosed raw (Rt.Lower.reachable raw) = true ∧
      funcs[f]? = some target ∧
      target = Lir.Func.splitCriticalEdges {
        name := s!"f{f}", params, results := 1
        blocks := (Rt.Lower.pruneWith (Rt.Lower.reachable raw) raw).toArray
        conv := Rt.Proof.convOf (rootsOf config P) f } ∧
      Rt.Proof.Lowered (tablesOf P pairs) f fd {
        name := s!"f{f}", params, results := 1, blocks := raw.toArray
        conv := Rt.Proof.convOf (rootsOf config P) f } starts := by
  obtain ⟨original, fd, hsource, hconsume, hlookup⟩ := consumed_entry hc hf
  obtain ⟨fd', target, hlookup', htarget, hindex⟩ :=
    (Rt.Proof.functions_spec hfns).2 (i := f) (f := f) (by simp [hf])
  rw [hlookup] at hlookup'
  cases hlookup'
  obtain ⟨params, raw, hraw, hclosed, heq⟩ := Rt.Proof.function_spec htarget
  obtain ⟨starts, hlayout⟩ := Rt.Proof.functionRaw_lowered hraw
    s!"f{f}" (Rt.Proof.convOf (rootsOf config P) f)
  exact ⟨original, fd, params, raw, target, starts, hsource, hconsume,
    hlookup, hraw, hclosed, hindex, heq, hlayout⟩


end Compilatrix.Cfg.Rc.Native.Spec
