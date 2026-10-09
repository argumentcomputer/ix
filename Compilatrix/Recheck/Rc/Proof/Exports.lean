import Compilatrix.Recheck.Rc.Proof.Parts
import Compilatrix.Recheck.Rc.Proof.FrontParts
import Compilatrix.Recheck.Rc.Proof.Replay
import Compilatrix.Cfg.Rc.Proof.Native.Public
import Compilatrix.Cfg.Rc.Proof.Native.Consume
import Compilatrix.Rt.Proof.Roots

set_option autoImplicit false
namespace Compilatrix.Recheck.RcReplay
open Compilatrix.Cfg.Rc.Native Compilatrix.Cfg.Rc.Native.Spec

private theorem consumed_params {P : Cfg.Rc.Program} {layout : Layout} {fd actual : Cfg.Fun}
    (accepted : consumeFunction P layout fd = .ok actual) : actual.params = fd.params := by
  have parts := consumeFunction_parts accepted
  cases blocks : fd.blocks with
  | nil =>
    have empty : actual.blocks = [] := List.length_eq_zero_iff.mp (by simpa [blocks] using parts.2.2.2.2.1)
    simp [Cfg.Fun.params, blocks, empty]
  | cons block rest =>
    obtain ⟨body, _, first⟩ := parts.2.2.2.2.2 (show fd.blocks[0]? = some block by simp [blocks])
    have head : actual.blocks.head? = some {block with body} := by
      simpa only [List.head?_eq_getElem?] using first
    simp [Cfg.Fun.params, blocks, head]

private theorem assembled_function {original : Rt.Lowered} {layout : Layout}
    {functions : List Lir.Func} {main f : Nat} {function : Lir.Func}
    (program : original.program = (rawProgram layout functions main).splitCriticalEdges)
    (lookup : (rawProgram layout functions main).funcs[f]? = some function) :
    (Cfg.Rc.Public.Spec.assemble original layout).runtime.program.funcs[f]? =
      some function.splitCriticalEdges := by
  have actual : original.program.funcs[f]? = some function.splitCriticalEdges := by
    rw [program]
    simp [Lir.Program.splitCriticalEdges, lookup]
  exact (Cfg.Rc.Public.Spec.assemble_existing original layout
    (Array.getElem?_eq_some_iff.mp actual).1).trans actual

/-- Every admitted original root retains its actual convention and arity
through consumption, both edge splits and the appended release wrapper. -/
theorem public_root {config : Rt.Config} {F : Fir.Program}
    {bodies : Src.NatMap Own.Plain.Code} {P : Cfg.Rc.Program} {lowered : Cfg.Rc.Public.Lowered}
    (accepted : Cfg.Rc.Public.lower config F bodies P = .ok lowered)
    {r fn : Nat} {symbol : String} (root : lowered.runtime.roots[r]? = some (fn, symbol))
    (range : fn < P.base.size) :
    ∃ fd function, P.base.fun? fn = some fd ∧
      lowered.runtime.program.funcs[fn]? = some function ∧
      function.conv = .sysvExport symbol ∧ function.params.length = fd.params.length ∧
      fn ≠ lowered.runtime.init ∧ fn ≠ lowered.drop := by
  obtain ⟨original, native, rfl, _⟩ := Cfg.Rc.Public.Spec.lower_parts accepted
  obtain ⟨main, pairs, functions, _, _, _, _, consuming, lowering, length, program,
    init, _, _, roots, _⟩ := Cfg.Rc.Native.Spec.lower_parts native
  obtain ⟨fd, actual, fdLookup, consumed, actualLookup⟩ := consumed_entry consuming range
  obtain ⟨actual', function, actualLookup', loweredFunction, functionLookup⟩ :=
    (Rt.Proof.functions_spec lowering).2 (i := fn) (f := fn) (by simp [range])
  have equal : actual' = actual := Option.some.inj (actualLookup'.symm.trans actualLookup)
  subst actual'
  have convention : Rt.Proof.convOf (Cfg.Rc.Native.Spec.rootsOf config P) fn = .sysvExport symbol := by
    have member : (fn, symbol) ∈ Cfg.Rc.Native.Spec.rootsOf config P := by
      rw [← roots]
      exact List.mem_of_getElem? root
    have found := Rt.Proof.lookup_dedup
      (P.base.exports.zipIdx.map fun (f, i) =>
        (f, Rt.Lower.symbolOf ((config.names[i]?).getD s!"root{i}"))) member
    change (Cfg.Rc.Native.Spec.rootsOf config P).lookup fn = some symbol at found
    simp only [Rt.Proof.convOf, found]
  obtain ⟨params, conv⟩ := Rt.Proof.function_params loweredFunction
  have raw : (rawProgram (layoutOf P) functions main).funcs[fn]? = some function :=
    (raw_source main fn (by omega)).trans functionLookup
  have final := assembled_function program raw
  refine ⟨fd, function.splitCriticalEdges, fdLookup, final, ?_, ?_, ?_, ?_⟩
  · exact (Rt.Proof.split_params_conv function).2.trans (conv.trans convention)
  · rw [(Rt.Proof.split_params_conv function).1, params, consumed_params consumed]
  · change fn ≠ original.init
    rw [init]
    simp only [layoutOf, Layout.init, Layout.incProc]
    omega
  · change fn ≠ original.program.funcs.size
    have splitLookup : original.program.funcs[fn]? = some function.splitCriticalEdges := by
      rw [program]; simp [Lir.Program.splitCriticalEdges, raw]
    exact Nat.ne_of_lt (Array.getElem?_eq_some_iff.mp splitLookup).1

theorem public_init {config : Rt.Config} {F : Fir.Program}
    {bodies : Src.NatMap Own.Plain.Code} {P : Cfg.Rc.Program} {lowered : Cfg.Rc.Public.Lowered}
    (accepted : Cfg.Rc.Public.lower config F bodies P = .ok lowered) :
    ∃ function, lowered.runtime.program.funcs[lowered.runtime.init]? = some function ∧
      function.conv = .sysvExport Rt.Procs.initSymbol ∧ function.params.length = 2 ∧
      lowered.runtime.init ≠ lowered.drop := by
  obtain ⟨original, native, rfl, _⟩ := Cfg.Rc.Public.Spec.lower_parts accepted
  obtain ⟨main, pairs, functions, _, _, _, _, _, _, length, program,
    init, _⟩ := Cfg.Rc.Native.Spec.lower_parts native
  have raw := raw_init (l := layoutOf P) length main
  have final := assembled_function program raw
  refine ⟨Rt.Procs.cxInit.splitCriticalEdges, ?_, ?_, ?_, ?_⟩
  · change (Cfg.Rc.Public.Spec.assemble original (layoutOf P)).runtime.program.funcs[original.init]? = _
    rw [init]
    exact final
  · exact (Rt.Proof.split_params_conv Rt.Procs.cxInit).2
  · exact congrArg List.length (Rt.Proof.split_params_conv Rt.Procs.cxInit).1
  · change original.init ≠ original.program.funcs.size
    have splitLookup : original.program.funcs[(layoutOf P).init]? = some Rt.Procs.cxInit.splitCriticalEdges := by
      rw [program]; simp [Lir.Program.splitCriticalEdges, raw]
    rw [init]
    exact Nat.ne_of_lt (Array.getElem?_eq_some_iff.mp splitLookup).1

theorem public_roots {config : Rt.Config} {F : Fir.Program}
    {bodies : Src.NatMap Own.Plain.Code} {P : Cfg.Rc.Program} {lowered : Cfg.Rc.Public.Lowered}
    (accepted : Cfg.Rc.Public.lower config F bodies P = .ok lowered) :
    lowered.runtime.roots.map Prod.fst = P.base.exports := by
  obtain ⟨original, native, rfl, _⟩ := Cfg.Rc.Public.Spec.lower_parts accepted
  obtain ⟨main, pairs, functions, _, _, _, _, _, _, _, _, _, _, _, roots, _⟩ :=
    Cfg.Rc.Native.Spec.lower_parts native
  change original.roots.map Prod.fst = _
  rw [roots]
  simp [Cfg.Rc.Native.Spec.rootsOf, List.map_map, Function.comp_def]

theorem runFront_exports_lt {cfg : Config} {P : Src.Program} {c : Cert} {f : Front}
    (accepted : runFront cfg P c = .ok f) :
    ∀ fn ∈ f.cfg.base.exports, fn < f.cfg.base.size := by
  obtain ⟨_, _, _, fir, _, generated, _⟩ := runFront_spec accepted
  rw [Cfg.Rc.generate_exports generated, Cfg.Rc.generate_size generated]
  exact Recheck.fir_exports_lt fir

/-- Actual selection and certificate validation preserve each root's SysV
interface. Roots retain tagged-Nat default representations. -/
theorem run_root {cfg : Config} {P : Src.Program} {c : Cert} {a : Artifact}
    (accepted : run cfg P c = .ok a) {xv : Xv.VProgram} {xl : Xv.LProgram}
    (selected : Xv.Select.select a.front.lowered.program = .ok xv)
    (validated : Xv.Validate.run cfg.env xv c.base.alloc = .ok xl)
    {r fn : Nat} {symbol : String} (root : a.front.lowered.roots[r]? = some (fn, symbol)) :
    ∃ xf, xl.funcs[fn]? = some xf ∧ xf.conv = .sysvExport symbol ∧
      xf.params.length = Recheck.cfgParams a.front.cfg.base fn ∧
      fn ≠ a.front.lowered.init ∧ fn ≠ a.front.drop ∧
      (emittedConfig cfg a.front c.base).reps fn = none := by
  have front := (run_parts accepted).1
  have native := (runFront_native front).2
  have member : fn ∈ a.front.cfg.base.exports := by
    rw [← public_roots native]
    exact List.mem_map.mpr ⟨(fn, symbol), List.mem_of_getElem? root, rfl⟩
  obtain ⟨fd, function, fdLookup, functionLookup, convention, params, notInit, notDrop⟩ :=
    public_root native root (runFront_exports_lt front fn member)
  obtain ⟨xf, xfLookup, xfConv, xfParams⟩ := Backend.xl_func selected validated functionLookup
  refine ⟨xf, xfLookup, xfConv.trans convention, ?_, notInit, notDrop, ?_⟩
  · rw [xfParams, params]
    simp [Recheck.cfgParams, fdLookup]
  · simp [emittedConfig, Front.reps, Cfg.Rc.Public.Lowered.reps,
      Rt.Lowered.reps, notDrop, notInit]

theorem run_init {cfg : Config} {P : Src.Program} {c : Cert} {a : Artifact}
    (accepted : run cfg P c = .ok a) {xv : Xv.VProgram} {xl : Xv.LProgram}
    (selected : Xv.Select.select a.front.lowered.program = .ok xv)
    (validated : Xv.Validate.run cfg.env xv c.base.alloc = .ok xl) :
    ∃ xf, xl.funcs[a.front.lowered.init]? = some xf ∧
      xf.conv = .sysvExport Rt.Procs.initSymbol ∧ xf.params.length = 2 ∧
      (emittedConfig cfg a.front c.base).reps a.front.lowered.init = some [.word, .word] := by
  have native := (runFront_native (run_parts accepted).1).2
  obtain ⟨function, lookup, convention, params, notDrop⟩ := public_init native
  obtain ⟨xf, xfLookup, xfConv, xfParams⟩ := Backend.xl_func selected validated lookup
  refine ⟨xf, xfLookup, xfConv.trans convention, xfParams.trans params, ?_⟩
  simp [emittedConfig, Front.reps, Cfg.Rc.Public.Lowered.reps, Rt.Lowered.reps, notDrop]

/-- The owned-result release export passes its argument as one unchanged raw
word, never through the tagged-Nat entry conversion. -/
theorem run_drop {cfg : Config} {P : Src.Program} {c : Cert} {a : Artifact}
    (accepted : run cfg P c = .ok a) {xv : Xv.VProgram} {xl : Xv.LProgram}
    (selected : Xv.Select.select a.front.lowered.program = .ok xv)
    (validated : Xv.Validate.run cfg.env xv c.base.alloc = .ok xl) :
    ∃ xf, xl.funcs[a.front.drop]? = some xf ∧ xf.conv = .sysvExport "cx_drop" ∧
      xf.params.length = 1 ∧ (emittedConfig cfg a.front c.base).reps a.front.drop = some [.word] := by
  have native := (runFront_native (run_parts accepted).1).2
  have lookup := Cfg.Rc.Public.Spec.accepted_drop native
  obtain ⟨xf, xfLookup, xfConv, xfParams⟩ := Backend.xl_func selected validated lookup
  exact ⟨xf, xfLookup, xfConv, xfParams, emittedConfig_drop cfg a.front c.base⟩








end Compilatrix.Recheck.RcReplay
