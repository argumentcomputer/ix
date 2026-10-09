import Compilatrix.Cfg.Rc.Proof.Native.SourceFunction

/-! The physical source instruction proofs run before source-function pruning.
These concrete stages retain the RC wrappers, allocator procedures and public
drop function verbatim, then relate source pruning and the first edge split
to the actual compiler output. The separate whole-program split still applies.
No physical execution or heap correctness premise occurs in this module. -/
set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Public.Spec
open Native.Spec

def runtimeFunctions (layout : Native.Layout) : List Lir.Func :=
  wrappers layout ++ procedures layout ++
    [Rt.Procs.cxInit, Rt.Procs.natPow, Rt.Procs.natGcd, dropWrapper layout.decProc]

theorem public_functions (layout : Native.Layout) (funcs : List Lir.Func) (main : Nat) :
    (rawPublicProgram layout funcs main).funcs.toList = funcs ++ runtimeFunctions layout := by
  simp [rawPublicProgram, rawProgram, runtimeFunctions, List.append_assoc]

theorem public_get (layout : Native.Layout) (funcs : List Lir.Func) (main f : Nat) :
    (rawPublicProgram layout funcs main).funcs[f]? =
      if f < funcs.length then funcs[f]? else (runtimeFunctions layout)[f-funcs.length]? := by
  rw [← Array.getElem?_toList, public_functions]
  split
  · rename_i hf
    exact List.getElem?_append_left hf
  · rename_i hf
    exact List.getElem?_append_right (Nat.le_of_not_lt hf)

def rawSource (config : Rt.Config) (P : Program) (pairs : List (Nat × Cfg.Fun)) (f : Nat) : Lir.Func :=
  match (consumed P pairs).fun? f with
  | none => default
  | some fd => match Rt.Lower.functionRaw (tablesOf P pairs) f fd with
    | .error _ => default
    | .ok (params, raw) => {
      name := s!"f{f}", params, results := 1, blocks := raw.toArray
      conv := Rt.Proof.convOf (rootsOf config P) f }

def prunedSource (config : Rt.Config) (P : Program) (pairs : List (Nat × Cfg.Fun)) (f : Nat) : Lir.Func :=
  match (consumed P pairs).fun? f with
  | none => default
  | some fd => match Rt.Lower.functionRaw (tablesOf P pairs) f fd with
    | .error _ => default
    | .ok (params, raw) => {
      name := s!"f{f}", params, results := 1
      blocks := (Rt.Lower.pruneWith (Rt.Lower.reachable raw) raw).toArray
      conv := Rt.Proof.convOf (rootsOf config P) f }

def sourceStage (P : Program) (source : Nat → Lir.Func) (main : Nat) : Lir.Program :=
  rawPublicProgram (layoutOf P) ((List.range P.base.size).map source) main

theorem sourceStage_get (P : Program) (source : Nat → Lir.Func) (main f : Nat) :
    (sourceStage P source main).funcs[f]? =
      if f < P.base.size then some (source f)
      else (runtimeFunctions (layoutOf P))[f-P.base.size]? := by
  rw [sourceStage, public_get]
  simp only [List.length_map, List.length_range]
  split
  · rename_i hf
    simp [List.getElem?_map, hf]
  · rfl

def sourcePruneLabels (P : Program) (pairs : List (Nat × Cfg.Fun)) (f : Nat) :
    Lir.Label → Lir.Label → Prop :=
  if f < P.base.size then
    match (consumed P pairs).fun? f with
    | none => Eq
    | some fd => match Rt.Lower.functionRaw (tablesOf P pairs) f fd with
      | .error _ => Eq
      | .ok (_, raw) => Rt.Proof.Kept raw (Rt.Lower.reachable raw)
  else Eq

def sourceSplitLabels (config : Rt.Config) (P : Program) (pairs : List (Nat × Cfg.Fun))
    (f : Nat) : Lir.Label → Lir.Label → Prop :=
  if f < P.base.size then Lir.splitRel (prunedSource config P pairs f) else Eq

theorem raw_blocks_nonempty {tables : Rt.Lower.Tables} {f : Nat} {fd : Cfg.Fun}
    {params : List Nat} {raw : List Lir.Block}
    (lowered : Rt.Lower.functionRaw tables f fd = .ok (params, raw)) : raw ≠ [] := by
  obtain ⟨starts, layout⟩ := Rt.Proof.functionRaw_lowered lowered "" .internal
  have entry : ∃ block, fd.blocks[0]? = some block := by
    unfold Rt.Lower.functionRaw at lowered
    cases h : fd.blocks.head? with
    | none => simp [h, throw, throwThe, MonadExceptOf.throw, Except.bind] at lowered
    | some block =>
      refine ⟨block, ?_⟩
      cases hb : fd.blocks with
      | nil => simp [hb] at h
      | cons first rest =>
        simp only [hb, List.head?_cons, Option.some.injEq] at h
        simp [h]
  obtain ⟨block, hb⟩ := entry
  obtain ⟨offset, ho, _⟩ := layout.entry hb
  obtain ⟨target, ht, _⟩ := layout.head hb ho
  intro equal
  subst raw
  simp at ht

theorem source_raw_pruned {config : Rt.Config} {P : Program}
    {pairs : List (Nat × Cfg.Fun)} {funcs : List Lir.Func}
    (lowered : Rt.Lower.functions (tablesOf P pairs) (consumed P pairs) (rootsOf config P)
      (List.range P.base.size) = .ok funcs) (main : Nat) :
    Lir.ProgSim (sourceStage P (rawSource config P pairs) main)
      (sourceStage P (prunedSource config P pairs) main) (sourcePruneLabels P pairs) where
  main := rfl
  funcs := by
    intro f source lookup
    rw [sourceStage_get] at lookup
    split at lookup
    · rename_i hf
      simp only [Option.some.injEq] at lookup
      subst source
      obtain ⟨fd, target, hfd, hfunction, _⟩ :=
        (Rt.Proof.functions_spec lowered).2 (i := f) (f := f) (by simp [hf])
      obtain ⟨params, raw, hraw, closed, _⟩ := Rt.Proof.function_spec hfunction
      refine ⟨prunedSource config P pairs f, ?_, ?_⟩
      · rw [sourceStage_get, if_pos hf]
      · have blocks : (rawSource config P pairs f).blocks = raw.toArray := by
          simp [rawSource, hfd, hraw]
        have equal : prunedSource config P pairs f =
            {rawSource config P pairs f with blocks :=
              (Rt.Lower.pruneWith (Rt.Lower.reachable raw) raw).toArray} := by
          simp [rawSource, prunedSource, hfd, hraw]
        rw [equal, show sourcePruneLabels P pairs f =
          Rt.Proof.Kept raw (Rt.Lower.reachable raw) by simp [sourcePruneLabels, hf, hfd, hraw]]
        exact Rt.Proof.prune_sim blocks closed (Rt.Proof.reachable_zero raw) (raw_blocks_nonempty hraw)
    · rename_i hf
      refine ⟨source, ?_, ?_⟩
      · rw [sourceStage_get, if_neg hf]
        exact lookup
      · simpa [sourcePruneLabels, hf] using Lir.funcSim_refl source

theorem source_pruned_split {config : Rt.Config} {P : Program}
    {pairs : List (Nat × Cfg.Fun)} {funcs : List Lir.Func}
    (lowered : Rt.Lower.functions (tablesOf P pairs) (consumed P pairs) (rootsOf config P)
      (List.range P.base.size) = .ok funcs) (main : Nat) :
    Lir.ProgSim (sourceStage P (prunedSource config P pairs) main)
      (rawPublicProgram (layoutOf P) funcs main) (sourceSplitLabels config P pairs) where
  main := rfl
  funcs := by
    have length : funcs.length = P.base.size := by simpa using (Rt.Proof.functions_spec lowered).1
    intro f source lookup
    rw [sourceStage_get] at lookup
    split at lookup
    · rename_i hf
      simp only [Option.some.injEq] at lookup
      subst source
      obtain ⟨fd, target, hfd, hfunction, index⟩ :=
        (Rt.Proof.functions_spec lowered).2 (i := f) (f := f) (by simp [hf])
      obtain ⟨params, raw, hraw, _, equal⟩ := Rt.Proof.function_spec hfunction
      refine ⟨target, ?_, ?_⟩
      · rw [public_get, length, if_pos hf]
        exact index
      · have result : target = (prunedSource config P pairs f).splitCriticalEdges := by
          simpa [prunedSource, hfd, hraw] using equal
        rw [result]
        simpa [sourceSplitLabels, hf] using Lir.split_sim (prunedSource config P pairs f)
    · rename_i hf
      refine ⟨source, ?_, ?_⟩
      · rw [public_get, length, if_neg hf]
        exact lookup
      · simpa [sourceSplitLabels, hf] using Lir.funcSim_refl source

theorem source_raw_layout {config : Rt.Config} {P : Program}
    {pairs : List (Nat × Cfg.Fun)} {funcs : List Lir.Func}
    (consuming : consumeAll P = .ok pairs)
    (lowered : Rt.Lower.functions (tablesOf P pairs) (consumed P pairs) (rootsOf config P)
      (List.range P.base.size) = .ok funcs) (main : Nat) {f : Nat} (range : f < P.base.size) :
    ∃ original fd starts,
      P.base.fun? f = some original ∧
      Native.consumeFunction P (layoutOf P) original = .ok fd ∧
      (consumed P pairs).fun? f = some fd ∧
      (sourceStage P (rawSource config P pairs) main).funcs[f]? = some (rawSource config P pairs f) ∧
      Rt.Proof.Lowered (tablesOf P pairs) f fd (rawSource config P pairs f) starts := by
  obtain ⟨original, fd, params, raw, target, starts, horiginal, hc, hfd, hraw, _, _, _, layout⟩ :=
    Native.Spec.function_receipt consuming lowered range
  refine ⟨original, fd, starts, horiginal, hc, hfd, ?_, ?_⟩
  · rw [sourceStage_get, if_pos range]
  · simpa [rawSource, hfd, hraw] using layout







end Compilatrix.Cfg.Rc.Public.Spec
