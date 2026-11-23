import IxCC.Cfg.Rc.Proof.Native.Public
import IxCC.Cfg.Rc.Proof.Prune
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
    inlinedPublicProgram l funcs main =
      Prune.pruneUnusedReuse l (Inline.inlineProgram l (rawPublicProgram l funcs main)) := by
  have hge : ¬ (rawProgram l funcs main).funcs.size < l.sourceCount := by
    simp only [rawProgram, List.size_toArray, List.length_append, hlen]
    omega
  have hsrc : l.sourceCount ≤ (Inline.inlineProgram l (rawProgram l funcs main)).funcs.size := by
    simp only [Inline.inlineProgram, Array.size_mapIdx, rawProgram, List.size_toArray,
      List.length_append, hlen]
    omega
  have hsize : l.init + 4 + 4 * l.ctors.length ≤
      (Inline.inlineProgram l (rawProgram l funcs main)).funcs.size := by
    simp only [Inline.inlineProgram, Array.size_mapIdx, rawProgram, List.size_toArray,
      List.length_append, List.length_cons, List.length_nil, hlen, wrappers_length,
      procedures_length, reuseProcs, resetWrappers, resetUWrappers, reuseWrappers, reuseUWrappers,
      List.length_map, List.length_zipIdx]
    simp only [Native.Layout.init, Native.Layout.incProc]
    omega
  have hinlPush : Inline.inlineProgram l (rawPublicProgram l funcs main) =
      { Inline.inlineProgram l (rawProgram l funcs main) with
        funcs := (Inline.inlineProgram l (rawProgram l funcs main)).funcs.push (dropWrapper l.decProc) } := by
    simp only [rawPublicProgram, Inline.inlineProgram, Array.mapIdx_push, hge, ↓reduceIte]
  rw [hinlPush, Prune.pruneUnusedReuse_push hsrc hsize]
  rfl

private theorem isPrunable_of_le_isUnique (l : Native.Layout) {g : Nat} (h : g ≤ l.isUniqueProc) :
    Prune.isPrunableReuse l g = false := by
  simp only [Prune.isPrunableReuse, decide_eq_false_iff_not]
  omega

private theorem noPrunableCalls_genAlloc (l : Native.Layout) (lay : Rt.Rc.CellLayout) :
    Prune.NoPrunableCallsInFunc l (Rt.Rc.Gen.alloc lay) := by
  unfold Rt.Rc.Gen.alloc
  cases lay.cls? with
  | none =>
    dsimp only
    exact Prune.noPrunableCalls_of_funcHasNoCalls (by decide)
  | some cls =>
    dsimp only
    by_cases hok : lay.ok = true
    · simp only [hok, ↓reduceIte]
      intro b hb
      simp only [Rt.Rc.Gen.allocFunc, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨fun _ _ _ hc => by simp at hc, fun _ _ ht => by cases ht⟩
    · simp only [hok, Bool.false_eq_true, ↓reduceIte]
      exact Prune.noPrunableCalls_of_funcHasNoCalls (by decide)

private theorem noPrunableCalls_incWrap (l : Native.Layout) :
    Prune.NoPrunableCallsInFunc l (Native.incrementWrapper l.incProc) := by
  intro b hb
  simp only [Native.incrementWrapper, List.mem_cons, List.not_mem_nil, or_false] at hb
  subst hb
  refine ⟨fun rs g as hc => ?_, fun _ _ ht => by cases ht⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, Lir.Stmt.call.injEq] at hc
  obtain ⟨_, rfl, _⟩ := hc
  exact isPrunable_of_le_isUnique l (by simp [Native.Layout.isUniqueProc, Native.Layout.init]; omega)

private theorem noPrunableCalls_decWrap (l : Native.Layout) :
    Prune.NoPrunableCallsInFunc l (Native.decrementWrapper l.decProc) := by
  intro b hb
  simp only [Native.decrementWrapper, List.mem_cons, List.not_mem_nil, or_false] at hb
  subst hb
  refine ⟨fun rs g as hc => ?_, fun _ _ ht => by cases ht⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, Lir.Stmt.call.injEq] at hc
  obtain ⟨_, rfl, _⟩ := hc
  exact isPrunable_of_le_isUnique l (by simp [Native.Layout.isUniqueProc, Native.Layout.init, Native.Layout.decProc]; omega)

private theorem noPrunableCalls_dropWrap (l : Native.Layout) :
    Prune.NoPrunableCallsInFunc l (dropWrapper l.decProc) :=
  noPrunableCalls_decWrap l

private theorem noPrunableCalls_allocWrap (l : Native.Layout) {i fields : Nat}
    (hi : i < l.ctors.length) :
    Prune.NoPrunableCallsInFunc l (Native.allocationWrapper (l.allocProc i) fields) := by
  intro b hb
  simp only [Native.allocationWrapper, List.mem_cons, List.not_mem_nil, or_false] at hb
  subst hb
  refine ⟨fun rs g as hc => ?_, fun _ _ ht => by cases ht⟩
  simp only [List.mem_cons, List.mem_map] at hc
  rcases hc with h1 | ⟨_, _, h2⟩
  · cases h1
    exact isPrunable_of_le_isUnique l
      (by simp [Native.Layout.isUniqueProc, Native.Layout.init, Native.Layout.allocProc]; omega)
  · cases h2

private theorem noPrunableCalls_resetWrap (l : Native.Layout) (lay : Rt.Rc.CellLayout) (cls : Nat) :
    Prune.NoPrunableCallsInFunc l (Native.mkResetWrapper l.isUniqueProc l.incProc l.decProc lay cls) := by
  intro b hb
  simp only [Native.mkResetWrapper, List.toList_toArray, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, List.mem_flatMap, List.mem_range] at hb
  rcases hb with ((((rfl | rfl) | ⟨j, _, rfl | rfl⟩) | rfl) | ⟨j, _, rfl | rfl⟩) | rfl
  · refine ⟨fun rs g as hc => ?_, fun _ _ ht => by cases ht⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, Lir.Stmt.call.injEq] at hc
    obtain ⟨_, rfl, _⟩ := hc
    exact isPrunable_of_le_isUnique l (Nat.le_refl _)
  · refine ⟨fun rs g as hc => ?_, fun _ _ ht => by cases ht⟩
    simp only [List.mem_append, List.mem_cons, List.mem_map] at hc
    rcases hc with ⟨_, _, h1⟩ | (h2 | ⟨_, _, h3⟩)
    · cases h1
    · cases h2
    · cases h3
  · exact ⟨fun _ _ _ hc => by simp at hc, fun _ _ ht => by cases ht⟩
  · refine ⟨fun rs g as hc => ?_, fun _ _ ht => by cases ht⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, Lir.Stmt.call.injEq] at hc
    obtain ⟨_, rfl, _⟩ := hc
    exact isPrunable_of_le_isUnique l (by simp [Native.Layout.isUniqueProc, Native.Layout.init, Native.Layout.decProc]; omega)
  · exact ⟨fun _ _ _ hc => by simp at hc, fun _ _ ht => by cases ht⟩
  · exact ⟨fun _ _ _ hc => by simp at hc, fun _ _ ht => by cases ht⟩
  · refine ⟨fun rs g as hc => ?_, fun _ _ ht => by cases ht⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h1 | h2
    · cases h1
    · cases h2
      exact isPrunable_of_le_isUnique l (by simp [Native.Layout.isUniqueProc, Native.Layout.init]; omega)
  · refine ⟨fun rs g as hc => ?_, fun _ _ ht => by cases ht⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, Lir.Stmt.call.injEq] at hc
    obtain ⟨_, rfl, _⟩ := hc
    exact isPrunable_of_le_isUnique l (by simp [Native.Layout.isUniqueProc, Native.Layout.init, Native.Layout.decProc]; omega)

private theorem noPrunableCalls_resetUWrap (l : Native.Layout) (lay : Rt.Rc.CellLayout) (cls : Nat) :
    Prune.NoPrunableCallsInFunc l (Native.mkResetUWrapper l.decProc lay cls) := by
  intro b hb
  simp only [Native.mkResetUWrapper, List.toList_toArray, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, List.mem_flatMap, List.mem_range] at hb
  rcases hb with (rfl | ⟨j, _, rfl | rfl⟩) | rfl
  · refine ⟨fun rs g as hc => ?_, fun _ _ ht => by cases ht⟩
    simp only [List.mem_append, List.mem_cons, List.mem_map] at hc
    rcases hc with ⟨_, _, h1⟩ | (h2 | ⟨_, _, h3⟩)
    · cases h1
    · cases h2
    · cases h3
  · exact ⟨fun _ _ _ hc => by simp at hc, fun _ _ ht => by cases ht⟩
  · refine ⟨fun rs g as hc => ?_, fun _ _ ht => by cases ht⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, Lir.Stmt.call.injEq] at hc
    obtain ⟨_, rfl, _⟩ := hc
    exact isPrunable_of_le_isUnique l (by simp [Native.Layout.isUniqueProc, Native.Layout.init, Native.Layout.decProc]; omega)
  · exact ⟨fun _ _ _ hc => by simp at hc, fun _ _ ht => by cases ht⟩

private theorem noPrunableCalls_reuseWrap (l : Native.Layout) {i : Nat}
    (hi : i < l.ctors.length) (lay : Rt.Rc.CellLayout) (cls : Nat) :
    Prune.NoPrunableCallsInFunc l (Native.mkReuseWrapper (l.allocProc i) lay cls) := by
  intro b hb
  simp only [Native.mkReuseWrapper, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl
  · exact ⟨fun _ _ _ hc => by simp at hc, fun _ _ ht => by cases ht⟩
  · refine ⟨fun rs g as hc => ?_, fun _ _ ht => by cases ht⟩
    simp only [List.mem_cons, List.mem_map] at hc
    rcases hc with h1 | ⟨_, _, h2⟩
    · cases h1
    · cases h2
  · refine ⟨fun rs g as hc => ?_, fun _ _ ht => by cases ht⟩
    simp only [List.mem_cons, List.mem_map] at hc
    rcases hc with h1 | ⟨_, _, h2⟩
    · cases h1
      exact isPrunable_of_le_isUnique l
        (by simp [Native.Layout.isUniqueProc, Native.Layout.init, Native.Layout.allocProc]; omega)
    · cases h2

private theorem noPrunableCalls_reuseUWrap (l : Native.Layout) (lay : Rt.Rc.CellLayout) (cls : Nat) :
    Prune.NoPrunableCallsInFunc l (Native.mkReuseUWrapper lay cls) := by
  intro b hb
  simp only [Native.mkReuseUWrapper, List.mem_cons, List.not_mem_nil, or_false] at hb
  subst hb
  refine ⟨fun rs g as hc => ?_, fun _ _ ht => by cases ht⟩
  simp only [List.mem_cons, List.mem_map] at hc
  rcases hc with h1 | ⟨_, _, h2⟩
  · cases h1
  · cases h2

theorem rawPublicProgram_noRuntimeReuseCalls {l : Native.Layout} {funcs : List Lir.Func}
    (hlen : funcs.length = l.sourceCount) (main : Nat) :
    Prune.NoRuntimeReuseCalls l (rawPublicProgram l funcs main) := by
  intro fi F hge hget
  rw [← Array.getElem?_toList] at hget
  simp only [rawPublicProgram, rawProgram, Array.toList_push, List.toList_toArray,
    List.append_assoc] at hget
  rw [List.getElem?_append_right (by omega)] at hget
  have hmem : F ∈ wrappers l ++ (procedures l ++ ([Rt.Procs.cxInit, Rt.Procs.natPow, Rt.Procs.natGcd] ++
      (reuseProcs l ++ [dropWrapper l.decProc]))) := List.mem_of_getElem? hget
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with hw | hp | (rfl | rfl | rfl) | hre | rfl
  · simp only [wrappers, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hw
    rcases hw with (rfl | rfl) | ⟨⟨c, i⟩, hci, rfl⟩
    · exact noPrunableCalls_incWrap l
    · exact noPrunableCalls_decWrap l
    · have hi : i < l.ctors.length := by
        have hmem := List.mem_zipIdx hci
        omega
      exact noPrunableCalls_allocWrap l hi
  · simp only [procedures, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hp
    rcases hp with (rfl | rfl) | ⟨c, _, rfl⟩
    · exact Prune.noPrunableCalls_of_funcHasNoCalls (by decide)
    · exact Prune.noPrunableCalls_of_funcHasNoCalls (by decide)
    · exact noPrunableCalls_genAlloc l _
  · exact Prune.noPrunableCalls_of_funcHasNoCalls (by decide)
  · exact Prune.noPrunableCalls_of_funcHasNoCalls (by decide)
  · exact Prune.noPrunableCalls_of_funcHasNoCalls (by decide)
  · simp only [reuseProcs, resetWrappers, resetUWrappers, reuseWrappers, reuseUWrappers,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hre
    rcases hre with (((rfl | ⟨c, _, rfl⟩) | ⟨c, _, rfl⟩) | ⟨⟨c, i⟩, hci, rfl⟩) | ⟨c, _, rfl⟩
    · exact Prune.noPrunableCalls_of_funcHasNoCalls (by decide)
    · exact noPrunableCalls_resetWrap l _ _
    · exact noPrunableCalls_resetUWrap l _ _
    · have hi : i < l.ctors.length := by
        have hmem := List.mem_zipIdx hci
        omega
      exact noPrunableCalls_reuseWrap l hi _ _
    · exact noPrunableCalls_reuseUWrap l _ _
  · exact noPrunableCalls_dropWrap l

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
  isUniqueProc := by
    have h := raw_isUnique_proc hlen main
    have hlt := (Array.getElem?_eq_some_iff.mp h).1
    simpa [rawPublicProgram, Array.getElem?_push_lt hlt, Array.getElem?_eq_getElem hlt] using h
  resetWrap := fun i c cls hc hcls => by
    have h := raw_reset_wrapper hlen main i hc hcls
    have hlt := (Array.getElem?_eq_some_iff.mp h).1
    simpa [rawPublicProgram, Array.getElem?_push_lt hlt, Array.getElem?_eq_getElem hlt] using h
  resetUWrap := fun i c cls hc hcls => by
    have h := raw_resetU_wrapper hlen main i hc hcls
    have hlt := (Array.getElem?_eq_some_iff.mp h).1
    simpa [rawPublicProgram, Array.getElem?_push_lt hlt, Array.getElem?_eq_getElem hlt] using h
  reuseWrap := fun i c cls hc hcls => by
    have h := raw_reuse_wrapper hlen main i hc hcls
    have hlt := (Array.getElem?_eq_some_iff.mp h).1
    simpa [rawPublicProgram, Array.getElem?_push_lt hlt, Array.getElem?_eq_getElem hlt] using h
  reuseUWrap := fun i c cls hc hcls => by
    have h := raw_reuseU_wrapper hlen main i hc hcls
    have hlt := (Array.getElem?_eq_some_iff.mp h).1
    simpa [rawPublicProgram, Array.getElem?_push_lt hlt, Array.getElem?_eq_getElem hlt] using h
  sourceBound := by
    simp only [rawPublicProgram, Array.size_push, rawProgram, List.size_toArray,
      List.length_append, hlen]
    omega

theorem accepted_split {config : Rt.Config} {F : Fir.Program}
    {bodies : Src.NatMap Own.Plain.Code} {P : Program} {lowered : Lowered}
    {borrows : Own.Plain.BorrowSigs} {uniqs : Own.Plain.UniqSigs}
    (accepted : Public.lower config F bodies P borrows uniqs = .ok lowered) :
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
