import IxCC.Cfg.Rc.Proof.Native.Public
import IxCC.Cfg.Rc.Proof.Prune
import IxCC.Cfg.Rc.Proof.InlineWrappers
import IxCC.Cfg.Rc.Proof.FastDec
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
    · simp [Lir.Program.splitCriticalEdges_eq, hf]
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
  simp [assemble, inlinedPublicProgram, hp, Lir.Program.splitCriticalEdges_eq, Array.map_push, drop_split]

def postDecPublicProgram (l : Native.Layout) (funcs : List Lir.Func) (main : Nat) : Lir.Program :=
  FastDec.install l (InlineWrappers.inlineProgram l
    (Prune.pruneUnusedReuse l (Inline.inlineProgram l (rawPublicProgram l funcs main))))

theorem inlinedPublicProgram_eq_inline (l : Native.Layout) (funcs : List Lir.Func) (main : Nat)
    (hlen : funcs.length = l.sourceCount) :
    inlinedPublicProgram l funcs main =
      Prune.pruneDeadRuntime l (postDecPublicProgram l funcs main) := by
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
  have hsizePruned : l.init + 4 + 4 * l.ctors.length ≤
      (Prune.pruneUnusedReuse l (Inline.inlineProgram l (rawProgram l funcs main))).funcs.size := by
    simpa [Prune.pruneUnusedReuse] using hsize
  have hdecLt : l.decProc <
      (InlineWrappers.inlineProgram l
        (Prune.pruneUnusedReuse l (Inline.inlineProgram l (rawProgram l funcs main)))).funcs.size := by
    rw [InlineWrappers.inlineProgram_funcs_size]
    simp only [Native.Layout.decProc, Native.Layout.init] at hsizePruned ⊢
    omega
  have hsizeDec : l.init + 4 + 4 * l.ctors.length ≤
      (FastDec.install l (InlineWrappers.inlineProgram l
        (Prune.pruneUnusedReuse l (Inline.inlineProgram l (rawProgram l funcs main))))).funcs.size := by
    rw [FastDec.install_funcs_size, InlineWrappers.inlineProgram_funcs_size]
    exact hsizePruned
  have hinlPush : Inline.inlineProgram l (rawPublicProgram l funcs main) =
      { Inline.inlineProgram l (rawProgram l funcs main) with
        funcs := (Inline.inlineProgram l (rawProgram l funcs main)).funcs.push (dropWrapper l.decProc) } := by
    simp only [rawPublicProgram, Inline.inlineProgram, Array.mapIdx_push, hge, ↓reduceIte]
  unfold postDecPublicProgram
  rw [hinlPush, Prune.pruneUnusedReuse_push hsrc hsize,
    InlineWrappers.inlineProgram_push hsizePruned, FastDec.install_push _ _ _ hdecLt,
    Prune.pruneDeadRuntime_push hsizeDec]
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
  simp only [rawPublicProgram, rawProgram, Array.toList_push,
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

theorem prunedPublicProgram_wrapperRuntime {l : Native.Layout} {funcs : List Lir.Func}
    (hlen : funcs.length = l.sourceCount) (main : Nat) :
    InlineWrappers.WrapperRuntime l
      (Prune.pruneUnusedReuse l (Inline.inlineProgram l (rawPublicProgram l funcs main))) where
  incProc := by
    have hr := rawPublicProgram_runtimeFuncs hlen main
    have hge : l.sourceCount ≤ l.incProc := by simp [Native.Layout.incProc]; omega
    have hle : l.incProc ≤ l.isUniqueProc := by simp [Native.Layout.isUniqueProc, Native.Layout.init]; omega
    rw [Prune.pruneUnusedReuse_get_le hle, Inline.inlineProgram_get_ge _ _ hge]
    exact hr.incProc
  decProc := by
    have hr := rawPublicProgram_runtimeFuncs hlen main
    have hge : l.sourceCount ≤ l.decProc := by simp [Native.Layout.decProc, Native.Layout.incProc]; omega
    have hle : l.decProc ≤ l.isUniqueProc := by simp [Native.Layout.isUniqueProc, Native.Layout.init, Native.Layout.decProc]; omega
    rw [Prune.pruneUnusedReuse_get_le hle, Inline.inlineProgram_get_ge _ _ hge]
    exact hr.decProc
  isUniqueProc := by
    have hr := rawPublicProgram_runtimeFuncs hlen main
    have hge : l.sourceCount ≤ l.isUniqueProc := by simp [Native.Layout.isUniqueProc, Native.Layout.init, Native.Layout.incProc]; omega
    rw [Prune.pruneUnusedReuse_get_le (Nat.le_refl _), Inline.inlineProgram_get_ge _ _ hge]
    exact hr.isUniqueProc
  allocProc := fun i c hc => by
    have hr := rawPublicProgram_runtimeFuncs hlen main
    have hi : i < l.ctors.length := (List.getElem?_eq_some_iff.mp hc).1
    have hge : l.sourceCount ≤ l.allocProc i := by simp [Native.Layout.allocProc, Native.Layout.incProc]; omega
    have hle : l.allocProc i ≤ l.isUniqueProc := by simp [Native.Layout.isUniqueProc, Native.Layout.init, Native.Layout.allocProc]; omega
    rw [Prune.pruneUnusedReuse_get_le hle, Inline.inlineProgram_get_ge _ _ hge]
    exact hr.allocProc i c hc

theorem preDecPublicProgram_decProc {l : Native.Layout} {funcs : List Lir.Func}
    (hlen : funcs.length = l.sourceCount) (main : Nat) :
    (InlineWrappers.inlineProgram l
      (Prune.pruneUnusedReuse l (Inline.inlineProgram l (rawPublicProgram l funcs main)))).funcs[l.decProc]? =
      some Rt.Rc.Gen.dec := by
  have hle : l.decProc ≤ l.isUniqueProc := by
    simp [Native.Layout.isUniqueProc, Native.Layout.init, Native.Layout.decProc]; omega
  rw [InlineWrappers.inlineProgram_get_le hle]
  exact (prunedPublicProgram_wrapperRuntime hlen main).decProc

private theorem noDeadRuntimeCalls_genAlloc (l : Native.Layout) (lay : Rt.Rc.CellLayout) :
    Prune.NoDeadRuntimeCallsInFunc l (Rt.Rc.Gen.alloc lay) := by
  unfold Rt.Rc.Gen.alloc
  cases lay.cls? with
  | none =>
    dsimp only
    exact Prune.noDeadRuntimeCalls_of_funcHasNoCalls (by decide)
  | some cls =>
    dsimp only
    by_cases hok : lay.ok = true
    · simp only [hok, ↓reduceIte]
      intro b hb
      simp only [Rt.Rc.Gen.allocFunc, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨fun _ _ _ hc => by simp at hc, fun _ _ ht => by cases ht⟩
    · simp only [hok, Bool.false_eq_true, ↓reduceIte]
      exact Prune.noDeadRuntimeCalls_of_funcHasNoCalls (by decide)

private theorem noDeadRuntimeCalls_dropWrap (l : Native.Layout) :
    Prune.NoDeadRuntimeCallsInFunc l (dropWrapper l.decProc) := by
  intro b hb
  simp only [dropWrapper, Native.decrementWrapper, List.mem_cons, List.not_mem_nil, or_false] at hb
  subst hb
  refine ⟨fun rs g as hc => ?_, fun _ _ ht => by cases ht⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, Lir.Stmt.call.injEq] at hc
  obtain ⟨_, rfl, _⟩ := hc
  exact Prune.isPrunableDeadRuntime_decProc l

theorem postDecPublicProgram_noDeadRuntimeCalls {l : Native.Layout} {funcs : List Lir.Func}
    (hlen : funcs.length = l.sourceCount) (main : Nat) :
    Prune.NoDeadRuntimeCalls l (postDecPublicProgram l funcs main) := by
  intro fi F hge hnotReuse hget
  by_cases hdec : fi = l.decProc
  · subst hdec
    have hfd : (postDecPublicProgram l funcs main).funcs[l.decProc]? = some FastDec.fastDec :=
      FastDec.install_get_dec l _ (preDecPublicProgram_decProc hlen main)
    rw [hfd, Option.some.injEq] at hget
    subst hget
    exact Prune.noDeadRuntimeCalls_of_funcHasNoCalls (by decide)
  · have hnp : Prune.isPrunableReuse l fi = false := by
      simp only [Prune.isPrunableReuse, decide_eq_false_iff_not]
      exact hnotReuse
    have hsrcGe : l.sourceCount ≤ fi := by simp only [Native.Layout.incProc] at hge; omega
    have hraw : (rawPublicProgram l funcs main).funcs[fi]? = some F := by
      rw [postDecPublicProgram, FastDec.install_get_ne _ _ hdec,
        InlineWrappers.inlineProgram_get_not_prunable hnp,
        Prune.pruneUnusedReuse_get_not_prunable hnp,
        Inline.inlineProgram_get_ge _ _ hsrcGe] at hget
      exact hget
    by_cases hhi : fi < l.init + 4
    · rw [← Array.getElem?_toList] at hraw
      simp only [rawPublicProgram, rawProgram, Array.toList_push, List.append_assoc] at hraw
      rw [List.getElem?_append_right (by omega), List.getElem?_append_right
        (by rw [wrappers_length]; simp only [Native.Layout.incProc] at hge; omega)] at hraw
      have hidx : fi - funcs.length - (wrappers l).length <
          (procedures l).length + 3 + 1 := by
        rw [wrappers_length, procedures_length]
        simp only [Native.Layout.init, Native.Layout.incProc] at hge hhi; omega
      have hpre : (procedures l ++ ([Rt.Procs.cxInit, Rt.Procs.natPow, Rt.Procs.natGcd] ++
          (reuseProcs l ++ [dropWrapper l.decProc]))) =
          (procedures l ++ [Rt.Procs.cxInit, Rt.Procs.natPow, Rt.Procs.natGcd, Rt.Rc.Gen.isUnique]) ++
          (resetWrappers l ++ resetUWrappers l ++ reuseWrappers l ++ reuseUWrappers l ++ [dropWrapper l.decProc]) := by
        simp [reuseProcs, List.append_assoc]
      rw [hpre, List.getElem?_append_left (by simp [List.length_append]; omega)] at hraw
      have hmem := List.mem_of_getElem? hraw
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with hp | rfl | rfl | rfl | rfl
      · simp only [procedures, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hp
        rcases hp with (rfl | rfl) | ⟨c, _, rfl⟩
        · exact Prune.noDeadRuntimeCalls_of_funcHasNoCalls (by decide)
        · exact Prune.noDeadRuntimeCalls_of_funcHasNoCalls (by decide)
        · exact noDeadRuntimeCalls_genAlloc l _
      · exact Prune.noDeadRuntimeCalls_of_funcHasNoCalls (by decide)
      · exact Prune.noDeadRuntimeCalls_of_funcHasNoCalls (by decide)
      · exact Prune.noDeadRuntimeCalls_of_funcHasNoCalls (by decide)
      · exact Prune.noDeadRuntimeCalls_of_funcHasNoCalls (by decide)
    · have hgeDrop : l.init + 4 + 4 * l.ctors.length ≤ fi := by
        simp only [Native.Layout.isUniqueProc] at hnotReuse; omega
      have hrawLen : (rawProgram l funcs main).funcs.size = l.init + 4 + 4 * l.ctors.length := by
        simp only [rawProgram, List.size_toArray, List.length_append, List.length_cons,
          List.length_nil, hlen, wrappers_length, procedures_length, reuseProcs, resetWrappers,
          resetUWrappers, reuseWrappers, reuseUWrappers, List.length_map, List.length_zipIdx]
        simp only [Native.Layout.init, Native.Layout.incProc]; omega
      have hltPush : fi < (rawPublicProgram l funcs main).funcs.size :=
        (Array.getElem?_eq_some_iff.mp hraw).1
      have hfeq : fi = (rawProgram l funcs main).funcs.size := by
        simp only [rawPublicProgram, Array.size_push] at hltPush; omega
      rw [hfeq] at hraw
      simp only [rawPublicProgram, Array.getElem?_push_size, Option.some.injEq] at hraw
      subst hraw
      exact noDeadRuntimeCalls_dropWrap l

theorem postDecPublicProgram_noWrapperToWrapperCalls {l : Native.Layout} {funcs : List Lir.Func}
    (hlen : funcs.length = l.sourceCount) (main : Nat) :
    Prune.NoWrapperToWrapperCalls l (postDecPublicProgram l funcs main) := by
  intro fi F hlo hhi hget
  have hneDec : fi ≠ l.decProc := by simp only [Native.Layout.decProc]; omega
  have hle : fi ≤ l.isUniqueProc := by
    simp only [Native.Layout.isUniqueProc, Native.Layout.init]; omega
  have hraw : (rawPublicProgram l funcs main).funcs[fi]? = some F := by
    rw [postDecPublicProgram, FastDec.install_get_ne _ _ hneDec,
      InlineWrappers.inlineProgram_get_le hle,
      Prune.pruneUnusedReuse_get_le hle,
      Inline.inlineProgram_get_ge _ _ hlo] at hget
    exact hget
  rw [← Array.getElem?_toList] at hraw
  simp only [rawPublicProgram, rawProgram, Array.toList_push, List.append_assoc] at hraw
  rw [List.getElem?_append_right (by omega), List.getElem?_append_left
    (by rw [wrappers_length]; simp only [Native.Layout.incProc] at hhi; omega)] at hraw
  have hmem := List.mem_of_getElem? hraw
  simp only [wrappers, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hmem
  rcases hmem with (rfl | rfl) | ⟨⟨c, i⟩, _, rfl⟩
  · intro b hb
    simp only [Native.incrementWrapper, List.mem_cons, List.not_mem_nil, or_false] at hb
    subst hb
    refine ⟨fun rs g as hc => ?_, fun _ _ ht => by cases ht⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, Lir.Stmt.call.injEq] at hc
    obtain ⟨_, rfl, _⟩ := hc
    exact fun ⟨_, hlt⟩ => Nat.lt_irrefl _ hlt
  · intro b hb
    simp only [Native.decrementWrapper, List.mem_cons, List.not_mem_nil, or_false] at hb
    subst hb
    refine ⟨fun rs g as hc => ?_, fun _ _ ht => by cases ht⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, Lir.Stmt.call.injEq] at hc
    obtain ⟨_, rfl, _⟩ := hc
    exact fun ⟨_, hlt⟩ => Nat.not_lt.mpr (Nat.le_succ l.incProc) hlt
  · intro b hb
    simp only [Native.allocationWrapper, List.mem_cons, List.not_mem_nil, or_false] at hb
    subst hb
    refine ⟨fun rs g as hc => ?_, fun _ _ ht => by cases ht⟩
    simp only [List.mem_cons, List.mem_map] at hc
    rcases hc with h1 | ⟨_, _, h2⟩
    · cases h1
      exact fun ⟨_, hlt⟩ =>
        Nat.not_lt.mpr (Nat.le_trans (Nat.le_add_right l.incProc 2) (Nat.le_add_right _ _)) hlt
    · cases h2

private theorem allocFunc_size_le (lay : Rt.Rc.CellLayout) (cls : Nat) :
    (Rt.Rc.Gen.allocFunc lay cls).size ≤ 256 := by
  simp [Rt.Rc.Gen.allocFunc, Lir.Func.size, Lir.Block.size]

private theorem genAlloc_size_le (lay : Rt.Rc.CellLayout) :
    (Rt.Rc.Gen.alloc lay).size ≤ 256 := by
  unfold Rt.Rc.Gen.alloc
  cases lay.cls? with
  | none =>
    simp [Rt.Rc.Gen.declined, Lir.Func.size, Lir.Block.size]
  | some cls =>
    dsimp only
    by_cases hok : lay.ok = true
    · simp only [hok, ↓reduceIte]; exact allocFunc_size_le lay cls
    · simp only [hok, Bool.false_eq_true, ↓reduceIte]
      simp [Rt.Rc.Gen.declined, Lir.Func.size, Lir.Block.size]

private theorem allocationWrapper_size (callee fields : Nat) :
    (Native.allocationWrapper callee fields).size = fields + 2 := by
  simp [Native.allocationWrapper, Lir.Func.size, Lir.Block.size]

theorem postDecPublicProgram_deadRuntimeSizeBound {l : Native.Layout} {funcs : List Lir.Func}
    (hlen : funcs.length = l.sourceCount)
    (hok : l.ctors.all (fun c => (Rt.Rc.CellLayout.ofFields c.arity c.tag).ok) = true)
    (main : Nat) :
    Prune.DeadRuntimeSizeBound l (postDecPublicProgram l funcs main) := by
  intro fi F hpr hget
  simp only [Prune.isPrunableDeadRuntime, decide_eq_true_eq] at hpr
  have hge : l.sourceCount ≤ fi := by
    simp only [Native.Layout.isUniqueProc, Native.Layout.init, Native.Layout.decProc,
      Native.Layout.incProc] at hpr ⊢; omega
  have hle : fi ≤ l.isUniqueProc := by
    simp only [Native.Layout.isUniqueProc, Native.Layout.init, Native.Layout.decProc,
      Native.Layout.incProc] at hpr ⊢; omega
  have hneDec : fi ≠ l.decProc := by
    simp only [Native.Layout.isUniqueProc, Native.Layout.init, Native.Layout.decProc,
      Native.Layout.incProc] at hpr ⊢; omega
  have hraw : (rawPublicProgram l funcs main).funcs[fi]? = some F := by
    rw [postDecPublicProgram, FastDec.install_get_ne _ _ hneDec,
      InlineWrappers.inlineProgram_get_le hle,
      Prune.pruneUnusedReuse_get_le hle,
      Inline.inlineProgram_get_ge _ _ hge] at hget
    exact hget
  rw [← Array.getElem?_toList] at hraw
  simp only [rawPublicProgram, rawProgram, Array.toList_push, List.append_assoc] at hraw
  rw [List.getElem?_append_right (by omega)] at hraw
  have hpre : (wrappers l ++ (procedures l ++ ([Rt.Procs.cxInit, Rt.Procs.natPow, Rt.Procs.natGcd] ++
      (reuseProcs l ++ [dropWrapper l.decProc])))) =
      (wrappers l ++ procedures l ++ [Rt.Procs.cxInit, Rt.Procs.natPow, Rt.Procs.natGcd, Rt.Rc.Gen.isUnique]) ++
      (resetWrappers l ++ resetUWrappers l ++ reuseWrappers l ++ reuseUWrappers l ++ [dropWrapper l.decProc]) := by
    simp [reuseProcs, List.append_assoc]
  rw [hpre, List.getElem?_append_left (by
    simp only [List.length_append, wrappers_length, procedures_length, List.length_cons, List.length_nil]
    simp only [Native.Layout.isUniqueProc, Native.Layout.init, Native.Layout.incProc] at hle; omega)] at hraw
  have hmem := List.mem_of_getElem? hraw
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with (hw | hp) | rfl | rfl | rfl | rfl
  · simp only [wrappers, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hw
    rcases hw with (rfl | rfl) | ⟨⟨c, i⟩, hci, rfl⟩
    · simp [Native.incrementWrapper, Lir.Func.size, Lir.Block.size]
    · simp [Native.decrementWrapper, Lir.Func.size, Lir.Block.size]
    · dsimp only
      have hcMem : c ∈ l.ctors := List.fst_mem_of_mem_zipIdx hci
      have hcOk := List.all_eq_true.mp hok c hcMem
      simp only [Rt.Rc.CellLayout.ok, Rt.Rc.CellLayout.ofFields, Bool.and_eq_true] at hcOk
      have har : c.arity ≤ Rt.maxFields := of_decide_eq_true hcOk.1.1.2
      rw [allocationWrapper_size]
      have hmf : Rt.maxFields = 254 := rfl
      omega
  · simp only [procedures, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hp
    rcases hp with (rfl | rfl) | ⟨c, _, rfl⟩
    · decide
    · decide
    · exact genAlloc_size_le _
  · decide
  · decide
  · decide
  · decide

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
