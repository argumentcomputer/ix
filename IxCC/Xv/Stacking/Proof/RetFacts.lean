import IxCC.Xv.Stacking.Proof.RetStep

/-!
# What a return needs

A call's result locations are the convention's result registers
(`conventionResults_get`); a callee declares as many results as its call
binds (`call_arity`); and what a callee may change is among what its caller
may change: the callee's clobbers (`clobbers_allowed`) and the result
registers the call defines (`results_allowed`).
-/

namespace IxCC.Xv.Stacking.Proof

open IxCC.X86 IxCC.X86.Stream

theorem conventionResults_get {vs : List Loc} (h : Xl.conventionResults vs = true) {i : Nat} (hi : i < vs.length) :
    ∃ r, Lir.Conv.resultRegs[i]? = some r ∧ vs[i]? = some (.reg r) := by
  simp only [Xl.conventionResults, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨hlen, heq⟩ := h
  have hn : Xl.nResultRegs = 2 := rfl
  match vs, heq with
  | [a], heq =>
    have : i = 0 := by simp at hi; omega
    subst this
    simp [Xl.resultLoc, Lir.Conv.resultRegs] at heq
    exact ⟨.rax, rfl, by simp [heq]⟩
  | [a, b], heq =>
    simp [Xl.resultLoc, Lir.Conv.resultRegs, List.range_succ] at heq
    obtain ⟨rfl, rfl⟩ := heq
    have : i = 0 ∨ i = 1 := by simp at hi; omega
    rcases this with rfl | rfl
    · exact ⟨.rax, rfl, rfl⟩
    · exact ⟨.rdx, rfl, rfl⟩
  | [], _ => simp at hi
  | _ :: _ :: _ :: _, _ => simp [hn] at hlen

/-- What `run` checked of a function's arities. -/
theorem FnAt.arities {S : Stk} {k : Lir.FunId} {f : Func Loc} {l : FrameLayout} {pl : Placed} (hf : FnAt S k f l pl)
    {b : Block Loc} (hb : b ∈ f.blocks.toList) :
    (∀ g args rets, Inst.call g args rets ∈ b.body.toList → resultsOf S.p g = some rets.length) ∧
      (∀ vs, b.term = .ret vs → vs.length = f.results) ∧
      (∀ g args, b.term = .tail g args → resultsOf S.p g = some f.results) := by
  have h := hf.checks.2.2
  simp only [aritiesOk, List.all_eq_true, Bool.and_eq_true] at h
  obtain ⟨h₁, h₂⟩ := h b hb
  refine ⟨fun g args rets hi => ?_, fun vs hv => ?_, fun g args hv => ?_⟩
  · have := h₁ _ hi
    simpa using this
  · rw [hv] at h₂; simpa using h₂
  · rw [hv] at h₂; simpa using h₂

theorem resultsOf_eq {S : Stk} {g : Lir.FunId} {gf : Func Loc} (h : S.p.funcs[g]? = some gf) :
    resultsOf S.p g = some gf.results := by
  simp [resultsOf, h]

theorem call_arity {S : Stk} {k : Lir.FunId} {f : Func Loc} {l : FrameLayout} {pl : Placed} (hf : FnAt S k f l pl)
    {b : Block Loc} (hb : b ∈ f.blocks.toList) {g : Lir.FunId} {args rets : List Loc}
    (hi : Inst.call g args rets ∈ b.body.toList) {gf : Func Loc} (hgf : S.p.funcs[g]? = some gf) :
    gf.results = rets.length := by
  have := (hf.arities hb).1 g args rets hi
  rw [resultsOf_eq hgf] at this
  exact Option.some.inj this

/-- What a function may change, by `run`'s clobber check. -/
theorem mayChange_allowed {S : Stk} {k : Lir.FunId} {f : Func Loc} {l : FrameLayout} {pl : Placed}
    (hf : FnAt S k f l pl) {r : GPR} (hr : r ∈ mayChange S.env f f.facts l ++ tailResults S.p f) :
    r ∈ allowedChanges S.env k f := by
  have hx := hf.checks.2.1
  simp only [extraChanges, List.append_eq_nil_iff, List.filter_eq_nil_iff] at hx
  have := hx.1 r hr
  simpa using this

theorem clobbers_allowed {S : Stk} {k : Lir.FunId} {f : Func Loc} {l : FrameLayout} {pl : Placed}
    (hf : FnAt S k f l pl) {b : Block Loc} (hb : b ∈ f.blocks.toList) {g : Lir.FunId} {args rets : List Loc}
    (hi : Inst.call g args rets ∈ b.body.toList) {r : GPR} (hr : r ∈ S.env.clobbers g) :
    r ∈ allowedChanges S.env k f := by
  refine mayChange_allowed hf (List.mem_append_left _ ?_)
  simp only [mayChange, List.mem_append, List.mem_flatMap]
  right
  refine ⟨g, ?_, hr⟩
  simp only [callees, List.mem_flatMap, List.mem_append, List.mem_filterMap]
  exact ⟨b, hb, .inl ⟨_, hi, rfl⟩⟩

theorem results_allowed {S : Stk} {k : Lir.FunId} {f : Func Loc} {l : FrameLayout} {pl : Placed}
    (hf : FnAt S k f l pl) {b : Block Loc} (hb : b ∈ f.blocks.toList) {g : Lir.FunId} {args rets : List Loc}
    (hi : Inst.call g args rets ∈ b.body.toList) {r : GPR} (hr : Loc.reg r ∈ rets) :
    r ∈ l.saved ∨ r ∈ allowedChanges S.env k f :=
  write_allowed hf (facts_inst hb hi (by simpa [Inst.defs] using hr))

theorem resultReg_not_saved {l : FrameLayout} {a : Facts} (hs : l.Sound a) {r : GPR}
    (hr : r ∈ Lir.Conv.resultRegs) : r ∉ l.saved := fun h => by
  have := (hs.savesExact r).1 h
  simp only [saves, List.mem_filter] at this
  simp only [Lir.Conv.resultRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> simp [calleeSaved] at this

theorem mem_take_zip_fst {r : GPR} {vals : List Word} (h : r ∈ Lir.Conv.resultRegs.take vals.length) :
    r ∈ (Lir.Conv.resultRegs.zip vals).map Prod.fst := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 h
  rw [List.getElem?_take] at hi
  split at hi
  · rename_i hlt
    obtain ⟨v, hv⟩ : ∃ v, vals[i]? = some v := ⟨_, List.getElem?_eq_getElem hlt⟩
    exact List.mem_map.2 ⟨(r, v), List.mem_iff_getElem?.2 ⟨i, by rw [List.getElem?_zip_eq_some]; exact ⟨hi, hv⟩⟩, rfl⟩
  · simp at hi

end IxCC.Xv.Stacking.Proof
