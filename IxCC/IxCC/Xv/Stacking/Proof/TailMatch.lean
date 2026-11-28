import IxCC.Xv.Stacking.Proof.RetMatch

/-!
# A tail call keeps the invariant

`tail_match`: when Xl tail-calls `g` from the running activation, and the
machine has run the epilogue, jumped to `g`'s first block, passed its stack
check and run its prologue (with the core, memory and holes that leaves, as
hypotheses), the invariant holds for the callee at its first instruction.
The callee takes the running activation's place (`tailAct`): it returns
where that one would have, its frame ends at the same return slot, and it
keeps the same entry registers and allowed changes, since what a tail
callee may change is among what its tail caller may (`tail_allowed`).
-/

namespace IxCC.Xv.Stacking.Proof

open IxCC.X86 IxCC.X86.Stream

/-- A saved register is one of the callee-saved registers stacking saves. -/
theorem saved_mem {l : FrameLayout} {a : Facts} (hs : l.Sound a) {r : GPR} (h : r ∈ l.saved) :
    r = .rbx ∨ r = .r12 ∨ r = .r13 ∨ r = .r14 := by
  have := (hs.savesExact r).1 h
  simp only [saves, List.mem_filter, calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this.1 with rfl | rfl | rfl | rfl <;> simp

/-- A stacked tail call: the epilogue, then a jump to the callee's entry. -/
theorem term_tail {c : FnCtx} {g : Lir.FunId} {args : List Loc} {post : List Instr} {t : X86.Terminator}
    (h : c.term (.tail g args) = .ok (post, t)) :
    ∃ entry arity, c.funcs.get? g = some (entry, arity) ∧ post = epilogue c.layout ∧
      t = .tailCall (UInt32.ofNat entry) := by
  cases hg : c.funcs.get? g with
  | none =>
    rw [Std.TreeMap.get?_eq_getElem?] at hg
    simp [FnCtx.term, FnCtx.callee, hg, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at h
    split at h <;> simp at h
  | some ea =>
    obtain ⟨entry, arity⟩ := ea
    refine ⟨entry, arity, rfl, ?_⟩
    rw [Std.TreeMap.get?_eq_getElem?] at hg
    simp [FnCtx.term, FnCtx.callee, hg, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at h
    split at h
    · split at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        exact ⟨h.1.symm, h.2.symm⟩
      · simp at h
    · simp at h

/-- What a tail callee may change is among what its tail caller may: its
clobbers by `run`'s clobber check, its result registers by the arity check. -/
theorem tail_allowed {S : Stk} {k : Lir.FunId} {f : Func Loc} {l : FrameLayout} {pl : Placed}
    (hf : FnAt S k f l pl) {b : Block Loc} (hb : b ∈ f.blocks.toList) {g : Lir.FunId} {args : List Loc}
    (ht : b.term = .tail g args) {gf : Func Loc} (hgf : S.p.funcs[g]? = some gf) {r : GPR}
    (hr : r ∈ allowedChanges S.env g gf) : r ∈ allowedChanges S.env k f := by
  simp only [allowedChanges, List.mem_append] at hr
  rcases hr with hr | hr
  · refine mayChange_allowed hf (List.mem_append_left _ ?_)
    simp only [mayChange, List.mem_append, List.mem_flatMap]
    right
    refine ⟨g, ?_, hr⟩
    simp only [callees, List.mem_flatMap, List.mem_append]
    exact ⟨b, hb, .inr (by simp [ht])⟩
  · have e : gf.results = f.results := by
      have := (hf.arities hb).2.2 g args ht
      rw [resultsOf_eq hgf] at this
      exact Option.some.inj this
    rw [e] at hr
    simp only [allowedChanges, List.mem_append]
    exact .inr hr

/-- The running activation's caller (or the wrapper) called with room for
a frame without a stack check. -/
theorem Chain.room {S : Stk} {W : Wrap} {mem : Memory} {holes : Holes} {fr : Xl.Frame} {a : Act}
    {ret : ReturnFrame} {below : List (Xl.Frame × Act × ReturnFrame)} (hc : Chain S W mem holes fr a ret below)
    {xm : Memory} {m : Machine} {holes' : Holes} (hg : Global W xm m holes')
    {f : Func Loc} {l : FrameLayout} {pl : Placed} (hf : FnAt S fr.fn f l pl) :
    W.limit.toNat + slack ≤ a.sp.toNat + l.size + 8 := by
  cases below with
  | nil =>
    obtain ⟨-, hsp, -, -, -⟩ := hc f l pl hf
    rw [hsp]; exact hg.room
  | cons x rest =>
    obtain ⟨fr₁, a₁, ret₁⟩ := x
    obtain ⟨⟨f₁, l₁, pl₁, hf₁⟩, hlink, -⟩ := hc
    obtain ⟨⟨-, hsp, -, -, -⟩, -, hS⟩ := hlink f l pl hf f₁ l₁ pl₁ hf₁
    rw [hsp]; exact hS.room

/-- The running activation replaced by its tail callee: the same return,
entry registers and allowed changes, a frame ending where it ended, and no
incoming cells. -/
theorem Chain.tail {S : Stk} {W : Wrap} {mem : Memory} {holes : Holes} {fr fr' : Xl.Frame} {a a' : Act}
    {ret : ReturnFrame} {f : Func Loc} {l : FrameLayout} {pl : Placed} (hf : FnAt S fr.fn f l pl)
    {gf : Func Loc} {gl : FrameLayout} {gpl : Placed} (hfg : FnAt S fr'.fn gf gl gpl)
    (hsp : a'.sp.toNat + gl.size = a.sp.toNat + l.size) (hentry : a'.entry = a.entry) (hallow : a'.allow = a.allow)
    (hin : gf.facts.inArgs = 0) (hres : gf.results = f.results) :
    ∀ {below : List (Xl.Frame × Act × ReturnFrame)}, Chain S W mem holes fr a ret below →
      Chain S W mem holes fr' a' ret below
  | [], h => fun f₀ l₀ pl₀ hf₀ => by
      obtain ⟨e₁, e₂, -⟩ := hfg.unique hf₀
      subst e₁ e₂
      obtain ⟨h₁, h₂, h₃, h₄, -, h₆⟩ := h f l pl hf
      exact ⟨h₁, by omega, by rw [hentry]; exact h₃, by rw [hallow]; exact h₄, hin, by rw [hres]; exact h₆⟩
  | (_, _, _) :: _, ⟨hex, hlink, hrest⟩ =>
      ⟨hex, fun f₀ l₀ pl₀ hf₀ f₁ l₁ pl₁ hf₁ => by
        obtain ⟨e₁, e₂, -⟩ := hfg.unique hf₀
        subst e₁ e₂
        obtain ⟨⟨h₁, h₂, h₃, h₄, h₅⟩, hA, hS⟩ := hlink f l pl hf f₁ l₁ pl₁ hf₁
        exact ⟨⟨h₁, by omega, by rw [hentry]; exact h₃, by rw [hallow]; exact h₄, by rw [hin]; omega⟩, hA, hS⟩,
       hrest⟩

/-- The tail callee at entry: its frame ends at its tail caller's return slot. -/
def tailAct (a : Act) (slot : Word) (gl : FrameLayout) : Act :=
  ⟨slot - UInt64.ofNat gl.size, a.entry, a.allow, a.regs⟩

theorem tail_match {S : Stk} {W : Wrap} {s : Xl.State} {m : Machine} {holes : Holes} {fr : Xl.Frame} {a : Act}
    {ret : ReturnFrame} {below : List (Xl.Frame × Act × ReturnFrame)} (hm : Match S W s m holes fr a ret below)
    {f : Func Loc} {l : FrameLayout} {pl : Placed} (htop : Top S W s m holes fr a ret f l pl)
    {b : Block Loc} {codes : List (List Instr)} {post : List Instr} {t : X86.Terminator}
    (hpos : XlPos S fr f l pl b codes post t) {g : Lir.FunId} {args : List Loc}
    (hterm : b.term = .tail g args) (hnA : args.length ≤ Xl.nArgRegs) (hconvA : Xl.conventionArgs args = true)
    {vals : List Word} (hread : Xl.readAll s.regs fr args = some vals) {callee : Xl.Frame} {regs' : Xl.Regs}
    (henter : Xl.enter S.p g vals = some (callee, regs'))
    {gf : Func Loc} {gl : FrameLayout} {gpl : Placed} (hfg : FnAt S g gf gl gpl)
    {b0 : Block Loc} {codes0 : List (List Instr)} {post0 : List Instr} {t0 : X86.Terminator}
    (hpos0 : XlPos S callee gf gl gpl b0 codes0 post0 t0)
    {core_f : Core} {holes_f : Holes}
    (hf_rsp : core_f.readReg .rsp = ret.returnSlot - UInt64.ofNat gl.size)
    (hf_regs : ∀ r, r ≠ .rsp → r ≠ .r11 → r ∉ l.saved → core_f.readReg r = m.core.readReg r)
    (hf_kept : ∀ r, r ∉ a.allow → r ≠ .rsp → core_f.readReg r = a.entry r)
    (hf_r : core_f.memory.readable = m.core.memory.readable) (hf_w : core_f.memory.writable = m.core.memory.writable)
    (hf_bytes : ∀ x, ¬((ret.returnSlot - UInt64.ofNat gl.size).toNat ≤ x.toNat ∧ x.toNat < ret.returnSlot.toNat) →
      core_f.memory.bytes x = m.core.memory.bytes x)
    (hf_saves : ∀ r o, (r, o) ∈ gl.saveOff →
      core_f.memory.read64 (ret.returnSlot - UInt64.ofNat gl.size + UInt64.ofNat o) = a.entry r)
    (hh : ∀ x, holes_f x → holes x)
    (hsd : ∀ r o, (r, o) ∈ gl.saveOff →
      ReadableData holes_f (ret.returnSlot - UInt64.ofNat gl.size + UInt64.ofNat o) 8)
    (hlow : W.limit.toNat ≤ (ret.returnSlot - UInt64.ofNat gl.size).toNat)
    (hroom : gf.facts.calls = true → W.limit.toNat + slack ≤ (ret.returnSlot - UInt64.ofNat gl.size).toNat) :
    Match S W { s with regs := regs', stack := callee :: below.map (·.1) }
      (inFrame core_f (UInt32.ofNat ((ctxOf S.placed gpl).labelBase + 0)) (offsetOf gl 0 0 codes0) m.returns)
      holes_f callee (tailAct a ret.returnSlot gl) ret below := by
  -- The callee
  simp only [Xl.enter, Option.bind_eq_bind, Option.bind_eq_some_iff] at henter
  obtain ⟨gf', hgf', u, hguard, he⟩ := henter
  have hgf : gf' = gf := Option.some.inj (hgf'.symm.trans hfg.func)
  subst hgf
  have hplen : gf'.params.length = vals.length := by
    by_cases hl : gf'.params.length = vals.length
    · exact hl
    · simp [guard, hl] at hguard
  simp only [Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  -- The tail caller's facts
  have hg := hm.global
  have hf := htop.fn
  have hs := hf.checks.1
  have gs := hfg.checks.1
  have hact := htop.act
  have span := hact.span hg.top
  have hbmem : b ∈ f.blocks.toList := List.mem_of_getElem? (by simpa using hpos.block)
  have hgbd := gs.bounded
  have hlo := hg.low
  have hlow₀ := span.low
  have hhigh := span.high
  have hal := hact.align
  have htopE := hg.top
  obtain ⟨hlenA, hgetA⟩ := readAll_get hread
  have hkin : gf'.facts.inArgs = 0 := by rw [facts_inArgs, hplen, hlenA]; omega
  have hdrop : vals.drop Xl.nArgRegs = [] := List.drop_eq_nil_of_le (by omega)
  -- Numbers
  have hrs : ret.returnSlot.toNat = a.sp.toNat + l.size := by
    rw [hact.slot]; exact addr_toNat (by omega)
  have hRc : (ret.returnSlot - UInt64.ofNat gl.size).toNat = a.sp.toNat + l.size - gl.size := by
    rw [sub_ofNat_toNat (by rw [hrs]; simp only [maxFrame, slack] at hlo hgbd; omega), hrs]
  have hgle : gl.size ≤ a.sp.toNat + l.size := by simp only [maxFrame, slack] at hlo hgbd; omega
  -- The callee's frame on the stack
  have gspan : FrameSpan W (ret.returnSlot - UInt64.ofNat gl.size) gl gf'.facts.inArgs :=
    ⟨hlow, by rw [hRc, hkin]; omega, by rw [hkin]; omega, htopE⟩
  -- Bytes at or above the return slot are kept
  have hkeepUp : ∀ x, ret.returnSlot.toNat ≤ x.toNat → core_f.memory.bytes x = m.core.memory.bytes x :=
    fun x hx => hf_bytes x fun ⟨_, h⟩ => by omega
  have hInStack : ∀ x, (ret.returnSlot - UInt64.ofNat gl.size).toNat ≤ x.toNat → x.toNat < ret.returnSlot.toNat →
      W.InStack x := fun x h₁ h₂ => ⟨by omega, by omega⟩
  have hbytesG : ∀ x, (¬W.InStack x ∨ W.entrySp.toNat ≤ x.toNat) → core_f.memory.bytes x = m.core.memory.bytes x :=
    fun x hx => hf_bytes x fun ⟨h₁, h₂⟩ => by
      rcases hx with hx | hx
      · exact hx (hInStack x h₁ h₂)
      · omega
  have hreg15 : core_f.readReg .r15 = W.ctx := by
    rw [hf_regs _ (by decide) (by decide) (fun h => by rcases saved_mem hs h with h | h | h | h <;> cases h)]
    exact htop.agree.ctxReg
  -- The global facts
  have hglob : Global W s.mem (inFrame core_f (UInt32.ofNat ((ctxOf S.placed gpl).labelBase + 0))
      (offsetOf gl 0 0 codes0) m.returns) holes_f :=
    Global.mono hg hf_r hf_w hbytesG (fun x hx => .inl (hh x hx)) hreg15 hg.entry.outer
  refine ⟨rfl, rfl, hm.returns, hm.ctx, ⟨gf', gl, gpl, ?_⟩, ?_, hglob⟩
  · -- The callee's running activation
    refine ⟨hfg, ⟨b0, codes0, post0, t0, hpos0, rfl⟩, ⟨entryRegs_size vals, ?_, hreg15, ?_, ?_, ?_⟩, hf_rsp,
      fun r hr hsp => .inr (hf_kept r hr hsp), ?_, ?_, hroom, ?_⟩
    · intro r hr v hv
      obtain ⟨i, hri, hvi⟩ := entryRegs_get hv
      have hrmem : r ∈ Lir.Conv.argRegs := List.mem_of_getElem? hri
      have hia : i < args.length := by rw [← hlenA]; exact (List.getElem?_eq_some_iff.1 hvi).1
      have harg := conventionArgs_get hconvA hia
      rw [argLoc_reg hri] at harg
      obtain ⟨v', hv', hrd⟩ := hgetA _ _ harg
      have e : v' = v := Option.some.inj (hv'.symm.trans hvi)
      subst e
      rw [Xl.read_reg hr] at hrd
      have hne1 : r ≠ .rsp := by intro e; subst e; simp [Lir.Conv.argRegs] at hrmem
      have hne2 : r ≠ .r11 := by intro e; subst e; simp [Lir.Conv.argRegs] at hrmem
      have hne3 : r ∉ l.saved := fun h => by
        rcases saved_mem hs h with rfl | rfl | rfl | rfl <;> simp [Lir.Conv.argRegs] at hrmem
      show core_f.readReg r = v'
      rw [hf_regs r hne1 hne2 hne3]
      exact htop.agree.regsRel r hr v' hrd
    · have hin := htop.agree.inside
      show Inside s.mem core_f.memory
      refine ⟨fun x hx => by rw [hf_r]; exact hin.readable x hx, fun x hx => by rw [hf_w]; exact hin.writable x hx,
        fun x hx => ?_⟩
      rw [hf_bytes x fun ⟨h₁, h₂⟩ => ?_]
      · exact hin.bytes x hx
      · have hst := hg.stack x (hInStack x h₁ h₂)
        rcases hx with hx | hx
        · rw [hst.1] at hx; cases hx
        · rw [hst.2.1] at hx; cases hx
    · intro x hx v hv
      cases x with
      | reg r => simp [Loc.isCell] at hx
      | slot i => simp [Xl.read] at hv
      | outArg i => simp [Xl.read] at hv
      | inArg i =>
        have hv' : (vals.drop Xl.nArgRegs)[i]? = some v := by simpa [Xl.read] using hv
        rw [hdrop] at hv'
        simp at hv'
    · exact frameCells_of hglob gs gspan hfg.play hfg.pfacts hf_rsp
    · refine ⟨fun r o hro => hf_saves r o hro, fun r o hro => hsd r o hro,
        fun r hr => hact.allowed r (tail_allowed hf hbmem hterm hfg.func hr), ?_, ?_, hact.snapshot, ?_, hlow,
        gspan.high, gspan.inBound⟩
      · simp only [tailAct]
        exact (UInt64.sub_add_cancel _ _).symm
      · show core_f.memory.read64 ret.returnSlot = _
        rw [← hact.retAddr]
        exact read64_keep fun j hj => hkeepUp _ (by rw [addr_toNat (by omega)]; omega)
      · simp only [tailAct]; rw [hRc]; omega
    · intro x hx v hv mm _
      cases x with
      | reg r => simp [Loc.isCell] at hx
      | slot i => simp [Xl.read] at hv
      | outArg i => simp [Xl.read] at hv
      | inArg i =>
        have hv' : (vals.drop Xl.nArgRegs)[i]? = some v := by simpa [Xl.read] using hv
        rw [hdrop] at hv'
        simp at hv'
    · show ((vals.drop Xl.nArgRegs).toArray).size = gf'.facts.inArgs
      rw [hkin, hdrop]; rfl
  · -- The suspended activations, below the callee as they were below the tail caller
    have hres : gf'.results = f.results := by
      have := (hf.arities hbmem).2.2 g args hterm
      rw [resultsOf_eq hfg.func] at this
      exact Option.some.inj this
    refine Chain.mono (B := ret.returnSlot.toNat) htopE (fun x h₁ _ => hkeepUp x h₁) (fun x hx => .inl (hh x hx))
      (Chain.tail (a := a) (a' := tailAct a ret.returnSlot gl) hf hfg (by simp only [tailAct]; rw [hRc]; omega) rfl rfl
        hkin hres hm.chain) ?_
    intro fr₁ a₁ ret₁ rest e f₁ l₁ pl₁ hf₁
    have hc0 := hm.chain
    rw [e] at hc0
    obtain ⟨-, hlink, -⟩ := hc0
    have := (hlink f l pl hf f₁ l₁ pl₁ hf₁).1.sp
    omega

end IxCC.Xv.Stacking.Proof
