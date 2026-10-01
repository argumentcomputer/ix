import Compilatrix.Xv.Stacking.Proof.WrapperHead

/-!
# The export wrapper's call to `main`

`CallCore`: the wrapper's core when it calls `main`: `rsp` at `entrySp`,
the context register loaded, `main`'s arguments in the internal
convention's registers, and the context cells and the words above
`entrySp` written. `wrapper_call`: the call, `main`'s stack check (if it has
one) and its prologue reach the invariant for `main`'s first state, with
the wrapper's tail as the return continuation (`WrapCont`); or the stack
check fails and the export exits with status 2.
-/

namespace Compilatrix.Xv.Stacking.Proof

open Compilatrix.X86 Compilatrix.X86.Stream

/-- The wrapper's core at its call to `main` with arguments `args`. -/
structure CallCore (core₀ : Core) (retAddr ctx : Word) (args : List Word) (C : Core) : Prop where
  rsp : C.readReg .rsp = entrySpOf core₀
  r15 : C.readReg .r15 = ctx
  args : RegsRel (Xl.entryRegs args) C
  readable : C.memory.readable = core₀.memory.readable
  writable : C.memory.writable = core₀.memory.writable
  bytes : ∀ x, ¬InEntryStack core₀ ctx x → (∀ i < 16, x ≠ ctx - 64 + UInt64.ofNat i) →
    C.memory.bytes x = core₀.memory.bytes x
  cell : C.memory.read64? (ctx - 64) = .ok (entrySpOf core₀)
  limit : C.memory.read64 (ctx - 56) = limitOf core₀ ctx
  saves : ∀ i < 7, C.memory.read64? (entrySpOf core₀ + UInt64.ofNat (8 + 8 * i)) = .ok (saveWord core₀ retAddr i)

/-- `main`'s first block, with its position. -/
theorem main_start {S : Stk} {args : List Word} {mem : Memory} {ctx : Word} {s₀ : Xl.State}
    (hs₀ : Xl.State.initial S.p args mem ctx = some s₀) {mf : Func Loc} {ml : FrameLayout} {mpl : Placed}
    (hfm : FnAt S S.p.main mf ml mpl) :
    ∃ b0 codes0 post0 t0, ∀ fr, s₀.stack = [fr] → XlPos S fr mf ml mpl b0 codes0 post0 t0 := by
  obtain ⟨b0, hb0⟩ := first_block hfm
  simp only [Xl.State.initial, Option.bind_eq_bind, Option.bind_eq_some_iff, Xl.enter] at hs₀
  obtain ⟨⟨fr₀, regs₀⟩, ⟨mf', hmf', u, hguard, he⟩, hs₀⟩ := hs₀
  simp only [Option.some.injEq, Prod.mk.injEq] at he hs₀
  obtain ⟨rfl, rfl⟩ := he
  subst hs₀
  have hfm' : FnAt S ({ fn := S.p.main, label := 0, pos := 0, inArgs := (args.drop Xl.nArgRegs).toArray } :
      Xl.Frame).fn mf ml mpl := hfm
  obtain ⟨-, codes0, post0, t0, hpos0⟩ := xlPos_start hfm' hb0
  refine ⟨b0, codes0, post0, t0, fun fr hfr => ?_⟩
  simp only [List.cons.injEq, and_true] at hfr
  subst hfr
  exact hpos0

/-- From `main`'s first label, after the call: the prologue, then the
invariant for `main`'s first state. -/
theorem entry_prologue {S : Stk} {core₀ : Core} {retAddr ctx : Word} {mem : Memory}
    (base : EntryBase core₀ retAddr mem ctx) {args : List Word} (hlenA : args.length ≤ Xl.nArgRegs)
    {s₀ : Xl.State} (hs₀ : Xl.State.initial S.p args mem ctx = some s₀)
    {C : Core} (hC : CallCore core₀ retAddr ctx args C) {blk : BlockId} {off : Nat}
    {mf : Func Loc} {ml : FrameLayout} {mpl : Placed} (hfm : FnAt S S.p.main mf ml mpl) (hres : mf.results = 1)
    {core' : Core} {holes₁ : Holes}
    (h_rsp : core'.readReg .rsp = entrySpOf core₀ - 8)
    (h_regs : ∀ r, r ≠ .rsp → r ≠ .r11 → core'.readReg r = C.readReg r)
    (h_r11 : core'.readReg .r11 ≠ C.readReg .r11 → GPR.r11 ∈ allowedChanges S.env S.p.main mf)
    (h_mem : core'.memory = C.memory.write64 (entrySpOf core₀ - 8) (callFrame C blk off).continuation.encode)
    (hh₁ : ∀ x, holes₁ x → (entrySpOf core₀ - 8).toNat ≤ x.toNat ∧ x.toNat < (entrySpOf core₀).toNat)
    (hlow : (limitOf core₀ ctx).toNat ≤ (entrySpOf core₀ - 8 - UInt64.ofNat ml.size).toNat)
    (hroom : mf.facts.calls = true → (limitOf core₀ ctx).toNat + slack ≤
      (entrySpOf core₀ - 8 - UInt64.ofNat ml.size).toNat) :
    ∃ holes' m' fr₀, SafeSteps Runtime.rejecting S.cs (prologue ml).length holes₁
        (inFrame core' (UInt32.ofNat ((ctxOf S.placed mpl).labelBase + 0)) 0 [callFrame C blk off]) holes' m' ∧
      s₀.stack = [fr₀] ∧
      Match S (entryWrap core₀ retAddr ctx C blk off) s₀ m' holes' fr₀
        (calleeAct S S.p.main mf ml (entrySpOf core₀) C) (callFrame C blk off) [] := by
  obtain ⟨b0, codes0, post0, t0, hpos0⟩ := main_start hs₀ hfm
  have gs := hfm.checks.1
  have hgbd := gs.bounded
  have hlo := base.low
  have htop := base.top
  have hE := base.entrySp_toNat
  have hL := base.limit_toNat
  have hR8 : (entrySpOf core₀ - 8).toNat = (entrySpOf core₀).toNat - 8 := sub8_toNat (by
    simp only [maxFrame, slack] at hlo; omega)
  have hRc : (entrySpOf core₀ - 8 - UInt64.ofNat ml.size).toNat = (entrySpOf core₀).toNat - 8 - ml.size := by
    rw [sub_ofNat_toNat (by rw [hR8]; simp only [maxFrame, slack] at hlo hgbd; omega), hR8]
  -- The prologue's code
  obtain ⟨fr₀, hfr₀, hcl⟩ : ∃ fr₀, s₀.stack = [fr₀] ∧ fr₀.label = 0 := by
    have hs₀' := hs₀
    simp only [Xl.State.initial, Option.bind_eq_bind, Option.bind_eq_some_iff, Xl.enter, Option.some.injEq] at hs₀'
    obtain ⟨⟨fr, regs⟩, ⟨mf', -, u, -, he⟩, hs⟩ := hs₀'
    simp only [Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨_, by rw [← hs], rfl⟩
  have hpos := hpos0 fr₀ hfr₀
  have hfound := hpos.found
  rw [hcl] at hfound
  have hlist : ({ instructions := (preOf ml 0 ++ codes0.flatten ++ post0).toArray, terminator := t0 } :
      X86.Block).instructions.toList = [] ++ prologue ml ++ (codes0.flatten ++ post0) := by simp [preOf]
  obtain ⟨hk, hsz⟩ := block_fits (cs := S.cs) hfound
  have hfound' : S.cs.program.blocks[(UInt32.ofNat ((ctxOf S.placed mpl).labelBase + 0)).toNat]? =
      some { instructions := (preOf ml 0 ++ codes0.flatten ++ post0).toArray, terminator := t0 } := by
    rw [UInt32.toNat_ofNat_of_lt' hk]; exact hfound
  have hseg := Straight.Segment.of_block hfound' hlist
  simp only [List.length_nil] at hseg
  have hfits : (prologue ml).length < UInt32.size := by
    simp only [List.size_toArray, List.length_append, preOf, ↓reduceIte] at hsz
    simp only [UInt32.size]; omega
  have hw : ∀ x, (entrySpOf core₀ - 8 - UInt64.ofNat ml.size).toNat ≤ x.toNat → x.toNat < (entrySpOf core₀ - 8).toNat →
      core'.memory.writable x = true := fun x h₁ h₂ => by
    rw [h_mem, Memory.write64_writable, hC.writable]
    refine (base.stack x ?_).2.1
    simp only [InEntryStack]; rw [hRc] at h₁; rw [hR8] at h₂; rw [hL] at hlow; rw [hRc] at hlow; omega
  have hdis : ∀ frame ∈ [callFrame C blk off], ∀ i < 8,
      (entrySpOf core₀ - 8).toNat ≤ (frame.returnSlot + UInt64.ofNat i).toNat := by
    intro frame hfr i hi
    simp only [List.mem_singleton] at hfr
    subst hfr
    simp only [callFrame, hC.rsp]
    rw [addr_toNat (by rw [hR8]; omega)]; omega
  obtain ⟨mem', holes', hst, hr', hw', hb', hv', hh', hd'⟩ :=
    prologue_steps (returns := [callFrame C blk off]) (holes := holes₁) gs hseg hfits h_rsp
      (by rw [hR8]; simp only [maxFrame, slack] at hlo hgbd; omega) hw hdis
  have hoff : offsetOf ml 0 0 codes0 = (prologue ml).length := by simp [offsetOf, preOf]
  obtain ⟨fr₀', hfr₀', hm⟩ := entry_match (S := S) base hlenA hs₀ hC.rsp hC.r15 hC.args hC.readable hC.writable hC.bytes
    hC.cell hC.limit hC.saves hfm hres hpos0
    (core_f := { core'.setReg .rsp (entrySpOf core₀ - 8 - UInt64.ofNat ml.size) with memory := mem' }) (holes_f := holes')
    (blk := blk) (off := off)
    (by simp [Core.readReg, Core.setReg, Registers.set])
    (fun r h1 h2 => by
      show (core'.setReg .rsp _).readReg r = _
      rw [Validate.readReg_setReg, if_neg h1, h_regs r h1 h2])
    (fun h => h_r11 fun e => h (by
      show (core'.setReg .rsp (entrySpOf core₀ - 8 - UInt64.ofNat ml.size)).readReg .r11 = C.readReg .r11
      rw [Validate.readReg_setReg, if_neg (by decide)]; exact e))
    (by show mem'.readable = _; rw [hr', h_mem]; simp) (by show mem'.writable = _; rw [hw', h_mem]; simp)
    (fun x hx => by
      show mem'.bytes x = _
      rw [hb' x (fun ⟨h1, h2⟩ => hx ⟨h1, by rw [hR8] at h2; omega⟩), h_mem]
      exact write64_bytes_off (by rw [hR8]; omega) (fun ⟨h1, h2⟩ => hx ⟨by rw [hRc]; rw [hR8] at h1; simp only [maxFrame, slack] at hlo hgbd; omega,
        by rw [hR8] at h2; simp only [maxFrame, slack] at hlo; omega⟩))
    (by
      show mem'.read64 (entrySpOf core₀ - 8) = _
      rw [read64_congr (m := core'.memory) (m' := mem') fun i hi => hb' _ fun ⟨_, h2⟩ => by
        rw [addr_toNat (by rw [hR8]; omega)] at h2; omega, h_mem]
      exact Memory.read64_write64 _ _ _)
    (fun r o hro => by
      show mem'.read64 _ = _
      rw [hv' r o hro, h_regs r (saved_ne_rsp gs (saveOff_mem hro)) (by
        intro e; subst e
        have := (gs.savesExact _).1 (saveOff_mem hro)
        simp [saves, calleeSaved] at this)])
    (fun x hx => by
      obtain ⟨h1, h2⟩ := hh₁ x (hh' x hx)
      exact ⟨h1, h2⟩)
    (fun r o hro => hd' r o hro) hlow hroom
  rw [hfr₀] at hfr₀'
  simp only [List.cons.injEq, and_true] at hfr₀'
  subst hfr₀'
  rw [hoff] at hm
  exact ⟨holes', _, fr₀, hst, hfr₀, hm⟩

/-- The failure exit's frame while the wrapper's call frame is the only
ghost frame (or there is none), the context cells and the words above
`entrySp` as at the call, and holes only in the call's return slot. -/
theorem entryFrame_of {core₀ : Core} {retAddr ctx : Word} {mem : Memory} (base : EntryBase core₀ retAddr mem ctx)
    {args : List Word} {C : Core} (hC : CallCore core₀ retAddr ctx args C) {m : Machine} {holes : Holes}
    (hr : m.core.memory.readable = C.memory.readable)
    (hb : ∀ x, ¬((entrySpOf core₀ - 8).toNat ≤ x.toNat ∧ x.toNat < (entrySpOf core₀).toNat) →
      m.core.memory.bytes x = C.memory.bytes x)
    (hh : ∀ x, holes x → (entrySpOf core₀ - 8).toNat ≤ x.toNat ∧ x.toNat < (entrySpOf core₀).toNat)
    (h15 : m.core.readReg .r15 = ctx)
    (hret : m.returns = [] ∨ ∃ f₁, m.returns = [f₁] ∧ f₁.returnSlot + 8 = entrySpOf core₀) :
    EntryFrame ctx (entrySpOf core₀) core₀ retAddr m holes := by
  have hlo := base.low
  have hbud := base.budget
  simp only [slack] at hbud
  have htop := base.top
  have hE := base.entrySp_toNat
  have hL := base.limit_toNat
  have hR8 : (entrySpOf core₀ - 8).toNat = (entrySpOf core₀).toNat - 8 := sub8_toNat (by
    simp only [maxFrame, slack] at hlo; omega)
  have hctxOut : ∀ i < 16, ¬((entrySpOf core₀ - 8).toNat ≤ (ctx - 64 + UInt64.ofNat i).toNat ∧
      (ctx - 64 + UInt64.ofNat i).toNat < (entrySpOf core₀).toNat) := fun i hi ⟨h₁, h₂⟩ =>
    (base.ctxCells i hi).2.2.2.2 ⟨by rw [hR8] at h₁; omega, by omega⟩
  have hsv : ∀ i < 7, ∀ j < 8, (entrySpOf core₀ + UInt64.ofNat (8 + 8 * i) + UInt64.ofNat j).toNat =
      (entrySpOf core₀).toNat + (8 + 8 * i) + j := fun i hi j hj => by
    rw [addr_toNat (by rw [addr_toNat (by omega)]; omega), addr_toNat (by omega)]
  refine ⟨?_, fun j hj hx => hctxOut j (by omega) (hh _ hx), ?_, fun i hi => ?_, fun i hi j hj hx => ?_, h15, ?_⟩
  · rw [read64?_keep hr fun j hj => hb _ (hctxOut j (by omega))]
    exact hC.cell
  · rcases hret with h | ⟨f₁, h, h₁⟩
    · exact .inl h
    · exact .inr ⟨[], f₁, by simpa using h, h₁, by simp⟩
  · rw [read64?_keep hr fun j hj => hb _ fun ⟨_, h₂⟩ => by rw [hsv i hi j hj] at h₂; omega]
    exact hC.saves i hi
  · have := (hh _ hx).2
    rw [hsv i hi j hj] at this; omega
  · simp [entrySpOf]

/-- The wrapper's call to `main` and `main`'s stack check and prologue: the
invariant for `main`'s first state, or the stack check fails and the export
exits with status 2. -/
theorem wrapper_call {S : Stk} {core₀ : Core} {retAddr ctx : Word} {mem : Memory}
    (base : EntryBase core₀ retAddr mem ctx) {args : List Word} (hlenA : args.length ≤ Xl.nArgRegs)
    {s₀ : Xl.State} (hs₀ : Xl.State.initial S.p args mem ctx = some s₀)
    {C : Core} (hC : CallCore core₀ retAddr ctx args C)
    {mf : Func Loc} {ml : FrameLayout} {mpl : Placed} (hfm : FnAt S S.p.main mf ml mpl) (hres : mf.results = 1)
    {blk : BlockId} {pre : List Instr}
    (code : BlockCode S.cs blk (pre ++ [Instr.call (UInt32.ofNat mpl.start)] ++ wrapperTail) .ret)
    {holes : Holes} (hempty : ∀ x, ¬holes x) :
    (∃ n holes' after, SafeSteps Runtime.rejecting S.cs n holes (inFrame C blk pre.length []) holes' after ∧
      Exit core₀ retAddr 2 0 after ∧ ReadableData holes' (after.core.readReg .rsp) 8) ∨
    (∃ n holes' m fr₀ a, SafeSteps Runtime.rejecting S.cs n holes (inFrame C blk pre.length []) holes' m ∧
      s₀.stack = [fr₀] ∧ Match S (entryWrap core₀ retAddr ctx C blk pre.length) s₀ m holes' fr₀ a
        (callFrame C blk pre.length) [] ∧ WrapCont S (entryWrap core₀ retAddr ctx C blk pre.length)) := by
  have gs := hfm.checks.1
  have hgbd := gs.bounded
  have hlo := base.low
  have hbud := base.budget
  have htop := base.top
  have hal := base.align
  have hE := base.entrySp_toNat
  have hL := base.limit_toNat
  have hbud' : 64 ≤ (budgetOf core₀ ctx).toNat := base.budget
  have hlo' : 2 ^ 20 + 64 + (budgetOf core₀ ctx).toNat + 56 ≤ (core₀.readReg .rsp).toNat := base.low
  have hR8 : (entrySpOf core₀ - 8).toNat = (entrySpOf core₀).toNat - 8 := sub8_toNat (by
    simp only [maxFrame, slack] at hlo; omega)
  have hRc : (entrySpOf core₀ - 8 - UInt64.ofNat ml.size).toNat = (entrySpOf core₀).toNat - 8 - ml.size := by
    rw [sub_ofNat_toNat (by rw [hR8]; simp only [maxFrame, slack] at hlo hgbd; omega), hR8]
  have hbyte8 : ∀ i < 8, (entrySpOf core₀ - 8 + UInt64.ofNat i).toNat = (entrySpOf core₀).toNat - 8 + i :=
    fun i hi => by rw [addr_toNat (by rw [hR8]; omega), hR8]
  -- The wrapper's tail is the call's continuation.
  have hwc : WrapCont S (entryWrap core₀ retAddr ctx C blk pre.length) :=
    ⟨blk, pre ++ [Instr.call (UInt32.ofNat mpl.start)], by simpa using code, by simp [entryWrap, callFrame]⟩
  -- The call
  have hfound := code.found
  have hseg : Straight.Segment S.cs blk pre.length [Instr.call (UInt32.ofNat mpl.start)] :=
    Straight.Segment.of_block hfound (pre := pre) (post := wrapperTail) (by simp)
  have hfits := code.fits
  simp only [List.length_append, List.length_singleton] at hfits
  obtain ⟨b0, codes0, post0, t0, hpos0⟩ := main_start hs₀ hfm
  obtain ⟨fr₀, hfr₀, hcl⟩ : ∃ fr₀, s₀.stack = [fr₀] ∧ fr₀.label = 0 := by
    have hs₀' := hs₀
    simp only [Xl.State.initial, Option.bind_eq_bind, Option.bind_eq_some_iff, Xl.enter, Option.some.injEq] at hs₀'
    obtain ⟨⟨fr, regs⟩, ⟨mf', -, u, -, he⟩, hs⟩ := hs₀'
    simp only [Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨_, by rw [← hs], rfl⟩
  have hfound0 := (hpos0 fr₀ hfr₀).found
  rw [hcl] at hfound0
  have hvalid : S.cs.program.hasBlock (UInt32.ofNat mpl.start) = true := by
    by_cases hc : FrameLayout.checked mf.facts ml = true
    · obtain ⟨pl', hpl', -, -, -, hblk⟩ := check_at S hfm.func hfm.layout hc
      have e : pl' = mpl := Option.some.inj (hpl'.symm.trans hfm.placed)
      subst e
      exact hasBlock_of hblk
    · have hsh : (ctxOf S.placed mpl).labelBase + 0 = mpl.start := by
        simp [ctxOf, shiftOf, hfm.play, hfm.pfacts, hc]
      rw [hsh] at hfound0
      exact hasBlock_of hfound0
  have haligned : SysV.callSiteAligned (C.readReg .rsp) = true := by
    have hRmod : (entrySpOf core₀).toNat % 16 = 0 := by rw [hE]; omega
    simp only [SysV.callSiteAligned, hC.rsp, beq_iff_eq]
    apply word_eq
    rw [UInt64.toNat_mod]
    simpa using hRmod
  have hInS : ∀ x, (entrySpOf core₀ - 8).toNat ≤ x.toNat → x.toNat < (entrySpOf core₀).toNat →
      InEntryStack core₀ ctx x := fun x h₁ h₂ => by
    simp only [InEntryStack]; rw [hR8] at h₁; rw [hE] at h₂; simp only [maxFrame, slack] at hlo; omega
  have hwritable : Memory.rangeAllowed C.memory.writable (C.readReg .rsp - 8) 8 = true := by
    rw [hC.rsp]
    refine (rangeAllowed_iff _ _ _).2 fun i hi => ?_
    rw [hC.writable]
    exact (base.stack _ (hInS _ (by rw [hbyte8 i hi]; omega) (by rw [hbyte8 i hi]; omega))).2.1
  have hcall := Straight.Segment.safe_call hseg (by simp only [UInt32.size] at hfits ⊢; omega) hvalid
    Runtime.rejecting (holes := holes) (returns := []) haligned hwritable (by intro f hf; simp at hf)
  -- After the call
  have h1rsp : (callCore C blk pre.length).readReg .rsp = entrySpOf core₀ - 8 := by
    show (C.setReg .rsp (C.readReg .rsp - 8)).readReg .rsp = _
    rw [Validate.readReg_setReg, if_pos rfl, hC.rsp]
  have h1regs : ∀ r, r ≠ .rsp → (callCore C blk pre.length).readReg r = C.readReg r := fun r hr => by
    show (C.setReg .rsp (C.readReg .rsp - 8)).readReg r = _
    rw [Validate.readReg_setReg, if_neg hr]
  have h1mem : (callCore C blk pre.length).memory = C.memory.write64 (entrySpOf core₀ - 8)
      (callFrame C blk pre.length).continuation.encode := by
    show C.memory.write64 (C.readReg .rsp - 8) _ = _
    rw [hC.rsp]
  have hh₁ : ∀ x, addRange holes (C.readReg .rsp - 8) 8 x →
      (entrySpOf core₀ - 8).toNat ≤ x.toNat ∧ x.toNat < (entrySpOf core₀).toNat := by
    intro x hx
    rcases hx with h | ⟨i, hi, rfl⟩
    · exact absurd h (hempty x)
    · rw [hC.rsp, hbyte8 i hi, hR8]; omega
  have hb1 : ∀ x, ¬((entrySpOf core₀ - 8).toNat ≤ x.toNat ∧ x.toNat < (entrySpOf core₀).toNat) →
      (callCore C blk pre.length).memory.bytes x = C.memory.bytes x := fun x hx => by
    rw [h1mem]; exact write64_bytes_off (by rw [hR8]; omega) fun ⟨h₁, h₂⟩ => hx ⟨h₁, by rw [hR8] at h₂; omega⟩
  have hr15 : (callCore C blk pre.length).readReg .r15 = ctx := by rw [h1regs _ (by decide), hC.r15]
  by_cases hc : FrameLayout.checked mf.facts ml = true
  · -- `main`'s stack check
    obtain ⟨pl', hpl', -, -, -, hblk⟩ := check_at S hfm.func hfm.layout hc
    have e : pl' = mpl := Option.some.inj (hpl'.symm.trans hfm.placed)
    subst e
    obtain ⟨hk, -⟩ := block_fits (cs := S.cs) hblk
    have hbc : BlockCode S.cs (UInt32.ofNat pl'.start) [Instr.lea .r11 (rspBelow (ml.size + slack))]
        (.branch cmpRM [.reg .r11, .mem stackLimitCell] .unsignedLt 1 (UInt32.ofNat (pl'.start + 1))) :=
      ⟨by rw [UInt32.toNat_ofNat_of_lt' (by simpa [UInt32.size] using hk)]; exact hblk, by simp [UInt32.size]⟩
    have hexit : ExitGroupAt S.cs := fun j hj => exit_at S.ok hj
    have h2 : S.cs.program.hasBlock 1 = true := (hexit.fail (k := 2) (by decide) (by decide)).hasBlock
    have hsh : (ctxOf S.placed pl').labelBase + 0 = pl'.start + 1 := by
      simp [ctxOf, shiftOf, hfm.play, hfm.pfacts, hc]
    have hn : S.cs.program.hasBlock (UInt32.ofNat (pl'.start + 1)) = true := by
      have := hfound0; rw [hsh] at this; exact hasBlock_of this
    have hctx8 : ∀ j < 8, ctx - 56 + UInt64.ofNat j = ctx - 64 + UInt64.ofNat (8 + j) := by
      intro j _; rw [ctx_56, UInt64.add_assoc, ← UInt64.ofNat_add]
    have hctxOut : ∀ i < 16, ¬((entrySpOf core₀ - 8).toNat ≤ (ctx - 64 + UInt64.ofNat i).toNat ∧
        (ctx - 64 + UInt64.ofNat i).toNat < (entrySpOf core₀).toNat) := fun i hi ⟨h₁, h₂⟩ =>
      (base.ctxCells i hi).2.2.2.2 (hInS _ h₁ h₂)
    have hlimOk : (callCore C blk pre.length).memory.read64? ((callCore C blk pre.length).readReg .r15 - 56) =
        .ok (limitOf core₀ ctx) := by
      rw [hr15, Memory.read64?, read?_ok fun j hj => by
        rw [hctx8 j hj, h1mem, Memory.write64_readable, hC.readable]; exact (base.ctxCells (8 + j) (by omega)).1]
      refine congrArg Except.ok ?_
      rw [← hC.limit]
      exact read64_congr fun j hj => by rw [hctx8 j hj]; exact hb1 _ (hctxOut (8 + j) (by omega))
    have hdata : ReadableData (addRange holes (C.readReg .rsp - 8) 8)
        ((callCore C blk pre.length).readReg .r15 - 56) 8 := by
      rw [hr15]
      intro j hj hx
      rw [hctx8 j hj] at hx
      exact hctxOut (8 + j) (by omega) (hh₁ _ hx)
    have hchk := check_steps (returns := [callFrame C blk pre.length]) hbc
      (by simp only [maxFrame, slack] at hgbd ⊢; omega) h2 hn hlimOk hdata
    rw [h1rsp] at hchk
    by_cases hX : (entrySpOf core₀ - 8 - UInt64.ofNat (ml.size + slack)).toNat < (limitOf core₀ ctx).toNat
    · -- The check fails: the exit group, status 2
      left
      rw [if_pos hX] at hchk
      have hef := entryFrame_of base hC
        (m := inFrame ((callCore C blk pre.length).setReg .r11 (entrySpOf core₀ - 8 - UInt64.ofNat (ml.size + slack)))
          1 0 [callFrame C blk pre.length]) (holes := addRange holes (C.readReg .rsp - 8) 8)
        (by show (C.memory.write64 _ _).readable = _; simp) (fun x hx => hb1 x hx) hh₁
        (by show ((callCore C blk pre.length).setReg .r11 _).readReg .r15 = ctx
            rw [Validate.readReg_setReg, if_neg (by decide), hr15])
        (.inr ⟨_, rfl, by simp [callFrame, hC.rsp]⟩)
      obtain ⟨n, after, -, hsafe, hexitE⟩ := Wrapper.fail_safe hexit Runtime.rejecting (k := 2) (by decide)
        (by decide) hef rfl rfl
      refine ⟨1 + 2 + n, _, after, (hcall.append hchk).append hsafe, hexitE, ?_⟩
      rw [hexitE.rsp]
      have := hef.savesData 6 (by decide)
      have e : entrySpOf core₀ + UInt64.ofNat (8 + 8 * 6) = core₀.readReg .rsp := by simp [entrySpOf]
      rwa [e] at this
    · -- The check passes: the prologue
      right
      rw [if_neg hX] at hchk
      have hXn : (entrySpOf core₀ - 8 - UInt64.ofNat (ml.size + slack)).toNat =
          (entrySpOf core₀).toNat - 8 - (ml.size + slack) := by
        rw [sub_ofNat_toNat (by rw [hR8]; simp only [maxFrame, slack] at hlo hgbd ⊢; omega), hR8]
      obtain ⟨holes', m', fr₀', hpro, hfr', hmatch⟩ := entry_prologue base hlenA hs₀ hC (blk := blk) (off := pre.length)
        hfm hres (core' := (callCore C blk pre.length).setReg .r11 (entrySpOf core₀ - 8 - UInt64.ofNat (ml.size + slack)))
        (holes₁ := addRange holes (C.readReg .rsp - 8) 8)
        (by rw [Validate.readReg_setReg, if_neg (by decide), h1rsp])
        (fun r h1 h2 => by rw [Validate.readReg_setReg, if_neg h2, h1regs r h1])
        (fun _ => r11_allowed hfm hc) (by show (callCore _ _ _).memory = _; exact h1mem) hh₁
        (by rw [hRc]; rw [hXn] at hX; omega) (fun _ => by rw [hRc]; rw [hXn] at hX; omega)
      rw [hsh] at hpro
      exact ⟨1 + 2 + (prologue ml).length, holes', m', fr₀', _, (hcall.append hchk).append hpro, hfr', hmatch, hwc⟩
  · -- No stack check: the prologue
    right
    have hsh : (ctxOf S.placed mpl).labelBase + 0 = mpl.start := by
      simp [ctxOf, shiftOf, hfm.play, hfm.pfacts, hc]
    obtain ⟨hsl, hnc⟩ := unchecked_slack gs hc
    obtain ⟨holes', m', fr₀', hpro, hfr', hmatch⟩ := entry_prologue base hlenA hs₀ hC (blk := blk) (off := pre.length)
      hfm hres (core' := callCore C blk pre.length) (holes₁ := addRange holes (C.readReg .rsp - 8) 8) h1rsp
      (fun r h1 _ => h1regs r h1) (fun h => absurd (h1regs .r11 (by decide)) h) h1mem hh₁
      (by rw [hRc, hL, hE]; simp only [slack] at hsl hbud ⊢; omega) (fun h => by rw [hnc] at h; cases h)
    rw [hsh] at hpro
    exact ⟨1 + (prologue ml).length, holes', m', fr₀', _, hcall.append hpro, hfr', hmatch, hwc⟩

end Compilatrix.Xv.Stacking.Proof
