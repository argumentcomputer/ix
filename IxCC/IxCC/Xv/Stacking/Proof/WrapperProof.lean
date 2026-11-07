import IxCC.Xv.Stacking.Proof.WrapperSteps

/-!
# The export wrapper's entry (05 §6.1, 04 §6)

`EntryBase` is what the export's caller provides (04 §6): `rdi` points 64
bytes below the context, `rsp` is SysV-aligned with the return address on
top, the context's `stackBudget` leaves room for a frame without a stack
check and the stack below `rsp` reaches no lower than `maxFrame + slack`,
the stack and the context cells are the machine's to read and write and
not Xl's, and Xl's memory lies inside the machine's. `EntryInv` adds that
Xl's arguments are the wrapper's: each SysV argument tagged as its export
passes it (`wrapperArgs`), every `Nat` below 2^63 (`ArgsFit`).

`entry_match`: after the wrapper's head, its call to `main` and `main`'s
prologue, the invariant holds for `main`'s first state, with the wrapper's
frame (`entryWrap`) as the stack every activation lives on.
-/

namespace IxCC.Xv.Stacking.Proof

open IxCC.X86 IxCC.X86.Stream

/-- The context's `stackBudget` word. -/
def budgetOf (core₀ : Core) (ctx : Word) : Word := core₀.memory.read64 (ctx - 48)

/-- `entrySp`: the wrapper's `rsp` at its call, below the six saved
registers and the alignment word. -/
def entrySpOf (core₀ : Core) : Word := core₀.readReg .rsp - 56

/-- `stackLimit`, as the wrapper computes it. -/
def limitOf (core₀ : Core) (ctx : Word) : Word := entrySpOf core₀ - budgetOf core₀ ctx

/-- The stack the wrapper gives the program, from the limit to the caller's
return address. -/
def InEntryStack (core₀ : Core) (ctx : Word) (x : Word) : Prop :=
  (core₀.readReg .rsp).toNat - 56 - (budgetOf core₀ ctx).toNat ≤ x.toNat ∧ x.toNat < (core₀.readReg .rsp).toNat + 8

/-- What the caller of an export provides (04 §6), for Xl memory `mem` and
context `ctx`. -/
structure EntryBase (core₀ : Core) (retAddr : Word) (mem : Memory) (ctx : Word) : Prop where
  rdi : core₀.readReg .rdi = ctx - 64
  align : (core₀.readReg .rsp).toNat % 16 = 8
  slot : core₀.memory.read64? (core₀.readReg .rsp) = .ok retAddr
  top : (core₀.readReg .rsp).toNat + 8 ≤ 2 ^ 64
  /-- The budget leaves room for a frame without a stack check. -/
  budget : slack ≤ (budgetOf core₀ ctx).toNat
  /-- The limit leaves room below it for any frame. -/
  low : maxFrame + slack + (budgetOf core₀ ctx).toNat + 56 ≤ (core₀.readReg .rsp).toNat
  stack : ∀ x, InEntryStack core₀ ctx x → core₀.memory.readable x = true ∧ core₀.memory.writable x = true ∧
    mem.readable x = false ∧ mem.writable x = false
  /-- `entrySp` and `stackLimit`. -/
  ctxCells : ∀ i < 16, core₀.memory.readable (ctx - 64 + UInt64.ofNat i) = true ∧
    core₀.memory.writable (ctx - 64 + UInt64.ofNat i) = true ∧ mem.readable (ctx - 64 + UInt64.ofNat i) = false ∧
    mem.writable (ctx - 64 + UInt64.ofNat i) = false ∧ ¬InEntryStack core₀ ctx (ctx - 64 + UInt64.ofNat i)
  /-- `stackBudget`. -/
  budgetCell : ∀ i < 8, core₀.memory.readable (ctx - 48 + UInt64.ofNat i) = true ∧
    ¬InEntryStack core₀ ctx (ctx - 48 + UInt64.ofNat i)
  inside : Inside mem core₀.memory

/-- An argument as the wrapper passes it to `main`: each SysV argument
register after `rdi`, tagged as its export passes it. -/
def wrapperArgs (reps : List ArgRep) (core₀ : Core) : List Word :=
  (sysvArgs.zip reps).map fun (r, rep) => tagged rep (core₀.readReg r)

/-- Every `Nat` argument is below 2^63. -/
def ArgsFit (reps : List ArgRep) (core₀ : Core) : Prop :=
  ∀ r rep, (r, rep) ∈ sysvArgs.zip reps → rep = .nat → (core₀.readReg r).toNat < 2 ^ 63

/-- How `main`'s export passes its arguments. -/
def mainReps (p : LProgram) (reps : Lir.FunId → Option (List ArgRep)) : List ArgRep :=
  match p.funcs[p.main]? with
  | some f => exportReps reps p.main f
  | none => []

/-- **The entry invariant**: the caller's contract (`EntryBase`), with
Xl's arguments the wrapper's and every `Nat` argument below 2^63. -/
structure EntryInv (p : LProgram) (reps : Lir.FunId → Option (List ArgRep)) (core₀ : Core) (retAddr : Word)
    (args : List Word) (mem : Memory) (ctx : Word) : Prop extends EntryBase core₀ retAddr mem ctx where
  args : args = wrapperArgs (mainReps p reps) core₀
  fit : ArgsFit (mainReps p reps) core₀

/-- The wrapper's frame and stack, for its call from core `C` at `blk`,
`off`. -/
def entryWrap (core₀ : Core) (retAddr ctx : Word) (C : Core) (blk : BlockId) (off : Nat) : Wrap :=
  ⟨ctx, entrySpOf core₀, core₀, retAddr, limitOf core₀ ctx, callFrame C blk off, C.readReg⟩

theorem EntryBase.entrySp_toNat {core₀ : Core} {retAddr : Word} {mem : Memory} {ctx : Word}
    (base : EntryBase core₀ retAddr mem ctx) : (entrySpOf core₀).toNat = (core₀.readReg .rsp).toNat - 56 :=
  sub_ofNat_toNat (n := 56) (by have := base.low; omega)

theorem EntryBase.limit_toNat {core₀ : Core} {retAddr : Word} {mem : Memory} {ctx : Word}
    (base : EntryBase core₀ retAddr mem ctx) :
    (limitOf core₀ ctx).toNat = (core₀.readReg .rsp).toNat - 56 - (budgetOf core₀ ctx).toNat := by
  rw [limitOf, UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, base.entrySp_toNat]; have := base.low; omega),
    base.entrySp_toNat]

theorem EntryBase.inStack {core₀ : Core} {retAddr : Word} {mem : Memory} {ctx : Word}
    (base : EntryBase core₀ retAddr mem ctx) {C : Core} {blk : BlockId} {off : Nat} {x : Word} :
    (entryWrap core₀ retAddr ctx C blk off).InStack x ↔ InEntryStack core₀ ctx x := by
  simp only [Wrap.InStack, entryWrap, InEntryStack, base.limit_toNat, base.entrySp_toNat]
  have := base.low
  omega

/-- After the wrapper's head, its call to `main` from core `C` (with `rsp =
entrySp`) and `main`'s stack check and prologue (the core, memory and holes
they leave, as hypotheses), the invariant holds for `main`'s first state. -/
theorem entry_match {S : Stk} {core₀ : Core} {retAddr ctx : Word} {mem : Memory}
    (base : EntryBase core₀ retAddr mem ctx) {args : List Word} (hlenA : args.length ≤ Xl.nArgRegs)
    {s₀ : Xl.State} (hs₀ : Xl.State.initial S.p args mem ctx = some s₀)
    {C : Core} {blk : BlockId} {off : Nat}
    (hC_rsp : C.readReg .rsp = entrySpOf core₀) (hC_r15 : C.readReg .r15 = ctx)
    (hC_args : RegsRel (Xl.entryRegs args) C)
    (hC_r : C.memory.readable = core₀.memory.readable) (hC_w : C.memory.writable = core₀.memory.writable)
    (hC_bytes : ∀ x, ¬InEntryStack core₀ ctx x → (∀ i < 16, x ≠ ctx - 64 + UInt64.ofNat i) →
      C.memory.bytes x = core₀.memory.bytes x)
    (hC_cell : C.memory.read64? (ctx - 64) = .ok (entrySpOf core₀))
    (hC_limit : C.memory.read64 (ctx - 56) = limitOf core₀ ctx)
    (hC_saves : ∀ i < 7, C.memory.read64? (entrySpOf core₀ + UInt64.ofNat (8 + 8 * i)) = .ok (saveWord core₀ retAddr i))
    {mf : Func Loc} {ml : FrameLayout} {mpl : Placed} (hfm : FnAt S S.p.main mf ml mpl) (hres : mf.results = 1)
    {b0 : Block Loc} {codes0 : List (List Instr)} {post0 : List Instr} {t0 : X86.Terminator}
    (hpos0 : ∀ fr, s₀.stack = [fr] → XlPos S fr mf ml mpl b0 codes0 post0 t0)
    {core_f : Core} {holes_f : Holes}
    (hf_rsp : core_f.readReg .rsp = entrySpOf core₀ - 8 - UInt64.ofNat ml.size)
    (hf_regs : ∀ r, r ≠ .rsp → r ≠ .r11 → core_f.readReg r = C.readReg r)
    (hf_r11 : core_f.readReg .r11 ≠ C.readReg .r11 → GPR.r11 ∈ allowedChanges S.env S.p.main mf)
    (hf_r : core_f.memory.readable = C.memory.readable) (hf_w : core_f.memory.writable = C.memory.writable)
    (hf_bytes : ∀ x, ¬((entrySpOf core₀ - 8 - UInt64.ofNat ml.size).toNat ≤ x.toNat ∧
      x.toNat < (entrySpOf core₀).toNat) → core_f.memory.bytes x = C.memory.bytes x)
    (hf_ret : core_f.memory.read64 (entrySpOf core₀ - 8) = (callFrame C blk off).continuation.encode)
    (hf_saves : ∀ r o, (r, o) ∈ ml.saveOff →
      core_f.memory.read64 (entrySpOf core₀ - 8 - UInt64.ofNat ml.size + UInt64.ofNat o) = C.readReg r)
    (hh : ∀ x, holes_f x → (entrySpOf core₀ - 8).toNat ≤ x.toNat ∧ x.toNat < (entrySpOf core₀).toNat)
    (hsd : ∀ r o, (r, o) ∈ ml.saveOff →
      ReadableData holes_f (entrySpOf core₀ - 8 - UInt64.ofNat ml.size + UInt64.ofNat o) 8)
    (hlow : (limitOf core₀ ctx).toNat ≤ (entrySpOf core₀ - 8 - UInt64.ofNat ml.size).toNat)
    (hroom : mf.facts.calls = true → (limitOf core₀ ctx).toNat + slack ≤
      (entrySpOf core₀ - 8 - UInt64.ofNat ml.size).toNat) :
    ∃ fr₀, s₀.stack = [fr₀] ∧
      Match S (entryWrap core₀ retAddr ctx C blk off) s₀
        (inFrame core_f (UInt32.ofNat ((ctxOf S.placed mpl).labelBase + 0)) (offsetOf ml 0 0 codes0)
          [callFrame C blk off])
        holes_f fr₀ (calleeAct S S.p.main mf ml (entrySpOf core₀) C) (callFrame C blk off) [] := by
  -- `main`'s first state
  simp only [Xl.State.initial, Option.bind_eq_bind, Option.bind_eq_some_iff, Xl.enter] at hs₀
  obtain ⟨⟨fr₀, regs₀⟩, ⟨mf', hmf', u, hguard, he⟩, hs₀⟩ := hs₀
  have e : mf' = mf := Option.some.inj (hmf'.symm.trans hfm.func)
  subst e
  have hplen : mf'.params.length = args.length := by
    by_cases hl : mf'.params.length = args.length
    · exact hl
    · simp [guard, hl] at hguard
  simp only [Option.some.injEq, Prod.mk.injEq] at he hs₀
  obtain ⟨rfl, rfl⟩ := he
  subst hs₀
  refine ⟨_, rfl, ?_⟩
  have hpos := hpos0 _ rfl
  -- Numbers
  have gs := hfm.checks.1
  have hgbd := gs.bounded
  have hlo := base.low
  have hbud := base.budget
  have htop := base.top
  have hal := base.align
  have hE := base.entrySp_toNat
  have hL := base.limit_toNat
  have hkin : mf'.facts.inArgs = 0 := by rw [facts_inArgs, hplen]; omega
  have hdrop : args.drop Xl.nArgRegs = [] := List.drop_eq_nil_of_le hlenA
  have hR8 : (entrySpOf core₀ - 8).toNat = (entrySpOf core₀).toNat - 8 := sub8_toNat (by
    simp only [maxFrame, slack] at hlo; omega)
  have hRc : (entrySpOf core₀ - 8 - UInt64.ofNat ml.size).toNat = (entrySpOf core₀).toNat - 8 - ml.size := by
    rw [sub_ofNat_toNat (by rw [hR8]; simp only [maxFrame, slack] at hlo hgbd; omega), hR8]
  have hstk : ∀ x, (entryWrap core₀ retAddr ctx C blk off).InStack x ↔ InEntryStack core₀ ctx x := fun x => base.inStack
  have hWtop : (entryWrap core₀ retAddr ctx C blk off).entrySp.toNat + 64 ≤ 2 ^ 64 := by simp only [entryWrap]; omega
  -- The frame on the stack
  have gspan : FrameSpan (entryWrap core₀ retAddr ctx C blk off) (entrySpOf core₀ - 8 - UInt64.ofNat ml.size) ml mf'.facts.inArgs :=
    ⟨hlow, by simp only [entryWrap]; rw [hRc, hkin]; simp only [maxFrame, slack] at hlo hgbd; omega,
      by rw [hkin]; omega, hWtop⟩
  have hInFrame : ∀ x, (entrySpOf core₀ - 8 - UInt64.ofNat ml.size).toNat ≤ x.toNat →
      x.toNat < (entrySpOf core₀).toNat → InEntryStack core₀ ctx x := fun x h₁ h₂ => by
    simp only [InEntryStack]; rw [hRc] at h₁; rw [hE] at h₂; rw [hL] at hlow; rw [hRc] at hlow; omega
  -- Bytes outside the stack and the context cells are the caller's.
  have hbytes0 : ∀ x, ¬InEntryStack core₀ ctx x → (∀ i < 16, x ≠ ctx - 64 + UInt64.ofNat i) →
      core_f.memory.bytes x = core₀.memory.bytes x := fun x h₁ h₂ => by
    rw [hf_bytes x fun ⟨a, b⟩ => h₁ (hInFrame x a b), hC_bytes x h₁ h₂]
  -- Bytes at or above `entrySp`, and outside the frame, are `C`'s.
  have hkeepUp : ∀ x, (entrySpOf core₀).toNat ≤ x.toNat → core_f.memory.bytes x = C.memory.bytes x :=
    fun x hx => hf_bytes x fun ⟨_, h⟩ => by omega
  have hctxKeep : ∀ i < 16, core_f.memory.bytes (ctx - 64 + UInt64.ofNat i) = C.memory.bytes (ctx - 64 + UInt64.ofNat i) :=
    fun i hi => hf_bytes _ fun ⟨a, b⟩ => (base.ctxCells i hi).2.2.2.2 (hInFrame _ a b)
  have hreg15 : core_f.readReg .r15 = ctx := by rw [hf_regs _ (by decide) (by decide), hC_r15]
  have hrd : core_f.memory.readable = core₀.memory.readable := by rw [hf_r, hC_r]
  have hwr : core_f.memory.writable = core₀.memory.writable := by rw [hf_w, hC_w]
  have hholesStack : ∀ x, holes_f x → InEntryStack core₀ ctx x := fun x hx => by
    obtain ⟨h₁, h₂⟩ := hh x hx
    simp only [InEntryStack]; rw [hR8] at h₁; rw [hE] at h₂; rw [hL] at hlow; rw [hRc] at hlow; omega
  have hctx8 : ∀ j < 8, ctx - 56 + UInt64.ofNat j = ctx - 64 + UInt64.ofNat (8 + j) := by
    intro j _; rw [ctx_56, UInt64.add_assoc, ← UInt64.ofNat_add]
  have hsv : ∀ i < 7, ∀ j < 8, (entrySpOf core₀ + UInt64.ofNat (8 + 8 * i) + UInt64.ofNat j).toNat =
      (entrySpOf core₀).toNat + (8 + 8 * i) + j := fun i hi j hj => by
    rw [addr_toNat (by rw [addr_toNat (by omega)]; omega), addr_toNat (by omega)]
  -- The machine stack's facts
  have hentry : EntryFrame (entryWrap core₀ retAddr ctx C blk off).ctx (entryWrap core₀ retAddr ctx C blk off).entrySp (entryWrap core₀ retAddr ctx C blk off).core₀ (entryWrap core₀ retAddr ctx C blk off).retAddr
      (inFrame core_f (UInt32.ofNat ((ctxOf S.placed mpl).labelBase + 0)) (offsetOf ml 0 0 codes0)
        [callFrame C blk off]) holes_f := by
    refine ⟨?_, ?_, .inr ⟨[], callFrame C blk off, rfl, ?_, by simp⟩, fun i hi => ?_, fun i hi j hj hx => ?_, hreg15, ?_⟩
    · show core_f.memory.read64? (ctx - 64) = .ok (entrySpOf core₀)
      rw [read64?_keep (hf_r) fun j hj => by
        have := hctxKeep j (by omega); simpa using this]
      exact hC_cell
    · intro j hj hx
      exact (base.ctxCells j (by omega)).2.2.2.2 (hholesStack _ hx)
    · show C.readReg .rsp - 8 + 8 = entrySpOf core₀
      rw [hC_rsp]; simp
    · show core_f.memory.read64? (entrySpOf core₀ + UInt64.ofNat (8 + 8 * i)) = _
      rw [read64?_keep hf_r fun j hj => hkeepUp _ (by rw [hsv i hi j hj]; omega)]
      exact hC_saves i hi
    · obtain ⟨_, h₂⟩ := hh _ hx
      have := hsv i hi j hj
      change holes_f (entrySpOf core₀ + UInt64.ofNat (8 + 8 * i) + UInt64.ofNat j) at hx
      obtain ⟨_, h₂'⟩ := hh _ hx
      omega
    · show core₀.readReg .rsp = entrySpOf core₀ + 56
      simp [entrySpOf]
  have hglob : Global (entryWrap core₀ retAddr ctx C blk off) mem (inFrame core_f (UInt32.ofNat ((ctxOf S.placed mpl).labelBase + 0))
      (offsetOf ml 0 0 codes0) [callFrame C blk off]) holes_f := by
    refine ⟨fun x hx => ?_, fun i hi => ?_, fun i hi h => ?_, fun x hx => ?_, hentry, ?_, ?_, hWtop, ?_, ?_⟩
    · obtain ⟨a, b, c, d⟩ := base.stack x ((hstk x).1 hx)
      exact ⟨c, d, by show core_f.memory.readable x = true; rw [hrd]; exact a,
        by show core_f.memory.writable x = true; rw [hwr]; exact b⟩
    · obtain ⟨a, b, c, d, -⟩ := base.ctxCells i hi
      exact ⟨c, d, by show core_f.memory.readable _ = true; rw [hrd]; exact a,
        by show core_f.memory.writable _ = true; rw [hwr]; exact b⟩
    · exact (base.ctxCells i hi).2.2.2.2 ((hstk _).1 h)
    · obtain ⟨-, -, c, d⟩ := base.stack x (hholesStack x hx)
      exact ⟨c, d⟩
    · show core_f.memory.read64 (ctx - 56) = limitOf core₀ ctx
      rw [← hC_limit]
      exact read64_keep fun j hj => by rw [hctx8 j hj]; exact hctxKeep (8 + j) (by omega)
    · intro j hj hx
      change holes_f (ctx - 56 + UInt64.ofNat j) at hx
      rw [hctx8 j hj] at hx
      exact (base.ctxCells (8 + j) (by omega)).2.2.2.2 (hholesStack _ hx)
    · show maxFrame + slack ≤ (limitOf core₀ ctx).toNat
      rw [hL]; omega
    · show (limitOf core₀ ctx).toNat + slack ≤ (entrySpOf core₀).toNat
      rw [hL, hE]; omega
  refine ⟨rfl, rfl, rfl, rfl, ⟨mf', ml, mpl, ?_⟩, ?_, hglob⟩
  · -- `main`'s running activation
    refine ⟨hfm, ⟨b0, codes0, post0, t0, hpos, rfl⟩, ⟨entryRegs_size args, ?_, hreg15, ?_, ?_, ?_⟩, hf_rsp,
      ?_, ?_, ?_, hroom, ?_⟩
    · intro r hr v hv
      obtain ⟨i, hri, hvi⟩ := entryRegs_get hv
      have hrmem : r ∈ Lir.Conv.argRegs := List.mem_of_getElem? hri
      have hne1 : r ≠ .rsp := by intro e; subst e; simp [Lir.Conv.argRegs] at hrmem
      have hne2 : r ≠ .r11 := by intro e; subst e; simp [Lir.Conv.argRegs] at hrmem
      show core_f.readReg r = v
      rw [hf_regs r hne1 hne2]
      exact hC_args r hr v hv
    · show Inside mem core_f.memory
      have hin := base.inside
      refine ⟨fun x hx => by rw [hrd]; exact hin.readable x hx, fun x hx => by rw [hwr]; exact hin.writable x hx,
        fun x hx => ?_⟩
      have hns : ¬InEntryStack core₀ ctx x := fun h => by
        obtain ⟨-, -, c, d⟩ := base.stack x h
        rcases hx with hx | hx
        · rw [c] at hx; cases hx
        · rw [d] at hx; cases hx
      have hnc : ∀ i < 16, x ≠ ctx - 64 + UInt64.ofNat i := fun i hi e => by
        obtain ⟨-, -, c, d, -⟩ := base.ctxCells i hi
        rw [e] at hx
        rcases hx with hx | hx
        · rw [c] at hx; cases hx
        · rw [d] at hx; cases hx
      rw [hbytes0 x hns hnc]
      exact hin.bytes x hx
    · intro x hx v hv
      cases x with
      | reg r => simp [Loc.isCell] at hx
      | slot i => simp [Xl.read] at hv
      | outArg i => simp [Xl.read] at hv
      | inArg i =>
        have hv' : (args.drop Xl.nArgRegs)[i]? = some v := by simpa [Xl.read] using hv
        rw [hdrop] at hv'
        simp at hv'
    · exact frameCells_of hglob gs gspan hfm.play hfm.pfacts hf_rsp
    · intro r hr hsp
      right
      by_cases h11 : r = .r11
      · subst h11
        show core_f.readReg .r11 = C.readReg .r11
        by_cases hne : core_f.readReg .r11 = C.readReg .r11
        · exact hne
        · exact absurd (hf_r11 hne) hr
      · exact hf_regs r hsp h11
    · refine ⟨fun r o hro => hf_saves r o hro, fun r o hro => hsd r o hro, fun r hr => hr, ?_, ?_, rfl,
        ?_, hlow, gspan.high, gspan.inBound⟩
      · simp only [callFrame, calleeAct, hC_rsp]
        exact (UInt64.sub_add_cancel _ _).symm
      · simp only [callFrame, hC_rsp]
        exact hf_ret
      · simp only [calleeAct]; rw [hRc, hE]; simp only [maxFrame, slack] at hlo hgbd; omega
    · intro x hx v hv mm _
      cases x with
      | reg r => simp [Loc.isCell] at hx
      | slot i => simp [Xl.read] at hv
      | outArg i => simp [Xl.read] at hv
      | inArg i =>
        have hv' : (args.drop Xl.nArgRegs)[i]? = some v := by simpa [Xl.read] using hv
        rw [hdrop] at hv'
        simp at hv'
    · show ((args.drop Xl.nArgRegs).toArray).size = mf'.facts.inArgs
      rw [hkin, hdrop]; rfl
  · -- `main` returns to the wrapper.
    intro f l pl hf
    obtain ⟨e₁, e₂, -⟩ := hfm.unique hf
    subst e₁ e₂
    refine ⟨rfl, ?_, fun r _ => rfl, ⟨_, hfm.func, rfl⟩, hkin, hres⟩
    simp only [calleeAct, entryWrap]
    rw [hRc]; simp only [maxFrame, slack] at hlo hgbd; omega

end IxCC.Xv.Stacking.Proof
