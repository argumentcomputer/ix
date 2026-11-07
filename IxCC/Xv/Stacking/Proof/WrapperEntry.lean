import IxCC.Xv.Stacking.Proof.WrapperCall

/-!
# The export wrapper's entry

`wrapper_pre`: from the export's entry, the wrapper's head, its `Nat` check
and its marshalling reach its call to `main` with `main`'s arguments in the
internal convention's registers (`CallCore`), when every `Nat` argument is
below 2^63 (`ArgsFit`); otherwise the check jumps to the exit group and
the export exits with status 3 (natOverflow). `wrapper_entry`: under the
entry invariant, the machine reaches the invariant for `main`'s first
state, or `main`'s stack check fails and the export exits with status 2.
`wrapper_overflow`: a `Nat` argument of 2^63 or more exits with status 3.
-/

namespace IxCC.Xv.Stacking.Proof

open IxCC.X86 IxCC.X86.Stream

/-! ## The arguments -/

theorem argPairs_get {reps : List ArgRep} {i : Nat} {s d : GPR} {rep : ArgRep} :
    (argPairs reps)[i]? = some ((s, d), rep) ↔
      sysvArgs[i]? = some s ∧ Lir.Conv.argRegs[i]? = some d ∧ reps[i]? = some rep := by
  simp only [argPairs, List.getElem?_zip_eq_some, and_assoc]

theorem argPairs_get' {reps : List ArgRep} {i : Nat} {p : (GPR × GPR) × ArgRep} (h : (argPairs reps)[i]? = some p) :
    sysvArgs[i]? = some p.1.1 ∧ Lir.Conv.argRegs[i]? = some p.1.2 ∧ reps[i]? = some p.2 := by
  obtain ⟨⟨s, d⟩, rep⟩ := p
  exact argPairs_get.1 h

/-- An argument's SysV register is not an earlier argument's internal one. -/
theorem marshal_order : ∀ i < 5, ∀ j < 7, j < i → Lir.Conv.argRegs[j]? ≠ sysvArgs[i]? := by decide

theorem argRegs_nodup : Lir.Conv.argRegs.Nodup := by decide

/-- A `Nat` argument's register. -/
theorem natSrcs_mem {reps : List ArgRep} {r : GPR} : r ∈ natSrcs reps ↔ (r, ArgRep.nat) ∈ sysvArgs.zip reps := by
  simp only [natSrcs, List.mem_filterMap]
  constructor
  · rintro ⟨⟨⟨s, d⟩, rep⟩, hm, he⟩
    cases rep with
    | word => simp at he
    | nat =>
      simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq] at he
      subst he
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hm
      obtain ⟨h1, -, h3⟩ := argPairs_get.1 hi
      exact List.mem_iff_getElem?.2 ⟨i, List.getElem?_zip_eq_some.2 ⟨h1, h3⟩⟩
  · intro h
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 h
    obtain ⟨h1, h3⟩ := List.getElem?_zip_eq_some.1 hi
    have hi5 : i < 5 := (List.getElem?_eq_some_iff.1 h1).1
    obtain ⟨d, hd⟩ : ∃ d, Lir.Conv.argRegs[i]? = some d :=
      ⟨_, List.getElem?_eq_getElem (by simp [Lir.Conv.argRegs]; omega)⟩
    exact ⟨((r, d), .nat), List.mem_iff_getElem?.2 ⟨i, argPairs_get.2 ⟨h1, hd, h3⟩⟩, by simp⟩

theorem argsFit_iff {reps : List ArgRep} {core : Core} :
    ArgsFit reps core ↔ ∀ r ∈ natSrcs reps, (core.readReg r).toNat < 2 ^ 63 := by
  constructor
  · intro h r hr; exact h r .nat (natSrcs_mem.1 hr) rfl
  · intro h r rep hm hrep; subst hrep; exact h r (natSrcs_mem.2 hm)

theorem wrapperArgs_length (reps : List ArgRep) (core : Core) : (wrapperArgs reps core).length ≤ Xl.nArgRegs := by
  simp only [wrapperArgs, List.length_map, List.length_zip, sysvArgs, List.length_cons, List.length_nil]
  have : Xl.nArgRegs = 7 := rfl
  omega

theorem sysvArgs_ne {r : GPR} (h : r ∈ sysvArgs) : r ≠ .rsp ∧ r ≠ .r15 ∧ r ≠ .r11 := by
  simp only [sysvArgs, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;> decide

theorem argRegs_ne {r : GPR} (h : r ∈ Lir.Conv.argRegs) : r ≠ .rsp ∧ r ≠ .r15 := by
  simp only [Lir.Conv.argRegs, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- After the marshalling from a core whose SysV argument registers are the
entry's, `main`'s arguments are in the internal convention's registers. -/
theorem marshal_regs {reps : List ArgRep} {core₀ Cpre C : Core}
    (hpre : ∀ r ∈ sysvArgs, Cpre.readReg r = core₀.readReg r)
    (hval : ∀ (i : Nat) (p : (GPR × GPR) × ArgRep), (argPairs reps)[i]? = some p →
      (∀ (j : Nat) (q : (GPR × GPR) × ArgRep), j < i → (argPairs reps)[j]? = some q → q.1.2 ≠ p.1.1) →
      (∀ (j : Nat) (q : (GPR × GPR) × ArgRep), i < j → (argPairs reps)[j]? = some q → q.1.2 ≠ p.1.2) →
      C.readReg p.1.2 = tagged p.2 (Cpre.readReg p.1.1)) :
    RegsRel (Xl.entryRegs (wrapperArgs reps core₀)) C := by
  intro r _ v hv
  obtain ⟨i, hri, hvi⟩ := entryRegs_get hv
  simp only [wrapperArgs, List.getElem?_map, Option.map_eq_some_iff] at hvi
  obtain ⟨⟨s, rep⟩, hz, rfl⟩ := hvi
  obtain ⟨hs, hrep⟩ := List.getElem?_zip_eq_some.1 hz
  have hi5 : i < 5 := (List.getElem?_eq_some_iff.1 hs).1
  have hp : (argPairs reps)[i]? = some ((s, r), rep) := argPairs_get.2 ⟨hs, hri, hrep⟩
  have := hval i _ hp (fun j q hj hq e => by
      obtain ⟨-, hq2, -⟩ := argPairs_get' hq
      have hj7 : j < 7 := (List.getElem?_eq_some_iff.1 hq2).1
      exact marshal_order i hi5 j hj7 hj (by rw [hq2, hs, e]))
    (fun j q hj hq e => by
      obtain ⟨-, hq2, -⟩ := argPairs_get' hq
      rw [e] at hq2
      have := nodup_getElem?_inj argRegs_nodup hq2 hri
      omega)
  simp only at this
  rw [this, hpre s (List.mem_of_getElem? hs)]

theorem regsRel_entry_nil (C : Core) : RegsRel (Xl.entryRegs []) C := fun _ _ _ hv => by
  obtain ⟨i, -, h⟩ := entryRegs_get hv
  simp at h

theorem argPairs_dst {reps : List ArgRep} {r : GPR} (h : r ∈ (argPairs reps).map (·.1.2)) : r ∈ Lir.Conv.argRegs := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hp
  exact List.mem_of_getElem? (argPairs_get' hi).2.1

/-- A core with the same memory, stack pointer and context register is the
same `CallCore`, for any registers. -/
theorem CallCore.regs {core₀ : Core} {retAddr ctx : Word} {args args' : List Word} {C C' : Core}
    (h : CallCore core₀ retAddr ctx args C) (hm : C'.memory = C.memory) (hrsp : C'.readReg .rsp = C.readReg .rsp)
    (h15 : C'.readReg .r15 = C.readReg .r15) (hargs : RegsRel (Xl.entryRegs args') C') :
    CallCore core₀ retAddr ctx args' C' :=
  ⟨by rw [hrsp, h.rsp], by rw [h15, h.r15], hargs, by rw [hm, h.readable], by rw [hm, h.writable],
    fun x h₁ h₂ => by rw [hm, h.bytes x h₁ h₂], by rw [hm, h.cell], by rw [hm, h.limit],
    fun i hi => by rw [hm, h.saves i hi]⟩

/-- The marshalling, to the wrapper's call. -/
theorem marshal_call {cs : Checked} {blk : BlockId} {pre₀ marshal : List Instr} {entry : BlockId}
    {reps : List ArgRep} (code : BlockCode cs blk (pre₀ ++ marshal ++ [Instr.call entry] ++ wrapperTail) .ret)
    (hm : (argPairs reps).mapM marshalOne = .ok marshal) {core₀ : Core} {retAddr ctx : Word}
    {Cpre : Core} (hpre : CallCore core₀ retAddr ctx [] Cpre) (hsys : ∀ r ∈ sysvArgs, Cpre.readReg r = core₀.readReg r)
    {holes : Holes} (hempty : ∀ x, ¬holes x) :
    ∃ C holes', SafeSteps Runtime.rejecting cs marshal.length holes (inFrame Cpre blk pre₀.length []) holes'
        (inFrame C blk (pre₀ ++ marshal).length []) ∧ (∀ x, ¬holes' x) ∧
      CallCore core₀ retAddr ctx (wrapperArgs reps core₀) C := by
  have hfound := code.found
  have hseg : Straight.Segment cs blk pre₀.length marshal :=
    Straight.Segment.of_block hfound (pre := pre₀) (post := [Instr.call entry] ++ wrapperTail) (by simp)
  have hfits := code.fits
  simp only [List.length_append, List.length_singleton] at hfits
  obtain ⟨C, holes', hst, hempty', hmem, hkeep, hval⟩ := marshal_steps (o := pre₀.length) (core := Cpre)
    (holes := holes) (argPairs reps) marshal hm hseg (by omega) hempty
  refine ⟨C, holes', by simpa using hst, hempty', hpre.regs hmem
    (hkeep _ fun h => (argRegs_ne (argPairs_dst h)).1 rfl) (hkeep _ fun h => (argRegs_ne (argPairs_dst h)).2 rfl)
    (marshal_regs hsys hval)⟩

/-- From the export's entry: the wrapper's head, its `Nat` check and its
marshalling, to its call to `main`; or a `Nat` argument too large for a
tag, and the export's exit with status 3. -/
theorem wrapper_pre {S : Stk} {core₀ : Core} {retAddr ctx : Word} {mem : Memory}
    (base : EntryBase core₀ retAddr mem ctx) {mf : Func Loc} {ml : FrameLayout} {mpl : Placed}
    (hfm : FnAt S S.p.main mf ml mpl) :
    mf.results = 1 ∧
    ((¬ArgsFit (mainReps S.p S.reps) core₀ ∧ ∃ n holes after, SafeSteps Runtime.rejecting S.cs n (fun _ => False)
        (Machine.initial S.cs core₀) holes after ∧ Exit core₀ retAddr 3 0 after ∧
        ReadableData holes (after.core.readReg .rsp) 8) ∨
     (ArgsFit (mainReps S.p S.reps) core₀ ∧ ∃ blk pre n holes C,
        BlockCode S.cs blk (pre ++ [Instr.call (UInt32.ofNat mpl.start)] ++ wrapperTail) .ret ∧
        SafeSteps Runtime.rejecting S.cs n (fun _ => False) (Machine.initial S.cs core₀) holes
          (inFrame C blk pre.length []) ∧ (∀ x, ¬holes x) ∧
        CallCore core₀ retAddr ctx (wrapperArgs (mainReps S.p S.reps) core₀) C)) := by
  obtain ⟨f, sym, w, blks, hf, -, hwfn, hwreps, hentry, hwo, hat⟩ := main_at S.ok
  have e : f = mf := Option.some.inj (hf.symm.trans hfm.func)
  subst e
  obtain ⟨hres, -, entry, arity, hget, hwrap⟩ := wrapperOf_ok hwo
  have hentry' : entry = mpl.start := by
    have h1 := entry_of S S.p.main
    have h2 : entriesOf (runPlaced S.p S.layouts S.reps) = entriesOf S.placed := rfl
    rw [h2, hwfn] at hget
    rw [hget, hfm.placed] at h1
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    exact h1.1
  subst hentry'
  have hreps : mainReps S.p S.reps = w.reps := by simp [mainReps, hf, hwreps]
  rw [hreps]
  refine ⟨hres, ?_⟩
  obtain ⟨-, marshal, hm, hcases⟩ := wrapper_ok hwrap
  have hinit : Machine.initial S.cs core₀ = inFrame core₀ (UInt32.ofNat w.start) 0 [] := by
    have : S.cs.program.entry = UInt32.ofNat w.start := hentry
    simp [Machine.initial, inFrame, this]
  rw [hinit]
  have hexit : ExitGroupAt S.cs := fun j hj => exit_at S.ok hj
  -- The wrapper's first block
  have hblk0 : ∀ B, blks[0]? = some B → S.cs.program.blocks[(UInt32.ofNat w.start).toNat]? = some B ∧
      B.instructions.size < UInt32.size := by
    intro B hB
    have h0 := hat 0 (List.getElem?_eq_some_iff.1 hB).1
    rw [Nat.add_zero, hB] at h0
    obtain ⟨hk, hsz⟩ := block_fits (cs := S.cs) h0
    exact ⟨by rw [UInt32.toNat_ofNat_of_lt' hk]; exact h0, by simpa [UInt32.size] using hsz⟩
  rcases hcases with ⟨hnil, rfl⟩ | ⟨first, rest, hcons, rfl⟩
  · -- No `Nat` argument: one block
    obtain ⟨hfound, hfits⟩ := hblk0 _ rfl
    have code : BlockCode S.cs (UInt32.ofNat w.start) (wrapperHead ++ marshal ++ [Instr.call (UInt32.ofNat mpl.start)] ++
        wrapperTail) .ret := ⟨by rw [hfound]; simp, by simpa using hfits⟩
    have hseg : Straight.Segment S.cs (UInt32.ofNat w.start) 0 wrapperHead :=
      Straight.Segment.of_block code.found (pre := []) (post := marshal ++ [Instr.call (UInt32.ofNat mpl.start)] ++ wrapperTail)
        (by simp)
    obtain ⟨c12, h12, s12, he12, hrsp, h15, hregs, hr, hw, hb, hcell, hlim, hsaves⟩ := wrapper_head hseg base
    have hpre : CallCore core₀ retAddr ctx [] c12 :=
      ⟨hrsp, h15, regsRel_entry_nil _, hr, hw, hb, hcell, hlim, hsaves⟩
    have hsys : ∀ r ∈ sysvArgs, c12.readReg r = core₀.readReg r := fun r hr' => by
      obtain ⟨a, b, c⟩ := sysvArgs_ne hr'
      exact hregs r a b c
    obtain ⟨C, holes', hst, hempty', hC⟩ := marshal_call (pre₀ := wrapperHead) code hm hpre hsys he12
    right
    refine ⟨(argsFit_iff.2 fun r hr' => by rw [hnil] at hr'; cases hr'), _, wrapperHead ++ marshal, _, holes', C,
      by simpa using code, s12.append hst, hempty', hC⟩
  · -- The `Nat` check, then the call's block
    obtain ⟨hfound, hfits⟩ := hblk0 _ rfl
    have h1 := hat 1 (by simp)
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at h1
    obtain ⟨hk1, hsz1⟩ := block_fits (cs := S.cs) h1
    have hfound1 := h1
    rw [← UInt32.toNat_ofNat_of_lt' hk1] at hfound1
    have code1 : BlockCode S.cs (UInt32.ofNat (w.start + 1)) ([] ++ marshal ++ [Instr.call (UInt32.ofNat mpl.start)] ++
        wrapperTail) .ret := ⟨hfound1.trans (by simp), by simpa using hsz1⟩
    have hseg : Straight.Segment S.cs (UInt32.ofNat w.start) 0 wrapperHead :=
      Straight.Segment.of_block hfound (pre := []) (post := natCheck first rest) (by simp)
    obtain ⟨c12, h12, s12, he12, hrsp, h15, hregs, hr, hw, hb, hcell, hlim, hsaves⟩ := wrapper_head hseg base
    -- `mov r11, first; or r11, r; …`
    have hsegN : Straight.Segment S.cs (UInt32.ofNat w.start) wrapperHead.length (natCheck first rest) :=
      Straight.Segment.of_block hfound (pre := wrapperHead) (post := []) (by simp)
    have hlenH : wrapperHead.length = 12 := rfl
    rw [hlenH] at hsegN
    simp only [natCheck] at hsegN
    have hsegN' : Straight.Segment S.cs (UInt32.ofNat w.start) 12 ([Instr.mov .w64 .r11 (.reg first)] ++
        rest.map fun r => .op orMR [.reg .r11, .reg r]) := by simpa using hsegN
    have hfitsN : 12 + (natCheck first rest).length < UInt32.size := by
      simp only [List.size_toArray, List.length_append] at hfits; rw [hlenH] at hfits; omega
    simp only [natCheck, List.length_cons, List.length_map] at hfitsN
    obtain ⟨hm1, s13, he13⟩ := bare_step (core := c12) (core' := c12.setReg .r11 (c12.readReg first)) hsegN'.left
      (by omega) (fun _ => nofun) (fun _ => nofun) rfl he12 (by rw [executeInstr_mov]; rfl)
    have hsrc : ∀ r ∈ natSrcs w.reps, r ∈ sysvArgs := fun r hr' => List.of_mem_zip (natSrcs_mem.1 hr') |>.1
    have h11 : GPR.r11 ∉ rest := fun h => (sysvArgs_ne (hsrc _ (by rw [hcons]; exact List.mem_cons_of_mem _ h))).2.2 rfl
    obtain ⟨hmN, sN, heN⟩ := ors_steps rest (o := 12 + 1) (core := c12.setReg .r11 (c12.readReg first))
      (by simpa using hsegN'.right) (by omega) h11 he13
    obtain ⟨cN, hcN⟩ : ∃ c, c = (c12.setReg .r11 (c12.readReg first)).setReg .r11
        ((rest.map (c12.setReg .r11 (c12.readReg first)).readReg).foldl (· ||| ·)
          ((c12.setReg .r11 (c12.readReg first)).readReg .r11)) := ⟨_, rfl⟩
    rw [← hcN] at sN
    have hcNr : ∀ r, r ≠ .r11 → cN.readReg r = c12.readReg r := fun r hr' => by
      rw [hcN, Validate.readReg_setReg, if_neg hr', Validate.readReg_setReg, if_neg hr']
    have hcNm : cN.memory = c12.memory := by rw [hcN]; rfl
    have hval : cN.readReg .r11 = ((rest.map core₀.readReg).foldl (· ||| ·) (core₀.readReg first)) := by
      have hfirst : first ∈ sysvArgs := hsrc _ (by rw [hcons]; exact List.mem_cons_self)
      rw [hcN, Validate.readReg_setReg, if_pos rfl, Validate.readReg_setReg, if_pos rfl]
      obtain ⟨a, b, c⟩ := sysvArgs_ne hfirst
      rw [hregs first a b c]
      congr 1
      apply List.map_congr_left
      intro q hq
      have hqs : q ∈ sysvArgs := hsrc _ (by rw [hcons]; exact List.mem_cons_of_mem _ hq)
      obtain ⟨a', b', c'⟩ := sysvArgs_ne hqs
      rw [Validate.readReg_setReg, if_neg c', hregs q a' b' c']
    -- The branch
    have hbc : BlockCode S.cs (UInt32.ofNat w.start) (wrapperHead ++ natCheck first rest)
        (.branch testMR [.reg .r11, .reg .r11] .signedLt (UInt32.ofNat (0 + statusOf .natOverflow - 1))
          (UInt32.ofNat (w.start + 1))) := ⟨hfound, by simpa using hfits⟩
    have hlenN : (wrapperHead ++ natCheck first rest).length = 12 + 1 + rest.length := by
      simp [natCheck, hlenH]; omega
    have hbig := test_signedLt (cN.readReg .r11)
    have h3 : S.cs.program.hasBlock (UInt32.ofNat 2) = true := (hexit.fail (k := 3) (by decide) (by decide)).hasBlock
    have hn1 : S.cs.program.hasBlock (UInt32.ofNat (w.start + 1)) = true := code1.hasBlock
    have hbr := hbc.safe_branch Runtime.rejecting cN [] hmN
      ⟨fun _ _ i _ h => heN _ h, fun _ _ frame hf => by simp at hf⟩ (test_exec .r11 cN) hbig
      (by split <;> assumption)
    rw [hlenN] at hbr
    have hpreN : CallCore core₀ retAddr ctx [] cN :=
      CallCore.regs ⟨hrsp, h15, regsRel_entry_nil _, hr, hw, hb, hcell, hlim, hsaves⟩ hcNm
        (hcNr _ (by decide)) (hcNr _ (by decide)) (regsRel_entry_nil _)
    have hemptyB : ∀ x, ¬Stream.nextHoles hmN (.op testMR [.reg .r11, .reg .r11]) cN x :=
      fun x h => heN x (clearAccesses_sub _ _ x h)
    have hfitE : ArgsFit w.reps core₀ ↔ ¬(2 ^ 63 ≤ (cN.readReg .r11).toNat) := by
      rw [argsFit_iff, hval, foldl_or_big, hcons]
      constructor
      · intro h hb'
        rcases hb' with hb' | ⟨b, hb', hge⟩
        · have := h first List.mem_cons_self; omega
        · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hb'
          have := h q (List.mem_cons_of_mem _ hq); omega
      · intro h r hr'
        rcases List.mem_cons.1 hr' with rfl | hr'
        · exact Nat.lt_of_not_le fun h' => h (.inl h')
        · exact Nat.lt_of_not_le fun h' => h (.inr ⟨_, List.mem_map_of_mem hr', h'⟩)
    by_cases hB : 2 ^ 63 ≤ (cN.readReg .r11).toNat
    · -- A `Nat` argument too large: `fail₃`
      left
      simp only [hB, decide_true, ↓reduceIte] at hbr
      refine ⟨fun h => hfitE.1 h hB, ?_⟩
      have hef := entryFrame_of base hpreN (m := inFrame cN (UInt32.ofNat (0 + statusOf .natOverflow - 1)) 0 [])
        (holes := Stream.nextHoles hmN (.op testMR [.reg .r11, .reg .r11]) cN) rfl (fun _ _ => rfl)
        (fun x hx => absurd hx (hemptyB x)) (by show cN.readReg .r15 = ctx; rw [hcNr _ (by decide), h15]) (.inl rfl)
      obtain ⟨n, after, -, hsafe, hexitE⟩ := Wrapper.fail_safe hexit Runtime.rejecting (k := 3) (by decide)
        (by decide) hef rfl rfl
      refine ⟨12 + (1 + (rest.length + (1 + n))), _, after, s12.append (s13.append (sN.append (hbr.append hsafe))),
        hexitE, ?_⟩
      rw [hexitE.rsp]
      have := hef.savesData 6 (by decide)
      have e : entrySpOf core₀ + UInt64.ofNat (8 + 8 * 6) = core₀.readReg .rsp := by simp [entrySpOf]
      rwa [e] at this
    · -- The arguments fit: the call's block
      right
      simp only [hB, decide_false, Bool.false_eq_true, ↓reduceIte] at hbr
      have hsysN : ∀ r ∈ sysvArgs, cN.readReg r = core₀.readReg r := fun r hr' => by
        obtain ⟨a, b, c⟩ := sysvArgs_ne hr'
        rw [hcNr r c, hregs r a b c]
      obtain ⟨C, holes', hst, hempty', hC⟩ := marshal_call (pre₀ := []) code1 hm hpreN hsysN hemptyB
      refine ⟨hfitE.2 hB, _, marshal, _, holes', C, by simpa using code1,
        s12.append (s13.append (sN.append (hbr.append (by simpa using hst)))), hempty', hC⟩

/-- `main` has a layout and a placement. -/
theorem main_fnAt (S : Stk) : ∃ mf ml mpl, FnAt S S.p.main mf ml mpl := by
  obtain ⟨f, -, -, -, hf, -⟩ := main_at S.ok
  obtain ⟨l, pl, h⟩ := fnAt_of S hf
  exact ⟨f, l, pl, h⟩

/-- **The wrapper's entry**: under the entry invariant, the machine reaches
the invariant for `main`'s first state on the wrapper's frame, with the
wrapper's tail as `main`'s return continuation; or `main`'s stack check
fails and the export exits with status 2. -/
theorem wrapper_entry {S : Stk} {core₀ : Core} {retAddr ctx : Word} {args : List Word} {mem : Memory}
    (inv : EntryInv S.p S.reps core₀ retAddr args mem ctx) {s₀ : Xl.State}
    (hs₀ : Xl.State.initial S.p args mem ctx = some s₀) :
    (∃ n holes after, SafeSteps Runtime.rejecting S.cs n (fun _ => False) (Machine.initial S.cs core₀) holes after ∧
      Exit core₀ retAddr 2 0 after ∧ ReadableData holes (after.core.readReg .rsp) 8) ∨
    (∃ (W : Wrap) (n : Nat) (holes : Holes) (m : Machine) (fr : Xl.Frame) (a : Act) (ret : ReturnFrame), W.core₀ = core₀ ∧ W.retAddr = retAddr ∧ WrapCont S W ∧
      SafeSteps Runtime.rejecting S.cs n (fun _ => False) (Machine.initial S.cs core₀) holes m ∧
      Match S W s₀ m holes fr a ret []) := by
  obtain ⟨mf, ml, mpl, hfm⟩ := main_fnAt S
  obtain ⟨hres, hpre⟩ := wrapper_pre inv.toEntryBase hfm
  rcases hpre with ⟨hbig, -⟩ | ⟨-, blk, pre, n, holes, C, code, hst, hempty, hC⟩
  · exact absurd inv.fit hbig
  · rw [← inv.args] at hC
    have hlenA : args.length ≤ Xl.nArgRegs := by rw [inv.args]; exact wrapperArgs_length _ _
    rcases wrapper_call inv.toEntryBase hlenA hs₀ hC hfm hres code hempty with
      ⟨n', holes', after, hst', hexit, hdata⟩ | ⟨n', holes', m, fr₀, a, hst', -, hm, hwc⟩
    · exact .inl ⟨n + n', holes', after, hst.append hst', hexit, hdata⟩
    · exact .inr ⟨_, n + n', holes', m, fr₀, a, _, rfl, rfl, hwc, hst.append hst', hm⟩

/-- A `Nat` argument of 2^63 or more: the wrapper's check exits with status
3 (natOverflow). -/
theorem wrapper_overflow {S : Stk} {core₀ : Core} {retAddr ctx : Word} {mem : Memory}
    (base : EntryBase core₀ retAddr mem ctx) (hbig : ¬ArgsFit (mainReps S.p S.reps) core₀) :
    ∃ n holes after, SafeSteps Runtime.rejecting S.cs n (fun _ => False) (Machine.initial S.cs core₀) holes after ∧
      Exit core₀ retAddr 3 0 after ∧ ReadableData holes (after.core.readReg .rsp) 8 := by
  obtain ⟨mf, ml, mpl, hfm⟩ := main_fnAt S
  obtain ⟨-, hpre⟩ := wrapper_pre (ctx := ctx) base hfm
  rcases hpre with ⟨-, h⟩ | ⟨hfit, -⟩
  · exact h
  · exact absurd hfit hbig

end IxCC.Xv.Stacking.Proof
