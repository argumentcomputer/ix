import IxCC.Xv.Stacking.Proof.Body

/-!
# The machine at an Xl position

The machine sits at the stacked code of Xl's position (`machine_at`), the
code of each instruction is a segment of its block (`XlPos.segment`), and
the steps there are checked: a footprint of Xl-visible memory and of the
running frame's cells reads no hole and writes no live return slot
(`Foot.safe`). Clearing what a step writes only removes holes, and leaves
the written cells readable (`clearAccesses_sub`, `clearAccesses_clears`).
-/

namespace IxCC.Xv.Stacking.Proof

open IxCC.X86 IxCC.X86.Stream

/-! ## Holes -/

theorem clearAccesses_sub : ∀ (accs : List Access) (holes : Holes) (x : Word), clearAccesses holes accs x → holes x
  | [], _, _, h => h
  | acc :: accs, holes, x, h => (clearAccesses_sub accs _ x h).1

theorem clearAccesses_clears : ∀ {accs : List Access} {holes : Holes} {acc : Access}, acc ∈ accs →
    ReadableData (clearAccesses holes accs) acc.address acc.bytes
  | acc' :: accs, holes, acc, hm, i, hi, hx => by
      rcases List.mem_cons.1 hm with rfl | hm
      · exact (clearAccesses_sub accs _ _ hx).2 ⟨i, hi, rfl⟩
      · exact clearAccesses_clears hm i hi hx

/-! ## Blocks and positions -/

theorem block_fits {cs : Checked} {k : Nat} {blk : X86.Block} (h : cs.program.blocks[k]? = some blk) :
    k < 2 ^ 32 ∧ blk.instructions.size < 2 ^ 32 := by
  have hv := cs.valid
  simp only [Program.wellFormed, Bool.and_eq_true, decide_eq_true_eq, Array.all_eq_true] at hv
  obtain ⟨⟨⟨-, hsize⟩, -⟩, hall⟩ := hv
  obtain ⟨hk, rfl⟩ := Array.getElem?_eq_some_iff.1 h
  have := hall k hk
  simp only [Bool.and_eq_true, Block.offsetsFit, decide_eq_true_eq] at this
  exact ⟨by omega, this.1.1.1⟩

theorem flatten_split {α : Type} {codes : List (List α)} {i : Nat} {code : List α} (hc : codes[i]? = some code) :
    codes.flatten = (codes.take i).flatten ++ code ++ (codes.drop (i + 1)).flatten := by
  have hi : i < codes.length := (List.getElem?_eq_some_iff.1 hc).1
  have hd : codes.drop i = code :: codes.drop (i + 1) := by
    rw [List.drop_eq_getElem_cons hi]
    congr 1
    exact Option.some.inj ((List.getElem?_eq_getElem hi).symm.trans hc)
  have h := congrArg List.flatten (List.take_append_drop i codes).symm
  rw [List.flatten_append, hd, List.flatten_cons] at h
  rw [h, List.append_assoc]

/-- The machine at Xl's position. -/
theorem machine_at {m : Machine} (hr : m.status = .running) {S : Stk} {pl : Placed} {label offset : Nat}
    (hpc : m.pc = pcOf S pl label offset) :
    m = inFrame m.core (UInt32.ofNat ((ctxOf S.placed pl).labelBase + label)) offset m.returns := by
  obtain ⟨core, pc, returns, status⟩ := m
  simp only at hr hpc
  subst hr hpc
  rfl

/-- The code of instruction `i` of Xl's block. -/
theorem XlPos.segment {S : Stk} {fr : Xl.Frame} {f : Func Loc} {l : FrameLayout} {pl : Placed} {b : Block Loc}
    {codes : List (List Instr)} {post : List Instr} {t : X86.Terminator} (hp : XlPos S fr f l pl b codes post t)
    {i : Nat} {code : List Instr} (hc : codes[i]? = some code) :
    Straight.Segment S.cs (UInt32.ofNat ((ctxOf S.placed pl).labelBase + fr.label)) (offsetOf l fr.label i codes) code ∧
      offsetOf l fr.label i codes + code.length < 2 ^ 32 := by
  obtain ⟨hk, hsz⟩ := block_fits (cs := S.cs) hp.found
  have hfound : S.cs.program.blocks[(UInt32.ofNat ((ctxOf S.placed pl).labelBase + fr.label)).toNat]? =
      some { instructions := (preOf l fr.label ++ codes.flatten ++ post).toArray, terminator := t } := by
    rw [UInt32.toNat_ofNat_of_lt' hk]; exact hp.found
  have hlist : ({ instructions := (preOf l fr.label ++ codes.flatten ++ post).toArray, terminator := t } : X86.Block).instructions.toList =
      (preOf l fr.label ++ (codes.take i).flatten) ++ code ++ ((codes.drop (i + 1)).flatten ++ post) := by
    simp only [List.toList_toArray, flatten_split hc, List.append_assoc]
  refine ⟨?_, ?_⟩
  · have := Straight.Segment.of_block hfound hlist
    simpa [offsetOf] using this
  · simp only [List.size_toArray, flatten_split hc, List.length_append] at hsz
    simp only [offsetOf]
    omega

/-- The terminator's code after Xl's block body. -/
theorem XlPos.blockCode {S : Stk} {fr : Xl.Frame} {f : Func Loc} {l : FrameLayout} {pl : Placed} {b : Block Loc}
    {codes : List (List Instr)} {post : List Instr} {t : X86.Terminator} (hp : XlPos S fr f l pl b codes post t) :
    BlockCode S.cs (UInt32.ofNat ((ctxOf S.placed pl).labelBase + fr.label)) (preOf l fr.label ++ codes.flatten ++ post) t ∧
      Straight.Segment S.cs (UInt32.ofNat ((ctxOf S.placed pl).labelBase + fr.label))
        (offsetOf l fr.label codes.length codes) post := by
  obtain ⟨hk, hsz⟩ := block_fits (cs := S.cs) hp.found
  have hfound : S.cs.program.blocks[(UInt32.ofNat ((ctxOf S.placed pl).labelBase + fr.label)).toNat]? =
      some { instructions := (preOf l fr.label ++ codes.flatten ++ post).toArray, terminator := t } := by
    rw [UInt32.toNat_ofNat_of_lt' hk]; exact hp.found
  refine ⟨⟨hfound, by simpa using hsz⟩, ?_⟩
  have hlist : ({ instructions := (preOf l fr.label ++ codes.flatten ++ post).toArray, terminator := t } : X86.Block).instructions.toList =
      (preOf l fr.label ++ codes.flatten) ++ post ++ [] := by simp
  have := Straight.Segment.of_block hfound hlist
  simpa [offsetOf, List.take_length] using this

/-! ## Live return slots -/

/-- The suspended activations' return slots lie on the stack, at or above
the first one's slots. -/
theorem Chain.slots {S : Stk} {W : Wrap} {mem : Memory} {holes : Holes} {B : Nat}
    (htop : W.entrySp.toNat + 64 ≤ 2 ^ 64) :
    ∀ {fr : Xl.Frame} {a : Act} {ret : ReturnFrame} {below : List (Xl.Frame × Act × ReturnFrame)},
      (∃ f l pl, FnAt S fr.fn f l pl) → Chain S W mem holes fr a ret below →
      (∀ fr₁ a₁ ret₁ rest, below = (fr₁, a₁, ret₁) :: rest → ∀ f₁ l₁ pl₁, FnAt S fr₁.fn f₁ l₁ pl₁ →
        B ≤ a₁.sp.toNat + 8 * l₁.outArgs) →
      ∀ x ∈ below, ∀ i < 8, W.InStack (x.2.2.returnSlot + UInt64.ofNat i) ∧
        B ≤ (x.2.2.returnSlot + UInt64.ofNat i).toNat
  | _, _, _, [], _, _, _, x, hx => by simp at hx
  | fr, a, ret, (fr₁, a₁, ret₁) :: rest, ⟨f, l, pl, hf⟩, ⟨hex, hlink, hrest⟩, hB, x, hx => by
    obtain ⟨f₁, l₁, pl₁, hf₁⟩ := hex
    have hB₁ := hB fr₁ a₁ ret₁ rest rfl f₁ l₁ pl₁ hf₁
    obtain ⟨-, hA, -⟩ := hlink f l pl hf f₁ l₁ pl₁ hf₁
    have hs := hf₁.checks.1
    have span := hA.span htop
    have hfit := hs.outArgsFit
    rcases List.mem_cons.1 hx with rfl | hx
    · intro i hi
      rw [hA.slot]
      have e : a₁.sp + UInt64.ofNat l₁.size + UInt64.ofNat i = a₁.sp + UInt64.ofNat (l₁.size + i) := by
        rw [UInt64.add_assoc, ← UInt64.ofNat_add]
      rw [e]
      obtain ⟨hto, hin⟩ := span.byte (o := l₁.size + i) (by omega)
      exact ⟨hin, by rw [hto]; omega⟩
    · refine Chain.slots htop ⟨f₁, l₁, pl₁, hf₁⟩ hrest (fun fr₂ a₂ ret₂ rest' e f₂ l₂ pl₂ hf₂ => ?_) x hx
      subst e
      obtain ⟨-, hlink₂, -⟩ := hrest
      obtain ⟨hL₂, -, -⟩ := hlink₂ f₁ l₁ pl₁ hf₁ f₂ l₂ pl₂ hf₂
      have := hL₂.sp
      omega

/-- Every live return slot: the running activation's, just above its frame,
or a suspended one's, above the running frame. -/
theorem Match.slot {S : Stk} {W : Wrap} {s : Xl.State} {m : Machine} {holes : Holes} {fr : Xl.Frame} {a : Act}
    {ret : ReturnFrame} {below : List (Xl.Frame × Act × ReturnFrame)} (hm : Match S W s m holes fr a ret below)
    {f : Func Loc} {l : FrameLayout} {pl : Placed} (htop : Top S W s m holes fr a ret f l pl)
    {frm : ReturnFrame} (hfrm : frm ∈ m.returns) {i : Nat} (hi : i < 8) :
    W.InStack (frm.returnSlot + UInt64.ofNat i) ∧
      ((frm.returnSlot + UInt64.ofNat i).toNat = a.sp.toNat + l.size + i ∨
        a.sp.toNat + l.size + 8 + 8 * f.facts.inArgs ≤ (frm.returnSlot + UInt64.ofNat i).toNat) := by
  have hg := hm.global
  have span := htop.act.span hg.top
  rw [hm.returns] at hfrm
  rcases List.mem_cons.1 hfrm with rfl | hfrm
  · rw [htop.act.slot]
    have e : a.sp + UInt64.ofNat l.size + UInt64.ofNat i = a.sp + UInt64.ofNat (l.size + i) := by
      rw [UInt64.add_assoc, ← UInt64.ofNat_add]
    rw [e]
    obtain ⟨hto, hin⟩ := span.byte (o := l.size + i) (by omega)
    exact ⟨hin, .inl (by rw [hto]; omega)⟩
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hfrm
    have := Chain.slots (B := a.sp.toNat + l.size + 8 + 8 * f.facts.inArgs) hg.top ⟨f, l, pl, htop.fn⟩ hm.chain
      (fun fr₁ a₁ ret₁ rest e f₁ l₁ pl₁ hf₁ => by
        have hc := hm.chain
        rw [e] at hc
        obtain ⟨-, hlink, -⟩ := hc
        exact (hlink f l pl htop.fn f₁ l₁ pl₁ hf₁).1.room) x hx i hi
    exact ⟨this.1, .inr this.2⟩

/-- A row footprint of Xl-visible memory and of the running frame's cells
(the read ones defined) is a checked step's. -/
theorem Foot.safe {S : Stk} {W : Wrap} {s : Xl.State} {m : Machine} {holes : Holes} {fr : Xl.Frame} {a : Act}
    {ret : ReturnFrame} {below : List (Xl.Frame × Act × ReturnFrame)} (hm : Match S W s m holes fr a ret below)
    {f : Func Loc} {l : FrameLayout} {pl : Placed} (htop : Top S W s m holes fr a ret f l pl) {o : Op}
    {xs : List Arg} {U D : List Loc} {core : Core} (hcore : core.readReg .rsp = m.core.readReg .rsp)
    (hf : Foot (ctxOf S.placed pl) o xs s.mem core U D)
    (hU : ∀ u ∈ U, u.isCell = true → ∃ v, Xl.read s.regs fr u = some v) :
    OperationSafe holes m.returns (.op o xs) core := by
  have hg := hm.global
  have hs := htop.fn.checks.1
  have span := htop.act.span hg.top
  refine ⟨fun acc hacc => ?_, fun acc hacc => ?_⟩
  · rcases hf.reads acc hacc with hX | ⟨hb, u, huU, hu, mm, hmm, ha⟩
    · intro i hi hh
      have := (hg.holesFree _ hh).1
      rw [hX i hi] at this
      cases this
    · obtain ⟨v, hv⟩ := hU u huU hu
      have hd := htop.cellsData u hu v hv mm hmm
      rw [cell_rsp hmm hcore] at ha
      rw [ha]
      exact fun i hi => hd i (by omega)
  · intro frm hfrm i hi j hj e
    obtain ⟨hin, hpos⟩ := hm.slot htop hfrm hi
    rcases hf.writes acc hacc with hX | ⟨hb, u, hu, mm, hmm, ha⟩
    · have := (hg.stack _ hin).2.1
      rw [e, hX j hj] at this
      cases this
    · obtain ⟨o', hc, -, hr, hbytes⟩ := span.cell hs htop.fn.play htop.fn.pfacts hmm (hcore.trans htop.rsp)
      rw [ha] at e
      have hj8 : j < 8 := by omega
      have hto := (hbytes j hj8).1
      obtain ⟨-, -, hside⟩ := hc.range hs
      have := congrArg UInt64.toNat e
      rw [hto] at this
      omega

end IxCC.Xv.Stacking.Proof
