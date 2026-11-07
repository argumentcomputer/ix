import IxCC.Xv.Stacking.Proof.CallFacts

/-!
# A call keeps the invariant

After an Xl call, the machine has called the callee's first block, passed
its stack check and run its prologue (`call_steps`), or failed the check and
left through the exit group with status 2. In the first case the invariant
holds for the callee at its first instruction, with the caller suspended
and linked to it (`call_match`).
-/

namespace IxCC.Xv.Stacking.Proof

open IxCC.X86 IxCC.X86.Stream

/-! ## Changes below a frame -/

/-- An activation's facts survive changes below its slots. -/
theorem ActFacts.mono {S : Stk} {W : Wrap} {mem mem' : Memory} {holes holes' : Holes} {fr fr' : Xl.Frame}
    {a : Act} {ret : ReturnFrame} {f : Func Loc} {l : FrameLayout} {pl : Placed}
    (h : ActFacts S W mem holes fr a ret f l) (hf : FnAt S fr.fn f l pl) (hfn : fr'.fn = fr.fn)
    (htop : W.entrySp.toNat + 64 ≤ 2 ^ 64) {B : Nat} (hB : B ≤ a.sp.toNat + 8 * l.outArgs)
    (hbytes : ∀ x, B ≤ x.toNat → x.toNat < W.entrySp.toNat → mem'.bytes x = mem.bytes x)
    (hholes : ∀ x, holes' x → holes x ∨ x.toNat < B) : ActFacts S W mem' holes' fr' a ret f l := by
  have hs := hf.checks.1
  have span := h.span htop
  have hfit := hs.outArgsFit
  have hkeep : ∀ o, 8 * l.outArgs ≤ o → o + 8 ≤ l.size + 8 + 8 * f.facts.inArgs → ∀ i < 8,
      mem'.bytes (a.sp + UInt64.ofNat o + UInt64.ofNat i) = mem.bytes (a.sp + UInt64.ofNat o + UInt64.ofNat i) ∧
        B ≤ (a.sp + UInt64.ofNat o + UInt64.ofNat i).toNat := by
    intro o ho ho' i hi
    have e : a.sp + UInt64.ofNat o + UInt64.ofNat i = a.sp + UInt64.ofNat (o + i) := by
      rw [UInt64.add_assoc, ← UInt64.ofNat_add]
    have hb := (span.byte (o := o + i) (by omega)).1
    rw [e, hb]
    have := span.high
    exact ⟨hbytes _ (by rw [hb]; omega) (by rw [hb]; omega), by omega⟩
  refine ⟨fun r o hro => ?_, fun r o hro => ?_, by rw [hfn]; exact h.allowed, h.slot, ?_, h.snapshot, h.align,
    h.low, h.high, h.inBound⟩
  · have hsr := save_range hs hro
    rw [← h.saves r o hro]
    exact read64_keep fun i hi => (hkeep o hsr.2.1 (by omega) i hi).1
  · have hsr := save_range hs hro
    exact ReadableData.keep (h.savesData r o hro) (fun i hi => (hkeep o hsr.2.1 (by omega) i hi).2) hholes
  · rw [← h.retAddr, h.slot]
    exact read64_keep fun i hi => (hkeep l.size (by omega) (by omega) i hi).1

theorem entry_save_toNat {W : Wrap} (htop : W.entrySp.toNat + 64 ≤ 2 ^ 64) {i j : Nat} (hi : i < 7) (hj : j < 8) :
    (W.entrySp + UInt64.ofNat (8 + 8 * i) + UInt64.ofNat j).toNat = W.entrySp.toNat + (8 + 8 * i) + j := by
  rw [addr_toNat (by rw [addr_toNat (by omega)]; omega), addr_toNat (by omega)]

theorem ctx_56 (ctx : Word) : ctx - 56 = ctx - 64 + UInt64.ofNat 8 := by
  rw [UInt64.sub_eq_add_neg, UInt64.sub_eq_add_neg, UInt64.add_assoc]
  congr 1

/-- The machine stack's facts survive changes to stack bytes below the
wrapper's frame and holes added there. -/
theorem Global.mono {W : Wrap} {xm : Memory} {m m' : Machine} {holes holes' : Holes} (hg : Global W xm m holes)
    (hr : m'.core.memory.readable = m.core.memory.readable) (hw : m'.core.memory.writable = m.core.memory.writable)
    (hbytes : ∀ x, (¬W.InStack x ∨ W.entrySp.toNat ≤ x.toNat) → m'.core.memory.bytes x = m.core.memory.bytes x)
    (hholes : ∀ x, holes' x → holes x ∨ (W.InStack x ∧ x.toNat < W.entrySp.toNat))
    (h15 : m'.core.readReg .r15 = W.ctx)
    (houter : m'.returns = [] ∨ ∃ inner f₁, m'.returns = inner ++ [f₁] ∧ f₁.returnSlot + 8 = W.entrySp ∧
      ∀ g ∈ inner, g.returnSlot + 8 ≠ W.entrySp) :
    Global W xm m' holes' := by
  have hctxB : ∀ i < 16, m'.core.memory.bytes (W.ctx - 64 + UInt64.ofNat i) =
      m.core.memory.bytes (W.ctx - 64 + UInt64.ofNat i) := fun i hi => hbytes _ (.inl (hg.apart i hi))
  have hctxH : ∀ i < 16, holes' (W.ctx - 64 + UInt64.ofNat i) → holes (W.ctx - 64 + UInt64.ofNat i) := by
    intro i hi hh
    rcases hholes _ hh with h | ⟨hin, -⟩
    · exact h
    · exact absurd hin (hg.apart i hi)
  have he := hg.entry
  have hsaveB : ∀ i < 7, ∀ j < 8, m'.core.memory.bytes (W.entrySp + UInt64.ofNat (8 + 8 * i) + UInt64.ofNat j) =
      m.core.memory.bytes (W.entrySp + UInt64.ofNat (8 + 8 * i) + UInt64.ofNat j) := fun i hi j hj =>
    hbytes _ (.inr (by rw [entry_save_toNat hg.top hi hj]; omega))
  have hsaveH : ∀ i < 7, ∀ j < 8, holes' (W.entrySp + UInt64.ofNat (8 + 8 * i) + UInt64.ofNat j) →
      holes (W.entrySp + UInt64.ofNat (8 + 8 * i) + UInt64.ofNat j) := by
    intro i hi j hj hh
    rcases hholes _ hh with h | ⟨-, hlt⟩
    · exact h
    · rw [entry_save_toNat hg.top hi hj] at hlt; omega
  refine ⟨fun x hx => ?_, fun i hi => ?_, hg.apart, fun x hx => ?_, ⟨?_, ?_, houter, fun i hi => ?_, ?_, h15, he.rsp0⟩,
    ?_, ?_, hg.top, hg.low, hg.room⟩
  · rw [hr, hw]; exact hg.stack x hx
  · rw [hr, hw]; exact hg.ctxCells i hi
  · rcases hholes x hx with h | ⟨hin, -⟩
    · exact hg.holesFree x h
    · exact ⟨(hg.stack x hin).1, (hg.stack x hin).2.1⟩
  · rw [← he.cell]
    exact read64?_keep hr fun i hi => hctxB i (by omega)
  · exact fun i hi hh => he.cellData i hi (hctxH i (by omega) hh)
  · rw [← he.saves i hi]
    exact read64?_keep hr fun j hj => hsaveB i hi j hj
  · exact fun i hi j hj hh => he.savesData i hi j hj (hsaveH i hi j hj hh)
  · rw [← hg.limit, ctx_56]
    exact read64_keep fun j hj => by
      rw [UInt64.add_assoc, ← UInt64.ofNat_add]; exact hctxB (8 + j) (by omega)
  · intro j hj hh
    rw [ctx_56, UInt64.add_assoc, ← UInt64.ofNat_add] at hh
    exact hg.limitData j hj (by
      rw [ctx_56, UInt64.add_assoc, ← UInt64.ofNat_add]; exact hctxH (8 + j) (by omega) hh)

/-! ## Words on the stack -/

theorem sub_ofNat_toNat {x : Word} {n : Nat} (h : n ≤ x.toNat) : (x - UInt64.ofNat n).toNat = x.toNat - n := by
  have hx : x.toNat < 2 ^ 64 := x.toBitVec.isLt
  have hn : (UInt64.ofNat n).toNat = n := UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
  rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hn]; exact h), hn]

theorem sub8_toNat {x : Word} (h : 8 ≤ x.toNat) : (x - 8).toNat = x.toNat - 8 := sub_ofNat_toNat h

theorem word_eq {x y : Word} (h : x.toNat = y.toNat) : x = y := UInt64.toNat_inj.1 h

/-- The activation changes nothing but the running activation's registers
at a call: a chain whose head activation keeps its stack pointer, entry
registers and allowed changes is the same chain. -/
theorem Chain.react {S : Stk} {W : Wrap} {mem : Memory} {holes : Holes} {fr : Xl.Frame} {a a' : Act}
    {ret : ReturnFrame} (hsp : a'.sp = a.sp) (hentry : a'.entry = a.entry) (hallow : a'.allow = a.allow) :
    ∀ {below : List (Xl.Frame × Act × ReturnFrame)}, Chain S W mem holes fr a ret below →
      Chain S W mem holes fr a' ret below
  | [], h => fun f l pl hf => by
      obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := h f l pl hf
      exact ⟨h₁, by rw [hsp]; exact h₂, by rw [hentry]; exact h₃, by rw [hallow]; exact h₄, h₅, h₆⟩
  | (_, _, _) :: _, ⟨hex, hlink, hrest⟩ =>
      ⟨hex, fun f l pl hf f₁ l₁ pl₁ hf₁ => by
        obtain ⟨⟨h₁, h₂, h₃, h₄, h₅⟩, hA, hS⟩ := hlink f l pl hf f₁ l₁ pl₁ hf₁
        exact ⟨⟨h₁, by rw [hsp]; exact h₂, by rw [hentry]; exact h₃, by rw [hallow]; exact h₄,
          by rw [hsp]; exact h₅⟩, hA, hS⟩, hrest⟩

/-- A callee's incoming cells fit in its caller's outgoing ones. -/
theorem call_inArgs_le {S : Stk} {k : Lir.FunId} {f : Func Loc} {l : FrameLayout} {pl : Placed}
    (hf : FnAt S k f l pl) {b : Block Loc} (hb : b ∈ f.blocks.toList) {g : Lir.FunId} {args rets : List Loc}
    (hi : Inst.call g args rets ∈ b.body.toList) (hconv : Xl.conventionArgs args = true) :
    args.length - Xl.nArgRegs ≤ l.outArgs := by
  by_cases hn : args.length ≤ Xl.nArgRegs
  · omega
  · have hlt : args.length - 1 < args.length := by omega
    have harg := conventionArgs_get hconv hlt
    rw [argLoc_out (by omega)] at harg
    have hmem : Loc.outArg (args.length - 1 - Xl.nArgRegs) ∈ (Inst.call g args rets).uses :=
      List.mem_of_getElem? harg
    have := facts_outArgs hb hi hmem
    have := hf.checks.1.outArgs
    omega

end IxCC.Xv.Stacking.Proof
