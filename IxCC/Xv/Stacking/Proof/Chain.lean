import IxCC.Xv.Stacking.Proof.Cells

/-!
# The suspended activations are out of the running one's reach

Everything the suspended activations keep (`Chain`) lies on the stack at or
above the first one's slots: its saves, return slot and defined cells, and
the deeper activations, each above the one it called. So a step of the
running activation, which changes no byte there and adds no hole there,
keeps the chain (`Chain.mono`).
-/

namespace IxCC.Xv.Stacking.Proof

open IxCC.X86 IxCC.X86.Stream

/-- Bytes from `a` on, for eight bytes, are kept. -/
theorem read64_keep {mem mem' : Memory} {a : Word} (h : ∀ i < 8, mem'.bytes (a + UInt64.ofNat i) = mem.bytes (a + UInt64.ofNat i)) :
    mem'.read64 a = mem.read64 a := read64_congr h

/-- Eight readable bytes stay readable when the new holes are old holes or
below them. -/
theorem ReadableData.keep {holes holes' : Holes} {a : Word} {B : Nat} (h : ReadableData holes a 8)
    (hab : ∀ i < 8, B ≤ (a + UInt64.ofNat i).toNat) (hh : ∀ x, holes' x → holes x ∨ x.toNat < B) :
    ReadableData holes' a 8 := fun i hi hx => by
  rcases hh _ hx with hx | hx
  · exact h i hi hx
  · have := hab i hi; omega

/-- A suspended activation's defined cell is a slot or an incoming argument:
at or above its slots. -/
theorem susp_cell_off {fr : Xl.Frame} {l : FrameLayout} {f : Func Loc} (hs : l.Sound f.facts)
    (hout : ∀ i : Nat, fr.outArgs[i]? = none) {x : Loc} {v : Word} (hv : Xl.read Xl.Regs.empty fr x = some v)
    {o : Nat} (hc : CellAt l f.facts.inArgs x o) : 8 * l.outArgs ≤ o := by
  cases hc with
  | slot ho =>
    have hm : o ∈ l.cells := List.mem_append_left _ (List.mem_of_getElem? ho)
    exact (hs.inBounds o hm).1
  | outArg hi =>
    rename_i i
    simp [Xl.read, hout i] at hv
  | inArg hi => have := hs.outArgsFit; omega

/-- The chain survives a step that keeps every byte from `B` up to the
wrapper's frame and adds holes only below `B`, where `B` is at most the
first suspended activation's slots. -/
theorem Chain.mono {S : Stk} {W : Wrap} {mem mem' : Memory} {holes holes' : Holes} {B : Nat}
    (htop : W.entrySp.toNat + 64 ≤ 2 ^ 64)
    (hbytes : ∀ x, B ≤ x.toNat → x.toNat < W.entrySp.toNat → mem'.bytes x = mem.bytes x)
    (hholes : ∀ x, holes' x → holes x ∨ x.toNat < B) :
    ∀ {fr : Xl.Frame} {a : Act} {ret : ReturnFrame} {below : List (Xl.Frame × Act × ReturnFrame)},
      Chain S W mem holes fr a ret below →
      (∀ fr₁ a₁ ret₁ rest, below = (fr₁, a₁, ret₁) :: rest → ∀ f₁ l₁ pl₁, FnAt S fr₁.fn f₁ l₁ pl₁ →
        B ≤ a₁.sp.toNat + 8 * l₁.outArgs) →
      Chain S W mem' holes' fr a ret below
  | fr, a, ret, [], h, _ => h
  | fr, a, ret, (fr₁, a₁, ret₁) :: rest, ⟨hex, hlink, hrest⟩, hB => by
    obtain ⟨f₁, l₁, pl₁, hf₁⟩ := hex
    have hB₁ := hB fr₁ a₁ ret₁ rest rfl f₁ l₁ pl₁ hf₁
    refine ⟨⟨f₁, l₁, pl₁, hf₁⟩, fun f l pl hf f₁' l₁' pl₁' hf₁' => ?_, Chain.mono htop hbytes hholes hrest ?_⟩
    · obtain ⟨hL, hA, hS⟩ := hlink f l pl hf f₁' l₁' pl₁' hf₁'
      obtain ⟨e₁, e₂, e₃⟩ := hf₁'.unique hf₁
      subst e₁ e₂ e₃
      have hs := hf₁.checks.1
      have span := hA.span htop
      have hfit := hs.outArgsFit
      -- A byte at offset `o` of the suspended frame, at or above its slots
      have hkeep : ∀ o, 8 * l₁.outArgs ≤ o → o + 8 ≤ l₁.size + 8 + 8 * f₁.facts.inArgs → ∀ i < 8,
          mem'.bytes (a₁.sp + UInt64.ofNat o + UInt64.ofNat i) = mem.bytes (a₁.sp + UInt64.ofNat o + UInt64.ofNat i) ∧
            B ≤ (a₁.sp + UInt64.ofNat o + UInt64.ofNat i).toNat := by
        intro o ho ho' i hi
        have e : a₁.sp + UInt64.ofNat o + UInt64.ofNat i = a₁.sp + UInt64.ofNat (o + i) := by
          rw [UInt64.add_assoc, ← UInt64.ofNat_add]
        have hb := (span.byte (o := o + i) (by omega)).1
        rw [e, hb]
        have := span.high
        exact ⟨hbytes _ (by rw [hb]; omega) (by rw [hb]; omega), by omega⟩
      refine ⟨hL, ⟨fun r o hro => ?_, fun r o hro => ?_, hA.allowed, hA.slot, ?_, hA.snapshot, hA.align, hA.low,
        hA.high, hA.inBound⟩, ⟨hS.call, hS.outArgs, hS.size, hS.regs, hS.r15, hS.rsp, hS.kept, fun x hx v hv => ?_,
        hS.inArgs, hS.room⟩⟩
      · have hsr := save_range hs hro
        rw [← hA.saves r o hro]
        exact read64_keep fun i hi => by
          exact (hkeep o hsr.2.1 (by omega) i hi).1
      · have hsr := save_range hs hro
        exact ReadableData.keep (hA.savesData r o hro) (fun i hi => (hkeep o hsr.2.1 (by omega) i hi).2) hholes
      · rw [← hA.retAddr, hA.slot]
        exact read64_keep fun i hi => (hkeep l₁.size (by omega) (by omega) i hi).1
      · obtain ⟨m, hm, hv', hdata⟩ := hS.cells x hx v hv
        obtain ⟨o, hc, rfl⟩ := cell_off hm
        rw [hf₁.play, hf₁.pfacts] at hc
        have ho := susp_cell_off hs hS.outArgs hv hc
        obtain ⟨-, hr, -⟩ := hc.range hs
        have heval : (rspAt o).eval (atSp a₁.sp) = a₁.sp + UInt64.ofNat o := by
          have hb := hs.bounded
          have hib := hA.inBound
          rw [rspAt_eval (by simp only [maxFrame, slack] at hb hib; omega)]
          rfl
        refine ⟨rspAt o, hm, ?_, ?_⟩
        · rw [← hv', heval]
          exact read64_keep fun i hi => (hkeep o ho hr i hi).1
        · rw [heval] at hdata ⊢
          exact ReadableData.keep hdata (fun i hi => (hkeep o ho hr i hi).2) hholes
    · intro fr₂ a₂ ret₂ rest' e f₂ l₂ pl₂ hf₂
      subst e
      obtain ⟨hex₂, hlink₂, -⟩ := hrest
      obtain ⟨hL₂, -, -⟩ := hlink₂ f₁ l₁ pl₁ hf₁ f₂ l₂ pl₂ hf₂
      have hs := hf₁.checks.1
      have := hs.outArgsFit
      have := hL₂.sp
      omega

end IxCC.Xv.Stacking.Proof
