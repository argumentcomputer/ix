import IxCC.Rt.Rc.Proof.InitExact
import IxCC.Rt.Rc.Proof.AllocatorMetadata

namespace IxCC.Rt.Rc.Procs.Init
open IxCC.Rt IxCC.Rt.Proof IxCC.Lir
open IxCC.X86 (Memory)

/-- Zero stores may repeat the selected address; every other store is disjoint. -/
theorem zeros_word {ctx b : Word} (hb : b.toNat+8 ≤ 2^64) :
    ∀ (m : Memory) (ds : List Int),
    (∀ j < 8, m.readable (b+UInt64.ofNat j) = true) →
    (WordAt m b 0 ∨ ∃ d ∈ ds, ctx+0+dispWord d = b) →
    (∀ d ∈ ds, (ctx+0+dispWord d).toNat+8 ≤ 2^64 ∧
      (ctx+0+dispWord d = b ∨ b.toNat+8 ≤ (ctx+0+dispWord d).toNat ∨
        (ctx+0+dispWord d).toNat+8 ≤ b.toNat)) →
    WordAt (zeros m ctx ds) b 0
  | m, [], _, hw, _ => by simpa [zeros] using hw
  | m, d :: ds, hr, hw, hd => by
    apply zeros_word hb (m.write .w64 (ctx+0+dispWord d) 0) ds
    · simpa [Memory.write] using hr
    · have hd' := hd d (by simp)
      rcases hd'.2 with he | hs
      · left
        rw [he]
        exact wordAt_write64 hr
      · rcases hw with hw | ⟨e, he, heq⟩
        · exact Or.inl (hw.write_disjoint hd'.1 hb hs)
        · rcases List.mem_cons.mp he with rfl | he
          · left
            rw [heq]
            exact wordAt_write64 hr
          · exact Or.inr ⟨e, he, heq⟩
    · exact fun e he => hd e (List.mem_cons_of_mem d he)

theorem head_address (ctx : Word) (cls : Nat) :
    ctx+0+dispWord (headOffset cls) = freeHeadAddress ctx (UInt64.ofNat cls) := by
  simp only [headOffset, freeHeadAddress, UInt64.add_zero]
  rw [show (8 : Int) * (cls : Int) = ((8*cls : Nat) : Int) by omega,
    dispWord_ofNat, UInt64.ofNat_mul]
  rw [UInt64.mul_comm]
  rfl

theorem head_nat {ctx : Word} {cls : Nat} (hfit : ctx.toNat+576 < 2^64)
    (hc : cls ≤ 71) :
    (freeHeadAddress ctx (UInt64.ofNat cls)).toNat = ctx.toNat+8*cls := by
  rw [← head_address, headOffset,
    show (8 : Int) * (cls : Int) = ((8*cls : Nat) : Int) by omega,
    dispWord_ofNat, UInt64.add_zero, addr_toNat (by omega)]

theorem zeroed_head {m : Memory} {ctx : Word} {cls : Nat}
    (hlo : 64 ≤ ctx.toNat) (hfit : ctx.toNat+576 < 2^64)
    (hc : 1 ≤ cls) (hc' : cls ≤ 32)
    (hr : ∀ j < 8, m.readable (freeHeadAddress ctx (UInt64.ofNat cls)+UInt64.ofNat j) = true) :
    WordAt (zeros m ctx (reservedOffs ++ headClasses.map headOffset))
      (freeHeadAddress ctx (UInt64.ofNat cls)) 0 := by
  have hn := head_nat hfit (cls := cls) (by omega)
  apply zeros_word (by omega) _ _ hr
  · right
    refine ⟨headOffset cls, List.mem_append_right _ (List.mem_map.mpr ⟨cls, ?_, rfl⟩),
      head_address ctx cls⟩
    simp only [headClasses, List.mem_map, List.mem_range]
    exact ⟨cls-1, by omega, by omega⟩
  · intro d hd
    have hz := zeroAddr hlo hfit hd
    refine ⟨by omega, ?_⟩
    simp only [reservedOffs, headClasses, headOffset, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false, List.mem_map, List.mem_range] at hd
    rcases hd with (rfl | rfl) | ⟨c, ⟨j, hj, rfl⟩, rfl⟩
    · right; right
      change (ctx+0+dispWord (-((16 : Nat) : Int))).toNat+8 ≤ _
      rw [ctx_disp_neg ctx (k := 16) (by decide), ctx_sub_toNat hlo (by decide)]
      omega
    · right; right
      change (ctx+0+dispWord (-((8 : Nat) : Int))).toNat+8 ≤ _
      rw [ctx_disp_neg ctx (k := 8) (by decide), ctx_sub_toNat hlo (by decide)]
      omega
    · have ha := head_address ctx (j+1)
      simp only [headOffset] at ha
      rw [ha]
      by_cases he : j+1 = cls
      · exact Or.inl (by rw [he])
      · right
        have hn' := head_nat hfit (cls := j+1) (by omega)
        omega

theorem initMemory_head {m : Memory} {ctx size budget : Word} {cls : Nat}
    (hlo : 64 ≤ ctx.toNat) (hfit : ctx.toNat+576 < 2^64)
    (hc : 1 ≤ cls) (hc' : cls ≤ 32)
    (hr : ∀ j < 8, m.readable (freeHeadAddress ctx (UInt64.ofNat cls)+UInt64.ofNat j) = true) :
    WordAt (initMemory m ctx size budget) (freeHeadAddress ctx (UInt64.ofNat cls)) 0 := by
  apply zeroed_head hlo hfit hc hc'
  simpa [Memory.write] using hr



end IxCC.Rt.Rc.Procs.Init
