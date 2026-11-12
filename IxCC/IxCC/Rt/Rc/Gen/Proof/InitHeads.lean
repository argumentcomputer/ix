import IxCC.Rt.Rc.Proof.InitHeads
import IxCC.Rt.Rc.Gen.Proof.AllocatorMetadata

/-! `cx_init` zeroes the free-list heads of all 71 classes (`Rt.headClasses`): each of them reads
back as the empty list. -/
namespace IxCC.Rt.Rc.Gen.Init
open IxCC.Rt.Rc.Procs IxCC.Rt.Rc.Procs.Init
open IxCC.Rt IxCC.Rt.Proof IxCC.Lir
open IxCC.X86 (Memory)

theorem zeroed_head_all {m : Memory} {ctx : Word} {cls : Nat}
    (hlo : 64 ≤ ctx.toNat) (hfit : ctx.toNat+576 < 2^64)
    (hc : 1 ≤ cls) (hc' : cls ≤ maxClass)
    (hr : ∀ j < 8, m.readable (freeHeadAddress ctx (UInt64.ofNat cls)+UInt64.ofNat j) = true) :
    WordAt (zeros m ctx (reservedOffs ++ headClasses.map headOffset))
      (freeHeadAddress ctx (UInt64.ofNat cls)) 0 := by
  unfold maxClass at hc'
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

theorem initMemory_head_all {m : Memory} {ctx size budget : Word} {cls : Nat}
    (hlo : 64 ≤ ctx.toNat) (hfit : ctx.toNat+576 < 2^64)
    (hc : 1 ≤ cls) (hc' : cls ≤ maxClass)
    (hr : ∀ j < 8, m.readable (freeHeadAddress ctx (UInt64.ofNat cls)+UInt64.ofNat j) = true) :
    WordAt (initMemory m ctx size budget) (freeHeadAddress ctx (UInt64.ofNat cls)) 0 := by
  apply zeroed_head_all hlo hfit hc hc'
  simpa [Memory.write] using hr

end IxCC.Rt.Rc.Gen.Init
