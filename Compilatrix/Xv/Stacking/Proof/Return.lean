import Compilatrix.Xv.Stacking.Proof.CallStep

/-!
# The machine steps of a return

The epilogue (`epilogue_steps`: a load per saved register, then `add rsp,
size`) as checked steps, and the registers Xl gives a caller back after a
return (`returnRegs_get`).
-/

namespace Compilatrix.Xv.Stacking.Proof

open Compilatrix.X86 Compilatrix.X86.Stream

/-- Loads of registers from `rsp`-relative cells, one checked step each. -/
theorem loads_steps {cs : Checked} {block : BlockId} {returns : List ReturnFrame} {holes : Holes} :
    ∀ (L : List (GPR × Nat)) {off : Nat} {core : Core},
      Straight.Segment cs block off (L.map fun p => Instr.load .w64 p.1 (rspAt p.2)) →
      off + L.length < UInt32.size → (∀ p ∈ L, p.2 < 2 ^ 31) → (∀ p ∈ L, p.1 ≠ .rsp) → (L.map Prod.fst).Nodup →
      (∀ p ∈ L, ∀ i < 8, core.memory.readable (core.readReg .rsp + UInt64.ofNat p.2 + UInt64.ofNat i) = true) →
      (∀ p ∈ L, ReadableData holes (core.readReg .rsp + UInt64.ofNat p.2) 8) →
      ∃ core', SafeSteps Runtime.rejecting cs L.length holes (inFrame core block off returns) holes
          (inFrame core' block (off + L.length) returns) ∧
        core'.memory = core.memory ∧ core'.readReg .rsp = core.readReg .rsp ∧
        (∀ p ∈ L, core'.readReg p.1 = core.memory.read64 (core.readReg .rsp + UInt64.ofNat p.2)) ∧
        (∀ r, r ∉ L.map Prod.fst → core'.readReg r = core.readReg r)
  | [], off, core, _, _, _, _, _, _, _ =>
      ⟨core, by simpa using SafeSteps.refl holes (inFrame core block off returns), rfl, rfl, by simp,
        fun _ _ => rfl⟩
  | (r, o) :: L, off, core, hseg, hfits, hoff, hrsp, hnd, hrd, hdata => by
      have hseg' : Straight.Segment cs block off
          ([Instr.load .w64 r (rspAt o)] ++ L.map fun p => Instr.load .w64 p.1 (rspAt p.2)) := by simpa using hseg
      have hev : (rspAt o).eval core = core.readReg .rsp + UInt64.ofNat o := rspAt_eval (hoff (r, o) (by simp)) core
      have hrd' : core.memory.read? .w64 ((rspAt o).eval core) =
          .ok (core.memory.read64 (core.readReg .rsp + UInt64.ofNat o)) := by
        have h := (rangeAllowed_iff core.memory.readable (core.readReg .rsp + UInt64.ofNat o) 8).2
          (hrd (r, o) (by simp))
        rw [hev]
        simp [Memory.read?, w64_bytes, h, Memory.read64]
      obtain ⟨fl, hex⟩ := load64_exec r (rspAt o) core hrd'
      have hfoot := load64_foot r (rspAt o) core
      obtain ⟨hsafe, -⟩ : OperationSafe holes returns
          (.op { mn := .mov, w := .w64, form := .RM } [.reg r, .mem (rspAt o).normalize]) core ∧ True := by
        refine ⟨⟨fun acc hacc => ?_, fun acc hacc => ?_⟩, trivial⟩
        · simp only [Stream.operationReads, hfoot.1, List.mem_singleton] at hacc
          subst hacc
          rw [hev]; exact hdata (r, o) (by simp)
        · simp [Stream.operationWrites, hfoot.2] at hacc
      have hsegL : Straight.Segment cs block off
          [.op { mn := .mov, w := .w64, form := .RM } [.reg r, .mem (rspAt o).normalize]] := hseg'.left
      have hone := hsegL.safe_op (by simp at hfits; omega) Runtime.rejecting hsafe hex
      have hkeep : Stream.nextHoles holes (.op { mn := .mov, w := .w64, form := .RM } [.reg r, .mem (rspAt o).normalize])
          core = holes := by simp [Stream.nextHoles, Stream.operationWrites, hfoot.2, Stream.clearAccesses]
      rw [hkeep] at hone
      have hr : r ≠ .rsp := hrsp (r, o) (by simp)
      have hrsp₁ : (core.setReg r (core.memory.read64 (core.readReg .rsp + UInt64.ofNat o))).readReg .rsp =
          core.readReg .rsp := by rw [Validate.readReg_setReg, if_neg (Ne.symm hr)]
      have hnd' : r ∉ L.map Prod.fst ∧ (L.map Prod.fst).Nodup := List.nodup_cons.1 hnd
      obtain ⟨core', hrest, hm', hr', hv', hk'⟩ := loads_steps L (off := off + 1)
        (core := core.setReg r (core.memory.read64 (core.readReg .rsp + UInt64.ofNat o)))
        (by simpa using hseg'.right) (by simp at hfits ⊢; omega) (fun p hp => hoff p (by simp [hp]))
        (fun p hp => hrsp p (by simp [hp])) hnd'.2
        (fun p hp i hi => by rw [hrsp₁]; exact hrd p (by simp [hp]) i hi)
        (fun p hp => by rw [hrsp₁]; exact hdata p (by simp [hp]))
      refine ⟨core', ?_, by rw [hm']; rfl, by rw [hr', hrsp₁], fun p hp => ?_, fun q hq => ?_⟩
      · have := hone.append hrest
        rw [show off + 1 + L.length = off + ((r, o) :: L).length by simp; omega,
          show 1 + L.length = ((r, o) :: L).length by simp; omega] at this
        exact this
      · rcases List.mem_cons.1 hp with rfl | hp
        · rw [hk' _ hnd'.1, Validate.readReg_setReg, if_pos rfl]
        · rw [hv' p hp, hrsp₁]; rfl
      · simp only [List.map_cons, List.mem_cons, not_or] at hq
        rw [hk' q hq.2, Validate.readReg_setReg, if_neg hq.1]

theorem epilogue_map (l : FrameLayout) :
    (l.saveOff.map fun (r, o) => Instr.load .w64 r (rspAt o)) =
      l.saveOff.map fun p => Instr.load .w64 p.1 (rspAt p.2) := by
  congr 1

/-- The epilogue from `rsp = sp`: the saved registers come back from their
cells and `rsp` moves up past the frame. -/
theorem epilogue_steps {cs : Checked} {blk : BlockId} {off : Nat} {l : FrameLayout} {a : Facts} (hs : l.Sound a)
    {returns : List ReturnFrame} {holes : Holes} {core : Core} {sp : Word}
    (hseg : Straight.Segment cs blk off (epilogue l)) (hfits : off + (epilogue l).length < UInt32.size)
    (hrsp : core.readReg .rsp = sp)
    (hrd : ∀ r o, (r, o) ∈ l.saveOff → ∀ i < 8, core.memory.readable (sp + UInt64.ofNat o + UInt64.ofNat i) = true)
    (hdata : ∀ r o, (r, o) ∈ l.saveOff → ReadableData holes (sp + UInt64.ofNat o) 8) :
    ∃ core', SafeSteps Runtime.rejecting cs (epilogue l).length holes (inFrame core blk off returns) holes
        (inFrame core' blk (off + (epilogue l).length) returns) ∧
      core'.memory = core.memory ∧ core'.readReg .rsp = sp + UInt64.ofNat l.size ∧
      (∀ r o, (r, o) ∈ l.saveOff → core'.readReg r = core.memory.read64 (sp + UInt64.ofNat o)) ∧
      (∀ r, r ≠ .rsp → r ∉ l.saved → core'.readReg r = core.readReg r) := by
  have hbd := hs.bounded
  have hnd : (l.saveOff.map Prod.fst).Nodup := hs.savesDistinct
  have hepi : epilogue l = (l.saveOff.map fun p => Instr.load .w64 p.1 (rspAt p.2)) ++
      (if l.size == 0 then [] else [addRsp l.size]) := by simp only [epilogue, epilogue_map]
  rw [hepi] at hseg hfits ⊢
  obtain ⟨core₁, hld, hm₁, hr₁, hv₁, hk₁⟩ := loads_steps (returns := returns) (holes := holes) l.saveOff
    (off := off) (core := core) hseg.left (by simp at hfits ⊢; omega)
    (fun p hp => by have := save_range hs hp; simp only [maxFrame, slack] at hbd; omega)
    (fun p hp => saved_ne_rsp hs (saveOff_mem hp)) hnd
    (fun p hp i hi => by rw [hrsp]; exact hrd p.1 p.2 hp i hi) (fun p hp => by rw [hrsp]; exact hdata p.1 p.2 hp)
  by_cases hz : l.size = 0
  · refine ⟨core₁, ?_, hm₁, by rw [hr₁, hrsp, hz]; simp, fun r o hro => ?_, fun r hr hns => ?_⟩
    · simpa [hz] using hld
    · rw [hv₁ (r, o) hro, hrsp]
    · exact hk₁ r hns
  · have hsize : l.size < 2 ^ 31 := by simp only [maxFrame, slack] at hbd; omega
    have hseg₂ := hseg.right
    simp only [beq_iff_eq, hz, ↓reduceIte] at hseg₂
    have hadd := seg_safe_reg hseg₂ (by simp [hz] at hfits ⊢; omega) (fun _ => nofun) (fun _ => nofun) rfl
      Runtime.rejecting (holes := holes) (R := returns) (core := core₁)
      (core' := core₁.setReg .rsp (sp + UInt64.ofNat l.size)) (addRsp_footprint _ core₁) (by
        rw [exec_addRsp hsize]; exact congrArg _ (congrArg _ (by rw [← hrsp, ← hr₁]; rfl)))
    refine ⟨core₁.setReg .rsp (sp + UInt64.ofNat l.size), ?_, by rw [← hm₁]; rfl,
      by rw [Validate.readReg_setReg, if_pos rfl], fun r o hro => ?_, fun r hr hns => ?_⟩
    · rw [List.length_map] at hadd
      have := hld.append hadd
      simpa [hz, Nat.add_assoc] using this
    · rw [Validate.readReg_setReg, if_neg (saved_ne_rsp hs (saveOff_mem hro)), hv₁ (r, o) hro, hrsp]
    · rw [Validate.readReg_setReg, if_neg hr, hk₁ r hns]

/-! ## Registers after a return -/

theorem clobber_fold {clobber : List GPR} :
    ∀ (L : List GPR) {rs : Xl.Regs}, rs.size = 16 →
      (L.foldl (fun rs r => if clobber.contains r then rs.set r none else rs) rs).size = 16 ∧
        ∀ q, (L.foldl (fun rs r => if clobber.contains r then rs.set r none else rs) rs).get q =
          if q ∈ L ∧ clobber.contains q = true then none else rs.get q
  | [], rs, hs => ⟨hs, fun q => by simp⟩
  | p :: L, rs, hs => by
      have hs' : (if clobber.contains p then rs.set p none else rs).size = 16 := by
        split <;> simp [Xl.Regs.size_set, hs]
      have hstep : ∀ q, (if clobber.contains p then rs.set p none else rs).get q =
          if clobber.contains p = true ∧ q = p then none else rs.get q := by
        intro q
        by_cases hp : clobber.contains p = true
        · simp only [hp, ↓reduceIte, true_and]
          rw [Xl.Regs.get_set _ hs]
        · rw [if_neg hp, if_neg (fun h => hp h.1)]
      obtain ⟨h1, h2⟩ := clobber_fold L hs'
      refine ⟨by simpa using h1, fun q => ?_⟩
      rw [List.foldl_cons, h2 q, hstep q]
      by_cases hqL : q ∈ L <;> by_cases hc : clobber.contains q = true <;> by_cases e : q = p <;> simp_all

theorem foldl_set_notin {rs : Xl.Regs} (hs : rs.size = 16) :
    ∀ (L : List (GPR × Word)) {q : GPR}, q ∉ L.map Prod.fst →
      (L.foldl (fun rs (p : GPR × Word) => rs.set p.1 (some p.2)) rs).get q = rs.get q
  | [], _, _ => rfl
  | (r, v) :: L, q, hq => by
      simp only [List.map_cons, List.mem_cons, not_or] at hq
      rw [List.foldl_cons, foldl_set_notin (by rw [Xl.Regs.size_set, hs]) L hq.2, Xl.Regs.get_set _ hs,
        if_neg hq.1]

theorem foldl_set_in {rs : Xl.Regs} (hs : rs.size = 16) :
    ∀ (L : List (GPR × Word)) {q : GPR} {v : Word}, (L.map Prod.fst).Nodup → (q, v) ∈ L →
      (L.foldl (fun rs (p : GPR × Word) => rs.set p.1 (some p.2)) rs).get q = some v
  | [], _, _, _, h => by simp at h
  | (r, w) :: L, q, v, hnd, h => by
      have hnd' : r ∉ L.map Prod.fst ∧ (L.map Prod.fst).Nodup := List.nodup_cons.1 hnd
      rw [List.foldl_cons]
      rcases List.mem_cons.1 h with e | h
      · cases e
        rw [foldl_set_notin (by rw [Xl.Regs.size_set, hs]) L hnd'.1, Xl.Regs.get_set _ hs, if_pos rfl]
      · exact foldl_set_in (by rw [Xl.Regs.size_set, hs]) L hnd'.2 h

theorem mem_allGPRs (r : GPR) : r ∈ allGPRs := by cases r <;> decide

theorem resultRegs_zip_nodup : ∀ vals : List Word, ((Lir.Conv.resultRegs.zip vals).map Prod.fst).Nodup
  | [] => by simp [Lir.Conv.resultRegs]
  | [_] => by simp [Lir.Conv.resultRegs]
  | _ :: _ :: _ => by simp [Lir.Conv.resultRegs]

/-- The registers Xl gives a caller back: a result, or, outside the
callee's clobbers and the results, the caller's own value. -/
theorem returnRegs_spec {saved : Xl.Regs} (hs : saved.size = 16) (clobber : List GPR) (vals : List Word) :
    (Xl.returnRegs saved clobber vals).size = 16 ∧ ∀ r v, (Xl.returnRegs saved clobber vals).get r = some v →
      (∃ i : Nat, Lir.Conv.resultRegs[i]? = some r ∧ vals[i]? = some v) ∨
      (r ∉ (Lir.Conv.resultRegs.zip vals).map Prod.fst ∧ clobber.contains r = false ∧ saved.get r = some v) := by
  obtain ⟨h1, h2⟩ := clobber_fold (clobber := clobber) allGPRs hs
  refine ⟨foldl_set_size h1 _, fun r v hv => ?_⟩
  by_cases hr : r ∈ (Lir.Conv.resultRegs.zip vals).map Prod.fst
  · left
    obtain ⟨⟨r', v'⟩, hm, e⟩ := List.mem_map.1 hr
    simp only at e
    subst e
    have hv' := hv.symm.trans (foldl_set_in h1 _ (resultRegs_zip_nodup vals) hm)
    cases hv'
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hm
    rw [List.getElem?_zip_eq_some] at hi
    exact ⟨i, hi.1, hi.2⟩
  · right
    have hv' := (foldl_set_notin h1 _ hr).symm.trans hv
    rw [h2 r] at hv'
    by_cases hc : clobber.contains r = true
    · rw [if_pos ⟨mem_allGPRs r, hc⟩] at hv'; cases hv'
    · rw [if_neg (fun h => hc h.2)] at hv'
      exact ⟨hr, by simpa using hc, hv'⟩

end Compilatrix.Xv.Stacking.Proof
