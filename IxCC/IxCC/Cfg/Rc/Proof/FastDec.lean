import IxCC.Cfg.Rc.FastDec
import IxCC.Cfg.Rc.Proof.Inline
import IxCC.X86.Memory

/-! # Semantic preservation of `Cfg.Rc.FastDec`

Proves `install_sim`: replacing `Rt.Rc.Gen.dec` at `l.decProc` with `fastDec`
preserves exact `Lir.eval` execution (`Sem.Sim Eq (fun k => k + 3 * Lir.fuelFor (install l p) k)`)
on every input state and arbitrary permissioned memory, with zero heap invariants. -/

set_option autoImplicit false
namespace IxCC.Cfg.Rc.FastDec

open IxCC.Cfg.Rc.Native
open IxCC.Rt.Rc.Procs (v i to cellAddr)

@[local simp] private theorem env_get?_insert_eq (e : Lir.Env) (k k' : Lir.VReg) (val : Lir.Word) :
    (e.insert k val)[k']? = if k = k' then some val else e[k']? := by
  by_cases h : k = k'
  · subst h; simp
  · simp [h, Lir.env_insert_ne _ _ h]

@[local simp] private theorem env_get_insert_eq (e : Lir.Env) (k k' : Lir.VReg) (val : Lir.Word)
    (h : k' ∈ e.insert k val) :
    (e.insert k val)[k']'h =
      if heq : k = k' then val
      else e[k']'(by simpa [Std.HashMap.mem_insert, beq_iff_eq, heq] using h) := by
  by_cases heq : k = k'
  · subst heq; simp
  · simp [Std.HashMap.getElem_insert, beq_iff_eq, heq]

@[local simp] private theorem v_def (x : Lir.VReg) : v x = Lir.Arg.v x := rfl
@[local simp] private theorem i_def (n : Nat) : i n = Lir.Arg.imm (UInt64.ofNat n) := rfl
@[local simp] private theorem dispWord_0 : Lir.dispWord 0 = 0 := by decide
@[local simp] private theorem dispWord_1 : Lir.dispWord 1 = 1 := by decide
@[local simp] private theorem dispWord_4 : Lir.dispWord 4 = 4 := by decide
@[local simp] private theorem dispWord_8 : Lir.dispWord 8 = 8 := by decide
@[local simp] private theorem dispWord_16 : Lir.dispWord 16 = 16 := by decide

/-! ## Program lookup lemmas -/

theorem install_main (l : Layout) (p : Lir.Program) : (install l p).main = p.main := rfl

theorem install_funcs_size (l : Layout) (p : Lir.Program) :
    (install l p).funcs.size = p.funcs.size := by
  simp [install]

theorem install_get_ne (l : Layout) (p : Lir.Program) {f : Lir.FunId} (hne : f ≠ l.decProc) :
    (install l p).funcs[f]? = p.funcs[f]? := by
  simp only [install, Array.getElem?_mapIdx]
  cases h : p.funcs[f]? with
  | none => simp
  | some F => simp [hne]

theorem install_get_dec (l : Layout) (p : Lir.Program)
    (hdec : p.funcs[l.decProc]? = some Rt.Rc.Gen.dec) :
    (install l p).funcs[l.decProc]? = some fastDec := by
  simp only [install, Array.getElem?_mapIdx, hdec]
  simp

theorem install_push (l : Layout) (p : Lir.Program) (F : Lir.Func)
    (hle : l.decProc < p.funcs.size) :
    install l { p with funcs := p.funcs.push F } =
      { install l p with funcs := (install l p).funcs.push F } := by
  have hne : p.funcs.size ≠ l.decProc := by omega
  simp [install, Array.mapIdx_push, hne]

/-! ## Byte-memory helpers for arbitrary permissioned memory -/

private theorem writeLittle_readable (mem : X86.Memory) (a val : Lir.Word) :
    ∀ n, (mem.writeLittle a val n).readable = mem.readable
  | 0 => rfl
  | n + 1 => by simp [X86.Memory.writeLittle, X86.Memory.writeByte, writeLittle_readable mem a val n]

private theorem writeLittle_writable (mem : X86.Memory) (a val : Lir.Word) :
    ∀ n, (mem.writeLittle a val n).writable = mem.writable
  | 0 => rfl
  | n + 1 => by simp [X86.Memory.writeLittle, X86.Memory.writeByte, writeLittle_writable mem a val n]

private theorem write_writable {mem mem' : X86.Memory} {w : X86.Width} {a val : Lir.Word}
    (h : mem.write? w a val = .ok mem') : mem'.writable = mem.writable := by
  simp only [X86.Memory.write?] at h
  split at h
  · cases h; exact writeLittle_writable mem a val w.bytes
  · cases h

private theorem write_ok_of_writable_eq {mem1 mem2 : X86.Memory} {w : X86.Width} {a val1 val2 : Lir.Word}
    (hw : mem1.writable = mem2.writable) (hok : ∃ m, mem1.write? w a val1 = .ok m) :
    ∃ m, mem2.write? w a val2 = .ok m := by
  obtain ⟨m, hm⟩ := hok
  simp only [X86.Memory.write?] at hm ⊢
  rw [← hw]
  split at hm
  · rename_i hp; simp [hp]
  · cases hm

private theorem add_offset_ne (a : Lir.Word) {o1 o2 i j : Nat}
    (h1 : o1 + i < 64) (h2 : o2 + j < 64) (hne : o1 + i ≠ o2 + j) :
    a + UInt64.ofNat o1 + UInt64.ofNat i ≠ a + UInt64.ofNat o2 + UInt64.ofNat j := by
  intro heq
  have h := congrArg UInt64.toNat heq
  simp only [UInt64.toNat_add, UInt64.toNat_ofNat'] at h
  omega

private theorem write_read_disjoint {mem mem' : X86.Memory} {w1 w2 : X86.Width}
    {a val : Lir.Word} {o1 o2 : Nat}
    (hw : mem.write? w2 (a + UInt64.ofNat o2) val = .ok mem')
    (h1 : o1 + w1.bytes ≤ 64) (h2 : o2 + w2.bytes ≤ 64)
    (hdisj : o1 + w1.bytes ≤ o2 ∨ o2 + w2.bytes ≤ o1) :
    mem'.read? w1 (a + UInt64.ofNat o1) = mem.read? w1 (a + UInt64.ofNat o1) := by
  simp only [X86.Memory.write?] at hw
  split at hw
  · cases hw
    simp only [X86.Memory.read?, X86.Memory.read, X86.Memory.write, writeLittle_readable]
    split
    · congr 1
      apply X86.Memory.readLittle_congr
      intro i hi
      apply X86.Memory.writeLittle_bytes_outside
      intro j hj
      exact add_offset_ne a (by omega) (by omega) (by omega)
    · rfl
  · cases hw

private theorem u8_shiftLeft_getLsbD (b : UInt8) (n k : Nat) (hn : n < 8) (hk : k < 8) :
    (b.toUInt64 <<< UInt64.ofNat (8 * n)).toBitVec.getLsbD (8 * n + k) = b.toBitVec.getLsbD k := by
  match n with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 =>
    simp only [UInt64.toBitVec_shiftLeft, UInt8.toBitVec_toUInt64,
      BitVec.shiftLeft_eq', BitVec.toNat_umod, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
    simp (discharger := omega) [decide_eq_true, decide_eq_false]
  | _ + 8 => omega

private theorem readLittle_eq_zero_bytes (mem : X86.Memory) (a : Lir.Word) :
    ∀ n, n ≤ 8 → mem.readLittle a n = 0 → ∀ i < n, mem.bytes (a + UInt64.ofNat i) = 0
  | 0, _, _, _, hi => absurd hi (by omega)
  | n + 1, hn, hz, i, hi => by
    rw [X86.Memory.readLittle] at hz
    have hbv : (mem.readLittle a n).toBitVec |||
        ((mem.bytes (a + UInt64.ofNat n)).toUInt64 <<< UInt64.ofNat (8 * n)).toBitVec = 0 := by
      have := congrArg UInt64.toBitVec hz
      simpa [UInt64.toBitVec_or] using this
    have hleft : mem.readLittle a n = 0 := by
      apply UInt64.toBitVec_inj.mp
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      have h0 : (0 : BitVec 64).getLsbD k = false := by simp
      have h := congrArg (fun x => x.getLsbD k) hbv
      simp only [BitVec.getLsbD_or, h0, Bool.or_eq_false_iff] at h
      simpa [h0] using h.1
    have hright : mem.bytes (a + UInt64.ofNat n) = 0 := by
      apply UInt8.toBitVec_inj.mp
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      have hlt : 8 * n + k < 64 := by omega
      have h0 : (0 : BitVec 64).getLsbD (8 * n + k) = false := by simp
      have h := congrArg (fun x => x.getLsbD (8 * n + k)) hbv
      simp only [BitVec.getLsbD_or, h0, Bool.or_eq_false_iff] at h
      have hr := h.2
      have hbit := u8_shiftLeft_getLsbD (mem.bytes (a + UInt64.ofNat n)) n k (by omega) hk
      have hz8 : (UInt8.toBitVec 0).getLsbD k = false := by simp
      rw [hz8, ← hbit]
      exact hr
    by_cases heq : i = n
    · subst heq; exact hright
    · exact readLittle_eq_zero_bytes mem a n (by omega) hleft i (by omega)

private theorem writeLittle_zero_id {mem : X86.Memory} {a : Lir.Word} {n : Nat}
    (hn : n ≤ 8) (hzero : mem.readLittle a n = 0) :
    mem.writeLittle a 0 n = mem := by
  cases mem with
  | mk bytes readable writable =>
    have hr := writeLittle_readable { bytes, readable, writable } a 0 n
    have hw := writeLittle_writable { bytes, readable, writable } a 0 n
    have hb : (({ bytes, readable, writable } : X86.Memory).writeLittle a 0 n).bytes = bytes := by
      funext addr
      by_cases hex : ∃ i < n, addr = a + UInt64.ofNat i
      · obtain ⟨i, hi, rfl⟩ := hex
        rw [X86.Memory.writeLittle_bytes _ a 0 hn hi]
        have := readLittle_eq_zero_bytes { bytes, readable, writable } a n hn hzero i hi
        simpa using this.symm
      · apply X86.Memory.writeLittle_bytes_outside
        intro i hi hEq
        exact hex ⟨i, hi, hEq⟩
    cases hres : ({ bytes, readable, writable } : X86.Memory).writeLittle a 0 n with
    | mk b' r' w' =>
      rw [hres] at hr hw hb
      simp only at hr hw hb
      subst hb hr hw
      rfl

private theorem write32_write32_zero_id {mem mem1 mem2 : X86.Memory} {a val : Lir.Word}
    (hread : mem.read? .w32 a = .ok 0)
    (hw1 : mem.write? .w32 a val = .ok mem1)
    (hw2 : mem1.write? .w32 a 0 = .ok mem2) :
    mem2 = mem := by
  simp only [X86.Memory.read?, X86.Memory.read, X86.Width.bytes] at hread
  by_cases hperm : X86.Memory.rangeAllowed mem.readable a 4 = true
  · simp only [hperm, ↓reduceIte, Except.ok.injEq] at hread
    have hzero : mem.readLittle a 4 = 0 := hread
    simp only [X86.Memory.write?, X86.Memory.write, X86.Width.bytes] at hw1 hw2
    by_cases hwp1 : X86.Memory.rangeAllowed mem.writable a 4 = true
    · simp only [hwp1, ↓reduceIte, Except.ok.injEq] at hw1
      subst hw1
      by_cases hwp2 : X86.Memory.rangeAllowed (mem.writeLittle a val 4).writable a 4 = true
      · simp only [hwp2, ↓reduceIte, Except.ok.injEq] at hw2
        subst hw2
        cases mem with
        | mk bytes readable writable =>
          have hr1 := writeLittle_readable { bytes, readable, writable } a val 4
          have hw1' := writeLittle_writable { bytes, readable, writable } a val 4
          have hr2 := writeLittle_readable (({ bytes, readable, writable } : X86.Memory).writeLittle a val 4) a 0 4
          have hw2' := writeLittle_writable (({ bytes, readable, writable } : X86.Memory).writeLittle a val 4) a 0 4
          have hb : ((({ bytes, readable, writable } : X86.Memory).writeLittle a val 4).writeLittle a 0 4).bytes = bytes := by
            funext addr
            by_cases hex : ∃ i < 4, addr = a + UInt64.ofNat i
            · obtain ⟨i, hi, rfl⟩ := hex
              rw [X86.Memory.writeLittle_bytes _ a 0 (by omega) hi]
              have := readLittle_eq_zero_bytes { bytes, readable, writable } a 4 (by omega) hzero i hi
              simpa using this.symm
            · rw [X86.Memory.writeLittle_bytes_outside _ a 0 addr 4 (fun i hi hEq => hex ⟨i, hi, hEq⟩),
                  X86.Memory.writeLittle_bytes_outside _ a val addr 4 (fun i hi hEq => hex ⟨i, hi, hEq⟩)]
          cases hres : (({ bytes, readable, writable } : X86.Memory).writeLittle a val 4).writeLittle a 0 4 with
          | mk b' r' w' =>
            rw [hres] at hr2 hw2' hb
            rw [hr1] at hr2; rw [hw1'] at hw2'
            simp only at hr2 hw2' hb
            subst hb hr2 hw2'
            rfl
      · simp [hwp2] at hw2
    · simp [hwp1] at hw1
  · simp [hperm] at hread

private theorem write32_zero_id {mem mem1 : X86.Memory} {a : Lir.Word}
    (hread : mem.read? .w32 a = .ok 0)
    (hw1 : mem.write? .w32 a 0 = .ok mem1) :
    mem1 = mem := by
  simp only [X86.Memory.read?, X86.Memory.read, X86.Width.bytes] at hread
  by_cases hperm : X86.Memory.rangeAllowed mem.readable a 4 = true
  · simp only [hperm, ↓reduceIte, Except.ok.injEq] at hread
    simp only [X86.Memory.write?, X86.Memory.write, X86.Width.bytes] at hw1
    by_cases hwp : X86.Memory.rangeAllowed mem.writable a 4 = true
    · simp only [hwp, ↓reduceIte, Except.ok.injEq] at hw1
      subst hw1
      exact writeLittle_zero_id (by omega) hread
    · simp [hwp] at hw1
  · simp [hperm] at hread

private theorem pack32 (value : Lir.Word) :
    ((0 : Lir.Word) ||| value.toUInt8.toUInt64 <<< 0 |||
      (value >>> 8).toUInt8.toUInt64 <<< 8 |||
      (value >>> 16).toUInt8.toUInt64 <<< 16 |||
      (value >>> 24).toUInt8.toUInt64 <<< 24) = X86.Width.w32.truncate value := by
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [X86.Width.truncate, X86.Width.mask, UInt64.toBitVec_and,
    UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight,
    UInt64.toBitVec_toUInt8, UInt8.toBitVec_toUInt64, UInt64.toBitVec_ofNat,
    BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', BitVec.toNat_umod, BitVec.toNat_ofNat,
    BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth]
  have hmask : (4294967295#64 : BitVec 64).getLsbD k = decide (k < 32) := by
    have : k < 64 := hk; revert k; decide
  have h0 : (0#64 : BitVec 64).getLsbD k = false := by
    have : k < 64 := hk; revert k; decide
  rw [hmask, h0]
  have ranges : k < 8 ∨ (8 ≤ k ∧ k < 16) ∨ (16 ≤ k ∧ k < 24) ∨ (24 ≤ k ∧ k < 32) ∨ (32 ≤ k ∧ k < 64) := by omega
  rcases ranges with h | h | h | h | h <;>
    simp (discharger := omega) [decide_eq_true, decide_eq_false]

private theorem read32_write32 {mem mem' : X86.Memory} {a val r0 : Lir.Word}
    (hread : mem.read? .w32 a = .ok r0)
    (hw : mem.write? .w32 a val = .ok mem') :
    mem'.read? .w32 a = .ok (X86.Width.w32.truncate val) := by
  simp only [X86.Memory.read?, X86.Width.bytes] at hread
  by_cases hperm : X86.Memory.rangeAllowed mem.readable a 4 = true
  · simp only [X86.Memory.write?, X86.Memory.write, X86.Width.bytes] at hw
    by_cases hwp : X86.Memory.rangeAllowed mem.writable a 4 = true
    · simp only [hwp, ↓reduceIte, Except.ok.injEq] at hw
      subst hw
      simp only [X86.Memory.read?, X86.Memory.read, X86.Width.bytes, writeLittle_readable, hperm,
        ↓reduceIte, Except.ok.injEq]
      simp (discharger := omega) only [X86.Memory.readLittle, X86.Memory.writeLittle_bytes]
      simpa using pack32 val
    · simp [hwp] at hw
  · simp [hperm] at hread

private theorem read64_write64_ok {mem mem' : X86.Memory} {a val r0 : Lir.Word}
    (hread : mem.read? .w64 a = .ok r0)
    (hw : mem.write? .w64 a val = .ok mem') :
    mem'.read? .w64 a = .ok val := by
  simp only [X86.Memory.read?] at hread
  split at hread
  · rename_i hperm
    simp only [X86.Memory.write?, X86.Memory.write] at hw
    split at hw
    · cases hw
      simp only [X86.Memory.read?, writeLittle_readable, hperm, ↓reduceIte, Except.ok.injEq]
      exact X86.Memory.read64_write64 mem a val
    · cases hw
  · cases hread

private theorem read32_truncate_self {mem : X86.Memory} {a val : Lir.Word}
    (h : mem.read? .w32 a = .ok val) : X86.Width.w32.truncate val = val := by
  simp only [X86.Memory.read?, X86.Memory.read, X86.Width.bytes] at h
  by_cases hperm : X86.Memory.rangeAllowed mem.readable a 4 = true
  · simp only [hperm, ↓reduceIte, Except.ok.injEq] at h
    subst h
    apply UInt64.toBitVec_inj.mp
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    have hmask : (4294967295#64 : BitVec 64).getLsbD k = decide (k < 32) := by
      have : k < 64 := hk; revert k; decide
    simp only [X86.Width.truncate, X86.Width.mask, UInt64.toBitVec_and, BitVec.getLsbD_and,
      UInt64.toBitVec_ofNat, hmask]
    by_cases hlt : k < 32
    · simp [hlt]
    · simp only [hlt, decide_false, Bool.and_false]
      simp only [X86.Memory.readLittle, UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft,
        UInt8.toBitVec_toUInt64, UInt64.toBitVec_ofNat, BitVec.shiftLeft_eq',
        BitVec.toNat_umod, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
        BitVec.getLsbD_setWidth]
      simp (discharger := omega)
  · simp [hperm] at h

private theorem w64_truncate_self (x : Lir.Word) : X86.Width.w64.truncate x = x := by
  apply UInt64.toBitVec_inj.mp
  have hall : (X86.Width.w64.mask).toBitVec = BitVec.allOnes 64 := by decide
  rw [X86.Width.truncate, UInt64.toBitVec_and, hall, BitVec.and_allOnes]

private theorem w32_truncate_zero : X86.Width.w32.truncate 0 = 0 := by decide
private theorem w32_truncate_one : X86.Width.w32.truncate 1 = 1 := by decide

private theorem w32_slt_zero_of_zero : Lir.Cond.holds .slt .w32 0 0 = false := by decide

private theorem w32_eq_zero_of_truncate {val : Lir.Word} (htr : X86.Width.w32.truncate val = val) :
    Lir.Cond.holds .eq .w32 val 0 = (val == 0) := by
  simp [Lir.Cond.holds, htr, w32_truncate_zero]

private theorem w64_tnz_1 (w : Lir.Word) :
    Lir.Cond.holds .tnz .w64 w 1 = ((w &&& 1) != 0) := by
  simp [Lir.Cond.holds, w64_truncate_self]

private theorem w64_eq_iff (a b : Lir.Word) :
    Lir.Cond.holds .eq .w64 a b = (a == b) := by
  simp [Lir.Cond.holds, w64_truncate_self]

private theorem w64_sub (a b : Lir.Word) :
    Lir.BinOp.eval .sub .w64 a b = some (a - b) := by
  simp [Lir.BinOp.eval, w64_truncate_self]

private theorem w32_sub (a b : Lir.Word) :
    Lir.BinOp.eval .sub .w32 a b = some (X86.Width.w32.truncate (a - b)) := by
  simp [Lir.BinOp.eval]

private theorem cond_eq_w64_of_w32_trunc (val : Lir.Word) :
    Lir.Cond.holds .eq .w64 (X86.Width.w32.truncate val) 0 = Lir.Cond.holds .eq .w32 val 0 := by
  simp [Lir.Cond.holds, w64_truncate_self, w32_truncate_zero]

/-! ## Synchronization relation between `Rt.Rc.Gen.dec` and `fastDec` -/

inductive DecFrameRel (fn : Lir.FunId) : Lir.Frame → Lir.Frame → Prop
  | b0 {e₁ e₂ : Lir.Env} {w : Lir.Word}
      (h0₁ : e₁[0]? = some w) (h0₂ : e₂[0]? = some w) :
      DecFrameRel fn { fn, label := 0, pos := 0, env := e₁ }
        { fn, label := 0, pos := 0, env := e₂ }
  | b1 {e₁ e₂ : Lir.Env} {cur par : Lir.Word}
      (h1₁ : e₁[1]? = some cur) (h2₁ : e₁[2]? = some par)
      (h1₂ : e₂[1]? = some cur) (h2₂ : e₂[2]? = some par) :
      DecFrameRel fn { fn, label := 1, pos := 0, env := e₁ }
        { fn, label := 1, pos := 0, env := e₂ }
  | b2 {e₁ e₂ : Lir.Env} {cur par : Lir.Word}
      (h1 : e₁[1]? = some cur) (h2 : e₁[2]? = some par)
      (h20 : e₂[20]? = some cur) (h21 : e₂[21]? = some par) :
      DecFrameRel fn { fn, label := 2, pos := 0, env := e₁ }
        { fn, label := 2, pos := 0, env := e₂ }
  | b6 {e₁ e₂ : Lir.Env} {par : Lir.Word}
      (h8₁ : e₁[8]? = some par) (h8₂ : e₂[8]? = some par) :
      DecFrameRel fn { fn, label := 6, pos := 0, env := e₁ }
        { fn, label := 6, pos := 0, env := e₂ }
  | b7 {e₁ e₂ : Lir.Env} {par : Lir.Word}
      (h8₁ : e₁[8]? = some par) (h8₂ : e₂[8]? = some par) (hne : par ≠ 0) :
      DecFrameRel fn { fn, label := 7, pos := 0, env := e₁ }
        { fn, label := 7, pos := 0, env := e₂ }
  | b9 {e₁ e₂ : Lir.Env} {par : Lir.Word}
      (h8₁ : e₁[8]? = some par) (h8₂ : e₂[8]? = some par) :
      DecFrameRel fn { fn, label := 9, pos := 0, env := e₁ }
        { fn, label := 9, pos := 0, env := e₂ }
  | b10 {e₁ e₂ : Lir.Env} :
      DecFrameRel fn { fn, label := 10, pos := 0, env := e₁ }
        { fn, label := 10, pos := 0, env := e₂ }

inductive StackRel (l : Layout) : List Lir.Frame → List Lir.Frame → Prop
  | other {stack : List Lir.Frame} (hno : ∀ fr ∈ stack, fr.fn ≠ l.decProc) :
      StackRel l stack stack
  | decTop {fr₁ fr₂ : Lir.Frame} {rest : List Lir.Frame}
      (hd : DecFrameRel l.decProc fr₁ fr₂)
      (hno : ∀ fr ∈ rest, fr.fn ≠ l.decProc) :
      StackRel l (fr₁ :: rest) (fr₂ :: rest)

def StateRel (l : Layout) (s₁ s₂ : Lir.State) : Prop :=
  s₁.mem = s₂.mem ∧ s₁.ctx = s₂.ctx ∧ StackRel l s₁.stack s₂.stack

/-! ## Step matching relation and helpers -/

inductive MatchedStep (l : Layout) (p : Lir.Program) (s₁ s₂ : Lir.State) : Prop
  | rawStuck : Lir.step p s₁ = .stuck → MatchedStep l p s₁ s₂
  | rawStuckWithin {c₁ : Nat} : c₁ ≤ 3 →
      Sem.Reaches (Lir.semStep p) s₁ c₁ .stuck →
      MatchedStep l p s₁ s₂
  | sameFinal {r : Sem.Result (List Lir.Word × X86.Memory)} :
      Sem.Final (Lir.semStep p s₁) r → Sem.Final (Lir.semStep (install l p) s₂) r →
      MatchedStep l p s₁ s₂
  | sync {s₁' s₂' s₁'' s₂'' : Lir.State} {b₁ b₂ : Bool} {c₁ c₂ : Nat} :
      Lir.semStep p s₁ = .next s₁' b₁ → Sem.Star (Lir.semStep p) s₁' c₁ s₁'' →
      Lir.semStep (install l p) s₂ = .next s₂' b₂ → Sem.Star (Lir.semStep (install l p)) s₂' c₂ s₂'' →
      b₁.toNat + c₁ ≤ b₂.toNat + c₂ + 3 →
      StateRel l s₁'' s₂'' →
      MatchedStep l p s₁ s₂

private theorem star_free {p : Lir.Program} {s s' s'' : Lir.State} {c : Nat}
    (h1 : Lir.step p s = .next s' false) (h2 : Sem.Star (Lir.semStep p) s' c s'') :
    Sem.Star (Lir.semStep p) s c s'' :=
  .free (Lir.semStep_next.mpr h1) h2

private theorem star_charge {p : Lir.Program} {s s' s'' : Lir.State} {c : Nat}
    (h1 : Lir.step p s = .next s' true) (h2 : Sem.Star (Lir.semStep p) s' c s'') :
    Sem.Star (Lir.semStep p) s (c + 1) s'' :=
  .charge (Lir.semStep_next.mpr h1) h2

private theorem star_reaches_stuck {p : Lir.Program} {s s' : Lir.State} {c : Nat}
    (hstar : Sem.Star (Lir.semStep p) s c s') (hst : Lir.step p s' = .stuck) :
    Sem.Reaches (Lir.semStep p) s c .stuck := by
  have := Inline.reaches_of_star_reaches hstar (.final (k := 0) (by rw [Lir.semStep, hst]; exact .stuck))
  simpa using this

private theorem enter_dec_or_other (l : Layout) (p : Lir.Program)
    (hdec : p.funcs[l.decProc]? = some Rt.Rc.Gen.dec)
    {g : Lir.FunId} {vs : List Lir.Word} {rest : List Lir.Frame}
    (hno : ∀ fr ∈ rest, fr.fn ≠ l.decProc) :
    (∀ fr₁, Lir.enter p g vs = some fr₁ →
      ∃ fr₂, Lir.enter (install l p) g vs = some fr₂ ∧ StackRel l (fr₁ :: rest) (fr₂ :: rest)) ∧
    (Lir.enter p g vs = none ↔ Lir.enter (install l p) g vs = none) := by
  by_cases hg : g = l.decProc
  · subst hg
    have h2 := install_get_dec l p hdec
    simp only [Lir.enter, hdec, h2, Option.bind_eq_bind, Option.bind_some, Rt.Rc.Gen.dec, fastDec]
    cases vs with
    | nil => simp [Lir.bindParams]
    | cons w restVs =>
      cases restVs with
      | nil =>
        simp only [Lir.bindParams, Option.bind_some, Option.some.injEq, forall_eq']
        exact ⟨⟨_, rfl, .decTop (.b0 (w := w) (by simp) (by simp)) hno⟩, by simp⟩
      | cons _ _ => simp [Lir.bindParams]
  · have hget := install_get_ne l p hg
    simp only [Lir.enter, hget]
    cases p.funcs[g]? with
    | none => simp
    | some F =>
      simp only [Option.bind_eq_bind, Option.bind_some]
      cases Lir.bindParams {} F.params vs with
      | none => simp
      | some ρ =>
        simp only [Option.bind_some, Option.some.injEq, forall_eq']
        refine ⟨⟨_, rfl, .other fun fr hmem => ?_⟩, by simp⟩
        rcases List.mem_cons.mp hmem with rfl | hmem'
        · exact hg
        · exact hno fr hmem'

/-! ## Non-`decProc` frame step preservation -/

private theorem step_match_other {l : Layout} {p : Lir.Program}
    (hdec : p.funcs[l.decProc]? = some Rt.Rc.Gen.dec)
    {mem : X86.Memory} {ctx : Lir.Word} {stack : List Lir.Frame}
    (hno : ∀ fr ∈ stack, fr.fn ≠ l.decProc) :
    MatchedStep l p { mem, ctx, stack } { mem, ctx, stack } := by
  cases stack with
  | nil => exact .rawStuck (by unfold Lir.step; rfl)
  | cons fr rest =>
    have hne : fr.fn ≠ l.decProc := hno fr (List.mem_cons_self ..)
    have hnoRest : ∀ f ∈ rest, f.fn ≠ l.decProc := fun f hf => hno f (List.mem_cons_of_mem _ hf)
    have hFget : (install l p).funcs[fr.fn]? = p.funcs[fr.fn]? := install_get_ne l p hne
    cases hF : p.funcs[fr.fn]? with
    | none => exact .rawStuck (by unfold Lir.step; simp [hF])
    | some F =>
      have hF' : (install l p).funcs[fr.fn]? = some F := by rw [hFget, hF]
      cases hB : F.blocks[fr.label]? with
      | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB])
      | some B =>
        by_cases hpos : fr.pos < B.body.size
        · cases hs : B.body[fr.pos] with
          | assign x r =>
            cases hex : Lir.Stmt.exec fr.env mem ctx (.assign x r) with
            | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos, hs, hex])
            | some pr =>
              have h1 : Lir.step p { mem, ctx, stack := fr :: rest } =
                  .next { mem := pr.2, ctx, stack := { fr with pos := fr.pos + 1, env := pr.1 } :: rest } false := by
                unfold Lir.step; simp [hF, hB, hpos, hs, hex]
              have h2 : Lir.step (install l p) { mem, ctx, stack := fr :: rest } =
                  .next { mem := pr.2, ctx, stack := { fr with pos := fr.pos + 1, env := pr.1 } :: rest } false := by
                unfold Lir.step; simp [hF', hB, hpos, hs, hex]
              exact .sync (Lir.semStep_next.mpr h1) (.refl _) (Lir.semStep_next.mpr h2) (.refl _) (by omega)
                ⟨rfl, rfl, .other (by intro f hf; rcases List.mem_cons.mp hf with rfl | hf'; exact hne; exact hnoRest f hf')⟩
          | limb r1 r2 op =>
            cases hex : Lir.Stmt.exec fr.env mem ctx (.limb r1 r2 op) with
            | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos, hs, hex])
            | some pr =>
              have h1 : Lir.step p { mem, ctx, stack := fr :: rest } =
                  .next { mem := pr.2, ctx, stack := { fr with pos := fr.pos + 1, env := pr.1 } :: rest } false := by
                unfold Lir.step; simp [hF, hB, hpos, hs, hex]
              have h2 : Lir.step (install l p) { mem, ctx, stack := fr :: rest } =
                  .next { mem := pr.2, ctx, stack := { fr with pos := fr.pos + 1, env := pr.1 } :: rest } false := by
                unfold Lir.step; simp [hF', hB, hpos, hs, hex]
              exact .sync (Lir.semStep_next.mpr h1) (.refl _) (Lir.semStep_next.mpr h2) (.refl _) (by omega)
                ⟨rfl, rfl, .other (by intro f hf; rcases List.mem_cons.mp hf with rfl | hf'; exact hne; exact hnoRest f hf')⟩
          | store w m a =>
            cases hex : Lir.Stmt.exec fr.env mem ctx (.store w m a) with
            | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos, hs, hex])
            | some pr =>
              have h1 : Lir.step p { mem, ctx, stack := fr :: rest } =
                  .next { mem := pr.2, ctx, stack := { fr with pos := fr.pos + 1, env := pr.1 } :: rest } false := by
                unfold Lir.step; simp [hF, hB, hpos, hs, hex]
              have h2 : Lir.step (install l p) { mem, ctx, stack := fr :: rest } =
                  .next { mem := pr.2, ctx, stack := { fr with pos := fr.pos + 1, env := pr.1 } :: rest } false := by
                unfold Lir.step; simp [hF', hB, hpos, hs, hex]
              exact .sync (Lir.semStep_next.mpr h1) (.refl _) (Lir.semStep_next.mpr h2) (.refl _) (by omega)
                ⟨rfl, rfl, .other (by intro f hf; rcases List.mem_cons.mp hf with rfl | hf'; exact hne; exact hnoRest f hf')⟩
          | call rs g as =>
            cases hargs : Lir.evalArgs fr.env as with
            | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos, hs, hargs])
            | some vs =>
              cases hent : Lir.enter p g vs with
              | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos, hs, hargs, hent])
              | some callee₁ =>
                have hnoCaller : ∀ f ∈ { fr with pos := fr.pos + 1, dsts := rs } :: rest, f.fn ≠ l.decProc := by
                  intro f hf; rcases List.mem_cons.mp hf with rfl | hf'; exact hne; exact hnoRest f hf'
                obtain ⟨callee₂, hent₂, hst⟩ := (enter_dec_or_other l p hdec hnoCaller).1 callee₁ hent
                have h1 : Lir.step p { mem, ctx, stack := fr :: rest } =
                    .next { mem, ctx, stack := callee₁ :: { fr with pos := fr.pos + 1, dsts := rs } :: rest } true := by
                  unfold Lir.step; simp [hF, hB, hpos, hs, hargs, hent]
                have h2 : Lir.step (install l p) { mem, ctx, stack := fr :: rest } =
                    .next { mem, ctx, stack := callee₂ :: { fr with pos := fr.pos + 1, dsts := rs } :: rest } true := by
                  unfold Lir.step; simp [hF', hB, hpos, hs, hargs, hent₂]
                exact .sync (Lir.semStep_next.mpr h1) (.refl _) (Lir.semStep_next.mpr h2) (.refl _) (by omega)
                  ⟨rfl, rfl, hst⟩
        · have matchEdge : ∀ (ρ : Lir.Env) (e : Lir.Edge),
              Lir.step p { mem, ctx, stack := fr :: rest } = Lir.takeEdge F { mem, ctx, stack := fr :: rest } fr rest ρ e →
              Lir.step (install l p) { mem, ctx, stack := fr :: rest } = Lir.takeEdge F { mem, ctx, stack := fr :: rest } fr rest ρ e →
              MatchedStep l p { mem, ctx, stack := fr :: rest } { mem, ctx, stack := fr :: rest } := by
            intro ρ e h1 h2
            unfold Lir.takeEdge at h1 h2
            cases ha : Lir.evalArgs ρ e.args with
            | none => exact .rawStuck (by rw [h1]; simp [ha])
            | some vals =>
              cases htb : F.blocks[e.target]? with
              | none => exact .rawStuck (by rw [h1]; simp [ha, htb])
              | some target =>
                cases hbp : Lir.bindParams ρ target.params vals with
                | none => exact .rawStuck (by rw [h1]; simp [ha, htb, hbp])
                | some ρ' =>
                  have h1' : Lir.step p { mem, ctx, stack := fr :: rest } =
                      .next { mem, ctx, stack := { fr with label := e.target, pos := 0, env := ρ' } :: rest }
                        (decide (e.target ≤ fr.label)) := by
                    rw [h1]; simp [ha, htb, hbp]
                  have h2' : Lir.step (install l p) { mem, ctx, stack := fr :: rest } =
                      .next { mem, ctx, stack := { fr with label := e.target, pos := 0, env := ρ' } :: rest }
                        (decide (e.target ≤ fr.label)) := by
                    rw [h2]; simp [ha, htb, hbp]
                  exact .sync (Lir.semStep_next.mpr h1') (.refl _) (Lir.semStep_next.mpr h2') (.refl _) (by omega)
                    ⟨rfl, rfl, .other (by intro f hf; rcases List.mem_cons.mp hf with rfl | hf'; exact hne; exact hnoRest f hf')⟩
          cases ht : B.term with
          | jump e =>
            exact matchEdge fr.env e
              (by unfold Lir.step; simp [hF, hB, hpos, ht])
              (by unfold Lir.step; simp [hF', hB, hpos, ht])
          | br cond w a b' t f =>
            cases ha : a.eval fr.env with
            | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos, ht, ha])
            | some va =>
              cases hb : b'.eval fr.env with
              | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos, ht, ha, hb])
              | some vb =>
                cases hc : cond.holds w va vb with
                | true =>
                  exact matchEdge fr.env t
                    (by unfold Lir.step; simp [hF, hB, hpos, ht, ha, hb, hc])
                    (by unfold Lir.step; simp [hF', hB, hpos, ht, ha, hb, hc])
                | false =>
                  exact matchEdge fr.env f
                    (by unfold Lir.step; simp [hF, hB, hpos, ht, ha, hb, hc])
                    (by unfold Lir.step; simp [hF', hB, hpos, ht, ha, hb, hc])
          | brOvf op x a b' ok ovf =>
            cases ha : a.eval fr.env with
            | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos, ht, ha])
            | some va =>
              cases hb : b'.eval fr.env with
              | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos, ht, ha, hb])
              | some vb =>
                let res := op.eval va vb
                let ρ₁ := fr.env.insert x res.1
                cases hc : res.2 with
                | true =>
                  exact matchEdge ρ₁ ovf
                    (by unfold Lir.step; simp [hF, hB, hpos, ht, ha, hb, res, ρ₁, hc])
                    (by unfold Lir.step; simp [hF', hB, hpos, ht, ha, hb, res, ρ₁, hc])
                | false =>
                  exact matchEdge ρ₁ ok
                    (by unfold Lir.step; simp [hF, hB, hpos, ht, ha, hb, res, ρ₁, hc])
                    (by unfold Lir.step; simp [hF', hB, hpos, ht, ha, hb, res, ρ₁, hc])
          | ret as =>
            cases hargs : Lir.evalArgs fr.env as with
            | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos, ht, hargs])
            | some vals =>
              cases rest with
              | nil =>
                exact .sameFinal (r := .ok (vals, mem))
                  (by rw [Lir.semStep]; unfold Lir.step; simp [hF, hB, hpos, ht, hargs]; exact .done)
                  (by rw [Lir.semStep]; unfold Lir.step; simp [hF', hB, hpos, ht, hargs]; exact .done)
              | cons caller tail =>
                cases hbp : Lir.bindParams caller.env caller.dsts vals with
                | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos, ht, hargs, hbp])
                | some ρ' =>
                  have h1 : Lir.step p { mem, ctx, stack := fr :: caller :: tail } =
                      .next { mem, ctx, stack := { caller with env := ρ', dsts := [] } :: tail } false := by
                    unfold Lir.step; simp [hF, hB, hpos, ht, hargs, hbp]
                  have h2 : Lir.step (install l p) { mem, ctx, stack := fr :: caller :: tail } =
                      .next { mem, ctx, stack := { caller with env := ρ', dsts := [] } :: tail } false := by
                    unfold Lir.step; simp [hF', hB, hpos, ht, hargs, hbp]
                  exact .sync (Lir.semStep_next.mpr h1) (.refl _) (Lir.semStep_next.mpr h2) (.refl _) (by omega)
                    ⟨rfl, rfl, .other (by
                      intro g hg; rcases List.mem_cons.mp hg with rfl | hg'
                      · exact hnoRest caller (List.mem_cons_self ..)
                      · exact hnoRest g (List.mem_cons_of_mem _ hg'))⟩
          | tail g as =>
            cases hargs : Lir.evalArgs fr.env as with
            | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos, ht, hargs])
            | some vs =>
              cases hent : Lir.enter p g vs with
              | none => exact .rawStuck (by unfold Lir.step; simp [hF, hB, hpos, ht, hargs, hent])
              | some callee₁ =>
                obtain ⟨callee₂, hent₂, hst⟩ := (enter_dec_or_other l p hdec hnoRest).1 callee₁ hent
                have h1 : Lir.step p { mem, ctx, stack := fr :: rest } =
                    .next { mem, ctx, stack := callee₁ :: rest } true := by
                  unfold Lir.step; simp [hF, hB, hpos, ht, hargs, hent]
                have h2 : Lir.step (install l p) { mem, ctx, stack := fr :: rest } =
                    .next { mem, ctx, stack := callee₂ :: rest } true := by
                  unfold Lir.step; simp [hF', hB, hpos, ht, hargs, hent₂]
                exact .sync (Lir.semStep_next.mpr h1) (.refl _) (Lir.semStep_next.mpr h2) (.refl _) (by omega)
                  ⟨rfl, rfl, hst⟩
          | fail r =>
            exact .sameFinal (r := .resource r)
              (by rw [Lir.semStep]; unfold Lir.step; simp [hF, hB, hpos, ht]; exact .fail)
              (by rw [Lir.semStep]; unfold Lir.step; simp [hF', hB, hpos, ht]; exact .fail)
          | trap =>
            exact .sameFinal (r := .trap)
              (by rw [Lir.semStep]; unfold Lir.step; simp [hF, hB, hpos, ht]; exact .trap)
              (by rw [Lir.semStep]; unfold Lir.step; simp [hF', hB, hpos, ht]; exact .trap)

/-! ## `decProc` block execution helpers -/

private theorem exec_gen_b9 {p : Lir.Program} {fn : Lir.FunId}
    (hdec : p.funcs[fn]? = some Rt.Rc.Gen.dec)
    {mem : X86.Memory} {ctx par : Lir.Word} {e : Lir.Env} {rest : List Lir.Frame}
    (h8 : e[8]? = some par)
    {cls : Lir.Word} (hcls : mem.read? .w8 (par + 1) = .ok cls)
    {pred : Lir.Word} (hpred : mem.read? .w64 (par + 8) = .ok pred)
    {old : Lir.Word} (hold : mem.read? .w64 (ctx + cls * 8) = .ok old)
    {mem1 mem2 : X86.Memory}
    (hw1 : mem.write? .w64 par old = .ok mem1)
    (hw2 : mem1.write? .w64 (ctx + cls * 8) par = .ok mem2) :
    Sem.Star (Lir.semStep p)
      { mem, ctx, stack := { fn, label := 9, pos := 0, env := e } :: rest } 1
      { mem := mem2, ctx, stack := { fn, label := 6, pos := 0, env := (((e.insert 11 cls).insert 15 pred).insert 16 old).insert 8 pred } :: rest } := by
  have hs0 : Lir.step p { mem, ctx, stack := { fn, label := 9, pos := 0, env := e } :: rest } =
      .next { mem, ctx, stack := { fn, label := 9, pos := 1, env := e.insert 11 cls } :: rest } false := by
    unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord,
      Lir.Addr.eval, cellAddr, h8, Lir.dispWord, hcls]
  have hs1 : Lir.step p { mem, ctx, stack := { fn, label := 9, pos := 1, env := e.insert 11 cls } :: rest } =
      .next { mem, ctx, stack := { fn, label := 9, pos := 2, env := (e.insert 11 cls).insert 15 pred } :: rest } false := by
    unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord,
      Lir.Addr.eval, cellAddr, h8, Lir.dispWord, hpred]
  have hs2 : Lir.step p { mem, ctx, stack := { fn, label := 9, pos := 2, env := (e.insert 11 cls).insert 15 pred } :: rest } =
      .next { mem, ctx, stack := { fn, label := 9, pos := 3, env := ((e.insert 11 cls).insert 15 pred).insert 16 old } :: rest } false := by
    unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord,
      Lir.Addr.eval, X86.Scale.word, Lir.dispWord, hold]
  have hs3 : Lir.step p { mem, ctx, stack := { fn, label := 9, pos := 3, env := ((e.insert 11 cls).insert 15 pred).insert 16 old } :: rest } =
      .next { mem := mem1, ctx, stack := { fn, label := 9, pos := 4, env := ((e.insert 11 cls).insert 15 pred).insert 16 old } :: rest } false := by
    unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, Lir.Stmt.exec, Lir.Arg.eval,
      Lir.Addr.eval, cellAddr, h8, Lir.dispWord, hw1]
  have hs4 : Lir.step p { mem := mem1, ctx, stack := { fn, label := 9, pos := 4, env := ((e.insert 11 cls).insert 15 pred).insert 16 old } :: rest } =
      .next { mem := mem2, ctx, stack := { fn, label := 9, pos := 5, env := ((e.insert 11 cls).insert 15 pred).insert 16 old } :: rest } false := by
    unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, Lir.Stmt.exec, Lir.Arg.eval,
      Lir.Addr.eval, X86.Scale.word, Lir.dispWord, h8, hw2]
  have hs5 : Lir.step p { mem := mem2, ctx, stack := { fn, label := 9, pos := 5, env := ((e.insert 11 cls).insert 15 pred).insert 16 old } :: rest } =
      .next { mem := mem2, ctx, stack := { fn, label := 6, pos := 0, env := (((e.insert 11 cls).insert 15 pred).insert 16 old).insert 8 pred } :: rest } true := by
    unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, Lir.takeEdge, to, v, Lir.evalArgs, Lir.Arg.eval, Lir.bindParams]
  exact star_free hs0 (star_free hs1 (star_free hs2 (star_free hs3 (star_free hs4 (star_charge hs5 (.refl _))))))

private theorem exec_fast_b9 {q : Lir.Program} {fn : Lir.FunId}
    (hfast : q.funcs[fn]? = some fastDec)
    {mem : X86.Memory} {ctx par : Lir.Word} {e : Lir.Env} {rest : List Lir.Frame}
    (h8 : e[8]? = some par)
    {cls : Lir.Word} (hcls : mem.read? .w8 (par + 1) = .ok cls)
    {pred : Lir.Word} (hpred : mem.read? .w64 (par + 8) = .ok pred)
    {old : Lir.Word} (hold : mem.read? .w64 (ctx + cls * 8) = .ok old)
    {mem1 mem2 : X86.Memory}
    (hw1 : mem.write? .w64 par old = .ok mem1)
    (hw2 : mem1.write? .w64 (ctx + cls * 8) par = .ok mem2) :
    Lir.semStep q { mem, ctx, stack := { fn, label := 9, pos := 0, env := e } :: rest } =
      .next { mem, ctx, stack := { fn, label := 9, pos := 1, env := e.insert 11 cls } :: rest } false ∧
    Sem.Star (Lir.semStep q)
      { mem, ctx, stack := { fn, label := 9, pos := 1, env := e.insert 11 cls } :: rest } 1
      { mem := mem2, ctx, stack := { fn, label := 6, pos := 0, env := (((e.insert 11 cls).insert 15 pred).insert 16 old).insert 8 pred } :: rest } := by
  have hs0 : Lir.step q { mem, ctx, stack := { fn, label := 9, pos := 0, env := e } :: rest } =
      .next { mem, ctx, stack := { fn, label := 9, pos := 1, env := e.insert 11 cls } :: rest } false := by
    unfold Lir.step; simp [hfast, fastDec, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord,
      Lir.Addr.eval, cellAddr, h8, Lir.dispWord, hcls]
  have hs1 : Lir.step q { mem, ctx, stack := { fn, label := 9, pos := 1, env := e.insert 11 cls } :: rest } =
      .next { mem, ctx, stack := { fn, label := 9, pos := 2, env := (e.insert 11 cls).insert 15 pred } :: rest } false := by
    unfold Lir.step; simp [hfast, fastDec, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord,
      Lir.Addr.eval, cellAddr, h8, Lir.dispWord, hpred]
  have hs2 : Lir.step q { mem, ctx, stack := { fn, label := 9, pos := 2, env := (e.insert 11 cls).insert 15 pred } :: rest } =
      .next { mem, ctx, stack := { fn, label := 9, pos := 3, env := ((e.insert 11 cls).insert 15 pred).insert 16 old } :: rest } false := by
    unfold Lir.step; simp [hfast, fastDec, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord,
      Lir.Addr.eval, X86.Scale.word, Lir.dispWord, hold]
  have hs3 : Lir.step q { mem, ctx, stack := { fn, label := 9, pos := 3, env := ((e.insert 11 cls).insert 15 pred).insert 16 old } :: rest } =
      .next { mem := mem1, ctx, stack := { fn, label := 9, pos := 4, env := ((e.insert 11 cls).insert 15 pred).insert 16 old } :: rest } false := by
    unfold Lir.step; simp [hfast, fastDec, Lir.Stmt.exec, Lir.Arg.eval,
      Lir.Addr.eval, cellAddr, h8, Lir.dispWord, hw1]
  have hs4 : Lir.step q { mem := mem1, ctx, stack := { fn, label := 9, pos := 4, env := ((e.insert 11 cls).insert 15 pred).insert 16 old } :: rest } =
      .next { mem := mem2, ctx, stack := { fn, label := 9, pos := 5, env := ((e.insert 11 cls).insert 15 pred).insert 16 old } :: rest } false := by
    unfold Lir.step; simp [hfast, fastDec, Lir.Stmt.exec, Lir.Arg.eval,
      Lir.Addr.eval, X86.Scale.word, Lir.dispWord, h8, hw2]
  have hs5 : Lir.step q { mem := mem2, ctx, stack := { fn, label := 9, pos := 5, env := ((e.insert 11 cls).insert 15 pred).insert 16 old } :: rest } =
      .next { mem := mem2, ctx, stack := { fn, label := 6, pos := 0, env := (((e.insert 11 cls).insert 15 pred).insert 16 old).insert 8 pred } :: rest } true := by
    unfold Lir.step; simp [hfast, fastDec, Lir.takeEdge, to, v, Lir.evalArgs, Lir.Arg.eval, Lir.bindParams]
  exact ⟨Lir.semStep_next.mpr hs0, star_free hs1 (star_free hs2 (star_free hs3 (star_free hs4 (star_charge hs5 (.refl _)))))⟩

private theorem exec_gen_b9_stuck_or_ok {p : Lir.Program} {fn : Lir.FunId}
    (hdec : p.funcs[fn]? = some Rt.Rc.Gen.dec)
    {mem : X86.Memory} {ctx par : Lir.Word} {e : Lir.Env} {rest : List Lir.Frame}
    (h8 : e[8]? = some par) :
    Sem.Reaches (Lir.semStep p) { mem, ctx, stack := { fn, label := 9, pos := 0, env := e } :: rest } 0 .stuck ∨
    ∃ cls pred old mem1 mem2,
      mem.read? .w8 (par + 1) = .ok cls ∧
      mem.read? .w64 (par + 8) = .ok pred ∧
      mem.read? .w64 (ctx + cls * 8) = .ok old ∧
      mem.write? .w64 par old = .ok mem1 ∧
      mem1.write? .w64 (ctx + cls * 8) par = .ok mem2 := by
  cases hcls : mem.read? .w8 (par + 1) with
  | error _ =>
    exact .inl (.final (by rw [Lir.semStep]; unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, cellAddr, h8, Lir.dispWord, hcls]; exact .stuck))
  | ok cls =>
    have hs0 : Lir.step p { mem, ctx, stack := { fn, label := 9, pos := 0, env := e } :: rest } =
        .next { mem, ctx, stack := { fn, label := 9, pos := 1, env := e.insert 11 cls } :: rest } false := by
      unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, cellAddr, h8, Lir.dispWord, hcls]
    cases hpred : mem.read? .w64 (par + 8) with
    | error _ =>
      exact .inl (star_reaches_stuck (star_free hs0 (.refl _)) (by unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, cellAddr, h8, Lir.dispWord, hpred]))
    | ok pred =>
      have hs1 : Lir.step p { mem, ctx, stack := { fn, label := 9, pos := 1, env := e.insert 11 cls } :: rest } =
          .next { mem, ctx, stack := { fn, label := 9, pos := 2, env := (e.insert 11 cls).insert 15 pred } :: rest } false := by
        unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, cellAddr, h8, Lir.dispWord, hpred]
      cases hold : mem.read? .w64 (ctx + cls * 8) with
      | error _ =>
        exact .inl (star_reaches_stuck (star_free hs0 (star_free hs1 (.refl _))) (by unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, X86.Scale.word, Lir.dispWord, hold]))
      | ok old =>
        have hs2 : Lir.step p { mem, ctx, stack := { fn, label := 9, pos := 2, env := (e.insert 11 cls).insert 15 pred } :: rest } =
            .next { mem, ctx, stack := { fn, label := 9, pos := 3, env := ((e.insert 11 cls).insert 15 pred).insert 16 old } :: rest } false := by
          unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, X86.Scale.word, Lir.dispWord, hold]
        cases hw1 : mem.write? .w64 par old with
        | error _ =>
          exact .inl (star_reaches_stuck (star_free hs0 (star_free hs1 (star_free hs2 (.refl _)))) (by unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, Lir.Stmt.exec, Lir.Arg.eval, Lir.Addr.eval, cellAddr, h8, Lir.dispWord, hw1]))
        | ok mem1 =>
          have hs3 : Lir.step p { mem, ctx, stack := { fn, label := 9, pos := 3, env := ((e.insert 11 cls).insert 15 pred).insert 16 old } :: rest } =
              .next { mem := mem1, ctx, stack := { fn, label := 9, pos := 4, env := ((e.insert 11 cls).insert 15 pred).insert 16 old } :: rest } false := by
            unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, Lir.Stmt.exec, Lir.Arg.eval, Lir.Addr.eval, cellAddr, h8, Lir.dispWord, hw1]
          cases hw2 : mem1.write? .w64 (ctx + cls * 8) par with
          | error _ =>
            exact .inl (star_reaches_stuck (star_free hs0 (star_free hs1 (star_free hs2 (star_free hs3 (.refl _))))) (by unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, Lir.Stmt.exec, Lir.Arg.eval, Lir.Addr.eval, X86.Scale.word, Lir.dispWord, h8, hw2]))
          | ok mem2 =>
            exact .inr ⟨cls, pred, old, mem1, mem2, rfl, rfl, hold, hw1, hw2⟩

/-! ## `decProc` step matching across the 6 synchronization points -/

private theorem step_match_dec {l : Layout} {p : Lir.Program}
    (hdec : p.funcs[l.decProc]? = some Rt.Rc.Gen.dec)
    {mem : X86.Memory} {ctx : Lir.Word} {fr₁ fr₂ : Lir.Frame} {rest : List Lir.Frame}
    (hd : DecFrameRel l.decProc fr₁ fr₂)
    (hno : ∀ fr ∈ rest, fr.fn ≠ l.decProc) :
    MatchedStep l p { mem, ctx, stack := fr₁ :: rest } { mem, ctx, stack := fr₂ :: rest } := by
  have hfast : (install l p).funcs[l.decProc]? = some fastDec := install_get_dec l p hdec
  cases hd with
  | @b0 e₁ e₂ w h0₁ h0₂ =>
    have hs1 : Lir.step p { mem, ctx, stack := { fn := l.decProc, label := 0, pos := 0, env := e₁ } :: rest } =
        .next { mem, ctx, stack := { fn := l.decProc, label := 1, pos := 0, env := (e₁.insert 1 w).insert 2 0 } :: rest } false := by
      unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.Arg.eval, h0₁, Lir.bindParams]
    have hs2 : Lir.step (install l p) { mem, ctx, stack := { fn := l.decProc, label := 0, pos := 0, env := e₂ } :: rest } =
        .next { mem, ctx, stack := { fn := l.decProc, label := 1, pos := 0, env := (e₂.insert 1 w).insert 2 0 } :: rest } false := by
      unfold Lir.step; simp [hfast, fastDec, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.Arg.eval, h0₂, Lir.bindParams]
    exact .sync (Lir.semStep_next.mpr hs1) (.refl _) (Lir.semStep_next.mpr hs2) (.refl _) (by omega)
      ⟨rfl, rfl, .decTop (.b1 (cur := w) (par := 0) (by simp) (by simp) (by simp) (by simp)) hno⟩
  | @b1 e₁ e₂ cur par h1₁ h2₁ h1₂ h2₂ =>
    by_cases hodd : (cur &&& 1) != 0
    · have hs1 : Lir.step p { mem, ctx, stack := { fn := l.decProc, label := 1, pos := 0, env := e₁ } :: rest } =
          .next { mem, ctx, stack := { fn := l.decProc, label := 6, pos := 0, env := e₁.insert 8 par } :: rest } false := by
        unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, Lir.Arg.eval, h1₁, h2₁, w64_tnz_1, hodd, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.bindParams]
      have hs2 : Lir.step (install l p) { mem, ctx, stack := { fn := l.decProc, label := 1, pos := 0, env := e₂ } :: rest } =
          .next { mem, ctx, stack := { fn := l.decProc, label := 6, pos := 0, env := e₂.insert 8 par } :: rest } false := by
        unfold Lir.step; simp [hfast, fastDec, Lir.Arg.eval, h1₂, h2₂, w64_tnz_1, hodd, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.bindParams]
      exact .sync (Lir.semStep_next.mpr hs1) (.refl _) (Lir.semStep_next.mpr hs2) (.refl _) (by omega)
        ⟨rfl, rfl, .decTop (.b6 (par := par) (by simp) (by simp)) hno⟩
    · have hev : ((cur &&& 1) != 0) = false := Bool.eq_false_iff.mpr hodd
      have hs1 : Lir.step p { mem, ctx, stack := { fn := l.decProc, label := 1, pos := 0, env := e₁ } :: rest } =
          .next { mem, ctx, stack := { fn := l.decProc, label := 2, pos := 0, env := e₁ } :: rest } false := by
        unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, Lir.Arg.eval, h1₁, w64_tnz_1, hev, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.bindParams]
      have hs2 : Lir.step (install l p) { mem, ctx, stack := { fn := l.decProc, label := 1, pos := 0, env := e₂ } :: rest } =
          .next { mem, ctx, stack := { fn := l.decProc, label := 2, pos := 0, env := (e₂.insert 20 cur).insert 21 par } :: rest } false := by
        unfold Lir.step; simp [hfast, fastDec, Lir.Arg.eval, h1₂, h2₂, w64_tnz_1, hev, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.bindParams]
      exact .sync (Lir.semStep_next.mpr hs1) (.refl _) (Lir.semStep_next.mpr hs2) (.refl _) (by omega)
        ⟨rfl, rfl, .decTop (.b2 (cur := cur) (par := par) h1₁ h2₁ (by simp) (by simp)) hno⟩
  | @b6 e₁ e₂ par h8₁ h8₂ =>
    by_cases hz : par = 0
    · subst hz
      have h1_6 : Lir.step p { mem, ctx, stack := { fn := l.decProc, label := 6, pos := 0, env := e₁ } :: rest } =
          .next { mem, ctx, stack := { fn := l.decProc, label := 10, pos := 0, env := e₁ } :: rest } false := by
        unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, Lir.Arg.eval, h8₁, w64_eq_iff, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.bindParams]
      have h2_6 : Lir.step (install l p) { mem, ctx, stack := { fn := l.decProc, label := 6, pos := 0, env := e₂ } :: rest } =
          .next { mem, ctx, stack := { fn := l.decProc, label := 10, pos := 0, env := e₂ } :: rest } false := by
        unfold Lir.step; simp [hfast, fastDec, Lir.Arg.eval, h8₂, w64_eq_iff, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.bindParams]
      exact .sync (Lir.semStep_next.mpr h1_6) (.refl _) (Lir.semStep_next.mpr h2_6) (.refl _) (by omega)
        ⟨rfl, rfl, .decTop .b10 hno⟩
    · have hne0 : (par == 0) = false := beq_false_of_ne hz
      have h1_6 : Lir.step p { mem, ctx, stack := { fn := l.decProc, label := 6, pos := 0, env := e₁ } :: rest } =
          .next { mem, ctx, stack := { fn := l.decProc, label := 7, pos := 0, env := e₁ } :: rest } false := by
        unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, Lir.Arg.eval, h8₁, w64_eq_iff, hne0, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.bindParams]
      have h2_6 : Lir.step (install l p) { mem, ctx, stack := { fn := l.decProc, label := 6, pos := 0, env := e₂ } :: rest } =
          .next { mem, ctx, stack := { fn := l.decProc, label := 7, pos := 0, env := e₂ } :: rest } false := by
        unfold Lir.step; simp [hfast, fastDec, Lir.Arg.eval, h8₂, w64_eq_iff, hne0, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.bindParams]
      exact .sync (Lir.semStep_next.mpr h1_6) (.refl _) (Lir.semStep_next.mpr h2_6) (.refl _) (by omega)
        ⟨rfl, rfl, .decTop (.b7 h8₁ h8₂ hz) hno⟩
  | @b10 e₁ e₂ =>
    cases rest with
    | nil =>
      exact .sameFinal (r := .ok ([], mem))
        (by rw [Lir.semStep]; unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, Lir.evalArgs]; exact .done)
        (by rw [Lir.semStep]; unfold Lir.step; simp [hfast, fastDec, Lir.evalArgs]; exact .done)
    | cons caller tail =>
      cases hbp : Lir.bindParams caller.env caller.dsts [] with
      | none =>
        exact .rawStuck (by unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, Lir.evalArgs, hbp])
      | some ρ' =>
        have h1_10 : Lir.step p { mem, ctx, stack := { fn := l.decProc, label := 10, pos := 0, env := e₁ } :: caller :: tail } =
            .next { mem, ctx, stack := { caller with env := ρ', dsts := [] } :: tail } false := by
          unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, Lir.evalArgs, hbp]
        have h2_10 : Lir.step (install l p) { mem, ctx, stack := { fn := l.decProc, label := 10, pos := 0, env := e₂ } :: caller :: tail } =
            .next { mem, ctx, stack := { caller with env := ρ', dsts := [] } :: tail } false := by
          unfold Lir.step; simp [hfast, fastDec, Lir.evalArgs, hbp]
        exact .sync (Lir.semStep_next.mpr h1_10) (.refl _) (Lir.semStep_next.mpr h2_10) (.refl _) (by omega)
          ⟨rfl, rfl, .other (by
            intro g hg; rcases List.mem_cons.mp hg with rfl | hg'
            · exact hno caller (List.mem_cons_self ..)
            · exact hno g (List.mem_cons_of_mem _ hg'))⟩
  | @b9 e₁ e₂ par h8₁ h8₂ =>
    rcases exec_gen_b9_stuck_or_ok hdec h8₁ with hstk | ⟨cls, pred, old, mem1, mem2, hcls, hpred, hold, hw1, hw2⟩
    · exact .rawStuckWithin (by omega) hstk
    · have hstar1 := exec_gen_b9 (rest := rest) hdec h8₁ hcls hpred hold hw1 hw2
      obtain ⟨hs2, hstar2⟩ := exec_fast_b9 (rest := rest) hfast h8₂ hcls hpred hold hw1 hw2
      have hs1 : Lir.step p { mem, ctx, stack := { fn := l.decProc, label := 9, pos := 0, env := e₁ } :: rest } =
          .next { mem, ctx, stack := { fn := l.decProc, label := 9, pos := 1, env := e₁.insert 11 cls } :: rest } false := by
        unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, cellAddr, h8₁, Lir.dispWord, hcls]
      -- Peel first step off hstar1 cleanly:
      cases hstar1 with
      | free hs1' htail1 =>
        exact .sync hs1' htail1 hs2 hstar2 (by omega)
          ⟨rfl, rfl, .decTop (.b6 (par := pred) (by simp) (by simp)) hno⟩
      | charge hs1' _ =>
        rw [Lir.semStep_next.mpr hs1] at hs1'
        cases hs1'
  | @b7 e₁ e₂ par h8₁ h8₂ hparNe =>
    cases hv9 : mem.read? .w32 (par + 4) with
    | error _ =>
      exact .rawStuck (by unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, cellAddr, h8₁, Lir.dispWord, hv9])
    | ok v9 =>
      have h1_0 : Lir.step p { mem, ctx, stack := { fn := l.decProc, label := 7, pos := 0, env := e₁ } :: rest } =
          .next { mem, ctx, stack := { fn := l.decProc, label := 7, pos := 1, env := e₁.insert 9 v9 } :: rest } false := by
        unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, cellAddr, h8₁, Lir.dispWord, hv9]
      have h2_0 : Lir.step (install l p) { mem, ctx, stack := { fn := l.decProc, label := 7, pos := 0, env := e₂ } :: rest } =
          .next { mem, ctx, stack := { fn := l.decProc, label := 7, pos := 1, env := e₂.insert 9 v9 } :: rest } false := by
        unfold Lir.step; simp [hfast, fastDec, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, cellAddr, h8₂, Lir.dispWord, hv9]
      cases hv10 : mem.read? .w8 par with
      | error _ =>
        exact .rawStuckWithin (by omega) (star_reaches_stuck (star_free h1_0 (.refl _))
          (by unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, cellAddr, h8₁, Lir.dispWord, hv10]))
      | ok v10 =>
        have h1_1 : Lir.step p { mem, ctx, stack := { fn := l.decProc, label := 7, pos := 1, env := e₁.insert 9 v9 } :: rest } =
            .next { mem, ctx, stack := { fn := l.decProc, label := 7, pos := 2, env := (e₁.insert 9 v9).insert 10 v10 } :: rest } false := by
          unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, cellAddr, h8₁, Lir.dispWord, hv10]
        by_cases hv9z : v9 = 0
        · subst hv9z
          have h1_2 : Lir.step p { mem, ctx, stack := { fn := l.decProc, label := 7, pos := 2, env := (e₁.insert 9 0).insert 10 v10 } :: rest } =
              .next { mem, ctx, stack := { fn := l.decProc, label := 9, pos := 0, env := (e₁.insert 9 0).insert 10 v10 } :: rest } false := by
            unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, Lir.Arg.eval, w64_eq_iff, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.bindParams]
          have h2_1 : Lir.step (install l p) { mem, ctx, stack := { fn := l.decProc, label := 7, pos := 1, env := e₂.insert 9 0 } :: rest } =
              .next { mem, ctx, stack := { fn := l.decProc, label := 9, pos := 0, env := e₂.insert 9 0 } :: rest } false := by
            unfold Lir.step; simp [hfast, fastDec, Lir.Arg.eval, w64_eq_iff, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.bindParams]
          exact .sync (Lir.semStep_next.mpr h1_0) (star_free h1_1 (star_free h1_2 (.refl _)))
            (Lir.semStep_next.mpr h2_0) (star_free h2_1 (.refl _)) (by omega)
            ⟨rfl, rfl, .decTop (.b9 (par := par) (by simp [h8₁]) (by simp [h8₂])) hno⟩
        · have hv9ne : (v9 == 0) = false := beq_false_of_ne hv9z
          have h1_2 : Lir.step p { mem, ctx, stack := { fn := l.decProc, label := 7, pos := 2, env := (e₁.insert 9 v9).insert 10 v10 } :: rest } =
              .next { mem, ctx, stack := { fn := l.decProc, label := 8, pos := 0, env := (e₁.insert 9 v9).insert 10 v10 } :: rest } false := by
            unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, Lir.Arg.eval, w64_eq_iff, hv9ne, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.bindParams]
          have h2_1 : Lir.step (install l p) { mem, ctx, stack := { fn := l.decProc, label := 7, pos := 1, env := e₂.insert 9 v9 } :: rest } =
              .next { mem, ctx, stack := { fn := l.decProc, label := 8, pos := 0, env := e₂.insert 9 v9 } :: rest } false := by
            unfold Lir.step; simp [hfast, fastDec, Lir.Arg.eval, w64_eq_iff, hv9ne, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.bindParams]
          have h2_b8_0 : Lir.step (install l p) { mem, ctx, stack := { fn := l.decProc, label := 8, pos := 0, env := e₂.insert 9 v9 } :: rest } =
              .next { mem, ctx, stack := { fn := l.decProc, label := 8, pos := 1, env := (e₂.insert 9 v9).insert 10 v10 } :: rest } false := by
            unfold Lir.step; simp [hfast, fastDec, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, cellAddr, h8₂, Lir.dispWord, hv10]
          let e₁a := (e₁.insert 9 v9).insert 10 v10
          let e₂a := (e₂.insert 9 v9).insert 10 v10
          let v12 := v10 - v9
          have h1_b8_0 : Lir.step p { mem, ctx, stack := { fn := l.decProc, label := 8, pos := 0, env := e₁a } :: rest } =
              .next { mem, ctx, stack := { fn := l.decProc, label := 8, pos := 1, env := e₁a.insert 12 v12 } :: rest } false := by
            unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁a, v12, Lir.Stmt.exec, Lir.Rhs.eval, Lir.Arg.eval, w64_sub]
          have h2_b8_1 : Lir.step (install l p) { mem, ctx, stack := { fn := l.decProc, label := 8, pos := 1, env := e₂a } :: rest } =
              .next { mem, ctx, stack := { fn := l.decProc, label := 8, pos := 2, env := e₂a.insert 12 v12 } :: rest } false := by
            unfold Lir.step; simp [hfast, fastDec, e₂a, v12, Lir.Stmt.exec, Lir.Rhs.eval, Lir.Arg.eval, w64_sub]
          cases hv13 : mem.read? .w64 (par + v12 * 8 + 8) with
          | error _ =>
            exact .rawStuckWithin (by omega) (star_reaches_stuck (star_free h1_0 (star_free h1_1 (star_free h1_2 (star_free h1_b8_0 (.refl _)))))
              (by unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁a, h8₁, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, X86.Scale.word, Lir.dispWord, hv13]))
          | ok v13 =>
            have h1_b8_1 : Lir.step p { mem, ctx, stack := { fn := l.decProc, label := 8, pos := 1, env := e₁a.insert 12 v12 } :: rest } =
                .next { mem, ctx, stack := { fn := l.decProc, label := 8, pos := 2, env := (e₁a.insert 12 v12).insert 13 v13 } :: rest } false := by
              unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁a, h8₁, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, X86.Scale.word, Lir.dispWord, hv13]
            have h2_b8_2 : Lir.step (install l p) { mem, ctx, stack := { fn := l.decProc, label := 8, pos := 2, env := e₂a.insert 12 v12 } :: rest } =
                .next { mem, ctx, stack := { fn := l.decProc, label := 8, pos := 3, env := (e₂a.insert 12 v12).insert 13 v13 } :: rest } false := by
              unfold Lir.step; simp [hfast, fastDec, e₂a, h8₂, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, X86.Scale.word, Lir.dispWord, hv13]
            let v14 := v9 - 1
            have h1_b8_2 : Lir.step p { mem, ctx, stack := { fn := l.decProc, label := 8, pos := 2, env := (e₁a.insert 12 v12).insert 13 v13 } :: rest } =
                .next { mem, ctx, stack := { fn := l.decProc, label := 8, pos := 3, env := ((e₁a.insert 12 v12).insert 13 v13).insert 14 v14 } :: rest } false := by
              unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁a, v14, Lir.Stmt.exec, Lir.Rhs.eval, Lir.Arg.eval, w64_sub]
            have h2_b8_3 : Lir.step (install l p) { mem, ctx, stack := { fn := l.decProc, label := 8, pos := 3, env := (e₂a.insert 12 v12).insert 13 v13 } :: rest } =
                .next { mem, ctx, stack := { fn := l.decProc, label := 8, pos := 4, env := ((e₂a.insert 12 v12).insert 13 v13).insert 14 v14 } :: rest } false := by
              unfold Lir.step; simp [hfast, fastDec, e₂a, v14, Lir.Stmt.exec, Lir.Rhs.eval, Lir.Arg.eval, w64_sub]
            let e₁b := ((e₁a.insert 12 v12).insert 13 v13).insert 14 v14
            let e₂b := ((e₂a.insert 12 v12).insert 13 v13).insert 14 v14
            cases hw : mem.write? .w32 (par + 4) v14 with
            | error _ =>
              exact .rawStuckWithin (by omega) (star_reaches_stuck (star_free h1_0 (star_free h1_1 (star_free h1_2 (star_free h1_b8_0 (star_free h1_b8_1 (star_free h1_b8_2 (.refl _)))))))
                (by unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁a, h8₁, Lir.Stmt.exec, Lir.Arg.eval, Lir.Addr.eval, cellAddr, Lir.dispWord, hw]))
            | ok mem' =>
              have h1_b8_3 : Lir.step p { mem, ctx, stack := { fn := l.decProc, label := 8, pos := 3, env := e₁b } :: rest } =
                  .next { mem := mem', ctx, stack := { fn := l.decProc, label := 8, pos := 4, env := e₁b } :: rest } false := by
                unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁b, e₁a, h8₁, Lir.Stmt.exec, Lir.Arg.eval, Lir.Addr.eval, cellAddr, Lir.dispWord, hw]
              have h2_b8_4 : Lir.step (install l p) { mem, ctx, stack := { fn := l.decProc, label := 8, pos := 4, env := e₂b } :: rest } =
                  .next { mem := mem', ctx, stack := { fn := l.decProc, label := 8, pos := 5, env := e₂b } :: rest } false := by
                unfold Lir.step; simp [hfast, fastDec, e₂b, e₂a, h8₂, Lir.Stmt.exec, Lir.Arg.eval, Lir.Addr.eval, cellAddr, Lir.dispWord, hw]
              have h1_b8_4 : Lir.step p { mem := mem', ctx, stack := { fn := l.decProc, label := 8, pos := 4, env := e₁b } :: rest } =
                  .next { mem := mem', ctx, stack := { fn := l.decProc, label := 1, pos := 0, env := (e₁b.insert 1 v13).insert 2 par } :: rest } true := by
                unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁b, e₁a, h8₁, Lir.takeEdge, to, v, Lir.evalArgs, Lir.Arg.eval, Lir.bindParams]
              by_cases hodd : (v13 &&& 1) != 0
              · have h1_b1 : Lir.step p { mem := mem', ctx, stack := { fn := l.decProc, label := 1, pos := 0, env := (e₁b.insert 1 v13).insert 2 par } :: rest } =
                    .next { mem := mem', ctx, stack := { fn := l.decProc, label := 6, pos := 0, env := ((e₁b.insert 1 v13).insert 2 par).insert 8 par } :: rest } false := by
                  unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, Lir.Arg.eval, w64_tnz_1, hodd, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.bindParams]
                have hparNeB : (par == 0) = false := beq_false_of_ne hparNe
                have h1_b6 : Lir.step p { mem := mem', ctx, stack := { fn := l.decProc, label := 6, pos := 0, env := ((e₁b.insert 1 v13).insert 2 par).insert 8 par } :: rest } =
                    .next { mem := mem', ctx, stack := { fn := l.decProc, label := 7, pos := 0, env := ((e₁b.insert 1 v13).insert 2 par).insert 8 par } :: rest } false := by
                  unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, Lir.Arg.eval, w64_eq_iff, hparNeB, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.bindParams]
                have h2_b8_5 : Lir.step (install l p) { mem := mem', ctx, stack := { fn := l.decProc, label := 8, pos := 5, env := e₂b } :: rest } =
                    .next { mem := mem', ctx, stack := { fn := l.decProc, label := 22, pos := 0, env := e₂b } :: rest } false := by
                  unfold Lir.step; simp [hfast, fastDec, e₂b, Lir.Arg.eval, w64_tnz_1, hodd, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.bindParams]
                cases hv14z : Lir.Cond.holds .eq .w32 v14 0 with
                | true =>
                  have hread9' : mem'.read? .w32 (par + 4) = .ok (X86.Width.w32.truncate v14) := read32_write32 hv9 hw
                  have hread10' : mem'.read? .w8 par = .ok v10 := by
                    have h := write_read_disjoint (a := par) (o1 := 0) (o2 := 4) (w1 := .w8) (w2 := .w32)
                      (by simpa using hw) (by decide) (by decide) (.inl (by decide))
                    simpa using h.trans (by simpa using hv10)
                  have heq64 : Lir.Cond.holds .eq .w64 (X86.Width.w32.truncate v14) 0 = true := by
                    rw [cond_eq_w64_of_w32_trunc, hv14z]
                  let e₁c := ((e₁b.insert 1 v13).insert 2 par).insert 8 par
                  have h1_b7_0 : Lir.step p { mem := mem', ctx, stack := { fn := l.decProc, label := 7, pos := 0, env := e₁c } :: rest } =
                      .next { mem := mem', ctx, stack := { fn := l.decProc, label := 7, pos := 1, env := e₁c.insert 9 (X86.Width.w32.truncate v14) } :: rest } false := by
                    unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁c, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, cellAddr, Lir.dispWord, hread9']
                  have h1_b7_1 : Lir.step p { mem := mem', ctx, stack := { fn := l.decProc, label := 7, pos := 1, env := e₁c.insert 9 (X86.Width.w32.truncate v14) } :: rest } =
                      .next { mem := mem', ctx, stack := { fn := l.decProc, label := 7, pos := 2, env := (e₁c.insert 9 (X86.Width.w32.truncate v14)).insert 10 v10 } :: rest } false := by
                    unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁c, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, cellAddr, Lir.dispWord, hread10']
                  have h1_b7_2 : Lir.step p { mem := mem', ctx, stack := { fn := l.decProc, label := 7, pos := 2, env := (e₁c.insert 9 (X86.Width.w32.truncate v14)).insert 10 v10 } :: rest } =
                      .next { mem := mem', ctx, stack := { fn := l.decProc, label := 9, pos := 0, env := (e₁c.insert 9 (X86.Width.w32.truncate v14)).insert 10 v10 } :: rest } false := by
                    unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, Lir.Arg.eval, heq64, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.bindParams]
                  have h2_b22 : Lir.step (install l p) { mem := mem', ctx, stack := { fn := l.decProc, label := 22, pos := 0, env := e₂b } :: rest } =
                      .next { mem := mem', ctx, stack := { fn := l.decProc, label := 9, pos := 0, env := e₂b } :: rest } true := by
                    unfold Lir.step; simp [hfast, fastDec, e₂b, Lir.Arg.eval, hv14z, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.bindParams]
                  exact .sync (Lir.semStep_next.mpr h1_0)
                    (star_free h1_1 (star_free h1_2 (star_free h1_b8_0 (star_free h1_b8_1 (star_free h1_b8_2 (star_free h1_b8_3 (star_charge h1_b8_4 (star_free h1_b1 (star_free h1_b6 (star_free h1_b7_0 (star_free h1_b7_1 (star_free h1_b7_2 (.refl _)))))))))))))
                    (Lir.semStep_next.mpr h2_0)
                    (star_free h2_1 (star_free h2_b8_0 (star_free h2_b8_1 (star_free h2_b8_2 (star_free h2_b8_3 (star_free h2_b8_4 (star_free h2_b8_5 (star_charge h2_b22 (.refl _)))))))))
                    (by omega)
                    ⟨rfl, rfl, .decTop (.b9 (par := par) (by simp [e₁c]) (by simp [e₂b, e₂a, h8₂])) hno⟩
                | false =>
                  have h2_b22 : Lir.step (install l p) { mem := mem', ctx, stack := { fn := l.decProc, label := 22, pos := 0, env := e₂b } :: rest } =
                      .next { mem := mem', ctx, stack := { fn := l.decProc, label := 7, pos := 0, env := e₂b } :: rest } true := by
                    unfold Lir.step; simp [hfast, fastDec, e₂b, Lir.Arg.eval, hv14z, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.bindParams]
                  exact .sync (Lir.semStep_next.mpr h1_0)
                    (star_free h1_1 (star_free h1_2 (star_free h1_b8_0 (star_free h1_b8_1 (star_free h1_b8_2 (star_free h1_b8_3 (star_charge h1_b8_4 (star_free h1_b1 (star_free h1_b6 (.refl _))))))))))
                    (Lir.semStep_next.mpr h2_0)
                    (star_free h2_1 (star_free h2_b8_0 (star_free h2_b8_1 (star_free h2_b8_2 (star_free h2_b8_3 (star_free h2_b8_4 (star_free h2_b8_5 (star_charge h2_b22 (.refl _)))))))))
                    (by omega)
                    ⟨rfl, rfl, .decTop (.b7 (par := par) (by simp) (by simp [e₂b, e₂a, h8₂]) hparNe) hno⟩
              · have hev : ((v13 &&& 1) != 0) = false := Bool.eq_false_iff.mpr hodd
                have h1_b1 : Lir.step p { mem := mem', ctx, stack := { fn := l.decProc, label := 1, pos := 0, env := (e₁b.insert 1 v13).insert 2 par } :: rest } =
                    .next { mem := mem', ctx, stack := { fn := l.decProc, label := 2, pos := 0, env := (e₁b.insert 1 v13).insert 2 par } :: rest } false := by
                  unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, Lir.Arg.eval, w64_tnz_1, hev, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.bindParams]
                have h2_b8_5 : Lir.step (install l p) { mem := mem', ctx, stack := { fn := l.decProc, label := 8, pos := 5, env := e₂b } :: rest } =
                    .next { mem := mem', ctx, stack := { fn := l.decProc, label := 23, pos := 0, env := e₂b } :: rest } false := by
                  unfold Lir.step; simp [hfast, fastDec, e₂b, Lir.Arg.eval, w64_tnz_1, hev, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.bindParams]
                have h2_b23 : Lir.step (install l p) { mem := mem', ctx, stack := { fn := l.decProc, label := 23, pos := 0, env := e₂b } :: rest } =
                    .next { mem := mem', ctx, stack := { fn := l.decProc, label := 2, pos := 0, env := (e₂b.insert 20 v13).insert 21 par } :: rest } true := by
                  unfold Lir.step; simp [hfast, fastDec, e₂b, e₂a, h8₂, Lir.takeEdge, to, v, Lir.evalArgs, Lir.Arg.eval, Lir.bindParams]
                exact .sync (Lir.semStep_next.mpr h1_0)
                  (star_free h1_1 (star_free h1_2 (star_free h1_b8_0 (star_free h1_b8_1 (star_free h1_b8_2 (star_free h1_b8_3 (star_charge h1_b8_4 (star_free h1_b1 (.refl _)))))))))
                  (Lir.semStep_next.mpr h2_0)
                  (star_free h2_1 (star_free h2_b8_0 (star_free h2_b8_1 (star_free h2_b8_2 (star_free h2_b8_3 (star_free h2_b8_4 (star_free h2_b8_5 (star_charge h2_b23 (.refl _)))))))))
                  (by omega)
                  ⟨rfl, rfl, .decTop (.b2 (cur := v13) (par := par) (by simp) (by simp) (by simp) (by simp)) hno⟩
  | @b2 e₁ e₂ cur par h1 h2 h20 h21 =>
    cases hv3 : mem.read? .w32 (cur + 4) with
    | error _ =>
      exact .rawStuck (by unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, cellAddr, h1, Lir.dispWord, hv3])
    | ok v3 =>
      have htr3 := read32_truncate_self hv3
      have h1_b2_0 : Lir.step p { mem, ctx, stack := { fn := l.decProc, label := 2, pos := 0, env := e₁ } :: rest } =
          .next { mem, ctx, stack := { fn := l.decProc, label := 2, pos := 1, env := e₁.insert 3 v3 } :: rest } false := by
        unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, cellAddr, h1, Lir.dispWord, hv3]
      have h2_b2_0 : Lir.step (install l p) { mem, ctx, stack := { fn := l.decProc, label := 2, pos := 0, env := e₂ } :: rest } =
          .next { mem, ctx, stack := { fn := l.decProc, label := 2, pos := 1, env := e₂.insert 3 v3 } :: rest } false := by
        unfold Lir.step; simp [hfast, fastDec, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, cellAddr, h20, Lir.dispWord, hv3]
      by_cases hv3z : v3 = 0
      · subst hv3z
        have h1_b2_1 : Lir.step p { mem, ctx, stack := { fn := l.decProc, label := 2, pos := 1, env := e₁.insert 3 0 } :: rest } =
            .next { mem, ctx, stack := { fn := l.decProc, label := 3, pos := 0, env := e₁.insert 3 0 } :: rest } false := by
          unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, Lir.Arg.eval, w32_slt_zero_of_zero, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.bindParams]
        have h1_b3 : Lir.step p { mem, ctx, stack := { fn := l.decProc, label := 3, pos := 0, env := e₁.insert 3 0 } :: rest } =
            .next { mem, ctx, stack := { fn := l.decProc, label := 5, pos := 0, env := e₁.insert 3 0 } :: rest } false := by
          unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, Lir.Arg.eval, w32_eq_zero_of_truncate htr3, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.bindParams]
        have h2_b2_1 : Lir.step (install l p) { mem, ctx, stack := { fn := l.decProc, label := 2, pos := 1, env := e₂.insert 3 0 } :: rest } =
            .next { mem, ctx, stack := { fn := l.decProc, label := 5, pos := 0, env := e₂.insert 3 0 } :: rest } false := by
          unfold Lir.step; simp [hfast, fastDec, Lir.Arg.eval, w32_eq_zero_of_truncate htr3, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.bindParams]
        cases hv5 : mem.read? .w8 cur with
        | error _ =>
          exact .rawStuckWithin (by omega) (star_reaches_stuck (star_free h1_b2_0 (star_free h1_b2_1 (star_free h1_b3 (.refl _))))
            (by unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, cellAddr, h1, Lir.dispWord, hv5]))
        | ok v5 =>
          let e₁s := (e₁.insert 3 0).insert 5 v5
          let e₂s := (e₂.insert 3 0).insert 5 v5
          have h1_b5_0 : Lir.step p { mem, ctx, stack := { fn := l.decProc, label := 5, pos := 0, env := e₁.insert 3 0 } :: rest } =
              .next { mem, ctx, stack := { fn := l.decProc, label := 5, pos := 1, env := e₁s } :: rest } false := by
            unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁s, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, cellAddr, h1, Lir.dispWord, hv5]
          have h2_b5_0 : Lir.step (install l p) { mem, ctx, stack := { fn := l.decProc, label := 5, pos := 0, env := e₂.insert 3 0 } :: rest } =
              .next { mem, ctx, stack := { fn := l.decProc, label := 5, pos := 1, env := e₂s } :: rest } false := by
            unfold Lir.step; simp [hfast, fastDec, e₂s, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, cellAddr, h20, Lir.dispWord, hv5]
          have h1_to_b5 : Sem.Star (Lir.semStep p) { mem, ctx, stack := { fn := l.decProc, label := 2, pos := 1, env := e₁.insert 3 0 } :: rest } 0
              { mem, ctx, stack := { fn := l.decProc, label := 5, pos := 1, env := e₁s } :: rest } :=
            star_free h1_b2_1 (star_free h1_b3 (star_free h1_b5_0 (.refl _)))
          have h2_to_b5 : Sem.Star (Lir.semStep (install l p)) { mem, ctx, stack := { fn := l.decProc, label := 2, pos := 1, env := e₂.insert 3 0 } :: rest } 0
              { mem, ctx, stack := { fn := l.decProc, label := 5, pos := 1, env := e₂s } :: rest } :=
            star_free h2_b2_1 (star_free h2_b5_0 (.refl _))
          -- Helper for the general `b12` (`Gen.dec`) vs `b24` (`fastDec`) step when both reach it
          have doGeneral :
              Lir.step p { mem, ctx, stack := { fn := l.decProc, label := 5, pos := 1, env := e₁s } :: rest } =
                .next { mem, ctx, stack := { fn := l.decProc, label := 12, pos := 0, env := e₁s } :: rest } false →
              Sem.Star (Lir.semStep (install l p))
                { mem, ctx, stack := { fn := l.decProc, label := 5, pos := 1, env := e₂s } :: rest } 0
                { mem, ctx, stack := { fn := l.decProc, label := 24, pos := 0, env := e₂s } :: rest } →
              MatchedStep l p { mem, ctx, stack := { fn := l.decProc, label := 2, pos := 0, env := e₁ } :: rest }
                { mem, ctx, stack := { fn := l.decProc, label := 2, pos := 0, env := e₂ } :: rest } := by
            intro h1_b5_1 h2_to_b24
            cases hf0 : mem.read? .w64 (cur + 8) with
            | error _ =>
              exact .rawStuckWithin (by omega) (star_reaches_stuck
                (star_free h1_b2_0 (Sem.Star.trans h1_to_b5 (star_free h1_b5_1 (.refl _))))
                (by unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁s, h1, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, cellAddr, Lir.dispWord, hf0]))
            | ok f0 =>
              let v7 := v5 - 1
              have h1_12_0 : Lir.step p { mem, ctx, stack := { fn := l.decProc, label := 12, pos := 0, env := e₁s } :: rest } =
                  .next { mem, ctx, stack := { fn := l.decProc, label := 12, pos := 1, env := e₁s.insert 6 f0 } :: rest } false := by
                unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁s, h1, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, cellAddr, Lir.dispWord, hf0]
              have h1_12_1 : Lir.step p { mem, ctx, stack := { fn := l.decProc, label := 12, pos := 1, env := e₁s.insert 6 f0 } :: rest } =
                  .next { mem, ctx, stack := { fn := l.decProc, label := 12, pos := 2, env := (e₁s.insert 6 f0).insert 7 v7 } :: rest } false := by
                unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁s, v7, Lir.Stmt.exec, Lir.Rhs.eval, Lir.Arg.eval, w64_sub]
              have h2_24_0 : Lir.step (install l p) { mem, ctx, stack := { fn := l.decProc, label := 24, pos := 0, env := e₂s } :: rest } =
                  .next { mem, ctx, stack := { fn := l.decProc, label := 24, pos := 1, env := e₂s.insert 6 f0 } :: rest } false := by
                unfold Lir.step; simp [hfast, fastDec, e₂s, h20, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, cellAddr, Lir.dispWord, hf0]
              have h2_24_1 : Lir.step (install l p) { mem, ctx, stack := { fn := l.decProc, label := 24, pos := 1, env := e₂s.insert 6 f0 } :: rest } =
                  .next { mem, ctx, stack := { fn := l.decProc, label := 24, pos := 2, env := (e₂s.insert 6 f0).insert 7 v7 } :: rest } false := by
                unfold Lir.step; simp [hfast, fastDec, e₂s, v7, Lir.Stmt.exec, Lir.Rhs.eval, Lir.Arg.eval, w64_sub]
              cases hw1 : mem.write? .w64 (cur + 8) par with
              | error _ =>
                exact .rawStuckWithin (by omega) (star_reaches_stuck
                  (star_free h1_b2_0 (Sem.Star.trans h1_to_b5 (star_free h1_b5_1 (star_free h1_12_0 (star_free h1_12_1 (.refl _))))))
                  (by unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁s, h1, h2, Lir.Stmt.exec, Lir.Arg.eval, Lir.Addr.eval, cellAddr, Lir.dispWord, hw1]))
              | ok mem1 =>
                have h1_12_2 : Lir.step p { mem, ctx, stack := { fn := l.decProc, label := 12, pos := 2, env := (e₁s.insert 6 f0).insert 7 v7 } :: rest } =
                    .next { mem := mem1, ctx, stack := { fn := l.decProc, label := 12, pos := 3, env := (e₁s.insert 6 f0).insert 7 v7 } :: rest } false := by
                  unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁s, h1, h2, Lir.Stmt.exec, Lir.Arg.eval, Lir.Addr.eval, cellAddr, Lir.dispWord, hw1]
                have h2_24_2 : Lir.step (install l p) { mem, ctx, stack := { fn := l.decProc, label := 24, pos := 2, env := (e₂s.insert 6 f0).insert 7 v7 } :: rest } =
                    .next { mem := mem1, ctx, stack := { fn := l.decProc, label := 24, pos := 3, env := (e₂s.insert 6 f0).insert 7 v7 } :: rest } false := by
                  unfold Lir.step; simp [hfast, fastDec, e₂s, h20, h21, Lir.Stmt.exec, Lir.Arg.eval, Lir.Addr.eval, cellAddr, Lir.dispWord, hw1]
                cases hw2 : mem1.write? .w32 (cur + 4) v7 with
                | error _ =>
                  exact .rawStuckWithin (by omega) (star_reaches_stuck
                    (star_free h1_b2_0 (Sem.Star.trans h1_to_b5 (star_free h1_b5_1 (star_free h1_12_0 (star_free h1_12_1 (star_free h1_12_2 (.refl _)))))))
                    (by unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁s, h1, Lir.Stmt.exec, Lir.Arg.eval, Lir.Addr.eval, cellAddr, Lir.dispWord, hw2]))
                | ok mem2 =>
                  have h1_12_3 : Lir.step p { mem := mem1, ctx, stack := { fn := l.decProc, label := 12, pos := 3, env := (e₁s.insert 6 f0).insert 7 v7 } :: rest } =
                      .next { mem := mem2, ctx, stack := { fn := l.decProc, label := 12, pos := 4, env := (e₁s.insert 6 f0).insert 7 v7 } :: rest } false := by
                    unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁s, h1, Lir.Stmt.exec, Lir.Arg.eval, Lir.Addr.eval, cellAddr, Lir.dispWord, hw2]
                  have h1_12_4 : Lir.step p { mem := mem2, ctx, stack := { fn := l.decProc, label := 12, pos := 4, env := (e₁s.insert 6 f0).insert 7 v7 } :: rest } =
                      .next { mem := mem2, ctx, stack := { fn := l.decProc, label := 1, pos := 0, env := (((e₁s.insert 6 f0).insert 7 v7).insert 1 f0).insert 2 cur } :: rest } true := by
                    unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁s, h1, Lir.takeEdge, to, v, Lir.evalArgs, Lir.Arg.eval, Lir.bindParams]
                  have h2_24_3 : Lir.step (install l p) { mem := mem1, ctx, stack := { fn := l.decProc, label := 24, pos := 3, env := (e₂s.insert 6 f0).insert 7 v7 } :: rest } =
                      .next { mem := mem2, ctx, stack := { fn := l.decProc, label := 24, pos := 4, env := (e₂s.insert 6 f0).insert 7 v7 } :: rest } false := by
                    unfold Lir.step; simp [hfast, fastDec, e₂s, h20, Lir.Stmt.exec, Lir.Arg.eval, Lir.Addr.eval, cellAddr, Lir.dispWord, hw2]
                  have h2_24_4 : Lir.step (install l p) { mem := mem2, ctx, stack := { fn := l.decProc, label := 24, pos := 4, env := (e₂s.insert 6 f0).insert 7 v7 } :: rest } =
                      .next { mem := mem2, ctx, stack := { fn := l.decProc, label := 1, pos := 0, env := (((e₂s.insert 6 f0).insert 7 v7).insert 1 f0).insert 2 cur } :: rest } true := by
                    unfold Lir.step; simp [hfast, fastDec, e₂s, h20, Lir.takeEdge, to, v, Lir.evalArgs, Lir.Arg.eval, Lir.bindParams]
                  exact .sync (Lir.semStep_next.mpr h1_b2_0)
                    (Sem.Star.trans h1_to_b5 (star_free h1_b5_1 (star_free h1_12_0 (star_free h1_12_1 (star_free h1_12_2 (star_free h1_12_3 (star_charge h1_12_4 (.refl _))))))))
                    (Lir.semStep_next.mpr h2_b2_0)
                    (Sem.Star.trans h2_to_b5 (Sem.Star.trans h2_to_b24 (star_free h2_24_0 (star_free h2_24_1 (star_free h2_24_2 (star_free h2_24_3 (star_charge h2_24_4 (.refl _))))))))
                    (by omega) ⟨rfl, rfl, .decTop (.b1 (cur := f0) (par := cur) (by simp) (by simp) (by simp) (by simp)) hno⟩
          -- Helper for fast leaf recycle `b19` vs `Gen.dec` `b9` (starting with `mem1` where `[cur+8] = par`)
          have doLeafRecycle : ∀ {cGen : Nat} {eGen : Lir.Env} {mem1 : X86.Memory} {eFast : Lir.Env},
              cGen ≤ 2 →
              eGen[8]? = some cur →
              eFast[20]? = some cur →
              eFast[21]? = some par →
              mem.write? .w64 (cur + 8) par = .ok mem1 →
              Sem.Star (Lir.semStep p) { mem, ctx, stack := { fn := l.decProc, label := 2, pos := 1, env := e₁.insert 3 0 } :: rest } cGen
                { mem := mem1, ctx, stack := { fn := l.decProc, label := 9, pos := 0, env := eGen } :: rest } →
              Sem.Star (Lir.semStep (install l p)) { mem, ctx, stack := { fn := l.decProc, label := 2, pos := 1, env := e₂.insert 3 0 } :: rest } 0
                { mem, ctx, stack := { fn := l.decProc, label := 19, pos := 0, env := eFast } :: rest } →
              (∃ f0, mem.read? .w64 (cur + 8) = .ok f0) →
              MatchedStep l p { mem, ctx, stack := { fn := l.decProc, label := 2, pos := 0, env := e₁ } :: rest }
                { mem, ctx, stack := { fn := l.decProc, label := 2, pos := 0, env := e₂ } :: rest } := by
            intro cGen eGen mem1 eFast hcGen h8g h20f h21f hw1 hstarGen hstarFast ⟨f0, hf0⟩
            rcases exec_gen_b9_stuck_or_ok hdec h8g (mem := mem1) (ctx := ctx) (rest := rest) with hstk | ⟨cls, pred, old, mA, mB, hcls, hpred, hold, hwA, hwB⟩
            · exact .rawStuckWithin (by omega)
                (Inline.reaches_of_star_reaches (star_free h1_b2_0 hstarGen) hstk)
            · have hpredEq : pred = par := by
                have hr := read64_write64_ok hf0 hw1
                rw [hr] at hpred; exact Option.some.inj (by simpa using hpred.symm)
              subst pred
              have hgen9 := exec_gen_b9 (rest := rest) hdec h8g hcls hpred hold hwA hwB
              have hf0s : Lir.step (install l p) { mem, ctx, stack := { fn := l.decProc, label := 19, pos := 0, env := eFast } :: rest } =
                  .next { mem := mem1, ctx, stack := { fn := l.decProc, label := 19, pos := 1, env := eFast } :: rest } false := by
                unfold Lir.step; simp [hfast, fastDec, h20f, h21f, Lir.Stmt.exec, Lir.Arg.eval, Lir.Addr.eval, cellAddr, Lir.dispWord, hw1]
              have hf1s : Lir.step (install l p) { mem := mem1, ctx, stack := { fn := l.decProc, label := 19, pos := 1, env := eFast } :: rest } =
                  .next { mem := mem1, ctx, stack := { fn := l.decProc, label := 19, pos := 2, env := eFast.insert 24 cls } :: rest } false := by
                unfold Lir.step; simp [hfast, fastDec, h20f, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, cellAddr, Lir.dispWord, hcls]
              have hf2s : Lir.step (install l p) { mem := mem1, ctx, stack := { fn := l.decProc, label := 19, pos := 2, env := eFast.insert 24 cls } :: rest } =
                  .next { mem := mem1, ctx, stack := { fn := l.decProc, label := 19, pos := 3, env := (eFast.insert 24 cls).insert 25 old } :: rest } false := by
                unfold Lir.step; simp [hfast, fastDec, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, X86.Scale.word, Lir.dispWord, hold]
              have hf3s : Lir.step (install l p) { mem := mem1, ctx, stack := { fn := l.decProc, label := 19, pos := 3, env := (eFast.insert 24 cls).insert 25 old } :: rest } =
                  .next { mem := mA, ctx, stack := { fn := l.decProc, label := 19, pos := 4, env := (eFast.insert 24 cls).insert 25 old } :: rest } false := by
                unfold Lir.step; simp [hfast, fastDec, h20f, Lir.Stmt.exec, Lir.Arg.eval, Lir.Addr.eval, cellAddr, Lir.dispWord, hwA]
              have hf4s : Lir.step (install l p) { mem := mA, ctx, stack := { fn := l.decProc, label := 19, pos := 4, env := (eFast.insert 24 cls).insert 25 old } :: rest } =
                  .next { mem := mB, ctx, stack := { fn := l.decProc, label := 19, pos := 5, env := (eFast.insert 24 cls).insert 25 old } :: rest } false := by
                unfold Lir.step; simp [hfast, fastDec, h20f, Lir.Stmt.exec, Lir.Arg.eval, Lir.Addr.eval, X86.Scale.word, Lir.dispWord, hwB]
              have hf5s : Lir.step (install l p) { mem := mB, ctx, stack := { fn := l.decProc, label := 19, pos := 5, env := (eFast.insert 24 cls).insert 25 old } :: rest } =
                  .next { mem := mB, ctx, stack := { fn := l.decProc, label := 6, pos := 0, env := ((eFast.insert 24 cls).insert 25 old).insert 8 par } :: rest } true := by
                unfold Lir.step; simp [hfast, fastDec, h21f, Lir.takeEdge, to, v, Lir.evalArgs, Lir.Arg.eval, Lir.bindParams]
              exact .sync (Lir.semStep_next.mpr h1_b2_0) (Sem.Star.trans hstarGen hgen9)
                (Lir.semStep_next.mpr h2_b2_0)
                (Sem.Star.trans hstarFast (star_free hf0s (star_free hf1s (star_free hf2s (star_free hf3s (star_free hf4s (star_charge hf5s (.refl _))))))))
                (by omega) ⟨rfl, rfl, .decTop (.b6 (par := par) (by simp) (by simp)) hno⟩
          -- Now case-split on `v5` (`2`, `0`, `1`, or other)
          by_cases hv5_2 : v5 = 2
          · subst hv5_2
            have h1_b5_1 : Lir.step p { mem, ctx, stack := { fn := l.decProc, label := 5, pos := 1, env := e₁s } :: rest } =
                .next { mem, ctx, stack := { fn := l.decProc, label := 12, pos := 0, env := e₁s } :: rest } false := by
              unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁s, Lir.Arg.eval, w64_eq_iff, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.bindParams]
            have h2_b5_1 : Lir.step (install l p) { mem, ctx, stack := { fn := l.decProc, label := 5, pos := 1, env := e₂s } :: rest } =
                .next { mem, ctx, stack := { fn := l.decProc, label := 11, pos := 0, env := e₂s } :: rest } false := by
              unfold Lir.step; simp [hfast, fastDec, e₂s, Lir.Arg.eval, w64_eq_iff, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.bindParams]
            cases hf0 : mem.read? .w64 (cur + 8) with
            | error _ =>
              exact .rawStuckWithin (by omega) (star_reaches_stuck
                (star_free h1_b2_0 (Sem.Star.trans h1_to_b5 (star_free h1_b5_1 (.refl _))))
                (by unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁s, h1, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, cellAddr, Lir.dispWord, hf0]))
            | ok f0 =>
              have h2_b11_0 : Lir.step (install l p) { mem, ctx, stack := { fn := l.decProc, label := 11, pos := 0, env := e₂s } :: rest } =
                  .next { mem, ctx, stack := { fn := l.decProc, label := 11, pos := 1, env := e₂s.insert 22 f0 } :: rest } false := by
                unfold Lir.step; simp [hfast, fastDec, e₂s, h20, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, cellAddr, Lir.dispWord, hf0]
              have h1_12_0 : Lir.step p { mem, ctx, stack := { fn := l.decProc, label := 12, pos := 0, env := e₁s } :: rest } =
                  .next { mem, ctx, stack := { fn := l.decProc, label := 12, pos := 1, env := e₁s.insert 6 f0 } :: rest } false := by
                unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁s, h1, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, cellAddr, Lir.dispWord, hf0]
              have h1_12_1 : Lir.step p { mem, ctx, stack := { fn := l.decProc, label := 12, pos := 1, env := e₁s.insert 6 f0 } :: rest } =
                  .next { mem, ctx, stack := { fn := l.decProc, label := 12, pos := 2, env := (e₁s.insert 6 f0).insert 7 1 } :: rest } false := by
                unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁s, Lir.Stmt.exec, Lir.Rhs.eval, Lir.Arg.eval, w64_sub]
              by_cases hf0odd : (f0 &&& 1) != 0
              · have h2_b11_1 : Lir.step (install l p) { mem, ctx, stack := { fn := l.decProc, label := 11, pos := 1, env := e₂s.insert 22 f0 } :: rest } =
                    .next { mem, ctx, stack := { fn := l.decProc, label := 12, pos := 0, env := e₂s.insert 22 f0 } :: rest } false := by
                  unfold Lir.step; simp [hfast, fastDec, Lir.Arg.eval, w64_tnz_1, hf0odd, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.bindParams]
                by_cases hcur0 : cur = 0
                · subst hcur0
                  have hf0' : mem.read? .w64 8 = .ok f0 := by simpa using hf0
                  have h2_b12 : Lir.step (install l p) { mem, ctx, stack := { fn := l.decProc, label := 12, pos := 0, env := e₂s.insert 22 f0 } :: rest } =
                      .next { mem, ctx, stack := { fn := l.decProc, label := 24, pos := 0, env := e₂s.insert 22 f0 } :: rest } false := by
                    unfold Lir.step; simp [hfast, fastDec, e₂s, h20, Lir.Arg.eval, w64_eq_iff, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.bindParams]
                  -- Note `e₂s.insert 22 f0` agrees with `e₂s` on `5, 20, 21`, so run `b24` directly!
                  cases hw1 : mem.write? .w64 8 par with
                  | error _ =>
                    exact .rawStuckWithin (by omega) (star_reaches_stuck
                      (star_free h1_b2_0 (Sem.Star.trans h1_to_b5 (star_free h1_b5_1 (star_free h1_12_0 (star_free h1_12_1 (.refl _))))))
                      (by unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁s, h1, h2, Lir.Stmt.exec, Lir.Arg.eval, Lir.Addr.eval, cellAddr, Lir.dispWord, hw1]))
                  | ok mem1 =>
                    have h1_12_2 : Lir.step p { mem, ctx, stack := { fn := l.decProc, label := 12, pos := 2, env := (e₁s.insert 6 f0).insert 7 1 } :: rest } =
                        .next { mem := mem1, ctx, stack := { fn := l.decProc, label := 12, pos := 3, env := (e₁s.insert 6 f0).insert 7 1 } :: rest } false := by
                      unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁s, h1, h2, Lir.Stmt.exec, Lir.Arg.eval, Lir.Addr.eval, cellAddr, Lir.dispWord, hw1]
                    cases hw2 : mem1.write? .w32 4 1 with
                    | error _ =>
                      exact .rawStuckWithin (by omega) (star_reaches_stuck
                        (star_free h1_b2_0 (Sem.Star.trans h1_to_b5 (star_free h1_b5_1 (star_free h1_12_0 (star_free h1_12_1 (star_free h1_12_2 (.refl _)))))))
                        (by unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁s, h1, Lir.Stmt.exec, Lir.Arg.eval, Lir.Addr.eval, cellAddr, Lir.dispWord, hw2]))
                    | ok mem2 =>
                      have h1_12_3 : Lir.step p { mem := mem1, ctx, stack := { fn := l.decProc, label := 12, pos := 3, env := (e₁s.insert 6 f0).insert 7 1 } :: rest } =
                          .next { mem := mem2, ctx, stack := { fn := l.decProc, label := 12, pos := 4, env := (e₁s.insert 6 f0).insert 7 1 } :: rest } false := by
                        unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁s, h1, Lir.Stmt.exec, Lir.Arg.eval, Lir.Addr.eval, cellAddr, Lir.dispWord, hw2]
                      have h1_12_4 : Lir.step p { mem := mem2, ctx, stack := { fn := l.decProc, label := 12, pos := 4, env := (e₁s.insert 6 f0).insert 7 1 } :: rest } =
                          .next { mem := mem2, ctx, stack := { fn := l.decProc, label := 1, pos := 0, env := (((e₁s.insert 6 f0).insert 7 1).insert 1 f0).insert 2 0 } :: rest } true := by
                        unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁s, h1, Lir.takeEdge, to, v, Lir.evalArgs, Lir.Arg.eval, Lir.bindParams]
                      let e2g := e₂s.insert 22 f0
                      have h2_24_0 : Lir.step (install l p) { mem, ctx, stack := { fn := l.decProc, label := 24, pos := 0, env := e2g } :: rest } =
                          .next { mem, ctx, stack := { fn := l.decProc, label := 24, pos := 1, env := e2g.insert 6 f0 } :: rest } false := by
                        unfold Lir.step; simp [hfast, fastDec, e2g, e₂s, h20, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, cellAddr, Lir.dispWord, hf0']
                      have h2_24_1 : Lir.step (install l p) { mem, ctx, stack := { fn := l.decProc, label := 24, pos := 1, env := e2g.insert 6 f0 } :: rest } =
                          .next { mem, ctx, stack := { fn := l.decProc, label := 24, pos := 2, env := (e2g.insert 6 f0).insert 7 1 } :: rest } false := by
                        unfold Lir.step; simp [hfast, fastDec, e2g, e₂s, Lir.Stmt.exec, Lir.Rhs.eval, Lir.Arg.eval, w64_sub]
                      have h2_24_2 : Lir.step (install l p) { mem, ctx, stack := { fn := l.decProc, label := 24, pos := 2, env := (e2g.insert 6 f0).insert 7 1 } :: rest } =
                          .next { mem := mem1, ctx, stack := { fn := l.decProc, label := 24, pos := 3, env := (e2g.insert 6 f0).insert 7 1 } :: rest } false := by
                        unfold Lir.step; simp [hfast, fastDec, e2g, e₂s, h20, h21, Lir.Stmt.exec, Lir.Arg.eval, Lir.Addr.eval, cellAddr, Lir.dispWord, hw1]
                      have h2_24_3 : Lir.step (install l p) { mem := mem1, ctx, stack := { fn := l.decProc, label := 24, pos := 3, env := (e2g.insert 6 f0).insert 7 1 } :: rest } =
                          .next { mem := mem2, ctx, stack := { fn := l.decProc, label := 24, pos := 4, env := (e2g.insert 6 f0).insert 7 1 } :: rest } false := by
                        unfold Lir.step; simp [hfast, fastDec, e2g, e₂s, h20, Lir.Stmt.exec, Lir.Arg.eval, Lir.Addr.eval, cellAddr, Lir.dispWord, hw2]
                      have h2_24_4 : Lir.step (install l p) { mem := mem2, ctx, stack := { fn := l.decProc, label := 24, pos := 4, env := (e2g.insert 6 f0).insert 7 1 } :: rest } =
                          .next { mem := mem2, ctx, stack := { fn := l.decProc, label := 1, pos := 0, env := (((e2g.insert 6 f0).insert 7 1).insert 1 f0).insert 2 0 } :: rest } true := by
                        unfold Lir.step; simp [hfast, fastDec, e2g, e₂s, h20, Lir.takeEdge, to, v, Lir.evalArgs, Lir.Arg.eval, Lir.bindParams]
                      exact .sync (Lir.semStep_next.mpr h1_b2_0)
                        (Sem.Star.trans h1_to_b5 (star_free h1_b5_1 (star_free h1_12_0 (star_free h1_12_1 (star_free h1_12_2 (star_free h1_12_3 (star_charge h1_12_4 (.refl _))))))))
                        (Lir.semStep_next.mpr h2_b2_0)
                        (Sem.Star.trans h2_to_b5 (star_free h2_b5_1 (star_free h2_b11_0 (star_free h2_b11_1 (star_free h2_b12 (star_free h2_24_0 (star_free h2_24_1 (star_free h2_24_2 (star_free h2_24_3 (star_charge h2_24_4 (.refl _)))))))))))
                        (by omega) ⟨rfl, rfl, .decTop (.b1 (cur := f0) (par := 0) (by simp) (by simp) (by simp) (by simp)) hno⟩
                · -- `v5 = 2`, `f0` odd, `cur ≠ 0`
                  have hcurNe : (cur == 0) = false := beq_false_of_ne hcur0
                  have h2_b12 : Lir.step (install l p) { mem, ctx, stack := { fn := l.decProc, label := 12, pos := 0, env := e₂s.insert 22 f0 } :: rest } =
                      .next { mem, ctx, stack := { fn := l.decProc, label := 13, pos := 0, env := e₂s.insert 22 f0 } :: rest } false := by
                    unfold Lir.step; simp [hfast, fastDec, e₂s, h20, Lir.Arg.eval, w64_eq_iff, hcurNe, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.bindParams]
                  cases hw1 : mem.write? .w64 (cur + 8) par with
                  | error _ =>
                    exact .rawStuckWithin (by omega) (star_reaches_stuck
                      (star_free h1_b2_0 (Sem.Star.trans h1_to_b5 (star_free h1_b5_1 (star_free h1_12_0 (star_free h1_12_1 (.refl _))))))
                      (by unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁s, h1, h2, Lir.Stmt.exec, Lir.Arg.eval, Lir.Addr.eval, cellAddr, Lir.dispWord, hw1]))
                  | ok mem1 =>
                    have h1_12_2 : Lir.step p { mem, ctx, stack := { fn := l.decProc, label := 12, pos := 2, env := (e₁s.insert 6 f0).insert 7 1 } :: rest } =
                        .next { mem := mem1, ctx, stack := { fn := l.decProc, label := 12, pos := 3, env := (e₁s.insert 6 f0).insert 7 1 } :: rest } false := by
                      unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁s, h1, h2, Lir.Stmt.exec, Lir.Arg.eval, Lir.Addr.eval, cellAddr, Lir.dispWord, hw1]
                    cases hw2 : mem1.write? .w32 (cur + 4) 1 with
                    | error _ =>
                      exact .rawStuckWithin (by omega) (star_reaches_stuck
                        (star_free h1_b2_0 (Sem.Star.trans h1_to_b5 (star_free h1_b5_1 (star_free h1_12_0 (star_free h1_12_1 (star_free h1_12_2 (.refl _)))))))
                        (by unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁s, h1, Lir.Stmt.exec, Lir.Arg.eval, Lir.Addr.eval, cellAddr, Lir.dispWord, hw2]))
                    | ok mem2 =>
                      have h1_12_3 : Lir.step p { mem := mem1, ctx, stack := { fn := l.decProc, label := 12, pos := 3, env := (e₁s.insert 6 f0).insert 7 1 } :: rest } =
                          .next { mem := mem2, ctx, stack := { fn := l.decProc, label := 12, pos := 4, env := (e₁s.insert 6 f0).insert 7 1 } :: rest } false := by
                        unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁s, h1, Lir.Stmt.exec, Lir.Arg.eval, Lir.Addr.eval, cellAddr, Lir.dispWord, hw2]
                      let e₁c := (((e₁s.insert 6 f0).insert 7 1).insert 1 f0).insert 2 cur
                      have h1_12_4 : Lir.step p { mem := mem2, ctx, stack := { fn := l.decProc, label := 12, pos := 4, env := (e₁s.insert 6 f0).insert 7 1 } :: rest } =
                          .next { mem := mem2, ctx, stack := { fn := l.decProc, label := 1, pos := 0, env := e₁c } :: rest } true := by
                        unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁c, e₁s, h1, Lir.takeEdge, to, v, Lir.evalArgs, Lir.Arg.eval, Lir.bindParams]
                      have h1_b1 : Lir.step p { mem := mem2, ctx, stack := { fn := l.decProc, label := 1, pos := 0, env := e₁c } :: rest } =
                          .next { mem := mem2, ctx, stack := { fn := l.decProc, label := 6, pos := 0, env := e₁c.insert 8 cur } :: rest } false := by
                        unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁c, Lir.Arg.eval, w64_tnz_1, hf0odd, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.bindParams]
                      have h1_b6 : Lir.step p { mem := mem2, ctx, stack := { fn := l.decProc, label := 6, pos := 0, env := e₁c.insert 8 cur } :: rest } =
                          .next { mem := mem2, ctx, stack := { fn := l.decProc, label := 7, pos := 0, env := e₁c.insert 8 cur } :: rest } false := by
                        unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, Lir.Arg.eval, w64_eq_iff, hcurNe, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.bindParams]
                      have hmem1_r32 : mem1.read? .w32 (cur + 4) = .ok 0 := by
                        have h := write_read_disjoint (a := cur) (o1 := 4) (o2 := 8) (w1 := .w32) (w2 := .w64)
                          (by simpa using hw1) (by decide) (by decide) (.inl (by decide))
                        simpa using h.trans hv3
                      have hmem2_r32 : mem2.read? .w32 (cur + 4) = .ok 1 := by
                        simpa [w32_truncate_one] using read32_write32 hmem1_r32 hw2
                      have hmem1_r8 : mem1.read? .w8 cur = .ok 2 := by
                        have h := write_read_disjoint (a := cur) (o1 := 0) (o2 := 8) (w1 := .w8) (w2 := .w64)
                          (by simpa using hw1) (by decide) (by decide) (.inl (by decide))
                        simpa using h.trans (by simpa using hv5)
                      have hmem2_r8 : mem2.read? .w8 cur = .ok 2 := by
                        have h := write_read_disjoint (a := cur) (o1 := 0) (o2 := 4) (w1 := .w8) (w2 := .w32)
                          (by simpa using hw2) (by decide) (by decide) (.inl (by decide))
                        simpa using h.trans (by simpa using hmem1_r8)
                      let e₁d := ((e₁c.insert 8 cur).insert 9 1).insert 10 2
                      have h1_b7_0 : Lir.step p { mem := mem2, ctx, stack := { fn := l.decProc, label := 7, pos := 0, env := e₁c.insert 8 cur } :: rest } =
                          .next { mem := mem2, ctx, stack := { fn := l.decProc, label := 7, pos := 1, env := (e₁c.insert 8 cur).insert 9 1 } :: rest } false := by
                        unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, cellAddr, Lir.dispWord, hmem2_r32]
                      have h1_b7_1 : Lir.step p { mem := mem2, ctx, stack := { fn := l.decProc, label := 7, pos := 1, env := (e₁c.insert 8 cur).insert 9 1 } :: rest } =
                          .next { mem := mem2, ctx, stack := { fn := l.decProc, label := 7, pos := 2, env := e₁d } :: rest } false := by
                        unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁d, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, cellAddr, Lir.dispWord, hmem2_r8]
                      have h1_b7_2 : Lir.step p { mem := mem2, ctx, stack := { fn := l.decProc, label := 7, pos := 2, env := e₁d } :: rest } =
                          .next { mem := mem2, ctx, stack := { fn := l.decProc, label := 8, pos := 0, env := e₁d } :: rest } false := by
                        unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁d, Lir.Arg.eval, w64_eq_iff, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.bindParams]
                      have h1_b8_0 : Lir.step p { mem := mem2, ctx, stack := { fn := l.decProc, label := 8, pos := 0, env := e₁d } :: rest } =
                          .next { mem := mem2, ctx, stack := { fn := l.decProc, label := 8, pos := 1, env := e₁d.insert 12 1 } :: rest } false := by
                        unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁d, Lir.Stmt.exec, Lir.Rhs.eval, Lir.Arg.eval, w64_sub]
                      have hmem2_r16 : mem2.read? .w64 (cur + 8 + 8) = mem.read? .w64 (cur + 16) := by
                        have haddr : cur + 8 + 8 = cur + UInt64.ofNat 16 := by
                          rw [UInt64.add_assoc]; rfl
                        rw [haddr]
                        have h1' := write_read_disjoint (a := cur) (o1 := 16) (o2 := 4) (w1 := .w64) (w2 := .w32)
                          (by simpa using hw2) (by decide) (by decide) (.inr (by decide))
                        have h2' := write_read_disjoint (a := cur) (o1 := 16) (o2 := 8) (w1 := .w64) (w2 := .w64)
                          (by simpa using hw1) (by decide) (by decide) (.inr (by decide))
                        exact h1'.trans h2'
                      cases hf1 : mem.read? .w64 (cur + 16) with
                      | error _ =>
                        have hmem2_err : mem2.read? .w64 (cur + 8 + 8) = .error _ := hmem2_r16.trans hf1
                        exact .rawStuckWithin (by omega) (star_reaches_stuck
                          (star_free h1_b2_0 (Sem.Star.trans h1_to_b5 (star_free h1_b5_1 (star_free h1_12_0 (star_free h1_12_1 (star_free h1_12_2 (star_free h1_12_3 (star_charge h1_12_4 (star_free h1_b1 (star_free h1_b6 (star_free h1_b7_0 (star_free h1_b7_1 (star_free h1_b7_2 (star_free h1_b8_0 (.refl _)))))))))))))))
                          (by unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁d, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, X86.Scale.word, Lir.dispWord, hmem2_err]))
                      | ok f1 =>
                        have hmem2_ok16 : mem2.read? .w64 (cur + 8 + 8) = .ok f1 := hmem2_r16.trans hf1
                        have h1_b8_1 : Lir.step p { mem := mem2, ctx, stack := { fn := l.decProc, label := 8, pos := 1, env := e₁d.insert 12 1 } :: rest } =
                            .next { mem := mem2, ctx, stack := { fn := l.decProc, label := 8, pos := 2, env := (e₁d.insert 12 1).insert 13 f1 } :: rest } false := by
                          unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁d, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, X86.Scale.word, Lir.dispWord, hmem2_ok16]
                        have h1_b8_2 : Lir.step p { mem := mem2, ctx, stack := { fn := l.decProc, label := 8, pos := 2, env := (e₁d.insert 12 1).insert 13 f1 } :: rest } =
                            .next { mem := mem2, ctx, stack := { fn := l.decProc, label := 8, pos := 3, env := ((e₁d.insert 12 1).insert 13 f1).insert 14 0 } :: rest } false := by
                          unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁d, Lir.Stmt.exec, Lir.Rhs.eval, Lir.Arg.eval, w64_sub]
                        obtain ⟨mem3, hw3⟩ := write_ok_of_writable_eq (write_writable hw2).symm ⟨mem2, hw2⟩ (val2 := 0)
                        have hmem3Eq : mem3 = mem1 := write32_write32_zero_id hmem1_r32 hw2 hw3
                        subst mem3
                        let e₁e := ((e₁d.insert 12 1).insert 13 f1).insert 14 0
                        have h1_b8_3 : Lir.step p { mem := mem2, ctx, stack := { fn := l.decProc, label := 8, pos := 3, env := e₁e } :: rest } =
                            .next { mem := mem1, ctx, stack := { fn := l.decProc, label := 8, pos := 4, env := e₁e } :: rest } false := by
                          unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁e, e₁d, Lir.Stmt.exec, Lir.Arg.eval, Lir.Addr.eval, cellAddr, Lir.dispWord, hw3]
                        let e₁f := (e₁e.insert 1 f1).insert 2 cur
                        have h1_b8_4 : Lir.step p { mem := mem1, ctx, stack := { fn := l.decProc, label := 8, pos := 4, env := e₁e } :: rest } =
                            .next { mem := mem1, ctx, stack := { fn := l.decProc, label := 1, pos := 0, env := e₁f } :: rest } true := by
                          unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁f, e₁e, e₁d, Lir.takeEdge, to, v, Lir.evalArgs, Lir.Arg.eval, Lir.bindParams]
                        have h2_b13_0 : Lir.step (install l p) { mem, ctx, stack := { fn := l.decProc, label := 13, pos := 0, env := e₂s.insert 22 f0 } :: rest } =
                            .next { mem, ctx, stack := { fn := l.decProc, label := 13, pos := 1, env := (e₂s.insert 22 f0).insert 23 f1 } :: rest } false := by
                          unfold Lir.step; simp [hfast, fastDec, e₂s, h20, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, cellAddr, Lir.dispWord, hf1]
                        have h1_to_b1f : Sem.Star (Lir.semStep p) { mem, ctx, stack := { fn := l.decProc, label := 2, pos := 1, env := e₁.insert 3 0 } :: rest } 2
                            { mem := mem1, ctx, stack := { fn := l.decProc, label := 1, pos := 0, env := e₁f } :: rest } :=
                          Sem.Star.trans h1_to_b5 (star_free h1_b5_1 (star_free h1_12_0 (star_free h1_12_1 (star_free h1_12_2 (star_free h1_12_3 (star_charge h1_12_4 (star_free h1_b1 (star_free h1_b6 (star_free h1_b7_0 (star_free h1_b7_1 (star_free h1_b7_2 (star_free h1_b8_0 (star_free h1_b8_1 (star_free h1_b8_2 (star_free h1_b8_3 (star_charge h1_b8_4 (.refl _)))))))))))))))))
                        by_cases hf1odd : (f1 &&& 1) != 0
                        · -- LEAF `Node(imm, imm)`!
                          have h1_b1f : Lir.step p { mem := mem1, ctx, stack := { fn := l.decProc, label := 1, pos := 0, env := e₁f } :: rest } =
                              .next { mem := mem1, ctx, stack := { fn := l.decProc, label := 6, pos := 0, env := e₁f.insert 8 cur } :: rest } false := by
                            unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁f, Lir.Arg.eval, w64_tnz_1, hf1odd, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.bindParams]
                          have h1_b6f : Lir.step p { mem := mem1, ctx, stack := { fn := l.decProc, label := 6, pos := 0, env := e₁f.insert 8 cur } :: rest } =
                              .next { mem := mem1, ctx, stack := { fn := l.decProc, label := 7, pos := 0, env := e₁f.insert 8 cur } :: rest } false := by
                            unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, Lir.Arg.eval, w64_eq_iff, hcurNe, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.bindParams]
                          have h1_b7f_0 : Lir.step p { mem := mem1, ctx, stack := { fn := l.decProc, label := 7, pos := 0, env := e₁f.insert 8 cur } :: rest } =
                              .next { mem := mem1, ctx, stack := { fn := l.decProc, label := 7, pos := 1, env := (e₁f.insert 8 cur).insert 9 0 } :: rest } false := by
                            unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, cellAddr, Lir.dispWord, hmem1_r32]
                          have h1_b7f_1 : Lir.step p { mem := mem1, ctx, stack := { fn := l.decProc, label := 7, pos := 1, env := (e₁f.insert 8 cur).insert 9 0 } :: rest } =
                              .next { mem := mem1, ctx, stack := { fn := l.decProc, label := 7, pos := 2, env := ((e₁f.insert 8 cur).insert 9 0).insert 10 2 } :: rest } false := by
                            unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, cellAddr, Lir.dispWord, hmem1_r8]
                          have h1_b7f_2 : Lir.step p { mem := mem1, ctx, stack := { fn := l.decProc, label := 7, pos := 2, env := ((e₁f.insert 8 cur).insert 9 0).insert 10 2 } :: rest } =
                              .next { mem := mem1, ctx, stack := { fn := l.decProc, label := 9, pos := 0, env := ((e₁f.insert 8 cur).insert 9 0).insert 10 2 } :: rest } false := by
                            unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, Lir.Arg.eval, w64_eq_iff, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.bindParams]
                          have h2_b13_1 : Lir.step (install l p) { mem, ctx, stack := { fn := l.decProc, label := 13, pos := 1, env := (e₂s.insert 22 f0).insert 23 f1 } :: rest } =
                              .next { mem, ctx, stack := { fn := l.decProc, label := 19, pos := 0, env := (e₂s.insert 22 f0).insert 23 f1 } :: rest } false := by
                            unfold Lir.step; simp [hfast, fastDec, Lir.Arg.eval, w64_tnz_1, hf1odd, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.bindParams]
                          exact doLeafRecycle (by omega) (by simp) (by simp [e₂s, h20]) (by simp [e₂s, h21]) hw1
                            (Sem.Star.trans h1_to_b1f (star_free h1_b1f (star_free h1_b6f (star_free h1_b7f_0 (star_free h1_b7f_1 (star_free h1_b7f_2 (.refl _)))))))
                            (Sem.Star.trans h2_to_b5 (star_free h2_b5_1 (star_free h2_b11_0 (star_free h2_b11_1 (star_free h2_b12 (star_free h2_b13_0 (star_free h2_b13_1 (.refl _))))))))
                            ⟨f0, hf0⟩
                        · -- `f1` is pointer (`b20` -> `b2(f1, cur)` with `mem1`!)
                          have hf1ev : ((f1 &&& 1) != 0) = false := Bool.eq_false_iff.mpr hf1odd
                          have h1_b1f : Lir.step p { mem := mem1, ctx, stack := { fn := l.decProc, label := 1, pos := 0, env := e₁f } :: rest } =
                              .next { mem := mem1, ctx, stack := { fn := l.decProc, label := 2, pos := 0, env := e₁f } :: rest } false := by
                            unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁f, Lir.Arg.eval, w64_tnz_1, hf1ev, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.bindParams]
                          have h2_b13_1 : Lir.step (install l p) { mem, ctx, stack := { fn := l.decProc, label := 13, pos := 1, env := (e₂s.insert 22 f0).insert 23 f1 } :: rest } =
                              .next { mem, ctx, stack := { fn := l.decProc, label := 20, pos := 0, env := ((e₂s.insert 22 f0).insert 23 f1).insert 26 f1 } :: rest } false := by
                            unfold Lir.step; simp [hfast, fastDec, Lir.Arg.eval, w64_tnz_1, hf1ev, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.bindParams]
                          let e₂g := ((e₂s.insert 22 f0).insert 23 f1).insert 26 f1
                          have h2_b20_0 : Lir.step (install l p) { mem, ctx, stack := { fn := l.decProc, label := 20, pos := 0, env := e₂g } :: rest } =
                              .next { mem := mem1, ctx, stack := { fn := l.decProc, label := 20, pos := 1, env := e₂g } :: rest } false := by
                            unfold Lir.step; simp [hfast, fastDec, e₂g, e₂s, h20, h21, Lir.Stmt.exec, Lir.Arg.eval, Lir.Addr.eval, cellAddr, Lir.dispWord, hw1]
                          have h2_b20_1 : Lir.step (install l p) { mem := mem1, ctx, stack := { fn := l.decProc, label := 20, pos := 1, env := e₂g } :: rest } =
                              .next { mem := mem1, ctx, stack := { fn := l.decProc, label := 2, pos := 0, env := (e₂g.insert 20 f1).insert 21 cur } :: rest } true := by
                            unfold Lir.step; simp [hfast, fastDec, e₂g, e₂s, h20, Lir.takeEdge, to, v, Lir.evalArgs, Lir.Arg.eval, Lir.bindParams]
                          exact .sync (Lir.semStep_next.mpr h1_b2_0) (Sem.Star.trans h1_to_b1f (star_free h1_b1f (.refl _)))
                            (Lir.semStep_next.mpr h2_b2_0)
                            (Sem.Star.trans h2_to_b5 (star_free h2_b5_1 (star_free h2_b11_0 (star_free h2_b11_1 (star_free h2_b12 (star_free h2_b13_0 (star_free h2_b13_1 (star_free h2_b20_0 (star_charge h2_b20_1 (.refl _))))))))))
                            (by omega) ⟨rfl, rfl, .decTop (.b2 (cur := f1) (par := cur) (by simp [e₁f]) (by simp [e₁f]) (by simp) (by simp)) hno⟩
              · -- `v5 = 2`, `f0` is pointer (`b18` -> `b2(f0, cur)`)
                have hf0ev : ((f0 &&& 1) != 0) = false := Bool.eq_false_iff.mpr hf0odd
                have h2_b11_1 : Lir.step (install l p) { mem, ctx, stack := { fn := l.decProc, label := 11, pos := 1, env := e₂s.insert 22 f0 } :: rest } =
                    .next { mem, ctx, stack := { fn := l.decProc, label := 18, pos := 0, env := e₂s.insert 22 f0 } :: rest } false := by
                  unfold Lir.step; simp [hfast, fastDec, Lir.Arg.eval, w64_tnz_1, hf0ev, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.bindParams]
                cases hw1 : mem.write? .w64 (cur + 8) par with
                | error _ =>
                  exact .rawStuckWithin (by omega) (star_reaches_stuck
                    (star_free h1_b2_0 (Sem.Star.trans h1_to_b5 (star_free h1_b5_1 (star_free h1_12_0 (star_free h1_12_1 (.refl _))))))
                    (by unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁s, h1, h2, Lir.Stmt.exec, Lir.Arg.eval, Lir.Addr.eval, cellAddr, Lir.dispWord, hw1]))
                | ok mem1 =>
                  have h1_12_2 : Lir.step p { mem, ctx, stack := { fn := l.decProc, label := 12, pos := 2, env := (e₁s.insert 6 f0).insert 7 1 } :: rest } =
                      .next { mem := mem1, ctx, stack := { fn := l.decProc, label := 12, pos := 3, env := (e₁s.insert 6 f0).insert 7 1 } :: rest } false := by
                    unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁s, h1, h2, Lir.Stmt.exec, Lir.Arg.eval, Lir.Addr.eval, cellAddr, Lir.dispWord, hw1]
                  cases hw2 : mem1.write? .w32 (cur + 4) 1 with
                  | error _ =>
                    exact .rawStuckWithin (by omega) (star_reaches_stuck
                      (star_free h1_b2_0 (Sem.Star.trans h1_to_b5 (star_free h1_b5_1 (star_free h1_12_0 (star_free h1_12_1 (star_free h1_12_2 (.refl _)))))))
                      (by unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁s, h1, Lir.Stmt.exec, Lir.Arg.eval, Lir.Addr.eval, cellAddr, Lir.dispWord, hw2]))
                  | ok mem2 =>
                    have h1_12_3 : Lir.step p { mem := mem1, ctx, stack := { fn := l.decProc, label := 12, pos := 3, env := (e₁s.insert 6 f0).insert 7 1 } :: rest } =
                        .next { mem := mem2, ctx, stack := { fn := l.decProc, label := 12, pos := 4, env := (e₁s.insert 6 f0).insert 7 1 } :: rest } false := by
                      unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁s, h1, Lir.Stmt.exec, Lir.Arg.eval, Lir.Addr.eval, cellAddr, Lir.dispWord, hw2]
                    let e₁c := (((e₁s.insert 6 f0).insert 7 1).insert 1 f0).insert 2 cur
                    have h1_12_4 : Lir.step p { mem := mem2, ctx, stack := { fn := l.decProc, label := 12, pos := 4, env := (e₁s.insert 6 f0).insert 7 1 } :: rest } =
                        .next { mem := mem2, ctx, stack := { fn := l.decProc, label := 1, pos := 0, env := e₁c } :: rest } true := by
                      unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁c, e₁s, h1, Lir.takeEdge, to, v, Lir.evalArgs, Lir.Arg.eval, Lir.bindParams]
                    have h1_b1 : Lir.step p { mem := mem2, ctx, stack := { fn := l.decProc, label := 1, pos := 0, env := e₁c } :: rest } =
                        .next { mem := mem2, ctx, stack := { fn := l.decProc, label := 2, pos := 0, env := e₁c } :: rest } false := by
                      unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁c, Lir.Arg.eval, w64_tnz_1, hf0ev, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.bindParams]
                    let e₂g := e₂s.insert 22 f0
                    have h2_b18_0 : Lir.step (install l p) { mem, ctx, stack := { fn := l.decProc, label := 18, pos := 0, env := e₂g } :: rest } =
                        .next { mem := mem1, ctx, stack := { fn := l.decProc, label := 18, pos := 1, env := e₂g } :: rest } false := by
                      unfold Lir.step; simp [hfast, fastDec, e₂g, e₂s, h20, h21, Lir.Stmt.exec, Lir.Arg.eval, Lir.Addr.eval, cellAddr, Lir.dispWord, hw1]
                    have h2_b18_1 : Lir.step (install l p) { mem := mem1, ctx, stack := { fn := l.decProc, label := 18, pos := 1, env := e₂g } :: rest } =
                        .next { mem := mem2, ctx, stack := { fn := l.decProc, label := 18, pos := 2, env := e₂g } :: rest } false := by
                      unfold Lir.step; simp [hfast, fastDec, e₂g, e₂s, h20, Lir.Stmt.exec, Lir.Arg.eval, Lir.Addr.eval, cellAddr, Lir.dispWord, hw2]
                    have h2_b18_2 : Lir.step (install l p) { mem := mem2, ctx, stack := { fn := l.decProc, label := 18, pos := 2, env := e₂g } :: rest } =
                        .next { mem := mem2, ctx, stack := { fn := l.decProc, label := 2, pos := 0, env := (e₂g.insert 20 f0).insert 21 cur } :: rest } true := by
                      unfold Lir.step; simp [hfast, fastDec, e₂g, e₂s, h20, Lir.takeEdge, to, v, Lir.evalArgs, Lir.Arg.eval, Lir.bindParams]
                    exact .sync (Lir.semStep_next.mpr h1_b2_0)
                      (Sem.Star.trans h1_to_b5 (star_free h1_b5_1 (star_free h1_12_0 (star_free h1_12_1 (star_free h1_12_2 (star_free h1_12_3 (star_charge h1_12_4 (star_free h1_b1 (.refl _)))))))))
                      (Lir.semStep_next.mpr h2_b2_0)
                      (Sem.Star.trans h2_to_b5 (star_free h2_b5_1 (star_free h2_b11_0 (star_free h2_b11_1 (star_free h2_b18_0 (star_free h2_b18_1 (star_charge h2_b18_2 (.refl _))))))))
                      (by omega) ⟨rfl, rfl, .decTop (.b2 (cur := f0) (par := cur) (by simp [e₁c]) (by simp [e₁c]) (by simp) (by simp)) hno⟩
          · -- `v5 ≠ 2`
            have hv5ne2 : (v5 == 2) = false := beq_false_of_ne hv5_2
            have h2_b5_1 : Lir.step (install l p) { mem, ctx, stack := { fn := l.decProc, label := 5, pos := 1, env := e₂s } :: rest } =
                .next { mem, ctx, stack := { fn := l.decProc, label := 14, pos := 0, env := e₂s } :: rest } false := by
              unfold Lir.step; simp [hfast, fastDec, e₂s, Lir.Arg.eval, w64_eq_iff, hv5ne2, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.bindParams]
            by_cases hv5_0 : v5 = 0
            · subst hv5_0
              have h1_b5_1 : Lir.step p { mem, ctx, stack := { fn := l.decProc, label := 5, pos := 1, env := e₁s } :: rest } =
                  .next { mem, ctx, stack := { fn := l.decProc, label := 11, pos := 0, env := e₁s } :: rest } false := by
                unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁s, Lir.Arg.eval, w64_eq_iff, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.bindParams]
              have h2_b14 : Lir.step (install l p) { mem, ctx, stack := { fn := l.decProc, label := 14, pos := 0, env := e₂s } :: rest } =
                  .next { mem, ctx, stack := { fn := l.decProc, label := 21, pos := 0, env := e₂s } :: rest } false := by
                unfold Lir.step; simp [hfast, fastDec, e₂s, Lir.Arg.eval, w64_eq_iff, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.bindParams]
              cases hcls : mem.read? .w8 (cur + 1) with
              | error _ =>
                exact .rawStuckWithin (by omega) (star_reaches_stuck
                  (star_free h1_b2_0 (Sem.Star.trans h1_to_b5 (star_free h1_b5_1 (.refl _))))
                  (by unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁s, h1, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, cellAddr, Lir.dispWord, hcls]))
              | ok cls =>
                have h1_11_0 : Lir.step p { mem, ctx, stack := { fn := l.decProc, label := 11, pos := 0, env := e₁s } :: rest } =
                    .next { mem, ctx, stack := { fn := l.decProc, label := 11, pos := 1, env := e₁s.insert 17 cls } :: rest } false := by
                  unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁s, h1, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, cellAddr, Lir.dispWord, hcls]
                have h2_21_0 : Lir.step (install l p) { mem, ctx, stack := { fn := l.decProc, label := 21, pos := 0, env := e₂s } :: rest } =
                    .next { mem, ctx, stack := { fn := l.decProc, label := 21, pos := 1, env := e₂s.insert 17 cls } :: rest } false := by
                  unfold Lir.step; simp [hfast, fastDec, e₂s, h20, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, cellAddr, Lir.dispWord, hcls]
                cases hold : mem.read? .w64 (ctx + cls * 8) with
                | error _ =>
                  exact .rawStuckWithin (by omega) (star_reaches_stuck
                    (star_free h1_b2_0 (Sem.Star.trans h1_to_b5 (star_free h1_b5_1 (star_free h1_11_0 (.refl _)))))
                    (by unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, X86.Scale.word, Lir.dispWord, hold]))
                | ok old =>
                  have h1_11_1 : Lir.step p { mem, ctx, stack := { fn := l.decProc, label := 11, pos := 1, env := e₁s.insert 17 cls } :: rest } =
                      .next { mem, ctx, stack := { fn := l.decProc, label := 11, pos := 2, env := (e₁s.insert 17 cls).insert 18 old } :: rest } false := by
                    unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, X86.Scale.word, Lir.dispWord, hold]
                  have h2_21_1 : Lir.step (install l p) { mem, ctx, stack := { fn := l.decProc, label := 21, pos := 1, env := e₂s.insert 17 cls } :: rest } =
                      .next { mem, ctx, stack := { fn := l.decProc, label := 21, pos := 2, env := (e₂s.insert 17 cls).insert 18 old } :: rest } false := by
                    unfold Lir.step; simp [hfast, fastDec, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, X86.Scale.word, Lir.dispWord, hold]
                  cases hw1 : mem.write? .w64 cur old with
                  | error _ =>
                    exact .rawStuckWithin (by omega) (star_reaches_stuck
                      (star_free h1_b2_0 (Sem.Star.trans h1_to_b5 (star_free h1_b5_1 (star_free h1_11_0 (star_free h1_11_1 (.refl _))))))
                      (by unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁s, h1, Lir.Stmt.exec, Lir.Arg.eval, Lir.Addr.eval, cellAddr, Lir.dispWord, hw1]))
                  | ok mem1 =>
                    have h1_11_2 : Lir.step p { mem, ctx, stack := { fn := l.decProc, label := 11, pos := 2, env := (e₁s.insert 17 cls).insert 18 old } :: rest } =
                        .next { mem := mem1, ctx, stack := { fn := l.decProc, label := 11, pos := 3, env := (e₁s.insert 17 cls).insert 18 old } :: rest } false := by
                      unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁s, h1, Lir.Stmt.exec, Lir.Arg.eval, Lir.Addr.eval, cellAddr, Lir.dispWord, hw1]
                    have h2_21_2 : Lir.step (install l p) { mem, ctx, stack := { fn := l.decProc, label := 21, pos := 2, env := (e₂s.insert 17 cls).insert 18 old } :: rest } =
                        .next { mem := mem1, ctx, stack := { fn := l.decProc, label := 21, pos := 3, env := (e₂s.insert 17 cls).insert 18 old } :: rest } false := by
                      unfold Lir.step; simp [hfast, fastDec, e₂s, h20, Lir.Stmt.exec, Lir.Arg.eval, Lir.Addr.eval, cellAddr, Lir.dispWord, hw1]
                    cases hw2 : mem1.write? .w64 (ctx + cls * 8) cur with
                    | error _ =>
                      exact .rawStuckWithin (by omega) (star_reaches_stuck
                        (star_free h1_b2_0 (Sem.Star.trans h1_to_b5 (star_free h1_b5_1 (star_free h1_11_0 (star_free h1_11_1 (star_free h1_11_2 (.refl _)))))))
                        (by unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁s, h1, Lir.Stmt.exec, Lir.Arg.eval, Lir.Addr.eval, X86.Scale.word, Lir.dispWord, hw2]))
                    | ok mem2 =>
                      have h1_11_3 : Lir.step p { mem := mem1, ctx, stack := { fn := l.decProc, label := 11, pos := 3, env := (e₁s.insert 17 cls).insert 18 old } :: rest } =
                          .next { mem := mem2, ctx, stack := { fn := l.decProc, label := 11, pos := 4, env := (e₁s.insert 17 cls).insert 18 old } :: rest } false := by
                        unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁s, h1, Lir.Stmt.exec, Lir.Arg.eval, Lir.Addr.eval, X86.Scale.word, Lir.dispWord, hw2]
                      have h1_11_4 : Lir.step p { mem := mem2, ctx, stack := { fn := l.decProc, label := 11, pos := 4, env := (e₁s.insert 17 cls).insert 18 old } :: rest } =
                          .next { mem := mem2, ctx, stack := { fn := l.decProc, label := 6, pos := 0, env := ((e₁s.insert 17 cls).insert 18 old).insert 8 par } :: rest } true := by
                        unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁s, h2, Lir.takeEdge, to, v, Lir.evalArgs, Lir.Arg.eval, Lir.bindParams]
                      have h2_21_3 : Lir.step (install l p) { mem := mem1, ctx, stack := { fn := l.decProc, label := 21, pos := 3, env := (e₂s.insert 17 cls).insert 18 old } :: rest } =
                          .next { mem := mem2, ctx, stack := { fn := l.decProc, label := 21, pos := 4, env := (e₂s.insert 17 cls).insert 18 old } :: rest } false := by
                        unfold Lir.step; simp [hfast, fastDec, e₂s, h20, Lir.Stmt.exec, Lir.Arg.eval, Lir.Addr.eval, X86.Scale.word, Lir.dispWord, hw2]
                      have h2_21_4 : Lir.step (install l p) { mem := mem2, ctx, stack := { fn := l.decProc, label := 21, pos := 4, env := (e₂s.insert 17 cls).insert 18 old } :: rest } =
                          .next { mem := mem2, ctx, stack := { fn := l.decProc, label := 6, pos := 0, env := ((e₂s.insert 17 cls).insert 18 old).insert 8 par } :: rest } true := by
                        unfold Lir.step; simp [hfast, fastDec, e₂s, h21, Lir.takeEdge, to, v, Lir.evalArgs, Lir.Arg.eval, Lir.bindParams]
                      exact .sync (Lir.semStep_next.mpr h1_b2_0)
                        (Sem.Star.trans h1_to_b5 (star_free h1_b5_1 (star_free h1_11_0 (star_free h1_11_1 (star_free h1_11_2 (star_free h1_11_3 (star_charge h1_11_4 (.refl _))))))))
                        (Lir.semStep_next.mpr h2_b2_0)
                        (Sem.Star.trans h2_to_b5 (star_free h2_b5_1 (star_free h2_b14 (star_free h2_21_0 (star_free h2_21_1 (star_free h2_21_2 (star_free h2_21_3 (star_charge h2_21_4 (.refl _)))))))))
                        (by omega) ⟨rfl, rfl, .decTop (.b6 (par := par) (by simp) (by simp)) hno⟩
            · -- `v5 ≠ 0` and `v5 ≠ 2`
              have hv5ne0 : (v5 == 0) = false := beq_false_of_ne hv5_0
              have h1_b5_1 : Lir.step p { mem, ctx, stack := { fn := l.decProc, label := 5, pos := 1, env := e₁s } :: rest } =
                  .next { mem, ctx, stack := { fn := l.decProc, label := 12, pos := 0, env := e₁s } :: rest } false := by
                unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁s, Lir.Arg.eval, w64_eq_iff, hv5ne0, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.bindParams]
              have h2_b14 : Lir.step (install l p) { mem, ctx, stack := { fn := l.decProc, label := 14, pos := 0, env := e₂s } :: rest } =
                  .next { mem, ctx, stack := { fn := l.decProc, label := 15, pos := 0, env := e₂s } :: rest } false := by
                unfold Lir.step; simp [hfast, fastDec, e₂s, Lir.Arg.eval, w64_eq_iff, hv5ne0, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.bindParams]
              by_cases hv5_1 : v5 = 1
              · subst hv5_1
                have h2_b15 : Lir.step (install l p) { mem, ctx, stack := { fn := l.decProc, label := 15, pos := 0, env := e₂s } :: rest } =
                    .next { mem, ctx, stack := { fn := l.decProc, label := 16, pos := 0, env := e₂s } :: rest } false := by
                  unfold Lir.step; simp [hfast, fastDec, e₂s, Lir.Arg.eval, w64_eq_iff, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.bindParams]
                cases hf0 : mem.read? .w64 (cur + 8) with
                | error _ =>
                  exact .rawStuckWithin (by omega) (star_reaches_stuck
                    (star_free h1_b2_0 (Sem.Star.trans h1_to_b5 (star_free h1_b5_1 (.refl _))))
                    (by unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁s, h1, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, cellAddr, Lir.dispWord, hf0]))
                | ok f0 =>
                  have h1_12_0 : Lir.step p { mem, ctx, stack := { fn := l.decProc, label := 12, pos := 0, env := e₁s } :: rest } =
                      .next { mem, ctx, stack := { fn := l.decProc, label := 12, pos := 1, env := e₁s.insert 6 f0 } :: rest } false := by
                    unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁s, h1, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, cellAddr, Lir.dispWord, hf0]
                  have h1_12_1 : Lir.step p { mem, ctx, stack := { fn := l.decProc, label := 12, pos := 1, env := e₁s.insert 6 f0 } :: rest } =
                      .next { mem, ctx, stack := { fn := l.decProc, label := 12, pos := 2, env := (e₁s.insert 6 f0).insert 7 0 } :: rest } false := by
                    unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁s, Lir.Stmt.exec, Lir.Rhs.eval, Lir.Arg.eval, w64_sub]
                  have h2_b16_0 : Lir.step (install l p) { mem, ctx, stack := { fn := l.decProc, label := 16, pos := 0, env := e₂s } :: rest } =
                      .next { mem, ctx, stack := { fn := l.decProc, label := 16, pos := 1, env := e₂s.insert 27 f0 } :: rest } false := by
                    unfold Lir.step; simp [hfast, fastDec, e₂s, h20, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, cellAddr, Lir.dispWord, hf0]
                  cases hw1 : mem.write? .w64 (cur + 8) par with
                  | error _ =>
                    exact .rawStuckWithin (by omega) (star_reaches_stuck
                      (star_free h1_b2_0 (Sem.Star.trans h1_to_b5 (star_free h1_b5_1 (star_free h1_12_0 (star_free h1_12_1 (.refl _))))))
                      (by unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁s, h1, h2, Lir.Stmt.exec, Lir.Arg.eval, Lir.Addr.eval, cellAddr, Lir.dispWord, hw1]))
                  | ok mem1 =>
                    have h1_12_2 : Lir.step p { mem, ctx, stack := { fn := l.decProc, label := 12, pos := 2, env := (e₁s.insert 6 f0).insert 7 0 } :: rest } =
                        .next { mem := mem1, ctx, stack := { fn := l.decProc, label := 12, pos := 3, env := (e₁s.insert 6 f0).insert 7 0 } :: rest } false := by
                      unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁s, h1, h2, Lir.Stmt.exec, Lir.Arg.eval, Lir.Addr.eval, cellAddr, Lir.dispWord, hw1]
                    cases hw2 : mem1.write? .w32 (cur + 4) 0 with
                    | error _ =>
                      exact .rawStuckWithin (by omega) (star_reaches_stuck
                        (star_free h1_b2_0 (Sem.Star.trans h1_to_b5 (star_free h1_b5_1 (star_free h1_12_0 (star_free h1_12_1 (star_free h1_12_2 (.refl _)))))))
                        (by unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁s, h1, Lir.Stmt.exec, Lir.Arg.eval, Lir.Addr.eval, cellAddr, Lir.dispWord, hw2]))
                    | ok mem2 =>
                      have hmem1_r32 : mem1.read? .w32 (cur + 4) = .ok 0 := by
                        have h := write_read_disjoint (a := cur) (o1 := 4) (o2 := 8) (w1 := .w32) (w2 := .w64)
                          (by simpa using hw1) (by decide) (by decide) (.inl (by decide))
                        simpa using h.trans hv3
                      have hmem2Eq : mem2 = mem1 := write32_zero_id hmem1_r32 hw2
                      subst mem2
                      have h1_12_3 : Lir.step p { mem := mem1, ctx, stack := { fn := l.decProc, label := 12, pos := 3, env := (e₁s.insert 6 f0).insert 7 0 } :: rest } =
                          .next { mem := mem1, ctx, stack := { fn := l.decProc, label := 12, pos := 4, env := (e₁s.insert 6 f0).insert 7 0 } :: rest } false := by
                        unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁s, h1, Lir.Stmt.exec, Lir.Arg.eval, Lir.Addr.eval, cellAddr, Lir.dispWord, hw2]
                      let e₁c := (((e₁s.insert 6 f0).insert 7 0).insert 1 f0).insert 2 cur
                      have h1_12_4 : Lir.step p { mem := mem1, ctx, stack := { fn := l.decProc, label := 12, pos := 4, env := (e₁s.insert 6 f0).insert 7 0 } :: rest } =
                          .next { mem := mem1, ctx, stack := { fn := l.decProc, label := 1, pos := 0, env := e₁c } :: rest } true := by
                        unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁c, e₁s, h1, Lir.takeEdge, to, v, Lir.evalArgs, Lir.Arg.eval, Lir.bindParams]
                      by_cases hf0odd : (f0 &&& 1) != 0
                      · have h2_b16_1 : Lir.step (install l p) { mem, ctx, stack := { fn := l.decProc, label := 16, pos := 1, env := e₂s.insert 27 f0 } :: rest } =
                            .next { mem, ctx, stack := { fn := l.decProc, label := 17, pos := 0, env := e₂s.insert 27 f0 } :: rest } false := by
                          unfold Lir.step; simp [hfast, fastDec, Lir.Arg.eval, w64_tnz_1, hf0odd, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.bindParams]
                        by_cases hcur0 : cur = 0
                        · subst hcur0
                          have hf0' : mem.read? .w64 8 = .ok f0 := by simpa using hf0
                          have hw1' : mem.write? .w64 8 par = .ok mem1 := by simpa using hw1
                          have hw2' : mem1.write? .w32 4 0 = .ok mem1 := by simpa using hw2
                          let e2g := e₂s.insert 27 f0
                          have h2_b17 : Lir.step (install l p) { mem, ctx, stack := { fn := l.decProc, label := 17, pos := 0, env := e2g } :: rest } =
                              .next { mem, ctx, stack := { fn := l.decProc, label := 24, pos := 0, env := e2g } :: rest } false := by
                            unfold Lir.step; simp [hfast, fastDec, e2g, e₂s, h20, Lir.Arg.eval, w64_eq_iff, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.bindParams]
                          have h2_24_0 : Lir.step (install l p) { mem, ctx, stack := { fn := l.decProc, label := 24, pos := 0, env := e2g } :: rest } =
                              .next { mem, ctx, stack := { fn := l.decProc, label := 24, pos := 1, env := e2g.insert 6 f0 } :: rest } false := by
                            unfold Lir.step; simp [hfast, fastDec, e2g, e₂s, h20, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, cellAddr, Lir.dispWord, hf0']
                          have h2_24_1 : Lir.step (install l p) { mem, ctx, stack := { fn := l.decProc, label := 24, pos := 1, env := e2g.insert 6 f0 } :: rest } =
                              .next { mem, ctx, stack := { fn := l.decProc, label := 24, pos := 2, env := (e2g.insert 6 f0).insert 7 0 } :: rest } false := by
                            unfold Lir.step; simp [hfast, fastDec, e2g, e₂s, Lir.Stmt.exec, Lir.Rhs.eval, Lir.Arg.eval, w64_sub]
                          have h2_24_2 : Lir.step (install l p) { mem, ctx, stack := { fn := l.decProc, label := 24, pos := 2, env := (e2g.insert 6 f0).insert 7 0 } :: rest } =
                              .next { mem := mem1, ctx, stack := { fn := l.decProc, label := 24, pos := 3, env := (e2g.insert 6 f0).insert 7 0 } :: rest } false := by
                            unfold Lir.step; simp [hfast, fastDec, e2g, e₂s, h20, h21, Lir.Stmt.exec, Lir.Arg.eval, Lir.Addr.eval, cellAddr, Lir.dispWord, hw1']
                          have h2_24_3 : Lir.step (install l p) { mem := mem1, ctx, stack := { fn := l.decProc, label := 24, pos := 3, env := (e2g.insert 6 f0).insert 7 0 } :: rest } =
                              .next { mem := mem1, ctx, stack := { fn := l.decProc, label := 24, pos := 4, env := (e2g.insert 6 f0).insert 7 0 } :: rest } false := by
                            unfold Lir.step; simp [hfast, fastDec, e2g, e₂s, h20, Lir.Stmt.exec, Lir.Arg.eval, Lir.Addr.eval, cellAddr, Lir.dispWord, hw2']
                          have h2_24_4 : Lir.step (install l p) { mem := mem1, ctx, stack := { fn := l.decProc, label := 24, pos := 4, env := (e2g.insert 6 f0).insert 7 0 } :: rest } =
                              .next { mem := mem1, ctx, stack := { fn := l.decProc, label := 1, pos := 0, env := (((e2g.insert 6 f0).insert 7 0).insert 1 f0).insert 2 0 } :: rest } true := by
                            unfold Lir.step; simp [hfast, fastDec, e2g, e₂s, h20, Lir.takeEdge, to, v, Lir.evalArgs, Lir.Arg.eval, Lir.bindParams]
                          exact .sync (Lir.semStep_next.mpr h1_b2_0)
                            (Sem.Star.trans h1_to_b5 (star_free h1_b5_1 (star_free h1_12_0 (star_free h1_12_1 (star_free h1_12_2 (star_free h1_12_3 (star_charge h1_12_4 (.refl _))))))))
                            (Lir.semStep_next.mpr h2_b2_0)
                            (Sem.Star.trans h2_to_b5 (star_free h2_b5_1 (star_free h2_b14 (star_free h2_b15 (star_free h2_b16_0 (star_free h2_b16_1 (star_free h2_b17 (star_free h2_24_0 (star_free h2_24_1 (star_free h2_24_2 (star_free h2_24_3 (star_charge h2_24_4 (.refl _)))))))))))))
                            (by omega) ⟨rfl, rfl, .decTop (.b1 (cur := f0) (par := 0) (by simp [e₁c]) (by simp [e₁c]) (by simp) (by simp)) hno⟩
                        · -- `v5 = 1`, `f0` odd, `cur ≠ 0`: fast leaf recycle `b19`!
                          have hcurNe : (cur == 0) = false := beq_false_of_ne hcur0
                          have hmem1_r8 : mem1.read? .w8 cur = .ok 1 := by
                            have h := write_read_disjoint (a := cur) (o1 := 0) (o2 := 8) (w1 := .w8) (w2 := .w64)
                              (by simpa using hw1) (by decide) (by decide) (.inl (by decide))
                            simpa using h.trans (by simpa using hv5)
                          have h1_b1 : Lir.step p { mem := mem1, ctx, stack := { fn := l.decProc, label := 1, pos := 0, env := e₁c } :: rest } =
                              .next { mem := mem1, ctx, stack := { fn := l.decProc, label := 6, pos := 0, env := e₁c.insert 8 cur } :: rest } false := by
                            unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁c, Lir.Arg.eval, w64_tnz_1, hf0odd, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.bindParams]
                          have h1_b6 : Lir.step p { mem := mem1, ctx, stack := { fn := l.decProc, label := 6, pos := 0, env := e₁c.insert 8 cur } :: rest } =
                              .next { mem := mem1, ctx, stack := { fn := l.decProc, label := 7, pos := 0, env := e₁c.insert 8 cur } :: rest } false := by
                            unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, Lir.Arg.eval, w64_eq_iff, hcurNe, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.bindParams]
                          have h1_b7_0 : Lir.step p { mem := mem1, ctx, stack := { fn := l.decProc, label := 7, pos := 0, env := e₁c.insert 8 cur } :: rest } =
                              .next { mem := mem1, ctx, stack := { fn := l.decProc, label := 7, pos := 1, env := (e₁c.insert 8 cur).insert 9 0 } :: rest } false := by
                            unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, cellAddr, Lir.dispWord, hmem1_r32]
                          have h1_b7_1 : Lir.step p { mem := mem1, ctx, stack := { fn := l.decProc, label := 7, pos := 1, env := (e₁c.insert 8 cur).insert 9 0 } :: rest } =
                              .next { mem := mem1, ctx, stack := { fn := l.decProc, label := 7, pos := 2, env := ((e₁c.insert 8 cur).insert 9 0).insert 10 1 } :: rest } false := by
                            unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, Lir.Stmt.exec, Lir.Rhs.eval, Lir.loadWord, Lir.Addr.eval, cellAddr, Lir.dispWord, hmem1_r8]
                          have h1_b7_2 : Lir.step p { mem := mem1, ctx, stack := { fn := l.decProc, label := 7, pos := 2, env := ((e₁c.insert 8 cur).insert 9 0).insert 10 1 } :: rest } =
                              .next { mem := mem1, ctx, stack := { fn := l.decProc, label := 9, pos := 0, env := ((e₁c.insert 8 cur).insert 9 0).insert 10 1 } :: rest } false := by
                            unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, Lir.Arg.eval, w64_eq_iff, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.bindParams]
                          have h2_b17 : Lir.step (install l p) { mem, ctx, stack := { fn := l.decProc, label := 17, pos := 0, env := e₂s.insert 27 f0 } :: rest } =
                              .next { mem, ctx, stack := { fn := l.decProc, label := 19, pos := 0, env := e₂s.insert 27 f0 } :: rest } false := by
                            unfold Lir.step; simp [hfast, fastDec, e₂s, h20, Lir.Arg.eval, w64_eq_iff, hcurNe, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.bindParams]
                          exact doLeafRecycle (by omega) (by simp) (by simp [e₂s, h20]) (by simp [e₂s, h21]) hw1
                            (Sem.Star.trans h1_to_b5 (star_free h1_b5_1 (star_free h1_12_0 (star_free h1_12_1 (star_free h1_12_2 (star_free h1_12_3 (star_charge h1_12_4 (star_free h1_b1 (star_free h1_b6 (star_free h1_b7_0 (star_free h1_b7_1 (star_free h1_b7_2 (.refl _)))))))))))))
                            (Sem.Star.trans h2_to_b5 (star_free h2_b5_1 (star_free h2_b14 (star_free h2_b15 (star_free h2_b16_0 (star_free h2_b16_1 (star_free h2_b17 (.refl _))))))))
                            ⟨f0, hf0⟩
                      · -- `v5 = 1`, `f0` is pointer (`b20` -> `b2(f0, cur)` with `mem1`!)
                        have hf0ev : ((f0 &&& 1) != 0) = false := Bool.eq_false_iff.mpr hf0odd
                        have h1_b1 : Lir.step p { mem := mem1, ctx, stack := { fn := l.decProc, label := 1, pos := 0, env := e₁c } :: rest } =
                            .next { mem := mem1, ctx, stack := { fn := l.decProc, label := 2, pos := 0, env := e₁c } :: rest } false := by
                          unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, e₁c, Lir.Arg.eval, w64_tnz_1, hf0ev, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.bindParams]
                        have h2_b16_1 : Lir.step (install l p) { mem, ctx, stack := { fn := l.decProc, label := 16, pos := 1, env := e₂s.insert 27 f0 } :: rest } =
                            .next { mem, ctx, stack := { fn := l.decProc, label := 20, pos := 0, env := (e₂s.insert 27 f0).insert 26 f0 } :: rest } false := by
                          unfold Lir.step; simp [hfast, fastDec, Lir.Arg.eval, w64_tnz_1, hf0ev, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.bindParams]
                        let e₂g := (e₂s.insert 27 f0).insert 26 f0
                        have h2_b20_0 : Lir.step (install l p) { mem, ctx, stack := { fn := l.decProc, label := 20, pos := 0, env := e₂g } :: rest } =
                            .next { mem := mem1, ctx, stack := { fn := l.decProc, label := 20, pos := 1, env := e₂g } :: rest } false := by
                          unfold Lir.step; simp [hfast, fastDec, e₂g, e₂s, h20, h21, Lir.Stmt.exec, Lir.Arg.eval, Lir.Addr.eval, cellAddr, Lir.dispWord, hw1]
                        have h2_b20_1 : Lir.step (install l p) { mem := mem1, ctx, stack := { fn := l.decProc, label := 20, pos := 1, env := e₂g } :: rest } =
                            .next { mem := mem1, ctx, stack := { fn := l.decProc, label := 2, pos := 0, env := (e₂g.insert 20 f0).insert 21 cur } :: rest } true := by
                          unfold Lir.step; simp [hfast, fastDec, e₂g, e₂s, h20, Lir.takeEdge, to, v, Lir.evalArgs, Lir.Arg.eval, Lir.bindParams]
                        exact .sync (Lir.semStep_next.mpr h1_b2_0)
                          (Sem.Star.trans h1_to_b5 (star_free h1_b5_1 (star_free h1_12_0 (star_free h1_12_1 (star_free h1_12_2 (star_free h1_12_3 (star_charge h1_12_4 (star_free h1_b1 (.refl _)))))))))
                          (Lir.semStep_next.mpr h2_b2_0)
                          (Sem.Star.trans h2_to_b5 (star_free h2_b5_1 (star_free h2_b14 (star_free h2_b15 (star_free h2_b16_0 (star_free h2_b16_1 (star_free h2_b20_0 (star_charge h2_b20_1 (.refl _)))))))))
                          (by omega) ⟨rfl, rfl, .decTop (.b2 (cur := f0) (par := cur) (by simp [e₁c]) (by simp [e₁c]) (by simp) (by simp)) hno⟩
              · -- `v5 ∉ {0, 1, 2}`: general path `b12` vs `b24`
                have hv5ne1 : (v5 == 1) = false := beq_false_of_ne hv5_1
                have h2_b15 : Lir.step (install l p) { mem, ctx, stack := { fn := l.decProc, label := 15, pos := 0, env := e₂s } :: rest } =
                    .next { mem, ctx, stack := { fn := l.decProc, label := 24, pos := 0, env := e₂s } :: rest } false := by
                  unfold Lir.step; simp [hfast, fastDec, e₂s, Lir.Arg.eval, w64_eq_iff, hv5ne1, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.bindParams]
                exact doGeneral h1_b5_1 (star_free h2_b5_1 (star_free h2_b14 (star_free h2_b15 (.refl _))))
      · -- `v3 ≠ 0`: static (`<s 0`) vs shared (`> 0`)
        have hv3ne : Lir.Cond.holds .eq .w32 v3 0 = false := by
          rw [w32_eq_zero_of_truncate htr3]; exact beq_false_of_ne hv3z
        have h2_b2_1 : Lir.step (install l p) { mem, ctx, stack := { fn := l.decProc, label := 2, pos := 1, env := e₂.insert 3 v3 } :: rest } =
            .next { mem, ctx, stack := { fn := l.decProc, label := 3, pos := 0, env := e₂.insert 3 v3 } :: rest } false := by
          unfold Lir.step; simp [hfast, fastDec, Lir.Arg.eval, hv3ne, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.bindParams]
        cases hslt : Lir.Cond.holds .slt .w32 v3 0 with
        | true =>
          have h1_b2_1 : Lir.step p { mem, ctx, stack := { fn := l.decProc, label := 2, pos := 1, env := e₁.insert 3 v3 } :: rest } =
              .next { mem, ctx, stack := { fn := l.decProc, label := 6, pos := 0, env := (e₁.insert 3 v3).insert 8 par } :: rest } false := by
            unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, h2, Lir.Arg.eval, hslt, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.bindParams]
          have h2_b3 : Lir.step (install l p) { mem, ctx, stack := { fn := l.decProc, label := 3, pos := 0, env := e₂.insert 3 v3 } :: rest } =
              .next { mem, ctx, stack := { fn := l.decProc, label := 6, pos := 0, env := (e₂.insert 3 v3).insert 8 par } :: rest } false := by
            unfold Lir.step; simp [hfast, fastDec, h21, Lir.Arg.eval, hslt, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.bindParams]
          exact .sync (Lir.semStep_next.mpr h1_b2_0) (star_free h1_b2_1 (.refl _))
            (Lir.semStep_next.mpr h2_b2_0) (star_free h2_b2_1 (star_free h2_b3 (.refl _)))
            (by omega) ⟨rfl, rfl, .decTop (.b6 (par := par) (by simp) (by simp)) hno⟩
        | false =>
          have h1_b2_1 : Lir.step p { mem, ctx, stack := { fn := l.decProc, label := 2, pos := 1, env := e₁.insert 3 v3 } :: rest } =
              .next { mem, ctx, stack := { fn := l.decProc, label := 3, pos := 0, env := e₁.insert 3 v3 } :: rest } false := by
            unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, Lir.Arg.eval, hslt, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.bindParams]
          have h1_b3 : Lir.step p { mem, ctx, stack := { fn := l.decProc, label := 3, pos := 0, env := e₁.insert 3 v3 } :: rest } =
              .next { mem, ctx, stack := { fn := l.decProc, label := 4, pos := 0, env := e₁.insert 3 v3 } :: rest } false := by
            unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, Lir.Arg.eval, hv3ne, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.bindParams]
          have h2_b3 : Lir.step (install l p) { mem, ctx, stack := { fn := l.decProc, label := 3, pos := 0, env := e₂.insert 3 v3 } :: rest } =
              .next { mem, ctx, stack := { fn := l.decProc, label := 4, pos := 0, env := e₂.insert 3 v3 } :: rest } false := by
            unfold Lir.step; simp [hfast, fastDec, Lir.Arg.eval, hslt, Lir.takeEdge, to, v, i, Lir.evalArgs, Lir.bindParams]
          let v4 := X86.Width.w32.truncate (v3 - 1)
          have h1_b4_0 : Lir.step p { mem, ctx, stack := { fn := l.decProc, label := 4, pos := 0, env := e₁.insert 3 v3 } :: rest } =
              .next { mem, ctx, stack := { fn := l.decProc, label := 4, pos := 1, env := (e₁.insert 3 v3).insert 4 v4 } :: rest } false := by
            unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, v4, Lir.Stmt.exec, Lir.Rhs.eval, Lir.Arg.eval, w32_sub]
          have h2_b4_0 : Lir.step (install l p) { mem, ctx, stack := { fn := l.decProc, label := 4, pos := 0, env := e₂.insert 3 v3 } :: rest } =
              .next { mem, ctx, stack := { fn := l.decProc, label := 4, pos := 1, env := (e₂.insert 3 v3).insert 4 v4 } :: rest } false := by
            unfold Lir.step; simp [hfast, fastDec, v4, Lir.Stmt.exec, Lir.Rhs.eval, Lir.Arg.eval, w32_sub]
          cases hw : mem.write? .w32 (cur + 4) v4 with
          | error _ =>
            exact .rawStuckWithin (by omega) (star_reaches_stuck
              (star_free h1_b2_0 (star_free h1_b2_1 (star_free h1_b3 (star_free h1_b4_0 (.refl _)))))
              (by unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, h1, Lir.Stmt.exec, Lir.Arg.eval, Lir.Addr.eval, cellAddr, Lir.dispWord, hw]))
          | ok mem' =>
            have h1_b4_1 : Lir.step p { mem, ctx, stack := { fn := l.decProc, label := 4, pos := 1, env := (e₁.insert 3 v3).insert 4 v4 } :: rest } =
                .next { mem := mem', ctx, stack := { fn := l.decProc, label := 4, pos := 2, env := (e₁.insert 3 v3).insert 4 v4 } :: rest } false := by
              unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, h1, Lir.Stmt.exec, Lir.Arg.eval, Lir.Addr.eval, cellAddr, Lir.dispWord, hw]
            have h1_b4_2 : Lir.step p { mem := mem', ctx, stack := { fn := l.decProc, label := 4, pos := 2, env := (e₁.insert 3 v3).insert 4 v4 } :: rest } =
                .next { mem := mem', ctx, stack := { fn := l.decProc, label := 6, pos := 0, env := ((e₁.insert 3 v3).insert 4 v4).insert 8 par } :: rest } false := by
              unfold Lir.step; simp [hdec, Rt.Rc.Gen.dec, h2, Lir.takeEdge, to, v, Lir.evalArgs, Lir.Arg.eval, Lir.bindParams]
            have h2_b4_1 : Lir.step (install l p) { mem, ctx, stack := { fn := l.decProc, label := 4, pos := 1, env := (e₂.insert 3 v3).insert 4 v4 } :: rest } =
                .next { mem := mem', ctx, stack := { fn := l.decProc, label := 4, pos := 2, env := (e₂.insert 3 v3).insert 4 v4 } :: rest } false := by
              unfold Lir.step; simp [hfast, fastDec, h20, Lir.Stmt.exec, Lir.Arg.eval, Lir.Addr.eval, cellAddr, Lir.dispWord, hw]
            have h2_b4_2 : Lir.step (install l p) { mem := mem', ctx, stack := { fn := l.decProc, label := 4, pos := 2, env := (e₂.insert 3 v3).insert 4 v4 } :: rest } =
                .next { mem := mem', ctx, stack := { fn := l.decProc, label := 6, pos := 0, env := ((e₂.insert 3 v3).insert 4 v4).insert 8 par } :: rest } false := by
              unfold Lir.step; simp [hfast, fastDec, h21, Lir.takeEdge, to, v, Lir.evalArgs, Lir.Arg.eval, Lir.bindParams]
            exact .sync (Lir.semStep_next.mpr h1_b2_0) (star_free h1_b2_1 (star_free h1_b3 (star_free h1_b4_0 (star_free h1_b4_1 (star_free h1_b4_2 (.refl _))))))
              (Lir.semStep_next.mpr h2_b2_0) (star_free h2_b2_1 (star_free h2_b3 (star_free h2_b4_0 (star_free h2_b4_1 (star_free h2_b4_2 (.refl _))))))
              (by omega) ⟨rfl, rfl, .decTop (.b6 (par := par) (by simp) (by simp)) hno⟩

/-! ## Unified step match and clocked simulation -/

private theorem step_match {l : Layout} {p : Lir.Program}
    (hdec : p.funcs[l.decProc]? = some Rt.Rc.Gen.dec)
    {s₁ s₂ : Lir.State} (hrel : StateRel l s₁ s₂) :
    MatchedStep l p s₁ s₂ := by
  obtain ⟨hmem, hctx, hst⟩ := hrel
  cases s₁; cases s₂
  simp only at hmem hctx
  subst hmem hctx
  cases hst with
  | other hno => exact step_match_other hdec hno
  | decTop hd hno => exact step_match_dec hdec hd hno

private theorem forward_run {l : Layout} {p : Lir.Program}
    (hdec : p.funcs[l.decProc]? = some Rt.Rc.Gen.dec) :
    ∀ fuel k s₁ s₂ r, StateRel l s₁ s₂ →
      Sem.runClocked (Lir.semStep p) fuel k s₁ = r →
      r ≠ .timeout → r ≠ .stuck →
      ∃ k', Sem.Reaches (Lir.semStep (install l p)) s₂ k' r := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    intro k s₁ s₂ r hrel hrun hnt hns
    have hr1 : Sem.Reaches (Lir.semStep p) s₁ k r := Sem.runClocked_sound hrun hnt
    cases step_match hdec hrel with
    | rawStuck hst =>
      have h2 : Sem.Reaches (Lir.semStep p) s₁ k .stuck := .final (by rw [Lir.semStep, hst]; exact .stuck)
      exact absurd (hr1.det h2) hns
    | @rawStuckWithin c₁ _ hst =>
      have h2 : Sem.Reaches (Lir.semStep p) s₁ (max k c₁) .stuck := hst.mono (by simp) (Nat.le_max_right k c₁)
      have h1 : Sem.Reaches (Lir.semStep p) s₁ (max k c₁) r := hr1.mono hnt (Nat.le_max_left k c₁)
      exact absurd (h1.det h2) hns
    | sameFinal hf₁ hf₂ =>
      have heq : r = _ := hr1.det (.final hf₁)
      subst heq
      exact ⟨0, .final hf₂⟩
    | sync hs₁ hstar₁ hs₂ hstar₂ _ hrel' =>
      obtain ⟨fuel', k', hflt, _, hrun'⟩ := Inline.runClocked_star_inv_lt hs₁ hstar₁ hrun hnt
      obtain ⟨k₂, hreach₂⟩ := ih fuel' hflt k' _ _ r hrel' hrun' hnt hns
      exact ⟨_, Inline.reaches_of_star_reaches (Sem.Star.head hs₂ hstar₂) hreach₂⟩

private theorem backward_run {l : Layout} {p : Lir.Program}
    (hdec : p.funcs[l.decProc]? = some Rt.Rc.Gen.dec) :
    ∀ fuel k s₁ s₂ r, StateRel l s₁ s₂ →
      Sem.runClocked (Lir.semStep (install l p)) fuel k s₂ = r →
      r ≠ .timeout → (∀ fail, r ≠ .resource fail) →
      ∃ r₁, r₁ ≠ .timeout ∧ Sem.Reaches (Lir.semStep p) s₁ (k + 3 * fuel) r₁ := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    intro k s₁ s₂ r hrel hrun hnt hnr
    have hfuelPos : 1 ≤ fuel := by
      cases fuel with
      | zero => simp [Sem.runClocked] at hrun; exact absurd hrun.symm hnt
      | succ _ => omega
    have hr2 : Sem.Reaches (Lir.semStep (install l p)) s₂ k r := Sem.runClocked_sound hrun hnt
    cases step_match hdec hrel with
    | rawStuck hst =>
      exact ⟨.stuck, by simp, .final (by rw [Lir.semStep, hst]; exact .stuck)⟩
    | rawStuckWithin hc hst =>
      exact ⟨.stuck, by simp, hst.mono (by simp) (by omega)⟩
    | sameFinal hf₁ hf₂ =>
      have heq : r = _ := hr2.det (.final hf₂)
      subst heq
      exact ⟨r, hnt, .final hf₁⟩
    | @sync s₁' s₂' s₁'' s₂'' b₁ b₂ c₁ c₂ hs₁ hstar₁ hs₂ hstar₂ hchg hrel' =>
      obtain ⟨fuel', k', hflt, hkEq, hrun'⟩ := Inline.runClocked_star_inv_lt hs₂ hstar₂ hrun hnt
      obtain ⟨r₁, hr₁nt, hreach₁⟩ := ih fuel' hflt k' s₁'' s₂'' r hrel' hrun' hnt hnr
      have htotal := Inline.reaches_of_star_reaches (Sem.Star.head hs₁ hstar₁) hreach₁
      exact ⟨r₁, hr₁nt, htotal.mono hr₁nt (by omega)⟩

/-- Exact forward preservation of any non-timeout, non-stuck `Lir.eval` outcome across `FastDec.install`. -/
theorem install_forward_eq {l : Layout} {p : Lir.Program}
    (hdec : p.funcs[l.decProc]? = some Rt.Rc.Gen.dec)
    {k : Nat} {args : List Lir.Word} {mem : X86.Memory} {ctx : Lir.Word}
    (hnt : Lir.eval p k args mem ctx ≠ .timeout)
    (hns : Lir.eval p k args mem ctx ≠ .stuck) :
    ∃ k', Lir.eval (install l p) k' args mem ctx = Lir.eval p k args mem ctx := by
  let q := install l p
  have hmain : q.main = p.main := rfl
  obtain ⟨heFwd, heNone⟩ := enter_dec_or_other l p hdec (rest := []) (by simp)
  cases hent : Lir.enter p p.main args with
  | none =>
    exact absurd (by simp [Lir.eval, Lir.State.initial, hent]) hns
  | some fr₁ =>
    obtain ⟨fr₂, hent₂, hst⟩ := heFwd fr₁ hent
    let s₁ : Lir.State := { mem, ctx, stack := [fr₁] }
    let s₂ : Lir.State := { mem, ctx, stack := [fr₂] }
    have hinit₁ : Lir.State.initial p args mem ctx = some s₁ := by simp [Lir.State.initial, hent, s₁]
    have hinit₂ : Lir.State.initial q args mem ctx = some s₂ := by simp [Lir.State.initial, hmain, q, hent₂, s₂]
    have hrun : Sem.runClocked (Lir.semStep p) (Lir.fuelFor p k) k s₁ = Lir.eval p k args mem ctx := by
      rw [Lir.eval_eq, hinit₁]
    obtain ⟨k', hreach₂⟩ := forward_run hdec (Lir.fuelFor p k) k s₁ s₂ _ ⟨rfl, rfl, hst⟩ hrun hnt hns
    exact ⟨k', (Lir.runs_eval hinit₂).eq hreach₂⟩

/-- **`FastDec.install l p` simulates `p` with exact value and memory equality.** -/
theorem install_sim {l : Layout} {p : Lir.Program}
    (hdec : p.funcs[l.decProc]? = some Rt.Rc.Gen.dec)
    (args : List Lir.Word) (mem : X86.Memory) (ctx : Lir.Word) :
    Sem.Sim Eq (fun k => k + 3 * Lir.fuelFor (install l p) k)
      (fun k => Lir.eval p k args mem ctx)
      (fun k => Lir.eval (install l p) k args mem ctx) := by
  let q := install l p
  have hmain : q.main = p.main := rfl
  obtain ⟨heFwd, heNone⟩ := enter_dec_or_other l p hdec (rest := []) (by simp)
  cases hent : Lir.enter p p.main args with
  | none =>
    have hent₂ : Lir.enter q q.main args = none := by rw [hmain]; exact heNone.mp hent
    have he1 : ∀ k, Lir.eval p k args mem ctx = .stuck := fun k => by
      simp [Lir.eval, Lir.State.initial, hent]
    have he2 : ∀ k, Lir.eval q k args mem ctx = .stuck := fun k => by
      simp [Lir.eval, Lir.State.initial, hent₂]
    exact {
      forward := fun k _ => ⟨k, by rw [he1, he2]; exact .stuck⟩
      timeout := fun k hk => by rw [he1] at hk; cases hk }
  | some fr₁ =>
    obtain ⟨fr₂, hent₂, hst⟩ := heFwd fr₁ hent
    let s₁ : Lir.State := { mem, ctx, stack := [fr₁] }
    let s₂ : Lir.State := { mem, ctx, stack := [fr₂] }
    have hinit₁ : Lir.State.initial p args mem ctx = some s₁ := by
      simp [Lir.State.initial, hent, s₁]
    have hinit₂ : Lir.State.initial q args mem ctx = some s₂ := by
      simp [Lir.State.initial, hmain, q, hent₂, s₂]
    have hruns₁ := Lir.runs_eval hinit₁
    have hruns₂ := Lir.runs_eval hinit₂
    have hrel : StateRel l s₁ s₂ := ⟨rfl, rfl, hst⟩
    exact {
      forward := fun k hk => by
        by_cases hst1 : Lir.eval p k args mem ctx = .stuck
        · exact ⟨0, hst1 ▸ .stuck⟩
        · have hrun : Sem.runClocked (Lir.semStep p) (Lir.fuelFor p k) k s₁ =
              Lir.eval p k args mem ctx := by
            rw [Lir.eval_eq, hinit₁]
          obtain ⟨k', hreach₂⟩ := forward_run hdec (Lir.fuelFor p k) k s₁ s₂ _ hrel hrun hk hst1
          exact ⟨k', hruns₂.eq hreach₂ ▸ Sem.Result.Refines.refl (fun _ => rfl)⟩
      timeout := fun k hk => by
        by_cases hto : Lir.eval q k args mem ctx = .timeout
        · exact .inl hto
        · by_cases hres : ∃ fail, Lir.eval q k args mem ctx = .resource fail
          · exact .inr hres
          · have hres' : ∀ fail, Lir.eval q k args mem ctx ≠ .resource fail :=
              fun fail h => hres ⟨fail, h⟩
            have hrun₂ : Sem.runClocked (Lir.semStep q) (Lir.fuelFor q k) k s₂ =
                Lir.eval q k args mem ctx := by
              rw [Lir.eval_eq, hinit₂]
            obtain ⟨r₁, hr₁nt, hreach₁⟩ := backward_run hdec (Lir.fuelFor q k) k s₁ s₂ _ hrel hrun₂ hto hres'
            have hto₁ : Sem.Reaches (Lir.semStep p) s₁ (k + 3 * Lir.fuelFor q k) .timeout :=
              hk ▸ hruns₁ (k + 3 * Lir.fuelFor q k)
            exact absurd (hreach₁.det hto₁) hr₁nt }

theorem install_sim_clock {l : Layout} {p : Lir.Program}
    (hdec : p.funcs[l.decProc]? = some Rt.Rc.Gen.dec)
    (args : List Lir.Word) (mem : X86.Memory) (ctx : Lir.Word)
    {f : Nat → Nat} (hf : ∀ k, k + 3 * Lir.fuelFor (install l p) k ≤ f k) :
    Sem.Sim Eq f
      (fun k => Lir.eval p k args mem ctx)
      (fun k => Lir.eval (install l p) k args mem ctx) :=
  let hsim := install_sim hdec args mem ctx
  { forward := hsim.forward
    timeout := fun k hk => by
      apply hsim.timeout k
      by_cases h0 : Lir.eval p (k + 3 * Lir.fuelFor (install l p) k) args mem ctx = .timeout
      · exact h0
      · have heq := Lir.eval_mono p args mem ctx (hf k) h0
        dsimp only at heq
        rw [hk] at heq
        exact absurd heq.symm h0 }

private theorem fastDec_size_ge_genDec : Rt.Rc.Gen.dec.size ≤ fastDec.size := by decide

private theorem list_sum_map_le_of_pointwise {α : Type} (f g : α → Nat) :
    ∀ (xs ys : List α) (hlen : xs.length = ys.length),
      (∀ i (hi : i < xs.length), f xs[i] ≤ g (ys[i]'(by omega))) →
      (xs.map f).sum ≤ (ys.map g).sum
  | [], [], _, _ => Nat.le_refl _
  | x :: xs, y :: ys, hlen, hpt => by
    simp only [List.map_cons, List.sum_cons]
    have h0 := hpt 0 (by simp)
    simp only [List.getElem_cons_zero] at h0
    have ih := list_sum_map_le_of_pointwise f g xs ys (by simpa using hlen) (fun i hi => by
      have := hpt (i + 1) (by simp; omega)
      simpa using this)
    omega

theorem install_size_ge {l : Layout} {p : Lir.Program}
    (hdec : p.funcs[l.decProc]? = some Rt.Rc.Gen.dec) :
    p.size ≤ (install l p).size := by
  rw [Inline.program_size_eq_sum, Inline.program_size_eq_sum]
  exact list_sum_map_le_of_pointwise Lir.Func.size Lir.Func.size p.funcs.toList (install l p).funcs.toList
    (by simp [install]) (fun i hi => by
      by_cases heq : i = l.decProc
      · subst heq
        have h1 : p.funcs.toList[l.decProc]'hi = Rt.Rc.Gen.dec := by
          have hg := Array.getElem?_eq_some_iff.mp hdec
          simpa using hg.2
        have h2 : (install l p).funcs.toList[l.decProc]'(by simpa [install] using hi) = fastDec := by
          have hg := Array.getElem?_eq_some_iff.mp (install_get_dec l p hdec)
          simpa using hg.2
        rw [h1, h2]
        exact fastDec_size_ge_genDec
      · have hget := install_get_ne l p heq
        have hi' : i < (install l p).funcs.size := by simpa [install] using hi
        have hi1 : i < p.funcs.size := by simpa using hi
        have heqElem : (install l p).funcs[i]'hi' = p.funcs[i]'hi1 := by
          rw [Array.getElem?_eq_getElem hi', Array.getElem?_eq_getElem hi1] at hget
          exact Option.some.inj hget
        simp [heqElem])

theorem fuelFor_le_install {l : Layout} {p : Lir.Program}
    (hdec : p.funcs[l.decProc]? = some Rt.Rc.Gen.dec) (k : Nat) :
    Lir.fuelFor p k ≤ Lir.fuelFor (install l p) k := by
  unfold Lir.fuelFor
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_right (install_size_ge hdec) 1)

end IxCC.Cfg.Rc.FastDec
