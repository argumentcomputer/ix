import IxCC.Lir.Opt.Sym
import IxCC.Lir.Proof.Eval
import IxCC.X86.Width
import IxCC.Xv.Select.Proof.Words

/-!
# Arithmetic, normalization, magic-multiplier, and interval soundness

Formal soundness proofs for `IxCC.Lir.Opt.DivMagic` and the pure expression /
interval layer of `IxCC.Lir.Opt.Sym`.
-/

set_option autoImplicit false

namespace IxCC.Lir.Opt

open IxCC.Lir (VReg Width Ext Base Addr Arg Cond BinOp Ovf LimbOp Rhs Word Env
  sext sarWord rolWord rorWord shiftMask dispWord loadWord)

/-! ## Condition laws -/

theorem condNegate_holds (c : Cond) (w : Width) (a b : Word) :
    (condNegate c).holds w a b = !(c.holds w a b) := by
  cases c with
  | eq => simp [condNegate, Cond.holds, bne]
  | ne => simp [condNegate, Cond.holds, bne]
  | ult =>
      simp only [condNegate, Cond.holds, UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt]
      by_cases h : (w.truncate a).toNat < (w.truncate b).toNat <;> simp [h] <;> omega
  | ule =>
      simp only [condNegate, Cond.holds, UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt]
      by_cases h : (w.truncate a).toNat ≤ (w.truncate b).toNat <;> simp [h] <;> omega
  | ugt =>
      simp only [condNegate, Cond.holds, UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt]
      by_cases h : (w.truncate b).toNat < (w.truncate a).toNat <;> simp [h] <;> omega
  | uge =>
      simp only [condNegate, Cond.holds, UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt]
      by_cases h : (w.truncate b).toNat ≤ (w.truncate a).toNat <;> simp [h] <;> omega
  | slt =>
      simp only [condNegate, Cond.holds]
      by_cases h : w.signedValue a < w.signedValue b <;> simp [h] <;> omega
  | sle =>
      simp only [condNegate, Cond.holds]
      by_cases h : w.signedValue a ≤ w.signedValue b <;> simp [h] <;> omega
  | sgt =>
      simp only [condNegate, Cond.holds]
      by_cases h : w.signedValue b < w.signedValue a <;> simp [h] <;> omega
  | sge =>
      simp only [condNegate, Cond.holds]
      by_cases h : w.signedValue b ≤ w.signedValue a <;> simp [h] <;> omega
  | tz => simp [condNegate, Cond.holds, bne]
  | tnz => simp [condNegate, Cond.holds, bne]

theorem condSwap_holds (c : Cond) (w : Width) (a b : Word) :
    (condSwap c).holds w b a = c.holds w a b := by
  cases c with
  | eq =>
      simp only [condSwap, Cond.holds]
      by_cases h : w.truncate a = w.truncate b
      · simp [h]
      · have h' : w.truncate b ≠ w.truncate a := fun e => h e.symm
        simp [beq_false_of_ne h, beq_false_of_ne h']
  | ne =>
      simp only [condSwap, Cond.holds, bne]
      by_cases h : w.truncate a = w.truncate b
      · simp [h]
      · have h' : w.truncate b ≠ w.truncate a := fun e => h e.symm
        simp [beq_false_of_ne h, beq_false_of_ne h']
  | tz => simp [condSwap, Cond.holds, UInt64.and_comm]
  | tnz => simp [condSwap, Cond.holds, UInt64.and_comm, bne]
  | ult | ule | ugt | uge | slt | sle | sgt | sge => rfl

theorem condReflVal_sound {c : Cond} {r : Bool} (h : condReflVal c = some r) (w : Width) (a : Word) :
    c.holds w a a = r := by
  cases c <;> simp [condReflVal] at h <;> subst h <;> simp [Cond.holds]

theorem binOpIsComm_eval {o : BinOp} (h : binOpIsComm o = true) (w : Width) (a b : Word) :
    o.eval w b a = o.eval w a b := by
  cases o <;> simp [binOpIsComm] at h <;>
    simp [BinOp.eval, UInt64.add_comm, UInt64.mul_comm, UInt64.and_comm, UInt64.or_comm, UInt64.xor_comm]

theorem binOpIsTotal_eval {o : BinOp} (h : binOpIsTotal o = true) (w : Width) (a b : Word) :
    ∃ v, o.eval w a b = some v := by
  cases o <;> simp [binOpIsTotal] at h <;> exact ⟨_, rfl⟩

/-! ## Word and truncation helper lemmas -/

theorem shiftMask_pow2_lt {w : Width} {k : Nat} (hk : k < w.bits) :
    (UInt64.ofNat k &&& shiftMask w).toNat = k := by
  rw [UInt64.toNat_and, UInt64.toNat_ofNat']
  cases w with
  | w8 =>
      simp only [X86.Width.bits] at hk
      have h1 : k % UInt64.size = k := Nat.mod_eq_of_lt (by simp [UInt64.size]; omega)
      rw [h1]
      change k &&& 31 = k
      rw [show (31 : Nat) = 2 ^ 5 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_eq_of_lt (by omega)
  | w16 =>
      simp only [X86.Width.bits] at hk
      have h1 : k % UInt64.size = k := Nat.mod_eq_of_lt (by simp [UInt64.size]; omega)
      rw [h1]
      change k &&& 31 = k
      rw [show (31 : Nat) = 2 ^ 5 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_eq_of_lt (by omega)
  | w32 =>
      simp only [X86.Width.bits] at hk
      have h1 : k % UInt64.size = k := Nat.mod_eq_of_lt (by simp [UInt64.size]; omega)
      rw [h1]
      change k &&& 31 = k
      rw [show (31 : Nat) = 2 ^ 5 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_eq_of_lt (by omega)
  | w64 =>
      simp only [X86.Width.bits] at hk
      have h1 : k % UInt64.size = k := Nat.mod_eq_of_lt (by simp [UInt64.size]; omega)
      rw [h1]
      change k &&& 63 = k
      rw [show (63 : Nat) = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_eq_of_lt (by omega)

theorem shiftMask_idem (w : Width) (k : Word) :
    (k &&& shiftMask w) &&& shiftMask w = k &&& shiftMask w := by
  rw [UInt64.and_assoc, UInt64.and_self]

theorem toNat_shr_word {a c : Word} (hc : c.toNat < 64) :
    (a >>> c).toNat = a.toNat / 2 ^ c.toNat := by
  rw [UInt64.toNat_shiftRight, Nat.mod_eq_of_lt hc, Nat.shiftRight_eq_div_pow]

theorem toNat_shl_word {a c : Word} (hc : c.toNat < 64) :
    (a <<< c).toNat = (a.toNat * 2 ^ c.toNat) % 2 ^ 64 := by
  rw [UInt64.toNat_shiftLeft, Nat.mod_eq_of_lt hc, Nat.shiftLeft_eq]

theorem width_bits_le_64 (w : Width) : w.bits ≤ 64 := X86.Encode.width_bound w

theorem pow2_dvd_64 (w : Width) : 2 ^ w.bits ∣ 2 ^ 64 :=
  Nat.pow_dvd_pow 2 (width_bits_le_64 w)

theorem mod_pow2_mod_64 (w : Width) (n : Nat) : (n % 2 ^ 64) % 2 ^ w.bits = n % 2 ^ w.bits :=
  Nat.mod_mod_of_dvd n (pow2_dvd_64 w)

/-! ## Rotate identities -/

theorem rolWord_zero_val (w : Width) (c : Word) : rolWord w 0 c = 0 := by
  unfold rolWord
  dsimp only
  rw [Xv.Select.Proof.truncate_zero]
  split
  · rfl
  · simp [UInt64.zero_shiftLeft, UInt64.zero_shiftRight, Xv.Select.Proof.truncate_zero]

theorem rorWord_zero_val (w : Width) (c : Word) : rorWord w 0 c = 0 := by
  unfold rorWord
  dsimp only
  rw [Xv.Select.Proof.truncate_zero]
  split
  · rfl
  · simp [UInt64.zero_shiftLeft, UInt64.zero_shiftRight, Xv.Select.Proof.truncate_zero]

theorem rolWord_zero_count (w : Width) (a : Word) : rolWord w a 0 = w.truncate a := by
  simp [rolWord]

theorem rorWord_zero_count (w : Width) (a : Word) : rorWord w a 0 = w.truncate a := by
  simp [rorWord]

theorem rorWord_of_shr_shl (w : Width) (a : Word) {r1 r2 : Nat}
    (h1pos : 0 < r1) (h1lt : r1 < w.bits) (hsum : r1 + r2 = w.bits) :
    w.truncate (w.truncate (w.truncate a >>> UInt64.ofNat r1) ||| w.truncate (a <<< UInt64.ofNat r2)) =
      rorWord w a (UInt64.ofNat r1 &&& shiftMask w) := by
  have hw := width_bits_le_64 w
  have hsh := shiftMask_pow2_lt h1lt
  have hmod : (UInt64.ofNat r1 &&& shiftMask w).toNat % w.bits = r1 := by
    rw [hsh, Nat.mod_eq_of_lt h1lt]
  have hne : (r1 == 0) = false := beq_false_of_ne (by omega)
  have hr2 : w.bits - r1 = r2 := by omega
  have hr1m : r1 % 64 = r1 := Nat.mod_eq_of_lt (by omega)
  have hr2m : r2 % 64 = r2 := Nat.mod_eq_of_lt (by omega)
  unfold rorWord
  simp only [hmod, hne, Bool.false_eq_true, ↓reduceIte, hr2]
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [X86.Encode.truncate_bits, BitVec.getLsbD_setWidth, UInt64.toBitVec_or,
    BitVec.getLsbD_or, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight,
    BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight]
  by_cases hlt : i < w.bits
  · have hlt2 : i - r2 < w.bits := by omega
    have hlt2' : i - r2 < 64 := by omega
    by_cases hge : i < r2
    · have h3 : r1 + i < w.bits := by omega
      have h4 : r1 + i < 64 := by omega
      simp [hlt, hi, hge, h3, h4, hr1m, hr2m]
    · have h3 : ¬ (r1 + i < w.bits) := by omega
      simp [hlt, hi, hge, h3, hlt2, hlt2', hr1m, hr2m]
  · simp [hlt]

private theorem word_toNat_mask_eq_ofNat (w : Width) (c : Word) :
    UInt64.ofNat (c &&& shiftMask w).toNat = c &&& shiftMask w := by
  exact UInt64.ofNat_toNat

theorem matchRotateShrShl_sound {ρ : Env} {ctx : Word} {snaps : MemSnaps}
    {w rw : Width} {s1 s2 x : SymExpr} {r v1 v2 : Word}
    (hm : matchRotateShrShl w s1 s2 = some (rw, x, r))
    (h1 : s1.eval ρ ctx snaps = some v1) (h2 : s2.eval ρ ctx snaps = some v2) :
    (SymExpr.bin .ror rw x (.imm r)).eval ρ ctx snaps = some (w.truncate (v1 ||| v2)) := by
  unfold matchRotateShrShl at hm
  split at hm
  · rename_i w1 x1 c1 w2 x2 c2
    split at hm
    · rename_i hcond
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hcond
      dsimp only at hm
      split at hm
      · rename_i hr
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hr
        obtain ⟨⟨hpos, hlt⟩, hsum⟩ := hr
        cases hm
        simp only [SymExpr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff,
          Option.some.injEq, BinOp.eval] at h1 h2
        obtain ⟨vx1, hx1, _, rfl, rfl⟩ := h1
        obtain ⟨vx2, hx2, _, rfl, rfl⟩ := h2
        rw [hx1] at hx2; cases hx2
        simp only [SymExpr.eval, Option.bind_eq_bind, hx1, Option.bind_some, BinOp.eval,
          Option.some.injEq]
        rw [← rorWord_of_shr_shl rw vx1 hpos hlt hsum, word_toNat_mask_eq_ofNat, word_toNat_mask_eq_ofNat]
      · cases hm
    · split at hm
      · rename_i hcond
        simp only [Bool.and_eq_true, beq_iff_eq] at hcond
        obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := hcond
        dsimp only at hm
        split at hm
        · rename_i hr
          simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hr
          obtain ⟨⟨hpos, hlt⟩, hsum⟩ := hr
          cases hm
          simp only [SymExpr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff,
            Option.some.injEq, BinOp.eval] at h1 h2
          obtain ⟨vx1, hx1, _, rfl, rfl⟩ := h1
          obtain ⟨vx2, hx2, _, rfl, rfl⟩ := h2
          rw [hx1] at hx2; cases hx2
          simp only [SymExpr.eval, Option.bind_eq_bind, hx1, Option.bind_some, BinOp.eval,
            Option.some.injEq]
          rw [← rorWord_of_shr_shl .w32 vx1 hpos hlt hsum,
            word_toNat_mask_eq_ofNat, word_toNat_mask_eq_ofNat, X86.Encode.truncate64]
          apply UInt64.toBitVec_inj.mp
          apply BitVec.eq_of_getLsbD_eq
          intro i hi
          simp only [X86.Encode.truncate_bits, UInt64.toBitVec_or, BitVec.getLsbD_setWidth,
            BitVec.getLsbD_or, X86.Width.bits]
          by_cases hlt32 : i < 32 <;> simp [hlt32, hi]
        · cases hm
      · cases hm
  · rename_i x1 m1 c1 x2 c2 m2
    split at hm
    · rename_i hcond
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hcond
      obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, hx2eq⟩ := hcond
      dsimp only at hm
      split at hm
      · rename_i hr
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hr
        obtain ⟨⟨hpos, hlt⟩, hsum⟩ := hr
        cases hm
        simp only [SymExpr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff,
          Option.some.injEq, BinOp.eval, X86.Encode.truncate64] at h1 h2
        obtain ⟨va1, ⟨vx1, hx1, _, rfl, rfl⟩, _, rfl, rfl⟩ := h1
        obtain ⟨vs2, ⟨vx2, hx2, _, rfl, rfl⟩, _, rfl, rfl⟩ := h2
        have hvx : vx2 &&& (0xffffffff : Word) = vx1 &&& (0xffffffff : Word) ∧
            (vx2 = vx1 ∨ vx2 = vx1 &&& (0xffffffff : Word)) := by
          rcases hx2eq with rfl | rfl
          · rw [hx1] at hx2; cases hx2; exact ⟨rfl, .inl rfl⟩
          · simp only [SymExpr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff,
              Option.some.injEq, BinOp.eval, X86.Encode.truncate64] at hx2
            obtain ⟨vx1', hx1', _, rfl, rfl⟩ := hx2
            rw [hx1] at hx1'; cases hx1'
            exact ⟨by rw [UInt64.and_assoc, UInt64.and_self], .inr rfl⟩
        have hmask32 : ∀ z : Word, z &&& (0xffffffff : Word) = X86.Width.w32.truncate z := fun _ => rfl
        have hsh_eq : (vx2 <<< (c2 &&& shiftMask .w64)) &&& (0xffffffff : Word) =
            X86.Width.w32.truncate (vx1 <<< UInt64.ofNat (c2 &&& 63).toNat) := by
          have hc2 : (c2 &&& 63).toNat < 64 := by
            have : (c2 &&& 63).toNat ≤ (63 : Word).toNat := by rw [UInt64.toNat_and]; exact Nat.and_le_right
            change _ ≤ 63 at this; omega
          have hc2_eq : c2 &&& shiftMask .w64 = UInt64.ofNat (c2 &&& 63).toNat := by
            show c2 &&& 63 = _; exact UInt64.ofNat_toNat.symm
          rw [hc2_eq, hmask32]
          rcases hvx.2 with rfl | rfl
          · rfl
          · apply UInt64.toBitVec_inj.mp
            apply BitVec.eq_of_getLsbD_eq
            intro i hi
            rw [hmask32]
            simp only [X86.Encode.truncate_bits, BitVec.getLsbD_setWidth, UInt64.toBitVec_shiftLeft,
              BitVec.shiftLeft_eq', BitVec.getLsbD_shiftLeft, X86.Width.bits]
            have hmod : ((UInt64.ofNat (c2 &&& 63).toNat).toBitVec % 64).toNat = (c2 &&& 63).toNat := by
              rw [UInt64.ofNat_toNat, BitVec.toNat_umod, UInt64.toNat_toBitVec]
              change (c2 &&& 63).toNat % 64 = (c2 &&& 63).toNat
              exact Nat.mod_eq_of_lt hc2
            rw [hmod]
            by_cases hlt32 : i < 32
            · by_cases hltc : i < (c2 &&& 63).toNat
              · simp only [hlt32, hi, hltc, decide_true, Bool.not_true, Bool.false_and, Bool.and_false]
              · have hsub : i - (c2 &&& 63).toNat < 32 := by omega
                have hsub64 : i - (c2 &&& 63).toNat < 64 := by omega
                simp only [hlt32, hi, hltc, hsub, hsub64, decide_true, decide_false, Bool.not_false,
                  Bool.true_and, Bool.and_true]
            · simp only [hlt32, decide_false, Bool.false_and, Bool.and_false]
        have hshr_eq : (vx1 &&& (0xffffffff : Word)) >>> (c1 &&& shiftMask .w64) =
            X86.Width.w32.truncate (X86.Width.w32.truncate vx1 >>> UInt64.ofNat (c1 &&& 63).toNat) := by
          have hc1_eq : c1 &&& shiftMask .w64 = UInt64.ofNat (c1 &&& 63).toNat := by
            show c1 &&& 63 = _; exact UInt64.ofNat_toNat.symm
          have hc1lt : (c1 &&& 63).toNat < 64 := by omega
          rw [hc1_eq, hmask32]
          apply UInt64.toBitVec_inj.mp
          apply BitVec.eq_of_getLsbD_eq
          intro i hi
          simp only [X86.Encode.truncate_bits, BitVec.getLsbD_setWidth, UInt64.toBitVec_shiftRight,
            BitVec.ushiftRight_eq', BitVec.getLsbD_ushiftRight, X86.Width.bits]
          have hmod : ((UInt64.ofNat (c1 &&& 63).toNat).toBitVec % 64).toNat = (c1 &&& 63).toNat := by
            rw [UInt64.ofNat_toNat, BitVec.toNat_umod, UInt64.toNat_toBitVec]
            change (c1 &&& 63).toNat % 64 = (c1 &&& 63).toNat
            exact Nat.mod_eq_of_lt hc1lt
          rw [hmod]
          by_cases hlt32 : i < 32
          · simp only [hlt32, hi, decide_true, Bool.true_and]
          · have hge32 : ¬ ((c1 &&& 63).toNat + i < 32) := by omega
            simp only [hlt32, hge32, decide_false, Bool.false_and, Bool.and_false]
        simp only [SymExpr.eval, Option.bind_eq_bind, hx1, Option.bind_some, BinOp.eval,
          Option.some.injEq]
        rw [← rorWord_of_shr_shl .w32 vx1 hpos hlt hsum, X86.Encode.truncate64, hshr_eq, hsh_eq]
        apply UInt64.toBitVec_inj.mp
        apply BitVec.eq_of_getLsbD_eq
        intro i hi
        simp only [X86.Encode.truncate_bits, UInt64.toBitVec_or, BitVec.getLsbD_setWidth,
          BitVec.getLsbD_or, X86.Width.bits]
        by_cases hlt32 : i < 32 <;> simp [hlt32, hi]
      · cases hm
    · cases hm
  · cases hm

theorem matchRotateOr_sound {ρ : Env} {ctx : Word} {snaps : MemSnaps}
    {w rw : Width} {a b x : SymExpr} {r va vb : Word}
    (hm : matchRotateOr w a b = some (rw, x, r))
    (ha : a.eval ρ ctx snaps = some va) (hb : b.eval ρ ctx snaps = some vb) :
    (SymExpr.bin .ror rw x (.imm r)).eval ρ ctx snaps = some (w.truncate (va ||| vb)) := by
  unfold matchRotateOr at hm
  cases h1 : matchRotateShrShl w a b with
  | some res =>
      rw [h1] at hm; cases hm
      exact matchRotateShrShl_sound h1 ha hb
  | none =>
      rw [h1] at hm
      rw [UInt64.or_comm]
      exact matchRotateShrShl_sound hm hb ha

theorem matchRotateMasked32Pair_sound {ρ : Env} {ctx : Word} {snaps : MemSnaps}
    {s1 s2 x : SymExpr} {r v1 v2 : Word}
    (hm : matchRotateMasked32Pair s1 s2 = some (x, r))
    (h1 : s1.eval ρ ctx snaps = some v1) (h2 : s2.eval ρ ctx snaps = some v2) :
    (SymExpr.bin .ror .w32 x (.imm r)).eval ρ ctx snaps = some ((v1 ||| v2) &&& 0xffffffff) := by
  unfold matchRotateMasked32Pair at hm
  split at hm
  · rename_i x1 m1 c1 x2 c2
    split at hm
    · rename_i hcond
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hcond
      obtain ⟨rfl, hx2eq⟩ := hcond
      dsimp only at hm
      split at hm
      · rename_i hr
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hr
        obtain ⟨⟨hpos, hlt⟩, hsum⟩ := hr
        cases hm
        have hshr : (SymExpr.bin .shr .w64 (.bin .and .w64 x (.imm 0xffffffff)) (.imm c1)).eval ρ ctx snaps = some v1 := h1
        have hshl : (SymExpr.bin .and .w64 (.bin .shl .w64 x2 (.imm c2)) (.imm 0xffffffff)).eval ρ ctx snaps =
            some (v2 &&& 0xffffffff) := by
          change (do let a ← (SymExpr.bin .shl .w64 x2 (.imm c2)).eval ρ ctx snaps;
                     let b ← (SymExpr.imm 0xffffffff).eval ρ ctx snaps;
                     BinOp.and.eval .w64 a b) = some (v2 &&& 0xffffffff)
          rw [h2]; simp [SymExpr.eval, BinOp.eval, X86.Encode.truncate64]
        have hm' : matchRotateShrShl .w64 (.bin .shr .w64 (.bin .and .w64 x (.imm 0xffffffff)) (.imm c1))
            (.bin .and .w64 (.bin .shl .w64 x2 (.imm c2)) (.imm 0xffffffff)) =
            some (.w32, x, UInt64.ofNat (c1 &&& 63).toNat) := by
          unfold matchRotateShrShl
          have hx2b : (x2 == x || x2 == .bin .and .w64 x (.imm 0xffffffff)) = true := by
            rcases hx2eq with rfl | rfl <;> simp
          simp only [beq_self_eq_true, Bool.true_and, hx2b, ↓reduceIte,
            hpos, hlt, hsum, decide_true]
        have heq := matchRotateShrShl_sound hm' hshr hshl
        rw [heq, X86.Encode.truncate64]
        congr 1
        simp only [SymExpr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff,
          Option.some.injEq, BinOp.eval, X86.Encode.truncate64] at h1
        obtain ⟨_, ⟨vx1, _, _, rfl, rfl⟩, _, rfl, rfl⟩ := h1
        have hv1_m : ((vx1 &&& 0xffffffff) >>> (c1 &&& shiftMask .w64)) &&& 0xffffffff =
            (vx1 &&& 0xffffffff) >>> (c1 &&& shiftMask .w64) := by
          have hc1n : (c1 &&& shiftMask .w64).toNat < 64 := by
            show (c1 &&& 63).toNat < 64
            have : (c1 &&& 63).toNat ≤ (63 : Word).toNat := by rw [UInt64.toNat_and]; exact Nat.and_le_right
            change _ ≤ 63 at this; omega
          apply UInt64.toBitVec_inj.mp
          apply BitVec.eq_of_getLsbD_eq
          intro i hi
          have hm32 : ∀ z : Word, z &&& (0xffffffff : Word) = X86.Width.w32.truncate z := fun _ => rfl
          rw [hm32, hm32]
          simp only [X86.Encode.truncate_bits, BitVec.getLsbD_setWidth, UInt64.toBitVec_shiftRight,
            BitVec.ushiftRight_eq', BitVec.getLsbD_ushiftRight, X86.Width.bits]
          have hmod : ((c1 &&& shiftMask .w64).toBitVec % 64).toNat = (c1 &&& shiftMask .w64).toNat := by
            rw [BitVec.toNat_umod, UInt64.toNat_toBitVec]
            change (c1 &&& shiftMask .w64).toNat % 64 = (c1 &&& shiftMask .w64).toNat
            exact Nat.mod_eq_of_lt hc1n
          rw [hmod]
          by_cases hlt32 : i < 32
          · simp only [hlt32, hi, decide_true, Bool.true_and]
          · have hge32 : ¬ ((c1 &&& shiftMask .w64).toNat + i < 32) := by omega
            simp only [hlt32, hge32, decide_false, Bool.false_and, Bool.and_false]
        apply UInt64.toBitVec_inj.mp
        apply BitVec.eq_of_getLsbD_eq
        intro i hi
        have hbm := congrArg (fun z : Word => z.toBitVec.getLsbD i) hv1_m
        simp only [UInt64.toBitVec_and, BitVec.getLsbD_and] at hbm
        simp only [UInt64.toBitVec_or, UInt64.toBitVec_and, BitVec.getLsbD_or, BitVec.getLsbD_and]
        rw [← hbm]
        cases (0xffffffff : Word).toBitVec.getLsbD i <;> simp
      · cases hm
    · cases hm
  · cases hm

theorem matchRotateMasked32_sound {ρ : Env} {ctx : Word} {snaps : MemSnaps}
    {a x : SymExpr} {r va : Word}
    (hm : matchRotateMasked32 a = some (x, r))
    (ha : a.eval ρ ctx snaps = some va) :
    (SymExpr.bin .ror .w32 x (.imm r)).eval ρ ctx snaps = some (va &&& 0xffffffff) := by
  unfold matchRotateMasked32 at hm
  split at hm
  · rename_i s1 s2
    simp only [SymExpr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq, BinOp.eval, X86.Encode.truncate64] at ha
    obtain ⟨v1, h1, v2, h2, rfl⟩ := ha
    cases hp : matchRotateMasked32Pair s1 s2 with
    | some res =>
        rw [hp] at hm; cases hm
        exact matchRotateMasked32Pair_sound hp h1 h2
    | none =>
        rw [hp] at hm
        rw [UInt64.or_comm]
        exact matchRotateMasked32Pair_sound hm h2 h1
  · cases hm

/-! ## Power-of-2 identities -/

theorem isPow2_mul {w : Width} {d : Word} {k : Nat} (h : isPow2 w d k = true) (a : Word) :
    BinOp.eval .mul w a d = BinOp.eval .shl w a (UInt64.ofNat k) := by
  simp only [isPow2, decide_eq_true_eq] at h
  obtain ⟨_, hk, hd⟩ := h
  have hk64 : k < 64 := Nat.lt_of_lt_of_le hk (width_bits_le_64 w)
  have hsh := shiftMask_pow2_lt hk
  simp only [BinOp.eval, Option.some.injEq]
  apply UInt64.toNat_inj.mp
  rw [X86.Encode.truncate_nat, X86.Encode.truncate_nat, UInt64.toNat_mul,
    toNat_shl_word (by omega), hsh, mod_pow2_mod_64, mod_pow2_mod_64]
  rw [← Nat.mul_mod_mod, ← X86.Encode.truncate_nat, hd]

theorem isPow2_udiv {w : Width} {d : Word} {k : Nat} (h : isPow2 w d k = true) (a : Word) :
    BinOp.eval .udiv w a d = BinOp.eval .shr w a (UInt64.ofNat k) := by
  simp only [isPow2, decide_eq_true_eq] at h
  obtain ⟨_, hk, hd⟩ := h
  have hk64 : k < 64 := Nat.lt_of_lt_of_le hk (width_bits_le_64 w)
  have hsh := shiftMask_pow2_lt hk
  have hd0 : (w.truncate d == 0) = false := by
    rw [beq_eq_false_iff_ne]
    intro heq
    have := congrArg UInt64.toNat heq
    rw [hd] at this
    exact absurd this (Nat.ne_of_gt (Nat.two_pow_pos k))
  simp only [BinOp.eval, hd0, Bool.false_eq_true, ↓reduceIte, Option.some.injEq]
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_div, hd, X86.Encode.truncate_nat, X86.Encode.truncate_nat,
    toNat_shr_word (by omega), hsh, X86.Encode.truncate_nat]
  have hlt : a.toNat % 2 ^ w.bits / 2 ^ k < 2 ^ w.bits :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.mod_lt _ (Nat.two_pow_pos _))
  rw [Nat.mod_eq_of_lt hlt]

theorem isPow2_urem {w : Width} {d : Word} {k : Nat} (h : isPow2 w d k = true) (a : Word) :
    BinOp.eval .urem w a d = BinOp.eval .and w a (UInt64.ofNat (2 ^ k - 1)) := by
  simp only [isPow2, decide_eq_true_eq] at h
  obtain ⟨_, hk, hd⟩ := h
  have hpow_lt : 2 ^ k < 2 ^ w.bits := Nat.pow_lt_pow_right (by decide) hk
  have hpow_lt64 : 2 ^ k < 2 ^ 64 :=
    Nat.lt_of_lt_of_le hpow_lt (Nat.pow_le_pow_right (by decide) (width_bits_le_64 w))
  have hd0 : (w.truncate d == 0) = false := by
    rw [beq_eq_false_iff_ne]
    intro heq
    have := congrArg UInt64.toNat heq
    rw [hd] at this
    exact absurd this (Nat.ne_of_gt (Nat.two_pow_pos k))
  simp only [BinOp.eval, hd0, Bool.false_eq_true, ↓reduceIte, Option.some.injEq]
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_mod, hd, X86.Encode.truncate_nat, X86.Encode.truncate_nat, UInt64.toNat_and,
    UInt64.toNat_ofNat', Nat.mod_eq_of_lt (show 2 ^ k - 1 < UInt64.size by simp [UInt64.size]; omega),
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (Nat.le_of_lt hk))]
  exact (Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (Nat.two_pow_pos k)) hpow_lt)).symm

theorem findPow2_sound {w : Width} {d : Word} {k : Nat} (h : findPow2 w d = some k) :
    isPow2 w d k = true := by
  unfold findPow2 at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · rename_i hp; cases h; exact hp
    · cases h

/-! ## Granlund–Montgomery magic multiplier soundness -/

/-- Core exact-division lemma over `Nat`: if `P ≤ d * M` and `(d * M - P) * bound < P`,
then `(a * M) / P = a / d` for every `a ≤ bound`. -/
theorem magic_nat_div {a d M P bound : Nat} (hd : 0 < d) (_hP : 0 < P) (ha : a ≤ bound)
    (hlo : P ≤ d * M) (hhi : (d * M - P) * bound < P) :
    (a * M) / P = a / d := by
  let q := a / d
  let r := a % d
  have hqr : a = q * d + r := by
    have := Nat.div_add_mod a d
    rw [Nat.mul_comm] at this
    exact this.symm
  have hr : r < d := Nat.mod_lt a hd
  let e := d * M - P
  have hdM : d * M = P + e := by omega
  have hlower : q * P ≤ a * M := by
    have h1 : d * (q * P) ≤ d * (a * M) := by
      calc d * (q * P) = (q * d) * P := by rw [← Nat.mul_assoc, Nat.mul_comm d q]
        _ ≤ a * P := Nat.mul_le_mul_right P (by omega)
        _ ≤ a * (d * M) := Nat.mul_le_mul_left a hlo
        _ = d * (a * M) := by rw [← Nat.mul_assoc, Nat.mul_comm a d, Nat.mul_assoc]
    exact Nat.le_of_mul_le_mul_left h1 hd
  have hupper : a * M < (q + 1) * P := by
    have h1 : d * (a * M) < d * ((q + 1) * P) := by
      have hdaM : d * (a * M) = q * d * P + r * P + a * e := by
        calc d * (a * M) = a * (d * M) := by rw [← Nat.mul_assoc, Nat.mul_comm d a, Nat.mul_assoc]
          _ = a * (P + e) := by rw [hdM]
          _ = a * P + a * e := Nat.mul_add a P e
          _ = (q * d + r) * P + a * e := by rw [← hqr]
          _ = q * d * P + r * P + a * e := by rw [Nat.add_mul]
      have hae : a * e < P :=
        Nat.lt_of_le_of_lt (by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left e ha) hhi
      have hrP : r * P ≤ (d - 1) * P := Nat.mul_le_mul_right P (by omega)
      have hrhs : d * ((q + 1) * P) = q * d * P + (d - 1) * P + P := by
        have hd1 : (d - 1) + 1 = d := by omega
        calc d * ((q + 1) * P) = d * (q * P + P) := by rw [Nat.add_mul, Nat.one_mul]
          _ = d * (q * P) + d * P := Nat.mul_add _ _ _
          _ = q * d * P + ((d - 1) + 1) * P := by rw [← Nat.mul_assoc, Nat.mul_comm d q, hd1]
          _ = q * d * P + (d - 1) * P + P := by rw [Nat.add_mul, Nat.one_mul, Nat.add_assoc]
      omega
    exact Nat.lt_of_mul_lt_mul_left h1
  exact Nat.div_eq_of_lt_le hlower hupper

/-- Case 1 (64-bit simple multiply-shift): `(mulHi a m) >>> s = a / d`. -/
theorem checkMagicSimple_sound {d m : Word} {s : Nat} (h : checkMagicSimple d m s = true) (a : Word) :
    UInt64.ofNat ((a.toNat * m.toNat) / 2 ^ 64) >>> (UInt64.ofNat s &&& 63) = a / d := by
  simp only [checkMagicSimple, decide_eq_true_eq] at h
  obtain ⟨hd, hs, hlo, hhi⟩ := h
  have hsh : (UInt64.ofNat s &&& 63).toNat = s := shiftMask_pow2_lt (w := .w64) hs
  have ha : a.toNat ≤ 2 ^ 64 - 1 := by have := a.toNat_lt_size; simp [UInt64.size] at this; omega
  have hm : m.toNat < 2 ^ 64 := m.toNat_lt_size
  have hhi_lt : (a.toNat * m.toNat) / 2 ^ 64 < 2 ^ 64 := by
    rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 2 ^ 64)]
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right m.toNat (Nat.le_of_lt a.toNat_lt_size))
      (Nat.mul_lt_mul_of_pos_left hm (by decide))
  apply UInt64.toNat_inj.mp
  rw [toNat_shr_word (by omega), hsh, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hhi_lt,
    Nat.div_div_eq_div_mul, ← Nat.pow_add, UInt64.toNat_div]
  exact magic_nat_div (by omega) (Nat.two_pow_pos _) ha hlo hhi

/-- Case 2 (64-bit add-shift multiply-high):
`hi = mulHi a m'`, `(((a - hi) >>> 1) + hi) >>> (s - 1) = a / d`. -/
theorem checkMagicAddShift_sound {d m' : Word} {s : Nat} (h : checkMagicAddShift d m' s = true) (a : Word) :
    let hi : Word := UInt64.ofNat ((a.toNat * m'.toNat) / 2 ^ 64)
    (((a - hi) >>> (1 &&& 63)) + hi) >>> (UInt64.ofNat (s - 1) &&& 63) = a / d := by
  simp only [checkMagicAddShift, decide_eq_true_eq] at h
  obtain ⟨hd, hs1, hs64, hlo, hhi⟩ := h
  intro hi
  have ha_lt : a.toNat < 2 ^ 64 := a.toNat_lt_size
  have hm_lt : m'.toNat < 2 ^ 64 := m'.toNat_lt_size
  have ha : a.toNat ≤ 2 ^ 64 - 1 := by omega
  have hhi_le : (a.toNat * m'.toNat) / 2 ^ 64 ≤ a.toNat := by
    rw [Nat.div_le_iff_le_mul_add_pred (by decide : 0 < 2 ^ 64)]
    have hmul : a.toNat * m'.toNat ≤ a.toNat * 2 ^ 64 := Nat.mul_le_mul_left _ (Nat.le_of_lt hm_lt)
    omega
  have hhi_nat : hi.toNat = (a.toNat * m'.toNat) / 2 ^ 64 := by
    simp only [hi, UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hhi_le ha_lt)
  have hsub_nat : (a - hi).toNat = a.toNat - hi.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hhi_nat]; exact hhi_le)]
  have h1and : ((1 : Word) &&& 63).toNat = 1 := by decide
  have hshr1_nat : ((a - hi) >>> (1 &&& 63)).toNat = (a.toNat - hi.toNat) / 2 := by
    rw [toNat_shr_word (by omega), h1and, hsub_nat]
  have hadd_lt : (a.toNat - hi.toNat) / 2 + hi.toNat < 2 ^ 64 := by omega
  have hadd_nat : (((a - hi) >>> (1 &&& 63)) + hi).toNat = (a.toNat + hi.toNat) / 2 := by
    rw [UInt64.toNat_add, hshr1_nat, Nat.mod_eq_of_lt hadd_lt]
    omega
  have hs_lt : s - 1 < X86.Width.w64.bits := by simp [X86.Width.bits]; omega
  have hsh : (UInt64.ofNat (s - 1) &&& 63).toNat = s - 1 := shiftMask_pow2_lt (w := .w64) hs_lt
  apply UInt64.toNat_inj.mp
  rw [toNat_shr_word (by simp [X86.Width.bits] at hs_lt; omega), hsh, hadd_nat, Nat.div_div_eq_div_mul,
    show 2 * 2 ^ (s - 1) = 2 ^ s by
      cases s with | zero => omega | succ k => simp [Nat.pow_succ, Nat.mul_comm],
    hhi_nat]
  have hcomb : (a.toNat + (a.toNat * m'.toNat) / 2 ^ 64) / 2 ^ s =
      (a.toNat * (2 ^ 64 + m'.toNat)) / 2 ^ (64 + s) := by
    rw [Nat.pow_add, ← Nat.div_div_eq_div_mul]
    congr 1
    rw [Nat.mul_add, Nat.add_comm (a.toNat * 2 ^ 64), Nat.add_mul_div_right _ _ (by decide : 0 < 2 ^ 64),
      Nat.add_comm]
  rw [hcomb, UInt64.toNat_div]
  exact magic_nat_div (by omega) (Nat.two_pow_pos _) ha hlo hhi

/-- 32-bit Case 1 (simple multiply-shift via 64-bit `mul`):
`((a &&& 0xffffffff) * m) >>> (32 + s) = (w32.truncate a) / d`. -/
theorem checkMagic32_sound {d m : Word} {s : Nat} (h : checkMagic32 d m s = true) (a : Word) :
    ((a &&& 0xffffffff) * m) >>> (UInt64.ofNat (32 + s) &&& 63) = X86.Width.w32.truncate a / d := by
  simp only [checkMagic32, decide_eq_true_eq] at h
  obtain ⟨hd, _, hm, hs, hlo, hhi⟩ := h
  have hu : a &&& 0xffffffff = X86.Width.w32.truncate a := rfl
  have hu_lt : (X86.Width.w32.truncate a).toNat < 2 ^ 32 := Xv.Select.Proof.truncate_lt .w32 a
  have hu_le : (X86.Width.w32.truncate a).toNat ≤ 2 ^ 32 - 1 := by omega
  have hprod_lt : (X86.Width.w32.truncate a).toNat * m.toNat < 2 ^ 64 := by
    calc (X86.Width.w32.truncate a).toNat * m.toNat
        ≤ (2 ^ 32 - 1) * 2 ^ 32 := Nat.mul_le_mul hu_le hm
      _ < 2 ^ 64 := by decide
  have hs64 : 32 + s < X86.Width.w64.bits := by simp [X86.Width.bits]; omega
  have hsh : (UInt64.ofNat (32 + s) &&& 63).toNat = 32 + s := shiftMask_pow2_lt (w := .w64) hs64
  apply UInt64.toNat_inj.mp
  rw [hu, toNat_shr_word (by omega), hsh, UInt64.toNat_mul, Nat.mod_eq_of_lt hprod_lt, UInt64.toNat_div]
  exact magic_nat_div (by omega) (Nat.two_pow_pos _) hu_le hlo hhi

/-- 32-bit Case 2 (add-shift multiply-high via 64-bit `mul`):
`u = a &&& 0xffffffff`, `hi = (u * m') >>> 32`, `(((u - hi) >>> 1) + hi) >>> (s - 1) = u / d`. -/
theorem checkMagic32AddShift_sound {d m' : Word} {s : Nat} (h : checkMagic32AddShift d m' s = true) (a : Word) :
    let u : Word := a &&& 0xffffffff
    let hi : Word := (u * m') >>> (32 &&& 63)
    (((u - hi) >>> (1 &&& 63)) + hi) >>> (UInt64.ofNat (s - 1) &&& 63) = X86.Width.w32.truncate a / d := by
  simp only [checkMagic32AddShift, decide_eq_true_eq] at h
  obtain ⟨hd, _, hm, hs1, hs32, hlo, hhi⟩ := h
  intro u hi
  have hu_eq : u = X86.Width.w32.truncate a := rfl
  have hu_lt : u.toNat < 2 ^ 32 := Xv.Select.Proof.truncate_lt .w32 a
  have hu_le : u.toNat ≤ 2 ^ 32 - 1 := by omega
  have hprod_lt : u.toNat * m'.toNat < 2 ^ 64 := by
    calc u.toNat * m'.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul hu_le (by omega)
      _ < 2 ^ 64 := by decide
  have h32and : ((32 : Word) &&& 63).toNat = 32 := by decide
  have hhi_nat : hi.toNat = (u.toNat * m'.toNat) / 2 ^ 32 := by
    simp only [hi]
    rw [toNat_shr_word (by omega), h32and, UInt64.toNat_mul, Nat.mod_eq_of_lt hprod_lt]
  have hhi_le : hi.toNat ≤ u.toNat := by
    rw [hhi_nat, Nat.div_le_iff_le_mul_add_pred (by decide : 0 < 2 ^ 32)]
    have hmul : u.toNat * m'.toNat ≤ u.toNat * 2 ^ 32 := Nat.mul_le_mul_left _ (Nat.le_of_lt hm)
    omega
  have hsub_nat : (u - hi).toNat = u.toNat - hi.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; exact hhi_le)]
  have h1and : ((1 : Word) &&& 63).toNat = 1 := by decide
  have hshr1_nat : ((u - hi) >>> (1 &&& 63)).toNat = (u.toNat - hi.toNat) / 2 := by
    rw [toNat_shr_word (by omega), h1and, hsub_nat]
  have hadd_lt : (u.toNat - hi.toNat) / 2 + hi.toNat < 2 ^ 64 := by omega
  have hadd_nat : (((u - hi) >>> (1 &&& 63)) + hi).toNat = (u.toNat + hi.toNat) / 2 := by
    rw [UInt64.toNat_add, hshr1_nat, Nat.mod_eq_of_lt hadd_lt]; omega
  have hs64 : s - 1 < X86.Width.w64.bits := by simp [X86.Width.bits]; omega
  have hsh : (UInt64.ofNat (s - 1) &&& 63).toNat = s - 1 := shiftMask_pow2_lt (w := .w64) hs64
  apply UInt64.toNat_inj.mp
  rw [toNat_shr_word (by omega), hsh, hadd_nat, Nat.div_div_eq_div_mul,
    show 2 * 2 ^ (s - 1) = 2 ^ s by
      cases s with | zero => omega | succ k => simp [Nat.pow_succ, Nat.mul_comm],
    hhi_nat, ← hu_eq, UInt64.toNat_div]
  have hcomb : (u.toNat + (u.toNat * m'.toNat) / 2 ^ 32) / 2 ^ s =
      (u.toNat * (2 ^ 32 + m'.toNat)) / 2 ^ (32 + s) := by
    rw [Nat.pow_add, ← Nat.div_div_eq_div_mul]
    congr 1
    rw [Nat.mul_add, Nat.add_comm (u.toNat * 2 ^ 32), Nat.add_mul_div_right _ _ (by decide : 0 < 2 ^ 32),
      Nat.add_comm]
  rw [hcomb]
  exact magic_nat_div (by omega) (Nat.two_pow_pos _) hu_le hlo hhi

/-- Remainder from quotient: `a - (a / d) * d = a % d` at any width `w`. -/
theorem urem_sub_mul_udiv (w : Width) (a d : Word) :
    w.truncate (a - w.truncate ((w.truncate a / w.truncate d) * d)) = w.truncate a % w.truncate d := by
  let ua := w.truncate a
  let ud := w.truncate d
  have hmul : w.truncate ((ua / ud) * d) = (ua / ud) * ud := by
    rw [X86.Encode.truncate_mul]
    have hq_lt : (ua / ud).toNat < 2 ^ w.bits :=
      Nat.lt_of_le_of_lt (by rw [UInt64.toNat_div]; exact Nat.div_le_self _ _) (Xv.Select.Proof.truncate_lt w a)
    rw [Xv.Select.Proof.truncate_eq_self hq_lt]
    apply Xv.Select.Proof.truncate_eq_self
    rw [UInt64.toNat_mul, UInt64.toNat_div]
    have hdm : ua.toNat / ud.toNat * ud.toNat ≤ ua.toNat := by
      rw [Nat.mul_comm]; exact Nat.mul_div_le ua.toNat ud.toNat
    have hua_lt : ua.toNat < 2 ^ w.bits := Xv.Select.Proof.truncate_lt w a
    have hle64 : 2 ^ w.bits ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (width_bits_le_64 w)
    have hlt_w' : ua.toNat / ud.toNat * ud.toNat < 2 ^ w.bits := Nat.lt_of_le_of_lt hdm hua_lt
    have hlt_64' : ua.toNat / ud.toNat * ud.toNat < 2 ^ 64 := Nat.lt_of_lt_of_le hlt_w' hle64
    rw [Nat.mod_eq_of_lt hlt_64']
    exact hlt_w'
  change w.truncate (a - w.truncate ((ua / ud) * d)) = ua % ud
  rw [hmul]
  have hle : ((ua / ud) * ud).toNat ≤ ua.toNat := by
    rw [UInt64.toNat_mul, UInt64.toNat_div]
    have hdm : ua.toNat / ud.toNat * ud.toNat ≤ ua.toNat := by
      rw [Nat.mul_comm]; exact Nat.mul_div_le ua.toNat ud.toNat
    have hlt64 : ua.toNat < 2 ^ 64 := ua.toNat_lt_size
    rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hdm hlt64)]
    exact hdm
  have hsub_eq : w.truncate (a - (ua / ud) * ud) = w.truncate (ua - (ua / ud) * ud) := by
    have h1 := X86.Encode.truncate_alu .sub w a ((ua / ud) * ud)
    have h2 := X86.Encode.truncate_alu .sub w ua ((ua / ud) * ud)
    simp only [X86.AluOp.eval, ua, X86.Encode.truncate_truncate] at h1 h2
    exact h1.trans h2.symm
  rw [hsub_eq]
  apply UInt64.toNat_inj.mp
  rw [X86.Encode.truncate_nat, UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; exact hle),
    UInt64.toNat_mod, UInt64.toNat_mul, UInt64.toNat_div]
  have hdm := Nat.div_add_mod ua.toNat ud.toNat
  have hlt_w : ua.toNat < 2 ^ w.bits := Xv.Select.Proof.truncate_lt w a
  have hlt64 : ua.toNat < 2 ^ 64 := ua.toNat_lt_size
  have hmul_le : ua.toNat / ud.toNat * ud.toNat ≤ ua.toNat := by
    rw [Nat.mul_comm]; exact Nat.mul_div_le ua.toNat ud.toNat
  rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hmul_le hlt64)]
  have hdiff : ua.toNat - ua.toNat / ud.toNat * ud.toNat = ua.toNat % ud.toNat := by
    rw [Nat.mul_comm] at hdm; omega
  rw [hdiff, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) hlt_w)]

/-! ## Normalization soundness (`mkAdd64`, `mkBinOrdered`, `mkBin`, `SymExpr.norm`) -/

theorem even_or_one_eq_add_one {v : Word} (heven : v &&& 1 = 0) : v ||| 1 = v + 1 := by
  have hv_mod : v.toNat % 2 = 0 := by
    have h := congrArg UInt64.toNat heven
    rw [UInt64.toNat_and, show (1 : Word).toNat = 1 from rfl, show (0 : Word).toNat = 0 from rfl,
      Nat.and_one_is_mod] at h
    exact h
  have hv_lt : v.toNat < 2 ^ 64 := v.toNat_lt_size
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_or, UInt64.toNat_add, show (1 : Word).toNat = 1 from rfl,
    Nat.mod_eq_of_lt (by omega : v.toNat + 1 < 2 ^ 64)]
  have h1 : v.toNat = 2 ^ 1 * (v.toNat / 2) := by omega
  rw [h1, ← Nat.two_pow_add_eq_or_of_lt (by decide : 1 < 2 ^ 1)]

theorem shl_nonzero_even (v s : Word) (hs : (s &&& 63) ≠ 0) : (v <<< (s &&& 63)) &&& 1 = 0 := by
  have hlt : (s &&& 63).toNat < 64 := Xv.Select.Proof.masked_lt .w64 s
  have hpos : 0 < (s &&& 63).toNat := by
    have hne : (s &&& 63).toNat ≠ 0 := fun h0 => hs (UInt64.toNat_inj.mp h0)
    omega
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_and, show (1 : Word).toNat = 1 from rfl, show (0 : Word).toNat = 0 from rfl,
    Nat.and_one_is_mod, toNat_shl_word hlt,
    Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 2 ^ 64)]
  have hdvd : 2 ∣ 2 ^ (s &&& 63).toNat := by
    cases hk : (s &&& 63).toNat with
    | zero => omega
    | succ k => rw [Nat.pow_succ]; exact Nat.dvd_mul_left 2 _
  exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans hdvd (Nat.dvd_mul_left _ _))

theorem shl_one_eq_add_w64 (v : Word) : v <<< (1 &&& 63) = v + v := by
  apply UInt64.toNat_inj.mp
  rw [toNat_shl_word (by decide), show ((1 : Word) &&& 63).toNat = 1 from by decide, UInt64.toNat_add]
  change (v.toNat * 2) % 2 ^ 64 = (v.toNat + v.toNat) % 2 ^ 64
  congr 1; omega

private theorem add_shl_const_w64 (v : Word) (k : Word) (hk : (k &&& 63).toNat < 64) :
    v + (v <<< (k &&& 63)) = v * UInt64.ofNat (1 + 2 ^ (k &&& 63).toNat) := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_add, toNat_shl_word hk, UInt64.toNat_mul, UInt64.toNat_ofNat']
  rw [Nat.add_mod_mod, Nat.mul_mod_mod]
  congr 1
  rw [Nat.mul_add, Nat.mul_one]

theorem matchAddShlSelf_sound {ρ : Env} {ctx : Word} {snaps : MemSnaps} {a b r : SymExpr} {va vb : Word}
    (hm : matchAddShlSelf a b = some r)
    (ha : a.eval ρ ctx snaps = some va) (hb : b.eval ρ ctx snaps = some vb) :
    r.eval ρ ctx snaps = some (va + vb) := by
  have hcase : ∀ (x y : SymExpr) (k c : Word),
      x = y → (k &&& 63).toNat < 64 → c = UInt64.ofNat (1 + 2 ^ (k &&& 63).toNat) →
      ∀ {vx vy : Word}, x.eval ρ ctx snaps = some vx →
      (SymExpr.bin .shl .w64 y (.imm k)).eval ρ ctx snaps = some vy →
      (SymExpr.bin .mul .w64 x (.imm c)).eval ρ ctx snaps = some (vx + vy) := by
    intro x y k c hxy hk hc vx vy hx hsh
    subst hxy hc
    simp only [SymExpr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
      BinOp.eval, X86.Encode.truncate64, shiftMask] at hsh
    obtain ⟨vx', hx', _, rfl, rfl⟩ := hsh
    rw [hx] at hx'; cases hx'
    simp only [SymExpr.eval, Option.bind_eq_bind, hx, Option.bind_some, BinOp.eval,
      X86.Encode.truncate64, Option.some.injEq]
    exact (add_shl_const_w64 vx k hk).symm
  unfold matchAddShlSelf at hm
  split at hm
  · split at hm
    · rename_i hxy; cases hm
      exact hcase _ _ 1 3 (by simpa using hxy) (by decide) (by decide) ha hb
    · cases hm
  · split at hm
    · rename_i hxy; cases hm; rw [UInt64.add_comm]
      exact hcase _ _ 1 3 (by simpa using hxy) (by decide) (by decide) hb ha
    · cases hm
  · split at hm
    · rename_i hxy; cases hm
      exact hcase _ _ 2 5 (by simpa using hxy) (by decide) (by decide) ha hb
    · cases hm
  · split at hm
    · rename_i hxy; cases hm; rw [UInt64.add_comm]
      exact hcase _ _ 2 5 (by simpa using hxy) (by decide) (by decide) hb ha
    · cases hm
  · split at hm
    · rename_i hxy; cases hm
      exact hcase _ _ 3 9 (by simpa using hxy) (by decide) (by decide) ha hb
    · cases hm
  · split at hm
    · rename_i hxy; cases hm; rw [UInt64.add_comm]
      exact hcase _ _ 3 9 (by simpa using hxy) (by decide) (by decide) hb ha
    · cases hm
  · cases hm

theorem mkAdd64Core_sound {ρ : Env} {ctx : Word} {snaps : MemSnaps} {a b : SymExpr} {va vb : Word}
    (ha : a.eval ρ ctx snaps = some va) (hb : b.eval ρ ctx snaps = some vb) :
    (mkAdd64Core a b).eval ρ ctx snaps = some (va + vb) := by
  unfold mkAdd64Core
  by_cases hab : (a == b) = true
  · have hab' : a = b := by simpa using hab
    subst hab'; rw [ha] at hb; cases hb
    simp only [hab, ↓reduceIte, SymExpr.eval, BinOp.eval, X86.Encode.truncate64, shiftMask,
      Option.bind_eq_bind, ha, Option.bind_some, shl_one_eq_add_w64]
  · simp only [hab, Bool.false_eq_true, ↓reduceIte]
    cases hm : matchAddShlSelf a b with
    | some r => exact matchAddShlSelf_sound hm ha hb
    | none =>
        dsimp only
        split
        · simp only [SymExpr.eval, BinOp.eval, X86.Encode.truncate64, Option.bind_eq_bind,
            ha, hb, Option.bind_some, UInt64.add_comm]
        · simp only [SymExpr.eval, BinOp.eval, X86.Encode.truncate64, Option.bind_eq_bind,
            ha, hb, Option.bind_some]

theorem mkAdd64_sound {ρ : Env} {ctx : Word} {snaps : MemSnaps} {a b : SymExpr} {va vb : Word}
    (ha : a.eval ρ ctx snaps = some va) (hb : b.eval ρ ctx snaps = some vb) :
    (mkAdd64 a b).eval ρ ctx snaps = some (va + vb) := by
  unfold mkAdd64
  split
  · simp only [SymExpr.eval, Option.some.injEq] at ha hb; subst ha hb; rfl
  · simp only [SymExpr.eval, Option.some.injEq] at hb; subst hb
    rw [UInt64.add_zero]; exact ha
  · simp only [SymExpr.eval, Option.some.injEq] at ha; subst ha
    rw [UInt64.zero_add]; exact hb
  · simp only [SymExpr.eval, BinOp.eval, X86.Encode.truncate64, Option.bind_eq_bind,
      Option.bind_eq_some_iff, Option.some.injEq] at ha hb
    obtain ⟨vx, hvx, _, rfl, rfl⟩ := ha
    subst hb
    dsimp only
    split
    · rename_i hsum
      simp only [beq_iff_eq] at hsum
      simp only [hvx, Option.some.injEq]
      rw [UInt64.add_assoc, hsum, UInt64.add_zero]
    · simp only [SymExpr.eval, BinOp.eval, X86.Encode.truncate64, Option.bind_eq_bind,
        hvx, Option.bind_some, Option.some.injEq]
      rw [UInt64.add_assoc]
  · simp only [SymExpr.eval, BinOp.eval, X86.Encode.truncate64, Option.bind_eq_bind,
      Option.bind_eq_some_iff, Option.some.injEq] at ha hb
    obtain ⟨vy, hvy, _, rfl, rfl⟩ := hb
    subst ha
    dsimp only
    split
    · rename_i hsum
      simp only [beq_iff_eq] at hsum
      simp only [hvy, Option.some.injEq]
      rw [← UInt64.add_assoc, UInt64.add_comm _ vy, UInt64.add_assoc, hsum, UInt64.add_zero]
    · simp only [SymExpr.eval, BinOp.eval, X86.Encode.truncate64, Option.bind_eq_bind,
        hvy, Option.bind_some, Option.some.injEq]
      rw [← UInt64.add_assoc, UInt64.add_comm vy, UInt64.add_assoc]
  · simp only [SymExpr.eval, BinOp.eval, X86.Encode.truncate64, Option.bind_eq_bind,
      Option.bind_eq_some_iff, Option.some.injEq] at ha hb
    obtain ⟨vx, hvx, _, rfl, rfl⟩ := ha
    obtain ⟨vy, hvy, _, rfl, rfl⟩ := hb
    have hcore := mkAdd64Core_sound hvx hvy
    have hreassoc : ∀ c1 c2 : Word, (vx + c1) + (vy + c2) = (vx + vy) + (c1 + c2) := fun c1 c2 => by
      calc (vx + c1) + (vy + c2) = vx + (c1 + (vy + c2)) := UInt64.add_assoc _ _ _
        _ = vx + ((vy + c2) + c1) := by rw [UInt64.add_comm c1]
        _ = vx + (vy + (c2 + c1)) := by rw [UInt64.add_assoc]
        _ = (vx + vy) + (c1 + c2) := by rw [← UInt64.add_assoc, UInt64.add_comm c2 c1]
    dsimp only
    split
    · rename_i hsum
      simp only [beq_iff_eq] at hsum
      simp only [hcore, Option.some.injEq]
      rw [hreassoc, hsum, UInt64.add_zero]
    · simp only [SymExpr.eval, BinOp.eval, X86.Encode.truncate64, Option.bind_eq_bind,
        hcore, Option.bind_some, Option.some.injEq]
      exact (hreassoc _ _).symm
  · simp only [SymExpr.eval, BinOp.eval, X86.Encode.truncate64, Option.bind_eq_bind,
      Option.bind_eq_some_iff, Option.some.injEq] at ha
    obtain ⟨vx, hvx, _, rfl, rfl⟩ := ha
    have hcore := mkAdd64Core_sound hvx hb
    simp only [SymExpr.eval, BinOp.eval, X86.Encode.truncate64, Option.bind_eq_bind,
      hcore, Option.bind_some, Option.some.injEq]
    rw [UInt64.add_assoc, UInt64.add_comm vb, ← UInt64.add_assoc]
  · simp only [SymExpr.eval, BinOp.eval, X86.Encode.truncate64, Option.bind_eq_bind,
      Option.bind_eq_some_iff, Option.some.injEq] at hb
    obtain ⟨vy, hvy, _, rfl, rfl⟩ := hb
    have hcore := mkAdd64Core_sound ha hvy
    simp only [SymExpr.eval, BinOp.eval, X86.Encode.truncate64, Option.bind_eq_bind,
      hcore, Option.bind_some, Option.some.injEq]
    exact UInt64.add_assoc va vy _
  · exact mkAdd64Core_sound ha hb

theorem mkBinOrdered_sound {ρ : Env} {ctx : Word} {snaps : MemSnaps} {o : BinOp} {w : Width}
    {a b : SymExpr} {va vb v : Word}
    (ha : a.eval ρ ctx snaps = some va) (hb : b.eval ρ ctx snaps = some vb)
    (he : o.eval w va vb = some v) :
    (mkBinOrdered o w a b).eval ρ ctx snaps = some v := by
  unfold mkBinOrdered
  split
  · simp only [SymExpr.eval, Option.some.injEq] at ha hb
    subst ha hb; rw [he]; rfl
  · cases o with
    | add =>
        dsimp only
        cases w with
        | w64 =>
            simp only [BinOp.eval, X86.Encode.truncate64, Option.some.injEq] at he; subst he
            exact mkAdd64_sound ha hb
        | w8 | w16 | w32 =>
            by_cases hab : (a == b) = true
            · have hab' : a = b := by simpa using hab
              subst hab'; rw [ha] at hb; cases hb
              simp only [hab, ↓reduceIte, SymExpr.eval, BinOp.eval, shiftMask, Option.bind_eq_bind,
                ha, Option.bind_some] at he ⊢
              rw [← he]; congr 1
              apply UInt64.toNat_inj.mp
              rw [X86.Encode.truncate_nat, X86.Encode.truncate_nat, UInt64.toNat_add,
                toNat_shl_word (by decide), show ((1 : Word) &&& 31).toNat = 1 from by decide,
                mod_pow2_mod_64, mod_pow2_mod_64]
              congr 1; omega
            · simp only [hab, Bool.false_eq_true, ↓reduceIte, SymExpr.eval, Option.bind_eq_bind,
                ha, hb, Option.bind_some, he]
    | sub =>
        dsimp only
        by_cases hab : (a == b) = true
        · have hab' : a = b := by simpa using hab
          subst hab'; rw [ha] at hb; cases hb
          simp only [hab, ↓reduceIte, SymExpr.eval]
          simp only [BinOp.eval, UInt64.sub_self, Xv.Select.Proof.truncate_zero, Option.some.injEq] at he
          exact congrArg some he
        · simp only [hab, Bool.false_eq_true, ↓reduceIte]
          cases w with
          | w64 =>
              cases b with
              | imm k =>
                  simp only [SymExpr.eval, Option.some.injEq] at hb; subst hb
                  simp only [BinOp.eval, X86.Encode.truncate64, Option.some.injEq] at he; subst he
                  by_cases hk : (k == 0) = true
                  · have hk0 : k = 0 := by simpa using hk
                    subst hk0; simp [ha]
                  · simp only [hk, Bool.false_eq_true, ↓reduceIte]
                    have hadd := mkAdd64_sound ha (b := .imm (0 - k)) (vb := 0 - k) rfl
                    rw [hadd]; congr 1
                    rw [UInt64.zero_sub, ← UInt64.sub_eq_add_neg]
              | _ => rw [SymExpr.eval, Option.bind_eq_bind, ha, hb]; exact he
          | w8 | w16 | w32 =>
              rw [SymExpr.eval, Option.bind_eq_bind, ha, hb]; exact he
    | mul =>
        dsimp only; split
        · simp only [SymExpr.eval, Option.some.injEq] at hb; subst hb
          simp only [BinOp.eval, UInt64.mul_zero, Xv.Select.Proof.truncate_zero, Option.some.injEq] at he
          exact congrArg some he
        · simp only [SymExpr.eval, Option.some.injEq] at hb; subst hb
          split
          · rename_i hw
            have hw' : w = .w64 := by simpa using hw
            subst hw'; rw [ha]
            simp only [BinOp.eval, X86.Encode.truncate64, UInt64.mul_one, Option.some.injEq] at he
            exact congrArg some he
          · rw [SymExpr.eval, Option.bind_eq_bind, ha, SymExpr.eval, Option.bind_some]; exact he
        · simp only [SymExpr.eval, Option.some.injEq] at hb; subst hb
          split
          · rename_i sh hfp
            rw [SymExpr.eval]; simp only [Option.bind_eq_bind, ha, SymExpr.eval, Option.bind_some]
            rw [← isPow2_mul (findPow2_sound hfp) va, he]
          · rw [SymExpr.eval]; simp only [Option.bind_eq_bind, ha, SymExpr.eval, Option.bind_some]; exact he
        · rw [SymExpr.eval, Option.bind_eq_bind, ha, hb]; exact he
    | and =>
        dsimp only; split
        · simp only [SymExpr.eval, Option.some.injEq] at hb; subst hb
          simp only [BinOp.eval, UInt64.and_zero, Xv.Select.Proof.truncate_zero, Option.some.injEq] at he
          exact congrArg some he
        · simp only [SymExpr.eval, Option.some.injEq] at hb; subst hb
          split
          · rename_i hcond
            simp only [Bool.and_eq_true, beq_iff_eq] at hcond
            obtain ⟨rfl, rfl⟩ := hcond
            rw [ha]
            simp only [BinOp.eval, X86.Encode.truncate64, Option.some.injEq] at he
            have : va &&& X86.Width.w64.mask = va := X86.Encode.truncate64 va
            rw [this] at he; exact congrArg some he
          · split
            · rename_i hcond
              simp only [Bool.and_eq_true, beq_iff_eq] at hcond
              obtain ⟨rfl, rfl⟩ := hcond
              cases hm : matchRotateMasked32 a with
              | none =>
                  rw [SymExpr.eval]; simp only [Option.bind_eq_bind, ha, SymExpr.eval, Option.bind_some]; exact he
              | some xr =>
                  rcases xr with ⟨x, r⟩
                  simp only [BinOp.eval, X86.Encode.truncate64, Option.some.injEq] at he
                  rw [← he]
                  exact matchRotateMasked32_sound hm ha
            · rw [SymExpr.eval]; simp only [Option.bind_eq_bind, ha, SymExpr.eval, Option.bind_some]; exact he
        · split
          · rename_i hcond
            simp only [Bool.and_eq_true, beq_iff_eq] at hcond
            obtain ⟨rfl, haeq⟩ := hcond
            rw [haeq] at ha; rw [ha] at hb; cases hb; rw [haeq, ha]
            simp only [BinOp.eval, X86.Encode.truncate64, UInt64.and_self, Option.some.injEq] at he
            exact congrArg some he
          · rw [SymExpr.eval, Option.bind_eq_bind, ha, hb]; exact he
    | or =>
        dsimp only; split
        · simp only [SymExpr.eval, Option.some.injEq] at hb; subst hb
          split
          · rename_i hw
            have hw' : w = .w64 := by simpa using hw
            subst hw'; rw [ha]
            simp only [BinOp.eval, X86.Encode.truncate64, UInt64.or_zero, Option.some.injEq] at he
            exact congrArg some he
          · rw [SymExpr.eval]; simp only [Option.bind_eq_bind, ha, SymExpr.eval, Option.bind_some]; exact he
        · simp only [SymExpr.eval, Option.some.injEq] at hb; subst hb
          split
          · rename_i hm
            simp only [beq_iff_eq] at hm
            simp only [SymExpr.eval]
            simp only [BinOp.eval, Option.some.injEq] at he
            rw [← he]; congr 1
            apply UInt64.toBitVec_inj.mp
            apply BitVec.eq_of_getLsbD_eq
            intro i hi
            have hm_bits := congrArg UInt64.toBitVec hm
            have hm_i := congrArg (fun bv => bv.getLsbD i) hm_bits
            simp only [X86.Encode.truncate_bits, X86.Encode.mask_bits, BitVec.getLsbD_setWidth,
              BitVec.getLsbD_allOnes, hi, decide_true, Bool.true_and] at hm_i
            simp only [X86.Encode.truncate_bits, X86.Encode.mask_bits, UInt64.toBitVec_or,
              BitVec.getLsbD_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_allOnes, hi, decide_true,
              Bool.true_and]
            by_cases hlt : i < w.bits
            · simp only [hlt, decide_true, Bool.true_and] at hm_i ⊢
              rw [hm_i, Bool.or_true]
            · simp [hlt]
          · split
            · rename_i hcond
              simp only [Bool.and_eq_true, beq_iff_eq] at hcond
              obtain ⟨rfl, rfl⟩ := hcond
              split
              · split
                · rename_i hsnz
                  simp only [bne_iff_ne] at hsnz
                  simp only [BinOp.eval, X86.Encode.truncate64, Option.some.injEq] at he
                  have hev : va &&& 1 = 0 := by
                    simp only [SymExpr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff,
                      Option.some.injEq, BinOp.eval, X86.Encode.truncate64, shiftMask] at ha
                    obtain ⟨vx, _, _, rfl, rfl⟩ := ha
                    exact shl_nonzero_even vx _ hsnz
                  rw [← he, even_or_one_eq_add_one hev]
                  exact mkAdd64_sound ha rfl
                · rw [SymExpr.eval, Option.bind_eq_bind, ha]; exact he
              · rw [SymExpr.eval, Option.bind_eq_bind, ha]; exact he
            · rw [SymExpr.eval, Option.bind_eq_bind, ha]; exact he
        · split
          · rename_i hcond
            simp only [Bool.and_eq_true, beq_iff_eq] at hcond
            obtain ⟨rfl, haeq⟩ := hcond
            rw [haeq] at ha; rw [ha] at hb; cases hb; rw [haeq, ha]
            simp only [BinOp.eval, X86.Encode.truncate64, UInt64.or_self, Option.some.injEq] at he
            exact congrArg some he
          · cases hm : matchRotateOr w a b with
            | none => rw [SymExpr.eval, Option.bind_eq_bind, ha, hb]; exact he
            | some res =>
                rcases res with ⟨rw, x, r⟩
                simp only [BinOp.eval, Option.some.injEq] at he
                rw [← he]
                exact matchRotateOr_sound hm ha hb
    | xor =>
        dsimp only; split
        · rename_i hab
          have hab' : a = b := by simpa using hab
          subst hab'; rw [ha] at hb; cases hb
          simp only [SymExpr.eval]
          simp only [BinOp.eval, UInt64.xor_self, Xv.Select.Proof.truncate_zero, Option.some.injEq] at he
          exact congrArg some he
        · split
          · simp only [SymExpr.eval, Option.some.injEq] at hb; subst hb
            simp only [BinOp.eval, X86.Encode.truncate64, UInt64.xor_zero, Option.some.injEq] at he
            rw [ha, he]
          · rw [SymExpr.eval, Option.bind_eq_bind, ha, hb]; exact he
    | shl =>
        dsimp only; split
        · simp only [SymExpr.eval, Option.some.injEq] at ha; subst ha
          simp only [BinOp.eval, UInt64.zero_shiftLeft, Xv.Select.Proof.truncate_zero, Option.some.injEq] at he
          exact congrArg some he
        · simp only [SymExpr.eval, Option.some.injEq] at hb; subst hb
          split
          · rename_i hcond
            simp only [Bool.and_eq_true, beq_iff_eq] at hcond
            obtain ⟨rfl, hk0⟩ := hcond
            rw [ha]
            simp only [BinOp.eval, X86.Encode.truncate64, hk0, UInt64.shiftLeft_zero, Option.some.injEq] at he
            exact congrArg some he
          · rw [SymExpr.eval]; simp only [Option.bind_eq_bind, ha, SymExpr.eval, Option.bind_some, BinOp.eval, shiftMask_idem]
            exact he
        · rw [SymExpr.eval, Option.bind_eq_bind, ha, hb]; exact he
    | shr =>
        dsimp only; split
        · simp only [SymExpr.eval, Option.some.injEq] at ha; subst ha
          simp only [BinOp.eval, Xv.Select.Proof.truncate_zero, UInt64.zero_shiftRight, Option.some.injEq] at he
          exact congrArg some he
        · simp only [SymExpr.eval, Option.some.injEq] at hb; subst hb
          split
          · rename_i hcond
            simp only [Bool.and_eq_true, beq_iff_eq] at hcond
            obtain ⟨rfl, hk0⟩ := hcond
            rw [ha]
            simp only [BinOp.eval, X86.Encode.truncate64, hk0, UInt64.shiftRight_zero, Option.some.injEq] at he
            exact congrArg some he
          · rw [SymExpr.eval]; simp only [Option.bind_eq_bind, ha, SymExpr.eval, Option.bind_some, BinOp.eval, shiftMask_idem]
            exact he
        · rw [SymExpr.eval, Option.bind_eq_bind, ha, hb]; exact he
    | sar =>
        dsimp only; split
        · simp only [SymExpr.eval, Option.some.injEq] at ha; subst ha
          simp only [BinOp.eval, Option.some.injEq] at he
          simp only [SymExpr.eval]
          rw [← he]; congr 1
          have hsext0 : sext w 0 = 0 := by cases w <;> decide
          have hsar0 : sarWord w 0 (vb &&& shiftMask w) = 0 := by
            simp only [sarWord, hsext0]
            have h0 : ((0 : Word).toInt64 >>> (vb &&& shiftMask w).toInt64).toUInt64 = 0 := by
              apply UInt64.toBitVec_inj.mp
              simp only [Int64.toBitVec_toUInt64, Int64.toBitVec_shiftRight, UInt64.toBitVec_zero]
              apply BitVec.eq_of_getLsbD_eq; intro i hi; simp
            rw [h0, Xv.Select.Proof.truncate_zero]
          exact hsar0.symm
        · simp only [SymExpr.eval, Option.some.injEq] at hb; subst hb
          split
          · rename_i hcond
            simp only [Bool.and_eq_true, beq_iff_eq] at hcond
            obtain ⟨rfl, hk0⟩ := hcond
            rw [ha]
            simp only [BinOp.eval, sarWord, sext, X86.Encode.truncate64, hk0, Option.some.injEq] at he
            have hsr0 : (va.toInt64 >>> (0 : Word).toInt64).toUInt64 = va := by
              apply UInt64.toBitVec_inj.mp; simp
            rw [hsr0] at he; exact congrArg some he
          · rw [SymExpr.eval]; simp only [Option.bind_eq_bind, ha, SymExpr.eval, Option.bind_some, BinOp.eval, shiftMask_idem]
            exact he
        · rw [SymExpr.eval, Option.bind_eq_bind, ha, hb]; exact he
    | rol =>
        dsimp only; split
        · simp only [SymExpr.eval, Option.some.injEq] at ha; subst ha
          simp only [BinOp.eval, rolWord_zero_val, Option.some.injEq] at he
          exact congrArg some he
        · simp only [SymExpr.eval, Option.some.injEq] at hb; subst hb
          split
          · rename_i hcond
            simp only [Bool.and_eq_true, beq_iff_eq] at hcond
            obtain ⟨rfl, hk0⟩ := hcond
            rw [ha]
            simp only [BinOp.eval, hk0, rolWord_zero_count, X86.Encode.truncate64, Option.some.injEq] at he
            exact congrArg some he
          · rw [SymExpr.eval]; simp only [Option.bind_eq_bind, ha, SymExpr.eval, Option.bind_some, BinOp.eval, shiftMask_idem]
            exact he
        · rw [SymExpr.eval, Option.bind_eq_bind, ha, hb]; exact he
    | ror =>
        dsimp only; split
        · simp only [SymExpr.eval, Option.some.injEq] at ha; subst ha
          simp only [BinOp.eval, rorWord_zero_val, Option.some.injEq] at he
          exact congrArg some he
        · simp only [SymExpr.eval, Option.some.injEq] at hb; subst hb
          split
          · rename_i hcond
            simp only [Bool.and_eq_true, beq_iff_eq] at hcond
            obtain ⟨rfl, hk0⟩ := hcond
            rw [ha]
            simp only [BinOp.eval, hk0, rorWord_zero_count, X86.Encode.truncate64, Option.some.injEq] at he
            exact congrArg some he
          · rw [SymExpr.eval]; simp only [Option.bind_eq_bind, ha, SymExpr.eval, Option.bind_some, BinOp.eval, shiftMask_idem]
            exact he
        · rw [SymExpr.eval, Option.bind_eq_bind, ha, hb]; exact he
    | udiv =>
        dsimp only
        cases b with
        | imm k =>
            simp only [SymExpr.eval, Option.some.injEq] at hb; subst hb
            by_cases hd1 : (w.truncate k == 1) = true
            · have hd1' : w.truncate k = 1 := by simpa using hd1
              simp only [hd1, ↓reduceIte]
              simp only [BinOp.eval, hd1'] at he
              have hne : ((1 : Word) == 0) = false := by decide
              simp only [hne, Bool.false_eq_true, ↓reduceIte, UInt64.div_one, Option.some.injEq] at he
              by_cases hw : w = .w64
              · subst hw
                simp only [beq_self_eq_true, ↓reduceIte, ha]
                rw [X86.Encode.truncate64] at he; exact congrArg some he
              · have hwf : (w == .w64) = false := beq_false_of_ne hw
                simp only [hwf, Bool.false_eq_true, ↓reduceIte]
                rw [SymExpr.eval]; simp only [Option.bind_eq_bind, ha, SymExpr.eval, Option.bind_some,
                  BinOp.eval, Option.some.injEq]
                rw [← he]; exact X86.Encode.truncate_truncate w va
            · simp only [hd1, Bool.false_eq_true, ↓reduceIte]
              cases hfp : findPow2 w k with
              | none => rw [SymExpr.eval]; simp only [Option.bind_eq_bind, ha, SymExpr.eval, Option.bind_some]; exact he
              | some sh =>
                  rw [SymExpr.eval]; simp only [Option.bind_eq_bind, ha, SymExpr.eval, Option.bind_some]
                  rw [← isPow2_udiv (findPow2_sound hfp) va, he]
        | _ => rw [SymExpr.eval, Option.bind_eq_bind, ha, hb]; exact he
    | urem =>
        dsimp only
        cases b with
        | imm k =>
            simp only [SymExpr.eval, Option.some.injEq] at hb; subst hb
            by_cases hd1 : (w.truncate k == 1) = true
            · have hd1' : w.truncate k = 1 := by simpa using hd1
              simp only [hd1, ↓reduceIte, SymExpr.eval]
              simp only [BinOp.eval, hd1'] at he
              have hne : ((1 : Word) == 0) = false := by decide
              simp only [hne, Bool.false_eq_true, ↓reduceIte, UInt64.mod_one, Option.some.injEq] at he
              exact congrArg some he
            · simp only [hd1, Bool.false_eq_true, ↓reduceIte]
              cases hfp : findPow2 w k with
              | none => rw [SymExpr.eval]; simp only [Option.bind_eq_bind, ha, SymExpr.eval, Option.bind_some]; exact he
              | some sh =>
                  rw [SymExpr.eval]; simp only [Option.bind_eq_bind, ha, SymExpr.eval, Option.bind_some]
                  rw [← isPow2_urem (findPow2_sound hfp) va, he]
        | _ => rw [SymExpr.eval, Option.bind_eq_bind, ha, hb]; exact he

theorem mkBin_sound {ρ : Env} {ctx : Word} {snaps : MemSnaps} {o : BinOp} {w : Width}
    {a b : SymExpr} {va vb v : Word}
    (ha : a.eval ρ ctx snaps = some va) (hb : b.eval ρ ctx snaps = some vb)
    (he : o.eval w va vb = some v) :
    (mkBin o w a b).eval ρ ctx snaps = some v := by
  unfold mkBin
  split
  · rename_i hsw
    simp only [Bool.and_eq_true] at hsw
    exact mkBinOrdered_sound hb ha (by rw [binOpIsComm_eval hsw.1]; exact he)
  · exact mkBinOrdered_sound ha hb he

theorem condStatic_sound {ρ : Env} {ctx : Word} {snaps : MemSnaps} {c : Cond} {w : Width}
    {a b : SymExpr} {va vb : Word} {r : Bool}
    (hs : condStatic c w a b = some r)
    (ha : a.eval ρ ctx snaps = some va) (hb : b.eval ρ ctx snaps = some vb) :
    c.holds w va vb = r := by
  unfold condStatic at hs
  split at hs
  · simp only [SymExpr.eval, Option.some.injEq] at ha hb hs
    subst ha hb hs; rfl
  · split at hs
    · rename_i hab
      have hab' : a = b := by simpa using hab
      subst hab'; rw [ha] at hb; cases hb
      exact condReflVal_sound hs w va
    · cases hs

/-- Normalization preserves evaluation whenever the input expression succeeds. -/
theorem SymExpr.norm_sound {ρ : Env} {ctx : Word} {snaps : MemSnaps} :
    ∀ {e : SymExpr} {v : Word}, e.eval ρ ctx snaps = some v → e.norm.eval ρ ctx snaps = some v
  | .reg _, _, h => h
  | .imm _, _, h => h
  | .ctx, _, h => h
  | .bin o w a b, v, h => by
      simp only [SymExpr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨va, ha, vb, hb, he⟩ := h
      exact mkBin_sound (norm_sound ha) (norm_sound hb) he
  | .select c w a b t f, v, h => by
      simp only [SymExpr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨va, ha, vb, hb, vt, ht, vf, hf, rfl⟩ := h
      have ha' := norm_sound ha; have hb' := norm_sound hb
      have ht' := norm_sound ht; have hf' := norm_sound hf
      simp only [SymExpr.norm]
      have hcond : ∀ (c1 : Cond) (a1 b1 : SymExpr) (va1 vb1 : Word),
          a1.eval ρ ctx snaps = some va1 → b1.eval ρ ctx snaps = some vb1 →
          c1.holds w va1 vb1 = c.holds w va vb →
          (if t.norm == f.norm then t.norm
           else match condStatic c1 w a1 b1 with
           | some true => t.norm
           | some false => f.norm
           | none => .select c1 w a1 b1 t.norm f.norm).eval ρ ctx snaps =
          some (if c.holds w va vb then vt else vf) := by
        intro c1 a1 b1 va1 vb1 ha1 hb1 hce
        by_cases htf : (t.norm == f.norm) = true
        · have htf' : t.norm = f.norm := by simpa using htf
          rw [htf'] at ht'; rw [ht'] at hf'; cases hf'
          simp only [htf', beq_self_eq_true, ↓reduceIte, ite_self, ht']
        · simp only [htf, Bool.false_eq_true, ↓reduceIte]
          cases hst : condStatic c1 w a1 b1 with
          | none =>
              rw [SymExpr.eval]; simp only [Option.bind_eq_bind, ha1, hb1, ht', hf', Option.bind_some, hce]
          | some r =>
              have hr := condStatic_sound hst ha1 hb1
              rw [hce] at hr
              cases r <;> simp [hr, ht', hf']
      by_cases hcmp : (b.norm.cmp a.norm == .lt) = true
      · simp only [hcmp, ↓reduceIte]
        exact hcond (condSwap c) b.norm a.norm vb va hb' ha' (condSwap_holds c w va vb)
      · simp only [hcmp]
        exact hcond c a.norm b.norm va vb ha' hb' rfl
  | .test c w a b, v, h => by
      simp only [SymExpr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨va, ha, vb, hb, rfl⟩ := h
      have ha' := norm_sound ha; have hb' := norm_sound hb
      simp only [SymExpr.norm]
      have hcond : ∀ (c1 : Cond) (a1 b1 : SymExpr) (va1 vb1 : Word),
          a1.eval ρ ctx snaps = some va1 → b1.eval ρ ctx snaps = some vb1 →
          c1.holds w va1 vb1 = c.holds w va vb →
          (match condStatic c1 w a1 b1 with
           | some true => SymExpr.imm 1
           | some false => SymExpr.imm 0
           | none => .test c1 w a1 b1).eval ρ ctx snaps =
          some (if c.holds w va vb then 1 else 0) := by
        intro c1 a1 b1 va1 vb1 ha1 hb1 hce
        cases hst : condStatic c1 w a1 b1 with
        | none => rw [SymExpr.eval]; simp only [Option.bind_eq_bind, ha1, hb1, Option.bind_some, hce]
        | some r =>
            have hr := condStatic_sound hst ha1 hb1
            rw [hce] at hr
            cases r <;> simp [hr, SymExpr.eval]
      by_cases hcmp : (b.norm.cmp a.norm == .lt) = true
      · simp only [hcmp, ↓reduceIte]
        exact hcond (condSwap c) b.norm a.norm vb va hb' ha' (condSwap_holds c w va vb)
      · simp only [hcmp]
        exact hcond c a.norm b.norm va vb ha' hb' rfl
  | .bsr64 a, v, h => by
      simp only [SymExpr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨va, ha, hres⟩ := h
      have ha' := norm_sound ha
      simp only [SymExpr.norm]
      cases hna : a.norm with
      | imm k =>
          rw [hna] at ha'; simp only [SymExpr.eval, Option.some.injEq] at ha'; subst k
          split at hres
          · cases hres
          · rename_i hnz
            have hnz' : (va == 0) = false := Bool.eq_false_iff.mpr hnz
            simp only [hnz', Bool.false_eq_true, ↓reduceIte, SymExpr.eval]
            exact hres
      | _ =>
          rw [hna] at ha'
          rw [SymExpr.eval]; simp only [Option.bind_eq_bind, ha', Option.bind_some]
          exact hres
  | .mulHi a b, v, h => by
      simp only [SymExpr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨va, ha, vb, hb, rfl⟩ := h
      have ha' := norm_sound ha; have hb' := norm_sound hb
      simp only [SymExpr.norm]
      have hmain : ∀ (a1 b1 : SymExpr) (va1 vb1 : Word),
          a1.eval ρ ctx snaps = some va1 → b1.eval ρ ctx snaps = some vb1 →
          va1.toNat * vb1.toNat = va.toNat * vb.toNat →
          (match a1, b1 with
           | .imm xa, .imm xb => SymExpr.imm (UInt64.ofNat ((xa.toNat * xb.toNat) / 2 ^ 64))
           | _, .imm 0 => .imm 0
           | _, .imm 1 => .imm 0
           | _, _ => .mulHi a1 b1).eval ρ ctx snaps =
          some (UInt64.ofNat ((va.toNat * vb.toNat) / 2 ^ 64)) := by
        intro a1 b1 va1 vb1 ha1 hb1 hmul
        split
        · simp only [SymExpr.eval, Option.some.injEq] at ha1 hb1 ⊢; subst ha1 hb1; rw [hmul]
        · simp only [SymExpr.eval, Option.some.injEq] at hb1 ⊢; subst hb1
          rw [← hmul]; simp
        · simp only [SymExpr.eval, Option.some.injEq] at hb1 ⊢; subst hb1
          rw [← hmul, show (1 : Word).toNat = 1 from rfl, Nat.mul_one,
            Nat.div_eq_of_lt va1.toNat_lt_size]; rfl
        · rw [SymExpr.eval]; simp only [Option.bind_eq_bind, ha1, hb1, Option.bind_some, hmul]
      by_cases hcmp : (b.norm.cmp a.norm == .lt) = true
      · simp only [hcmp, ↓reduceIte]
        exact hmain b.norm a.norm vb va hb' ha' (Nat.mul_comm _ _)
      · simp only [hcmp]
        exact hmain a.norm b.norm va vb ha' hb' rfl
  | .divQ hi lo d, v, h => by
      simp only [SymExpr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨vhi, hhi, vlo, hlo, vd, hd, hres⟩ := h
      have hhi' := norm_sound hhi; have hlo' := norm_sound hlo; have hd' := norm_sound hd
      simp only [SymExpr.norm]
      split
      · rename_i _ _ _ vhi' vlo' vd' heq1 heq2 heq3
        rw [heq1] at hhi'; rw [heq2] at hlo'; rw [heq3] at hd'
        simp only [SymExpr.eval, Option.some.injEq] at hhi' hlo' hd'
        subst vhi' vlo' vd'
        split at hres
        · cases hres
        · rename_i hok
          have hok' : (vd.toNat == 0 || decide (vd.toNat ≤ vhi.toNat)) = false := Bool.eq_false_iff.mpr hok
          simp only [hok', Bool.false_eq_true, ↓reduceIte, SymExpr.eval]; exact hres
      · rw [SymExpr.eval]; simp only [Option.bind_eq_bind, hhi', hlo', hd', Option.bind_some]; exact hres
  | .divR hi lo d, v, h => by
      simp only [SymExpr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨vhi, hhi, vlo, hlo, vd, hd, hres⟩ := h
      have hhi' := norm_sound hhi; have hlo' := norm_sound hlo; have hd' := norm_sound hd
      simp only [SymExpr.norm]
      split
      · rename_i _ _ _ vhi' vlo' vd' heq1 heq2 heq3
        rw [heq1] at hhi'; rw [heq2] at hlo'; rw [heq3] at hd'
        simp only [SymExpr.eval, Option.some.injEq] at hhi' hlo' hd'
        subst vhi' vlo' vd'
        split at hres
        · cases hres
        · rename_i hok
          have hok' : (vd.toNat == 0 || decide (vd.toNat ≤ vhi.toNat)) = false := Bool.eq_false_iff.mpr hok
          simp only [hok', Bool.false_eq_true, ↓reduceIte, SymExpr.eval]; exact hres
      · rw [SymExpr.eval]; simp only [Option.bind_eq_bind, hhi', hlo', hd', Option.bind_some]; exact hres
  | .addCLo a b c, v, h => by
      simp only [SymExpr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨va, ha, vb, hb, vc, hc, rfl⟩ := h
      have ha' := norm_sound ha; have hb' := norm_sound hb; have hc' := norm_sound hc
      simp only [SymExpr.norm]
      split
      · rename_i _ _ _ va' vb' vc' heq1 heq2 heq3
        rw [heq1] at ha'; rw [heq2] at hb'; rw [heq3] at hc'
        simp only [SymExpr.eval, Option.some.injEq] at ha' hb' hc' ⊢; subst ha' hb' hc'; rfl
      · rw [SymExpr.eval]; simp only [Option.bind_eq_bind, ha', hb', hc', Option.bind_some]
  | .addCHi a b c, v, h => by
      simp only [SymExpr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨va, ha, vb, hb, vc, hc, rfl⟩ := h
      have ha' := norm_sound ha; have hb' := norm_sound hb; have hc' := norm_sound hc
      simp only [SymExpr.norm]
      split
      · rename_i _ _ _ va' vb' vc' heq1 heq2 heq3
        rw [heq1] at ha'; rw [heq2] at hb'; rw [heq3] at hc'
        simp only [SymExpr.eval, Option.some.injEq] at ha' hb' hc' ⊢; subst ha' hb' hc'; rfl
      · rw [SymExpr.eval]; simp only [Option.bind_eq_bind, ha', hb', hc', Option.bind_some]
  | .subBLo a b c, v, h => by
      simp only [SymExpr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨va, ha, vb, hb, vc, hc, rfl⟩ := h
      have ha' := norm_sound ha; have hb' := norm_sound hb; have hc' := norm_sound hc
      simp only [SymExpr.norm]
      split
      · rename_i _ _ _ va' vb' vc' heq1 heq2 heq3
        rw [heq1] at ha'; rw [heq2] at hb'; rw [heq3] at hc'
        simp only [SymExpr.eval, Option.some.injEq] at ha' hb' hc' ⊢; subst ha' hb' hc'; rfl
      · rw [SymExpr.eval]; simp only [Option.bind_eq_bind, ha', hb', hc', Option.bind_some]
  | .subBHi a b c, v, h => by
      simp only [SymExpr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨va, ha, vb, hb, vc, hc, rfl⟩ := h
      have ha' := norm_sound ha; have hb' := norm_sound hb; have hc' := norm_sound hc
      simp only [SymExpr.norm]
      split
      · rename_i _ _ _ va' vb' vc' heq1 heq2 heq3
        rw [heq1] at ha'; rw [heq2] at hb'; rw [heq3] at hc'
        simp only [SymExpr.eval, Option.some.injEq] at ha' hb' hc' ⊢; subst ha' hb' hc'; rfl
      · rw [SymExpr.eval]; simp only [Option.bind_eq_bind, ha', hb', hc', Option.bind_some]
  | .load snap w e addr, v, h => by
      simp only [SymExpr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨va, ha, hld⟩ := h
      simp only [SymExpr.norm, SymExpr.eval, Option.bind_eq_bind, norm_sound ha, Option.bind_some, hld]

/-! ## `exprEquiv` soundness -/

private theorem matchMulHiConst_sound {ρ : Env} {ctx : Word} {snaps : MemSnaps}
    {a e : SymExpr} {m va v : Word}
    (hm : matchMulHiConst a e = some m)
    (ha : a.eval ρ ctx snaps = some va)
    (he : e.eval ρ ctx snaps = some v) :
    v = UInt64.ofNat ((va.toNat * m.toNat) / 2 ^ 64) := by
  unfold matchMulHiConst at hm
  split at hm
  · rename_i x m'
    by_cases hxa : (x == a) = true
    · have hxa' : x = a := by simpa using hxa
      subst hxa'; simp only [hxa, ↓reduceIte, Option.some.injEq] at hm; subst hm
      rw [SymExpr.eval] at he; simp only [Option.bind_eq_bind, ha, SymExpr.eval, Option.bind_some, Option.some.injEq] at he
      exact he.symm
    · simp [hxa] at hm
  · rename_i m' x _
    by_cases hxa : (x == a) = true
    · have hxa' : x = a := by simpa using hxa
      subst hxa'; simp only [hxa, ↓reduceIte, Option.some.injEq] at hm; subst hm
      rw [SymExpr.eval] at he; simp only [Option.bind_eq_bind, ha, SymExpr.eval, Option.bind_some, Option.some.injEq] at he
      rw [Nat.mul_comm] at he; exact he.symm
    · simp [hxa] at hm
  · cases hm

private theorem matchAddShiftCore_sound {ρ : Env} {ctx : Word} {snaps : MemSnaps}
    {a core : SymExpr} {m' va v : Word}
    (hm : matchAddShiftCore a core = some m')
    (ha : a.eval ρ ctx snaps = some va)
    (hc : core.eval ρ ctx snaps = some v) :
    let hi : Word := UInt64.ofNat ((va.toNat * m'.toNat) / 2 ^ 64)
    v = ((va - hi) >>> (1 &&& 63)) + hi := by
  have hcheck : ∀ (t hi : SymExpr) (vt vhi : Word),
      t.eval ρ ctx snaps = some vt → hi.eval ρ ctx snaps = some vhi →
      (match matchMulHiConst a hi with
       | none => none
       | some m'' =>
           match t with
           | .bin .shr .w64 (.bin .sub .w64 a1 hi1) (.imm 1) =>
               if a1 == a && hi1 == hi then some m'' else none
           | _ => none) = some m' →
      vhi = UInt64.ofNat ((va.toNat * m'.toNat) / 2 ^ 64) ∧ vt = (va - vhi) >>> (1 &&& 63) := by
    intro t hi vt vhi ht hhi hck
    cases hmh : matchMulHiConst a hi with
    | none => rw [hmh] at hck; cases hck
    | some m'' =>
        rw [hmh] at hck
        dsimp only at hck
        split at hck
        · rename_i a1 hi1
          by_cases hboth : (a1 == a && hi1 == hi) = true
          · simp only [hboth, ↓reduceIte, Option.some.injEq] at hck; subst hck
            simp only [Bool.and_eq_true, beq_iff_eq] at hboth
            obtain ⟨ha1, hhi1⟩ := hboth
            have hvhi := matchMulHiConst_sound hmh ha hhi
            rw [ha1, hhi1] at ht
            rw [SymExpr.eval] at ht
            simp only [Option.bind_eq_bind, SymExpr.eval, BinOp.eval, X86.Encode.truncate64, shiftMask,
              ha, hhi, Option.bind_some, Option.some.injEq] at ht
            exact ⟨hvhi, ht.symm⟩
          · simp [hboth] at hck
        · cases hck
  unfold matchAddShiftCore at hm
  split at hm
  · rename_i lhs rhs
    rw [SymExpr.eval] at hc
    simp only [BinOp.eval, X86.Encode.truncate64, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at hc
    obtain ⟨vl, hl, vr, hr, rfl⟩ := hc
    dsimp only at hm
    split at hm
    · rename_i m1 hm1; cases hm
      obtain ⟨hvr, hvl⟩ := hcheck lhs rhs vl vr hl hr hm1
      rw [hvl, hvr]
    · obtain ⟨hvl, hvr⟩ := hcheck rhs lhs vr vl hr hl hm
      rw [hvr, hvl, UInt64.add_comm]
  · cases hm

theorem checkDivMagicExpr_sound {ρ : Env} {ctx : Word} {snaps : MemSnaps}
    {w : Width} {a e2 : SymExpr} {d va v2 : Word}
    (hck : checkDivMagicExpr w a d e2 = true)
    (ha : a.eval ρ ctx snaps = some va)
    (he2 : e2.eval ρ ctx snaps = some v2)
    (hd : w.truncate d ≠ 0) :
    v2 = w.truncate va / w.truncate d := by
  unfold checkDivMagicExpr at hck
  by_cases heq : (e2 == mkBin .udiv w a (.imm d)) = true
  · have heq' : e2 = mkBin .udiv w a (.imm d) := by simpa using heq
    subst heq'
    have hdiv : BinOp.eval .udiv w va d = some (w.truncate va / w.truncate d) := by
      simp [BinOp.eval, beq_false_of_ne hd]
    have hm := mkBin_sound ha (b := .imm d) (vb := d) rfl hdiv
    rw [hm] at he2; cases he2; rfl
  · simp only [heq, Bool.false_eq_true, ↓reduceIte] at hck
    cases w with
    | w8 | w16 => cases hck
    | w64 =>
        simp only [X86.Encode.truncate64] at hd ⊢
        dsimp only at hck
        split at hck
        · rename_i hi sh
          have hadd : (match matchAddShiftCore a hi with
              | some m' => checkMagicAddShift d m' (sh.toNat + 1)
              | none => false) = true → v2 = va / d := by
            intro hck'
            cases hmc : matchAddShiftCore a hi with
            | none => rw [hmc] at hck'; cases hck'
            | some m' =>
                rw [hmc] at hck'
                rw [SymExpr.eval] at he2
                simp only [BinOp.eval, X86.Encode.truncate64, shiftMask, Option.bind_eq_bind,
                  Option.bind_eq_some_iff, Option.some.injEq] at he2
                obtain ⟨vc, hc, vsh, hvsh, rfl⟩ := he2
                simp only [SymExpr.eval, Option.some.injEq] at hvsh; subst hvsh
                have hvc := matchAddShiftCore_sound hmc ha hc
                rw [hvc]
                have hsound := checkMagicAddShift_sound hck' va
                dsimp only at hsound
                simp only [Nat.add_sub_cancel, UInt64.ofNat_toNat] at hsound
                exact hsound
          cases hmh : matchMulHiConst a hi with
          | none =>
              rw [hmh] at hck; simp only [Bool.false_eq_true, ↓reduceIte] at hck
              exact hadd hck
          | some m =>
              rw [hmh] at hck; dsimp only at hck
              split at hck
              · rename_i hcms
                rw [SymExpr.eval] at he2
                simp only [BinOp.eval, X86.Encode.truncate64, shiftMask, Option.bind_eq_bind,
                  Option.bind_eq_some_iff, Option.some.injEq] at he2
                obtain ⟨vhi, hhi, vsh, hvsh, rfl⟩ := he2
                simp only [SymExpr.eval, Option.some.injEq] at hvsh; subst hvsh
                have hvhi := matchMulHiConst_sound hmh ha hhi
                rw [hvhi]
                have hsound := checkMagicSimple_sound hcms va
                rw [UInt64.ofNat_toNat] at hsound
                exact hsound
              · exact hadd hck
        · have hadd : (match matchAddShiftCore a e2 with
              | some m' => checkMagicAddShift d m' 1
              | none => false) = true → v2 = va / d := by
            intro hck'
            cases hmc : matchAddShiftCore a e2 with
            | none => rw [hmc] at hck'; cases hck'
            | some m' =>
                rw [hmc] at hck'
                have hvc := matchAddShiftCore_sound hmc ha he2
                have hsound := checkMagicAddShift_sound hck' va
                have h0 : ((UInt64.ofNat (1 - 1) : Word) &&& 63) = 0 := by decide
                dsimp only at hsound
                rw [h0, UInt64.shiftRight_zero] at hsound
                rw [hvc, hsound]
          cases hmh : matchMulHiConst a e2 with
          | none =>
              rw [hmh] at hck; simp only [Bool.false_eq_true, ↓reduceIte] at hck
              exact hadd hck
          | some m =>
              rw [hmh] at hck; dsimp only at hck
              split at hck
              · rename_i hcms
                have hvhi := matchMulHiConst_sound hmh ha he2
                have hsound := checkMagicSimple_sound hcms va
                have h0 : ((UInt64.ofNat 0 : Word) &&& 63) = 0 := by decide
                rw [h0, UInt64.shiftRight_zero] at hsound
                rw [hvhi, hsound]
              · exact hadd hck
    | w32 =>
        dsimp only at hck
        rw [Bool.or_eq_true] at hck
        have ha32 : (mkBin .and .w64 a (.imm 0xffffffff)).eval ρ ctx snaps = some (va &&& 0xffffffff) :=
          mkBin_sound ha (b := .imm 0xffffffff) (vb := 0xffffffff) rfl (by simp [BinOp.eval, X86.Encode.truncate64])
        rcases hck with h1 | h2
        · unfold matchMagic32Simple at h1
          dsimp only at h1
          cases e2 with
          | bin o w' x y =>
              cases o <;> cases w' <;> try (simp at h1; done)
              cases x with
              | bin o2 w2 u1 u2 =>
                  cases o2 <;> cases w2 <;> try (simp at h1; done)
                  cases y with
                  | imm sh =>
                      cases u2 with
                      | imm m =>
                          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h1
                          obtain ⟨⟨rfl, h32⟩, hcm⟩ := h1
                          simp only [SymExpr.eval, BinOp.eval, X86.Encode.truncate64, shiftMask,
                            Option.bind_eq_bind, ha32, Option.bind_some, Option.some.injEq] at he2
                          subst he2
                          have hsound := checkMagic32_sound hcm va
                          have hsh : UInt64.ofNat (32 + (sh.toNat - 32)) = sh := by
                            rw [Nat.add_sub_of_le h32, UInt64.ofNat_toNat]
                          rw [hsh] at hsound; exact hsound
                      | _ =>
                          cases u1 with
                          | imm m =>
                              simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h1
                              obtain ⟨⟨hu2, h32⟩, hcm⟩ := h1
                              rw [hu2] at he2
                              simp only [SymExpr.eval, BinOp.eval, X86.Encode.truncate64, shiftMask,
                                Option.bind_eq_bind, ha32, Option.bind_some, Option.some.injEq] at he2
                              subst he2
                              rw [UInt64.mul_comm]
                              have hsound := checkMagic32_sound hcm va
                              have hsh : UInt64.ofNat (32 + (sh.toNat - 32)) = sh := by
                                rw [Nat.add_sub_of_le h32, UInt64.ofNat_toNat]
                              rw [hsh] at hsound; exact hsound
                          | _ => simp at h1
                  | _ => simp at h1
              | _ => simp at h1
          | _ => simp at h1
        · unfold matchMagic32AddShift at h2
          dsimp only at h2
          let uExpr := mkBin .and .w64 a (.imm 0xffffffff)
          have hhi_sound : ∀ (hi : SymExpr) (vhi m' : Word),
              hi.eval ρ ctx snaps = some vhi →
              (match hi with
               | .bin .shr .w64 (.bin .mul .w64 u' (.imm m')) (.imm 32) => if u' == uExpr then some m' else none
               | .bin .shr .w64 (.bin .mul .w64 (.imm m') u') (.imm 32) => if u' == uExpr then some m' else none
               | _ => none) = some m' →
              vhi = ((va &&& 0xffffffff) * m') >>> (32 &&& 63) := by
            intro hi vhi m' hhi hmh
            split at hmh
            · rename_i u' m1
              split at hmh
              · rename_i hu
                have hu' : u' = uExpr := by simpa using hu
                subst hu'; cases hmh
                simp only [uExpr, SymExpr.eval, BinOp.eval, X86.Encode.truncate64, shiftMask,
                  Option.bind_eq_bind, ha32, Option.bind_some, Option.some.injEq] at hhi
                exact hhi.symm
              · cases hmh
            · rename_i m1 u' _
              split at hmh
              · rename_i hu
                have hu' : u' = uExpr := by simpa using hu
                subst hu'; cases hmh
                simp only [uExpr, SymExpr.eval, BinOp.eval, X86.Encode.truncate64, shiftMask,
                  Option.bind_eq_bind, ha32, Option.bind_some, Option.some.injEq] at hhi
                rw [UInt64.mul_comm] at hhi; exact hhi.symm
              · cases hmh
            · cases hmh
          have hcore_sound : ∀ (core : SymExpr) (vc m' : Word),
              core.eval ρ ctx snaps = some vc →
              (match core with
               | .bin .add .w64 lhs rhs =>
                   let ck (t hi : SymExpr) : Option Word :=
                     match match hi with
                       | .bin .shr .w64 (.bin .mul .w64 u' (.imm m')) (.imm 32) => if u' == uExpr then some m' else none
                       | .bin .shr .w64 (.bin .mul .w64 (.imm m') u') (.imm 32) => if u' == uExpr then some m' else none
                       | _ => none with
                     | none => none
                     | some m' =>
                         match t with
                         | .bin .shr .w64 (.bin .sub .w64 u1 hi1) (.imm 1) =>
                             if u1 == uExpr && hi1 == hi then some m' else none
                         | _ => none
                   match ck lhs rhs with | some m' => some m' | none => ck rhs lhs
               | _ => none) = some m' →
              let u : Word := va &&& 0xffffffff
              let hi : Word := (u * m') >>> (32 &&& 63)
              vc = ((u - hi) >>> (1 &&& 63)) + hi := by
            intro core vc m' hvc hmc
            have hpair : ∀ (t hi : SymExpr) (vt vhi : Word),
                t.eval ρ ctx snaps = some vt → hi.eval ρ ctx snaps = some vhi →
                (match match hi with
                  | .bin .shr .w64 (.bin .mul .w64 u' (.imm m')) (.imm 32) => if u' == uExpr then some m' else none
                  | .bin .shr .w64 (.bin .mul .w64 (.imm m') u') (.imm 32) => if u' == uExpr then some m' else none
                  | _ => none with
                | none => none
                | some m' =>
                    match t with
                    | .bin .shr .w64 (.bin .sub .w64 u1 hi1) (.imm 1) =>
                        if u1 == uExpr && hi1 == hi then some m' else none
                    | _ => none) = some m' →
                vhi = ((va &&& 0xffffffff) * m') >>> (32 &&& 63) ∧
                  vt = ((va &&& 0xffffffff) - vhi) >>> (1 &&& 63) := by
              intro t hi vt vhi ht hhi hck
              cases hmh : (match hi with
                | .bin .shr .w64 (.bin .mul .w64 u' (.imm m')) (.imm 32) => if u' == uExpr then some m' else none
                | .bin .shr .w64 (.bin .mul .w64 (.imm m') u') (.imm 32) => if u' == uExpr then some m' else none
                | _ => none) with
              | none => rw [hmh] at hck; cases hck
              | some m'' =>
                  rw [hmh] at hck
                  cases t with
                  | bin o w' x y =>
                      cases o <;> cases w' <;> try (simp at hck; done)
                      cases x with
                      | bin o2 w2 u1 hi1 =>
                          cases o2 <;> cases w2 <;> try (simp at hck; done)
                          cases y with
                          | imm k =>
                              by_cases hk1 : k = 1
                              · subst hk1
                                by_cases hb : (u1 == uExpr && hi1 == hi) = true
                                · simp only [hb, ↓reduceIte, Option.some.injEq] at hck; subst hck
                                  simp only [Bool.and_eq_true, beq_iff_eq] at hb
                                  obtain ⟨hu1, hhi1⟩ := hb
                                  have hvhi := hhi_sound hi vhi m'' hhi hmh
                                  rw [hu1, hhi1] at ht
                                  rw [SymExpr.eval] at ht
                                  simp only [uExpr, SymExpr.eval, BinOp.eval, X86.Encode.truncate64, shiftMask,
                                    Option.bind_eq_bind, ha32, hhi, Option.bind_some, Option.some.injEq] at ht
                                  exact ⟨hvhi, ht.symm⟩
                                · simp [hb] at hck
                              · simp [hk1] at hck
                          | _ => simp at hck
                      | _ => simp at hck
                  | _ => simp at hck
            cases core with
            | bin o w' lhs rhs =>
                cases o <;> cases w' <;> try (simp at hmc; done)
                rw [SymExpr.eval] at hvc
                simp only [BinOp.eval, X86.Encode.truncate64, Option.bind_eq_bind,
                  Option.bind_eq_some_iff, Option.some.injEq] at hvc
                obtain ⟨vl, hl, vr, hr, rfl⟩ := hvc
                dsimp only at hmc
                split at hmc
                · rename_i m1 hm1; cases hmc
                  obtain ⟨hvr, hvl⟩ := hpair lhs rhs vl vr hl hr hm1
                  rw [hvl, hvr]
                · obtain ⟨hvl, hvr⟩ := hpair rhs lhs vr vl hr hl hmc
                  rw [hvr, hvl, UInt64.add_comm]
            | _ => simp at hmc
          split at h2
          · rename_i core sh
            split at h2
            · rename_i m' hmc
              rw [SymExpr.eval] at he2
              simp only [BinOp.eval, X86.Encode.truncate64, shiftMask,
                Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at he2
              obtain ⟨vc, hvc, vsh, hvsh, rfl⟩ := he2
              simp only [SymExpr.eval, Option.some.injEq] at hvsh; subst hvsh
              rw [hcore_sound core vc m' hvc hmc]
              have hsound := checkMagic32AddShift_sound h2 va
              dsimp only at hsound
              simp only [Nat.add_sub_cancel, UInt64.ofNat_toNat] at hsound
              exact hsound
            · cases h2
          · rename_i _
            split at h2
            · rename_i m' hmc
              rw [hcore_sound e2 v2 m' he2 hmc]
              have hsound := checkMagic32AddShift_sound h2 va
              dsimp only at hsound
              have h0 : ((UInt64.ofNat (1 - 1) : Word) &&& 63) = 0 := by decide
              rw [h0, UInt64.shiftRight_zero] at hsound
              exact hsound
            · cases h2

theorem checkRemMagicExpr_sound {ρ : Env} {ctx : Word} {snaps : MemSnaps}
    {w : Width} {a e2 : SymExpr} {d va v2 : Word}
    (hck : checkRemMagicExpr w a d e2 = true)
    (ha : a.eval ρ ctx snaps = some va)
    (he2 : e2.eval ρ ctx snaps = some v2) :
    w.truncate d ≠ 0 ∧ v2 = w.truncate va % w.truncate d := by
  unfold checkRemMagicExpr at hck
  dsimp only at hck
  by_cases hd0 : (w.truncate d == 0) = true
  · simp [hd0] at hck
  · have hd : w.truncate d ≠ 0 := by simpa using hd0
    simp only [hd0, Bool.false_eq_true, ↓reduceIte] at hck
    refine ⟨hd, ?_⟩
    cases e2 with
    | bin o w' a' prod =>
        cases o <;> try (simp at hck; done)
        dsimp only at hck
        by_cases hwa : (w' == w && a' == a) = true
        · simp only [hwa, ↓reduceIte] at hck
          simp only [Bool.and_eq_true, beq_iff_eq] at hwa
          obtain ⟨hw', ha'⟩ := hwa
          subst w'; subst a'
          rw [SymExpr.eval] at he2
          simp only [BinOp.eval, Option.bind_eq_bind, ha, Option.bind_some,
            Option.bind_eq_some_iff, Option.some.injEq] at he2
          obtain ⟨vprod, hprod, rfl⟩ := he2
          have hvprod : vprod = w.truncate ((w.truncate va / w.truncate d) * d) := by
            cases prod with
            | bin op wp p1 p2 =>
                cases op with
                | mul =>
                    cases p2 with
                    | imm d' =>
                        dsimp only at hck
                        by_cases hwd : (wp == w && w.truncate d' == w.truncate d) = true
                        · simp only [hwd, ↓reduceIte] at hck
                          simp only [Bool.and_eq_true, beq_iff_eq] at hwd
                          obtain ⟨rfl, hd'⟩ := hwd
                          rw [SymExpr.eval] at hprod
                          simp only [BinOp.eval, Option.bind_eq_bind, Option.bind_eq_some_iff,
                            Option.some.injEq] at hprod
                          obtain ⟨vq, hq, vd', hvd', rfl⟩ := hprod
                          simp only [SymExpr.eval, Option.some.injEq] at hvd'; subst hvd'
                          have hvq := checkDivMagicExpr_sound hck ha hq hd
                          rw [hvq, X86.Encode.truncate_mul, hd', ← X86.Encode.truncate_mul]
                        · simp [hwd] at hck
                    | _ =>
                        cases p1 with
                        | imm d' =>
                            dsimp only at hck
                            by_cases hwd : (wp == w && w.truncate d' == w.truncate d) = true
                            · simp only [hwd, ↓reduceIte] at hck
                              simp only [Bool.and_eq_true, beq_iff_eq] at hwd
                              obtain ⟨rfl, hd'⟩ := hwd
                              rw [SymExpr.eval] at hprod
                              simp only [BinOp.eval, Option.bind_eq_bind, Option.bind_eq_some_iff,
                                Option.some.injEq] at hprod
                              obtain ⟨vd', hvd', vq, hq, rfl⟩ := hprod
                              simp only [SymExpr.eval, Option.some.injEq] at hvd'; subst hvd'
                              have hvq := checkDivMagicExpr_sound hck ha hq hd
                              rw [UInt64.mul_comm, hvq, X86.Encode.truncate_mul, hd', ← X86.Encode.truncate_mul]
                            · simp [hwd] at hck
                        | _ => simp at hck
                | shl =>
                    cases p2 with
                    | imm sh =>
                        dsimp only at hck
                        by_cases hwd : (wp == w && isPow2 w d sh.toNat) = true
                        · simp only [hwd, ↓reduceIte] at hck
                          simp only [Bool.and_eq_true, beq_iff_eq] at hwd
                          obtain ⟨rfl, hp2⟩ := hwd
                          rw [SymExpr.eval] at hprod
                          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hprod
                          obtain ⟨vq, hq, vsh, hvsh, hsh⟩ := hprod
                          simp only [SymExpr.eval, Option.some.injEq] at hvsh; subst hvsh
                          have hvq := checkDivMagicExpr_sound hck ha hq hd
                          have hmul_eq := isPow2_mul hp2 vq
                          rw [UInt64.ofNat_toNat] at hmul_eq
                          rw [← hmul_eq] at hsh
                          simp only [BinOp.eval, Option.some.injEq] at hsh
                          rw [← hsh, hvq]
                        · simp [hwd] at hck
                    | _ => simp at hck
                | _ => simp at hck
            | _ => simp at hck
          rw [hvprod]
          exact urem_sub_mul_udiv w va d
        · simp [hwa] at hck
    | _ => simp at hck

/-- Soundness of `exprEquivAux`: structural congruence + Granlund–Montgomery constant
division/remainder equivalence. -/
theorem exprEquivAux_sound {ρ : Env} {ctx : Word} {snaps : MemSnaps} {e1 e2 : SymExpr} {v1 v2 : Word}
    (heq : exprEquivAux e1 e2 = true)
    (h1 : e1.eval ρ ctx snaps = some v1)
    (h2 : e2.eval ρ ctx snaps = some v2) : v1 = v2 := by
  induction e1 generalizing e2 v1 v2 with
  | reg x =>
      cases e2 with
      | reg y =>
          simp only [exprEquivAux, beq_iff_eq] at heq; subst heq
          rw [h1] at h2; exact Option.some.inj h2
      | _ => simp [exprEquivAux] at heq
  | imm k =>
      cases e2 with
      | imm k2 =>
          simp only [exprEquivAux, beq_iff_eq] at heq; subst heq
          rw [h1] at h2; exact Option.some.inj h2
      | _ => simp [exprEquivAux] at heq
  | ctx =>
      cases e2 with
      | ctx => rw [h1] at h2; exact Option.some.inj h2
      | _ => simp [exprEquivAux] at heq
  | bin o1 w1 a1 b1 iha ihb =>
      have hstruct : ∀ {o2 w2 a2 b2}, e2 = .bin o2 w2 a2 b2 →
          (o1 == o2 && w1 == w2 && exprEquivAux a1 a2 && exprEquivAux b1 b2) = true → v1 = v2 := by
        intro o2 w2 a2 b2 he2 hs
        subst he2
        simp only [Bool.and_eq_true, beq_iff_eq] at hs
        obtain ⟨⟨⟨rfl, rfl⟩, hae⟩, hbe⟩ := hs
        rw [SymExpr.eval] at h1 h2
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h1 h2
        obtain ⟨va1, ha1, vb1, hb1, hv1⟩ := h1
        obtain ⟨va2, ha2, vb2, hb2, hv2⟩ := h2
        rw [iha hae ha1 ha2, ihb hbe hb1 hb2, hv2] at hv1
        exact (Option.some.inj hv1).symm
      simp only [exprEquivAux] at heq
      split at heq
      · rename_i d
        by_cases hck : checkDivMagicExpr w1 a1 d e2 = true
        · rw [SymExpr.eval] at h1
          simp only [BinOp.eval, Option.bind_eq_bind, Option.bind_eq_some_iff, SymExpr.eval,
            Option.some.injEq] at h1
          obtain ⟨va, ha, vd, rfl, hdiv⟩ := h1
          split at hdiv
          · cases hdiv
          · rename_i hne0
            simp only [Option.some.injEq] at hdiv
            have hd : w1.truncate d ≠ 0 := by simpa using hne0
            have hv2 := checkDivMagicExpr_sound hck ha h2 hd
            rw [← hdiv, hv2]
        · simp only [hck, Bool.false_eq_true, ↓reduceIte] at heq
          cases e2 with
          | bin o2 w2 a2 b2 => exact hstruct rfl heq
          | _ => cases heq
      · rename_i d
        by_cases hck : checkRemMagicExpr w1 a1 d e2 = true
        · rw [SymExpr.eval] at h1
          simp only [BinOp.eval, Option.bind_eq_bind, Option.bind_eq_some_iff, SymExpr.eval,
            Option.some.injEq] at h1
          obtain ⟨va, ha, vd, rfl, hrem⟩ := h1
          split at hrem
          · cases hrem
          · simp only [Option.some.injEq] at hrem
            have ⟨_, hv2⟩ := checkRemMagicExpr_sound hck ha h2
            rw [← hrem, hv2]
        · simp only [hck, Bool.false_eq_true, ↓reduceIte] at heq
          cases e2 with
          | bin o2 w2 a2 b2 => exact hstruct rfl heq
          | _ => cases heq
      · simp only [Bool.false_eq_true, ↓reduceIte] at heq
        cases e2 with
        | bin o2 w2 a2 b2 => exact hstruct rfl heq
        | _ => cases heq
  | select c1 w1 a1 b1 t1 f1 iha ihb iht ihf =>
      cases e2 with
      | select c2 w2 a2 b2 t2 f2 =>
          simp only [exprEquivAux, Bool.and_eq_true, beq_iff_eq] at heq
          obtain ⟨⟨⟨⟨⟨rfl, rfl⟩, hae⟩, hbe⟩, hte⟩, hfe⟩ := heq
          rw [SymExpr.eval] at h1 h2
          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff,
            Option.some.injEq] at h1 h2
          obtain ⟨va1, ha1, vb1, hb1, vt1, ht1, vf1, hf1, rfl⟩ := h1
          obtain ⟨va2, ha2, vb2, hb2, vt2, ht2, vf2, hf2, rfl⟩ := h2
          rw [iha hae ha1 ha2, ihb hbe hb1 hb2, iht hte ht1 ht2, ihf hfe hf1 hf2]
      | _ => simp [exprEquivAux] at heq
  | test c1 w1 a1 b1 iha ihb =>
      cases e2 with
      | test c2 w2 a2 b2 =>
          simp only [exprEquivAux, Bool.and_eq_true, beq_iff_eq] at heq
          obtain ⟨⟨⟨rfl, rfl⟩, hae⟩, hbe⟩ := heq
          rw [SymExpr.eval] at h1 h2
          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff,
            Option.some.injEq] at h1 h2
          obtain ⟨va1, ha1, vb1, hb1, rfl⟩ := h1
          obtain ⟨va2, ha2, vb2, hb2, rfl⟩ := h2
          rw [iha hae ha1 ha2, ihb hbe hb1 hb2]
      | _ => simp [exprEquivAux] at heq
  | bsr64 a1 iha =>
      cases e2 with
      | bsr64 a2 =>
          simp only [exprEquivAux] at heq
          rw [SymExpr.eval] at h1 h2
          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h1 h2
          obtain ⟨va1, ha1, hv1⟩ := h1
          obtain ⟨va2, ha2, hv2⟩ := h2
          rw [iha heq ha1 ha2, hv2] at hv1
          exact (Option.some.inj hv1).symm
      | _ => simp [exprEquivAux] at heq
  | mulHi a1 b1 iha ihb =>
      cases e2 with
      | mulHi a2 b2 =>
          simp only [exprEquivAux, Bool.and_eq_true] at heq
          rw [SymExpr.eval] at h1 h2
          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff,
            Option.some.injEq] at h1 h2
          obtain ⟨va1, ha1, vb1, hb1, rfl⟩ := h1
          obtain ⟨va2, ha2, vb2, hb2, rfl⟩ := h2
          rw [iha heq.1 ha1 ha2, ihb heq.2 hb1 hb2]
      | _ => simp [exprEquivAux] at heq
  | divQ a1 b1 c1 iha ihb ihc =>
      cases e2 with
      | divQ a2 b2 c2 =>
          simp only [exprEquivAux, Bool.and_eq_true] at heq
          rw [SymExpr.eval] at h1 h2
          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h1 h2
          obtain ⟨va1, ha1, vb1, hb1, vc1, hc1, hv1⟩ := h1
          obtain ⟨va2, ha2, vb2, hb2, vc2, hc2, hv2⟩ := h2
          rw [iha heq.1.1 ha1 ha2, ihb heq.1.2 hb1 hb2, ihc heq.2 hc1 hc2, hv2] at hv1
          exact (Option.some.inj hv1).symm
      | _ => simp [exprEquivAux] at heq
  | divR a1 b1 c1 iha ihb ihc =>
      cases e2 with
      | divR a2 b2 c2 =>
          simp only [exprEquivAux, Bool.and_eq_true] at heq
          rw [SymExpr.eval] at h1 h2
          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h1 h2
          obtain ⟨va1, ha1, vb1, hb1, vc1, hc1, hv1⟩ := h1
          obtain ⟨va2, ha2, vb2, hb2, vc2, hc2, hv2⟩ := h2
          rw [iha heq.1.1 ha1 ha2, ihb heq.1.2 hb1 hb2, ihc heq.2 hc1 hc2, hv2] at hv1
          exact (Option.some.inj hv1).symm
      | _ => simp [exprEquivAux] at heq
  | addCLo a1 b1 c1 iha ihb ihc =>
      cases e2 with
      | addCLo a2 b2 c2 =>
          simp only [exprEquivAux, Bool.and_eq_true] at heq
          rw [SymExpr.eval] at h1 h2
          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff,
            Option.some.injEq] at h1 h2
          obtain ⟨va1, ha1, vb1, hb1, vc1, hc1, rfl⟩ := h1
          obtain ⟨va2, ha2, vb2, hb2, vc2, hc2, rfl⟩ := h2
          rw [iha heq.1.1 ha1 ha2, ihb heq.1.2 hb1 hb2, ihc heq.2 hc1 hc2]
      | _ => simp [exprEquivAux] at heq
  | addCHi a1 b1 c1 iha ihb ihc =>
      cases e2 with
      | addCHi a2 b2 c2 =>
          simp only [exprEquivAux, Bool.and_eq_true] at heq
          rw [SymExpr.eval] at h1 h2
          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff,
            Option.some.injEq] at h1 h2
          obtain ⟨va1, ha1, vb1, hb1, vc1, hc1, rfl⟩ := h1
          obtain ⟨va2, ha2, vb2, hb2, vc2, hc2, rfl⟩ := h2
          rw [iha heq.1.1 ha1 ha2, ihb heq.1.2 hb1 hb2, ihc heq.2 hc1 hc2]
      | _ => simp [exprEquivAux] at heq
  | subBLo a1 b1 c1 iha ihb ihc =>
      cases e2 with
      | subBLo a2 b2 c2 =>
          simp only [exprEquivAux, Bool.and_eq_true] at heq
          rw [SymExpr.eval] at h1 h2
          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff,
            Option.some.injEq] at h1 h2
          obtain ⟨va1, ha1, vb1, hb1, vc1, hc1, rfl⟩ := h1
          obtain ⟨va2, ha2, vb2, hb2, vc2, hc2, rfl⟩ := h2
          rw [iha heq.1.1 ha1 ha2, ihb heq.1.2 hb1 hb2, ihc heq.2 hc1 hc2]
      | _ => simp [exprEquivAux] at heq
  | subBHi a1 b1 c1 iha ihb ihc =>
      cases e2 with
      | subBHi a2 b2 c2 =>
          simp only [exprEquivAux, Bool.and_eq_true] at heq
          rw [SymExpr.eval] at h1 h2
          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff,
            Option.some.injEq] at h1 h2
          obtain ⟨va1, ha1, vb1, hb1, vc1, hc1, rfl⟩ := h1
          obtain ⟨va2, ha2, vb2, hb2, vc2, hc2, rfl⟩ := h2
          rw [iha heq.1.1 ha1 ha2, ihb heq.1.2 hb1 hb2, ihc heq.2 hc1 hc2]
      | _ => simp [exprEquivAux] at heq
  | load s1 w1 ex1 a1 iha =>
      cases e2 with
      | load s2 w2 ex2 a2 =>
          simp only [exprEquivAux, Bool.and_eq_true, beq_iff_eq] at heq
          obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, hae⟩ := heq
          rw [SymExpr.eval] at h1 h2
          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h1 h2
          obtain ⟨va1, ha1, hv1⟩ := h1
          obtain ⟨va2, ha2, hv2⟩ := h2
          rw [iha hae ha1 ha2, hv2] at hv1
          exact (Option.some.inj hv1).symm
      | _ => simp [exprEquivAux] at heq

/-- Soundness of `exprEquiv`: if `exprEquiv e1 e2 = true` and both `e1` and `e2` succeed,
they evaluate to the exact same word. -/
theorem exprEquiv_sound {ρ : Env} {ctx : Word} {snaps : MemSnaps} {e1 e2 : SymExpr} {v1 v2 : Word}
    (heq : exprEquiv e1 e2 = true)
    (h1 : e1.eval ρ ctx snaps = some v1)
    (h2 : e2.eval ρ ctx snaps = some v2) : v1 = v2 := by
  have hn1 := SymExpr.norm_sound h1
  have hn2 := SymExpr.norm_sound h2
  unfold exprEquiv at heq
  dsimp only at heq
  by_cases hsame : (e1.norm == e2.norm) = true
  · have hsame' : e1.norm = e2.norm := by simpa using hsame
    rw [hsame', hn2] at hn1
    exact (Option.some.inj hn1).symm
  · simp only [hsame, Bool.false_eq_true, ↓reduceIte] at heq
    exact exprEquivAux_sound heq hn1 hn2

/-! ## Branch facts, parity, fact-aware normalization, and interval soundness -/

/-- A word `v` lies in unsigned range `r`. -/
def URange.Contains (r : URange) (v : Word) : Prop :=
  r.lo ≤ v.toNat ∧ v.toNat ≤ r.hi

/-- A branch fact `f` holds in `(ρ, ctx, snaps)` (both sides evaluate and satisfy `f.cond`). -/
def PFact.Holds (ρ : Env) (ctx : Word) (snaps : MemSnaps) (f : PFact) : Prop :=
  ∃ v1 v2 : Word, f.lhs.eval ρ ctx snaps = some v1 ∧ f.rhs.eval ρ ctx snaps = some v2 ∧
    f.cond.holds f.width v1 v2 = f.result

/-- All facts in `facts` hold. -/
def FactsHold (ρ : Env) (ctx : Word) (snaps : MemSnaps) (facts : List PFact) : Prop :=
  ∀ f ∈ facts, f.Holds ρ ctx snaps

/-! ### Exact LSB parity soundness -/

/-- Parity predicate on a 64-bit word. -/
def Parity.Holds (p : Parity) (v : Word) : Prop :=
  match p with
  | .unknown => True
  | .even => v &&& 1 = 0
  | .odd => v &&& 1 = 1

private theorem word_and_one_iff_mod (v : Word) :
    (v &&& 1 = 0 ↔ v.toNat % 2 = 0) ∧ (v &&& 1 = 1 ↔ v.toNat % 2 = 1) := by
  have h : (v &&& 1).toNat = v.toNat % 2 := by
    rw [UInt64.toNat_and, show (1 : Word).toNat = 1 from rfl, Nat.and_one_is_mod]
  constructor
  · constructor
    · intro h0; rw [← h, h0]; rfl
    · intro hm; apply UInt64.toNat_inj.mp; rw [h, hm]; rfl
  · constructor
    · intro h1; rw [← h, h1]; rfl
    · intro hm; apply UInt64.toNat_inj.mp; rw [h, hm]; rfl

private theorem word_and_one_cases (v : Word) : v &&& 1 = 0 ∨ v &&& 1 = 1 := by
  have h := word_and_one_iff_mod v
  have hm : v.toNat % 2 = 0 ∨ v.toNat % 2 = 1 := by omega
  rcases hm with h0 | h1
  · exact .inl (h.1.2 h0)
  · exact .inr (h.2.2 h1)

private theorem truncate_and_one (w : Width) (v : Word) : w.truncate v &&& 1 = v &&& 1 := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_and, UInt64.toNat_and, show (1 : Word).toNat = 1 from rfl,
    Nat.and_one_is_mod, Nat.and_one_is_mod, X86.Encode.truncate_nat]
  have hdvd : 2 ∣ 2 ^ w.bits := by
    cases w <;> decide
  exact Nat.mod_mod_of_dvd v.toNat hdvd

private theorem truncate_one (w : Width) : w.truncate 1 = 1 := by
  cases w <;> decide

private theorem Parity.meet_holds {p1 p2 : Parity} {v : Word}
    (h1 : p1.Holds v) (h2 : p2.Holds v) : (p1.meet p2).Holds v := by
  cases p1 <;> cases p2 <;> simp_all [Parity.meet, Parity.Holds]

private theorem Parity.join_holds_left {p1 p2 : Parity} {v : Word}
    (h1 : p1.Holds v) : (p1.join p2).Holds v := by
  cases p1 <;> cases p2 <;> simp_all [Parity.join, Parity.Holds]

private theorem Parity.join_holds_right {p1 p2 : Parity} {v : Word}
    (h2 : p2.Holds v) : (p1.join p2).Holds v := by
  cases p1 <;> cases p2 <;> simp_all [Parity.join, Parity.Holds]

private theorem Parity.xor_add {p1 p2 : Parity} {a b : Word}
    (h1 : p1.Holds a) (h2 : p2.Holds b) : (p1.xor p2).Holds (a + b) := by
  have hmod : (a + b).toNat % 2 = (a.toNat % 2 + b.toNat % 2) % 2 := by
    rw [UInt64.toNat_add, Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 2 ^ 64), Nat.add_mod]
  cases p1 <;> cases p2 <;> simp only [Parity.xor, Parity.Holds] at h1 h2 ⊢ <;> try trivial
  · exact (word_and_one_iff_mod _).1.2 (by rw [hmod, (word_and_one_iff_mod a).1.1 h1, (word_and_one_iff_mod b).1.1 h2])
  · exact (word_and_one_iff_mod _).2.2 (by rw [hmod, (word_and_one_iff_mod a).1.1 h1, (word_and_one_iff_mod b).2.1 h2])
  · exact (word_and_one_iff_mod _).2.2 (by rw [hmod, (word_and_one_iff_mod a).2.1 h1, (word_and_one_iff_mod b).1.1 h2])
  · exact (word_and_one_iff_mod _).1.2 (by rw [hmod, (word_and_one_iff_mod a).2.1 h1, (word_and_one_iff_mod b).2.1 h2])

private theorem Parity.xor_sub {p1 p2 : Parity} {a b : Word}
    (h1 : p1.Holds a) (h2 : p2.Holds b) : (p1.xor p2).Holds (a - b) := by
  have hadd : (a - b) + b = a := by
    apply UInt64.toBitVec_inj.mp
    simp only [UInt64.toBitVec_add, UInt64.toBitVec_sub, BitVec.sub_add_cancel]
  have hmod : ((a - b).toNat + b.toNat) % 2 = a.toNat % 2 := by
    have := congrArg (fun z : Word => z.toNat % 2) hadd
    rw [UInt64.toNat_add, Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 2 ^ 64)] at this
    exact this
  cases p1 <;> cases p2 <;> simp only [Parity.xor, Parity.Holds] at h1 h2 ⊢ <;> try trivial
  · have ha := (word_and_one_iff_mod a).1.1 h1; have hb := (word_and_one_iff_mod b).1.1 h2
    exact (word_and_one_iff_mod _).1.2 (by omega)
  · have ha := (word_and_one_iff_mod a).1.1 h1; have hb := (word_and_one_iff_mod b).2.1 h2
    exact (word_and_one_iff_mod _).2.2 (by omega)
  · have ha := (word_and_one_iff_mod a).2.1 h1; have hb := (word_and_one_iff_mod b).1.1 h2
    exact (word_and_one_iff_mod _).2.2 (by omega)
  · have ha := (word_and_one_iff_mod a).2.1 h1; have hb := (word_and_one_iff_mod b).2.1 h2
    exact (word_and_one_iff_mod _).1.2 (by omega)

private theorem Parity.xor_bit {p1 p2 : Parity} {a b : Word}
    (h1 : p1.Holds a) (h2 : p2.Holds b) : (p1.xor p2).Holds (a ^^^ b) := by
  have hx : (a ^^^ b) &&& 1 = (a &&& 1) ^^^ (b &&& 1) := by
    apply UInt64.toBitVec_inj.mp; apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [UInt64.toBitVec_and, UInt64.toBitVec_xor, BitVec.getLsbD_and, BitVec.getLsbD_xor]
    cases (1 : Word).toBitVec.getLsbD i <;> simp
  cases p1 <;> cases p2 <;> simp only [Parity.xor, Parity.Holds] at h1 h2 ⊢ <;> try trivial
  all_goals rw [hx, h1, h2]; decide

private theorem Parity.mul_holds {p1 p2 : Parity} {a b : Word}
    (h1 : p1.Holds a) (h2 : p2.Holds b) : (p1.mul p2).Holds (a * b) := by
  have hmod : (a * b).toNat % 2 = ((a.toNat % 2) * (b.toNat % 2)) % 2 := by
    rw [UInt64.toNat_mul, Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 2 ^ 64), Nat.mul_mod]
  cases p1 <;> cases p2 <;> simp only [Parity.mul, Parity.Holds] at h1 h2 ⊢ <;> try trivial
  · exact (word_and_one_iff_mod _).1.2 (by rw [hmod, (word_and_one_iff_mod b).1.1 h2]; simp)
  · exact (word_and_one_iff_mod _).1.2 (by rw [hmod, (word_and_one_iff_mod a).1.1 h1]; simp)
  · exact (word_and_one_iff_mod _).1.2 (by rw [hmod, (word_and_one_iff_mod a).1.1 h1]; simp)
  · exact (word_and_one_iff_mod _).1.2 (by rw [hmod, (word_and_one_iff_mod a).1.1 h1]; simp)
  · exact (word_and_one_iff_mod _).1.2 (by rw [hmod, (word_and_one_iff_mod b).1.1 h2]; simp)
  · exact (word_and_one_iff_mod _).2.2 (by rw [hmod, (word_and_one_iff_mod a).2.1 h1, (word_and_one_iff_mod b).2.1 h2])

private theorem Parity.or_holds {p1 p2 : Parity} {a b : Word}
    (h1 : p1.Holds a) (h2 : p2.Holds b) : (p1.or p2).Holds (a ||| b) := by
  have hor : (a ||| b) &&& 1 = (a &&& 1) ||| (b &&& 1) := by
    apply UInt64.toBitVec_inj.mp; apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [UInt64.toBitVec_and, UInt64.toBitVec_or, BitVec.getLsbD_and, BitVec.getLsbD_or]
    cases (1 : Word).toBitVec.getLsbD i <;> simp
  cases p1 <;> cases p2 <;> simp only [Parity.or, Parity.Holds] at h1 h2 ⊢ <;> try trivial
  · rw [hor, h2]; rcases word_and_one_cases a with ha | ha <;> rw [ha] <;> decide
  · rw [hor, h1, h2]; decide
  · rw [hor, h1, h2]; decide
  · rw [hor, h1]; rcases word_and_one_cases b with hb | hb <;> rw [hb] <;> decide
  · rw [hor, h1, h2]; decide
  · rw [hor, h1, h2]; decide

private theorem Parity.and_holds {p1 p2 : Parity} {a b : Word}
    (h1 : p1.Holds a) (h2 : p2.Holds b) : (p1.and p2).Holds (a &&& b) := by
  have hand : (a &&& b) &&& 1 = (a &&& 1) &&& (b &&& 1) := by
    apply UInt64.toBitVec_inj.mp; apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [UInt64.toBitVec_and, BitVec.getLsbD_and]
    cases (1 : Word).toBitVec.getLsbD i <;> simp
  cases p1 <;> cases p2 <;> simp only [Parity.and, Parity.Holds] at h1 h2 ⊢ <;> try trivial
  · rw [hand, h2]; rcases word_and_one_cases a with ha | ha <;> rw [ha] <;> decide
  · rw [hand, h1]; rcases word_and_one_cases b with hb | hb <;> rw [hb] <;> decide
  · rw [hand, h1, h2]; decide
  · rw [hand, h1, h2]; decide
  · rw [hand, h1, h2]; decide
  · rw [hand, h1, h2]; decide

theorem parityFromCondImm_sound {w : Width} {c : Cond} {k v : Word} {res : Bool}
    (hc : c.holds w v k = res) : (parityFromCondImm w c k res).Holds v := by
  unfold parityFromCondImm
  have hc' : (if res then c else condNegate c).holds w v k = true := by
    cases res
    · simp [condNegate_holds, hc]
    · simpa using hc
  generalize (if res then c else condNegate c) = c' at hc' ⊢
  cases c' <;> simp only [Cond.holds, beq_iff_eq, bne_iff_ne] at hc'
  all_goals try exact trivial
  · -- eq
    have h1 := congrArg (fun z : Word => z &&& 1) hc'
    rw [truncate_and_one] at h1
    dsimp only
    split
    · rename_i h0
      have h0' : w.truncate k &&& 1 = 0 := by simpa using h0
      rw [h0'] at h1; exact h1
    · rename_i hne0
      have hne0' : w.truncate k &&& 1 ≠ 0 := by simpa using hne0
      rcases word_and_one_cases (w.truncate k) with h0 | hodd
      · exact absurd h0 hne0'
      · rw [hodd] at h1; exact h1
  · -- tz
    dsimp only
    split
    · rename_i hk1
      have hk1' : w.truncate k &&& 1 = 1 := by simpa using hk1
      have h1 := congrArg (fun z : Word => z &&& 1) hc'
      rw [truncate_and_one, UInt64.and_assoc, ← truncate_and_one w k, hk1'] at h1
      exact h1
    · trivial
  · -- tnz
    dsimp only
    split
    · rename_i hk1
      have hk1' : w.truncate k = 1 := by simpa using hk1
      have htr : w.truncate (v &&& k) = v &&& 1 := by
        have htand : w.truncate (v &&& k) = w.truncate v &&& w.truncate k := by
          apply UInt64.toBitVec_inj.mp; apply BitVec.eq_of_getLsbD_eq; intro i hi
          simp only [X86.Encode.truncate_bits, UInt64.toBitVec_and, BitVec.getLsbD_setWidth,
            BitVec.getLsbD_and]
          by_cases h : i < w.bits <;> simp [h, hi]
        rw [htand, hk1', truncate_and_one]
      rw [htr] at hc'
      rcases word_and_one_cases v with h0 | hodd
      · exact absurd h0 hc'
      · exact hodd
    · trivial

private theorem andContains_odd {ρ : Env} {ctx : Word} {snaps : MemSnaps}
    {e0 : SymExpr} {v : Word} (he0 : e0.eval ρ ctx snaps = some v) :
    ∀ {e : SymExpr} {ve : Word},
      andContains e0 e = true → e.eval ρ ctx snaps = some ve → ve &&& 1 ≠ 0 → v &&& 1 = 1 := by
  intro e
  induction e with
  | bin o w x y ihx ihy =>
      intro ve hc hev hodd
      cases o <;> cases w <;> try cases hc
      rw [SymExpr.eval] at hev
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.some.injEq, BinOp.eval, X86.Encode.truncate64] at hev
      obtain ⟨vx, hvx, vy, hvy, rfl⟩ := hev
      have hvx_odd : vx &&& 1 ≠ 0 := fun h0 => hodd (by rw [UInt64.and_comm vx vy, UInt64.and_assoc, h0, UInt64.and_zero])
      have hvy_odd : vy &&& 1 ≠ 0 := fun h0 => hodd (by rw [UInt64.and_assoc, h0, UInt64.and_zero])
      simp only [andContains, Bool.or_eq_true, beq_iff_eq] at hc
      rcases hc with ((rfl | rfl) | hx) | hy
      · rw [he0] at hvx; cases hvx
        rcases word_and_one_cases v with h0 | h1
        · exact absurd h0 hvx_odd
        · exact h1
      · rw [he0] at hvy; cases hvy
        rcases word_and_one_cases v with h0 | h1
        · exact absurd h0 hvy_odd
        · exact h1
      · exact ihx hx hvx hvx_odd
      · exact ihy hy hvy hvy_odd
  | _ => intro _ hc; cases hc

theorem parityFromFact_sound {ρ : Env} {ctx : Word} {snaps : MemSnaps}
    {e0 : SymExpr} {f : PFact} {v : Word}
    (hf : f.Holds ρ ctx snaps) (he0 : e0.eval ρ ctx snaps = some v) :
    (parityFromFact e0 f).Holds v := by
  obtain ⟨v1, v2, h1, h2, hcond⟩ := hf
  have hside : ∀ (side : SymExpr) (c : Cond) (k vs : Word),
      side.eval ρ ctx snaps = some vs → c.holds f.width vs k = f.result →
      (if side == e0 then parityFromCondImm f.width c k f.result
       else match side with
       | .bin .and .w64 x (.imm m) =>
           if x == e0 && f.width == .w64 && (m &&& 1 == 1) then
             let c' := if f.result then c else condNegate c
             if c' == .eq then (if k &&& 1 == 0 then .even else .odd) else .unknown
           else .unknown
       | .bin .and .w64 x y =>
           if andContains e0 (.bin .and .w64 x y) && f.width == .w64 && k == 1 then
             let c' := if f.result then c else condNegate c
             if c' == .tnz then .odd else .unknown
           else .unknown
       | _ => .unknown).Holds v := by
    intro side c k vs hvs hcs
    by_cases hse : (side == e0) = true
    · have hse' : side = e0 := by simpa using hse
      subst hse'; rw [he0] at hvs; cases hvs
      simp only [beq_self_eq_true, ↓reduceIte]
      exact parityFromCondImm_sound hcs
    · simp only [hse, Bool.false_eq_true, ↓reduceIte]
      cases side with
      | bin o w x y =>
          cases o <;> cases w <;> try exact trivial
          cases y with
          | imm m =>
              dsimp only
              split
              · rename_i hg
                simp only [Bool.and_eq_true, beq_iff_eq] at hg
                obtain ⟨⟨rfl, hw⟩, hm1⟩ := hg
                have hc' : (if f.result then c else condNegate c).holds .w64 vs k = true := by
                  rw [hw] at hcs
                  cases hres : f.result <;> rw [hres] at hcs <;> simp [condNegate_holds, hcs]
                generalize (if f.result then c else condNegate c) = c' at hc' ⊢
                split
                · rename_i hceq
                  have hceq' : c' = .eq := by simpa using hceq
                  rw [hceq'] at hc'
                  simp only [Cond.holds, X86.Encode.truncate64, beq_iff_eq] at hc'
                  rw [SymExpr.eval] at hvs
                  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff,
                    Option.some.injEq, BinOp.eval, X86.Encode.truncate64] at hvs
                  obtain ⟨vx, hvx, _, hm_eq, rfl⟩ := hvs
                  simp only [SymExpr.eval, Option.some.injEq] at hm_eq; subst hm_eq
                  rw [he0] at hvx; cases hvx
                  have hb := congrArg (fun z : Word => z &&& 1) hc'
                  rw [UInt64.and_assoc, hm1] at hb
                  split
                  · rename_i hk0; have hk0' : k &&& 1 = 0 := by simpa using hk0
                    rw [hk0'] at hb; exact hb
                  · rename_i hkne0; have hkne0' : k &&& 1 ≠ 0 := by simpa using hkne0
                    rcases word_and_one_cases k with hk0 | hk1
                    · exact absurd hk0 hkne0'
                    · rw [hk1] at hb; exact hb
                · trivial
              · trivial
          | _ =>
              dsimp only
              split
              · rename_i hg
                simp only [Bool.and_eq_true, beq_iff_eq] at hg
                obtain ⟨⟨hand, hw⟩, rfl⟩ := hg
                have hc' : (if f.result then c else condNegate c).holds .w64 vs 1 = true := by
                  rw [hw] at hcs
                  cases hres : f.result <;> rw [hres] at hcs <;> simp [condNegate_holds, hcs]
                generalize (if f.result then c else condNegate c) = c' at hc' ⊢
                split
                · rename_i hctnz
                  have hctnz' : c' = .tnz := by simpa using hctnz
                  rw [hctnz'] at hc'
                  simp only [Cond.holds, X86.Encode.truncate64, bne_iff_ne] at hc'
                  exact andContains_odd he0 hand hvs hc'
                · trivial
              · trivial
      | _ => trivial
  unfold parityFromFact
  cases hr : f.rhs with
  | imm k =>
      rw [hr] at h2; simp only [SymExpr.eval, Option.some.injEq] at h2; subst h2
      exact hside f.lhs f.cond k v1 h1 hcond
  | _ =>
      cases hl : f.lhs with
      | imm k =>
          rw [hl] at h1; simp only [SymExpr.eval, Option.some.injEq] at h1; subst h1
          rw [← condSwap_holds] at hcond
          exact hside _ (condSwap f.cond) k v2 (by rw [← hr]; exact h2) hcond
      | _ => trivial

private theorem parityFold_sound {ρ : Env} {ctx : Word} {snaps : MemSnaps}
    (e0 : SymExpr) (v : Word) (he0 : e0.eval ρ ctx snaps = some v) :
    ∀ (fs : List PFact) (acc : Parity),
      FactsHold ρ ctx snaps fs → acc.Holds v →
      (fs.foldl (init := acc) fun a f => a.meet (parityFromFact e0 f)).Holds v
  | [], _, _, hacc => hacc
  | f :: rest, acc, hfs, hacc =>
      parityFold_sound e0 v he0 rest _ (fun f' hf' => hfs f' (by simp [hf']))
        (Parity.meet_holds hacc (parityFromFact_sound (hfs f (by simp)) he0))

theorem parityOf_sound {ρ : Env} {ctx : Word} {snaps : MemSnaps} {facts : List PFact}
    (hfacts : FactsHold ρ ctx snaps facts) :
    ∀ {e : SymExpr} {v : Word}, e.eval ρ ctx snaps = some v → (parityOf facts e).Holds v := by
  intro e
  induction e with
  | imm w =>
      intro v hv
      simp only [SymExpr.eval, Option.some.injEq] at hv; subst hv
      unfold parityOf
      apply parityFold_sound (.imm w) w rfl facts _ hfacts
      by_cases h0 : (w &&& 1 == 0) = true
      · simp only [h0, ↓reduceIte, Parity.Holds]; exact beq_iff_eq.mp h0
      · simp only [h0, Bool.false_eq_true, ↓reduceIte, Parity.Holds]
        rcases word_and_one_cases w with hw0 | hw1
        · exact absurd (beq_iff_eq.mpr hw0) h0
        · exact hw1
  | bin o w a b iha ihb =>
      intro v hv
      unfold parityOf
      apply parityFold_sound (.bin o w a b) v hv facts _ hfacts
      simp only [SymExpr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at hv
      obtain ⟨va, ha, vb, hb, he⟩ := hv
      have hpa := iha ha; have hpb := ihb hb
      cases o <;> cases w <;> try exact trivial
      · simp only [BinOp.eval, X86.Encode.truncate64, Option.some.injEq] at he; subst he
        exact Parity.xor_add hpa hpb
      · simp only [BinOp.eval, X86.Encode.truncate64, Option.some.injEq] at he; subst he
        exact Parity.xor_sub hpa hpb
      · simp only [BinOp.eval, X86.Encode.truncate64, Option.some.injEq] at he; subst he
        exact Parity.and_holds hpa hpb
      · simp only [BinOp.eval, X86.Encode.truncate64, Option.some.injEq] at he; subst he
        exact Parity.or_holds hpa hpb
      · simp only [BinOp.eval, X86.Encode.truncate64, Option.some.injEq] at he; subst he
        exact Parity.xor_bit hpa hpb
      · simp only [BinOp.eval, X86.Encode.truncate64, Option.some.injEq] at he; subst he
        exact Parity.mul_holds hpa hpb
      · simp only [BinOp.eval, X86.Encode.truncate64, shiftMask, Option.some.injEq] at he; subst he
        cases b with
        | imm k =>
            simp only [SymExpr.eval, Option.some.injEq] at hb; subst hb
            dsimp only
            split
            · rename_i hnz
              exact shl_nonzero_even va k (by simpa [bne] using hnz)
            · rename_i hz
              have hk0 : k &&& 63 = 0 := by simpa [bne] using hz
              rw [hk0, UInt64.shiftLeft_zero]; exact hpa
        | _ => trivial
  | select c w a b t f _ _ iht ihf =>
      intro v hv
      unfold parityOf
      apply parityFold_sound (.select c w a b t f) v hv facts _ hfacts
      simp only [SymExpr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hv
      obtain ⟨va, _, vb, _, vt, ht, vf, hf, rfl⟩ := hv
      by_cases hc : c.holds w va vb = true
      · simp only [hc, ↓reduceIte]; exact Parity.join_holds_left (iht ht)
      · simp only [hc]; exact Parity.join_holds_right (ihf hf)
  | _ =>
      intro v hv
      unfold parityOf
      exact parityFold_sound _ v hv facts .unknown hfacts trivial

/-! ### Fact-aware normalization & `sfib` ring identity soundness -/

theorem odd_word_eq_two_mul_shr_add_one {x : Word} (hodd : x &&& 1 = 1) :
    x = (x >>> (1 &&& 63)) * 2 + 1 := by
  have hm : x.toNat % 2 = 1 := (word_and_one_iff_mod x).2.1 hodd
  have hlt : x.toNat < 2 ^ 64 := x.toNat_lt_size
  have hshr : (x >>> (1 &&& 63)).toNat = x.toNat / 2 := by
    rw [toNat_shr_word (by decide), show ((1 : Word) &&& 63).toNat = 1 from by decide]
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_add, UInt64.toNat_mul, hshr, show (2 : Word).toNat = 2 from rfl,
    show (1 : Word).toNat = 1 from rfl,
    Nat.mod_eq_of_lt (by omega : x.toNat / 2 * 2 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : x.toNat / 2 * 2 + 1 < 2 ^ 64)]
  omega

theorem sfib_word_identity {x : Word} (hodd : x &&& 1 = 1) :
    let q : Word := x >>> (1 &&& 63)
    q * (x + (0 - 1)) + x = q * (x + 1) + 1 := by
  intro q
  have hx : x = q * 2 + 1 := odd_word_eq_two_mul_shr_add_one hodd
  have h1 : (0 - 1 : Word) + 2 = 1 := by decide
  calc q * (x + (0 - 1)) + x
      = q * (x + (0 - 1)) + (q * 2 + 1) := by conv => lhs; rhs; rw [hx]
    _ = (q * (x + (0 - 1)) + q * 2) + 1 := (UInt64.add_assoc _ _ _).symm
    _ = q * ((x + (0 - 1)) + 2) + 1 := by rw [← UInt64.mul_add]
    _ = q * (x + ((0 - 1) + 2)) + 1 := by rw [UInt64.add_assoc]
    _ = q * (x + 1) + 1 := by rw [h1]

theorem matchSfibStep_sound {ρ : Env} {ctx : Word} {snaps : MemSnaps} {facts : List PFact}
    (hfacts : FactsHold ρ ctx snaps facts) {a b r : SymExpr} {va vb : Word}
    (hm : matchSfibStep facts a b = some r)
    (ha : a.eval ρ ctx snaps = some va) (hb : b.eval ρ ctx snaps = some vb) :
    r.eval ρ ctx snaps = some (va + vb) := by
  have hcheck : ∀ (prod x : SymExpr) (vp vx : Word),
      prod.eval ρ ctx snaps = some vp → x.eval ρ ctx snaps = some vx →
      (if parityOf facts x != .odd then none
       else
         let q := SymExpr.bin .shr .w64 x (.imm 1)
         let xm1 := mkAdd64 x (.imm (0 - 1))
         match prod with
         | .bin .mul .w64 p1 p2 =>
             if (p1 == q && p2 == xm1) || (p1 == xm1 && p2 == q) then
               some (mkAdd64 (mkBin .mul .w64 q (mkAdd64 x (.imm 1))) (.imm 1))
             else none
         | _ => none) = some r →
      r.eval ρ ctx snaps = some (vp + vx) := by
    intro prod x vp vx hp hx hck
    split at hck
    · cases hck
    · rename_i hodd_b
      have hodd_p : parityOf facts x = .odd := by simpa [bne] using hodd_b
      have hodd : vx &&& 1 = 1 := by
        have h := parityOf_sound hfacts hx
        rw [hodd_p] at h; exact h
      dsimp only at hck
      cases prod with
      | bin o w p1 p2 =>
          cases o <;> cases w <;> try cases hck
          dsimp only at hck
          split at hck
          · rename_i hmatch
            cases hck
            simp only [SymExpr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff,
              Option.some.injEq, BinOp.eval, X86.Encode.truncate64] at hp
            obtain ⟨v1, hv1, v2, hv2, rfl⟩ := hp
            have hq : (SymExpr.bin .shr .w64 x (.imm 1)).eval ρ ctx snaps = some (vx >>> (1 &&& 63)) := by
              simp only [SymExpr.eval, Option.bind_eq_bind, hx, Option.bind_some,
                BinOp.eval, X86.Encode.truncate64, shiftMask]
            have hxm1 : (mkAdd64 x (.imm (0 - 1))).eval ρ ctx snaps = some (vx + (0 - 1)) :=
              mkAdd64_sound hx rfl
            have hxp1 : (mkAdd64 x (.imm 1)).eval ρ ctx snaps = some (vx + 1) :=
              mkAdd64_sound hx rfl
            have hvp_eq : v1 * v2 = (vx >>> (1 &&& 63)) * (vx + (0 - 1)) := by
              simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hmatch
              rcases hmatch with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · rw [hq, Option.some.injEq] at hv1; rw [hxm1, Option.some.injEq] at hv2; rw [← hv1, ← hv2]
              · rw [hxm1, Option.some.injEq] at hv1; rw [hq, Option.some.injEq] at hv2; rw [← hv1, ← hv2, UInt64.mul_comm]
            have hmul : (mkBin .mul .w64 (SymExpr.bin .shr .w64 x (.imm 1)) (mkAdd64 x (.imm 1))).eval ρ ctx snaps =
                some ((vx >>> (1 &&& 63)) * (vx + 1)) :=
              mkBin_sound hq hxp1 (by simp [BinOp.eval, X86.Encode.truncate64])
            rw [hvp_eq, sfib_word_identity hodd]
            exact mkAdd64_sound hmul rfl
          · cases hck
      | _ => cases hck
  unfold matchSfibStep at hm
  dsimp only at hm
  split at hm
  · rename_i r1 hr1; cases hm
    exact hcheck a b va vb ha hb hr1
  · rw [UInt64.add_comm]
    exact hcheck b a vb va hb ha hm

theorem SymExpr.normFacts_sound {ρ : Env} {ctx : Word} {snaps : MemSnaps} {facts : List PFact}
    (hfacts : FactsHold ρ ctx snaps facts) :
    ∀ {e : SymExpr} {v : Word}, e.eval ρ ctx snaps = some v →
      (e.normFacts facts).eval ρ ctx snaps = some v
  | .reg _, _, h => h
  | .imm _, _, h => h
  | .ctx, _, h => h
  | .bin o w a b, v, h => by
      simp only [SymExpr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨va, ha, vb, hb, ho⟩ := h
      have hres : (mkBin o w (a.normFacts facts) (b.normFacts facts)).eval ρ ctx snaps = some v :=
        mkBin_sound (normFacts_sound hfacts ha) (normFacts_sound hfacts hb) ho
      unfold SymExpr.normFacts
      dsimp only
      generalize hmk : mkBin o w (a.normFacts facts) (b.normFacts facts) = res at hres ⊢
      split
      · rename_i x
        split
        · rename_i hev_b
          have hev_p : parityOf facts x = .even := by simpa using hev_b
          simp only [SymExpr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff,
            Option.some.injEq, BinOp.eval, X86.Encode.truncate64] at hres
          obtain ⟨vx, hvx, _, rfl, rfl⟩ := hres
          have hev : vx &&& 1 = 0 := by
            have hp := parityOf_sound hfacts hvx; rw [hev_p] at hp; exact hp
          rw [even_or_one_eq_add_one hev]
          exact mkAdd64_sound hvx rfl
        · exact hres
      · rename_i p q c
        cases hm : matchSfibStep facts p q with
        | none => exact hres
        | some r =>
            simp only [SymExpr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff,
              Option.some.injEq, BinOp.eval, X86.Encode.truncate64] at hres
            obtain ⟨vpq, ⟨vp, hp, vq, hq, rfl⟩, _, rfl, rfl⟩ := hres
            exact mkAdd64_sound (matchSfibStep_sound hfacts hm hp hq) rfl
      · rename_i p q _
        cases hm : matchSfibStep facts p q with
        | none => exact hres
        | some r =>
            simp only [Option.getD_some]
            simp only [SymExpr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff,
              Option.some.injEq, BinOp.eval, X86.Encode.truncate64] at hres
            obtain ⟨vp, hp, vq, hq, rfl⟩ := hres
            exact matchSfibStep_sound hfacts hm hp hq
      · exact hres
  | .select c w a b t f, v, h => by
      simp only [SymExpr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨va, ha, vb, hb, vt, ht, vf, hf, rfl⟩ := h
      apply SymExpr.norm_sound
      simp only [SymExpr.eval, Option.bind_eq_bind, normFacts_sound hfacts ha,
        normFacts_sound hfacts hb, normFacts_sound hfacts ht, normFacts_sound hfacts hf,
        Option.bind_some]
  | .test c w a b, v, h => by
      simp only [SymExpr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨va, ha, vb, hb, rfl⟩ := h
      apply SymExpr.norm_sound
      simp only [SymExpr.eval, Option.bind_eq_bind, normFacts_sound hfacts ha,
        normFacts_sound hfacts hb, Option.bind_some]
  | .bsr64 a, v, h => by
      simp only [SymExpr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨va, ha, hres⟩ := h
      apply SymExpr.norm_sound
      simp only [SymExpr.eval, Option.bind_eq_bind, normFacts_sound hfacts ha, Option.bind_some, hres]
  | .mulHi a b, v, h => by
      simp only [SymExpr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨va, ha, vb, hb, rfl⟩ := h
      apply SymExpr.norm_sound
      simp only [SymExpr.eval, Option.bind_eq_bind, normFacts_sound hfacts ha,
        normFacts_sound hfacts hb, Option.bind_some]
  | .divQ hi lo d, v, h => by
      simp only [SymExpr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨vhi, hhi, vlo, hlo, vd, hd, hres⟩ := h
      apply SymExpr.norm_sound
      simp only [SymExpr.eval, Option.bind_eq_bind, normFacts_sound hfacts hhi,
        normFacts_sound hfacts hlo, normFacts_sound hfacts hd, Option.bind_some, hres]
  | .divR hi lo d, v, h => by
      simp only [SymExpr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨vhi, hhi, vlo, hlo, vd, hd, hres⟩ := h
      apply SymExpr.norm_sound
      simp only [SymExpr.eval, Option.bind_eq_bind, normFacts_sound hfacts hhi,
        normFacts_sound hfacts hlo, normFacts_sound hfacts hd, Option.bind_some, hres]
  | .addCLo a b c, v, h => by
      simp only [SymExpr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨va, ha, vb, hb, vc, hc, rfl⟩ := h
      apply SymExpr.norm_sound
      simp only [SymExpr.eval, Option.bind_eq_bind, normFacts_sound hfacts ha,
        normFacts_sound hfacts hb, normFacts_sound hfacts hc, Option.bind_some]
  | .addCHi a b c, v, h => by
      simp only [SymExpr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨va, ha, vb, hb, vc, hc, rfl⟩ := h
      apply SymExpr.norm_sound
      simp only [SymExpr.eval, Option.bind_eq_bind, normFacts_sound hfacts ha,
        normFacts_sound hfacts hb, normFacts_sound hfacts hc, Option.bind_some]
  | .subBLo a b c, v, h => by
      simp only [SymExpr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨va, ha, vb, hb, vc, hc, rfl⟩ := h
      apply SymExpr.norm_sound
      simp only [SymExpr.eval, Option.bind_eq_bind, normFacts_sound hfacts ha,
        normFacts_sound hfacts hb, normFacts_sound hfacts hc, Option.bind_some]
  | .subBHi a b c, v, h => by
      simp only [SymExpr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨va, ha, vb, hb, vc, hc, rfl⟩ := h
      apply SymExpr.norm_sound
      simp only [SymExpr.eval, Option.bind_eq_bind, normFacts_sound hfacts ha,
        normFacts_sound hfacts hb, normFacts_sound hfacts hc, Option.bind_some]
  | .load s w e a, v, h => by
      simp only [SymExpr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨va, ha, hld⟩ := h
      simp only [SymExpr.normFacts, SymExpr.eval, Option.bind_eq_bind, normFacts_sound hfacts ha,
        Option.bind_some, hld]

theorem exprEquivFacts_sound {ρ : Env} {ctx : Word} {snaps : MemSnaps} {facts : List PFact}
    {e1 e2 : SymExpr} {v1 v2 : Word}
    (hfacts : FactsHold ρ ctx snaps facts)
    (heq : exprEquivFacts facts e1 e2 = true)
    (h1 : e1.eval ρ ctx snaps = some v1)
    (h2 : e2.eval ρ ctx snaps = some v2) : v1 = v2 := by
  unfold exprEquivFacts at heq
  split at heq
  · rename_i h; exact exprEquiv_sound h h1 h2
  · exact exprEquiv_sound heq (SymExpr.normFacts_sound hfacts h1) (SymExpr.normFacts_sound hfacts h2)

/-! ### Condition unwrapping & even-`addC` overflow soundness -/

theorem unwrapSelectCond_sound {ρ : Env} {ctx : Word} {snaps : MemSnaps}
    {c c' : Cond} {w w' : Width} {a b a' b' : SymExpr} {va vb : Word}
    (hu : unwrapSelectCond c w a b = some (c', w', a', b'))
    (ha : a.eval ρ ctx snaps = some va) (hb : b.eval ρ ctx snaps = some vb) :
    ∃ va' vb', a'.eval ρ ctx snaps = some va' ∧ b'.eval ρ ctx snaps = some vb' ∧
      c'.holds w' va' vb' = c.holds w va vb := by
  unfold unwrapSelectCond at hu
  split at hu
  · cases hu
  · rename_i hok
    simp only [Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, not_or, not_and,
      Classical.not_not] at hok
    obtain ⟨rfl, hc_eqne⟩ := hok
    have hce : c = .eq ∨ c = .ne := by
      by_cases h1 : c = .eq
      · exact .inl h1
      · exact .inr (hc_eqne h1)
    have hcheck : ∀ (e : SymExpr) (ve k : Word),
        e.eval ρ ctx snaps = some ve →
        (match e with
         | .select sc sw sa sb (.imm kt) (.imm kf) =>
             if kt == k && kf != k then
               some (if c == .eq then sc else condNegate sc, sw, sa, sb)
             else if kf == k && kt != k then
               some (if c == .eq then condNegate sc else sc, sw, sa, sb)
             else none
         | .test sc sw sa sb =>
             if k == 1 then
               some (if c == .eq then sc else condNegate sc, sw, sa, sb)
             else if k == 0 then
               some (if c == .eq then condNegate sc else sc, sw, sa, sb)
             else none
         | _ => none) = some (c', w', a', b') →
        ∃ va' vb', a'.eval ρ ctx snaps = some va' ∧ b'.eval ρ ctx snaps = some vb' ∧
          c'.holds w' va' vb' = c.holds .w64 ve k := by
      intro e ve k he hck
      cases e with
      | select sc sw sa sb et ef =>
          cases et <;> cases ef <;> try cases hck
          rename_i kt kf
          dsimp only at hck
          simp only [SymExpr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at he
          obtain ⟨vsa, hsa, vsb, hsb, _, rfl, _, rfl, rfl⟩ := he
          split at hck
          · rename_i h1
            simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at h1
            obtain ⟨rfl, hne⟩ := h1; cases hck
            refine ⟨vsa, vsb, hsa, hsb, ?_⟩
            rcases hce with rfl | rfl
            · have heq : (Cond.eq == Cond.eq) = true := rfl
              simp only [heq, ↓reduceIte]
              cases sc.holds w' vsa vsb <;>
                simp [Cond.holds, X86.Encode.truncate64, beq_false_of_ne hne]
            · have hne' : (Cond.ne == Cond.eq) = false := rfl
              simp only [hne', Bool.false_eq_true, ↓reduceIte, condNegate_holds]
              cases sc.holds w' vsa vsb <;>
                simp [Cond.holds, X86.Encode.truncate64, hne]
          · split at hck
            · rename_i h2
              simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at h2
              obtain ⟨rfl, hne⟩ := h2; cases hck
              refine ⟨vsa, vsb, hsa, hsb, ?_⟩
              rcases hce with rfl | rfl
              · have heq : (Cond.eq == Cond.eq) = true := rfl
                simp only [heq, ↓reduceIte, condNegate_holds]
                cases sc.holds w' vsa vsb <;>
                  simp [Cond.holds, X86.Encode.truncate64, beq_false_of_ne hne]
              · have hne' : (Cond.ne == Cond.eq) = false := rfl
                simp only [hne', Bool.false_eq_true, ↓reduceIte]
                cases sc.holds w' vsa vsb <;>
                  simp [Cond.holds, X86.Encode.truncate64, hne]
            · cases hck
      | test sc sw sa sb =>
          dsimp only at hck
          simp only [SymExpr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at he
          obtain ⟨vsa, hsa, vsb, hsb, rfl⟩ := he
          split at hck
          · rename_i hk1; have hk1' : k = 1 := by simp at hk1; exact hk1
            subst hk1'; cases hck
            refine ⟨vsa, vsb, hsa, hsb, ?_⟩
            rcases hce with rfl | rfl
            · have heq : (Cond.eq == Cond.eq) = true := rfl
              simp only [heq, ↓reduceIte]
              cases sc.holds w' vsa vsb <;>
                simp [Cond.holds, X86.Encode.truncate64]
            · have hne' : (Cond.ne == Cond.eq) = false := rfl
              simp only [hne', Bool.false_eq_true, ↓reduceIte, condNegate_holds]
              cases sc.holds w' vsa vsb <;>
                simp [Cond.holds, X86.Encode.truncate64]
          · split at hck
            · rename_i hk0; have hk0' : k = 0 := by simp at hk0; exact hk0
              subst hk0'; cases hck
              refine ⟨vsa, vsb, hsa, hsb, ?_⟩
              rcases hce with rfl | rfl
              · have heq : (Cond.eq == Cond.eq) = true := rfl
                simp only [heq, ↓reduceIte, condNegate_holds]
                cases sc.holds w' vsa vsb <;>
                  simp [Cond.holds, X86.Encode.truncate64]
              · have hne' : (Cond.ne == Cond.eq) = false := rfl
                simp only [hne', Bool.false_eq_true, ↓reduceIte]
                cases sc.holds w' vsa vsb <;>
                  simp [Cond.holds, X86.Encode.truncate64]
            · cases hck
      | _ => cases hck
    dsimp only at hu
    cases b with
    | imm k =>
        simp only [SymExpr.eval, Option.some.injEq] at hb; subst hb
        exact hcheck a va k ha hu
    | _ =>
        cases a with
        | imm k =>
            simp only [SymExpr.eval, Option.some.injEq] at ha; subst ha
            have hsw : c.holds .w64 k vb = c.holds .w64 vb k := by
              rcases hce with rfl | rfl
              · rw [← condSwap_holds]; rfl
              · rw [← condSwap_holds]; rfl
            rw [hsw]
            exact hcheck _ vb k hb hu
        | _ => cases hu

theorem unwrapOddBit2_sound {ρ : Env} {ctx : Word} {snaps : MemSnaps} {facts : List PFact}
    (hfacts : FactsHold ρ ctx snaps facts)
    {c c' : Cond} {w w' : Width} {a b a' b' : SymExpr} {va vb : Word}
    (hu : unwrapOddBit2 facts c w a b = some (c', w', a', b'))
    (ha : a.eval ρ ctx snaps = some va) (hb : b.eval ρ ctx snaps = some vb) :
    ∃ va' vb', a'.eval ρ ctx snaps = some va' ∧ b'.eval ρ ctx snaps = some vb' ∧
      c'.holds w' va' vb' = c.holds w va vb := by
  have hbit2 : ∀ (vx : Word), vx &&& 1 = 1 →
      ((vx &&& 3 == 1) = (vx &&& 2 == 0)) ∧ ((vx &&& 3 == 3) = (vx &&& 2 != 0)) := by
    intro vx hodd
    have h1 : vx.toNat % 2 = 1 := (word_and_one_iff_mod vx).2.1 hodd
    have h3 : (vx &&& 3).toNat = vx.toNat % 4 := by
      rw [UInt64.toNat_and, show (3 : Word).toNat = 2 ^ 2 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    have h2 : (vx &&& 2).toNat = if (vx.toNat / 2) % 2 = 1 then 2 else 0 := by
      have hbv : (vx &&& 2).toBitVec = (if vx.toBitVec.getLsbD 1 then (2 : Word).toBitVec else (0 : Word).toBitVec) := by
        apply BitVec.eq_of_getLsbD_eq; intro i hi
        simp only [UInt64.toBitVec_and, BitVec.getLsbD_and]
        by_cases hi1 : i = 1
        · subst hi1; cases hx1 : vx.toBitVec.getLsbD 1 <;> decide
        · have h2f : (2#64).getLsbD i = false := by
            simp only [BitVec.getLsbD_ofNat, Nat.testBit_eq_decide_div_mod_eq]
            cases i with | zero => decide | succ j =>
              cases j with | zero => exact absurd rfl hi1 | succ m =>
                have : 2 / 2 ^ (m + 2) = 0 := Nat.div_eq_of_lt (by
                  have : 4 ≤ 2 ^ (m + 2) := by
                    calc 4 = 2 ^ 2 := rfl
                      _ ≤ 2 ^ (m + 2) := Nat.pow_le_pow_right (by decide) (by omega)
                  omega)
                simp [this]
          cases vx.toBitVec.getLsbD 1 <;> simp [h2f]
      have hbit1 : vx.toBitVec.getLsbD 1 = decide ((vx.toNat / 2) % 2 = 1) := by
        simp [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
      rw [← UInt64.toNat_toBitVec, hbv, hbit1]
      by_cases hm : (vx.toNat / 2) % 2 = 1 <;> simp [hm]
    have h3eq1 : (vx &&& 3 = 1) ↔ (vx.toNat / 2) % 2 = 0 := by
      constructor
      · intro h; have := congrArg UInt64.toNat h; rw [h3] at this; change vx.toNat % 4 = 1 at this; omega
      · intro h; apply UInt64.toNat_inj.mp; rw [h3]; change vx.toNat % 4 = 1; omega
    have h3eq3 : (vx &&& 3 = 3) ↔ (vx.toNat / 2) % 2 = 1 := by
      constructor
      · intro h; have := congrArg UInt64.toNat h; rw [h3] at this; change vx.toNat % 4 = 3 at this; omega
      · intro h; apply UInt64.toNat_inj.mp; rw [h3]; change vx.toNat % 4 = 3; omega
    have h2eq0 : (vx &&& 2 = 0) ↔ (vx.toNat / 2) % 2 = 0 := by
      constructor
      · intro h; have := congrArg UInt64.toNat h; rw [h2] at this
        by_cases hm : (vx.toNat / 2) % 2 = 1
        · simp [hm] at this
        · omega
      · intro h; apply UInt64.toNat_inj.mp; rw [h2]; simp [show (vx.toNat / 2) % 2 ≠ 1 by omega]
    constructor
    · by_cases hm : (vx.toNat / 2) % 2 = 0
      · simp [h3eq1.2 hm, h2eq0.2 hm]
      · have hne1 : vx &&& 3 ≠ 1 := fun h => hm (h3eq1.1 h)
        have hne0 : vx &&& 2 ≠ 0 := fun h => hm (h2eq0.1 h)
        simp [beq_false_of_ne hne1, beq_false_of_ne hne0]
    · by_cases hm : (vx.toNat / 2) % 2 = 1
      · have hne0 : vx &&& 2 ≠ 0 := fun h => by have := h2eq0.1 h; omega
        simp [h3eq3.2 hm, hne0]
      · have hne3 : vx &&& 3 ≠ 3 := fun h => hm (h3eq3.1 h)
        have heq0 : vx &&& 2 = 0 := h2eq0.2 (by omega)
        simp [beq_false_of_ne hne3, heq0]
  unfold unwrapOddBit2 at hu
  split at hu
  · cases hu
  · rename_i hok
    simp only [Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, not_or, not_and,
      Classical.not_not] at hok
    obtain ⟨rfl, hc_eqne⟩ := hok
    have hce : c = .eq ∨ c = .ne := by
      by_cases h1 : c = .eq
      · exact .inl h1
      · exact .inr (hc_eqne h1)
    have hcheck : ∀ (e : SymExpr) (ve k : Word),
        e.eval ρ ctx snaps = some ve →
        (match e with
         | .bin .and .w64 x (.imm 3) =>
             if (k == 1 || k == 3) && parityOf facts x == .odd then
               let isTz := (c == .eq && k == 1) || (c == .ne && k == 3)
               some (if isTz then .tz else .tnz, .w64, x, .imm 2)
             else none
         | _ => none) = some (c', w', a', b') →
        ∃ va' vb', a'.eval ρ ctx snaps = some va' ∧ b'.eval ρ ctx snaps = some vb' ∧
          c'.holds w' va' vb' = c.holds .w64 ve k := by
      intro e ve k he hck
      split at hck
      · rename_i x
        split at hck
        · rename_i hg
          simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hg
          obtain ⟨hk13, hodd_p⟩ := hg
          cases hck
          rw [SymExpr.eval] at he
          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff,
            Option.some.injEq, BinOp.eval, X86.Encode.truncate64] at he
          obtain ⟨vx, hvx, _, h3eq, rfl⟩ := he
          simp only [SymExpr.eval, Option.some.injEq] at h3eq; subst h3eq
          have hodd : vx &&& 1 = 1 := by
            have hp := parityOf_sound hfacts hvx; rw [hodd_p] at hp; exact hp
          obtain ⟨hb1, hb3⟩ := hbit2 vx hodd
          refine ⟨vx, 2, hvx, rfl, ?_⟩
          rcases hce with rfl | rfl <;> rcases hk13 with rfl | rfl
          · simp [Cond.holds, X86.Encode.truncate64, hb1]
          · simp [Cond.holds, X86.Encode.truncate64, hb3]
          · simp [Cond.holds, X86.Encode.truncate64, bne, hb1]
          · simp [Cond.holds, X86.Encode.truncate64, bne, hb3]
        · cases hck
      · cases hck
    dsimp only at hu
    cases b with
    | imm k =>
        simp only [SymExpr.eval, Option.some.injEq] at hb; subst hb
        exact hcheck a va k ha hu
    | _ =>
        cases a with
        | imm k =>
            simp only [SymExpr.eval, Option.some.injEq] at ha; subst ha
            have hsw : c.holds .w64 k vb = c.holds .w64 vb k := by
              rcases hce with rfl | rfl
              · rw [← condSwap_holds]; rfl
              · rw [← condSwap_holds]; rfl
            rw [hsw]
            exact hcheck _ vb k hb hu
        | _ => cases hu

/-- If both `va` and `vb` are even 64-bit words, `(va + 1) + vb` overflows 2^64 iff `va + vb` does. -/
theorem addC_even_ovf_eq {va vb : Word} (ha : va &&& 1 = 0) (hb : vb &&& 1 = 0) :
    (Ovf.addC.eval (va + 1) vb).2 = (Ovf.addC.eval va vb).2 := by
  have ham : va.toNat % 2 = 0 := (word_and_one_iff_mod va).1.1 ha
  have hbm : vb.toNat % 2 = 0 := (word_and_one_iff_mod vb).1.1 hb
  have halt : va.toNat < 2 ^ 64 := va.toNat_lt_size
  have hblt : vb.toNat < 2 ^ 64 := vb.toNat_lt_size
  have ha1 : (va + 1).toNat = va.toNat + 1 := by
    rw [UInt64.toNat_add, show (1 : Word).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
  simp only [Ovf.eval, UInt64.lt_iff_toNat_lt, UInt64.toNat_add, ha1]
  by_cases h : va.toNat + vb.toNat < 2 ^ 64
  · have h1 : va.toNat + 1 + vb.toNat < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt h1]
    simp only [decide_eq_decide]; omega
  · have h1 : (va.toNat + vb.toNat) % 2 ^ 64 = va.toNat + vb.toNat - 2 ^ 64 := by
      have hdecomp : va.toNat + vb.toNat = (va.toNat + vb.toNat - 2 ^ 64) + 2 ^ 64 := by omega
      conv => lhs; rw [hdecomp]
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    have h2 : (va.toNat + 1 + vb.toNat) % 2 ^ 64 = va.toNat + 1 + vb.toNat - 2 ^ 64 := by
      have hdecomp : va.toNat + 1 + vb.toNat = (va.toNat + 1 + vb.toNat - 2 ^ 64) + 2 ^ 64 := by omega
      conv => lhs; rw [hdecomp]
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [h1, h2]
    simp only [decide_eq_decide]; omega

/-! ### Bitwise-OR bounds and interval soundness -/

private theorem bitvec_or_bounds :
    ∀ (w : Nat) (x y : BitVec w),
      x.toNat ≤ (x ||| y).toNat ∧ y.toNat ≤ (x ||| y).toNat ∧ (x ||| y).toNat ≤ x.toNat + y.toNat
  | 0, x, y => by
      have hx := x.isLt; have hy := y.isLt; have hxy := (x ||| y).isLt
      simp only [Nat.pow_zero] at hx hy hxy; omega
  | w + 1, x, y => by
      have hdecomp : ∀ (z : BitVec (w + 1)),
          z.toNat = (z.setWidth w).toNat + (if z.getLsbD w then 2 ^ w else 0) := by
        intro z
        have hlt := z.isLt
        rw [Nat.pow_succ] at hlt
        have hsw : (z.setWidth w).toNat = z.toNat % 2 ^ w := BitVec.toNat_setWidth w z
        have hbit : z.getLsbD w = decide (z.toNat / 2 ^ w % 2 = 1) := by
          simp [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
        have hq : z.toNat / 2 ^ w < 2 := Nat.div_lt_of_lt_mul (by omega)
        have hdm := Nat.div_add_mod z.toNat (2 ^ w)
        rw [hsw, hbit]
        generalize z.toNat / 2 ^ w = q at hq hdm ⊢
        by_cases h1 : q = 1
        · rw [h1, Nat.mul_one] at hdm; simp [h1]; omega
        · have h0 : q = 0 := by omega
          rw [h0, Nat.mul_zero, Nat.zero_add] at hdm; simp [h0]; omega
      have hsw_or : (x ||| y).setWidth w = x.setWidth w ||| y.setWidth w := by
        apply BitVec.eq_of_getLsbD_eq; intro i hi
        simp [hi]
      obtain ⟨h1, h2, h3⟩ := bitvec_or_bounds w (x.setWidth w) (y.setWidth w)
      rw [hdecomp x, hdecomp y, hdecomp (x ||| y), hsw_or, BitVec.getLsbD_or]
      cases x.getLsbD w <;> cases y.getLsbD w <;>
        simp only [Bool.false_or, Bool.true_or, ↓reduceIte, Bool.false_eq_true] <;> omega

private theorem word_or_bounds (a b : Word) :
    a.toNat ≤ (a ||| b).toNat ∧ b.toNat ≤ (a ||| b).toNat ∧ (a ||| b).toNat ≤ a.toNat + b.toNat := by
  simpa [UInt64.toNat_toBitVec, UInt64.toBitVec_or] using bitvec_or_bounds 64 a.toBitVec b.toBitVec

theorem URange.inter_contains {r1 r2 : URange} {v : Word}
    (h1 : r1.Contains v) (h2 : r2.Contains v) : (r1.inter r2).Contains v := by
  simp only [URange.Contains, URange.inter] at h1 h2 ⊢
  omega

theorem URange.refineRight_contains {r : URange} {c : Cond} {k v : Word} {res : Bool}
    (hr : r.Contains v) (hc : c.holds .w64 v k = res) :
    (r.refineRight c k res).Contains v := by
  unfold URange.refineRight
  dsimp only
  have hc' : (if res then c else condNegate c).holds .w64 v k = true := by
    cases res
    · simp [condNegate_holds, hc]
    · simpa using hc
  have hv_lt : v.toNat < 2 ^ 64 := v.toNat_lt_size
  have hk_lt : k.toNat < 2 ^ 64 := k.toNat_lt_size
  generalize (if res then c else condNegate c) = c' at hc' ⊢
  cases c' <;> dsimp only <;> simp only [Cond.holds, X86.Encode.truncate64, decide_eq_true_eq, beq_iff_eq,
    bne_iff_ne, UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le] at hc'
  all_goals try exact hr
  · have := congrArg UInt64.toNat hc'
    exact URange.inter_contains hr (by simp only [URange.Contains]; omega)
  · have hne : v.toNat ≠ k.toNat := fun h => hc' (UInt64.toNat_inj.mp h)
    have hr' := hr
    simp only [URange.Contains] at hr'
    by_cases hlo : (r.lo == k.toNat && decide (k.toNat + 1 < 2 ^ 64)) = true
    · simp only [hlo, ↓reduceIte]
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hlo
      exact URange.inter_contains hr (by simp only [URange.Contains]; omega)
    · simp only [hlo, Bool.false_eq_true, ↓reduceIte]
      by_cases hhi : (r.hi == k.toNat && decide (k.toNat > 0)) = true
      · simp only [hhi, ↓reduceIte]
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hhi
        exact URange.inter_contains hr (by simp only [URange.Contains]; omega)
      · simp only [hhi, Bool.false_eq_true, ↓reduceIte]
        exact hr
  · by_cases hk0 : (k.toNat == 0) = true
    · simp only [beq_iff_eq] at hk0; omega
    · simp only [hk0, Bool.false_eq_true, ↓reduceIte]
      exact URange.inter_contains hr (by simp only [URange.Contains]; omega)
  · exact URange.inter_contains hr (by simp only [URange.Contains]; omega)
  · by_cases hkmax : k.toNat + 1 ≥ 2 ^ 64
    · omega
    · simp only [hkmax, ↓reduceIte]
      exact URange.inter_contains hr (by simp only [URange.Contains]; omega)
  · exact URange.inter_contains hr (by simp only [URange.Contains]; omega)

theorem URange.refineNonImm_contains {r : URange} {c : Cond} {v v2 : Word} {res : Bool}
    (hr : r.Contains v) (hc : c.holds .w64 v v2 = res) :
    (r.refineNonImm c res).Contains v := by
  unfold URange.refineNonImm
  dsimp only
  have hc' : (if res then c else condNegate c).holds .w64 v v2 = true := by
    cases res
    · simp [condNegate_holds, hc]
    · simpa using hc
  have hv_lt : v.toNat < 2 ^ 64 := v.toNat_lt_size
  have hv2_lt : v2.toNat < 2 ^ 64 := v2.toNat_lt_size
  generalize (if res then c else condNegate c) = c' at hc' ⊢
  cases c' <;> simp only [Cond.holds, X86.Encode.truncate64, decide_eq_true_eq,
    UInt64.lt_iff_toNat_lt] at hc'
  all_goals try exact hr
  · exact URange.inter_contains hr (by simp only [URange.Contains]; omega)
  · exact URange.inter_contains hr (by simp only [URange.Contains]; omega)

theorem URange.refineParity_contains {r : URange} {p : Parity} {v : Word}
    (hr : r.Contains v) (hp : p.Holds v) : (r.refineParity p).Contains v := by
  simp only [URange.Contains] at hr
  unfold URange.refineParity
  have hok : ¬ (r.hi < r.lo) := by omega
  simp only [hok, ↓reduceIte]
  cases p with
  | unknown => exact hr
  | even =>
      have hm : v.toNat % 2 = 0 := (word_and_one_iff_mod v).1.1 hp
      simp only [URange.Contains]
      split <;> split <;> simp_all <;> omega
  | odd =>
      have hm : v.toNat % 2 = 1 := (word_and_one_iff_mod v).2.1 hp
      have hne0 : (r.hi == 0) = false := beq_false_of_ne (by omega)
      simp only [hne0, Bool.false_eq_true, ↓reduceIte, URange.Contains]
      split <;> split <;> simp_all <;> omega

private theorem refineRangeFold_contains {ρ : Env} {ctx : Word} {snaps : MemSnaps}
    (e0 : SymExpr) (p : Parity) (v : Word) (he0 : e0.eval ρ ctx snaps = some v) (hp : p.Holds v) :
    ∀ (fs : List PFact) (acc : URange),
      FactsHold ρ ctx snaps fs → acc.Contains v →
      (fs.foldl (init := acc) fun acc f =>
        if f.width == .w64 then
          let acc1 := match f.lhs, f.rhs with
            | l, .imm k => if l == e0 then acc.refineRight f.cond k f.result else acc
            | .imm k, r => if r == e0 then acc.refineRight (condSwap f.cond) k f.result else acc
            | l, r =>
                let a1 := if l == e0 then acc.refineNonImm f.cond f.result else acc
                if r == e0 then a1.refineNonImm (condSwap f.cond) f.result else a1
          acc1.refineParity p
        else acc).Contains v
  | [], acc, _, hacc => hacc
  | f :: rest, acc, hfs, hacc => by
      simp only [List.foldl_cons]
      apply refineRangeFold_contains e0 p v he0 hp rest _ (fun f' hf' => hfs f' (by simp [hf']))
      obtain ⟨v1, v2, h1, h2, hcond⟩ := hfs f (by simp)
      by_cases hw : (f.width == .w64) = true
      · have hw' : f.width = .w64 := by simpa using hw
        rw [hw'] at hcond
        simp only [hw, ↓reduceIte]
        apply URange.refineParity_contains _ hp
        cases hr : f.rhs with
        | imm k =>
            rw [hr] at h2; simp only [SymExpr.eval, Option.some.injEq] at h2; subst h2
            dsimp only
            by_cases hl : (f.lhs == e0) = true
            · have hl' : f.lhs = e0 := by simpa using hl
              rw [hl', he0] at h1; cases h1
              simp only [hl, ↓reduceIte]
              exact URange.refineRight_contains hacc hcond
            · simp [hl, hacc]
        | _ =>
            cases hl : f.lhs with
            | imm k =>
                rw [hl] at h1; simp only [SymExpr.eval, Option.some.injEq] at h1; subst h1
                dsimp only
                by_cases hre : (f.rhs == e0) = true
                · have hre' : f.rhs = e0 := by simpa using hre
                  rw [hre', he0] at h2; cases h2
                  rw [hr] at hre
                  simp only [hre, ↓reduceIte]
                  rw [← condSwap_holds] at hcond
                  exact URange.refineRight_contains hacc hcond
                · rw [hr] at hre; simp [hre, hacc]
            | _ =>
                dsimp only
                have ha1 : (if f.lhs == e0 then acc.refineNonImm f.cond f.result else acc).Contains v := by
                  by_cases hle : (f.lhs == e0) = true
                  · have hle' : f.lhs = e0 := by simpa using hle
                    rw [hle', he0] at h1; cases h1
                    simp only [hle, ↓reduceIte]
                    exact URange.refineNonImm_contains hacc hcond
                  · simp [hle, hacc]
                rw [hl] at ha1
                by_cases hre : (f.rhs == e0) = true
                · have hre' : f.rhs = e0 := by simpa using hre
                  rw [hre', he0] at h2; cases h2
                  rw [hr] at hre
                  simp only [hre, ↓reduceIte] at ha1 ⊢
                  rw [← condSwap_holds] at hcond
                  exact URange.refineNonImm_contains ha1 hcond
                · rw [hr] at hre
                  simp only [hre, Bool.false_eq_true, ↓reduceIte] at ha1 ⊢
                  exact ha1
      · simp [hw, hacc]

theorem refineRangeOnce_contains {ρ : Env} {ctx : Word} {snaps : MemSnaps}
    {facts : List PFact} {e : SymExpr} {p : Parity} {r0 : URange} {v : Word}
    (hfacts : FactsHold ρ ctx snaps facts) (he : e.eval ρ ctx snaps = some v)
    (hp : p.Holds v) (hr0 : r0.Contains v) :
    (refineRangeOnce facts e p r0).Contains v :=
  refineRangeFold_contains e p v he hp facts (r0.refineParity p) hfacts
    (URange.refineParity_contains hr0 hp)

theorem rangeOf_sound {ρ : Env} {ctx : Word} {snaps : MemSnaps} {facts : List PFact}
    (hfacts : FactsHold ρ ctx snaps facts) :
    ∀ {e : SymExpr} {v : Word}, e.eval ρ ctx snaps = some v → (rangeOf facts e).Contains v := by
  intro e
  induction e with
  | imm w =>
      intro v hv
      simp only [SymExpr.eval, Option.some.injEq] at hv; subst hv
      unfold rangeOf
      have hp := parityOf_sound hfacts (e := .imm w) rfl
      exact refineRangeOnce_contains hfacts rfl hp
        (refineRangeOnce_contains hfacts rfl hp ⟨Nat.le_refl _, Nat.le_refl _⟩)
  | bin o w a b iha ihb =>
      intro v hv
      have hfull : (URange.mk 0 (2 ^ 64 - 1)).Contains v := by
        simp only [URange.Contains]; have := v.toNat_lt_size; simp [UInt64.size] at this; omega
      unfold rangeOf
      have hp := parityOf_sound hfacts hv
      apply refineRangeOnce_contains hfacts hv hp
      apply refineRangeOnce_contains hfacts hv hp
      simp only [SymExpr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at hv
      obtain ⟨va, ha, vb, hb, he⟩ := hv
      have hra := iha ha
      have hrb := ihb hb
      cases o <;> cases w <;> try exact hfull
      · -- add .w64
        simp only [BinOp.eval, X86.Encode.truncate64, Option.some.injEq] at he; subst he
        dsimp only
        split
        · rename_i hlt
          simp only [URange.Contains, UInt64.toNat_add] at hra hrb ⊢
          rw [Nat.mod_eq_of_lt (by omega)]
          omega
        · cases b with
          | imm k =>
              simp only [SymExpr.eval, Option.some.injEq] at hb; subst hb
              dsimp only
              split
              · rename_i hneg
                simp only [Bool.and_eq_true, decide_eq_true_eq] at hneg
                simp only [URange.Contains, UInt64.toNat_add] at hra ⊢
                have hlt_k : k.toNat < 2 ^ 64 := k.toNat_lt_size
                have hmod : (va.toNat + k.toNat) % 2 ^ 64 = va.toNat - (2 ^ 64 - k.toNat) := by
                  have h1 : va.toNat + k.toNat = (va.toNat - (2 ^ 64 - k.toNat)) + 2 ^ 64 := by omega
                  rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
                rw [hmod]; omega
              · exact hfull
          | _ => exact hfull
      · -- sub .w64
        simp only [BinOp.eval, X86.Encode.truncate64, Option.some.injEq] at he; subst he
        dsimp only
        split
        · rename_i hle
          simp only [URange.Contains] at hra hrb ⊢
          rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega)]
          omega
        · exact hfull
      · -- and .w64
        simp only [BinOp.eval, X86.Encode.truncate64, Option.some.injEq] at he; subst he
        cases b with
        | imm k =>
            simp only [SymExpr.eval, Option.some.injEq] at hb; subst hb
            simp only [URange.Contains, UInt64.toNat_and] at hra ⊢
            exact ⟨Nat.zero_le _, Nat.le_min.mpr ⟨Nat.le_trans Nat.and_le_left hra.2, Nat.and_le_right⟩⟩
        | _ => exact hfull
      · -- or .w64
        simp only [BinOp.eval, X86.Encode.truncate64, Option.some.injEq] at he; subst he
        cases b with
        | imm k =>
            simp only [SymExpr.eval, Option.some.injEq] at hb; subst hb
            obtain ⟨hlo1, hlo2, hhi⟩ := word_or_bounds va k
            have hlt_or : (va ||| k).toNat < 2 ^ 64 := (va ||| k).toNat_lt_size
            simp only [URange.Contains] at hra ⊢
            omega
        | _ => exact hfull
      · -- mul .w64
        simp only [BinOp.eval, X86.Encode.truncate64, Option.some.injEq] at he; subst he
        dsimp only
        split
        · rename_i hlt
          simp only [URange.Contains, UInt64.toNat_mul] at hra hrb ⊢
          have hprod : va.toNat * vb.toNat ≤ (rangeOf facts a).hi * (rangeOf facts b).hi :=
            Nat.mul_le_mul hra.2 hrb.2
          rw [Nat.mod_eq_of_lt (by omega)]
          exact ⟨Nat.mul_le_mul hra.1 hrb.1, hprod⟩
        · exact hfull
      · -- shl .w64
        simp only [BinOp.eval, X86.Encode.truncate64, shiftMask, Option.some.injEq] at he; subst he
        cases b with
        | imm k =>
            simp only [SymExpr.eval, Option.some.injEq] at hb; subst hb
            dsimp only
            split
            · rename_i hlt
              have hc : (k &&& 63).toNat < 64 := Xv.Select.Proof.masked_lt .w64 k
              simp only [URange.Contains, toNat_shl_word hc] at hra ⊢
              have hprod : va.toNat * 2 ^ (k &&& 63).toNat ≤ (rangeOf facts a).hi * 2 ^ (k &&& 63).toNat :=
                Nat.mul_le_mul_right _ hra.2
              rw [Nat.mod_eq_of_lt (by omega)]
              exact ⟨Nat.mul_le_mul_right _ hra.1, hprod⟩
            · exact hfull
        | _ => exact hfull
      · -- shr .w64
        simp only [BinOp.eval, X86.Encode.truncate64, shiftMask, Option.some.injEq] at he; subst he
        cases b with
        | imm k =>
            simp only [SymExpr.eval, Option.some.injEq] at hb; subst hb
            have hc : (k &&& 63).toNat < 64 := Xv.Select.Proof.masked_lt .w64 k
            simp only [URange.Contains, toNat_shr_word hc] at hra ⊢
            exact ⟨Nat.div_le_div_right hra.1, Nat.div_le_div_right hra.2⟩
        | _ => exact hfull
  | select c w a b t f _ _ iht ihf =>
      intro v hv
      unfold rangeOf
      have hp := parityOf_sound hfacts hv
      apply refineRangeOnce_contains hfacts hv hp
      apply refineRangeOnce_contains hfacts hv hp
      simp only [SymExpr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hv
      obtain ⟨va, _, vb, _, vt, ht, vf, hf, rfl⟩ := hv
      have hrt := iht ht; have hrf := ihf hf
      simp only [URange.Contains] at hrt hrf ⊢
      cases hc : c.holds w va vb <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  | _ =>
      intro v hv
      unfold rangeOf
      have hp := parityOf_sound hfacts hv
      have hfull : (URange.mk 0 (2 ^ 64 - 1)).Contains v := by
        simp only [URange.Contains]; have := v.toNat_lt_size; simp [UInt64.size] at this; omega
      exact refineRangeOnce_contains hfacts hv hp (refineRangeOnce_contains hfacts hv hp hfull)

theorem factMatches_sound {ρ : Env} {ctx : Word} {snaps : MemSnaps} {f : PFact}
    {c : Cond} {w : Width} {a b : SymExpr} {va vb : Word} {res : Bool}
    (hf : f.Holds ρ ctx snaps) (hm : factMatches f c w a b = some res)
    (ha : a.eval ρ ctx snaps = some va) (hb : b.eval ρ ctx snaps = some vb) :
    c.holds w va vb = res := by
  obtain ⟨v1, v2, h1, h2, hcond⟩ := hf
  unfold factMatches at hm
  split at hm
  · cases hm
  · rename_i hwn
    have hw : f.width = w := by simpa using hwn
    rw [hw] at hcond
    split at hm
    · rename_i hlr
      simp only [Bool.and_eq_true, beq_iff_eq] at hlr
      obtain ⟨hl, hr⟩ := hlr
      rw [hl, ha] at h1; cases h1
      rw [hr, hb] at h2; cases h2
      split at hm
      · rename_i hc; have hc' : f.cond = c := by simpa using hc
        cases hm; rw [← hc']; exact hcond
      · split at hm
        · rename_i hc; have hc' : f.cond = condNegate c := by simpa using hc
          cases hm; rw [hc', condNegate_holds] at hcond
          cases hc1 : c.holds w va vb <;> cases hr1 : f.result <;> simp_all
        · cases hm
    · split at hm
      · rename_i hrl
        simp only [Bool.and_eq_true, beq_iff_eq] at hrl
        obtain ⟨hl, hr⟩ := hrl
        rw [hl, hb] at h1; cases h1
        rw [hr, ha] at h2; cases h2
        split at hm
        · rename_i hc; have hc' : f.cond = condSwap c := by simpa using hc
          cases hm; rw [hc', condSwap_holds] at hcond; exact hcond
        · split at hm
          · rename_i hc; have hc' : f.cond = condNegate (condSwap c) := by simpa using hc
            cases hm; rw [hc', condNegate_holds, condSwap_holds] at hcond
            cases hc1 : c.holds w va vb <;> cases hr1 : f.result <;> simp_all
          · cases hm
      · cases hm

theorem condFromRanges_sound {c : Cond} {ra rb : URange} {va vb : Word} {res : Bool}
    (h : condFromRanges c ra rb = some res) (ha : ra.Contains va) (hb : rb.Contains vb) :
    c.holds .w64 va vb = res := by
  unfold condFromRanges at h
  simp only [URange.Contains] at ha hb
  have hok : (decide (ra.hi < ra.lo) || decide (rb.hi < rb.lo)) = false := by simp; omega
  rw [hok] at h; simp only [Bool.false_eq_true, ↓reduceIte] at h
  cases c with
  | eq =>
      dsimp only at h; simp only [Cond.holds, X86.Encode.truncate64]
      split at h
      · rename_i h1; cases h; simp only [Bool.and_eq_true, beq_iff_eq] at h1 ⊢
        apply UInt64.toNat_inj.mp; omega
      · split at h
        · rename_i h2; cases h; simp only [Bool.or_eq_true, decide_eq_true_eq] at h2
          rw [beq_eq_false_iff_ne]; intro heq; have := congrArg UInt64.toNat heq; omega
        · cases h
  | ne =>
      dsimp only at h; simp only [Cond.holds, X86.Encode.truncate64]
      split at h
      · rename_i h1; cases h; simp only [Bool.or_eq_true, decide_eq_true_eq] at h1
        simp only [bne, Bool.not_eq_true', beq_eq_false_iff_ne]
        intro heq; have := congrArg UInt64.toNat heq; omega
      · split at h
        · rename_i h2; cases h; simp only [Bool.and_eq_true, beq_iff_eq] at h2
          simp only [bne, Bool.not_eq_false', beq_iff_eq]
          apply UInt64.toNat_inj.mp; omega
        · cases h
  | ult =>
      dsimp only at h; simp only [Cond.holds, X86.Encode.truncate64, UInt64.lt_iff_toNat_lt]
      split at h
      · cases h; simp; omega
      · split at h
        · cases h; simp; omega
        · cases h
  | ule =>
      dsimp only at h; simp only [Cond.holds, X86.Encode.truncate64, UInt64.le_iff_toNat_le]
      split at h
      · cases h; simp; omega
      · split at h
        · cases h; simp; omega
        · cases h
  | ugt =>
      dsimp only at h; simp only [Cond.holds, X86.Encode.truncate64, UInt64.lt_iff_toNat_lt]
      split at h
      · cases h; simp; omega
      · split at h
        · cases h; simp; omega
        · cases h
  | uge =>
      dsimp only at h; simp only [Cond.holds, X86.Encode.truncate64, UInt64.le_iff_toNat_le]
      split at h
      · cases h; simp; omega
      · split at h
        · cases h; simp; omega
        · cases h
  | slt | sle | sgt | sge | tz | tnz => cases h

theorem condFromFactsCore_sound {ρ : Env} {ctx : Word} {snaps : MemSnaps} {facts : List PFact}
    {c : Cond} {w : Width} {a' b' : SymExpr} {va vb : Word} {res : Bool}
    (hfacts : FactsHold ρ ctx snaps facts)
    (h : condFromFactsCore facts c w a' b' = some res)
    (ha' : a'.eval ρ ctx snaps = some va) (hb' : b'.eval ρ ctx snaps = some vb) :
    c.holds w va vb = res := by
  unfold condFromFactsCore at h
  cases hst : condStatic c w a' b' with
  | some r =>
      rw [hst] at h; cases h
      exact condStatic_sound hst ha' hb'
  | none =>
      rw [hst] at h
      cases hfm : facts.findSome? (fun f => factMatches f c w a' b') with
      | some r =>
          rw [hfm] at h; cases h
          obtain ⟨f, hmem, hm⟩ := List.exists_of_findSome?_eq_some hfm
          exact factMatches_sound (hfacts f hmem) hm ha' hb'
      | none =>
          rw [hfm] at h; dsimp only at h
          have hpar_sound : ∀ (x : SymExpr) (vx : Word) (h1 : (b' = .imm 1 ∧ x = a' ∧ vx = va ∧ vb = 1) ∨
              (a' = .imm 1 ∧ x = b' ∧ vx = vb ∧ va = 1)),
              (c == .tz || c == .tnz) = true →
              (match parityOf facts x with
               | .even => some (c == .tz)
               | .odd => some (c == .tnz)
               | .unknown => none) = some res →
              c.holds w va vb = res := by
            intro x vx h1 hct hpr
            have hx : x.eval ρ ctx snaps = some vx := by
              rcases h1 with ⟨_, rfl, rfl, _⟩ | ⟨_, rfl, rfl, _⟩
              · exact ha'
              · exact hb'
            have hpa := parityOf_sound hfacts hx
            have htr1 : w.truncate (vx &&& 1) = vx &&& 1 := by
              cases w <;> (
                apply UInt64.toBitVec_inj.mp
                apply BitVec.eq_of_getLsbD_eq
                intro i hi
                simp only [X86.Encode.truncate_bits, UInt64.toBitVec_and, BitVec.getLsbD_setWidth,
                  BitVec.getLsbD_and, X86.Width.bits]
                cases i with
                | zero => simp
                | succ k =>
                    have h1z : (1 : Word).toBitVec.getLsbD (k + 1) = false := by
                      show Nat.testBit 1 (k + 1) = false
                      rw [Nat.testBit_eq_decide_div_mod_eq,
                        Nat.div_eq_of_lt (Nat.one_lt_two_pow (by omega : k + 1 ≠ 0))]
                      rfl
                    simp only [h1z, Bool.and_false])
            have hand_eq : w.truncate (va &&& vb) = vx &&& 1 := by
              rcases h1 with ⟨_, _, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩
              · exact htr1
              · rw [UInt64.and_comm]; exact htr1
            simp only [Bool.or_eq_true, beq_iff_eq] at hct
            cases hp : parityOf facts x <;> rw [hp] at hpr hpa
            · cases hpr
            · cases hpr
              simp only [Parity.Holds] at hpa
              rcases hct with rfl | rfl <;> simp [Cond.holds, hand_eq, hpa]
            · cases hpr
              simp only [Parity.Holds] at hpa
              rcases hct with rfl | rfl <;> simp [Cond.holds, hand_eq, hpa]
          split at h
          · rename_i r hfp
            cases h
            split at hfp
            · rename_i hct
              split at hfp
              · rename_i x hx_eq
                by_cases hb1 : (b' == .imm 1) = true
                · have hb1' : b' = .imm 1 := by simpa using hb1
                  simp only [hb1, ↓reduceIte, Option.some.injEq] at hx_eq
                  rw [hb1'] at hb'; simp only [SymExpr.eval, Option.some.injEq] at hb'
                  exact hpar_sound x va (.inl ⟨hb1', hx_eq.symm, rfl, hb'.symm⟩) hct hfp
                · simp only [hb1, Bool.false_eq_true, ↓reduceIte] at hx_eq
                  by_cases ha1 : (a' == .imm 1) = true
                  · have ha1' : a' = .imm 1 := by simpa using ha1
                    simp only [ha1, ↓reduceIte, Option.some.injEq] at hx_eq
                    rw [ha1'] at ha'; simp only [SymExpr.eval, Option.some.injEq] at ha'
                    exact hpar_sound x vb (.inr ⟨ha1', hx_eq.symm, rfl, ha'.symm⟩) hct hfp
                  · simp [ha1] at hx_eq
              · cases hfp
            · cases hfp
          · by_cases hw : w = .w64
            · subst hw
              simp only [beq_self_eq_true, ↓reduceIte] at h
              exact condFromRanges_sound h (rangeOf_sound hfacts ha') (rangeOf_sound hfacts hb')
            · have hwf : (w == .w64) = false := beq_false_of_ne hw
              simp [hwf] at h

theorem condFromFacts_sound {ρ : Env} {ctx : Word} {snaps : MemSnaps} {facts : List PFact}
    {c : Cond} {w : Width} {a b : SymExpr} {va vb : Word} {res : Bool}
    (hfacts : FactsHold ρ ctx snaps facts)
    (h : condFromFacts facts c w a b = some res)
    (ha : a.eval ρ ctx snaps = some va) (hb : b.eval ρ ctx snaps = some vb) :
    c.holds w va vb = res := by
  have ha' := SymExpr.norm_sound ha
  have hb' := SymExpr.norm_sound hb
  unfold condFromFacts at h
  dsimp only at h
  cases hc1 : condFromFactsCore facts c w a.norm b.norm with
  | some r =>
      rw [hc1] at h; cases h
      exact condFromFactsCore_sound hfacts hc1 ha' hb'
  | none =>
      rw [hc1] at h
      cases hu : unwrapSelectCond c w a.norm b.norm with
      | none => rw [hu] at h; cases h
      | some resU =>
          rcases resU with ⟨c1, w1, a1, b1⟩
          rw [hu] at h
          obtain ⟨va1, vb1, ha1, hb1, heq⟩ := unwrapSelectCond_sound hu ha' hb'
          rw [← heq]
          exact condFromFactsCore_sound hfacts h (SymExpr.norm_sound ha1) (SymExpr.norm_sound hb1)

theorem ovfFromFacts_sound {ρ : Env} {ctx : Word} {snaps : MemSnaps} {facts : List PFact}
    {o : Ovf} {a b : SymExpr} {va vb : Word} {res : Bool}
    (hfacts : FactsHold ρ ctx snaps facts)
    (h : ovfFromFacts facts o a b = some res)
    (ha : a.eval ρ ctx snaps = some va) (hb : b.eval ρ ctx snaps = some vb) :
    (o.eval va vb).2 = res := by
  have ha' := SymExpr.norm_sound ha
  have hb' := SymExpr.norm_sound hb
  unfold ovfFromFacts at h
  dsimp only at h
  split at h
  · rename_i _ _ va' vb' heqa heqb
    rw [heqa] at ha'; rw [heqb] at hb'
    simp only [SymExpr.eval, Option.some.injEq] at ha' hb' h
    subst ha' hb' h; rfl
  · have hra := rangeOf_sound hfacts ha'
    have hrb := rangeOf_sound hfacts hb'
    simp only [URange.Contains] at hra hrb
    have hok : (decide ((rangeOf facts a.norm).hi < (rangeOf facts a.norm).lo) ||
        decide ((rangeOf facts b.norm).hi < (rangeOf facts b.norm).lo)) = false := by simp; omega
    rw [hok] at h; simp only [Bool.false_eq_true, ↓reduceIte] at h
    cases o with
    | addC =>
        dsimp only at h
        split at h
        · cases h
          simp only [Ovf.eval, decide_eq_false_iff_not, UInt64.lt_iff_toNat_lt, UInt64.toNat_add]
          rw [Nat.mod_eq_of_lt (by omega)]; omega
        · cases h
    | subB =>
        dsimp only at h
        split at h
        · cases h
          simp only [Ovf.eval, decide_eq_false_iff_not, UInt64.lt_iff_toNat_lt]; omega
        · cases h
    | mulOvf =>
        dsimp only at h
        split at h
        · cases h
          simp only [Ovf.eval, decide_eq_false_iff_not]
          have : va.toNat * vb.toNat ≤ (rangeOf facts a.norm).hi * (rangeOf facts b.norm).hi :=
            Nat.mul_le_mul hra.2 hrb.2
          omega
        · cases h

end IxCC.Lir.Opt
