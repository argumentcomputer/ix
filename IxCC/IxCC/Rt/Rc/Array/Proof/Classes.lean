import IxCC.Rt.Rc.Array.Proof.StepLemmas

/-! # Operational Correctness of O(1) Size-Class Lir Procedures

Proves exact Lir operational correctness of `arrClassFor` and `arrClassWords`:
* `arrClassFor_eval` / `arrClassFor_call_star`: for `1 ≤ w ≤ maxCellWords`,
  computes `classForFast w` (which equals `Rt.Rc.classFor w` by `classForFast_eq`)
  in zero clock charges with unchanged memory.
* `arrClassFor_zero_fail` / `arrClassFor_overflow_fail`: cleanly fails `.heap`
  for `w = 0` or `w > maxCellWords`.
* `arrClassWords_eval` / `arrClassWords_call_star`: for `1 ≤ c ≤ maxClass`,
  computes `classWords c` in zero clock charges with unchanged memory. -/

set_option autoImplicit false

namespace IxCC.Rt.Rc.Array

open Lir
open IxCC.Rt.Rc (maxClass classWords classFor maxCellWords maxCellWords_eq)
open IxCC.Rt.Rc.Procs (v i to)

/-! ## `arrClassFor` operational correctness -/

theorem arrClassFor_at_ret {P : Program} {fn : FunId} (hf : P.funcs[fn]? = some arrClassFor) {mem : X86.Memory} {context : Word}
    {rest : List Frame} {w : Nat} (h1 : 1 ≤ w) (h2 : w ≤ maxCellWords) :
    ∃ s', Sem.Star (semStep P)
        (State.mk mem context ({ fn := fn, label := 0, pos := 0, env := ({} : Env).insert 0 (UInt64.ofNat w) } :: rest))
        0 s' ∧
      (match rest with
       | [] => semStep P s' = .done ([UInt64.ofNat (classForFast w)], mem)
       | caller :: tail =>
           ∀ dst, caller.dsts = [dst] →
             semStep P s' =
               .next (State.mk mem context ({ caller with env := caller.env.insert dst (UInt64.ofNat (classForFast w)), dsts := [] } :: tail)) false) := by
  have hm : maxCellWords = 2 ^ 26 := maxCellWords_eq
  let e0 : Env := ({} : Env).insert 0 (UInt64.ofNat w)
  have he0 : (v 0).eval e0 = some (UInt64.ofNat w) := by
    simp only [v, Arg.eval, e0, env_get_insert_self]
  have hne0 : Cond.holds .eq .w64 (UInt64.ofNat w) (UInt64.ofNat 0) = false := by
    rw [cond_eq_w64]
    exact beq_false_of_ne (fun h => by
      have := congrArg UInt64.toNat h
      rw [u64_toNat_ofNat_lt (by omega), u64_toNat_ofNat_lt (by decide)] at this; omega)
  have hnle_max : Cond.holds .ugt .w64 (UInt64.ofNat w) (UInt64.ofNat maxCellWords) = false := by
    rw [cond_ugt_w64, u64_toNat_ofNat_lt (by omega), u64_toNat_ofNat_lt (by omega)]
    exact decide_eq_false (by omega)
  have s01 := step_br_false (p := P) (fn := fn) (lbl := 0) (rest := rest)
    (mem := mem) (context := context) (env := e0) hf rfl rfl he0 rfl hne0 rfl rfl rfl
  have s12 := step_br_false (p := P) (fn := fn) (lbl := 1) (rest := rest)
    (mem := mem) (context := context) (env := e0) hf rfl rfl he0 rfl hnle_max rfl rfl rfl
  by_cases hsmall : w ≤ 32
  · have hbr : Cond.holds .ule .w64 (UInt64.ofNat w) (UInt64.ofNat 32) = true := by
      rw [cond_ule_w64, u64_toNat_ofNat_lt (by omega), u64_toNat_ofNat_lt (by decide)]
      exact decide_eq_true hsmall
    have s23 := step_br_true (p := P) (fn := fn) (lbl := 2) (rest := rest)
      (mem := mem) (context := context) (env := e0) hf rfl rfl he0 rfl hbr rfl rfl rfl
    have sret := step_ret_one (p := P) (fn := fn) (lbl := 3)
      (mem := mem) (context := context) (rest := rest) (env := e0) (res := UInt64.ofNat w) hf rfl rfl he0
    refine ⟨_, .free s01 (.free s12 (.free s23 (.refl _))), ?_⟩
    have hcf : classForFast w = w := by simp [classForFast, hsmall]
    rw [hcf]
    exact sret
  · have hbr : Cond.holds .ule .w64 (UInt64.ofNat w) (UInt64.ofNat 32) = false := by
      rw [cond_ule_w64, u64_toNat_ofNat_lt (by omega), u64_toNat_ofNat_lt (by decide)]
      exact decide_eq_false hsmall
    have s24 := step_br_false (p := P) (fn := fn) (lbl := 2) (rest := rest)
      (mem := mem) (context := context) (env := e0) hf rfl rfl he0 rfl hbr rfl rfl rfl
    let x := w - 1
    let b := x.log2
    have hx_ge : 32 ≤ x := by omega
    have hx_lt : x < 2 ^ 26 := by omega
    have hb_ge5 : 5 ≤ b := by rw [Nat.le_log2 (by omega)]; omega
    have hb_le25 : b ≤ 25 := by have := (Nat.log2_lt (by omega)).mpr hx_lt; omega
    let e1 := e0.insert 1 (UInt64.ofNat x)
    let e2 := e1.insert 2 (UInt64.ofNat b)
    have s4a := step_assign (p := P) (fn := fn) (lbl := 4) (pos := 0)
      (rest := rest) (mem := mem) (context := context) (env := e0) hf rfl (by decide) rfl
      (rhs_bin_eval he0 rfl (binOp_sub64 w 1 (by omega) (by omega)))
    have s4b := step_assign (p := P) (fn := fn) (lbl := 4) (pos := 1)
      (rest := rest) (mem := mem) (context := context) (env := e1) hf rfl (by decide) rfl
      (rhs_bsr64_eval (x := x) (by simp only [v, Arg.eval, e1, env_get_insert_self]) (by omega) (by omega))
    have he2_0 : (v 0).eval e2 = some (UInt64.ofNat w) := by
      simp only [v, Arg.eval, e2, e1, e0, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]
    have he2_2 : (v 2).eval e2 = some (UInt64.ofNat b) := by
      simp only [v, Arg.eval, e2, env_get_insert_self]
    by_cases hmid : w ≤ 2048
    · have hbr2 : Cond.holds .ule .w64 (UInt64.ofNat w) (UInt64.ofNat 2048) = true := by
        rw [cond_ule_w64, u64_toNat_ofNat_lt (by omega), u64_toNat_ofNat_lt (by decide)]
        exact decide_eq_true hmid
      have s45 := step_br_true (p := P) (fn := fn) (lbl := 4) (rest := rest)
        (mem := mem) (context := context) (env := e2) hf rfl rfl he2_0 rfl hbr2 rfl rfl rfl
      let r3 := b - 5
      let r4 := r3 <<< 2
      let r5 := b - 2
      let r6 := x >>> r5
      let r7 := r6 &&& 3
      let r8 := r4 + 33
      let r9 := r8 + r7
      let e3 := e2.insert 3 (UInt64.ofNat r3)
      let e4 := e3.insert 4 (UInt64.ofNat r4)
      let e5 := e4.insert 5 (UInt64.ofNat r5)
      let e6 := e5.insert 6 (UInt64.ofNat r6)
      let e7 := e6.insert 7 (UInt64.ofNat r7)
      let e8 := e7.insert 8 (UInt64.ofNat r8)
      let e9 := e8.insert 9 (UInt64.ofNat r9)
      have hr4_eq : r4 = 4 * r3 := by show (b - 5) <<< 2 = 4 * (b - 5); rw [Nat.shiftLeft_eq]; omega
      have hr6_lt : r6 < 2 ^ 64 := by
        show x >>> (b - 2) < 2 ^ 64; rw [Nat.shiftRight_eq_div_pow]
        exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
      have hr7_le : r7 ≤ 3 := Nat.and_le_right
      have s50 := step_assign (p := P) (fn := fn) (lbl := 5) (pos := 0)
        (rest := rest) (mem := mem) (context := context) (env := e2) hf rfl (by decide) rfl
        (rhs_bin_eval he2_2 rfl (binOp_sub64 b 5 hb_ge5 (by omega)))
      have s51 := step_assign (p := P) (fn := fn) (lbl := 5) (pos := 1)
        (rest := rest) (mem := mem) (context := context) (env := e3) hf rfl (by decide) rfl
        (rhs_bin_eval (by simp only [v, Arg.eval, e3, env_get_insert_self]) rfl
          (binOp_shl64 r3 2 (by decide) (by omega) (by omega)))
      have s52 := step_assign (p := P) (fn := fn) (lbl := 5) (pos := 2)
        (rest := rest) (mem := mem) (context := context) (env := e4) hf rfl (by decide) rfl
        (rhs_bin_eval (by simp only [v, Arg.eval, e4, e3, e2, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]) rfl
          (binOp_sub64 b 2 (by omega) (by omega)))
      have s53 := step_assign (p := P) (fn := fn) (lbl := 5) (pos := 3)
        (rest := rest) (mem := mem) (context := context) (env := e5) hf rfl (by decide) rfl
        (rhs_bin_eval (by simp only [v, Arg.eval, e5, e4, e3, e2, e1, env_get_insert, Nat.reduceEqDiff, ↓reduceIte])
          (by simp only [v, Arg.eval, e5, env_get_insert_self])
          (binOp_shr64 x r5 (by omega : r5 < 64) (by omega)))
      have s54 := step_assign (p := P) (fn := fn) (lbl := 5) (pos := 4)
        (rest := rest) (mem := mem) (context := context) (env := e6) hf rfl (by decide) rfl
        (rhs_bin_eval (by simp only [v, Arg.eval, e6, env_get_insert_self]) rfl
          (binOp_and64 r6 3 hr6_lt (by decide)))
      have s55 := step_assign (p := P) (fn := fn) (lbl := 5) (pos := 5)
        (rest := rest) (mem := mem) (context := context) (env := e7) hf rfl (by decide) rfl
        (rhs_bin_eval (by simp only [v, Arg.eval, e7, e6, e5, e4, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]) rfl
          (binOp_add64 r4 33 (by omega)))
      have s56 := step_assign (p := P) (fn := fn) (lbl := 5) (pos := 6)
        (rest := rest) (mem := mem) (context := context) (env := e8) hf rfl (by decide) rfl
        (rhs_bin_eval (by simp only [v, Arg.eval, e8, env_get_insert_self])
          (by simp only [v, Arg.eval, e8, e7, env_get_insert, Nat.reduceEqDiff, ↓reduceIte])
          (binOp_add64 r8 r7 (by omega)))
      have sret := step_ret_one (p := P) (fn := fn) (lbl := 5)
        (mem := mem) (context := context) (rest := rest) (env := e9) (res := UInt64.ofNat r9)
        hf rfl rfl (by simp only [v, Arg.eval, e9, env_get_insert_self])
      have hr9_eq : r9 = classForFast w := by
        simp only [classForFast, hsmall, hmid, ↓reduceIte, r9, r8, r7, r6, r5, r4, r3, b, x]
        omega
      refine ⟨_, .free s01 (.free s12 (.free s24 (.free s4a (.free s4b (.free s45
        (.free s50 (.free s51 (.free s52 (.free s53 (.free s54 (.free s55 (.free s56 (.refl _))))))))))))), ?_⟩
      rw [← hr9_eq]
      exact sret
    · have hbr2 : Cond.holds .ule .w64 (UInt64.ofNat w) (UInt64.ofNat 2048) = false := by
        rw [cond_ule_w64, u64_toNat_ofNat_lt (by omega), u64_toNat_ofNat_lt (by decide)]
        exact decide_eq_false hmid
      have s47 := step_br_false (p := P) (fn := fn) (lbl := 4) (rest := rest)
        (mem := mem) (context := context) (env := e2) hf rfl rfl he2_0 rfl hbr2 rfl rfl rfl
      let e10 := e2.insert 10 (UInt64.ofNat (b + 46))
      have s70 := step_assign (p := P) (fn := fn) (lbl := 7) (pos := 0)
        (rest := rest) (mem := mem) (context := context) (env := e2) hf rfl (by decide) rfl
        (rhs_bin_eval he2_2 rfl (binOp_add64 b 46 (by omega)))
      have sret := step_ret_one (p := P) (fn := fn) (lbl := 7)
        (mem := mem) (context := context) (rest := rest) (env := e10) (res := UInt64.ofNat (b + 46))
        hf rfl rfl (by simp only [v, Arg.eval, e10, env_get_insert_self])
      have hcf : classForFast w = b + 46 := by
        simp only [classForFast, hsmall, hmid, ↓reduceIte]; rfl
      refine ⟨_, .free s01 (.free s12 (.free s24 (.free s4a (.free s4b (.free s47 (.free s70 (.refl _))))))), ?_⟩
      rw [hcf]
      exact sret

/-- Calling `arrClassFor` inside any caller frame returns `classForFast w` in zero
internal charges and leaves memory untouched. -/
theorem arrClassFor_call_star {P : Program} {fn : FunId} (hf : P.funcs[fn]? = some arrClassFor) {mem : X86.Memory} {context : Word}
    {caller : Frame} {tail : List Frame} {dst : VReg} {w : Nat}
    (hdst : caller.dsts = [dst]) (h1 : 1 ≤ w) (h2 : w ≤ maxCellWords) :
    Sem.Star (semStep P)
      (State.mk mem context ({ fn := fn, label := 0, pos := 0, env := ({} : Env).insert 0 (UInt64.ofNat w) } :: caller :: tail))
      0
      (State.mk mem context ({ caller with env := caller.env.insert dst (UInt64.ofNat (classForFast w)), dsts := [] } :: tail)) := by
  obtain ⟨s', hstar, hret⟩ := arrClassFor_at_ret hf (mem := mem) (context := context)
    (rest := caller :: tail) h1 h2
  exact hstar.trans (.free (hret dst hdst) (.refl _))

/-- Standalone `Lir.eval` theorem for `arrClassFor` on any valid word count `1 ≤ w ≤ 2^26`. -/
theorem arrClassFor_eval (mem : X86.Memory) (context : Word) (clock : Nat)
    {w : Nat} (h1 : 1 ≤ w) (h2 : w ≤ maxCellWords) :
    eval (arrayProgram fnClassFor) clock [UInt64.ofNat w] mem context =
      .ok ([UInt64.ofNat (classForFast w)], mem) := by
  have hinit := state_initial_of (p := arrayProgram fnClassFor) (args := [UInt64.ofNat w])
    (mem := mem) (context := context) (arrayProgram_func_classFor fnClassFor) rfl
  obtain ⟨s', hstar, hdone⟩ := arrClassFor_at_ret (arrayProgram_func_classFor fnClassFor) (mem := mem)
    (context := context) (rest := []) h1 h2
  apply (runs_eval hinit).eq
  simpa using Sem.Reaches.star hstar (k := clock) (.final (by rw [hdone]; exact .done))

/-- `arrClassFor(0)` cleanly fails with `.resource .heap`. -/
theorem arrClassFor_zero_fail (mem : X86.Memory) (context : Word) (clock : Nat) :
    eval (arrayProgram fnClassFor) clock [0] mem context = .resource .heap := by
  have hf := arrayProgram_func_classFor fnClassFor
  let e0 : Env := ({} : Env).insert 0 0
  have hinit := state_initial_of (p := arrayProgram fnClassFor) (args := [0])
    (mem := mem) (context := context) hf rfl
  have heq0 : Cond.holds .eq .w64 0 (UInt64.ofNat 0) = true := by decide
  have s06 := step_br_true (p := arrayProgram fnClassFor) (fn := fnClassFor) (lbl := 0) (rest := [])
    (mem := mem) (context := context) (env := e0) hf rfl rfl
    (by simp only [v, Arg.eval, e0, env_get_insert_self]) rfl heq0 rfl rfl rfl
  have sfin := final_fail (p := arrayProgram fnClassFor) (fn := fnClassFor) (lbl := 6)
    (rest := []) (mem := mem) (context := context) (env := e0) hf rfl rfl
  apply (runs_eval hinit).eq
  exact .free s06 (.final sfin)

/-- `arrClassFor(w)` for `w > maxCellWords` cleanly fails with `.resource .heap`. -/
theorem arrClassFor_overflow_fail (mem : X86.Memory) (context : Word) (clock : Nat)
    {w : Word} (hgt : maxCellWords < w.toNat) :
    eval (arrayProgram fnClassFor) clock [w] mem context = .resource .heap := by
  have hf := arrayProgram_func_classFor fnClassFor
  have hm : maxCellWords = 2 ^ 26 := maxCellWords_eq
  let e0 : Env := ({} : Env).insert 0 w
  have he0 : (v 0).eval e0 = some w := by
    simp only [v, Arg.eval, e0, env_get_insert_self]
  have hinit := state_initial_of (p := arrayProgram fnClassFor) (args := [w])
    (mem := mem) (context := context) hf rfl
  have hne0 : Cond.holds .eq .w64 w (UInt64.ofNat 0) = false := by
    rw [cond_eq_w64]
    exact beq_false_of_ne (fun h => by rw [h] at hgt; simp [hm] at hgt)
  have hgtb : Cond.holds .ugt .w64 w (UInt64.ofNat maxCellWords) = true := by
    rw [cond_ugt_w64, u64_toNat_ofNat_lt (by omega)]
    exact decide_eq_true hgt
  have s01 := step_br_false (p := arrayProgram fnClassFor) (fn := fnClassFor) (lbl := 0) (rest := [])
    (mem := mem) (context := context) (env := e0) hf rfl rfl he0 rfl hne0 rfl rfl rfl
  have s16 := step_br_true (p := arrayProgram fnClassFor) (fn := fnClassFor) (lbl := 1) (rest := [])
    (mem := mem) (context := context) (env := e0) hf rfl rfl he0 rfl hgtb rfl rfl rfl
  have sfin := final_fail (p := arrayProgram fnClassFor) (fn := fnClassFor)
    (lbl := 6) (rest := []) (mem := mem) (context := context) (env := e0) hf rfl rfl
  apply (runs_eval hinit).eq
  exact .free s01 (.free s16 (.final sfin))

/-! ## `arrClassWords` operational correctness -/

theorem arrClassWords_at_ret {P : Program} {fn : FunId} (hf : P.funcs[fn]? = some arrClassWords) {mem : X86.Memory} {context : Word}
    {rest : List Frame} {c : Nat} (h1 : 1 ≤ c) (h2 : c ≤ maxClass) :
    ∃ s', Sem.Star (semStep P)
        (State.mk mem context ({ fn := fn, label := 0, pos := 0, env := ({} : Env).insert 0 (UInt64.ofNat c) } :: rest))
        0 s' ∧
      (match rest with
       | [] => semStep P s' = .done ([UInt64.ofNat (classWords c)], mem)
       | caller :: tail =>
           ∀ dst, caller.dsts = [dst] →
             semStep P s' =
               .next (State.mk mem context ({ caller with env := caller.env.insert dst (UInt64.ofNat (classWords c)), dsts := [] } :: tail)) false) := by
  have hcmax : maxClass = 71 := rfl
  let e0 : Env := ({} : Env).insert 0 (UInt64.ofNat c)
  have he0 : (v 0).eval e0 = some (UInt64.ofNat c) := by
    simp only [v, Arg.eval, e0, env_get_insert_self]
  rw [← classWordsFast_eq h1 h2]
  by_cases hsmall : c ≤ 32
  · have hbr : Cond.holds .ule .w64 (UInt64.ofNat c) (UInt64.ofNat 32) = true := by
      rw [cond_ule_w64, u64_toNat_ofNat_lt (by omega), u64_toNat_ofNat_lt (by decide)]
      exact decide_eq_true hsmall
    have s01 := step_br_true (p := P) (fn := fn) (lbl := 0) (rest := rest)
      (mem := mem) (context := context) (env := e0) hf rfl rfl he0 rfl hbr rfl rfl rfl
    have sret := step_ret_one (p := P) (fn := fn) (lbl := 1)
      (mem := mem) (context := context) (rest := rest) (env := e0) (res := UInt64.ofNat c) hf rfl rfl he0
    refine ⟨_, .free s01 (.refl _), ?_⟩
    simp only [classWordsFast, hsmall, ↓reduceIte]
    exact sret
  · have hbr : Cond.holds .ule .w64 (UInt64.ofNat c) (UInt64.ofNat 32) = false := by
      rw [cond_ule_w64, u64_toNat_ofNat_lt (by omega), u64_toNat_ofNat_lt (by decide)]
      exact decide_eq_false hsmall
    have s02 := step_br_false (p := P) (fn := fn) (lbl := 0) (rest := rest)
      (mem := mem) (context := context) (env := e0) hf rfl rfl he0 rfl hbr rfl rfl rfl
    by_cases hmid : c ≤ 56
    · have hbr2 : Cond.holds .ule .w64 (UInt64.ofNat c) (UInt64.ofNat 56) = true := by
        rw [cond_ule_w64, u64_toNat_ofNat_lt (by omega), u64_toNat_ofNat_lt (by decide)]
        exact decide_eq_true hmid
      have s23 := step_br_true (p := P) (fn := fn) (lbl := 2) (rest := rest)
        (mem := mem) (context := context) (env := e0) hf rfl rfl he0 rfl hbr2 rfl rfl rfl
      let k := c - 33
      let r2 := k &&& 3
      let r3 := r2 + 1
      let r4 := r3 <<< 3
      let r5 := r4 + 32
      let r6 := k >>> 2
      let r7 := r5 <<< r6
      let e1 := e0.insert 1 (UInt64.ofNat k)
      let e2 := e1.insert 2 (UInt64.ofNat r2)
      let e3 := e2.insert 3 (UInt64.ofNat r3)
      let e4 := e3.insert 4 (UInt64.ofNat r4)
      let e5 := e4.insert 5 (UInt64.ofNat r5)
      let e6 := e5.insert 6 (UInt64.ofNat r6)
      let e7 := e6.insert 7 (UInt64.ofNat r7)
      have hr2_le : r2 ≤ 3 := Nat.and_le_right
      have hr4_eq : r4 = 8 * r3 := by show r3 <<< 3 = 8 * r3; rw [Nat.shiftLeft_eq]; omega
      have hr6_le : r6 ≤ 5 := by show (c - 33) >>> 2 ≤ 5; rw [Nat.shiftRight_eq_div_pow]; omega
      have hr7_lt : r7 < 2 ^ 64 := by
        show r5 <<< r6 < 2 ^ 64
        rw [Nat.shiftLeft_eq]
        have hpow : 2 ^ r6 ≤ 2 ^ 5 := Nat.pow_le_pow_right (by decide) hr6_le
        have hr5_le : r5 ≤ 64 := by omega
        calc r5 * 2 ^ r6 ≤ 64 * 2 ^ 5 := Nat.mul_le_mul hr5_le hpow
          _ < 2 ^ 64 := by decide
      have s30 := step_assign (p := P) (fn := fn) (lbl := 3) (pos := 0)
        (rest := rest) (mem := mem) (context := context) (env := e0) hf rfl (by decide) rfl
        (rhs_bin_eval he0 rfl (binOp_sub64 c 33 (by omega) (by omega)))
      have s31 := step_assign (p := P) (fn := fn) (lbl := 3) (pos := 1)
        (rest := rest) (mem := mem) (context := context) (env := e1) hf rfl (by decide) rfl
        (rhs_bin_eval (by simp only [v, Arg.eval, e1, env_get_insert_self]) rfl
          (binOp_and64 k 3 (by omega) (by decide)))
      have s32 := step_assign (p := P) (fn := fn) (lbl := 3) (pos := 2)
        (rest := rest) (mem := mem) (context := context) (env := e2) hf rfl (by decide) rfl
        (rhs_bin_eval (by simp only [v, Arg.eval, e2, env_get_insert_self]) rfl
          (binOp_add64 r2 1 (by omega)))
      have s33 := step_assign (p := P) (fn := fn) (lbl := 3) (pos := 3)
        (rest := rest) (mem := mem) (context := context) (env := e3) hf rfl (by decide) rfl
        (rhs_bin_eval (by simp only [v, Arg.eval, e3, env_get_insert_self]) rfl
          (binOp_shl64 r3 3 (by decide) (by omega) (by omega)))
      have s34 := step_assign (p := P) (fn := fn) (lbl := 3) (pos := 4)
        (rest := rest) (mem := mem) (context := context) (env := e4) hf rfl (by decide) rfl
        (rhs_bin_eval (by simp only [v, Arg.eval, e4, env_get_insert_self]) rfl
          (binOp_add64 r4 32 (by omega)))
      have s35 := step_assign (p := P) (fn := fn) (lbl := 3) (pos := 5)
        (rest := rest) (mem := mem) (context := context) (env := e5) hf rfl (by decide) rfl
        (rhs_bin_eval (by simp only [v, Arg.eval, e5, e4, e3, e2, e1, env_get_insert, Nat.reduceEqDiff, ↓reduceIte]) rfl
          (binOp_shr64 k 2 (by decide) (by omega)))
      have s36 := step_assign (p := P) (fn := fn) (lbl := 3) (pos := 6)
        (rest := rest) (mem := mem) (context := context) (env := e6) hf rfl (by decide) rfl
        (rhs_bin_eval (by simp only [v, Arg.eval, e6, e5, env_get_insert, Nat.reduceEqDiff, ↓reduceIte])
          (by simp only [v, Arg.eval, e6, env_get_insert_self])
          (binOp_shl64 r5 r6 (by omega : r6 < 64) (by omega) hr7_lt))
      have sret := step_ret_one (p := P) (fn := fn) (lbl := 3)
        (mem := mem) (context := context) (rest := rest) (env := e7) (res := UInt64.ofNat r7)
        hf rfl rfl (by simp only [v, Arg.eval, e7, env_get_insert_self])
      have hcw : classWordsFast c = r7 := by
        simp only [classWordsFast, hsmall, hmid, ↓reduceIte, r7, r6, r5, r4, r3, r2, k]
        rw [Nat.add_comm 32]
      refine ⟨_, .free s02 (.free s23 (.free s30 (.free s31 (.free s32 (.free s33 (.free s34 (.free s35 (.free s36 (.refl _))))))))), ?_⟩
      rw [hcw]
      exact sret
    · have hbr2 : Cond.holds .ule .w64 (UInt64.ofNat c) (UInt64.ofNat 56) = false := by
        rw [cond_ule_w64, u64_toNat_ofNat_lt (by omega), u64_toNat_ofNat_lt (by decide)]
        exact decide_eq_false hmid
      have s24 := step_br_false (p := P) (fn := fn) (lbl := 2) (rest := rest)
        (mem := mem) (context := context) (env := e0) hf rfl rfl he0 rfl hbr2 rfl rfl rfl
      let sh := c - 57
      let res := 4096 <<< sh
      have hsh_le : sh ≤ 14 := by omega
      have hres_lt : res < 2 ^ 64 := by
        show 4096 <<< sh < 2 ^ 64
        rw [Nat.shiftLeft_eq]
        have hpow : 2 ^ sh ≤ 2 ^ 14 := Nat.pow_le_pow_right (by decide) hsh_le
        calc 4096 * 2 ^ sh ≤ 4096 * 2 ^ 14 := Nat.mul_le_mul_left 4096 hpow
          _ < 2 ^ 64 := by decide
      let e8 := e0.insert 8 (UInt64.ofNat sh)
      let e9 := e8.insert 9 (UInt64.ofNat res)
      have s40 := step_assign (p := P) (fn := fn) (lbl := 4) (pos := 0)
        (rest := rest) (mem := mem) (context := context) (env := e0) hf rfl (by decide) rfl
        (rhs_bin_eval he0 rfl (binOp_sub64 c 57 (by omega) (by omega)))
      have s41 := step_assign (p := P) (fn := fn) (lbl := 4) (pos := 1)
        (rest := rest) (mem := mem) (context := context) (env := e8) hf rfl (by decide) rfl
        (rhs_bin_eval rfl (by simp only [v, Arg.eval, e8, env_get_insert_self])
          (binOp_shl64 4096 sh (by omega : sh < 64) (by decide) hres_lt))
      have sret := step_ret_one (p := P) (fn := fn) (lbl := 4)
        (mem := mem) (context := context) (rest := rest) (env := e9) (res := UInt64.ofNat res)
        hf rfl rfl (by simp only [v, Arg.eval, e9, env_get_insert_self])
      have hcw : classWordsFast c = res := by
        simp only [classWordsFast, hsmall, hmid, ↓reduceIte]; rfl
      refine ⟨_, .free s02 (.free s24 (.free s40 (.free s41 (.refl _)))), ?_⟩
      rw [hcw]
      exact sret

/-- Calling `arrClassWords` inside any caller frame returns `classWords c` in zero
internal charges and leaves memory untouched. -/
theorem arrClassWords_call_star {P : Program} {fn : FunId} (hf : P.funcs[fn]? = some arrClassWords) {mem : X86.Memory} {context : Word}
    {caller : Frame} {tail : List Frame} {dst : VReg} {c : Nat}
    (hdst : caller.dsts = [dst]) (h1 : 1 ≤ c) (h2 : c ≤ maxClass) :
    Sem.Star (semStep P)
      (State.mk mem context ({ fn := fn, label := 0, pos := 0, env := ({} : Env).insert 0 (UInt64.ofNat c) } :: caller :: tail))
      0
      (State.mk mem context ({ caller with env := caller.env.insert dst (UInt64.ofNat (classWords c)), dsts := [] } :: tail)) := by
  obtain ⟨s', hstar, hret⟩ := arrClassWords_at_ret hf (mem := mem) (context := context)
    (rest := caller :: tail) h1 h2
  exact hstar.trans (.free (hret dst hdst) (.refl _))

/-- Standalone `Lir.eval` theorem for `arrClassWords` across all 71 size classes. -/
theorem arrClassWords_eval (mem : X86.Memory) (context : Word) (clock : Nat)
    {c : Nat} (h1 : 1 ≤ c) (h2 : c ≤ maxClass) :
    eval (arrayProgram fnClassWords) clock [UInt64.ofNat c] mem context =
      .ok ([UInt64.ofNat (classWords c)], mem) := by
  have hinit := state_initial_of (p := arrayProgram fnClassWords) (args := [UInt64.ofNat c])
    (mem := mem) (context := context) (arrayProgram_func_classWords fnClassWords) rfl
  obtain ⟨s', hstar, hdone⟩ := arrClassWords_at_ret (arrayProgram_func_classWords fnClassWords) (mem := mem)
    (context := context) (rest := []) h1 h2
  apply (runs_eval hinit).eq
  simpa using Sem.Reaches.star hstar (k := clock) (.final (by rw [hdone]; exact .done))

end IxCC.Rt.Rc.Array
