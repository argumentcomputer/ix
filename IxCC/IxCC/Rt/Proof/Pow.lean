import IxCC.Rt.Proof.Procs

/-!
# `rt_nat_pow`

Square-and-multiply over untagged values (`Rt.Procs.natPow`). From its
entry with the words of `x` and `y`, the procedure returns the word of
`x ^ y` or fails with `natOverflow`:

* `y = 0` returns `1`; `x ≤ 1` returns `x`; `y > 62` (with `x ≥ 2`) fails;
* otherwise the loop at block 7 keeps `acc · base^n = x^y` with `1 ≤ acc`,
  `2 ≤ base`, `1 ≤ n` and both below `2^63`. A round multiplies `acc` by
  `base` when `n` is odd (checked by division and against `2^63`), halves
  `n`, and squares `base` while bits remain (checked likewise), so every
  passing check is exact (`Words.mul_check`) and `n` strictly decreases.
-/

set_option autoImplicit false

namespace IxCC.Rt.Proof

open IxCC.Lir
open IxCC.Rt.Procs

variable {p : Program} {mem : X86.Memory} {ctx : Word}

/-! ## The blocks -/

theorem natPow_b0 : natPow.blocks[0]? = some {
    body := #[.assign 2 (.bin .shr .w64 (.v 0) (.imm (UInt64.ofNat 1))),
      .assign 3 (.bin .shr .w64 (.v 1) (.imm (UInt64.ofNat 1)))]
    term := .br .eq .w64 (.v 3) (.imm (UInt64.ofNat 0)) ⟨1, []⟩ ⟨2, []⟩ } := rfl
theorem natPow_b1 : natPow.blocks[1]? = some { term := .ret [.imm (UInt64.ofNat 3)] } := rfl
theorem natPow_b2 : natPow.blocks[2]? =
    some { term := .br .ule .w64 (.v 2) (.imm (UInt64.ofNat 1)) ⟨3, []⟩ ⟨4, []⟩ } := rfl
theorem natPow_b3 : natPow.blocks[3]? = some { term := .ret [.v 0] } := rfl
theorem natPow_b4 : natPow.blocks[4]? =
    some { term := .br .ugt .w64 (.v 3) (.imm (UInt64.ofNat 62)) ⟨5, []⟩ ⟨6, []⟩ } := rfl
theorem natPow_b5 : natPow.blocks[5]? = some { term := .fail .natOverflow, cold := true } := rfl
theorem natPow_b6 : natPow.blocks[6]? =
    some { term := .jump ⟨7, [.imm (UInt64.ofNat 1), .v 2, .v 3]⟩ } := rfl
theorem natPow_b7 : natPow.blocks[7]? = some {
    params := [4, 5, 6]
    body := #[.assign 7 (.bin .and .w64 (.v 6) (.imm (UInt64.ofNat 1))),
      .assign 8 (.bin .mul .w64 (.v 4) (.v 5)), .assign 9 (.bin .udiv .w64 (.v 8) (.v 4)),
      .assign 10 (.test .ne .w64 (.v 9) (.v 5)), .assign 11 (.test .slt .w64 (.v 8) (.imm (UInt64.ofNat 0))),
      .assign 12 (.bin .or .w64 (.v 10) (.v 11)), .assign 13 (.bin .and .w64 (.v 12) (.v 7))]
    term := .br .ne .w64 (.v 13) (.imm (UInt64.ofNat 0)) ⟨8, []⟩ ⟨9, []⟩ } := rfl
theorem natPow_b8 : natPow.blocks[8]? = some { term := .fail .natOverflow, cold := true } := rfl
theorem natPow_b9 : natPow.blocks[9]? = some {
    body := #[.assign 14 (.select .eq .w64 (.v 7) (.imm (UInt64.ofNat 0)) (.v 4) (.v 8)),
      .assign 15 (.bin .shr .w64 (.v 6) (.imm (UInt64.ofNat 1)))]
    term := .br .eq .w64 (.v 15) (.imm (UInt64.ofNat 0)) ⟨10, []⟩ ⟨11, []⟩ } := rfl
theorem natPow_b10 : natPow.blocks[10]? = some {
    body := #[.assign 16 (.addr { base := some (.v 14), index := some (14, .one), disp := 1 })]
    term := .ret [.v 16] } := rfl
theorem natPow_b11 : natPow.blocks[11]? = some {
    body := #[.assign 17 (.bin .mul .w64 (.v 5) (.v 5)), .assign 18 (.bin .udiv .w64 (.v 17) (.v 5)),
      .assign 19 (.test .ne .w64 (.v 18) (.v 5)), .assign 20 (.test .slt .w64 (.v 17) (.imm (UInt64.ofNat 0))),
      .assign 21 (.bin .or .w64 (.v 19) (.v 20))]
    term := .br .ne .w64 (.v 21) (.imm (UInt64.ofNat 0)) ⟨12, []⟩ ⟨13, []⟩ } := rfl
theorem natPow_b12 : natPow.blocks[12]? = some { term := .fail .natOverflow, cold := true } := rfl
theorem natPow_b13 : natPow.blocks[13]? = some { term := .jump ⟨7, [.v 14, .v 17, .v 15]⟩ } := rfl

/-! ## Arithmetic of a round -/

theorem pow_round (A Bs N : Nat) :
    A * Bs ^ N = (if N % 2 = 1 then A * Bs else A) * (Bs * Bs) ^ (N / 2) := by
  have hN : N = 2 * (N / 2) + N % 2 := (Nat.div_add_mod N 2).symm
  have hpow : Bs ^ N = (Bs * Bs) ^ (N / 2) * Bs ^ (N % 2) := by
    conv => lhs; rw [hN]
    rw [Nat.pow_add, Nat.pow_mul, Nat.pow_two]
  rw [hpow]
  split
  · rename_i h
    rw [h, Nat.pow_one]
    rw [Nat.mul_comm ((Bs * Bs) ^ (N / 2)) Bs, ← Nat.mul_assoc]
  · have h : N % 2 = 0 := by omega
    rw [h, Nat.pow_zero, Nat.mul_one]

/-- A product checked by division by a nonzero factor and against `2^63`
is exact and below `2^63`. -/
theorem checked_mul {a b : Word} (ha : 0 < a.toNat) (hdiv : (a * b) / a = b) (hlt : (a * b).toNat < 2 ^ 63) :
    (a * b).toNat = a.toNat * b.toNat := by
  have hdiv' := congrArg UInt64.toNat hdiv
  rw [UInt64.toNat_div, UInt64.toNat_mul] at hdiv'
  have := mul_check ha hdiv'
  rw [UInt64.toNat_mul, Nat.mod_eq_of_lt this]

theorem word_ne_zero {a : Word} (h : 0 < a.toNat) : a ≠ 0 := by
  intro h'; subst h'; simp at h

/-- The overflow flag of a round: zero exactly when the product is not
needed or checks. -/
theorem round_flag {q base prod bit : Word} (hbit : bit = 0 ∨ bit = 1) :
    ((if q ≠ base then (1 : Word) else 0) ||| (if 2 ^ 63 ≤ prod.toNat then (1 : Word) else 0)) &&& bit = 0 ↔
      (bit = 1 → q = base ∧ prod.toNat < 2 ^ 63) := by
  rcases hbit with rfl | rfl <;> by_cases h1 : q = base <;> by_cases h2 : 2 ^ 63 ≤ prod.toNat <;>
    simp [h1, h2] <;> omega

theorem square_flag {q base sq : Word} :
    (if q ≠ base then (1 : Word) else 0) ||| (if 2 ^ 63 ≤ sq.toNat then (1 : Word) else 0) = 0 ↔
      q = base ∧ sq.toNat < 2 ^ 63 := by
  by_cases h1 : q = base <;> by_cases h2 : 2 ^ 63 ≤ sq.toNat <;> simp [h1, h2] <;> omega

theorem bit_toNat (nw : Word) : (nw &&& UInt64.ofNat 1).toNat = nw.toNat % 2 := by
  rw [UInt64.toNat_and]
  simp [Nat.and_one_is_mod]

theorem bit_cases (nw : Word) : (nw &&& UInt64.ofNat 1) = 0 ∨ (nw &&& UInt64.ofNat 1) = 1 := by
  have := bit_toNat nw
  rcases Nat.mod_two_eq_zero_or_one nw.toNat with h | h
  · exact .inl (UInt64.toNat_inj.mp (by rw [this, h]; rfl))
  · exact .inr (UInt64.toNat_inj.mp (by rw [this, h]; rfl))

theorem half_toNat (nw : Word) : (nw >>> (UInt64.ofNat 1 &&& 63)).toNat = nw.toNat / 2 := by
  rw [and63_one, UInt64.toNat_shiftRight]
  simp [Nat.shiftRight_eq_div_pow]

theorem fails_prepend {s s' : State} {c : Nat} (h : Sem.Star (semStep p) s c s')
    (hf : Sem.Fails (semStep p) s') : Sem.Fails (semStep p) s := by
  obtain ⟨c', s'', r, h', hs⟩ := hf
  exact ⟨c + c', s'', r, h.trans h', hs⟩

/-! ## The loop -/

/-- The square-and-multiply loop from block 7, with `acc`, `base`, `n` in
`v4`, `v5`, `v6`, reaches block 10's `ret v16` with the word of
`acc · base^n`, or fails. -/
theorem natPow_loop {g : FunId} (hf : p.funcs[g]? = some natPow) {rest : List Frame} :
    ∀ (N A Bs : Nat) (ρ : Env) (acc base nw : Word),
      acc.toNat = A → base.toNat = Bs → nw.toNat = N →
      1 ≤ A → A < 2 ^ 63 → 2 ≤ Bs → Bs < 2 ^ 63 → 1 ≤ N →
      ρ[4]? = some acc → ρ[5]? = some base → ρ[6]? = some nw →
      (∃ c ρ' w, Sem.Star (semStep p) (atState mem ctx g 7 0 ρ rest) c (atState mem ctx g 10 1 ρ' rest) ∧
        ρ'[16]? = some w ∧ natWord (A * Bs ^ N) = some w) ∨
      Sem.Fails (semStep p) (atState mem ctx g 7 0 ρ rest) := by
  intro N
  induction N using Nat.strongRecOn with
  | ind N ih =>
  intro A Bs ρ acc base nw hA hB hN hA1 hA2 hB1 hB2 hN1 h4 h5 h6
  have hacc0 : acc ≠ 0 := word_ne_zero (by omega)
  have hbase0 : base ≠ 0 := word_ne_zero (by omega)
  -- block 7's body
  let bit := nw &&& UInt64.ofNat 1
  let prod := acc * base
  let t10 : Word := if prod / acc ≠ base then 1 else 0
  let t11 : Word := if 2 ^ 63 ≤ prod.toNat then 1 else 0
  let ρ₇ := (((((((ρ.insert 7 bit).insert 8 prod).insert 9 (prod / acc)).insert 10 t10).insert 11 t11).insert 12
    (t10 ||| t11)).insert 13 ((t10 ||| t11) &&& bit))
  have hx7 : execList ρ mem ctx
      [.assign 7 (.bin .and .w64 (.v 6) (.imm (UInt64.ofNat 1))),
        .assign 8 (.bin .mul .w64 (.v 4) (.v 5)), .assign 9 (.bin .udiv .w64 (.v 8) (.v 4)),
        .assign 10 (.test .ne .w64 (.v 9) (.v 5)), .assign 11 (.test .slt .w64 (.v 8) (.imm (UInt64.ofNat 0))),
        .assign 12 (.bin .or .w64 (.v 10) (.v 11)), .assign 13 (.bin .and .w64 (.v 12) (.v 7))] =
      some (ρ₇, mem) := by
    simp (config := { decide := true }) only [lir_eval, ↓reduceIte, h4, h5, h6, hacc0, holds_slt_zero]
    simp [ρ₇, t10, t11, prod, bit]
  have hstar7 := stmts_at (p := p) (ctx := ctx) (rest := rest) (pre := []) (post := []) hf natPow_b7 rfl
    (by simp [Stmt.isCall]) hx7
  have hbit := bit_cases nw
  have hbitN := bit_toNat nw
  by_cases ht13 : (t10 ||| t11) &&& bit = 0
  · -- no overflow: block 9
    have hround := (round_flag hbit).1 ht13
    let acc' := if bit = 0 then acc else prod
    have hacc' : acc'.toNat = (if N % 2 = 1 then A * Bs else A) ∧ acc'.toNat < 2 ^ 63 := by
      rcases hbit with h0 | h1
      · have : N % 2 = 0 := by rw [← hN, ← hbitN]; show (nw &&& UInt64.ofNat 1).toNat = 0; rw [h0]; rfl
        simp only [acc', show bit = 0 from h0, ↓reduceIte, this]
        exact ⟨hA, by omega⟩
      · have : N % 2 = 1 := by rw [← hN, ← hbitN]; show (nw &&& UInt64.ofNat 1).toNat = 1; rw [h1]; rfl
        obtain ⟨hq, hlt⟩ := hround h1
        have hb1 : bit ≠ 0 := by rw [show bit = 1 from h1]; decide
        simp only [acc', hb1, ↓reduceIte, this]
        refine ⟨?_, hlt⟩
        rw [checked_mul (by omega) hq hlt, hA, hB]
    have hs7 := br_at (p := p) (mem := mem) (ctx := ctx) (rest := rest) (pos := 7) (ρ := ρ₇)
      (e := ⟨9, []⟩) (va := (t10 ||| t11) &&& bit) (vb := UInt64.ofNat 0) (vals := []) (ρ' := ρ₇)
      hf natPow_b7 rfl rfl (by simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₇])
      rfl (by simp only [lir_eval, ht13]; simp) rfl natPow_b9 rfl
    let half := nw >>> 1
    have hhalf : half.toNat = N / 2 := by
      have := half_toNat nw
      rw [and63_one] at this
      rw [← hN]; exact this
    let ρ₉ := (ρ₇.insert 14 acc').insert 15 half
    have hx9 : execList ρ₇ mem ctx
        [.assign 14 (.select .eq .w64 (.v 7) (.imm (UInt64.ofNat 0)) (.v 4) (.v 8)),
          .assign 15 (.bin .shr .w64 (.v 6) (.imm (UInt64.ofNat 1)))] = some (ρ₉, mem) := by
      simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₇, h4, h6]
      simp [ρ₉, acc', half, decide_eq_true_eq]
      rfl
    have hstar9 := stmts_at (p := p) (ctx := ctx) (rest := rest) (pre := []) (post := []) hf natPow_b9 rfl
      (by simp [Stmt.isCall]) hx9
    by_cases hN1 : N / 2 = 0
    · -- the last bit: block 10 retags and returns
      have hNodd : N % 2 = 1 := by omega
      have hhalf0 : half = 0 := UInt64.toNat_inj.mp (by rw [hhalf, hN1]; rfl)
      have hs9 := br_at (p := p) (mem := mem) (ctx := ctx) (rest := rest) (pos := 2) (ρ := ρ₉)
        (e := ⟨10, []⟩) (va := half) (vb := UInt64.ofNat 0) (vals := []) (ρ' := ρ₉)
        hf natPow_b9 rfl rfl (by simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₉])
        rfl (by simp only [lir_eval, hhalf0]; simp) rfl natPow_b10 rfl
      let w := acc' + acc' + 1
      have hx10 : execList ρ₉ mem ctx
          [.assign 16 (.addr { base := some (.v 14), index := some (14, .one), disp := 1 })] =
          some (ρ₉.insert 16 w, mem) := by
        simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₉, UInt64.mul_one]
        rfl
      have hstar10 := stmts_at (p := p) (ctx := ctx) (rest := rest) (pre := []) (post := []) hf natPow_b10 rfl
        (by simp [Stmt.isCall]) hx10
      left
      refine ⟨0, ρ₉.insert 16 w, w, ?_, by simp [env_insert_get], ?_⟩
      · have := hstar7.trans ((star_of_step hs7).trans (hstar9.trans ((star_of_step hs9).trans hstar10)))
        simpa using this
      · have hN' : N = 1 := by omega
        subst hN'
        obtain ⟨h1, h2⟩ := hacc'
        simp only [hNodd, ↓reduceIte] at h1
        refine natWord_iff.2 ⟨by rw [Nat.pow_one]; omega, ?_⟩
        rw [retag_toNat h2, h1, Nat.pow_one]
    · -- bits remain: square the base (block 11)
      have hhalfne : half ≠ 0 := fun h => hN1 (by rw [← hhalf, h]; rfl)
      have hs9 := br_at (p := p) (mem := mem) (ctx := ctx) (rest := rest) (pos := 2) (ρ := ρ₉)
        (e := ⟨11, []⟩) (va := half) (vb := UInt64.ofNat 0) (vals := []) (ρ' := ρ₉)
        hf natPow_b9 rfl rfl (by simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₉])
        rfl (by simp only [lir_eval]; simp [hhalfne]) rfl natPow_b11 rfl
      let sq := base * base
      let t19 : Word := if sq / base ≠ base then 1 else 0
      let t20 : Word := if 2 ^ 63 ≤ sq.toNat then 1 else 0
      let ρ₁₁ := ((((ρ₉.insert 17 sq).insert 18 (sq / base)).insert 19 t19).insert 20 t20).insert 21 (t19 ||| t20)
      have hx11 : execList ρ₉ mem ctx
          [.assign 17 (.bin .mul .w64 (.v 5) (.v 5)), .assign 18 (.bin .udiv .w64 (.v 17) (.v 5)),
            .assign 19 (.test .ne .w64 (.v 18) (.v 5)),
            .assign 20 (.test .slt .w64 (.v 17) (.imm (UInt64.ofNat 0))),
            .assign 21 (.bin .or .w64 (.v 19) (.v 20))] = some (ρ₁₁, mem) := by
        simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₉, ρ₇, h5, hbase0, holds_slt_zero]
        simp [ρ₁₁, t19, t20, sq]
        rfl
      have hstar11 := stmts_at (p := p) (ctx := ctx) (rest := rest) (pre := []) (post := []) hf natPow_b11 rfl
        (by simp [Stmt.isCall]) hx11
      by_cases h21 : t19 ||| t20 = 0
      · obtain ⟨hsq, hsqlt⟩ := square_flag.1 h21
        have hsqN : sq.toNat = Bs * Bs := by rw [checked_mul (by omega) hsq hsqlt, hB]
        have hs11 := br_at (p := p) (mem := mem) (ctx := ctx) (rest := rest) (pos := 5) (ρ := ρ₁₁)
          (e := ⟨13, []⟩) (va := t19 ||| t20) (vb := UInt64.ofNat 0) (vals := []) (ρ' := ρ₁₁)
          hf natPow_b11 rfl rfl (by simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₁₁])
          rfl (by simp only [lir_eval, h21]; simp) rfl natPow_b13 rfl
        let ρ₁₃ := ((ρ₁₁.insert 4 acc').insert 5 sq).insert 6 half
        have hs13 := jump_at (p := p) (mem := mem) (ctx := ctx) (rest := rest) (pos := 0) (ρ := ρ₁₁)
          (e := ⟨7, [.v 14, .v 17, .v 15]⟩) (vals := [acc', sq, half]) (ρ' := ρ₁₃) hf natPow_b13 rfl rfl
          (by simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₁₁, ρ₉]) natPow_b7
          (by simp (config := { decide := true }) only [lir_eval]; rfl)
        have hpre := hstar7.trans ((star_of_step hs7).trans (hstar9.trans ((star_of_step hs9).trans
          (hstar11.trans ((star_of_step hs11).trans (star_of_step hs13))))))
        obtain ⟨hacc'N, hacc'lt⟩ := hacc'
        have hA'1 : 1 ≤ acc'.toNat := by
          rw [hacc'N]; split
          · exact Nat.le_trans hA1 (Nat.le_mul_of_pos_right A (by omega))
          · exact hA1
        rcases ih (N / 2) (by omega) acc'.toNat (Bs * Bs) ρ₁₃ acc' sq half rfl hsqN hhalf hA'1 hacc'lt
            (by have := Nat.mul_le_mul hB1 hB1; omega) (by omega) (by omega)
            (by simp (config := { decide := true }) only [ρ₁₃, env_insert_get, ↓reduceIte]) (by simp (config := { decide := true }) only [ρ₁₃, env_insert_get, ↓reduceIte]) (by simp (config := { decide := true }) only [ρ₁₃, env_insert_get, ↓reduceIte])
          with ⟨c, ρ', w, hrun, hw16, hw⟩ | hfail
        · left
          refine ⟨_, ρ', w, hpre.trans hrun, hw16, ?_⟩
          rw [pow_round, ← hacc'N]
          exact hw
        · exact .inr (fails_prepend hpre hfail)
      · have hs11 := br_at (p := p) (mem := mem) (ctx := ctx) (rest := rest) (pos := 5) (ρ := ρ₁₁)
          (e := ⟨12, []⟩) (va := t19 ||| t20) (vb := UInt64.ofNat 0) (vals := []) (ρ' := ρ₁₁)
          hf natPow_b11 rfl rfl (by simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₁₁])
          rfl (by simp only [lir_eval]; simp [h21]) rfl natPow_b12 rfl
        have hfail := fail_at (p := p) (mem := mem) (ctx := ctx) (rest := rest) (pos := 0) (ρ := ρ₁₁)
          hf natPow_b12 rfl rfl
        right
        exact fails_of_star (hstar7.trans ((star_of_step hs7).trans (hstar9.trans ((star_of_step hs9).trans
          (hstar11.trans (star_of_step hs11)))))) hfail
  · -- the product is needed and overflows: block 8 fails
    have hs7 := br_at (p := p) (mem := mem) (ctx := ctx) (rest := rest) (pos := 7) (ρ := ρ₇)
      (e := ⟨8, []⟩) (va := (t10 ||| t11) &&& bit) (vb := UInt64.ofNat 0) (vals := []) (ρ' := ρ₇)
      hf natPow_b7 rfl rfl (by simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₇])
      rfl (by simp only [lir_eval]; simp [ht13]) rfl natPow_b8 rfl
    have hfail := fail_at (p := p) (mem := mem) (ctx := ctx) (rest := rest) (pos := 0) (ρ := ρ₇)
      hf natPow_b8 rfl rfl
    right
    exact fails_of_star (hstar7.trans (star_of_step hs7)) hfail

/-- What a procedure call computes: from its entry, the callee reaches a
`ret` of one argument whose word is `w`. -/
def ProcReturns (p : Program) (g : FunId) (F : Func) (s : State) (mem : X86.Memory) (ctx : Word)
    (rest : List Frame) (good : Word → Prop) : Prop :=
  ∃ c L B a ρ' w, F.blocks[L]? = some B ∧ B.term = .ret [a] ∧
    Sem.Star (semStep p) s c (atState mem ctx g L B.body.size ρ' rest) ∧ evalArgs ρ' [a] = some [w] ∧ good w

/-- `rt_nat_pow` from its entry with the words of `x` and `y` returns the
word of `x ^ y`, or fails with `natOverflow`. -/
theorem natPow_spec {g : FunId} (hf : p.funcs[g]? = some natPow) {rest : List Frame} {x y : Nat}
    {wx wy : Word} (hx : natWord x = some wx) (hy : natWord y = some wy) :
    ProcReturns p g natPow (atState mem ctx g 0 0 ((({} : Env).insert 0 wx).insert 1 wy) rest) mem ctx rest
        (fun w => natWord (x ^ y) = some w) ∨
      Sem.Fails (semStep p) (atState mem ctx g 0 0 ((({} : Env).insert 0 wx).insert 1 wy) rest) := by
  let ρ₀ : Env := (({} : Env).insert 0 wx).insert 1 wy
  have hxN := untag_toNat hx
  have hyN := untag_toNat hy
  let ρ₁ := (ρ₀.insert 2 (wx >>> 1)).insert 3 (wy >>> 1)
  have hx0 : execList ρ₀ mem ctx
      [.assign 2 (.bin .shr .w64 (.v 0) (.imm (UInt64.ofNat 1))),
        .assign 3 (.bin .shr .w64 (.v 1) (.imm (UInt64.ofNat 1)))] = some (ρ₁, mem) := by
    simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₀]
    rfl
  have hstar0 := stmts_at (p := p) (ctx := ctx) (rest := rest) (pre := []) (post := []) hf natPow_b0 rfl
    (by simp [Stmt.isCall]) hx0
  by_cases hy0 : y = 0
  · -- `x ^ 0 = 1`
    subst hy0
    have hz : wy >>> 1 = 0 := UInt64.toNat_inj.mp (by rw [hyN]; rfl)
    have hs0 := br_at (p := p) (mem := mem) (ctx := ctx) (rest := rest) (pos := 2) (ρ := ρ₁)
      (e := ⟨1, []⟩) (va := wy >>> 1) (vb := UInt64.ofNat 0) (vals := []) (ρ' := ρ₁)
      hf natPow_b0 rfl rfl (by simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₁])
      rfl (by simp only [lir_eval, hz]; simp) rfl natPow_b1 rfl
    left
    refine ⟨_, 1, _, _, ρ₁, UInt64.ofNat 3, natPow_b1, rfl, (hstar0.trans (star_of_step hs0)),
      by simp only [lir_eval], ?_⟩
    simp only [Nat.pow_zero]
    exact natWord_of_lt (by decide)
  · have hnz : wy >>> 1 ≠ 0 := fun h => hy0 (by rw [← hyN, h]; rfl)
    have hs0 := br_at (p := p) (mem := mem) (ctx := ctx) (rest := rest) (pos := 2) (ρ := ρ₁)
      (e := ⟨2, []⟩) (va := wy >>> 1) (vb := UInt64.ofNat 0) (vals := []) (ρ' := ρ₁)
      hf natPow_b0 rfl rfl (by simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₁])
      rfl (by simp only [lir_eval]; simp [hnz]) rfl natPow_b2 rfl
    by_cases hx1 : x ≤ 1
    · -- `0 ^ y = 0`, `1 ^ y = 1`
      have hle : wx >>> 1 ≤ 1 := by
        rw [UInt64.le_iff_toNat_le, hxN]; simpa using hx1
      have hs2 := br_at (p := p) (mem := mem) (ctx := ctx) (rest := rest) (pos := 0) (ρ := ρ₁)
        (e := ⟨3, []⟩) (va := wx >>> 1) (vb := UInt64.ofNat 1) (vals := []) (ρ' := ρ₁)
        hf natPow_b2 rfl rfl (by simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₁])
        rfl (by simp only [lir_eval]; simp [hle]) rfl natPow_b3 rfl
      left
      refine ⟨_, 3, _, _, ρ₁, wx, natPow_b3, rfl, (hstar0.trans ((star_of_step hs0).trans (star_of_step hs2))),
        by simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₁, ρ₀], ?_⟩
      have : x ^ y = x := by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hx1 with rfl | rfl
        · exact Nat.zero_pow (by omega)
        · exact Nat.one_pow y
      rw [this]; exact hx
    · have hgt : (1 : Word) < wx >>> (1 : Word) := by
        rw [UInt64.lt_iff_toNat_lt, hxN]; simp; omega
      have hs2 := br_at (p := p) (mem := mem) (ctx := ctx) (rest := rest) (pos := 0) (ρ := ρ₁)
        (e := ⟨4, []⟩) (va := wx >>> 1) (vb := UInt64.ofNat 1) (vals := []) (ρ' := ρ₁)
        hf natPow_b2 rfl rfl (by simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₁])
        rfl (by simp only [lir_eval]; simp [hgt]) rfl natPow_b4 rfl
      by_cases hy62 : 62 < y
      · -- `x ≥ 2` and `y > 62` overflow
        have hlt : (62 : Word) < wy >>> (1 : Word) := by
          rw [UInt64.lt_iff_toNat_lt, hyN]; simpa using hy62
        have hs4 := br_at (p := p) (mem := mem) (ctx := ctx) (rest := rest) (pos := 0) (ρ := ρ₁)
          (e := ⟨5, []⟩) (va := wy >>> 1) (vb := UInt64.ofNat 62) (vals := []) (ρ' := ρ₁)
          hf natPow_b4 rfl rfl (by simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₁])
          rfl (by simp only [lir_eval]; simp [hlt]) rfl natPow_b5 rfl
        right
        exact fails_of_star (hstar0.trans ((star_of_step hs0).trans ((star_of_step hs2).trans
          (star_of_step hs4)))) (fail_at (p := p) (mem := mem) (ctx := ctx) (rest := rest) (pos := 0) (ρ := ρ₁)
            hf natPow_b5 rfl rfl)
      · have hnlt : wy >>> (1 : Word) ≤ (62 : Word) := by
          rw [UInt64.le_iff_toNat_le, hyN]; simp; omega
        have hs4 := br_at (p := p) (mem := mem) (ctx := ctx) (rest := rest) (pos := 0) (ρ := ρ₁)
          (e := ⟨6, []⟩) (va := wy >>> 1) (vb := UInt64.ofNat 62) (vals := []) (ρ' := ρ₁)
          hf natPow_b4 rfl rfl (by simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₁])
          rfl (by simp only [lir_eval]; simp [hnlt]) rfl natPow_b6 rfl
        let ρ₆ := ((ρ₁.insert 4 (UInt64.ofNat 1)).insert 5 (wx >>> 1)).insert 6 (wy >>> 1)
        have hs6 := jump_at (p := p) (mem := mem) (ctx := ctx) (rest := rest) (pos := 0) (ρ := ρ₁)
          (e := ⟨7, [.imm (UInt64.ofNat 1), .v 2, .v 3]⟩) (vals := [UInt64.ofNat 1, wx >>> 1, wy >>> 1])
          (ρ' := ρ₆) hf natPow_b6 rfl rfl
          (by simp (config := { decide := true }) only [lir_eval, ↓reduceIte, ρ₁]) natPow_b7
          (by simp (config := { decide := true }) only [lir_eval]; rfl)
        have hpre := hstar0.trans ((star_of_step hs0).trans ((star_of_step hs2).trans
          ((star_of_step hs4).trans (star_of_step hs6))))
        rcases natPow_loop (mem := mem) (ctx := ctx) hf y 1 x ρ₆ (UInt64.ofNat 1) (wx >>> 1) (wy >>> 1) rfl hxN hyN
            (Nat.le_refl 1) (by decide) (by omega) (natWord_lt hx) (by omega)
            (by simp (config := { decide := true }) only [ρ₆, env_insert_get, ↓reduceIte])
            (by simp (config := { decide := true }) only [ρ₆, env_insert_get, ↓reduceIte])
            (by simp (config := { decide := true }) only [ρ₆, env_insert_get, ↓reduceIte])
          with ⟨c, ρ', w, hrun, hw16, hw⟩ | hfail
        · left
          refine ⟨_, 10, _, _, ρ', w, natPow_b10, rfl, hpre.trans hrun, by simp only [lir_eval, hw16], ?_⟩
          simpa using hw
        · exact .inr (fails_prepend hpre hfail)

/-- `rt_nat_gcd` in the shape of `ProcReturns`. -/
theorem natGcd_returns {g : FunId} (hf : p.funcs[g]? = some natGcd) {rest : List Frame} {x y : Nat}
    {wx wy : Word} (hx : natWord x = some wx) (hy : natWord y = some wy) :
    ProcReturns p g natGcd (atState mem ctx g 0 0 ((({} : Env).insert 0 wx).insert 1 wy) rest) mem ctx rest
      (fun w => natWord (Nat.gcd x y) = some w) := by
  obtain ⟨c, ρ', w, hrun, hw2, hw⟩ := natGcd_spec (mem := mem) (ctx := ctx) (rest := rest) hf hx hy
  exact ⟨c, 2, _, _, ρ', w, natGcd_b2, rfl, hrun, by simp only [lir_eval, hw2], hw⟩

end IxCC.Rt.Proof
