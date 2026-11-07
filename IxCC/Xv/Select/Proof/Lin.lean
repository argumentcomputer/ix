import IxCC.Xv.Select.Proof.Words
import IxCC.Lir.Proof.Eval

/-!
# Address sums

Selection builds addresses as sums of scaled registers and a displacement
(`Select.Lin`), folds single-use address arithmetic into them, and encodes
them as `[base + index·scale + disp32]` (`Lin.encode`). This module gives a
sum its value in a Lir environment (`linVal`) and proves each step exact:
a Lir address is its sum's value, folding a statement whose register holds
its right-hand side's value keeps the value, and an encoded addressing
mode evaluates (`Amode.evalV`) to the sum's value.
-/

namespace IxCC.Xv.Select.Proof

open IxCC.Lir (VReg Word Env)
open IxCC.Xv.Select (Lin)

/-! ## Values -/

/-- A term's value: its multiplier times its register's value. -/
def termVal (ρ : Env) (ctx : Word) : Base VReg × Nat → Option Word
  | (.r x, m) => (UInt64.ofNat m * ·) <$> ρ[x]?
  | (.ctx, m) => some (UInt64.ofNat m * ctx)

def termsVal (ρ : Env) (ctx : Word) : List (Base VReg × Nat) → Option Word
  | [] => some 0
  | t :: ts => do
      let v ← termVal ρ ctx t
      let s ← termsVal ρ ctx ts
      some (v + s)

/-- A sum's value, modulo 2^64. -/
def linVal (ρ : Env) (ctx : Word) (l : Lin) : Option Word :=
  (termsVal ρ ctx l.terms).map (· + Lir.dispWord l.disp)

theorem termsVal_append (ρ : Env) (ctx : Word) :
    ∀ (a b : List (Base VReg × Nat)), termsVal ρ ctx (a ++ b) =
      (termsVal ρ ctx a).bind fun sa => (termsVal ρ ctx b).map (sa + ·)
  | [], b => by cases h : termsVal ρ ctx b <;> simp [termsVal, h]
  | t :: a, b => by
      simp only [List.cons_append, termsVal, termsVal_append ρ ctx a b]
      cases termVal ρ ctx t <;> cases termsVal ρ ctx a <;> cases termsVal ρ ctx b <;>
        simp [UInt64.add_assoc]

theorem termVal_scale (ρ : Env) (ctx : Word) (c : Nat) (t : Base VReg × Nat) :
    termVal ρ ctx (t.1, c * t.2) = (UInt64.ofNat c * ·) <$> termVal ρ ctx t := by
  obtain ⟨b, m⟩ := t
  cases b <;> simp [termVal]
  · cases ρ[‹VReg›]? <;> simp [UInt64.ofNat_mul, UInt64.mul_assoc]
  · simp [UInt64.ofNat_mul, UInt64.mul_assoc]

theorem termsVal_scale (ρ : Env) (ctx : Word) (c : Nat) :
    ∀ (ts : List (Base VReg × Nat)), termsVal ρ ctx (ts.map fun (t, m) => (t, c * m)) =
      (UInt64.ofNat c * ·) <$> termsVal ρ ctx ts
  | [] => by simp [termsVal]
  | t :: ts => by
      simp only [List.map_cons, termsVal]
      rw [show (t.1, c * t.2) = ((t.1, c * t.2) : Base VReg × Nat) from rfl, termVal_scale,
        termsVal_scale ρ ctx c ts]
      cases termVal ρ ctx t <;> cases termsVal ρ ctx ts <;> simp [UInt64.mul_add]

theorem dispWord_add (a b : Int) : Lir.dispWord (a + b) = Lir.dispWord a + Lir.dispWord b := by
  apply UInt64.toBitVec_inj.mp
  simp [Lir.dispWord, BitVec.ofInt_add]

theorem dispWord_mul (c : Nat) (a : Int) : Lir.dispWord (c * a) = UInt64.ofNat c * Lir.dispWord a := by
  apply UInt64.toBitVec_inj.mp
  simp [Lir.dispWord, BitVec.ofInt_mul]
  rfl

theorem dispWord_negWord (k : Word) : Lir.dispWord (-(k.toNat : Int)) = 0 - k := by
  apply UInt64.toNat_inj.mp
  simp only [Lir.dispWord, UInt64.toNat_ofBitVec, BitVec.toNat_ofInt, UInt64.toNat_sub]
  have h0 : (UInt64.toNat 0) = 0 := rfl
  have := k.toNat_lt_size
  simp only [UInt64.size] at this
  rw [h0]
  omega

theorem linVal_add (ρ : Env) (ctx : Word) (a b : Lin) :
    linVal ρ ctx (a.add b) = (linVal ρ ctx a).bind fun va => (linVal ρ ctx b).map (va + ·) := by
  simp only [linVal, Lin.add, termsVal_append, dispWord_add]
  cases termsVal ρ ctx a.terms <;> cases termsVal ρ ctx b.terms <;> simp
  ac_rfl

theorem linVal_scale (ρ : Env) (ctx : Word) (c : Nat) (a : Lin) :
    linVal ρ ctx (a.scale c) = (UInt64.ofNat c * ·) <$> linVal ρ ctx a := by
  simp only [linVal, Lin.scale, termsVal_scale, dispWord_mul]
  cases termsVal ρ ctx a.terms <;> simp [UInt64.mul_add]

theorem linVal_ofArg (ρ : Env) (ctx : Word) (a : Lir.Arg) : linVal ρ ctx (Lin.ofArg a) = a.eval ρ := by
  cases a with
  | v x => cases h : ρ[x]? <;> simp [linVal, Lin.ofArg, termsVal, termVal, Lir.Arg.eval, h, Lir.dispWord_zero]
  | imm k => simp [linVal, Lin.ofArg, termsVal, Lir.Arg.eval, Lir.dispWord_ofNat]

theorem linVal_ofAddr (ρ : Env) (ctx : Word) (m : Lir.Addr) : linVal ρ ctx (Lin.ofAddr m) = m.eval ρ ctx := by
  obtain ⟨base, index, disp⟩ := m
  have hs : ∀ s : X86.Scale, UInt64.ofNat s.word.toNat = s.word := fun s => by cases s <;> rfl
  rcases base with _ | (x | _) <;> rcases index with _ | ⟨y, s⟩
  · simp [linVal, Lin.ofAddr, termsVal, Lir.Addr.eval]
  · cases hy : ρ[y]? <;> simp [linVal, Lin.ofAddr, termsVal, termVal, Lir.Addr.eval, hs, hy, UInt64.mul_comm]
  · cases hx : ρ[x]? <;> simp [linVal, Lin.ofAddr, termsVal, termVal, Lir.Addr.eval, hx]
  · cases hx : ρ[x]? <;> cases hy : ρ[y]? <;>
      simp [linVal, Lin.ofAddr, termsVal, termVal, Lir.Addr.eval, hs, hx, hy, UInt64.mul_comm, UInt64.add_assoc]
  · simp [linVal, Lin.ofAddr, termsVal, termVal, Lir.Addr.eval]
  · cases hy : ρ[y]? <;>
      simp [linVal, Lin.ofAddr, termsVal, termVal, Lir.Addr.eval, hs, hy, UInt64.mul_comm, UInt64.add_assoc]

/-! ## Folding -/

theorem shl_mul (a : Word) {n : Nat} (h : n < 64) : a <<< UInt64.ofNat n = UInt64.ofNat (2 ^ n) * a := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_shiftLeft, UInt64.toNat_mul, UInt64.toNat_ofNat', UInt64.toNat_ofNat']
  have h64 : n % 2 ^ 64 % 64 = n := by omega
  rw [h64, Nat.shiftLeft_eq, Nat.mul_comm]
  have : 2 ^ n < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) h
  rw [Nat.mod_eq_of_lt (b := 2 ^ 64) this]

/-- The sum a foldable right-hand side contributes has its value. -/
theorem rhsLin_val {ρ : Env} {mem : X86.Memory} {ctx : Word} {r : Lir.Rhs} {sub : Lin} {v : Word}
    (hl : Select.rhsLin r = some sub) (hv : r.eval ρ mem ctx = some v) : linVal ρ ctx sub = some v := by
  unfold Select.rhsLin at hl
  split at hl <;> (try simp only [Option.some.injEq] at hl) <;> try subst hl
  · simpa [Lir.Rhs.eval, linVal_ofAddr] using hv
  · simpa [Lir.Rhs.eval, linVal_ofArg] using hv
  · rename_i a b
    simp only [Lir.Rhs.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at hv
    obtain ⟨va, ha, vb, hb, he⟩ := hv
    simp [Lir.BinOp.eval, X86.Encode.truncate64] at he
    rw [linVal_add, linVal_ofArg, linVal_ofArg, ha, hb]
    simp [he]
  · rename_i a k
    simp only [Lir.Rhs.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at hv
    obtain ⟨va, ha, vb, hb, he⟩ := hv
    simp [Lir.BinOp.eval, X86.Encode.truncate64, Lir.Arg.eval] at he hb
    subst hb
    rw [linVal_add, linVal_ofArg, ha]
    simp [linVal, termsVal, dispWord_negWord, ← he, UInt64.sub_eq_add_neg]
  · rename_i a s
    split at hl
    · simp only [Option.some.injEq] at hl
      subst hl
      rename_i hs
      simp only [Lir.Rhs.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at hv
      obtain ⟨va, ha, vb, hb, he⟩ := hv
      simp [Lir.Arg.eval] at hb
      subst hb
      simp only [Lir.BinOp.eval, X86.Encode.truncate64, Option.some.injEq] at he
      rw [linVal_scale, linVal_ofArg, ha]
      simp only [Option.map_eq_map, Option.map_some, Option.some.injEq]
      have hlt : (s &&& Lir.shiftMask .w64).toNat < 64 := by omega
      rw [← shl_mul va hlt, ← he, UInt64.ofNat_toNat]
    · cases hl
  · rename_i a k
    split at hl
    · simp only [Option.some.injEq] at hl
      subst hl
      rename_i hk
      simp only [Lir.Rhs.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at hv
      obtain ⟨va, ha, vb, hb, he⟩ := hv
      simp [Lir.Arg.eval] at hb
      subst hb
      simp [Lir.BinOp.eval, X86.Encode.truncate64] at he
      rw [linVal_scale, linVal_ofArg, ha]
      simp [← he, UInt64.mul_comm]
    · cases hl
  · rename_i k a
    split at hl
    · simp only [Option.some.injEq] at hl
      subst hl
      simp only [Lir.Rhs.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at hv
      obtain ⟨va, ha, vb, hb, he⟩ := hv
      simp [Lir.Arg.eval] at ha
      subst ha
      simp [Lir.BinOp.eval, X86.Encode.truncate64] at he
      rw [linVal_scale, linVal_ofArg, hb]
      simp [← he]
    · cases hl
  · cases hl

/-- The terms of a sum other than `t`, and `t`'s multipliers summed. -/
theorem termsVal_split (ρ : Env) (ctx : Word) (t : Base VReg) (vt : Word)
    (ht : termVal ρ ctx (t, 1) = some vt) :
    ∀ (ts : List (Base VReg × Nat)) (s : Word), termsVal ρ ctx ts = some s →
      ∃ s', termsVal ρ ctx (ts.filter (·.1 != t)) = some s' ∧
        s = s' + UInt64.ofNat ((ts.filter (·.1 == t)).map (·.2)).sum * vt
  | [], s, h => by simp [termsVal] at h; subst h; exact ⟨0, by simp [termsVal], by simp⟩
  | (b, m) :: ts, s, h => by
      simp only [termsVal, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨v, hv, s₁, hs₁, he₀⟩ := h
      simp only [Option.some.injEq] at he₀
      subst he₀
      obtain ⟨s', hs', he⟩ := termsVal_split ρ ctx t vt ht ts s₁ hs₁
      by_cases hb : b = t
      · subst hb
        have hvt : v = UInt64.ofNat m * vt := by
          cases b with
          | r x =>
            simp only [termVal, Option.map_eq_map, Option.map_eq_some_iff] at hv ht
            obtain ⟨w, hw, rfl⟩ := hv
            obtain ⟨w', hw', rfl⟩ := ht
            rw [hw] at hw'; cases hw'; simp
          | ctx => simp [termVal] at hv ht; subst hv ht; simp
        refine ⟨s', by simpa using hs', ?_⟩
        simp only [List.filter_cons, beq_self_eq_true, ↓reduceIte, List.map_cons, List.sum_cons, he, hvt]
        simp [UInt64.ofNat_add, UInt64.add_mul]
        ac_rfl
      · have hbn : (b != t) = true := by simpa using hb
        have hbe : (b == t) = false := by simpa using hb
        refine ⟨v + s', ?_, ?_⟩
        · simp [List.filter_cons, hbn, termsVal, hv, hs']
        · simp [List.filter_cons, hbe, he, UInt64.add_assoc]

/-- Folding a statement into a sum keeps its value: the folded register holds
the value of the statement's sum. -/
theorem fold_val {ρ : Env} {ctx : Word} {l sub : Lin} {x : VReg} {vx a : Word}
    (hx : ρ[x]? = some vx) (hsub : linVal ρ ctx sub = some vx) (hl : linVal ρ ctx l = some a) :
    linVal ρ ctx (({ l with terms := l.terms.filter (·.1 != .r x) } : Lin).add
      (sub.scale ((l.terms.filter (·.1 == .r x)).map (·.2)).sum)) = some a := by
  have ht : termVal ρ ctx (.r x, 1) = some vx := by simp [termVal, hx]
  simp only [linVal, Option.map_eq_some_iff] at hl
  obtain ⟨s, hs, rfl⟩ := hl
  obtain ⟨s', hs', he⟩ := termsVal_split ρ ctx (.r x) vx ht l.terms s hs
  rw [linVal_add, linVal_scale, hsub]
  simp [linVal, hs', he]
  ac_rfl


/-! ## Encoding -/

theorem termsVal_filter_nonzero (ρ : Env) (ctx : Word) :
    ∀ (ts : List (Base VReg × Nat)) (s : Word), termsVal ρ ctx ts = some s →
      termsVal ρ ctx (ts.filter fun (_, m) => m % 2 ^ 64 != 0) = some s
  | [], s, h => h
  | (b, m) :: ts, s, h => by
      simp only [termsVal, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨v, hv, s₁, hs₁, he⟩ := h
      simp only [Option.some.injEq] at he
      subst he
      have ih := termsVal_filter_nonzero ρ ctx ts s₁ hs₁
      by_cases hm : m % 2 ^ 64 = 0
      · have hz : UInt64.ofNat m = 0 := by
          apply UInt64.toNat_inj.mp; simp [UInt64.toNat_ofNat', hm]
        have hv0 : v = 0 := by
          cases b <;> simp [termVal, hz] at hv
          · obtain ⟨w, -, rfl⟩ := hv; rfl
          · exact hv.symm
        simp [List.filter_cons, hm, ih, hv0]
      · simp [List.filter_cons, hm, termsVal, hv, ih]

theorem dispWord_signed64 (d : Int) : Lir.dispWord (Select.signed64 d) = Lir.dispWord d := by
  apply UInt64.toNat_inj.mp
  simp only [Lir.dispWord, UInt64.toNat_ofBitVec, BitVec.toNat_ofInt, Select.signed64]
  split <;> omega

theorem disp32_eq {d : Int} (h : -2147483648 ≤ Select.signed64 d ∧ Select.signed64 d < 2147483648) :
    X86.signExtend32 (Int32.ofInt (Select.signed64 d)).toUInt32 = Lir.dispWord d := by
  rw [← dispWord_signed64]
  apply UInt64.toBitVec_inj.mp
  rw [X86.Encode.signExtend32_ofInt_of_bounds _ (by omega) (by omega)]
  rfl

theorem scaleOf_word {m : Nat} {s : X86.Scale} (h : Select.scaleOf m = some s) : s.word = UInt64.ofNat m := by
  unfold Select.scaleOf at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;> rfl

theorem termVal_r {ρ : Env} {ctx : Word} {x : VReg} {m : Nat} {v : Word} (h : termVal ρ ctx (.r x, m) = some v) :
    ∃ w, ρ[x]? = some w ∧ v = UInt64.ofNat m * w := by
  simp only [termVal, Option.map_eq_map, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, rfl⟩ := h
  exact ⟨w, hw, rfl⟩

theorem baseVal_eq {ρ : Env} {ctx : Word} {b : Base VReg} {v : Word} (h : termVal ρ ctx (b, 1) = some v) :
    (match b with | .ctx => some ctx | .r x => ρ[x]?) = some v := by
  cases b with
  | r x => obtain ⟨w, hw, rfl⟩ := termVal_r h; simp [hw]
  | ctx => simp [termVal] at h; simp [h]

theorem regIndex_eq {ρ : Env} {ctx : Word} {t : Base VReg × Nat} {x : VReg} {s : X86.Scale} {v : Word}
    (hr : (match t with
      | (.r x, m) => (x, ·) <$> Select.scaleOf (m % 2 ^ 64)
      | (.ctx, _) => none) = some (x, s))
    (ht : termVal ρ ctx t = some v) : (· * s.word) <$> ρ[x]? = some v := by
  obtain ⟨b, m⟩ := t
  cases b with
  | ctx => simp at hr
  | r y =>
    simp only [Option.map_eq_map, Option.map_eq_some_iff, Prod.mk.injEq] at hr
    obtain ⟨s', hs', rfl, rfl⟩ := hr
    obtain ⟨w, hw, rfl⟩ := termVal_r ht
    simp [hw, scaleOf_word hs', UInt64.mul_comm]
    apply UInt64.toNat_inj.mp; simp

theorem evalV_base_index {ρ : Env} {ctx : Word} {b : Base VReg} {x : VReg} {sc : X86.Scale} {d : Int32}
    {vb vi : Word} (hb : termVal ρ ctx (b, 1) = some vb) (hi : ρ[x]? = some vi) :
    Amode.evalV ρ ctx { base := some b, index := some (x, sc), disp := d } =
      some (vb + vi * sc.word + X86.signExtend32 d.toUInt32) := by
  cases b with
  | r y => obtain ⟨w, hw, rfl⟩ := termVal_r hb; simp [Amode.evalV, hw, hi]
  | ctx => simp [termVal] at hb; subst hb; simp [Amode.evalV, hi]

/-- An encoded addressing mode evaluates to its sum's value. -/
theorem encodeTerms_val {ρ : Env} {ctx : Word} {terms : List (Base VReg × Nat)} {disp : Int} {am : Amode VReg}
    {s : Word} (h : Select.encodeTerms terms disp = some am) (hs : termsVal ρ ctx terms = some s) :
    am.evalV ρ ctx = some (s + Lir.dispWord disp) := by
  unfold Select.encodeTerms at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, hg, h⟩ := h
  have hrange : -2147483648 ≤ Select.signed64 disp ∧ Select.signed64 disp < 2147483648 := by
    by_cases hn : -2147483648 ≤ Select.signed64 disp ∧ Select.signed64 disp < 2147483648
    · exact hn
    · simp [guard, hn, failure] at hg
  have hd := disp32_eq hrange
  have hf := termsVal_filter_nonzero ρ ctx terms s hs
  generalize terms.filter (fun (_, m) => m % 2 ^ 64 != 0) = ts at h hf
  split at h
  · simp only [Option.some.injEq] at h; subst h
    simp [termsVal] at hf; subst hf
    simp [Amode.evalV, hd]
  · simp only [Option.some.injEq] at h; subst h
    rename_i b
    simp only [termsVal, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hf
    obtain ⟨v, hv, _, rfl, he⟩ := hf
    simp only [UInt64.add_zero] at he; subst he
    have := baseVal_eq hv
    cases b <;> simp_all [Amode.evalV, hd]
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨⟨x, sc⟩, hr, rfl⟩ := h
    rename_i t _
    simp only [termsVal, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hf
    obtain ⟨v, hv, _, rfl, he⟩ := hf
    simp only [UInt64.add_zero] at he; subst he
    have hi := regIndex_eq hr hv
    simp only [Option.map_eq_map, Option.map_eq_some_iff] at hi
    obtain ⟨vi, hvi, rfl⟩ := hi
    simp [Amode.evalV, hvi, hd]
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨⟨x, sc⟩, hr, rfl⟩ := h
    simp only [termsVal, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hf
    obtain ⟨v₁, hv₁, _, ⟨v₂, hv₂, _, rfl, rfl⟩, he⟩ := hf
    simp only [UInt64.add_zero] at he; subst he
    have hi := regIndex_eq hr hv₂
    simp only [Option.map_eq_map, Option.map_eq_some_iff] at hi
    obtain ⟨vi, hvi, rfl⟩ := hi
    rw [evalV_base_index hv₁ hvi, hd]
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨⟨x, sc⟩, hr, rfl⟩ := h
    simp only [termsVal, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hf
    obtain ⟨v₁, hv₁, _, ⟨v₂, hv₂, _, rfl, rfl⟩, he⟩ := hf
    simp only [UInt64.add_zero] at he; subst he
    have hi := regIndex_eq hr hv₁
    simp only [Option.map_eq_map, Option.map_eq_some_iff] at hi
    obtain ⟨vi, hvi, rfl⟩ := hi
    rw [evalV_base_index hv₂ hvi, hd, UInt64.add_comm (vi * sc.word) v₂]
  · cases h


/-! ## Merging equal registers -/

/-- One step of `mergeTerms`. -/
def mergeStep (acc : List (Base VReg × Nat)) (p : Base VReg × Nat) : List (Base VReg × Nat) :=
  match acc.find? (·.1 == p.1) with
  | some _ => acc.map fun (u, n) => if u == p.1 then (u, n + p.2) else (u, n)
  | none => acc ++ [(p.1, p.2)]

theorem mergeTerms_eq (ts : List (Base VReg × Nat)) : Select.mergeTerms ts = ts.foldl mergeStep [] := by
  unfold Select.mergeTerms
  congr

theorem termVal_add_mult {ρ : Env} {ctx : Word} {t : Base VReg} {n m : Nat} {v u : Word}
    (hn : termVal ρ ctx (t, n) = some v) (hm : termVal ρ ctx (t, m) = some u) :
    termVal ρ ctx (t, n + m) = some (v + u) := by
  cases t with
  | r x =>
    obtain ⟨w, hw, rfl⟩ := termVal_r hn
    obtain ⟨w', hw', rfl⟩ := termVal_r hm
    rw [hw] at hw'; cases hw'
    simp [termVal, hw, UInt64.ofNat_add, UInt64.add_mul]
  | ctx =>
    simp [termVal] at hn hm ⊢; subst hn hm
    simp [UInt64.ofNat_add, UInt64.add_mul]

theorem termVal_mult {ρ : Env} {ctx : Word} {t : Base VReg} {n m : Nat} {v : Word}
    (hn : termVal ρ ctx (t, n) = some v) : ∃ u, termVal ρ ctx (t, m) = some u := by
  cases t with
  | r x => obtain ⟨w, hw, rfl⟩ := termVal_r hn; exact ⟨UInt64.ofNat m * w, by simp [termVal, hw]⟩
  | ctx => exact ⟨_, rfl⟩

theorem termsVal_map_add (ρ : Env) (ctx : Word) (t : Base VReg) (m : Nat) (u : Word)
    (hu : termVal ρ ctx (t, m) = some u) :
    ∀ (acc : List (Base VReg × Nat)) (a : Word), (acc.map (·.1)).Nodup → t ∈ acc.map (·.1) →
      termsVal ρ ctx acc = some a →
      termsVal ρ ctx (acc.map fun (b, n) => if b == t then (b, n + m) else (b, n)) = some (a + u)
  | [], _, _, ht, _ => by simp at ht
  | (b, n) :: acc, a, hnd, ht, h => by
      simp only [List.map_cons, List.nodup_cons] at hnd
      simp only [termsVal, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨v, hv, s, hs, rfl⟩ := h
      by_cases hb : b = t
      · subst hb
        have hrest : (acc.map fun (b', n) => if b' == b then (b', n + m) else (b', n)) = acc := by
          rw [List.map_congr_left (g := id) ?_, List.map_id]
          intro p hp
          have : p.1 ≠ b := fun e => hnd.1 (e ▸ List.mem_map_of_mem hp)
          obtain ⟨p1, p2⟩ := p
          simp only at this
          simp [this]
        rw [List.map_cons, hrest]
        dsimp only
        rw [if_pos (by simp)]
        simp only [termsVal, termVal_add_mult hv hu, hs, Option.bind_eq_bind, Option.bind_some]
        simp; ac_rfl
      · have ht' : t ∈ acc.map (·.1) := by
          simp only [List.map_cons, List.mem_cons] at ht
          rcases ht with ht | ht
          · exact absurd ht.symm hb
          · exact ht
        have hbt : (b == t) = false := by simpa using hb
        rw [List.map_cons]
        dsimp only
        rw [if_neg (by simp [hbt])]
        simp only [termsVal, hv, termsVal_map_add ρ ctx t m u hu acc s hnd.2 ht' hs, Option.bind_eq_bind,
          Option.bind_some]
        simp [UInt64.add_assoc]

theorem mergeStep_val {ρ : Env} {ctx : Word} {acc : List (Base VReg × Nat)} {p : Base VReg × Nat} {a v : Word}
    (hnd : (acc.map (·.1)).Nodup) (ha : termsVal ρ ctx acc = some a) (hv : termVal ρ ctx p = some v) :
    termsVal ρ ctx (mergeStep acc p) = some (a + v) ∧ ((mergeStep acc p).map (·.1)).Nodup := by
  obtain ⟨t, m⟩ := p
  unfold mergeStep
  split
  · rename_i q hq
    have hmem : t ∈ acc.map (·.1) := by
      have := List.mem_of_find?_eq_some hq
      have he : q.1 = t := by simpa using List.find?_some hq
      exact he ▸ List.mem_map_of_mem this
    refine ⟨termsVal_map_add ρ ctx t m v hv acc a hnd hmem ha, ?_⟩
    have : ((acc.map fun (b, n) => if b == t then (b, n + m) else (b, n)).map (·.1)) = acc.map (·.1) := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro p _
      simp only [Function.comp]
      split <;> rfl
    rw [this]; exact hnd
  · rename_i hq
    refine ⟨?_, ?_⟩
    · rw [termsVal_append, ha]
      simp [termsVal, hv]
    · simp only [List.map_append, List.map_cons, List.map_nil]
      rw [List.nodup_append]
      refine ⟨hnd, by simp, ?_⟩
      intro x hx y hy e
      simp at hy
      subst hy; subst e
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
      have := List.find?_eq_none.1 hq p hp
      simp at this

theorem foldl_merge_val {ρ : Env} {ctx : Word} :
    ∀ (ts acc : List (Base VReg × Nat)) (a s : Word), (acc.map (·.1)).Nodup → termsVal ρ ctx acc = some a →
      termsVal ρ ctx ts = some s → termsVal ρ ctx (ts.foldl mergeStep acc) = some (a + s)
  | [], acc, a, s, _, ha, hs => by simp [termsVal] at hs; subst hs; simpa using ha
  | p :: ts, acc, a, s, hnd, ha, hs => by
      simp only [termsVal, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hs
      obtain ⟨v, hv, s', hs', rfl⟩ := hs
      obtain ⟨h₁, h₂⟩ := mergeStep_val hnd ha hv
      rw [List.foldl_cons, foldl_merge_val ts _ _ _ h₂ h₁ hs', UInt64.add_assoc]

theorem mergeTerms_val {ρ : Env} {ctx : Word} {ts : List (Base VReg × Nat)} {s : Word}
    (hs : termsVal ρ ctx ts = some s) : termsVal ρ ctx (Select.mergeTerms ts) = some s := by
  rw [mergeTerms_eq]
  have := foldl_merge_val ts [] 0 s (by simp) (by simp [termsVal]) hs
  simpa using this

/-- An encoded sum's addressing mode evaluates to the sum's value. -/
theorem encode_val {ρ : Env} {ctx : Word} {l : Lin} {am : Amode VReg} {a : Word}
    (h : l.encode = some am) (hl : linVal ρ ctx l = some a) : am.evalV ρ ctx = some a := by
  simp only [linVal, Option.map_eq_some_iff] at hl
  obtain ⟨s, hs, rfl⟩ := hl
  unfold Lin.encode at h
  cases h₁ : Select.encodeTerms l.terms l.disp with
  | some am' =>
    rw [h₁] at h
    simp only [Option.orElse_eq_orElse, Option.orElse_some, Option.some.injEq] at h
    subst h
    exact encodeTerms_val h₁ hs
  | none =>
    rw [h₁] at h
    simp only [Option.orElse_eq_orElse, Option.orElse_none] at h
    exact encodeTerms_val h (mergeTerms_val hs)


/-! ## Registers -/

/-- Every register a sum names is below `N`. -/
def LinLow (N : Nat) (l : Lin) : Prop := ∀ t ∈ l.terms, ∀ x, t.1 = .r x → x < N

theorem linLow_add {N : Nat} {a b : Lin} (ha : LinLow N a) (hb : LinLow N b) : LinLow N (a.add b) := by
  intro t ht x hx
  simp only [Lin.add, List.mem_append] at ht
  rcases ht with ht | ht
  · exact ha t ht x hx
  · exact hb t ht x hx

theorem linLow_scale {N : Nat} {a : Lin} (c : Nat) (ha : LinLow N a) : LinLow N (a.scale c) := by
  intro t ht x hx
  simp only [Lin.scale, List.mem_map] at ht
  obtain ⟨p, hp, rfl⟩ := ht
  exact ha p hp x hx

theorem linLow_ofArg {N : Nat} {a : Lir.Arg} (h : ∀ u ∈ a.uses, u < N) : LinLow N (Lin.ofArg a) := by
  intro t ht x hx
  cases a with
  | v y => simp [Lin.ofArg] at ht; subst ht; simp at hx; subst hx; exact h y (by simp [Lir.Arg.uses, Lir.Arg.vreg?])
  | imm k => simp [Lin.ofArg] at ht

theorem linLow_ofAddr {N : Nat} {m : Lir.Addr} (h : ∀ u ∈ m.uses, u < N) : LinLow N (Lin.ofAddr m) := by
  intro t ht x hx
  obtain ⟨base, index, disp⟩ := m
  rcases base with _ | (y | _) <;> rcases index with _ | ⟨z, s⟩ <;>
    simp [Lin.ofAddr] at ht <;> (try rcases ht with rfl | rfl) <;> (try subst ht) <;> simp at hx <;>
    subst hx <;> exact h _ (by simp [Lir.Addr.uses, Lir.Base.uses])

theorem linLow_rhsLin {N : Nat} {r : Lir.Rhs} {sub : Lin} (hl : Select.rhsLin r = some sub)
    (h : ∀ u ∈ r.uses, u < N) : LinLow N sub := by
  unfold Select.rhsLin at hl
  split at hl <;> (try simp only [Option.some.injEq] at hl) <;> (try subst hl)
  · exact linLow_ofAddr (by simpa [Lir.Rhs.uses] using h)
  · exact linLow_ofArg (by simpa [Lir.Rhs.uses] using h)
  · exact linLow_add (linLow_ofArg fun u hu => h u (by simp only [Lir.Rhs.uses, List.mem_append]; first | exact .inl hu | exact .inr hu))
      (linLow_ofArg fun u hu => h u (by simp only [Lir.Rhs.uses, List.mem_append]; first | exact .inl hu | exact .inr hu))
  · refine linLow_add (linLow_ofArg fun u hu => h u (by simp only [Lir.Rhs.uses, List.mem_append]; first | exact .inl hu | exact .inr hu)) ?_
    intro t ht; simp at ht
  · split at hl
    · simp only [Option.some.injEq] at hl; subst hl
      exact linLow_scale _ (linLow_ofArg fun u hu => h u (by simp only [Lir.Rhs.uses, List.mem_append]; first | exact .inl hu | exact .inr hu))
    · cases hl
  · split at hl
    · simp only [Option.some.injEq] at hl; subst hl
      exact linLow_scale _ (linLow_ofArg fun u hu => h u (by simp only [Lir.Rhs.uses, List.mem_append]; first | exact .inl hu | exact .inr hu))
    · cases hl
  · split at hl
    · simp only [Option.some.injEq] at hl; subst hl
      exact linLow_scale _ (linLow_ofArg fun u hu => h u (by simp only [Lir.Rhs.uses, List.mem_append]; first | exact .inl hu | exact .inr hu))
    · cases hl
  · cases hl

theorem linLow_fold {N : Nat} {l sub : Lin} {x : VReg} (hl : LinLow N l) (hs : LinLow N sub) (m : Nat) :
    LinLow N (({ l with terms := l.terms.filter (·.1 != .r x) } : Lin).add (sub.scale m)) := by
  refine linLow_add ?_ (linLow_scale m hs)
  intro t ht y hy
  exact hl t (List.mem_filter.1 ht).1 y hy

theorem base_mem_regs {b : Base VReg} {ix : Option (VReg × X86.Scale)} {d : Int32} {x : VReg}
    (hx : x ∈ ({ base := some b, index := ix, disp := d } : Amode VReg).regs) :
    b = .r x ∨ ∃ s, ix = some (x, s) := by
  cases b <;> rcases ix with _ | ⟨y, s⟩ <;> simp [Amode.regs] at hx <;>
    first | (subst hx; simp) | (rcases hx with rfl | rfl <;> simp)

theorem encodeTerms_regs {ts : List (Base VReg × Nat)} {d : Int} {am : Amode VReg}
    (h : Select.encodeTerms ts d = some am) : ∀ x ∈ am.regs, ∃ m, (.r x, m) ∈ ts := by
  unfold Select.encodeTerms at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, _, h⟩ := h
  generalize hf : ts.filter (fun (_, m) => m % 2 ^ 64 != 0) = fs at h
  have hsub : ∀ p ∈ fs, p ∈ ts := by rw [← hf]; intro p hp; exact (List.mem_filter.1 hp).1
  have hidx : ∀ {t : Base VReg × Nat} {x : VReg} {s : X86.Scale}, t ∈ fs →
      (match t with
        | (.r x, m) => (x, ·) <$> Select.scaleOf (m % 2 ^ 64)
        | (.ctx, _) => none) = some (x, s) → ∃ m, (.r x, m) ∈ ts := by
    intro t x s ht hr
    obtain ⟨b, m⟩ := t
    cases b with
    | ctx => simp at hr
    | r y =>
      simp only [Option.map_eq_map, Option.map_eq_some_iff, Prod.mk.injEq] at hr
      obtain ⟨_, _, rfl, _⟩ := hr
      exact ⟨m, hsub _ ht⟩
  split at h
  · simp only [Option.some.injEq] at h; subst h; intro x hx; simp [Amode.regs] at hx
  · simp only [Option.some.injEq] at h; subst h
    rename_i b
    intro x hx
    cases b <;> simp [Amode.regs] at hx
    subst hx; exact ⟨1, hsub _ (by simp)⟩
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨⟨y, sc⟩, hr, rfl⟩ := h
    intro x hx
    simp [Amode.regs] at hx; subst hx
    exact hidx (by simp) hr
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨⟨y, sc⟩, hr, rfl⟩ := h
    intro x hx
    rcases base_mem_regs hx with hb | ⟨s, hs⟩
    · exact ⟨1, hb ▸ hsub _ (by simp)⟩
    · simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      exact hidx (by simp) hr
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨⟨y, sc⟩, hr, rfl⟩ := h
    intro x hx
    rcases base_mem_regs hx with hb | ⟨s, hs⟩
    · exact ⟨1, hb ▸ hsub _ (by simp)⟩
    · simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      exact hidx (by simp) hr
  · cases h

theorem mergeStep_regs (acc : List (Base VReg × Nat)) (p : Base VReg × Nat) :
    ∀ q ∈ mergeStep acc p, q.1 ∈ (acc.map (·.1)) ∨ q.1 = p.1 := by
  intro q hq
  unfold mergeStep at hq
  split at hq
  · simp only [List.mem_map] at hq
    obtain ⟨r, hr, he⟩ := hq
    left
    have : q.1 = r.1 := by obtain ⟨u, n⟩ := r; dsimp only at he; split at he <;> (subst he; rfl)
    rw [this]; exact List.mem_map_of_mem hr
  · simp only [List.mem_append, List.mem_singleton] at hq
    rcases hq with hq | rfl
    · exact .inl (List.mem_map_of_mem hq)
    · exact .inr rfl

theorem foldl_merge_regs : ∀ (ts acc : List (Base VReg × Nat)), ∀ q ∈ ts.foldl mergeStep acc,
    q.1 ∈ acc.map (·.1) ∨ q.1 ∈ ts.map (·.1)
  | [], acc, q, hq => .inl (List.mem_map_of_mem hq)
  | p :: ts, acc, q, hq => by
      rw [List.foldl_cons] at hq
      rcases foldl_merge_regs ts _ q hq with h | h
      · obtain ⟨r, hr, he⟩ := List.mem_map.1 h
        rcases mergeStep_regs acc p r hr with h' | h'
        · exact .inl (he ▸ h')
        · exact .inr (by simp [← he, h'])
      · exact .inr (by simp at h ⊢; exact .inr h)

theorem encode_regs {l : Lin} {am : Amode VReg} (h : l.encode = some am) :
    ∀ x ∈ am.regs, ∃ m, (.r x, m) ∈ l.terms := by
  unfold Lin.encode at h
  cases h₁ : Select.encodeTerms l.terms l.disp with
  | some am' =>
    rw [h₁] at h
    simp only [Option.orElse_eq_orElse, Option.orElse_some, Option.some.injEq] at h
    subst h
    exact encodeTerms_regs h₁
  | none =>
    rw [h₁] at h
    simp only [Option.orElse_eq_orElse, Option.orElse_none] at h
    intro x hx
    obtain ⟨m, hm⟩ := encodeTerms_regs h x hx
    rw [mergeTerms_eq] at hm
    rcases foldl_merge_regs l.terms [] _ hm with h' | h'
    · simp at h'
    · obtain ⟨p, hp, he⟩ := List.mem_map.1 h'
      exact ⟨p.2, by rw [show p = (.r x, p.2) by obtain ⟨u, n⟩ := p; simp at he; simp [he]] at hp; exact hp⟩

/-- An encoded sum names only registers of the sum. -/
theorem encode_low {N : Nat} {l : Lin} {am : Amode VReg} (h : l.encode = some am) (hl : LinLow N l) :
    ∀ x ∈ am.regs, x < N := by
  intro x hx
  obtain ⟨m, hm⟩ := encode_regs h x hx
  exact hl _ hm x rfl

/-- An address that evaluates in one environment evaluates the same in any
environment agreeing on its registers. -/
theorem evalV_congr {ρ ρ' : Env} {ctx : Word} {am : Amode VReg} {a : Word}
    (hag : ∀ x ∈ am.regs, ∀ v, ρ[x]? = some v → ρ'[x]? = some v) (h : am.evalV ρ ctx = some a) :
    am.evalV ρ' ctx = some a := by
  have hd := Amode.evalV_defined h
  have he : ∀ x ∈ am.regs, ρ'[x]? = ρ[x]? := fun x hx => by
    obtain ⟨w, hw⟩ := hd x hx
    rw [hw, hag x hx w hw]
  rw [← h]
  rcases am with ⟨base, index, disp⟩
  rcases base with _ | (b | _) <;> rcases index with _ | ⟨i, s⟩
  · rfl
  · simp only [Amode.evalV, he i (by simp [Amode.regs])]
  · simp only [Amode.evalV, he b (by simp [Amode.regs])]
  · simp only [Amode.evalV, he b (by simp [Amode.regs]), he i (by simp [Amode.regs])]
  · rfl
  · simp only [Amode.evalV, he i (by simp [Amode.regs])]

end IxCC.Xv.Select.Proof
