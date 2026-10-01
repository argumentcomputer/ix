import Compilatrix.Xv.Select.Proof.Arith

/-!
# Shifts and division (rule 12)

`AssignOk` for `selectShift` (`shl/shr/sar r/m, imm8`, `r/m, cl`, a zero
count as a truncating move, and `shl` by at most 3 as an untied `lea` when
the operand lives on) and `selectDiv` (`xor hi32, hi32; div r/m` on
`rdx:rax`, the divisor a register, a folded load, or a materialized
immediate; narrow widths divide the zero-extended operands at width 32).

The machine and Lir mask shift counts alike, so a selected shift computes
Lir's low bits (`shift_lir`); `div` with a zeroed high half never
overflows, and a zero divisor is Lir's `stuck` (the step never runs).
-/

namespace Compilatrix.Xv.Select.Proof

open Compilatrix.Lir (VReg Word Env)
open Compilatrix.X86 (Width)
open Compilatrix.Xv.Select

/-! ## Shift values -/

/-- The x86 shift of a Lir shift. -/
def shiftOf : Lir.BinOp → X86.ShiftOp
  | .shl => .shl
  | .shr => .shr
  | _ => .sar

def IsShift (o : Lir.BinOp) : Prop := o = .shl ∨ o = .shr ∨ o = .sar

theorem shiftOf_mnemonic {o : Lir.BinOp} (h : IsShift o) : shiftMnemonic o = (shiftOf o).mnemonic := by
  rcases h with rfl | rfl | rfl <;> rfl

/-- A Lir shift is the machine's, read at its width. -/
theorem shift_lir {o : Lir.BinOp} (h : IsShift o) (w : Width) (a b : Word) :
    o.eval w a b = some (w.truncate (shiftResult (shiftOf o) w a b)) := by
  rcases h with rfl | rfl | rfl
  · simp [Lir.BinOp.eval, shiftOf, shl_eq]
  · simp [Lir.BinOp.eval, shiftOf, shr_eq]
  · simp [Lir.BinOp.eval, shiftOf, sar_eq]

theorem shiftResult_count {op : X86.ShiftOp} {w : Width} {a k k' : Word}
    (h : X86.shiftCount w k = X86.shiftCount w k') : shiftResult op w a k = shiftResult op w a k' := by
  simp only [shiftResult, h]

theorem shiftCount_masked (w : Width) (k : Word) :
    X86.shiftCount w (UInt64.ofNat (k &&& Lir.shiftMask w).toNat) = X86.shiftCount w k := by
  rw [shiftCount_eq, shiftCount_eq, UInt64.ofNat_toNat, UInt64.and_assoc, UInt64.and_self]

theorem shiftResult_zero (op : X86.ShiftOp) (w : Width) (a : Word) :
    w.truncate (shiftResult op w a 0) = w.truncate a := by
  rw [shiftResult, truncate_mergeWrite]
  have h0 : X86.shiftCount w 0 = 0 := by cases w <;> rfl
  rw [h0]
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  cases op <;>
    simp [X86.Encode.truncate_bits, BitVec.getLsbD_setWidth, X86.ShiftOp.apply] <;>
    by_cases h : i < w.bits <;> simp [h, hi]

/-- A shift's result is already truncated at widths 32 and 64. -/
theorem shift_close (w : Width) (op : X86.ShiftOp) (a k : Word) :
    (if narrowWidth w then w.truncate (shiftResult op w a k) else shiftResult op w a k) =
      w.truncate (shiftResult op w a k) := by
  by_cases hn : narrowWidth w = true
  · simp [hn]
  · simp only [Bool.not_eq_true] at hn
    simp only [hn, Bool.false_eq_true, ↓reduceIte]
    refine (shiftResult_wide ?_ op a k).symm
    cases w <;> simp_all [narrowWidth]


/-! ## `shl/shr/sar` -/

/-- A shift by a constant once the operand is in a register. -/
def shiftImmTail (x : VReg) (mn : X86.Mnemonic) (w : X86.Width) (a : VReg) (s : Nat) (pre : List (Inst VReg)) :
    SelM (List (Inst VReg)) := do
  let dst ← if narrowWidth w then fresh else pure x
  fire "shift.imm"
  return pre ++ (← narrowed w x dst [.op (row mn w .MI) [dst] [.r a, .i (UInt64.ofNat s)]])

/-- A shift by `cl` once the operand is in a register. -/
def shiftClTail (x : VReg) (mn : X86.Mnemonic) (w : X86.Width) (a c : VReg) (pre : List (Inst VReg)) :
    SelM (List (Inst VReg)) := do
  let dst ← if narrowWidth w then fresh else pure x
  fire "shift.cl"
  return pre ++ (← narrowed w x dst [.op (row mn w .MC) [dst] [.r a, .r c]])

/-- `selectShift` once it knows whether the operand lives on, as in `Select.Rules`. -/
def shiftBody (x : VReg) (o : Lir.BinOp) (w : X86.Width) (a b : Lir.Arg) (liveOn : Bool) :
    SelM (List (Inst VReg)) := do
  let (a, pre) ← argReg a
  let mn := shiftMnemonic o
  match b with
  | .imm k =>
      let s := (k &&& Lir.shiftMask w).toNat
      if s == 0 then
        fire "shift.zero"
        return pre ++ truncTo w x a
      if o == .shl && w == .w64 && s ≤ 3 && liveOn then
        if let some am := encodeTerms [(.r a, 2 ^ s)] 0 then
          fire "shl.lea"
          return pre ++ [.op leaRow [x] [.m am]]
      shiftImmTail x mn w a s pre
  | .v c => shiftClTail x mn w a c pre

theorem selectShift_eq (x : VReg) (o : Lir.BinOp) (w : X86.Width) (a b : Lir.Arg) :
    selectShift x o w a b = (do
      let liveOn ← match a with
        | .v y => do pure (decide ((← useCount y) > 1))
        | .imm _ => pure false
      shiftBody x o w a b liveOn) := rfl

/-- A narrowed shift row: the destination, then the narrowing. -/
theorem shiftRow_ok (op : X86.ShiftOp) {form : X86.OpEn} {x : VReg} {w : Width} {b : XArg VReg}
    {pre : List (Inst VReg)} {c : Ctx} {st st' : St} {is : List (Inst VReg)} {name : String}
    (h : (do
      let dst ← if narrowWidth w then fresh else pure x
      fire name
      return pre ++ (← narrowed w x dst [.op (row op.mnemonic w form) [dst] [.r a, b]])) c st = .ok (is, st'))
    (hrow : ∀ (σ : Env) mem ctx dst va vk, σ[a]? = some va → b.valIn σ mem ctx w = some vk →
      Inst.exec σ mem ctx (.op (row op.mnemonic w form) [dst] [.r a, b]) = some (σ.insert dst (shiftResult op w va vk), mem)) :
    st.next ≤ st'.next ∧ st'.consumed = st.consumed ∧ ∃ js, is = pre ++ js ∧ a ∈ readsOf js ∧
      (∀ u ∈ b.regs, u ∈ readsOf js) ∧
      ∀ σ mem ctx va vk, σ[a]? = some va → b.valIn σ mem ctx w = some vk → x < st.next →
        Computes js σ mem ctx st.next x (w.truncate (shiftResult op w va vk)) := by
  by_cases hn : narrowWidth w = true
  · sel_simp [hn] at h
    rw [bind_ok] at h
    obtain ⟨js, st₁, h₁, h⟩ := h
    sel_simp [Option.some.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hn₁, hc₁, hr₁, hv₁⟩ := narrowed_spec h₁
    refine ⟨by simp [hn₁], by simp [hc₁], js, rfl, hr₁ a (by simp [Inst.uses, xargsRegs, XArg.regs]),
      fun u hu => hr₁ u (by simp [Inst.uses, xargsRegs, hu]), fun σ mem ctx va vk ha hb hx => ?_⟩
    have := hv₁ σ mem ctx st.next _ (fun h' => by simp [hn] at h') (fun _ => ⟨Nat.le_refl _, hx⟩)
      (Computes.single (hrow σ mem ctx st.next va vk ha hb))
    rwa [shift_close] at this
  · sel_simp [hn] at h
    rw [bind_ok] at h
    obtain ⟨js, st₁, h₁, h⟩ := h
    sel_simp [Option.some.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hn₁, hc₁, hr₁, hv₁⟩ := narrowed_spec h₁
    refine ⟨by simp [hn₁], by simp [hc₁], js, rfl, hr₁ a (by simp [Inst.uses, xargsRegs, XArg.regs]),
      fun u hu => hr₁ u (by simp [Inst.uses, xargsRegs, hu]), fun σ mem ctx va vk ha hb hx => ?_⟩
    have := hv₁ σ mem ctx st.next _ (fun _ => rfl) (fun h' => absurd h' hn)
      (Computes.single (hrow σ mem ctx x va vk ha hb))
    rwa [shift_close] at this

theorem shiftBody_ok {x : VReg} {o : Lir.BinOp} (ho : IsShift o) {w : Width} {a b : Lir.Arg} {liveOn : Bool}
    {c : Ctx} {st st' : St} {is : List (Inst VReg)} (hlive : ∀ k, a = .imm k → liveOn = false)
    (h : shiftBody x o w a b liveOn c st = .ok (is, st')) : AssignOk c st st' x (.bin o w a b) is := by
  have hmn := shiftOf_mnemonic ho
  unfold shiftBody at h
  rw [bind_ok] at h
  obtain ⟨⟨a', pre⟩, st₁, h₁, h⟩ := h
  obtain ⟨hn₁, hc₁, hr₁, hu₁, hl₁, hv₁⟩ := argReg_spec h₁
  simp only [hmn] at h
  have lir : ∀ (ρ : Env) mem ctx v, (Lir.Rhs.bin o w a b).eval ρ mem ctx = some v →
      ∃ va vb, a.eval ρ = some va ∧ b.eval ρ = some vb ∧ v = w.truncate (shiftResult (shiftOf o) w va vb) := by
    intro ρ mem ctx v hv
    simp only [Lir.Rhs.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at hv
    obtain ⟨va, ha, vb, hb, hv⟩ := hv
    rw [shift_lir ho] at hv
    exact ⟨va, vb, ha, hb, (Option.some.inj hv).symm⟩
  -- the operand, in its register after `pre`
  have opnd : ∀ N (ρ σ : Env) mem ctx va (is : List (Inst VReg)), N ≤ st.next → (∀ u ∈ a.uses, u < N) →
      a.eval ρ = some va → a' ∈ readsOf is → Agree N (readsOf is) ρ σ →
      ∃ σ₁, execSeq σ mem ctx pre = some (σ₁, mem) ∧ σ₁[a']? = some va ∧ ∀ u, u < st.next → σ₁[u]? = σ[u]? :=
    fun N ρ σ mem ctx va is hN hu ha hr hag =>
      hv₁ σ mem ctx va (hag.arg (fun u hu' => by rw [hu₁ u hu']; exact hr) hu ha)
  have ha'lt : ∀ {N : Nat}, N ≤ st.next → (∀ u ∈ a.uses, u < N) → a' < st₁.next :=
    fun hN hu => hl₁ fun u hu' => Nat.lt_of_lt_of_le (hu u hu') hN
  cases b with
  | imm k =>
    simp only at h
    by_cases hz : ((k &&& Lir.shiftMask w).toNat == 0) = true
    · sel_simp [hz] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨(Ext.of_le hn₁ hc₁).trans (Ext.fire c _ _), fun N ρ σ mem ctx v hcl hN hx hu hev hp hag => ?_⟩
      obtain ⟨va, vb, ha, hb, rfl⟩ := lir ρ mem ctx v hev
      simp only [Lir.Arg.eval, Option.some.injEq] at hb
      subst hb
      obtain ⟨σ₁, he₁, ha₁, hab₁⟩ := opnd N ρ σ mem ctx va _ hN (bin_uses_left hu) ha
        (by simp [readsOf_truncTo, hr₁]) hag
      refine ⟨σ₁.insert x (w.truncate va), by rw [execSeq_append he₁, exec_truncTo w ha₁], ?_, ?_⟩
      · simp only [Std.HashMap.getElem?_insert_self, Option.some.injEq]
        have h0 : X86.shiftCount w k = X86.shiftCount w 0 := by
          rw [shiftCount_eq, shiftCount_eq]; simp only [beq_iff_eq] at hz; rw [hz]; simp
        rw [shiftResult_count h0, shiftResult_zero]
      · intro u hu' hne
        rw [insert_ne (Ne.symm hne), hab₁ u hu']
    · sel_simp [hz] at h
      -- the general immediate shift
      have imm_tail : shiftImmTail x (shiftOf o).mnemonic w a' (k &&& Lir.shiftMask w).toNat pre c st₁ =
          .ok (is, st') → AssignOk c st st' x (.bin o w a (.imm k)) is := by
        intro h
        obtain ⟨hn₂, hc₂, js, rfl, hra, -, hv₂⟩ := shiftRow_ok (shiftOf o) h
          (fun σ mem ctx dst va vk ha hb => by
            simp only [XArg.valIn, Option.some.injEq] at hb
            subst hb
            exact exec_shiftI (shiftOf o) w _ ha)
        refine ⟨Ext.of_le (Nat.le_trans hn₁ hn₂) (by rw [hc₂, hc₁]), fun N ρ σ mem ctx v hcl hN hx hu hev hp hag => ?_⟩
        obtain ⟨va, vb, ha, hb, rfl⟩ := lir ρ mem ctx v hev
        simp only [Lir.Arg.eval, Option.some.injEq] at hb
        subst hb
        obtain ⟨σ₁, he₁, ha₁, hab₁⟩ := opnd N ρ σ mem ctx va _ hN (bin_uses_left hu) ha
          (by simp [hr₁, hra]) hag
        refine Computes.append he₁ hab₁ ?_
        have := (hv₂ σ₁ mem ctx va _ ha₁ rfl (Nat.lt_of_lt_of_le hx (Nat.le_trans hN hn₁))).mono hn₁
        rwa [shiftResult_count (shiftCount_masked w k)] at this
      by_cases hlea : (o == .shl && w == .w64 && decide ((k &&& Lir.shiftMask w).toNat ≤ 3) && liveOn) = true
      · sel_simp [hlea] at h
        cases he : encodeTerms [(.r a', 2 ^ (k &&& Lir.shiftMask w).toNat)] 0 with
        | none =>
          sel_simp [he] at h
          exact imm_tail h
        | some am =>
          sel_simp [he] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hlea
          obtain ⟨⟨⟨rfl, rfl⟩, hs3⟩, hl⟩ := hlea
          cases a with
          | imm k' => exact absurd (hlive k' rfl) (by simp [hl])
          | v y =>
            simp only [argReg, pure_run, Except.ok.injEq, Prod.mk.injEq] at h₁
            obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h₁
            refine ⟨Ext.fire c _ _, fun N ρ σ mem ctx v hcl hN hx hu hev hp hag => ?_⟩
            obtain ⟨va, vb, ha, hb, rfl⟩ := lir ρ mem ctx v hev
            simp only [Lir.Arg.eval, Option.some.injEq] at ha hb
            subst hb
            have hyN : y < N := bin_uses_left hu y (by simp [Lir.Arg.uses, Lir.Arg.vreg?])
            have hρ := encodeTerms_val he (s := UInt64.ofNat (2 ^ (k &&& Lir.shiftMask .w64).toNat) * va)
              (ρ := ρ) (ctx := ctx) (by simp [termsVal, termVal, ha])
            have hσ := hag.amode (fun u hu' => by simp [Inst.uses, xargsRegs, XArg.regs, hu'])
              (fun u hu' => by
                obtain ⟨m, hm⟩ := encodeTerms_regs he u hu'
                simp at hm
                rw [hm.1]; exact hyN) hρ
            refine Computes.single ((exec_lea hσ).trans ?_)
            have hlt : (k &&& Lir.shiftMask .w64).toNat < 64 := masked_lt _ _
            have hval : Width.w64.truncate (shiftResult (shiftOf .shl) .w64 va k) =
                UInt64.ofNat (2 ^ (k &&& Lir.shiftMask .w64).toNat) * va := by
              show Width.w64.truncate (shiftResult .shl .w64 va k) = _
              rw [shl_eq, X86.Encode.truncate64, ← shl_mul va hlt, UInt64.ofNat_toNat]
            rw [Lir.dispWord_zero, UInt64.add_zero, hval]
      · sel_simp [hlea] at h
        exact imm_tail h
  | v c' =>
    sel_simp [Option.some.injEq] at h
    obtain ⟨hn₂, hc₂, js, rfl, hra, hrc, hv₂⟩ := shiftRow_ok (shiftOf o) h
      (fun σ mem ctx dst va vk ha hb => by
        simp only [XArg.valIn] at hb
        exact exec_shiftC (shiftOf o) w ha hb)
    refine ⟨Ext.of_le (Nat.le_trans hn₁ hn₂) (by rw [hc₂, hc₁]), fun N ρ σ mem ctx v hcl hN hx hu hev hp hag => ?_⟩
    obtain ⟨va, vb, ha, hb, rfl⟩ := lir ρ mem ctx v hev
    obtain ⟨σ₁, he₁, ha₁, hab₁⟩ := opnd N ρ σ mem ctx va _ hN (bin_uses_left hu) ha
      (by simp [hr₁, hra]) hag
    have hcN : c' < N := bin_uses_right hu c' (by simp [Lir.Arg.uses, Lir.Arg.vreg?])
    have hc₁' : σ₁[c']? = some vb := by
      rw [hab₁ c' (Nat.lt_of_lt_of_le hcN hN)]
      exact hag.get (by simp [hr₁]; exact hrc c' (by simp [XArg.regs])) hcN hb
    refine Computes.append he₁ hab₁ ?_
    exact (hv₂ σ₁ mem ctx va vb ha₁ hc₁' (Nat.lt_of_lt_of_le hx (Nat.le_trans hN hn₁))).mono hn₁

theorem selectShift_ok {x : VReg} {o : Lir.BinOp} (ho : IsShift o) {w : Width} {a b : Lir.Arg}
    {c : Ctx} {st st' : St} {is : List (Inst VReg)} (h : selectShift x o w a b c st = .ok (is, st')) :
    AssignOk c st st' x (.bin o w a b) is := by
  rw [selectShift_eq] at h
  cases a with
  | v y =>
    sel_simp [Option.some.injEq] at h
    exact shiftBody_ok ho (fun _ h => by cases h) h
  | imm k =>
    sel_simp [Option.some.injEq] at h
    exact shiftBody_ok ho (fun _ _ => rfl) h


/-! ## `div` -/

/-- The dividend's register (zero-extended at narrow widths). -/
def divLo (w : X86.Width) (a : Lir.Arg) : SelM (VReg × List (Inst VReg)) :=
  if narrowWidth w then argTrunc w a else argReg a

/-- The divisor: a register, a folded load, or a materialized immediate. -/
def divDivisor (i : Nat) (w : X86.Width) (b : Lir.Arg) : SelM (XArg VReg × List (Inst VReg)) :=
  match b with
  | .v y =>
      if narrowWidth w then do
        let (t, pre) ← argTrunc w (.v y)
        pure (XArg.r t, pre)
      else do
        match ← sinkLoad? y i (opWidth w).bytes with
        | some m =>
            fire "div.load"
            pure (XArg.m m, [])
        | none => pure (XArg.r y, [])
  | .imm k => do
      let (t, pre) ← materialize (w.truncate k)
      pure (XArg.r t, pre)

/-- `xor hi, hi; div` once the operands are placed. -/
def divTail (x : VReg) (rem : Bool) (wo : X86.Width) (lo : VReg) (preA : List (Inst VReg)) (divisor : XArg VReg)
    (preB : List (Inst VReg)) : SelM (List (Inst VReg)) := do
  let hi ← fresh
  let q ← if rem then fresh else pure x
  let r ← if rem then pure x else fresh
  fire (if rem then "div.rem" else "div.quot")
  return preA ++ preB ++ [.zero hi, .op (X86.Op.divM wo) [q, r] [divisor, .r lo, .r hi]]

theorem divLo_spec {w : Width} {a : Lir.Arg} {c : Ctx} {st st' : St} {lo : VReg} {pre : List (Inst VReg)}
    (h : divLo w a c st = .ok ((lo, pre), st')) :
    st.next ≤ st'.next ∧ st'.consumed = st.consumed ∧ (∀ u ∈ a.uses, u = lo ∨ u ∈ readsOf pre) ∧
      ((∀ u ∈ a.uses, u < st.next) → lo < st'.next) ∧
      ∀ σ mem ctx va, (∀ u ∈ a.uses, u < st.next) → a.eval σ = some va →
        ∃ σ' vlo, execSeq σ mem ctx pre = some (σ', mem) ∧ σ'[lo]? = some vlo ∧
          (opWidth w).truncate vlo = w.truncate va ∧ ∀ u, u < st.next → σ'[u]? = σ[u]? := by
  unfold divLo at h
  by_cases hn : narrowWidth w = true
  · simp only [hn, ↓reduceIte] at h
    obtain ⟨hn₁, hc₁, hu₁, hl₁, hv₁⟩ := argTrunc_spec h
    refine ⟨hn₁, hc₁, hu₁, hl₁, fun σ mem ctx va hlow hv => ?_⟩
    obtain ⟨σ', he, hy, hab⟩ := hv₁ σ mem ctx va hlow hv
    exact ⟨σ', _, he, hy, truncate_truncate_ge (bits_opWidth w) va, hab⟩
  · simp only [hn, Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨hn₁, hc₁, hr₁, hu₁, hl₁, hv₁⟩ := argReg_spec h
    refine ⟨hn₁, hc₁, fun u hu => .inl (hu₁ u hu), hl₁, fun σ mem ctx va hlow hv => ?_⟩
    obtain ⟨σ', he, hy, hab⟩ := hv₁ σ mem ctx va hv
    exact ⟨σ', va, he, hy, by rw [opWidth_of_not_narrow (by simpa using hn)], hab⟩

theorem divDivisor_spec {i : Nat} {w : Width} {b : Lir.Arg} {c : Ctx} {st st' : St} {d : XArg VReg}
    {pre : List (Inst VReg)} (hi : c.pos = i) (h : divDivisor i w b c st = .ok ((d, pre), st')) :
    Ext c st st' ∧ (∀ k, d ≠ .i k) ∧
      ∀ N (ρ σ : Env) mem ctx vb, CtxLow c N → N ≤ st.next → (∀ u ∈ b.uses, u < N) → b.eval ρ = some vb →
        Pend c st st' ρ mem ctx → Agree N (readsOf pre ++ d.regs) ρ σ →
        (∀ u ∈ d.regs, u < st'.next) ∧ ∃ σ' vd, execSeq σ mem ctx pre = some (σ', mem) ∧
          d.valIn σ' mem ctx (opWidth w) = some vd ∧ (opWidth w).truncate vd = w.truncate vb ∧
          ∀ u, u < st.next → σ'[u]? = σ[u]? := by
  unfold divDivisor at h
  cases b with
  | v y =>
    have hyu : ∀ {N : Nat}, (∀ u ∈ (Lir.Arg.v y).uses, u < N) → y < N := fun h => h _ (by simp [uses_v])
    by_cases hn : narrowWidth w = true
    · simp only [hn, ↓reduceIte] at h
      rw [bind_ok] at h
      obtain ⟨⟨t, pre'⟩, st₁, h₁, h⟩ := h
      sel_simp [Option.some.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      obtain ⟨hn₁, hc₁, hu₁, hl₁, hv₁⟩ := argTrunc_spec h₁
      refine ⟨Ext.of_le hn₁ hc₁, fun _ => by simp, ?_⟩
      intro N ρ σ mem ctx vb hcl hN hu hv hp hag
      have hylt : y < st.next := Nat.lt_of_lt_of_le (hyu hu) hN
      refine ⟨fun u hu' => by simp [XArg.regs] at hu'; subst hu'; exact hl₁ (by simp [uses_v, hylt]), ?_⟩
      have hσ : (Lir.Arg.v y).eval σ = some vb := by
        rcases hu₁ y (by simp [uses_v]) with h' | h'
        · exact hag.get (by simp [XArg.regs, h']) (hyu hu) hv
        · exact hag.get (by simp [h']) (hyu hu) hv
      obtain ⟨σ', he, ht, hab⟩ := hv₁ σ mem ctx vb (by simp [uses_v, hylt]) hσ
      exact ⟨σ', _, he, by simp [XArg.valIn, ht], truncate_truncate_ge (bits_opWidth w) vb, hab⟩
    · simp only [hn, Bool.false_eq_true, ↓reduceIte] at h
      rw [bind_ok] at h
      obtain ⟨r, st₁, h₁, h⟩ := h
      obtain ⟨hext₁, hn₁, hnone₁, hsome₁⟩ := sinkLoad?_spec h₁ hi.symm
      cases r with
      | some m =>
        sel_simp [Option.some.injEq] at h
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
        obtain ⟨hlow, hval⟩ := hsome₁ m rfl
        refine ⟨hext₁.trans (Ext.fire c _ _), fun _ => by simp, ?_⟩
        intro N ρ σ mem ctx vb hcl hN hu hv hp hag
        obtain ⟨_, hmN⟩ := hlow N hcl
        obtain ⟨addr, vy, hy, haddr, hread⟩ := hval ρ mem ctx (hp.left (Ext.fire c _ _))
        simp only [Lir.Arg.eval] at hv
        rw [hv] at hy
        cases hy
        have hm := hag.amode (fun u hu' => by simp [XArg.regs, hu']) hmN haddr
        refine ⟨fun u hu' => Nat.lt_of_lt_of_le (hmN u (by simpa [XArg.regs] using hu'))
            (by simp [hn₁]; exact hN), σ, _, rfl, valIn_m hm (hread _ (Nat.le_refl _)), ?_, fun _ _ => rfl⟩
        rw [truncate_idem, opWidth_of_not_narrow (by simpa using hn)]
      | none =>
        obtain rfl := hnone₁ rfl
        sel_simp [Option.some.injEq] at h
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
        refine ⟨Ext.refl c _, fun _ => by simp, ?_⟩
        intro N ρ σ mem ctx vb hcl hN hu hv hp hag
        refine ⟨fun u hu' => by simp [XArg.regs] at hu'; subst hu'; exact Nat.lt_of_lt_of_le (hyu hu) hN, σ, vb, rfl,
          hag.get (by simp [XArg.regs]) (hyu hu) hv, ?_, fun _ _ => rfl⟩
        rw [opWidth_of_not_narrow (by simpa using hn)]
  | imm k =>
    rw [bind_ok] at h
    obtain ⟨⟨t, pre'⟩, st₁, h₁, h⟩ := h
    sel_simp [Option.some.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    obtain ⟨rfl, hn₁, hc₁, hr₁, hv₁⟩ := materialize_spec h₁
    refine ⟨Ext.of_le (by rw [hn₁]; exact Nat.le_succ _) hc₁, fun _ => by simp, ?_⟩
    intro N ρ σ mem ctx vb hcl hN hu hv hp hag
    simp only [Lir.Arg.eval, Option.some.injEq] at hv
    subst hv
    refine ⟨fun u hu' => by simp [XArg.regs] at hu'; subst hu'; rw [hn₁]; exact Nat.lt_succ_self _,
      _, _, hv₁ σ mem ctx, by simp [XArg.valIn], truncate_truncate_ge (bits_opWidth w) k, insert_below (Nat.le_refl _)⟩


/-- The Lir operation `selectDiv … rem` lowers. -/
def divOp (rem : Bool) : Lir.BinOp := if rem then .urem else .udiv

theorem div_lir {rem : Bool} {w : Width} {a b : Lir.Arg} {ρ : Env} {mem : X86.Memory} {ctx v : Word}
    (h : (Lir.Rhs.bin (divOp rem) w a b).eval ρ mem ctx = some v) :
    ∃ va vb, a.eval ρ = some va ∧ b.eval ρ = some vb ∧ w.truncate vb ≠ 0 ∧
      v = (if rem then w.truncate va % w.truncate vb else w.truncate va / w.truncate vb) := by
  simp only [Lir.Rhs.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨va, ha, vb, hb, hv⟩ := h
  refine ⟨va, vb, ha, hb, ?_⟩
  cases rem <;> simp only [divOp, Lir.BinOp.eval, Bool.false_eq_true, ↓reduceIte] at hv <;>
    split at hv <;> simp_all

theorem div_ok {i : Nat} {x : VReg} {rem : Bool} {w : Width} {a b : Lir.Arg} {c : Ctx} {st st₁ st₂ st' : St}
    {lo : VReg} {preA : List (Inst VReg)} {d : XArg VReg} {preB is : List (Inst VReg)} (hi : c.pos = i)
    (hA : divLo w a c st = .ok ((lo, preA), st₁)) (hB : divDivisor i w b c st₁ = .ok ((d, preB), st₂))
    (hT : divTail x rem (opWidth w) lo preA d preB c st₂ = .ok (is, st')) :
    AssignOk c st st' x (.bin (divOp rem) w a b) is := by
  have hw := opWidth_wide w
  obtain ⟨hnA, hcA, huA, hlA, hvA⟩ := divLo_spec hA
  obtain ⟨hextB, hdi, hvB⟩ := divDivisor_spec hi hB
  -- the instructions
  obtain ⟨q, r, hq, hr, rfl, hT'⟩ : ∃ q r, st₂.next + 1 = (if rem then q else r) ∧
      (if rem then r else q) = x ∧
      is = preA ++ preB ++ [.zero st₂.next, .op (X86.Op.divM (opWidth w)) [q, r] [d, .r lo, .r st₂.next]] ∧
      Ext c st₂ st' := by
    unfold divTail at hT
    cases rem
    · sel_simp [Option.some.injEq] at hT
      obtain ⟨rfl, rfl⟩ := hT
      exact ⟨x, st₂.next + 1, rfl, rfl, rfl, Ext.of_le (by simp; vomega) (by simp)⟩
    · sel_simp [Option.some.injEq] at hT
      obtain ⟨rfl, rfl⟩ := hT
      exact ⟨st₂.next + 1, x, rfl, rfl, rfl, Ext.of_le (by simp; vomega) (by simp)⟩
  refine ⟨(Ext.of_le hnA hcA).trans (hextB.trans hT'), fun N ρ σ mem ctx v hcl hN hx hu hev hp hag => ?_⟩
  obtain ⟨va, vb, ha, hb, hnz, rfl⟩ := div_lir hev
  have hlowA : ∀ u ∈ a.uses, u < st.next := fun u hu' => Nat.lt_of_lt_of_le (bin_uses_left hu u hu') hN
  have hn₂ : st.next ≤ st₂.next := Nat.le_trans hnA hextB.next
  -- the dividend in `lo`, after `preA`
  have hreadsA : ∀ u ∈ a.uses, u ∈ readsOf (preA ++ preB ++ [.zero st₂.next,
      .op (X86.Op.divM (opWidth w)) [q, r] [d, .r lo, .r st₂.next]]) := by
    intro u hu'
    rcases huA u hu' with rfl | h'
    · simp [Inst.uses, xargsRegs, XArg.regs]
    · simp [h']
  obtain ⟨σ₁, vlo, he₁, hlo₁, hvlo, hab₁⟩ := hvA σ mem ctx va hlowA
    (hag.arg hreadsA (bin_uses_left hu) ha)
  -- the divisor, after `preB`
  obtain ⟨hdr, σ₂, vd, he₂, hd₂, hvd, hab₂⟩ := hvB N ρ σ₁ mem ctx vb hcl (Nat.le_trans hN hnA) (bin_uses_right hu) hb
    ((hp.right (Ext.of_le hnA hcA)).left hT')
    ((hag.mono fun u hu' => by
        rcases List.mem_append.1 hu' with h' | h'
        · simp [h']
        · simp [Inst.uses, xargsRegs, h']).above hab₁ hN)
  have hlo₂ : σ₂[lo]? = some vlo := by rw [hab₂ lo (hlA hlowA)]; exact hlo₁
  -- `xor hi, hi` and `div`
  have hz : Inst.exec σ₂ mem ctx (.zero st₂.next) = some (σ₂.insert st₂.next 0, mem) := exec_zero _ _ _ _
  have hd₃ : d.valIn (σ₂.insert st₂.next 0) mem ctx (opWidth w) = some vd := by
    rw [valIn_above hdr (insert_below (Nat.le_refl _))]; exact hd₂
  have hlo₃ : (σ₂.insert st₂.next 0)[lo]? = some vlo := by
    rw [insert_ne (by have := hlA hlowA; have := hextB.next; vomega)]; exact hlo₂
  have hnz' : ((opWidth w).truncate vd).toNat ≠ 0 := by
    rw [hvd]; intro h0; exact hnz (UInt64.toNat_inj.mp (by simpa using h0))
  have hdiv := exec_div (q := q) (r := r) (vhi := 0) hw hd₃ (hdi) hlo₃ (by rw [Std.HashMap.getElem?_insert_self]) hnz'
    (by rw [truncate_zero]; simpa [Nat.pos_iff_ne_zero] using hnz')
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left
  · rw [execSeq_append (by rw [execSeq_append he₁, he₂]), execSeq_cons hz, execSeq_singleton, hdiv]
  · rw [divQuot_eq hw, divRem_eq hw, hvlo, hvd]
    have hfx : st₂.next + 1 ≠ x := by vomega
    cases rem
    · simp only [Bool.false_eq_true, ↓reduceIte] at hq hr ⊢
      subst hr hq
      rw [insert_ne hfx, Std.HashMap.getElem?_insert_self]
    · simp only [↓reduceIte] at hq hr ⊢
      subst hr
      rw [Std.HashMap.getElem?_insert_self]
  · intro u hu' hne
    have hq' : q ≠ u := by
      cases rem <;> simp only [Bool.false_eq_true, ↓reduceIte] at hq hr
      · rw [hr]; exact Ne.symm hne
      · rw [← hq]; vomega
    have hr' : r ≠ u := by
      cases rem <;> simp only [Bool.false_eq_true, ↓reduceIte] at hq hr
      · rw [← hq]; vomega
      · rw [hr]; exact Ne.symm hne
    rw [insert_ne hr', insert_ne hq', insert_ne (by vomega), hab₂ u (Nat.lt_of_lt_of_le hu' hnA), hab₁ u hu']

theorem selectDiv_ok {i : Nat} {x : VReg} {rem : Bool} {w : Width} {a b : Lir.Arg} {c : Ctx} {st st' : St}
    {is : List (Inst VReg)} (hi : c.pos = i) (h : selectDiv i x rem w a b c st = .ok (is, st')) :
    AssignOk c st st' x (.bin (divOp rem) w a b) is := by
  unfold selectDiv at h
  by_cases hn : narrowWidth w = true
  · sel_simp [hn] at h
    rw [bind_ok] at h
    obtain ⟨⟨lo, preA⟩, st₁, h₁, h⟩ := h
    have hA : divLo w a c st = .ok ((lo, preA), st₁) := by simpa [divLo, hn] using h₁
    cases b with
    | v y =>
      sel_simp [Option.some.injEq] at h
      rw [bind_ok] at h
      obtain ⟨⟨t, pre⟩, st₂, h₂, h⟩ := h
      have hB : divDivisor i w (.v y) c st₁ = .ok ((.r t, pre), st₂) := by
        simp only [divDivisor, hn, ↓reduceIte]
        rw [bind_ok]
        exact ⟨_, _, h₂, rfl⟩
      exact div_ok hi hA hB h
    | imm k =>
      sel_simp [Option.some.injEq] at h
      rw [bind_ok] at h
      obtain ⟨⟨t, pre⟩, st₂, h₂, h⟩ := h
      have hB : divDivisor i w (.imm k) c st₁ = .ok ((.r t, pre), st₂) := by
        simp only [divDivisor]
        rw [bind_ok]
        exact ⟨_, _, h₂, rfl⟩
      exact div_ok hi hA hB h
  · sel_simp [hn] at h
    rw [bind_ok] at h
    obtain ⟨⟨lo, preA⟩, st₁, h₁, h⟩ := h
    have hA : divLo w a c st = .ok ((lo, preA), st₁) := by simpa [divLo, hn] using h₁
    cases b with
    | v y =>
      sel_simp [Option.some.injEq] at h
      rw [bind_ok] at h
      obtain ⟨r, st₂, h₂, h⟩ := h
      cases r with
      | some m =>
        sel_simp [Option.some.injEq] at h
        have hB : divDivisor i w (.v y) c st₁ = .ok ((.m m, []), fireSt "div.load" st₂) := by
          simp only [divDivisor, hn, Bool.false_eq_true, ↓reduceIte]
          rw [bind_ok]
          exact ⟨_, _, h₂, rfl⟩
        exact div_ok hi hA hB h
      | none =>
        sel_simp [Option.some.injEq] at h
        have hB : divDivisor i w (.v y) c st₁ = .ok ((.r y, []), st₂) := by
          simp only [divDivisor, hn, Bool.false_eq_true, ↓reduceIte]
          rw [bind_ok]
          exact ⟨_, _, h₂, rfl⟩
        exact div_ok hi hA hB h
    | imm k =>
      sel_simp [Option.some.injEq] at h
      rw [bind_ok] at h
      obtain ⟨⟨t, pre⟩, st₂, h₂, h⟩ := h
      have hB : divDivisor i w (.imm k) c st₁ = .ok ((.r t, pre), st₂) := by
        simp only [divDivisor]
        rw [bind_ok]
        exact ⟨_, _, h₂, rfl⟩
      exact div_ok hi hA hB h

end Compilatrix.Xv.Select.Proof
