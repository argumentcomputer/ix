import Compilatrix.Xv.Select.Proof.Assign

/-!
# Arithmetic rules: ALU rows, `lea`, `imul`

`AssignOk` for `selectAlu` (rules 6, 7 and 9 for `add`, `sub`, `and`, `or`,
`xor`: tied `op r/m, r`, `op r/m, imm8/imm32`, `op r, m` with a folded load,
and the untied `lea` of rule 7) and `selectMul` (rule 12's `imul` and rule
9's `imul r, m`), narrow widths included: a narrow operation runs at width 32
into a fresh register and is zero-extended into its destination.

`leaTail`, `aluBody` and `mulBody` are parts of the rules as written in
`Select.Rules`; `leaAdd?_eq`, `selectAlu_eq` and `selectMul_eq` unfold the
rules to them (`rfl`).
-/

namespace Compilatrix.Xv.Select.Proof

open Compilatrix.Lir (VReg Word Env)
open Compilatrix.X86 (Width)
open Compilatrix.Xv.Select

/-! ## Rule 7: `lea` for an addition -/

/-- `leaAdd?` once the operands' sum is formed. -/
def leaTail (x : VReg) (lin : Lin) (regs : List VReg) : SelM (Option (List (Inst VReg))) := do
  let (folded, used) ← foldLin lin
  let liveOn ← regs.allM fun r => return (← useCount r) > 1
  unless !used.isEmpty || liveOn do return none
  match folded.encode with
  | some am =>
      commitFold used
      fire "lea.add"
      return some [.op leaRow [x] [.m am]]
  | none => return none

theorem leaAdd?_eq (x : VReg) (o : Lir.BinOp) (a b : Lir.Arg) :
    leaAdd? x o a b = (match o, a, b with
      | .add, .v a, .v b => leaTail x ((Lin.ofArg (.v a)).add (Lin.ofArg (.v b))) [a, b]
      | .add, .v a, .imm k => leaTail x ((Lin.ofArg (.v a)).add (Lin.ofArg (.imm k))) [a]
      | .add, .imm k, .v a => leaTail x ((Lin.ofArg (.v a)).add (Lin.ofArg (.imm k))) [a]
      | .sub, .v a, .imm k => leaTail x ((Lin.ofArg (.v a)).add { disp := -(k.toNat : Int) }) [a]
      | _, _, _ => pure none) := by
  cases o <;> cases a <;> cases b <;> rfl

theorem allM_useCount :
    ∀ {regs : List VReg} {c : Ctx} {st st' : St} {b : Bool},
      (regs.allM fun r => do let n ← useCount r; pure (decide (n > 1)) : SelM Bool) c st = .ok (b, st') → st' = st
  | [], c, st, st', b, h => by
      simp only [List.allM, pure_run, Except.ok.injEq, Prod.mk.injEq] at h
      exact h.2.symm
  | r :: rs, c, st, st', b, h => by
      simp only [List.allM] at h
      rw [bind_ok] at h
      obtain ⟨b₁, st₁, h₁, h⟩ := h
      sel_simp [Option.some.injEq] at h₁
      obtain ⟨-, rfl⟩ := h₁
      cases b₁ with
      | true => exact allM_useCount h
      | false => sel_simp [Option.some.injEq] at h; exact h.2.symm

theorem leaTail_spec {x : VReg} {lin : Lin} {regs : List VReg} {c : Ctx} {st st' : St}
    {res : Option (List (Inst VReg))} (h : leaTail x lin regs c st = .ok (res, st')) :
    (res = none → st' = st) ∧ ∀ is, res = some is → ∃ am, is = [.op leaRow [x] [.m am]] ∧ Ext c st st' ∧
      st'.next = st.next ∧ (∀ N, CtxLow c N → LinLow N lin → ∀ u ∈ am.regs, u < N) ∧
      ∀ ρ mem ctx a, Pend c st st' ρ mem ctx → linVal ρ ctx lin = some a → am.evalV ρ ctx = some a := by
  unfold leaTail at h
  rw [bind_ok] at h
  obtain ⟨⟨folded, used⟩, st₁, h₁, h⟩ := h
  obtain ⟨rfl, hF⟩ := foldLin_spec h₁
  simp only at h
  rw [bind_ok] at h
  obtain ⟨liveOn, st₂, h₂, h⟩ := h
  obtain rfl := allM_useCount h₂
  by_cases hc : (!used.isEmpty || liveOn) = true
  · sel_simp [hc] at h
    cases he : folded.encode with
    | none =>
      sel_simp [he] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨fun _ => rfl, fun _ h => by cases h⟩
    | some am =>
      sel_simp [he] at h
      rw [bind_ok] at h
      obtain ⟨u, st₃, h₃, h⟩ := h
      sel_simp [Option.some.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hn₃, hc₃⟩ := commitFold_spec h₃
      refine ⟨fun h => (by cases h), fun is his => ?_⟩
      simp only [Option.some.injEq] at his
      subst his
      refine ⟨am, rfl, (hF.ext hn₃ hc₃).trans (Ext.fire c _ _), by simp [hn₃], fun N hcl hl => encode_low he (hF.low N hcl hl),
        fun ρ mem ctx a hp hl => encode_val he (hF.val ρ mem ctx a (hF.pend hc₃ (hp.left (Ext.fire c _ _))) hl)⟩
  · sel_simp [hc] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨fun _ => rfl, fun _ h => by cases h⟩

theorem linVal_disp (ρ : Env) (ctx : Word) (d : Int) : linVal ρ ctx ({ disp := d } : Lin) = some (Lir.dispWord d) := by
  simp [linVal, termsVal]

/-- A `lea` of the operands' sum computes a 64-bit addition or subtraction. -/
theorem leaAdd_ok {x : VReg} {o : Lir.BinOp} {a b : Lir.Arg} {lin : Lin} {regs : List VReg} {c : Ctx} {st st' : St}
    {is : List (Inst VReg)} (h : leaTail x lin regs c st = .ok (some is, st'))
    (hval : ∀ (ρ : Env) mem ctx v, (Lir.Rhs.bin o .w64 a b).eval ρ mem ctx = some v → linVal ρ ctx lin = some v)
    (hlow : ∀ N, (∀ u ∈ (Lir.Rhs.bin o .w64 a b).uses, u < N) → LinLow N lin) :
    AssignOk c st st' x (.bin o .w64 a b) is := by
  obtain ⟨-, hsome⟩ := leaTail_spec h
  obtain ⟨am, rfl, hext, hn, hl, hv⟩ := hsome is rfl
  refine ⟨hext, fun N ρ σ mem ctx v hcl hN hx hu hev hp hag => ?_⟩
  have hρ := hv ρ mem ctx v hp (hval ρ mem ctx v hev)
  have hσ := hag.amode (fun u hu' => by simp [Inst.uses, xargsRegs, XArg.regs, hu']) (hl N hcl (hlow N hu)) hρ
  exact Computes.single (exec_lea hσ)

theorem leaAdd?_spec {x : VReg} {o : Lir.BinOp} {a b : Lir.Arg} {c : Ctx} {st st' : St}
    {res : Option (List (Inst VReg))} (h : leaAdd? x o a b c st = .ok (res, st')) :
    (res = none → st' = st) ∧ ∀ is, res = some is → AssignOk c st st' x (.bin o .w64 a b) is := by
  rw [leaAdd?_eq] at h
  have tail : ∀ {lin regs}, leaTail x lin regs c st = .ok (res, st') →
      (∀ (ρ : Env) mem ctx v, (Lir.Rhs.bin o .w64 a b).eval ρ mem ctx = some v → linVal ρ ctx lin = some v) →
      (∀ N, (∀ u ∈ (Lir.Rhs.bin o .w64 a b).uses, u < N) → LinLow N lin) →
      (res = none → st' = st) ∧ ∀ is, res = some is → AssignOk c st st' x (.bin o .w64 a b) is := by
    intro lin regs h hval hlow
    refine ⟨(leaTail_spec h).1, fun is his => ?_⟩
    subst his
    exact leaAdd_ok h hval hlow
  have lowv : ∀ {N : Nat} {y : VReg}, (∀ u ∈ (Lir.Arg.v y).uses, u < N) → LinLow N (Lin.ofArg (.v y)) :=
    fun h => linLow_ofArg h
  cases o <;> cases a <;> cases b
  all_goals first
    | (simp only [pure_run, Except.ok.injEq, Prod.mk.injEq] at h
       obtain ⟨rfl, rfl⟩ := h
       exact ⟨fun _ => rfl, fun _ h => by cases h⟩)
    | skip
  case add.v.v y z =>
    refine tail h (fun ρ mem ctx v hv => ?_) (fun N hu => linLow_add (lowv fun u hu' => hu u (by simp_all [Lir.Rhs.uses]))
      (lowv fun u hu' => hu u (by simp_all [Lir.Rhs.uses])))
    simp only [Lir.Rhs.eval, Lir.BinOp.eval, Lir.Arg.eval, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at hv
    obtain ⟨va, hva, vb, hvb, rfl⟩ := hv
    rw [linVal_add, linVal_ofArg, linVal_ofArg]
    simp [Lir.Arg.eval, hva, hvb]
  case add.v.imm y k =>
    refine tail h (fun ρ mem ctx v hv => ?_) (fun N hu => linLow_add (lowv fun u hu' => hu u (by simp_all [Lir.Rhs.uses]))
      (linLow_ofArg (by simp [Lir.Arg.uses, Lir.Arg.vreg?])))
    simp only [Lir.Rhs.eval, Lir.BinOp.eval, Lir.Arg.eval, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at hv
    obtain ⟨va, hva, vb, hvb, rfl⟩ := hv
    rw [linVal_add, linVal_ofArg, linVal_ofArg]
    simp_all [Lir.Arg.eval]
  case add.imm.v k y =>
    refine tail h (fun ρ mem ctx v hv => ?_) (fun N hu => linLow_add (lowv fun u hu' => hu u (by simp_all [Lir.Rhs.uses]))
      (linLow_ofArg (by simp [Lir.Arg.uses, Lir.Arg.vreg?])))
    simp only [Lir.Rhs.eval, Lir.BinOp.eval, Lir.Arg.eval, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at hv
    obtain ⟨va, hva, vb, hvb, rfl⟩ := hv
    rw [linVal_add, linVal_ofArg, linVal_ofArg]
    simp_all [Lir.Arg.eval, UInt64.add_comm]
  case sub.v.imm y k =>
    refine tail h (fun ρ mem ctx v hv => ?_) (fun N hu => linLow_add (lowv fun u hu' => hu u (by simp_all [Lir.Rhs.uses]))
      (fun t ht => by simp at ht))
    simp only [Lir.Rhs.eval, Lir.BinOp.eval, Lir.Arg.eval, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at hv
    obtain ⟨va, hva, vb, hvb, rfl⟩ := hv
    rw [linVal_add, linVal_ofArg, linVal_disp, dispWord_negWord]
    simp_all [Lir.Arg.eval, UInt64.sub_eq_add_neg]

/-! ## ALU rows (rules 6 and 9) -/

/-- `selectAlu` once its destination is chosen, as in `Select.Rules`. -/
def aluBody (i : Nat) (x : VReg) (o : Lir.BinOp) (w : X86.Width) (a b : Lir.Arg) (dst : VReg) :
    SelM (List (Inst VReg)) := do
  let narrow := narrowWidth w
  let wo := opWidth w
  let mn := aluMnemonic o
  let trunc (k : Word) : Word := if narrow then w.truncate k else k
  let body ← match a, b with
    | .v a, .v b => do
        if let some m ← sinkLoad? b i wo.bytes then
          fire "alu.load"
          return ← narrowed w x dst [.op (row mn wo .RM) [dst] [.r a, .m m]]
        if o != .sub then
          if let some m ← sinkLoad? a i wo.bytes then
            fire "alu.load"
            return ← narrowed w x dst [.op (row mn wo .RM) [dst] [.r b, .m m]]
        let (a, b) ← if o == .sub then pure (a, b) else tieOrder a b
        fire "alu.rr"
        pure [.op (row mn wo .MR) [dst] [.r a, .r b]]
    | .v a, .imm k => aluImm mn wo dst a (trunc k)
    | .imm k, .v b =>
        if o == .sub then do
          let (t, pre) ← materialize k
          fire "alu.rr"
          pure (pre ++ [.op (row mn wo .MR) [dst] [.r t, .r b]])
        else do
          fire "alu.swap"
          aluImm mn wo dst b (trunc k)
    | .imm ka, .imm kb => do
        let (t, pre) ← materialize ka
        pure (pre ++ (← aluImm mn wo dst t (trunc kb)))
  narrowed w x dst body

/-- `selectAlu` after the `lea` attempt. -/
def aluStart (i : Nat) (x : VReg) (o : Lir.BinOp) (w : X86.Width) (a b : Lir.Arg) : SelM (List (Inst VReg)) := do
  let dst ← if narrowWidth w then fresh else pure x
  aluBody i x o w a b dst

theorem selectAlu_eq (i : Nat) (x : VReg) (o : Lir.BinOp) (w : X86.Width) (a b : Lir.Arg) :
    selectAlu i x o w a b = (do
      if w == .w64 && (o == .add || o == .sub) then
        if let some out ← leaAdd? x o a b then return out
      aluStart i x o w a b) := rfl

theorem trunc_low (w : Width) (k : Word) : w.truncate (if narrowWidth w then w.truncate k else k) = w.truncate k := by
  split
  · exact truncate_idem w k
  · rfl

/-- The last step of an ALU path: narrowing the operation's result into `x`. -/
theorem alu_close {o : Lir.BinOp} {w : Width} {x dst : VReg} {body is : List (Inst VReg)} {c : Ctx} {st₁ st' : St}
    (h : narrowed w x dst body c st₁ = .ok (is, st')) :
    st'.next = st₁.next ∧ st'.consumed = st₁.consumed ∧ (∀ u ∈ readsOf body, u ∈ readsOf is) ∧
      ∀ σ mem ctx n va vb va' vb', (narrowWidth w = false → dst = x) → (narrowWidth w = true → n ≤ dst ∧ x < n) →
        w.truncate va' = w.truncate va → w.truncate vb' = w.truncate vb →
        Computes body σ mem ctx n dst ((opWidth w).truncate ((aluOf o).eval va' vb')) →
        Computes is σ mem ctx n x (w.truncate ((aluOf o).eval va vb)) := by
  obtain ⟨hn, hc, hr, hv⟩ := narrowed_spec h
  refine ⟨hn, hc, hr, fun σ mem ctx n va vb va' vb' hd₁ hd₂ ha hb hbody => ?_⟩
  have := hv σ mem ctx n _ hd₁ hd₂ hbody
  rwa [narrow_val, alu_congr _ ha hb] at this

theorem low_trunc_wo (w : Width) (z : Word) : w.truncate ((opWidth w).truncate z) = w.truncate z :=
  truncate_truncate_le (bits_opWidth w) z


theorem alu_lir {o : Lir.BinOp} (ho : IsAlu o) {w : Width} {a b : Lir.Arg} {ρ : Env} {mem : X86.Memory} {ctx v : Word}
    (h : (Lir.Rhs.bin o w a b).eval ρ mem ctx = some v) :
    ∃ va vb, a.eval ρ = some va ∧ b.eval ρ = some vb ∧ v = w.truncate ((aluOf o).eval va vb) := by
  simp only [Lir.Rhs.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨va, ha, vb, hb, hv⟩ := h
  rw [aluOf_eval ho] at hv
  exact ⟨va, vb, ha, hb, (Option.some.inj hv).symm⟩

theorem bin_uses_left {o : Lir.BinOp} {w : Width} {a b : Lir.Arg} {N : Nat}
    (h : ∀ u ∈ (Lir.Rhs.bin o w a b).uses, u < N) : ∀ u ∈ a.uses, u < N :=
  fun u hu => h u (by simp [Lir.Rhs.uses, hu])

theorem bin_uses_right {o : Lir.BinOp} {w : Width} {a b : Lir.Arg} {N : Nat}
    (h : ∀ u ∈ (Lir.Rhs.bin o w a b).uses, u < N) : ∀ u ∈ b.uses, u < N :=
  fun u hu => h u (by simp [Lir.Rhs.uses, hu])

theorem aluBody_ok {i : Nat} {x : VReg} {o : Lir.BinOp} (ho : IsAlu o) {w : Width} {a b : Lir.Arg} {dst : VReg}
    {c : Ctx} {st₀ st st' : St} {is : List (Inst VReg)} (hi : c.pos = i)
    (hdst₁ : narrowWidth w = false → dst = x) (hdst₂ : narrowWidth w = true → st₀.next ≤ dst ∧ dst < st.next)
    (hst : Ext c st₀ st) (hcs : st.consumed = st₀.consumed)
    (h : aluBody i x o w a b dst c st = .ok (is, st')) :
    AssignOk c st₀ st' x (.bin o w a b) is := by
  have hw := opWidth_wide w
  have hmn := aluOf_mnemonic ho
  have hdn : ∀ {N : Nat}, x < N → N ≤ st₀.next → narrowWidth w = true → st₀.next ≤ dst ∧ x < st₀.next :=
    fun hx hN hn => ⟨(hdst₂ hn).1, Nat.lt_of_lt_of_le hx hN⟩
  have vlow : ∀ {N : Nat} {y : VReg}, (∀ u ∈ (Lir.Arg.v y).uses, u < N) → y < N :=
    fun h => h _ (by simp [Lir.Arg.uses, Lir.Arg.vreg?])
  have hdstlt : dst < st.next ∨ dst = x := by
    by_cases hn : narrowWidth w = true
    · exact .inl (hdst₂ hn).2
    · exact .inr (hdst₁ (by simpa using hn))
  unfold aluBody at h
  simp only [hmn] at h
  cases a with
  | v a' =>
    cases b with
    | v b' =>
      sel_simp [Option.some.injEq] at h
      rw [bind_ok] at h
      obtain ⟨r₁, st₁, h₁, h⟩ := h
      obtain ⟨hext₁, hn₁, hnone₁, hsome₁⟩ := sinkLoad?_spec h₁ hi.symm
      cases r₁ with
      | some m =>
        -- rule 9: `op r, m` with the right operand's load
        sel_simp [Option.some.injEq] at h
        obtain ⟨hn₂, hc₂, hr₂, hv₂⟩ := alu_close h
        have he₂ : Ext c st₁ st' := (Ext.fire c _ _).trans (Ext.of_same hn₂ hc₂)
        refine ⟨hst.trans (hext₁.trans he₂), fun N ρ σ mem ctx v hcl hN hx hu hev hp hag => ?_⟩
        obtain ⟨va, vb, ha, hb, rfl⟩ := alu_lir ho hev
        obtain ⟨hlow, hval⟩ := hsome₁ m rfl
        obtain ⟨_, hmN⟩ := hlow N hcl
        obtain ⟨addr, vy, hy, haddr, hread⟩ := hval ρ mem ctx ((hp.right hst).left he₂)
        simp only [Lir.Arg.eval] at ha hb
        rw [hb] at hy
        cases hy
        have hag' := hag.mono hr₂
        have ha' := hag'.get (by simp [Inst.uses, xargsRegs, XArg.regs]) (vlow (bin_uses_left hu)) ha
        have hm := hag'.amode (fun u hu' => by simp [Inst.uses, xargsRegs, XArg.regs, hu']) hmN haddr
        exact hv₂ σ mem ctx st₀.next va vb va _ hdst₁ (hdn hx hN) rfl (low_trunc_wo w vb)
          (Computes.single (exec_aluM (aluOf o) hw ha' hm (hread _ (Nat.le_refl _))))
      | none =>
        obtain rfl := hnone₁ rfl
        by_cases hs : o = .sub
        · subst hs
          sel_simp [bne_self_eq_false, beq_self_eq_true] at h
          obtain ⟨hn₂, hc₂, hr₂, hv₂⟩ := alu_close h
          refine ⟨hst.trans ((Ext.fire c _ _).trans (Ext.of_same hn₂ hc₂)),
            fun N ρ σ mem ctx v hcl hN hx hu hev hp hag => ?_⟩
          obtain ⟨va, vb, ha, hb, rfl⟩ := alu_lir ho hev
          have hag' := hag.mono hr₂
          have ha' := hag'.get (by simp [Inst.uses, xargsRegs, XArg.regs]) (vlow (bin_uses_left hu)) ha
          have hb' := hag'.get (by simp [Inst.uses, xargsRegs, XArg.regs]) (vlow (bin_uses_right hu)) hb
          exact hv₂ σ mem ctx st₀.next va vb va vb hdst₁ (hdn hx hN) rfl rfl
            (Computes.single (exec_aluR (aluOf .sub) hw ha' hb'))
        · have hs₁ : (o != .sub) = true := by simpa using hs
          have hs₂ : (o == .sub) = false := by simpa using hs
          sel_simp [hs₁, hs₂] at h
          rw [bind_ok] at h
          obtain ⟨r₂, st₂, h₂, h⟩ := h
          obtain ⟨hext₂, hn₂', hnone₂, hsome₂⟩ := sinkLoad?_spec h₂ hi.symm
          cases r₂ with
          | some m =>
            -- rule 9 with the left operand's load, the operation commuted
            sel_simp [Option.some.injEq] at h
            obtain ⟨hn₃, hc₃, hr₃, hv₃⟩ := alu_close h
            have he₃ : Ext c st₂ st' := (Ext.fire c _ _).trans (Ext.of_same hn₃ hc₃)
            refine ⟨hst.trans (hext₂.trans he₃), fun N ρ σ mem ctx v hcl hN hx hu hev hp hag => ?_⟩
            obtain ⟨va, vb, ha, hb, rfl⟩ := alu_lir ho hev
            obtain ⟨hlow, hval⟩ := hsome₂ m rfl
            obtain ⟨_, hmN⟩ := hlow N hcl
            obtain ⟨addr, vy, hy, haddr, hread⟩ := hval ρ mem ctx ((hp.right hst).left he₃)
            simp only [Lir.Arg.eval] at ha hb
            rw [ha] at hy
            cases hy
            have hag' := hag.mono hr₃
            have hb' := hag'.get (by simp [Inst.uses, xargsRegs, XArg.regs]) (vlow (bin_uses_right hu)) hb
            have hm := hag'.amode (fun u hu' => by simp [Inst.uses, xargsRegs, XArg.regs, hu']) hmN haddr
            have := exec_aluM (aluOf o) hw (x := dst) hb' hm (hread _ (Nat.le_refl _))
            rw [alu_comm _ (aluOf_sub ho hs)] at this
            exact hv₃ σ mem ctx st₀.next va vb _ vb hdst₁ (hdn hx hN) (low_trunc_wo w va) rfl
              (Computes.single this)
          | none =>
            obtain rfl := hnone₂ rfl
            sel_simp [Option.some.injEq] at h
            rw [bind_ok] at h
            obtain ⟨⟨a'', b''⟩, st₃, h₃, h⟩ := h
            obtain ⟨hn₃, hc₃, hab⟩ := tieOrder_spec h₃
            sel_simp [Option.some.injEq] at h
            obtain ⟨hn₄, hc₄, hr₄, hv₄⟩ := alu_close h
            refine ⟨hst.trans ((Ext.of_same hn₃ hc₃).trans ((Ext.fire c _ _).trans (Ext.of_same hn₄ hc₄))),
              fun N ρ σ mem ctx v hcl hN hx hu hev hp hag => ?_⟩
            obtain ⟨va, vb, ha, hb, rfl⟩ := alu_lir ho hev
            have hag' := hag.mono hr₄
            rcases hab with hab | hab <;> simp only [Prod.mk.injEq] at hab <;> obtain ⟨rfl, rfl⟩ := hab
            · have ha' := hag'.get (by simp [Inst.uses, xargsRegs, XArg.regs]) (vlow (bin_uses_left hu)) ha
              have hb' := hag'.get (by simp [Inst.uses, xargsRegs, XArg.regs]) (vlow (bin_uses_right hu)) hb
              exact hv₄ σ mem ctx st₀.next va vb va vb hdst₁ (hdn hx hN) rfl rfl
                (Computes.single (exec_aluR (aluOf o) hw ha' hb'))
            · have ha' := hag'.get (by simp [Inst.uses, xargsRegs, XArg.regs]) (vlow (bin_uses_left hu)) ha
              have hb' := hag'.get (by simp [Inst.uses, xargsRegs, XArg.regs]) (vlow (bin_uses_right hu)) hb
              have := exec_aluR (aluOf o) hw (x := dst) (mem := mem) (ctx := ctx) hb' ha'
              rw [alu_comm _ (aluOf_sub ho hs)] at this
              exact hv₄ σ mem ctx st₀.next va vb va vb hdst₁ (hdn hx hN) rfl rfl (Computes.single this)
    | imm k =>
      sel_simp [Option.some.injEq] at h
      rw [bind_ok] at h
      obtain ⟨body, st₁, h₁, h⟩ := h
      obtain ⟨hn₁, hc₁, hr₁, hv₁⟩ := aluImm_spec (aluOf o) hw h₁
      obtain ⟨hn₂, hc₂, hr₂, hv₂⟩ := alu_close h
      refine ⟨hst.trans ((Ext.of_le hn₁ hc₁).trans (Ext.of_same hn₂ hc₂)),
        fun N ρ σ mem ctx v hcl hN hx hu hev hp hag => ?_⟩
      obtain ⟨va, vb, ha, hb, rfl⟩ := alu_lir ho hev
      simp only [Lir.Arg.eval, Option.some.injEq] at hb
      subst hb
      have ha' := (hag.mono hr₂).get hr₁ (vlow (bin_uses_left hu)) ha
      exact hv₂ σ mem ctx st₀.next va _ va _ hdst₁ (hdn hx hN) rfl (trunc_low w _)
        ((hv₁ σ mem ctx va ha' (Nat.lt_of_lt_of_le (vlow (bin_uses_left hu)) (Nat.le_trans hN hst.next))).mono
          hst.next)
  | imm k =>
    cases b with
    | v b' =>
      sel_simp [Option.some.injEq] at h
      by_cases hs : o = .sub
      · subst hs
        sel_simp [beq_self_eq_true] at h
        rw [bind_ok] at h
        obtain ⟨⟨t, pre⟩, st₁, h₁, h⟩ := h
        sel_simp [Option.some.injEq] at h
        obtain ⟨rfl, hn₁, hc₁, hr₁, hv₁⟩ := materialize_spec h₁
        obtain ⟨hn₂, hc₂, hr₂, hv₂⟩ := alu_close h
        refine ⟨hst.trans ((Ext.of_le (by rw [hn₁]; exact Nat.le_succ _) hc₁).trans
          ((Ext.fire c _ _).trans (Ext.of_same hn₂ hc₂))), fun N ρ σ mem ctx v hcl hN hx hu hev hp hag => ?_⟩
        obtain ⟨va, vb, ha, hb, rfl⟩ := alu_lir ho hev
        simp only [Lir.Arg.eval, Option.some.injEq] at ha
        subst ha
        have hb' := (hag.mono hr₂).get (by simp [Inst.uses, xargsRegs, XArg.regs]) (vlow (bin_uses_right hu)) hb
        have hb'' : (σ.insert st.next k)[b']? = some vb := by
          rw [insert_ne]; exact hb'
          intro he
          have := vlow (bin_uses_right hu)
          have := Nat.le_trans hN hst.next
          vomega
        refine hv₂ σ mem ctx st₀.next k vb k vb hdst₁ (hdn hx hN) rfl rfl ?_
        exact Computes.append (hv₁ σ mem ctx) (insert_below hst.next)
          (Computes.single (exec_aluR (aluOf .sub) hw (by simp) hb''))
      · have hs₂ : (o == .sub) = false := by simpa using hs
        sel_simp [hs₂] at h
        rw [bind_ok] at h
        obtain ⟨body, st₁, h₁, h⟩ := h
        obtain ⟨hn₁, hc₁, hr₁, hv₁⟩ := aluImm_spec (aluOf o) hw h₁
        obtain ⟨hn₂, hc₂, hr₂, hv₂⟩ := alu_close h
        refine ⟨hst.trans ((Ext.fire c _ _).trans ((Ext.of_le hn₁ hc₁).trans (Ext.of_same hn₂ hc₂))),
          fun N ρ σ mem ctx v hcl hN hx hu hev hp hag => ?_⟩
        obtain ⟨va, vb, ha, hb, rfl⟩ := alu_lir ho hev
        simp only [Lir.Arg.eval, Option.some.injEq] at ha
        subst ha
        have hb' := (hag.mono hr₂).get hr₁ (vlow (bin_uses_right hu)) hb
        have := (hv₁ σ mem ctx vb hb' (Nat.lt_of_lt_of_le (vlow (bin_uses_right hu))
          (by simp; exact Nat.le_trans hN hst.next))).mono (by simpa using hst.next)
        rw [alu_comm _ (aluOf_sub ho hs)] at this
        exact hv₂ σ mem ctx st₀.next k vb _ vb hdst₁ (hdn hx hN) (trunc_low w k) rfl this
    | imm kb =>
      sel_simp [Option.some.injEq] at h
      rw [bind_ok] at h
      obtain ⟨⟨t, pre⟩, st₁, h₁, h⟩ := h
      rw [bind_ok] at h
      obtain ⟨body, st₂, h₂, h⟩ := h
      sel_simp [Option.some.injEq] at h
      obtain ⟨rfl, hn₁, hc₁, hr₁, hv₁⟩ := materialize_spec h₁
      obtain ⟨hn₂, hc₂, hr₂, hv₂⟩ := aluImm_spec (aluOf o) hw h₂
      obtain ⟨hn₃, hc₃, hr₃, hv₃⟩ := alu_close h
      refine ⟨hst.trans ((Ext.of_le (by rw [hn₁]; exact Nat.le_succ _) hc₁).trans
        ((Ext.of_le hn₂ hc₂).trans (Ext.of_same hn₃ hc₃))), fun N ρ σ mem ctx v hcl hN hx hu hev hp hag => ?_⟩
      obtain ⟨va, vb, ha, hb, rfl⟩ := alu_lir ho hev
      simp only [Lir.Arg.eval, Option.some.injEq] at ha hb
      subst ha hb
      refine hv₃ σ mem ctx st₀.next k kb k _ hdst₁ (hdn hx hN) rfl (trunc_low w kb) ?_
      exact Computes.append (hv₁ σ mem ctx) (insert_below hst.next)
        ((hv₂ (σ.insert st.next k) mem ctx k (by simp) (by rw [hn₁]; exact Nat.lt_succ_self _)).mono
          (by rw [hn₁]; exact Nat.le_succ_of_le hst.next))

theorem selectAlu_ok {i : Nat} {x : VReg} {o : Lir.BinOp} (ho : IsAlu o) {w : Width} {a b : Lir.Arg}
    {c : Ctx} {st st' : St} {is : List (Inst VReg)} (hi : c.pos = i)
    (h : selectAlu i x o w a b c st = .ok (is, st')) : AssignOk c st st' x (.bin o w a b) is := by
  have start : aluStart i x o w a b c st = .ok (is, st') → AssignOk c st st' x (.bin o w a b) is := by
    intro h
    unfold aluStart at h
    by_cases hn : narrowWidth w = true
    · sel_simp [hn] at h
      exact aluBody_ok (st₀ := st) (st := { st with next := st.next + 1 }) ho hi (fun h' => by simp [hn] at h')
        (fun _ => ⟨Nat.le_refl _, by simp⟩)
        (Ext.of_le (by simp) rfl) rfl h
    · sel_simp [hn] at h
      exact aluBody_ok ho hi (fun _ => rfl) (fun h' => absurd h' hn) (Ext.refl c _) rfl h
  rw [selectAlu_eq] at h
  by_cases hl : (w == .w64 && (o == .add || o == .sub)) = true
  · sel_simp [hl] at h
    rw [bind_ok] at h
    obtain ⟨r, st₁, h₁, h⟩ := h
    obtain ⟨hnone, hsome⟩ := leaAdd?_spec h₁
    cases r with
    | some out =>
      sel_simp [Option.some.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hw : w = .w64 := by simp only [Bool.and_eq_true, beq_iff_eq] at hl; exact hl.1
      subst hw
      exact hsome out rfl
    | none =>
      obtain rfl := hnone rfl
      sel_simp [Option.some.injEq] at h
      exact start h
  · sel_simp [hl] at h
    exact start h


/-! ## `imul` (rules 9 and 12) -/

/-- `selectMul` once its destination is chosen, as in `Select.Rules`. -/
def mulBody (i : Nat) (x : VReg) (w : X86.Width) (a b : Lir.Arg) (dst : VReg) : SelM (List (Inst VReg)) := do
  let narrow := narrowWidth w
  let wo := opWidth w
  let trunc (k : Word) : Word := if narrow then w.truncate k else k
  let rm := row .imul wo .RM
  let body ← match a, b with
    | .v a, .v b => do
        match ← sinkLoad? b i wo.bytes with
        | some m =>
            fire "imul.load"
            pure [.op rm [dst] [.r a, .m m]]
        | none =>
        match ← sinkLoad? a i wo.bytes with
        | some m =>
            fire "imul.load"
            pure [.op rm [dst] [.r b, .m m]]
        | none =>
            let (a, b) ← tieOrder a b
            fire "imul.rr"
            pure [.op rm [dst] [.r a, .r b]]
    | .v a, .imm k | .imm k, .v a => mulImm wo dst a (trunc k)
    | .imm ka, .imm kb => do
        let (t, pre) ← materialize ka
        pure (pre ++ (← mulImm wo dst t (trunc kb)))
  narrowed w x dst body

theorem selectMul_eq (i : Nat) (x : VReg) (w : X86.Width) (a b : Lir.Arg) :
    selectMul i x w a b = (do
      let dst ← if narrowWidth w then fresh else pure x
      mulBody i x w a b dst) := rfl

theorem mul_close {w : Width} {x dst : VReg} {body is : List (Inst VReg)} {c : Ctx} {st₁ st' : St}
    (h : narrowed w x dst body c st₁ = .ok (is, st')) :
    st'.next = st₁.next ∧ st'.consumed = st₁.consumed ∧ (∀ u ∈ readsOf body, u ∈ readsOf is) ∧
      ∀ σ mem ctx n va vb va' vb', (narrowWidth w = false → dst = x) → (narrowWidth w = true → n ≤ dst ∧ x < n) →
        w.truncate va' = w.truncate va → w.truncate vb' = w.truncate vb →
        Computes body σ mem ctx n dst ((opWidth w).truncate (va' * vb')) →
        Computes is σ mem ctx n x (w.truncate (va * vb)) := by
  obtain ⟨hn, hc, hr, hv⟩ := narrowed_spec h
  refine ⟨hn, hc, hr, fun σ mem ctx n va vb va' vb' hd₁ hd₂ ha hb hbody => ?_⟩
  have := hv σ mem ctx n _ hd₁ hd₂ hbody
  rwa [narrow_val, mul_congr ha hb] at this

theorem mul_lir {w : Width} {a b : Lir.Arg} {ρ : Env} {mem : X86.Memory} {ctx v : Word}
    (h : (Lir.Rhs.bin .mul w a b).eval ρ mem ctx = some v) :
    ∃ va vb, a.eval ρ = some va ∧ b.eval ρ = some vb ∧ v = w.truncate (va * vb) := by
  simp only [Lir.Rhs.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨va, ha, vb, hb, hv⟩ := h
  exact ⟨va, vb, ha, hb, (Option.some.inj hv).symm⟩

theorem mulBody_ok {i : Nat} {x : VReg} {w : Width} {a b : Lir.Arg} {dst : VReg}
    {c : Ctx} {st₀ st st' : St} {is : List (Inst VReg)} (hi : c.pos = i)
    (hdst₁ : narrowWidth w = false → dst = x) (hdst₂ : narrowWidth w = true → st₀.next ≤ dst ∧ dst < st.next)
    (hst : Ext c st₀ st) (hcs : st.consumed = st₀.consumed)
    (h : mulBody i x w a b dst c st = .ok (is, st')) :
    AssignOk c st₀ st' x (.bin .mul w a b) is := by
  have hw := opWidth_wide w
  have hdn : ∀ {N : Nat}, x < N → N ≤ st₀.next → narrowWidth w = true → st₀.next ≤ dst ∧ x < st₀.next :=
    fun hx hN hn => ⟨(hdst₂ hn).1, Nat.lt_of_lt_of_le hx hN⟩
  have vlow : ∀ {N : Nat} {y : VReg}, (∀ u ∈ (Lir.Arg.v y).uses, u < N) → y < N :=
    fun h => h _ (by simp [Lir.Arg.uses, Lir.Arg.vreg?])
  unfold mulBody at h
  cases a with
  | v a' =>
    cases b with
    | v b' =>
      sel_simp [Option.some.injEq] at h
      rw [bind_ok] at h
      obtain ⟨r₁, st₁, h₁, h⟩ := h
      obtain ⟨hext₁, hn₁, hnone₁, hsome₁⟩ := sinkLoad?_spec h₁ hi.symm
      cases r₁ with
      | some m =>
        sel_simp [Option.some.injEq] at h
        obtain ⟨hn₂, hc₂, hr₂, hv₂⟩ := mul_close h
        have he₂ : Ext c st₁ st' := (Ext.fire c _ _).trans (Ext.of_same hn₂ hc₂)
        refine ⟨hst.trans (hext₁.trans he₂), fun N ρ σ mem ctx v hcl hN hx hu hev hp hag => ?_⟩
        obtain ⟨va, vb, ha, hb, rfl⟩ := mul_lir hev
        obtain ⟨hlow, hval⟩ := hsome₁ m rfl
        obtain ⟨_, hmN⟩ := hlow N hcl
        obtain ⟨addr, vy, hy, haddr, hread⟩ := hval ρ mem ctx ((hp.right hst).left he₂)
        simp only [Lir.Arg.eval] at ha hb
        rw [hb] at hy
        cases hy
        have hag' := hag.mono hr₂
        have ha' := hag'.get (by simp [Inst.uses, xargsRegs, XArg.regs]) (vlow (bin_uses_left hu)) ha
        have hm := hag'.amode (fun u hu' => by simp [Inst.uses, xargsRegs, XArg.regs, hu']) hmN haddr
        exact hv₂ σ mem ctx st₀.next va vb va _ hdst₁ (hdn hx hN) rfl (low_trunc_wo w vb)
          (Computes.single (exec_imulM hw ha' hm (hread _ (Nat.le_refl _))))
      | none =>
        obtain rfl := hnone₁ rfl
        sel_simp [Option.some.injEq] at h
        rw [bind_ok] at h
        obtain ⟨r₂, st₂, h₂, h⟩ := h
        obtain ⟨hext₂, hn₂', hnone₂, hsome₂⟩ := sinkLoad?_spec h₂ hi.symm
        cases r₂ with
        | some m =>
          sel_simp [Option.some.injEq] at h
          obtain ⟨hn₃, hc₃, hr₃, hv₃⟩ := mul_close h
          have he₃ : Ext c st₂ st' := (Ext.fire c _ _).trans (Ext.of_same hn₃ hc₃)
          refine ⟨hst.trans (hext₂.trans he₃), fun N ρ σ mem ctx v hcl hN hx hu hev hp hag => ?_⟩
          obtain ⟨va, vb, ha, hb, rfl⟩ := mul_lir hev
          obtain ⟨hlow, hval⟩ := hsome₂ m rfl
          obtain ⟨_, hmN⟩ := hlow N hcl
          obtain ⟨addr, vy, hy, haddr, hread⟩ := hval ρ mem ctx ((hp.right hst).left he₃)
          simp only [Lir.Arg.eval] at ha hb
          rw [ha] at hy
          cases hy
          have hag' := hag.mono hr₃
          have hb' := hag'.get (by simp [Inst.uses, xargsRegs, XArg.regs]) (vlow (bin_uses_right hu)) hb
          have hm := hag'.amode (fun u hu' => by simp [Inst.uses, xargsRegs, XArg.regs, hu']) hmN haddr
          have := exec_imulM hw (x := dst) hb' hm (hread _ (Nat.le_refl _))
          rw [UInt64.mul_comm] at this
          exact hv₃ σ mem ctx st₀.next va vb _ vb hdst₁ (hdn hx hN) (low_trunc_wo w va) rfl (Computes.single this)
        | none =>
          obtain rfl := hnone₂ rfl
          sel_simp [Option.some.injEq] at h
          rw [bind_ok] at h
          obtain ⟨⟨a'', b''⟩, st₃, h₃, h⟩ := h
          obtain ⟨hn₃, hc₃, hab⟩ := tieOrder_spec h₃
          sel_simp [Option.some.injEq] at h
          obtain ⟨hn₄, hc₄, hr₄, hv₄⟩ := mul_close h
          refine ⟨hst.trans ((Ext.of_same hn₃ hc₃).trans ((Ext.fire c _ _).trans (Ext.of_same hn₄ hc₄))),
            fun N ρ σ mem ctx v hcl hN hx hu hev hp hag => ?_⟩
          obtain ⟨va, vb, ha, hb, rfl⟩ := mul_lir hev
          have hag' := hag.mono hr₄
          rcases hab with hab | hab <;> simp only [Prod.mk.injEq] at hab <;> obtain ⟨rfl, rfl⟩ := hab
          · have ha' := hag'.get (by simp [Inst.uses, xargsRegs, XArg.regs]) (vlow (bin_uses_left hu)) ha
            have hb' := hag'.get (by simp [Inst.uses, xargsRegs, XArg.regs]) (vlow (bin_uses_right hu)) hb
            exact hv₄ σ mem ctx st₀.next va vb va vb hdst₁ (hdn hx hN) rfl rfl
              (Computes.single (exec_imulR hw ha' hb'))
          · have ha' := hag'.get (by simp [Inst.uses, xargsRegs, XArg.regs]) (vlow (bin_uses_left hu)) ha
            have hb' := hag'.get (by simp [Inst.uses, xargsRegs, XArg.regs]) (vlow (bin_uses_right hu)) hb
            have := exec_imulR hw (x := dst) (mem := mem) (ctx := ctx) hb' ha'
            rw [UInt64.mul_comm] at this
            exact hv₄ σ mem ctx st₀.next va vb va vb hdst₁ (hdn hx hN) rfl rfl (Computes.single this)
    | imm k =>
      sel_simp [Option.some.injEq] at h
      rw [bind_ok] at h
      obtain ⟨body, st₁, h₁, h⟩ := h
      obtain ⟨hn₁, hc₁, hr₁, hv₁⟩ := mulImm_spec hw h₁
      obtain ⟨hn₂, hc₂, hr₂, hv₂⟩ := mul_close h
      refine ⟨hst.trans ((Ext.of_le hn₁ hc₁).trans (Ext.of_same hn₂ hc₂)),
        fun N ρ σ mem ctx v hcl hN hx hu hev hp hag => ?_⟩
      obtain ⟨va, vb, ha, hb, rfl⟩ := mul_lir hev
      simp only [Lir.Arg.eval, Option.some.injEq] at hb
      subst hb
      have ha' := (hag.mono hr₂).get hr₁ (vlow (bin_uses_left hu)) ha
      exact hv₂ σ mem ctx st₀.next va _ va _ hdst₁ (hdn hx hN) rfl (trunc_low w _)
        ((hv₁ σ mem ctx va ha' (Nat.lt_of_lt_of_le (vlow (bin_uses_left hu)) (Nat.le_trans hN hst.next))).mono
          hst.next)
  | imm k =>
    cases b with
    | v b' =>
      sel_simp [Option.some.injEq] at h
      rw [bind_ok] at h
      obtain ⟨body, st₁, h₁, h⟩ := h
      obtain ⟨hn₁, hc₁, hr₁, hv₁⟩ := mulImm_spec hw h₁
      obtain ⟨hn₂, hc₂, hr₂, hv₂⟩ := mul_close h
      refine ⟨hst.trans ((Ext.of_le hn₁ hc₁).trans (Ext.of_same hn₂ hc₂)),
        fun N ρ σ mem ctx v hcl hN hx hu hev hp hag => ?_⟩
      obtain ⟨va, vb, ha, hb, rfl⟩ := mul_lir hev
      simp only [Lir.Arg.eval, Option.some.injEq] at ha
      subst ha
      have hb' := (hag.mono hr₂).get hr₁ (vlow (bin_uses_right hu)) hb
      have := (hv₁ σ mem ctx vb hb' (Nat.lt_of_lt_of_le (vlow (bin_uses_right hu)) (Nat.le_trans hN hst.next))).mono
        hst.next
      rw [UInt64.mul_comm] at this
      exact hv₂ σ mem ctx st₀.next k vb _ vb hdst₁ (hdn hx hN) (trunc_low w k) rfl this
    | imm kb =>
      sel_simp [Option.some.injEq] at h
      rw [bind_ok] at h
      obtain ⟨⟨t, pre⟩, st₁, h₁, h⟩ := h
      rw [bind_ok] at h
      obtain ⟨body, st₂, h₂, h⟩ := h
      sel_simp [Option.some.injEq] at h
      obtain ⟨rfl, hn₁, hc₁, hr₁, hv₁⟩ := materialize_spec h₁
      obtain ⟨hn₂, hc₂, hr₂, hv₂⟩ := mulImm_spec hw h₂
      obtain ⟨hn₃, hc₃, hr₃, hv₃⟩ := mul_close h
      refine ⟨hst.trans ((Ext.of_le (by rw [hn₁]; exact Nat.le_succ _) hc₁).trans
        ((Ext.of_le hn₂ hc₂).trans (Ext.of_same hn₃ hc₃))), fun N ρ σ mem ctx v hcl hN hx hu hev hp hag => ?_⟩
      obtain ⟨va, vb, ha, hb, rfl⟩ := mul_lir hev
      simp only [Lir.Arg.eval, Option.some.injEq] at ha hb
      subst ha hb
      refine hv₃ σ mem ctx st₀.next k kb k _ hdst₁ (hdn hx hN) rfl (trunc_low w kb) ?_
      exact Computes.append (hv₁ σ mem ctx) (insert_below hst.next)
        ((hv₂ (σ.insert st.next k) mem ctx k (by simp) (by rw [hn₁]; exact Nat.lt_succ_self _)).mono
          (by rw [hn₁]; exact Nat.le_succ_of_le hst.next))

theorem selectMul_ok {i : Nat} {x : VReg} {w : Width} {a b : Lir.Arg} {c : Ctx} {st st' : St}
    {is : List (Inst VReg)} (hi : c.pos = i) (h : selectMul i x w a b c st = .ok (is, st')) :
    AssignOk c st st' x (.bin .mul w a b) is := by
  rw [selectMul_eq] at h
  by_cases hn : narrowWidth w = true
  · sel_simp [hn] at h
    exact mulBody_ok (st₀ := st) (st := { st with next := st.next + 1 }) hi (fun h' => by simp [hn] at h')
      (fun _ => ⟨Nat.le_refl _, by simp⟩) (Ext.of_le (by simp) rfl) rfl h
  · sel_simp [hn] at h
    exact mulBody_ok hi (fun _ => rfl) (fun h' => absurd h' hn) (Ext.refl c _) rfl h

end Compilatrix.Xv.Select.Proof
