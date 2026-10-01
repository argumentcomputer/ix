import Compilatrix.Xv.Select.Proof.Producer

/-!
# Assignment rules: copies, immediates, addresses, loads, `select`, `test`

`AssignOk c st st' x r is`: the instructions `is` selected for `x := r` at
the current site extend the selection state with folds of the site, and,
wherever the Lir statement evaluates to `v` (with the folded statements'
values pending, and the Xv environment holding the Lir values of the
registers the instructions read), they run, put `v` in `x`, and change no
other register below the first fresh one (`Computes`).

This module proves it for the rules that are not binary operations: `move`,
rule 5's immediates, rule 8's `lea`, the loads (`mov`, `movzx`, and the
sign-extending `movzx; xor; add`), rule 10's fused `cmovcc` (with a folded
64-bit load as its source) and rule 11's fused `setcc`.
-/

namespace Compilatrix.Xv.Select.Proof

open Compilatrix.Lir (VReg Word Env)
open Compilatrix.X86 (Width)
open Compilatrix.Xv.Select

/-- What the instructions selected for `x := r` at the current site guarantee. -/
def AssignOk (c : Ctx) (st st' : St) (x : VReg) (r : Lir.Rhs) (is : List (Inst VReg)) : Prop :=
  Ext c st st' ∧ ∀ N (ρ σ : Env) mem ctx v, CtxLow c N → N ≤ st.next → x < N → (∀ u ∈ r.uses, u < N) →
    r.eval ρ mem ctx = some v → Pend c st st' ρ mem ctx → Agree N (readsOf is) ρ σ →
    Computes is σ mem ctx st.next x v

/-- A producer's decision survives writes to registers above its operands. -/
theorem Decides.above {op : X86.Op} {args : List (XArg VReg)} {cond : X86.Condition} {σ σ' : Env}
    {mem : X86.Memory} {ctx : Word} {b : Bool} {n : Nat} (h : Decides op args cond σ mem ctx b)
    (hb : ∀ u ∈ xargsRegs args, u < n) (hab : ∀ u, u < n → σ'[u]? = σ[u]?) : Decides op args cond σ' mem ctx b := by
  obtain ⟨k, w, form, a₁, a₂, v₁, v₂, rfl, hf, rfl, h₁, h₂, hfl⟩ := h
  refine ⟨k, w, form, a₁, a₂, v₁, v₂, rfl, hf, rfl, ?_, ?_, hfl⟩
  · rw [valIn_above (fun u hu => hb u (by simp [xargsRegs, hu])) hab]; exact h₁
  · rw [valIn_above (fun u hu => hb u (by simp [xargsRegs, hu])) hab]; exact h₂

theorem uses_v (y : VReg) : (Lir.Arg.v y).uses = [y] := rfl

theorem Rhs.uses_select {c : Lir.Cond} {w : Width} {a b t f : Lir.Arg} {u : VReg} :
    u ∈ (Lir.Rhs.select c w a b t f).uses ↔ u ∈ a.uses ∨ u ∈ b.uses ∨ u ∈ t.uses ∨ u ∈ f.uses := by
  simp [Lir.Rhs.uses, or_assoc]

/-! ## Copies and immediates -/

theorem move_ok {x a : VReg} {c : Ctx} {st : St} :
    AssignOk c st (fireSt "move" st) x (.arg (.v a)) [.move x a] := by
  refine ⟨Ext.fire c _ _, fun N ρ σ mem ctx v hcl hN hx hu hv hp hag => ?_⟩
  have ha : σ[a]? = some v := hag.get (by simp [Inst.uses]) (hu a (by simp [Lir.Rhs.uses, uses_v])) hv
  exact Computes.single (exec_move ha)

theorem movImm_ok {x : VReg} {k : Word} {c : Ctx} {st st' : St} {is : List (Inst VReg)}
    (h : movImm x k c st = .ok (is, st')) : AssignOk c st st' x (.arg (.imm k)) is := by
  obtain ⟨hn, hc, -, hv⟩ := movImm_spec h
  refine ⟨Ext.of_same hn hc, fun N ρ σ mem ctx v hcl hN hx hu hev hp hag => ?_⟩
  simp only [Lir.Rhs.eval, Lir.Arg.eval, Option.some.injEq] at hev
  subst hev
  refine ⟨σ.insert x k, hv σ mem ctx, by simp, fun u _ hne => insert_ne (Ne.symm hne)⟩

/-! ## Addresses (rule 8) -/

theorem lea_ok {x : VReg} {m : Lir.Addr} {c : Ctx} {st st' : St} {is : List (Inst VReg)}
    (h : (do let am ← buildAmode m; fire "lea.addr"; return [Inst.op leaRow [x] [.m am]] : SelM _) c st =
      .ok (is, st')) : AssignOk c st st' x (.addr m) is := by
  rw [bind_ok] at h
  obtain ⟨am, st₁, h₁, h⟩ := h
  sel_simp [Option.some.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨hext, hn, hlow, hval⟩ := buildAmode_spec h₁
  refine ⟨hext.trans (Ext.fire c _ _), fun N ρ σ mem ctx v hcl hN hx hu hev hp hag => ?_⟩
  simp only [Lir.Rhs.eval] at hev
  have hρ := hval ρ mem ctx v hev (hp.left (Ext.fire c _ _))
  have hσ := hag.amode (fun u hu => by simp [Inst.uses, xargsRegs, XArg.regs, hu])
    (hlow N hcl (fun u hu' => hu u (by simpa [Lir.Rhs.uses] using hu'))) hρ
  exact Computes.single (exec_lea hσ)

/-! ## Loads -/

/-- A loaded word, zero- or sign-extended. -/
def extWord (w : Width) : Lir.Ext → Word → Word
  | .zero, z => z
  | .sign, z => Lir.sext w z

theorem loadWord_inv {mem : X86.Memory} {w : Width} {e : Lir.Ext} {addr v : Word}
    (h : Lir.loadWord mem w e addr = some v) :
    ∃ z, mem.read? w addr = .ok z ∧ w.truncate z = z ∧ v = extWord w e z := by
  unfold Lir.loadWord at h
  cases hr : mem.read? w addr with
  | error f => simp [hr] at h
  | ok z =>
    simp only [hr, Option.some.injEq] at h
    have h' := read_prefix (Nat.le_refl _) hr
    rw [hr] at h'
    simp only [Except.ok.injEq] at h'
    refine ⟨z, rfl, h'.symm, ?_⟩
    cases e <;> simp [extWord, ← h]

/-- The sign bit of a narrow width. -/
def signBit (w : Width) : Word := UInt64.ofNat (2 ^ (w.bits - 1))

theorem signBit_lt {w : Width} (hw : w ≠ .w64) : (signBit w).toNat < 2 ^ 32 := by
  cases w <;> first | exact absurd rfl hw | decide

theorem norm_signBit {w : Width} (hw : w ≠ .w64) :
    Width.w32.truncate (X86.ImmKind.imm32.norm (signBit w)) = signBit w := by
  cases w <;> first | exact absurd rfl hw | rfl

theorem xor_signBit {w : Width} (hw : w ≠ .w64) {z : Word} (hz : z.toNat < 2 ^ w.bits) :
    Width.w32.truncate (z ^^^ X86.ImmKind.imm32.norm (signBit w)) = z ^^^ signBit w := by
  have hz32 : z.toNat < 2 ^ 32 := Nat.lt_of_lt_of_le hz (Nat.pow_le_pow_right (by decide)
    (by cases w <;> simp_all [Width.bits]))
  rw [truncate_xor, norm_signBit hw, truncate_eq_self (w := .w32) hz32]
  apply truncate_eq_self
  rw [UInt64.toNat_xor]
  exact Nat.xor_lt_two_pow hz32 (signBit_lt hw)

/-- The sign-extending tail after a zero-extending load into `t`:
`xor t', t, 2^(w−1); add x, t', −2^(w−1)`. -/
theorem sext_tail {w : Width} (hw : w ≠ .w64) {x t t' : VReg} {c : Ctx} {st₃ st' : St}
    {add : List (Inst VReg)} (h₃ : aluImm .add .w64 x t' (0 - signBit w) c st₃ = .ok (add, st'))
    (ht' : t' < st₃.next) (htt : t ≠ t') :
    st₃.next ≤ st'.next ∧ st'.consumed = st₃.consumed ∧
      t ∈ readsOf (.op (row .xor .w32 .MI) [t'] [.r t, .i (X86.ImmKind.imm32.norm (signBit w))] :: add) ∧
      ∀ σ mem ctx z, σ[t]? = some z → z.toNat < 2 ^ w.bits → ∀ n, n ≤ t' → n ≤ st₃.next →
        Computes (.op (row .xor .w32 .MI) [t'] [.r t, .i (X86.ImmKind.imm32.norm (signBit w))] :: add) σ mem ctx n x
          (Lir.sext w z) := by
  obtain ⟨hn, hc, -, hv⟩ := aluImm_spec .add (.inr rfl) h₃
  refine ⟨hn, hc, by simp [Inst.uses, xargsRegs, XArg.regs], fun σ mem ctx z hz hzl n hn₁ hn₂ => ?_⟩
  have hx1 : Inst.exec σ mem ctx (.op (row .xor .w32 .MI) [t'] [.r t, .i (X86.ImmKind.imm32.norm (signBit w))]) =
      some (σ.insert t' (z ^^^ signBit w), mem) := by
    have := exec_aluI .xor (w := .w32) (.inl rfl) (form := .MI) (.inr rfl) (X86.ImmKind.imm32.norm (signBit w)) hz
      (x := t') (mem := mem) (ctx := ctx)
    rw [show X86.AluOp.eval .xor z (X86.ImmKind.imm32.norm (signBit w)) = z ^^^ X86.ImmKind.imm32.norm (signBit w)
      from rfl, xor_signBit hw hzl] at this
    exact this
  have := (hv (σ.insert t' (z ^^^ signBit w)) mem ctx (z ^^^ signBit w) (by simp) ht').mono hn₂
  refine (Computes.append (is := [_]) (by rw [execSeq_singleton, hx1]) (insert_below hn₁) this).congr ?_
  rw [show X86.AluOp.eval .add (z ^^^ signBit w) (0 - signBit w) = (z ^^^ signBit w) + (0 - signBit w) from rfl,
    X86.Encode.truncate64]
  exact sext_xor_add hw hzl


theorem selectLoad_ok {x : VReg} {w : Width} {e : Lir.Ext} {m : Lir.Addr} {c : Ctx} {st st' : St}
    {is : List (Inst VReg)} (h : selectLoad x w e m c st = .ok (is, st')) : AssignOk c st st' x (.load w e m) is := by
  unfold selectLoad at h
  rw [bind_ok] at h
  obtain ⟨am, st₁, h₁, h⟩ := h
  obtain ⟨hext, hn, hlow, hval⟩ := buildAmode_spec h₁
  -- the address and the loaded word, in `σ`
  have addr_of : ∀ (st'' : St) N (ρ σ : Env) mem ctx v, Ext c st₁ st'' → CtxLow c N →
      (∀ u ∈ (Lir.Rhs.load w e m).uses, u < N) → (Lir.Rhs.load w e m).eval ρ mem ctx = some v →
      Pend c st st'' ρ mem ctx → (∀ u ∈ am.regs, u ∈ readsOf is) → Agree N (readsOf is) ρ σ →
      ∃ addr z, am.evalV σ ctx = some addr ∧ mem.read? w addr = .ok z ∧ w.truncate z = z ∧
        v = extWord w e z := by
    intro st'' N ρ σ mem ctx v he hcl hu hev hp hreads hag
    simp only [Lir.Rhs.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at hev
    obtain ⟨addr, haddr, hload⟩ := hev
    have hρ := hval ρ mem ctx addr haddr (hp.left he)
    have hσ := hag.amode hreads (hlow N hcl (fun u hu' => hu u (by simpa [Lir.Rhs.uses] using hu'))) hρ
    obtain ⟨z, hr, hz, rfl⟩ := loadWord_inv hload
    exact ⟨addr, z, hσ, hr, hz, rfl⟩
  cases w with
  | w64 =>
    sel_simp [Option.some.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨hext.trans (Ext.fire c _ _), fun N ρ σ mem ctx v hcl hN hx hu hev hp hag => ?_⟩
    obtain ⟨addr, z, hσ, hr, hz, hv⟩ := addr_of _ N ρ σ mem ctx v (Ext.fire c _ _) hcl hu hev hp
      (fun u hu => by simp [Inst.uses, xargsRegs, XArg.regs, hu]) hag
    refine Computes.single ((exec_movLoad (.inr rfl) hσ hr).trans ?_)
    cases e <;> simp [hv, extWord, Lir.sext]
  | w32 =>
    cases e with
    | zero =>
      sel_simp [Option.some.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨hext.trans (Ext.fire c _ _), fun N ρ σ mem ctx v hcl hN hx hu hev hp hag => ?_⟩
      obtain ⟨addr, z, hσ, hr, hz, hv⟩ := addr_of _ N ρ σ mem ctx v (Ext.fire c _ _) hcl hu hev hp
        (fun u hu => by simp [Inst.uses, xargsRegs, XArg.regs, hu]) hag
      refine Computes.single ((exec_movLoad (.inl rfl) hσ hr).trans ?_)
      simp [hv, hz, extWord]
    | sign =>
      sel_simp [Option.some.injEq] at h
      rw [bind_ok] at h
      obtain ⟨add, st₃, h₃, h⟩ := h
      sel_simp [Option.some.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hn₃, hc₃, -, hval₃⟩ := sext_tail (w := .w32) (t := st₁.next) (by decide) h₃ (by simp) (by simp)
      have hext' : Ext c st₁ (fireSt "load.sext" st₃) := Ext.of_le (by simp at hn₃ ⊢; vomega) (by simp [hc₃])
      refine ⟨hext.trans hext', fun N ρ σ mem ctx v hcl hN hx hu hev hp hag => ?_⟩
      obtain ⟨addr, z, hσ, hr, hz, hv⟩ := addr_of _ N ρ σ mem ctx v hext' hcl hu hev hp
        (fun u hu => by simp [Inst.uses, xargsRegs, XArg.regs, hu]) hag
      have hzl : z.toNat < 2 ^ Width.w32.bits := by rw [← hz]; exact truncate_lt _ _
      have h1 : Inst.exec σ mem ctx (.op (row .mov .w32 .RM) [st₁.next] [.m am]) = some (σ.insert st₁.next z, mem) := by
        exact (exec_movLoad (.inl rfl) hσ hr).trans (by rw [hz])
      refine Computes.append (is := [_]) (by rw [execSeq_singleton, h1]) (insert_below (Nat.le_of_eq hn.symm)) ?_
      have := hval₃ (σ.insert st₁.next z) mem ctx z (by simp) hzl st.next (by rw [← hn]; vomega)
        (by show st.next ≤ st₁.next + 1 + 1; vomega)
      simpa [hv, extWord, signBit] using this
  | w8 =>
    cases e with
    | zero =>
      sel_simp [Option.some.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨hext.trans (Ext.fire c _ _), fun N ρ σ mem ctx v hcl hN hx hu hev hp hag => ?_⟩
      obtain ⟨addr, z, hσ, hr, hz, hv⟩ := addr_of _ N ρ σ mem ctx v (Ext.fire c _ _) hcl hu hev hp
        (fun u hu => by simp [Inst.uses, xargsRegs, XArg.regs, hu]) hag
      refine Computes.single ((exec_movzxLoad (.inl rfl) hσ hr).trans ?_)
      simp [hv, hz, extWord]
    | sign =>
      sel_simp [Option.some.injEq] at h
      rw [bind_ok] at h
      obtain ⟨add, st₃, h₃, h⟩ := h
      sel_simp [Option.some.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hn₃, hc₃, -, hval₃⟩ := sext_tail (w := .w8) (t := st₁.next) (by decide) h₃ (by simp) (by simp)
      have hext' : Ext c st₁ (fireSt "load.sext" st₃) := Ext.of_le (by simp at hn₃ ⊢; vomega) (by simp [hc₃])
      refine ⟨hext.trans hext', fun N ρ σ mem ctx v hcl hN hx hu hev hp hag => ?_⟩
      obtain ⟨addr, z, hσ, hr, hz, hv⟩ := addr_of _ N ρ σ mem ctx v hext' hcl hu hev hp
        (fun u hu => by simp [Inst.uses, xargsRegs, XArg.regs, hu]) hag
      have hzl : z.toNat < 2 ^ Width.w8.bits := by rw [← hz]; exact truncate_lt _ _
      have h1 : Inst.exec σ mem ctx (.op (row .movzx .w32 .RM .w8) [st₁.next] [.m am]) =
          some (σ.insert st₁.next z, mem) := by
        exact (exec_movzxLoad (.inl rfl) hσ hr).trans (by rw [hz])
      refine Computes.append (is := [_]) (by rw [execSeq_singleton, h1]) (insert_below (Nat.le_of_eq hn.symm)) ?_
      have := hval₃ (σ.insert st₁.next z) mem ctx z (by simp) hzl st.next (by rw [← hn]; vomega)
        (by show st.next ≤ st₁.next + 1 + 1; vomega)
      simpa [hv, extWord, signBit] using this
  | w16 =>
    cases e with
    | zero =>
      sel_simp [Option.some.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨hext.trans (Ext.fire c _ _), fun N ρ σ mem ctx v hcl hN hx hu hev hp hag => ?_⟩
      obtain ⟨addr, z, hσ, hr, hz, hv⟩ := addr_of _ N ρ σ mem ctx v (Ext.fire c _ _) hcl hu hev hp
        (fun u hu => by simp [Inst.uses, xargsRegs, XArg.regs, hu]) hag
      refine Computes.single ((exec_movzxLoad (.inr rfl) hσ hr).trans ?_)
      simp [hv, hz, extWord]
    | sign =>
      sel_simp [Option.some.injEq] at h
      rw [bind_ok] at h
      obtain ⟨add, st₃, h₃, h⟩ := h
      sel_simp [Option.some.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hn₃, hc₃, -, hval₃⟩ := sext_tail (w := .w16) (t := st₁.next) (by decide) h₃ (by simp) (by simp)
      have hext' : Ext c st₁ (fireSt "load.sext" st₃) := Ext.of_le (by simp at hn₃ ⊢; vomega) (by simp [hc₃])
      refine ⟨hext.trans hext', fun N ρ σ mem ctx v hcl hN hx hu hev hp hag => ?_⟩
      obtain ⟨addr, z, hσ, hr, hz, hv⟩ := addr_of _ N ρ σ mem ctx v hext' hcl hu hev hp
        (fun u hu => by simp [Inst.uses, xargsRegs, XArg.regs, hu]) hag
      have hzl : z.toNat < 2 ^ Width.w16.bits := by rw [← hz]; exact truncate_lt _ _
      have h1 : Inst.exec σ mem ctx (.op (row .movzx .w32 .RM .w16) [st₁.next] [.m am]) =
          some (σ.insert st₁.next z, mem) := by
        exact (exec_movzxLoad (.inr rfl) hσ hr).trans (by rw [hz])
      refine Computes.append (is := [_]) (by rw [execSeq_singleton, h1]) (insert_below (Nat.le_of_eq hn.symm)) ?_
      have := hval₃ (σ.insert st₁.next z) mem ctx z (by simp) hzl st.next (by rw [← hn]; vomega)
        (by show st.next ≤ st₁.next + 1 + 1; vomega)
      simpa [hv, extWord, signBit] using this


/-! ## Fused `setcc` and `cmovcc` (rules 10 and 11) -/

theorem Agree.above {N n : Nat} {S : List VReg} {ρ σ σ' : Env} (h : Agree N S ρ σ)
    (hab : ∀ u, u < n → σ'[u]? = σ[u]?) (hN : N ≤ n) : Agree N S ρ σ' :=
  fun u hu hu' v hv => by rw [hab u (Nat.lt_of_lt_of_le hu' hN)]; exact h u hu hu' v hv

theorem above_trans {n n' : Nat} {σ σ' σ'' : Env} (h₁ : ∀ u, u < n → σ'[u]? = σ[u]?)
    (h₂ : ∀ u, u < n' → σ''[u]? = σ'[u]?) (hn : n ≤ n') : ∀ u, u < n → σ''[u]? = σ[u]? :=
  fun u hu => (h₂ u (Nat.lt_of_lt_of_le hu hn)).trans (h₁ u hu)

theorem selectTest_ok {x : VReg} {cond : Lir.Cond} {w : Width} {a b : Lir.Arg} {c : Ctx} {st st' : St}
    {is : List (Inst VReg)} (h : selectTest x cond w a b c st = .ok (is, st')) :
    AssignOk c st st' x (.test cond w a b) is := by
  unfold selectTest at h
  rw [bind_ok] at h
  obtain ⟨pr, st₁, h₁, h⟩ := h
  sel_simp [Option.some.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨hext, hr, hval⟩ := compareProducer_spec h₁
  refine ⟨hext.trans (Ext.fire c _ _), fun N ρ σ mem ctx v hcl hN hx hu hev hp hag => ?_⟩
  simp only [Lir.Rhs.eval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hev
  obtain ⟨va, ha, vb, hb, rfl⟩ := hev
  obtain ⟨σ', he, hab, -, hd⟩ := hval N ρ σ mem ctx va vb hcl hN
    (fun u hu' => hu u (by simp [Lir.Rhs.uses, hu'])) (fun u hu' => hu u (by simp [Lir.Rhs.uses, hu'])) ha hb
    (hp.left (Ext.fire c _ _)) (hag.mono fun u hu' => by simp [Inst.uses, hu'])
  exact Computes.append he hab (Computes.single (hd.setcc x))

theorem selectSelect_ok {i : Nat} {x : VReg} {cond : Lir.Cond} {w : Width} {a b t f : Lir.Arg} {c : Ctx}
    {st st' : St} {is : List (Inst VReg)} (hi : c.pos = i) (h : selectSelect i x cond w a b t f c st = .ok (is, st')) :
    AssignOk c st st' x (.select cond w a b t f) is := by
  unfold selectSelect at h
  rw [bind_ok] at h
  obtain ⟨pr, st₁, h₁, h⟩ := h
  rw [bind_ok] at h
  obtain ⟨⟨f', preF⟩, st₂, h₂, h⟩ := h
  obtain ⟨hextP, hrP, hvalP⟩ := compareProducer_spec h₁
  obtain ⟨hn₂, hc₂, hr₂, hu₂, hl₂, hv₂⟩ := argReg_spec h₂
  have hextP₂ : Ext c st st₂ := hextP.trans (Ext.of_le hn₂ hc₂)
  -- the common tail: the producer, `f`, then `t` in `t'` after `preT`, and the fused pair
  have tail : ∀ (t' : XArg VReg) (preT : List (Inst VReg)) (st₃ st' : St), Ext c st₂ st₃ → Ext c st₃ st' →
      st'.next = st₃.next →
      (∀ N (ρ σ : Env) mem ctx vt, CtxLow c N → N ≤ st.next → (∀ u ∈ t.uses, u < N) → t.eval ρ = some vt →
        Pend c st₂ st₃ ρ mem ctx → Agree N (readsOf preT ++ t'.regs) ρ σ →
        ∃ σ₃, execSeq σ mem ctx preT = some (σ₃, mem) ∧ (∀ u, u < st₂.next → σ₃[u]? = σ[u]?) ∧
          t'.valIn σ₃ mem ctx .w64 = some vt) →
      (∀ c', t' ≠ .i c') →
      AssignOk c st st' x (.select cond w a b t f)
        (pr.pre ++ preF ++ preT ++ [.fused pr.op pr.args (X86.Op.cmovRM pr.cond .w64) [x] [.r f', t']]) := by
    intro t' preT st₃ st' he₃ he' hn' hT hti
    refine ⟨hextP₂.trans (he₃.trans he'), fun N ρ σ mem ctx v hcl hN hx hu hev hp hag => ?_⟩
    simp only [Lir.Rhs.eval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hev
    obtain ⟨va, ha, vb, hb, vt, ht, vf, hf, rfl⟩ := hev
    have hfu : ∀ u ∈ f.uses, u < N := fun u hu' => hu u (by simp [Lir.Rhs.uses, hu'])
    have htu : ∀ u ∈ t.uses, u < N := fun u hu' => hu u (by simp [Lir.Rhs.uses, hu'])
    have hreads : ∀ u, u ∈ xargsRegs pr.args ∨ u = f' ∨ u ∈ readsOf preT ∨ u ∈ t'.regs →
        u ∈ readsOf (pr.pre ++ preF ++ preT ++ [.fused pr.op pr.args (X86.Op.cmovRM pr.cond .w64) [x] [.r f', t']]) := by
      intro u hu'
      have hlast : ∀ u ∈ (Inst.fused pr.op pr.args (X86.Op.cmovRM pr.cond .w64) [x] [.r f', t']).uses,
          u ∈ readsOf (pr.pre ++ preF ++ preT ++ [.fused pr.op pr.args (X86.Op.cmovRM pr.cond .w64) [x] [.r f', t']]) :=
        fun u hu' => by rw [readsOf_append]; exact List.mem_append_right _ (by simpa using hu')
      rcases hu' with hu' | hu' | hu' | hu'
      · exact hlast u (by simp only [Inst.uses]; exact List.mem_append_left _ hu')
      · exact hlast u (by simp only [Inst.uses]; exact List.mem_append_right _ (by simp [xargsRegs, XArg.regs, hu']))
      · rw [readsOf_append]
        exact List.mem_append_left _ (by rw [readsOf_append]; exact List.mem_append_right _ hu')
      · exact hlast u (by
          simp only [Inst.uses]
          exact List.mem_append_right _ (by
            simp only [xargsRegs, List.flatMap_cons, List.flatMap_nil, List.append_nil]
            exact List.mem_append_right _ hu'))
    -- the producer
    obtain ⟨σ₁, he₁, hab₁, hbd₁, hd₁⟩ := hvalP N ρ σ mem ctx va vb hcl hN
      (fun u hu' => hu u (by simp [Lir.Rhs.uses, hu'])) (fun u hu' => hu u (by simp [Lir.Rhs.uses, hu'])) ha hb
      (hp.left ((Ext.of_le hn₂ hc₂).trans (he₃.trans he'))) (hag.mono fun u hu' => hreads u (.inl hu'))
    -- `f`
    have hagf : Agree N [f'] ρ σ₁ := (hag.mono fun u hu' => hreads u (.inr (.inl (by simpa using hu')))).above
      hab₁ hN
    have hf' : f.eval σ₁ = some vf := hagf.arg (fun u hu' => by simp [hu₂ u hu']) hfu hf
    obtain ⟨σ₂, he₂, hy₂, hab₂⟩ := hv₂ σ₁ mem ctx vf hf'
    have hfl : f' < st₂.next := hl₂ fun u hu' => Nat.lt_of_lt_of_le (hfu u hu')
      (Nat.le_trans hN (Ext.next hextP))
    -- `t`
    have hst₂ : N ≤ st₂.next := Nat.le_trans hN (Ext.next hextP₂)
    obtain ⟨σ₃, he₃', hab₃, hvt⟩ := hT N ρ σ₂ mem ctx vt hcl hN htu ht
      ((hp.right hextP₂).left he')
      ((hag.mono fun u hu' => by
          rcases List.mem_append.1 hu' with hu' | hu'
          · exact hreads u (.inr (.inr (.inl hu')))
          · exact hreads u (.inr (.inr (.inr hu')))).above
        (above_trans hab₁ hab₂ (Ext.next hextP)) hN)
    -- the fused pair
    have hd₃ := hd₁.above hbd₁ (above_trans hab₂ hab₃ hn₂)
    have hf₃ : σ₃[f']? = some vf := by rw [hab₃ f' hfl]; exact hy₂
    have hx₃ := hd₃.cmov (x := x) hf₃ hvt hti
    refine Computes.append (is := pr.pre ++ preF ++ preT) ?_ ?_ (Computes.single hx₃)
    · rw [execSeq_append (is := pr.pre ++ preF) (by rw [execSeq_append he₁, he₂]), he₃']
    · intro u hu'
      rw [hab₃ u (Nat.lt_of_lt_of_le hu' (Ext.next hextP₂)), hab₂ u (Nat.lt_of_lt_of_le hu' (Ext.next hextP)),
        hab₁ u hu']
  cases t with
  | v y =>
    sel_simp [Option.some.injEq] at h
    rw [bind_ok] at h
    obtain ⟨r, st₃, h₃, h⟩ := h
    obtain ⟨hext₃, hn₃, hnone₃, hsome₃⟩ := sinkLoad?_spec h₃ hi.symm
    cases r with
    | some m =>
      sel_simp [Option.some.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hlow, hval⟩ := hsome₃ m rfl
      refine tail (.m m) [] st₃ _ hext₃ ((Ext.fire c _ _).trans (Ext.fire c _ _)) (by simp) ?_ (fun _ => by simp)
      intro N ρ σ mem ctx vt hcl hN htu ht hp hag
      obtain ⟨_, hmN⟩ := hlow N hcl
      obtain ⟨addr, vy, hy, haddr, hread⟩ := hval ρ mem ctx hp
      simp only [Lir.Arg.eval] at ht
      rw [ht] at hy
      cases hy
      have hm := hag.amode (fun u hu' => by simp [XArg.regs, hu']) hmN haddr
      exact ⟨σ, rfl, fun _ _ => rfl, valIn_m hm ((hread .w64 (Nat.le_refl _)).trans (by rw [X86.Encode.truncate64]))⟩
    | none =>
      obtain rfl := hnone₃ rfl
      sel_simp [Option.some.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine tail (.r y) [] _ _ (Ext.refl c _) (Ext.fire c _ _) (by simp) ?_ (fun _ => by simp)
      intro N ρ σ mem ctx vt hcl hN htu ht hp hag
      exact ⟨σ, rfl, fun _ _ => rfl, hag.get (by simp [XArg.regs]) (htu y (by simp [uses_v])) ht⟩
  | imm k =>
    sel_simp [Option.some.injEq] at h
    rw [bind_ok] at h
    obtain ⟨⟨y, preT⟩, st₃, h₃, h⟩ := h
    sel_simp [Option.some.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨rfl, hn₃, hc₃, hr₃, hv₃⟩ := materialize_spec h₃
    refine tail (.r st₂.next) preT st₃ _ (Ext.of_le (by rw [hn₃]; exact Nat.le_succ _) hc₃) (Ext.fire c _ _) (by simp)
      ?_ (fun _ => by simp)
    intro N ρ σ mem ctx vt hcl hN htu ht hp hag
    simp only [Lir.Arg.eval, Option.some.injEq] at ht
    subst ht
    exact ⟨_, hv₃ σ mem ctx, insert_below (Nat.le_refl _), by simp [XArg.valIn]⟩

end Compilatrix.Xv.Select.Proof
