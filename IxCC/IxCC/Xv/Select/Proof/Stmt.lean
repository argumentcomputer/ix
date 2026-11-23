import IxCC.Xv.Select.Proof.Shift

/-!
# Statement rules

`StmtOk c st st' s is`: the instructions `is` selected for the Lir statement
`s` (an assignment or a store) at the current site extend the selection
state with folds of the site, and, wherever `s` runs from `ρ` and `mem` to
`ρ'` and `mem'` (with the folded statements' values pending, and the Xv
environment holding the Lir values of the registers the instructions read),
they run from `σ` and `mem` to `mem'`, give each register `s` defines its
Lir value, and change no other register below the first fresh one.

- `selectBin_ok`, `selectAssign_ok`: each assignment rule (`AssignOk`).
- `selectStore_ok`: rule 8's address (folded unless the fold would reach a
  protected context cell) with `mov m, r` or `mov m, imm`; a store writes the
  low `w` bytes of its value, so an immediate with the same low bits is
  exact (`write?_congr`).
- `selectCall_spec`: a call's arguments in registers, immediates
  materialized before it.
-/

namespace IxCC.Xv.Select.Proof

open IxCC.Lir (VReg Word Env)
open IxCC.X86 (Width)
open IxCC.Xv.Select

/-! ## Stores write the low bytes -/


theorem byte_trunc {w : Width} {v v' : Word} (h : w.truncate v = w.truncate v') {k : Nat} (hk : k < w.bytes) :
    (v >>> UInt64.ofNat (8 * k)).toUInt8 = (v' >>> UInt64.ofNat (8 * k)).toUInt8 := by
  have hbits : w.bits = 8 * w.bytes := by cases w <;> rfl
  have hb8 : w.bytes ≤ 8 := by cases w <;> decide
  have hb : ∀ j, j < w.bits → v.toBitVec.getLsbD j = v'.toBitVec.getLsbD j := by
    intro j hj
    have := congrArg (fun z : Word => z.toBitVec.getLsbD j) h
    simp only [X86.Encode.truncate_bits, BitVec.getLsbD_setWidth] at this
    have hj64 : j < 64 := by omega
    simpa [hj, hj64] using this
  apply UInt8.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hmod : (UInt64.ofNat (8 * k)).toBitVec.toNat % 64 = 8 * k := by
    simp; omega
  simp only [UInt64.toBitVec_toUInt8, BitVec.getLsbD_setWidth, UInt64.toBitVec_shiftRight,
    BitVec.ushiftRight_eq', BitVec.toNat_umod, BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and]
  have e : (UInt64.ofNat (8 * k)).toBitVec.toNat % BitVec.toNat (64 : BitVec 64) = 8 * k := by
    simp; omega
  rw [e]
  exact hb _ (by omega)

theorem writeLittle_congr (mem : X86.Memory) (addr v v' : Word) :
    ∀ n, (∀ k < n, (v >>> UInt64.ofNat (8 * k)).toUInt8 = (v' >>> UInt64.ofNat (8 * k)).toUInt8) →
      mem.writeLittle addr v n = mem.writeLittle addr v' n
  | 0, _ => rfl
  | n + 1, h => by
      simp only [X86.Memory.writeLittle]
      rw [writeLittle_congr mem addr v v' n (fun k hk => h k (by omega)), h n (by omega)]

theorem write?_congr {mem : X86.Memory} {w : Width} {addr v v' : Word} (h : w.truncate v = w.truncate v') :
    mem.write? w addr v = mem.write? w addr v' := by
  unfold X86.Memory.write? X86.Memory.write
  rw [writeLittle_congr mem addr v v' w.bytes (fun k hk => byte_trunc h hk)]

/-! ## Binary operations and assignments -/

theorem selectBin_ok {i : Nat} {x : VReg} {o : Lir.BinOp} {w : Width} {a b : Lir.Arg} {c : Ctx} {st st' : St}
    {is : List (Inst VReg)} (hi : c.pos = i) (h : selectBin i x o w a b c st = .ok (is, st')) :
    AssignOk c st st' x (.bin o w a b) is := by
  unfold selectBin at h
  cases o
  · exact selectAlu_ok (.inl rfl) hi h
  · exact selectAlu_ok (.inr (.inl rfl)) hi h
  · exact selectAlu_ok (.inr (.inr (.inl rfl))) hi h
  · exact selectAlu_ok (.inr (.inr (.inr (.inl rfl)))) hi h
  · exact selectAlu_ok (.inr (.inr (.inr (.inr rfl)))) hi h
  · exact selectMul_ok hi h
  · exact selectShift_ok (.inl rfl) h
  · exact selectShift_ok (.inr (.inl rfl)) h
  · exact selectShift_ok (.inr (.inr rfl)) h
  · exact selectDiv_ok (rem := false) hi h
  · exact selectDiv_ok (rem := true) hi h

theorem selectAssign_ok {i : Nat} {x : VReg} {r : Lir.Rhs} {c : Ctx} {st st' : St} {is : List (Inst VReg)}
    (hi : c.pos = i) (h : selectAssign i x r c st = .ok (is, st')) : AssignOk c st st' x r is := by
  unfold selectAssign at h
  cases r with
  | arg a =>
    cases a with
    | v a =>
      sel_simp [Option.some.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact move_ok
    | imm k => exact movImm_ok h
  | bin o w a b => exact selectBin_ok hi h
  | load w e m => exact selectLoad_ok h
  | addr m => exact lea_ok h
  | select cond w a b t f => exact selectSelect_ok hi h
  | test cond w a b => exact selectTest_ok h
  | bsr64 a => exact selectBsr64_ok h

/-! ## Stores -/

/-- The store row once the address is chosen, as in `Select.Rules`. -/
def storeTail (w : X86.Width) (am : Amode VReg) (a : Lir.Arg) : SelM (List (Inst VReg)) :=
  match a with
  | .v y => do
      fire "store.reg"
      return [.op (row .mov w .MR) [] [.m am, .r y]]
  | .imm k =>
      match immFull? w k with
      | some c => do
          fire "store.imm"
          return [.op (row .mov w .MI) [] [.m am, .i c]]
      | none => do
          let (t, pre) ← materialize k
          fire "store.reg"
          return pre ++ [.op (row .mov w .MR) [] [.m am, .r t]]

theorem storeTail_ok {w : Width} {am : Amode VReg} {a : Lir.Arg} {c : Ctx} {st st' : St} {is : List (Inst VReg)}
    (h : storeTail w am a c st = .ok (is, st')) :
    st.next ≤ st'.next ∧ st'.consumed = st.consumed ∧ (∀ u ∈ am.regs, u ∈ readsOf is) ∧
      (∀ u ∈ a.uses, u ∈ readsOf is) ∧
      ∀ σ mem mem' ctx addr va, am.evalV σ ctx = some addr → a.eval σ = some va → (∀ u ∈ am.regs, u < st.next) →
        mem.write? w addr va = .ok mem' →
        ∃ σ', execSeq σ mem ctx is = some (σ', mem') ∧ ∀ u, u < st.next → σ'[u]? = σ[u]? := by
  unfold storeTail at h
  cases a with
  | v y =>
    sel_simp [Option.some.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨by simp, by simp, fun u hu => by simp [Inst.uses, xargsRegs, XArg.regs, hu],
      fun u hu => by simp [uses_v] at hu; simp [Inst.uses, xargsRegs, XArg.regs, hu], ?_⟩
    intro σ mem mem' ctx addr va hm hy _ hw
    exact ⟨σ, by rw [execSeq_singleton]; exact exec_storeR w hm hy hw, fun _ _ => rfl⟩
  | imm k =>
    cases hf : immFull? w k with
    | some c' =>
      sel_simp [hf] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨by simp, by simp, fun u hu => by simp [Inst.uses, xargsRegs, XArg.regs, hu],
        fun u hu => by simp [Lir.Arg.uses, Lir.Arg.vreg?] at hu, ?_⟩
      intro σ mem mem' ctx addr va hm hk _ hw
      simp only [Lir.Arg.eval, Option.some.injEq] at hk
      subst hk
      have hw' : mem.write? w addr c' = .ok mem' := by rw [write?_congr (immFull?_low hf)]; exact hw
      exact ⟨σ, by rw [execSeq_singleton]; exact exec_storeI w c' hm hw', fun _ _ => rfl⟩
    | none =>
      sel_simp [hf] at h
      rw [bind_ok] at h
      obtain ⟨⟨t, pre⟩, st₁, h₁, h⟩ := h
      sel_simp [Option.some.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨rfl, hn₁, hc₁, hr₁, hv₁⟩ := materialize_spec h₁
      refine ⟨by simp [hn₁], by simp [hc₁], fun u hu => by simp [hr₁, Inst.uses, xargsRegs, XArg.regs, hu],
        fun u hu => by simp [Lir.Arg.uses, Lir.Arg.vreg?] at hu, ?_⟩
      intro σ mem mem' ctx addr va hm hk hlow hw
      simp only [Lir.Arg.eval, Option.some.injEq] at hk
      subst hk
      have hm' : am.evalV (σ.insert st.next k) ctx = some addr :=
        evalV_congr (fun u hu v hv => by rw [insert_ne (by have := hlow u hu; vomega)]; exact hv) hm
      refine ⟨σ.insert st.next k, ?_, insert_below (Nat.le_refl _)⟩
      rw [execSeq_append (hv₁ σ mem ctx), execSeq_singleton]
      exact exec_storeR w hm' (by simp) hw


/-- What the instructions selected for a statement other than a call
guarantee. -/
def StmtOk (c : Ctx) (st st' : St) (s : Lir.Stmt) (is : List (Inst VReg)) : Prop :=
  Ext c st st' ∧ ∀ N (ρ σ ρ' : Env) mem mem' ctx, CtxLow c N → N ≤ st.next → (∀ u ∈ s.uses, u < N) →
    (∀ u ∈ s.defs, u < N) → s.exec ρ mem ctx = some (ρ', mem') → Pend c st st' ρ mem ctx →
    Agree N (readsOf is) ρ σ →
    ∃ σ', execSeq σ mem ctx is = some (σ', mem') ∧
      ∀ u, u < st.next → (u ∈ s.defs → σ'[u]? = ρ'[u]?) ∧ (u ∉ s.defs → σ'[u]? = σ[u]?)

theorem AssignOk.stmt {c : Ctx} {st st' : St} {x : VReg} {r : Lir.Rhs} {is : List (Inst VReg)}
    (h : AssignOk c st st' x r is) : StmtOk c st st' (.assign x r) is := by
  refine ⟨h.1, fun N ρ σ ρ' mem mem' ctx hcl hN hu hd hx hp hag => ?_⟩
  simp only [Lir.Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hx
  obtain ⟨v, hv, rfl, rfl⟩ := hx
  obtain ⟨σ', he, hxv, hu'⟩ := h.2 N ρ σ mem ctx v hcl hN (hd x (by simp [Lir.Stmt.defs]))
    (fun u hu'' => hu u (by simpa [Lir.Stmt.uses] using hu'')) hv hp hag
  refine ⟨σ', he, fun u hlt => ⟨fun hmem => ?_, fun hmem => hu' u hlt (by simpa [Lir.Stmt.defs] using hmem)⟩⟩
  simp only [Lir.Stmt.defs, List.mem_singleton] at hmem
  subst hmem
  simp [hxv]

theorem selectStore_ok {w : Width} {m : Lir.Addr} {a : Lir.Arg} {c : Ctx} {st st' : St} {is : List (Inst VReg)}
    (h : selectStore w m a c st = .ok (is, st')) : StmtOk c st st' (.store w m a) is := by
  have fin : ∀ (am : Amode VReg) (st₂ : St), Ext c st st₂ → st₂.next = st.next →
      (∀ N, CtxLow c N → (∀ u ∈ m.uses, u < N) → ∀ u ∈ am.regs, u < N) →
      (∀ (ρ : Env) mem ctx addr, m.eval ρ ctx = some addr → Pend c st st₂ ρ mem ctx → am.evalV ρ ctx = some addr) →
      storeTail w am a c st₂ = .ok (is, st') → StmtOk c st st' (.store w m a) is := by
    intro am st₂ hext hn hlow hval ht
    obtain ⟨hn₃, hc₃, hram, hra, hv₃⟩ := storeTail_ok ht
    refine ⟨hext.trans (Ext.of_le hn₃ hc₃), fun N ρ σ ρ' mem mem' ctx hcl hN hu hd hx hp hag => ?_⟩
    simp only [Lir.Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at hx
    obtain ⟨addr, haddr, va, hva, hx⟩ := hx
    split at hx
    · rename_i mem'' hw
      simp only [Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      have hmu : ∀ u ∈ m.uses, u < N := fun u hu' => hu u (by simp [Lir.Stmt.uses, hu'])
      have hau : ∀ u ∈ a.uses, u < N := fun u hu' => hu u (by simp [Lir.Stmt.uses, hu'])
      have hσm := hag.amode hram (hlow N hcl hmu) (hval ρ mem ctx addr haddr (hp.left (Ext.of_le hn₃ hc₃)))
      have hσa := hag.arg hra hau hva
      obtain ⟨σ', he, hab⟩ := hv₃ σ mem mem'' ctx addr va hσm hσa
        (fun u hu' => by rw [hn]; exact Nat.lt_of_lt_of_le (hlow N hcl hmu u hu') hN) hw
      exact ⟨σ', he, fun u hlt => ⟨fun hmem => by simp [Lir.Stmt.defs] at hmem,
        fun _ => hab u (by rw [hn]; exact hlt)⟩⟩
    · cases hx
  -- the address without folding
  have plain : ∀ {am : Amode VReg}, (Lin.ofAddr m).encode = some am → storeTail w am a c st = .ok (is, st') →
      StmtOk c st st' (.store w m a) is := fun he h =>
    fin _ st (Ext.refl c _) rfl (fun N _ hm => encode_low he (linLow_ofAddr hm))
      (fun ρ mem ctx addr hm _ => encode_val he (by rw [linVal_ofAddr]; exact hm)) h
  unfold selectStore at h
  rw [bind_ok] at h
  obtain ⟨⟨l, used⟩, st₁, h₁, h⟩ := h
  obtain ⟨rfl, hF⟩ := foldLin_spec h₁
  simp only at h
  cases he : l.encode with
  | some am =>
    by_cases hp : am.hitsProtectedCtx w.bytes = true
    · sel_simp [he, hp] at h
      cases he' : (Lin.ofAddr m).encode with
      | some am' =>
        sel_simp [he'] at h
        exact plain he' h
      | none =>
        sel_simp [he'] at h
        rw [bind_ok] at h
        obtain ⟨am', st₂, h₂, -⟩ := h
        exact absurd h₂ unsupported_ne
    · sel_simp [he, hp] at h
      rw [bind_ok] at h
      obtain ⟨u, st₂, h₂, h⟩ := h
      sel_simp [Option.some.injEq] at h
      obtain ⟨hn₂, hc₂⟩ := commitFold_spec h₂
      exact fin am st₂ (hF.ext hn₂ hc₂) hn₂ (fun N hcl hm => encode_low he (hF.low N hcl (linLow_ofAddr hm)))
        (fun ρ mem ctx addr hm hp' => encode_val he (hF.val ρ mem ctx addr (hF.pend hc₂ hp')
          (by rw [linVal_ofAddr]; exact hm))) h
  | none =>
    sel_simp [he] at h
    cases he' : (Lin.ofAddr m).encode with
    | some am' =>
      sel_simp [he'] at h
      exact plain he' h
    | none =>
      sel_simp [he'] at h
      rw [bind_ok] at h
      obtain ⟨am', st₂, h₂, -⟩ := h
      exact absurd h₂ unsupported_ne

/-! ## Multi-result limb primitives -/

private theorem limb_result {n : Nat} {r1 r2 : VReg} {v1 v2 : Word} {ρ σ σ' : Env}
    (h : ∀ u, u < n → σ'[u]? = ((σ.insert r1 v1).insert r2 v2)[u]?) :
    ∀ u, u < n → (u ∈ [r1, r2] → σ'[u]? = ((ρ.insert r1 v1).insert r2 v2)[u]?) ∧
      (u ∉ [r1, r2] → σ'[u]? = σ[u]?) := by
  intro u hlt
  rw [h u hlt]
  constructor
  · intro hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl
    · by_cases h12 : r2 = u
      · subst h12; simp
      · rw [insert_ne h12, insert_ne h12]; simp
    · simp
  · intro hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hmem
    rw [insert_ne (Ne.symm hmem.2), insert_ne (Ne.symm hmem.1)]

private theorem zero_lt_iff_ne (vc : Word) :
    (if (0 : Word) < vc then (1 : Word) else 0) = UInt64.ofNat (if vc == 0 then 0 else 1) := by
  by_cases h : vc = 0
  · subst h; decide
  · have hlt : (0 : Word) < vc := by
      rw [UInt64.lt_iff_toNat_lt]
      have : vc.toNat ≠ 0 := fun h0 => h (UInt64.toNat_inj.mp (by simpa using h0))
      simp; omega
    have hbeq : (vc == 0) = false := beq_false_of_ne h
    simp [hlt, hbeq]

private theorem addCarry_cout (va vb vc : Word) :
    let cin : Nat := if vc == 0 then 0 else 1
    ((0 : Word) + (if va + vb < va then 1 else 0)) +
        (if va + vb + UInt64.ofNat cin < va + vb then 1 else 0) =
      if 2 ^ 64 ≤ va.toNat + vb.toNat + cin then 1 else 0 := by
  intro cin
  have ha := va.toNat_lt_size
  have hb := vb.toNat_lt_size
  have hcin : cin = 0 ∨ cin = 1 := by simp only [cin]; split <;> simp
  simp only [UInt64.size] at ha hb
  rcases hcin with h0 | h1
  · simp only [h0, show UInt64.ofNat 0 = (0 : Word) from rfl]
    have hlt : ¬ (va + vb + (0 : Word) < va + vb) := by simp
    simp only [hlt, ↓reduceIte, UInt64.zero_add, UInt64.add_zero]
    by_cases hov : 2 ^ 64 ≤ va.toNat + vb.toNat
    · have h1 : va + vb < va := by
        simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_add]; omega
      simp [hov, h1]
    · have h1 : ¬ (va + vb < va) := by
        simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_add]; omega
      simp [hov, h1]
  · simp only [h1, show UInt64.ofNat 1 = (1 : Word) from rfl]
    have h1n : (1 : Word).toNat = 1 := rfl
    by_cases hov1 : 2 ^ 64 ≤ va.toNat + vb.toNat
    · have hlt1 : va + vb < va := by
        simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_add]; omega
      have hlt2 : ¬ (va + vb + (1 : Word) < va + vb) := by
        simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, h1n]; omega
      have hov : 2 ^ 64 ≤ va.toNat + vb.toNat + 1 := by omega
      simp [hlt1, hlt2, hov]
    · have hlt1 : ¬ (va + vb < va) := by
        simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_add]; omega
      by_cases hov2 : 2 ^ 64 ≤ va.toNat + vb.toNat + 1
      · have hlt2 : va + vb + (1 : Word) < va + vb := by
          simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, h1n]; omega
        simp [hlt1, hlt2, hov2]
      · have hlt2 : ¬ (va + vb + (1 : Word) < va + vb) := by
          simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, h1n]; omega
        simp [hlt1, hlt2, hov2]

private theorem subBorrow_bout (va vb vc : Word) :
    let bin : Nat := if vc == 0 then 0 else 1
    ((0 : Word) + (if va < vb then 1 else 0)) +
        (if va - vb < va - vb - UInt64.ofNat bin then 1 else 0) =
      if va.toNat < vb.toNat + bin then 1 else 0 := by
  intro bin
  have ha := va.toNat_lt_size
  have hb := vb.toNat_lt_size
  have hbin : bin = 0 ∨ bin = 1 := by simp only [bin]; split <;> simp
  simp only [UInt64.size] at ha hb
  rcases hbin with h0 | h1
  · simp only [h0, show UInt64.ofNat 0 = (0 : Word) from rfl]
    have hlt2 : ¬ (va - vb < va - vb - (0 : Word)) := by simp
    simp only [hlt2, ↓reduceIte, UInt64.zero_add, UInt64.add_zero]
    by_cases hlt1 : va.toNat < vb.toNat
    · have hlt1' : va < vb := UInt64.lt_iff_toNat_lt.mpr hlt1
      simp [hlt1, hlt1']
    · have hlt1' : ¬ (va < vb) := fun h => hlt1 (UInt64.lt_iff_toNat_lt.mp h)
      simp [hlt1, hlt1']
  · simp only [h1, show UInt64.ofNat 1 = (1 : Word) from rfl]
    have h1n : (1 : Word).toNat = 1 := rfl
    by_cases hlt1 : va.toNat < vb.toNat
    · have hlt1' : va < vb := UInt64.lt_iff_toNat_lt.mpr hlt1
      have hlt2 : ¬ (va - vb < va - vb - (1 : Word)) := by
        simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub, h1n]; omega
      have hbo : va.toNat < vb.toNat + 1 := by omega
      simp [hlt1', hlt2, hbo]
    · have hlt1' : ¬ (va < vb) := fun h => hlt1 (UInt64.lt_iff_toNat_lt.mp h)
      by_cases heq : va.toNat = vb.toNat
      · have hlt2 : va - vb < va - vb - (1 : Word) := by
          simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub, h1n]; omega
        have hbo : va.toNat < vb.toNat + 1 := by omega
        simp [hlt1', hlt2, hbo]
      · have hlt2 : ¬ (va - vb < va - vb - (1 : Word)) := by
          simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub, h1n]; omega
        have hbo : ¬ (va.toNat < vb.toNat + 1) := by omega
        simp [hlt1', hlt2, hbo]

theorem selectLimb_ok {i : Nat} {r1 r2 : VReg} {op : Lir.LimbOp} {c : Ctx} {st st' : St}
    {is : List (Inst VReg)} (hi : c.pos = i) (h : selectLimb i r1 r2 op c st = .ok (is, st')) :
    StmtOk c st st' (.limb r1 r2 op) is := by
  cases op with
  | mulWide64 a b =>
    have fallback : ∀ (st₀ : St), Ext c st st₀ → st₀.next = st.next →
        (do let (a', preA) ← argReg a; let (b', preB) ← argReg b; fire "limb.mulWide";
            return preA ++ preB ++ [Inst.op (X86.Op.mulM .w64) [r1, r2] [.r b', .r a']] : SelM _) c st₀ =
          .ok (is, st') →
        StmtOk c st st' (.limb r1 r2 (.mulWide64 a b)) is := by
      intro st₀ hext₀ hn₀ hf
      rw [bind_ok] at hf
      obtain ⟨⟨a', preA⟩, st₁, h₁, hf⟩ := hf
      rw [bind_ok] at hf
      obtain ⟨⟨b', preB⟩, st₂, h₂, hf⟩ := hf
      sel_simp [Option.some.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      obtain ⟨hn₁, hc₁, -, hua, hla, hva⟩ := argReg_spec h₁
      obtain ⟨hn₂, hc₂, -, hub, -, hvb⟩ := argReg_spec h₂
      refine ⟨hext₀.trans ((Ext.of_le hn₁ hc₁).trans ((Ext.of_le hn₂ hc₂).trans (Ext.fire c _ _))),
        fun N ρ σ ρ' mem mem' ctx hcl hN hu hd hx hp hag => ?_⟩
      simp only [Lir.Stmt.exec, Lir.LimbOp.eval, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨_, ⟨va, ha, vb, hb, rfl⟩, rfl, rfl⟩ := hx
      have hau : ∀ u ∈ a.uses, u < N := fun u hu' => hu u (by simp [Lir.Stmt.uses, Lir.LimbOp.uses, hu'])
      have hbu : ∀ u ∈ b.uses, u < N := fun u hu' => hu u (by simp [Lir.Stmt.uses, Lir.LimbOp.uses, hu'])
      have haσ : a.eval σ = some va := hag.arg
        (fun u hu' => by
          rw [readsOf_append]; exact List.mem_append_right _ (by simp [Inst.uses, xargsRegs, XArg.regs, hua u hu']))
        hau ha
      obtain ⟨σ₁, he₁, ha₁, hab₁⟩ := hva σ mem ctx va haσ
      have hbσ : b.eval σ₁ = some vb :=
        (hag.mono fun u hu' => by
          rw [readsOf_append]; exact List.mem_append_right _ (by simp [Inst.uses, xargsRegs, XArg.regs, hub u hu'])).above
            hab₁ (by rw [hn₀]; exact hN) |>.arg (fun _ hu' => hu') hbu hb
      obtain ⟨σ₂, he₂, hb₂, hab₂⟩ := hvb σ₁ mem ctx vb hbσ
      have ha₂ : σ₂[a']? = some va := by
        rw [hab₂ a' (hla fun u hu' => by rw [hn₀]; exact Nat.lt_of_lt_of_le (hau u hu') hN)]
        exact ha₁
      have hmul := exec_umul (lo := r1) (hi := r2) (factor := .r b') (mem := mem) (ctx := ctx) hb₂ (by simp) ha₂
      refine ⟨_, by rw [execSeq_append (by rw [execSeq_append he₁, he₂]), execSeq_singleton, hmul],
        limb_result fun u hlt => ?_⟩
      by_cases h2 : r2 = u
      · subst h2; simp
      · rw [insert_ne h2, insert_ne h2]
        by_cases h1 : r1 = u
        · subst h1; simp
        · rw [insert_ne h1, insert_ne h1, hab₂ u (Nat.lt_of_lt_of_le (by rw [hn₀]; exact hlt) hn₁),
            hab₁ u (by rw [hn₀]; exact hlt)]
    unfold selectLimb at h
    cases a with
    | imm ka =>
      sel_simp [Option.some.injEq] at h
      exact fallback st (Ext.refl c _) rfl h
    | v a' =>
      cases b with
      | imm kb =>
        sel_simp [Option.some.injEq] at h
        exact fallback st (Ext.refl c _) rfl h
      | v b' =>
        sel_simp [Option.some.injEq] at h
        rw [bind_ok] at h
        obtain ⟨r₁, st₁, h₁, h⟩ := h
        obtain ⟨hext₁, hn₁, hnone₁, hsome₁⟩ := sinkLoad?_spec h₁ hi.symm
        cases r₁ with
        | some m =>
          sel_simp [Option.some.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨hlow, hval⟩ := hsome₁ m rfl
          refine ⟨hext₁.trans (Ext.fire c _ _), fun N ρ σ ρ' mem mem' ctx hcl hN hu hd hx hp hag => ?_⟩
          simp only [Lir.Stmt.exec, Lir.LimbOp.eval, Option.bind_eq_bind, Option.bind_eq_some_iff,
            Option.some.injEq, Prod.mk.injEq] at hx
          obtain ⟨_, ⟨va, ha, vb, hb, rfl⟩, rfl, rfl⟩ := hx
          obtain ⟨_, hmN⟩ := hlow N hcl
          obtain ⟨addr, vy, hy, haddr, hread⟩ := hval ρ mem ctx (hp.left (Ext.fire c _ _))
          simp only [Lir.Arg.eval] at ha hb
          rw [hb] at hy; cases hy
          have hm := hag.amode (fun u hu' => by simp [Inst.uses, xargsRegs, XArg.regs, hu']) hmN haddr
          have hmf : (XArg.m m).valIn σ mem ctx .w64 = some vb :=
            valIn_m hm ((hread .w64 (Nat.le_refl _)).trans (by rw [X86.Encode.truncate64]))
          have haσ : σ[a']? = some va :=
            hag.get (by simp [Inst.uses, xargsRegs, XArg.regs]) (hu a' (by simp [Lir.Stmt.uses, Lir.LimbOp.uses, uses_v])) ha
          refine ⟨_, by rw [execSeq_singleton]; exact exec_umul hmf (by simp) haσ, limb_result fun _ _ => rfl⟩
        | none =>
          obtain rfl := hnone₁ rfl
          sel_simp [Option.some.injEq] at h
          rw [bind_ok] at h
          obtain ⟨r₂, st₂, h₂, h⟩ := h
          obtain ⟨hext₂, hn₂, hnone₂, hsome₂⟩ := sinkLoad?_spec h₂ hi.symm
          cases r₂ with
          | some m =>
            sel_simp [Option.some.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨hlow, hval⟩ := hsome₂ m rfl
            refine ⟨hext₂.trans (Ext.fire c _ _), fun N ρ σ ρ' mem mem' ctx hcl hN hu hd hx hp hag => ?_⟩
            simp only [Lir.Stmt.exec, Lir.LimbOp.eval, Option.bind_eq_bind, Option.bind_eq_some_iff,
              Option.some.injEq, Prod.mk.injEq] at hx
            obtain ⟨_, ⟨va, ha, vb, hb, rfl⟩, rfl, rfl⟩ := hx
            obtain ⟨_, hmN⟩ := hlow N hcl
            obtain ⟨addr, vy, hy, haddr, hread⟩ := hval ρ mem ctx (hp.left (Ext.fire c _ _))
            simp only [Lir.Arg.eval] at ha hb
            rw [ha] at hy; cases hy
            have hm := hag.amode (fun u hu' => by simp [Inst.uses, xargsRegs, XArg.regs, hu']) hmN haddr
            have hmf : (XArg.m m).valIn σ mem ctx .w64 = some va :=
              valIn_m hm ((hread .w64 (Nat.le_refl _)).trans (by rw [X86.Encode.truncate64]))
            have hbσ : σ[b']? = some vb :=
              hag.get (by simp [Inst.uses, xargsRegs, XArg.regs]) (hu b' (by simp [Lir.Stmt.uses, Lir.LimbOp.uses, uses_v])) hb
            have hmul := exec_umul (lo := r1) (hi := r2) hmf (by simp) hbσ
            rw [UInt64.mul_comm vb va, Nat.mul_comm vb.toNat va.toNat] at hmul
            refine ⟨_, by rw [execSeq_singleton]; exact hmul, limb_result fun _ _ => rfl⟩
          | none =>
            obtain rfl := hnone₂ rfl
            sel_simp [Option.some.injEq] at h
            exact fallback _ (Ext.refl c _) rfl h
  | divWide64 hiArg loArg d =>
    unfold selectLimb at h
    rw [bind_ok] at h
    obtain ⟨⟨hi', preHi⟩, st₁, h₁, h⟩ := h
    rw [bind_ok] at h
    obtain ⟨⟨lo', preLo⟩, st₂, h₂, h⟩ := h
    obtain ⟨hn₁, hc₁, -, huhi, hlhi, hvhi⟩ := argReg_spec h₁
    obtain ⟨hn₂, hc₂, -, hulo, hllo, hvlo⟩ := argReg_spec h₂
    have hext₁₂ : Ext c st st₂ := (Ext.of_le hn₁ hc₁).trans (Ext.of_le hn₂ hc₂)
    have tail : ∀ (divisor : XArg VReg) (preD : List (Inst VReg)) (st₃ : St), Ext c st₂ st₃ →
        (∀ N (ρ σ : Env) mem ctx vd, CtxLow c N → N ≤ st.next → (∀ u ∈ d.uses, u < N) → d.eval ρ = some vd →
          Pend c st₂ st₃ ρ mem ctx → Agree N (readsOf preD ++ divisor.regs) ρ σ →
          ∃ σ₃, execSeq σ mem ctx preD = some (σ₃, mem) ∧ (∀ u, u < st₂.next → σ₃[u]? = σ[u]?) ∧
            divisor.valIn σ₃ mem ctx .w64 = some vd) →
        (∀ k, divisor ≠ .i k) →
        is = preHi ++ preLo ++ preD ++ [.op (X86.Op.divM .w64) [r1, r2] [divisor, .r lo', .r hi']] →
        st' = fireSt "limb.divWide" st₃ →
        StmtOk c st st' (.limb r1 r2 (.divWide64 hiArg loArg d)) is := by
      intro divisor preD st₃ hext₃ hD hdi rfl rfl
      refine ⟨hext₁₂.trans (hext₃.trans (Ext.fire c _ _)), fun N ρ σ ρ' mem mem' ctx hcl hN hu hd hx hp hag => ?_⟩
      simp only [Lir.Stmt.exec, Lir.LimbOp.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at hx
      obtain ⟨⟨v1, v2⟩, ⟨vhi, hhi, vlo, hlo, vd, hd', hdiv⟩, hx⟩ := hx
      simp only [Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      split at hdiv
      · cases hdiv
      · rename_i hok
        simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or] at hok
        simp only [Option.some.injEq, Prod.mk.injEq] at hdiv
        obtain ⟨rfl, rfl⟩ := hdiv
        have hhiu : ∀ u ∈ hiArg.uses, u < N := fun u hu' => hu u (by simp [Lir.Stmt.uses, Lir.LimbOp.uses, hu'])
        have hlou : ∀ u ∈ loArg.uses, u < N := fun u hu' => hu u (by simp [Lir.Stmt.uses, Lir.LimbOp.uses, hu'])
        have hdu : ∀ u ∈ d.uses, u < N := fun u hu' => hu u (by simp [Lir.Stmt.uses, Lir.LimbOp.uses, hu'])
        have hreads : ∀ u, u = hi' ∨ u = lo' ∨ u ∈ readsOf preD ∨ u ∈ divisor.regs →
            u ∈ readsOf (preHi ++ preLo ++ preD ++ [.op (X86.Op.divM .w64) [r1, r2] [divisor, .r lo', .r hi']]) := by
          intro u hu'
          rcases hu' with rfl | rfl | hu' | hu'
          · rw [readsOf_append]; exact List.mem_append_right _ (by simp [Inst.uses, xargsRegs, XArg.regs])
          · rw [readsOf_append]; exact List.mem_append_right _ (by simp [Inst.uses, xargsRegs, XArg.regs])
          · rw [readsOf_append]; exact List.mem_append_left _ (by rw [readsOf_append]; exact List.mem_append_right _ hu')
          · rw [readsOf_append]; exact List.mem_append_right _ (by simp [Inst.uses, xargsRegs, hu'])
        have hhiσ : hiArg.eval σ = some vhi :=
          hag.arg (fun u hu' => hreads u (.inl (huhi u hu'))) hhiu hhi
        obtain ⟨σ₁, he₁, hhi₁, hab₁⟩ := hvhi σ mem ctx vhi hhiσ
        have hloσ : loArg.eval σ₁ = some vlo :=
          ((hag.mono fun u hu' => hreads u (.inr (.inl (hulo u hu')))).above hab₁ hN).arg
            (fun _ hu' => hu') hlou hlo
        obtain ⟨σ₂, he₂, hlo₂, hab₂⟩ := hvlo σ₁ mem ctx vlo hloσ
        have hab₁₂ : ∀ u, u < st.next → σ₂[u]? = σ[u]? := above_trans hab₁ hab₂ hn₁
        obtain ⟨σ₃, he₃, hab₃, hvd⟩ := hD N ρ σ₂ mem ctx vd hcl hN hdu hd'
          ((hp.right hext₁₂).left (Ext.fire c _ _))
          ((hag.mono fun u hu' => by
              rcases List.mem_append.1 hu' with hu' | hu'
              · exact hreads u (.inr (.inr (.inl hu')))
              · exact hreads u (.inr (.inr (.inr hu')))).above hab₁₂ hN)
        have hhi₃ : σ₃[hi']? = some vhi := by
          have hlt := hlhi fun u hu' => Nat.lt_of_lt_of_le (hhiu u hu') hN
          rw [hab₃ hi' (Nat.lt_of_lt_of_le hlt hn₂), hab₂ hi' hlt]; exact hhi₁
        have hlo₃ : σ₃[lo']? = some vlo := by
          have hlt := hllo fun u hu' => Nat.lt_of_lt_of_le (hlou u hu') (Nat.le_trans hN hn₁)
          rw [hab₃ lo' hlt]; exact hlo₂
        have hstep := exec_div (w := .w64) (.inr rfl) (q := r1) (r := r2) hvd hdi hlo₃ hhi₃
          (by simpa [X86.Encode.truncate64] using hok.1)
          (by simpa [X86.Encode.truncate64] using (Nat.lt_of_not_ge hok.2))
        simp only [divDividend, X86.Encode.truncate64, X86.Width.bits] at hstep
        refine ⟨_, by rw [execSeq_append (by rw [execSeq_append (by rw [execSeq_append he₁, he₂]), he₃]),
          execSeq_singleton, hstep], limb_result fun u hlt => ?_⟩
        by_cases h2 : r2 = u
        · subst h2; simp
        · rw [insert_ne h2, insert_ne h2]
          by_cases h1 : r1 = u
          · subst h1; simp
          · rw [insert_ne h1, insert_ne h1, hab₃ u (Nat.lt_of_lt_of_le hlt (Nat.le_trans hn₁ hn₂)), hab₁₂ u hlt]
    cases d with
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
        refine tail (.m m) [] (fireSt "limb.divWide.load" st₃) (hext₃.trans (Ext.fire c _ _)) ?_ (by simp) rfl rfl
        intro N ρ σ mem ctx vd hcl hN hdu hd' hp hag
        obtain ⟨_, hmN⟩ := hlow N hcl
        obtain ⟨addr, vy, hy, haddr, hread⟩ := hval ρ mem ctx (hp.left (Ext.fire c _ _))
        simp only [Lir.Arg.eval] at hd'
        rw [hd'] at hy; cases hy
        have hm := hag.amode (fun u hu' => by simp [XArg.regs, hu']) hmN haddr
        exact ⟨σ, rfl, fun _ _ => rfl, valIn_m hm ((hread .w64 (Nat.le_refl _)).trans (by rw [X86.Encode.truncate64]))⟩
      | none =>
        obtain rfl := hnone₃ rfl
        sel_simp [Option.some.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine tail (.r y) [] _ (Ext.refl c _) ?_ (by simp) rfl rfl
        intro N ρ σ mem ctx vd hcl hN hdu hd' hp hag
        exact ⟨σ, rfl, fun _ _ => rfl, hag.get (by simp [XArg.regs]) (hdu y (by simp [uses_v])) hd'⟩
    | imm k =>
      sel_simp [Option.some.injEq] at h
      rw [bind_ok] at h
      obtain ⟨⟨t, preD⟩, st₃, h₃, h⟩ := h
      sel_simp [Option.some.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨rfl, hn₃, hc₃, -, hv₃⟩ := materialize_spec h₃
      refine tail (.r st₂.next) preD st₃ (Ext.of_le (by rw [hn₃]; exact Nat.le_succ _) hc₃) ?_ (by simp) rfl rfl
      intro N ρ σ mem ctx vd hcl hN hdu hd' hp hag
      simp only [Lir.Arg.eval, Option.some.injEq] at hd'
      subst hd'
      exact ⟨_, hv₃ σ mem ctx, insert_below (Nat.le_refl _), by simp [XArg.valIn]⟩
  | addCarry64 a b cinArg =>
    unfold selectLimb at h
    rw [bind_ok] at h
    obtain ⟨⟨a', preA⟩, st₁, h₁, h⟩ := h
    rw [bind_ok] at h
    obtain ⟨⟨b', preB⟩, st₂, h₂, h⟩ := h
    rw [bind_ok] at h
    obtain ⟨⟨c', preC⟩, st₃, h₃, h⟩ := h
    sel_simp [Option.some.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hn₁, hc₁, -, hua, hla, hva⟩ := argReg_spec h₁
    obtain ⟨hn₂, hc₂, -, hub, hlb, hvb⟩ := argReg_spec h₂
    obtain ⟨hn₃, hc₃, -, huc, hlc, hvc⟩ := argReg_spec h₃
    have hst₁₂ : st.next ≤ st₂.next := Nat.le_trans hn₁ hn₂
    have hst₁₃ : st.next ≤ st₃.next := Nat.le_trans hst₁₂ hn₃
    refine ⟨(Ext.of_le hn₁ hc₁).trans ((Ext.of_le hn₂ hc₂).trans ((Ext.of_le hn₃ hc₃).trans
        (Ext.of_le (by simp; vomega) (by simp)))),
      fun N ρ σ ρ' mem mem' ctx hcl hN hu hd hx hp hag => ?_⟩
    simp only [Lir.Stmt.exec, Lir.LimbOp.eval, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq, Prod.mk.injEq] at hx
    obtain ⟨_, ⟨va, ha, vb, hb, vc, hc, rfl⟩, rfl, rfl⟩ := hx
    have hau : ∀ u ∈ a.uses, u < N := fun u hu' => hu u (by simp [Lir.Stmt.uses, Lir.LimbOp.uses, hu'])
    have hbu : ∀ u ∈ b.uses, u < N := fun u hu' => hu u (by simp [Lir.Stmt.uses, Lir.LimbOp.uses, hu'])
    have hcu : ∀ u ∈ cinArg.uses, u < N := fun u hu' => hu u (by simp [Lir.Stmt.uses, Lir.LimbOp.uses, hu'])
    have hreads : ∀ u, u = a' ∨ u = b' ∨ u = c' →
        u ∈ readsOf (preA ++ preB ++ preC ++ [
          .zero st₃.next,
          .op (row .add .w64 .MR) [st₃.next + 1] [.r a', .r b'],
          .fused (row .cmp .w64 .MR) [.r (st₃.next + 1), .r a'] (row .adc .w64 .MI8) [st₃.next + 1 + 1] [.r st₃.next, .i 0],
          .fused (row .cmp .w64 .MR) [.r st₃.next, .r c'] (row .adc .w64 .MI8) [r1] [.r (st₃.next + 1), .i 0],
          .fused (row .cmp .w64 .MR) [.r r1, .r (st₃.next + 1)] (row .adc .w64 .MI8) [r2] [.r (st₃.next + 1 + 1), .i 0]]) := by
      intro u hu'
      rw [readsOf_append]
      exact List.mem_append_right _ (by rcases hu' with rfl | rfl | rfl <;> simp [Inst.uses, xargsRegs, XArg.regs])
    have haσ : a.eval σ = some va := hag.arg (fun u hu' => hreads u (.inl (hua u hu'))) hau ha
    obtain ⟨σ₁, he₁, ha₁, hab₁⟩ := hva σ mem ctx va haσ
    have hbσ : b.eval σ₁ = some vb :=
      ((hag.mono fun u hu' => hreads u (.inr (.inl (hub u hu')))).above hab₁ hN).arg
        (fun _ hu' => hu') hbu hb
    obtain ⟨σ₂, he₂, hb₂, hab₂⟩ := hvb σ₁ mem ctx vb hbσ
    have hab₁₂ : ∀ u, u < st.next → σ₂[u]? = σ[u]? := above_trans hab₁ hab₂ hn₁
    have hcσ : cinArg.eval σ₂ = some vc :=
      ((hag.mono fun u hu' => hreads u (.inr (.inr (huc u hu')))).above hab₁₂ hN).arg
        (fun _ hu' => hu') hcu hc
    obtain ⟨σ₃, he₃, hc₃', hab₃⟩ := hvc σ₂ mem ctx vc hcσ
    have hab₁₃ : ∀ u, u < st.next → σ₃[u]? = σ[u]? := above_trans hab₁₂ hab₃ hst₁₂
    have haLt : a' < st₃.next := Nat.lt_of_lt_of_le (hla fun u hu' => Nat.lt_of_lt_of_le (hau u hu') hN) (Nat.le_trans hn₂ hn₃)
    have hbLt : b' < st₃.next := Nat.lt_of_lt_of_le (hlb fun u hu' => Nat.lt_of_lt_of_le (hbu u hu') (Nat.le_trans hN hn₁)) hn₃
    have hcLt : c' < st₃.next := hlc fun u hu' => Nat.lt_of_lt_of_le (hcu u hu') (Nat.le_trans hN hst₁₂)
    have hr1Lt : r1 < st₃.next := Nat.lt_of_lt_of_le (hd r1 (by simp [Lir.Stmt.defs])) (Nat.le_trans hN hst₁₃)
    have ha₃ : σ₃[a']? = some va := by
      rw [hab₃ a' (Nat.lt_of_lt_of_le (hla fun u hu' => Nat.lt_of_lt_of_le (hau u hu') hN) hn₂),
        hab₂ a' (hla fun u hu' => Nat.lt_of_lt_of_le (hau u hu') hN)]; exact ha₁
    have hb₃ : σ₃[b']? = some vb := by
      rw [hab₃ b' (hlb fun u hu' => Nat.lt_of_lt_of_le (hbu u hu') (Nat.le_trans hN hn₁))]; exact hb₂
    let z0 := st₃.next
    let s1 := st₃.next + 1
    let c1 := st₃.next + 1 + 1
    let σ₄ := σ₃.insert z0 0
    let σ₅ := σ₄.insert s1 (va + vb)
    let σ₆ := σ₅.insert c1 ((0 : Word) + (if va + vb < va then 1 else 0))
    let cin : Nat := if vc == 0 then 0 else 1
    let vsum := va + vb + UInt64.ofNat cin
    let vcout : Word := if 2 ^ 64 ≤ va.toNat + vb.toNat + cin then 1 else 0
    let σ₇ := σ₆.insert r1 vsum
    let σ₈ := σ₇.insert r2 vcout
    have hs4 : Inst.exec σ₃ mem ctx (.zero z0) = some (σ₄, mem) := exec_zero σ₃ mem ctx z0
    have hs5 : Inst.exec σ₄ mem ctx (.op (row .add .w64 .MR) [s1] [.r a', .r b']) = some (σ₅, mem) := by
      have := exec_aluR .add (.inr rfl) (x := s1) (mem := mem) (ctx := ctx)
        (by show σ₄[a']? = some va; rw [insert_ne (by vomega)]; exact ha₃)
        (by show σ₄[b']? = some vb; rw [insert_ne (by vomega)]; exact hb₃)
      simpa [σ₅, X86.Encode.truncate64, X86.AluOp.eval, X86.AluOp.mnemonic, row] using this
    have hs6 : Inst.exec σ₅ mem ctx
        (.fused (row .cmp .w64 .MR) [.r s1, .r a'] (row .adc .w64 .MI8) [c1] [.r z0, .i 0]) = some (σ₆, mem) := by
      have := exec_fusedCarry false (u := s1) (v := a') (x := c1) (src := z0) (mem := mem) (ctx := ctx)
        (by show σ₅[s1]? = some (va + vb); exact Std.HashMap.getElem?_insert_self)
        (by show σ₅[a']? = some va; rw [insert_ne (by vomega), insert_ne (by vomega)]; exact ha₃)
        (by show σ₅[z0]? = some 0; rw [insert_ne (by vomega)]; exact Std.HashMap.getElem?_insert_self)
      dsimp only [Bool.false_eq_true, ↓reduceIte, row] at this ⊢
      exact this
    have hs7 : Inst.exec σ₆ mem ctx
        (.fused (row .cmp .w64 .MR) [.r z0, .r c'] (row .adc .w64 .MI8) [r1] [.r s1, .i 0]) = some (σ₇, mem) := by
      have := exec_fusedCarry false (u := z0) (v := c') (x := r1) (src := s1) (mem := mem) (ctx := ctx)
        (by show σ₆[z0]? = some 0; rw [insert_ne (by vomega), insert_ne (by vomega)]; exact Std.HashMap.getElem?_insert_self)
        (by show σ₆[c']? = some vc; rw [insert_ne (by vomega), insert_ne (by vomega), insert_ne (by vomega)]; exact hc₃')
        (by show σ₆[s1]? = some (va + vb); rw [insert_ne (by vomega)]; exact Std.HashMap.getElem?_insert_self)
      dsimp only [Bool.false_eq_true, ↓reduceIte, row] at this ⊢
      rw [zero_lt_iff_ne] at this
      exact this
    have hs8 : Inst.exec σ₇ mem ctx
        (.fused (row .cmp .w64 .MR) [.r r1, .r s1] (row .adc .w64 .MI8) [r2] [.r c1, .i 0]) = some (σ₈, mem) := by
      have := exec_fusedCarry false (u := r1) (v := s1) (x := r2) (src := c1) (mem := mem) (ctx := ctx)
        (by show σ₇[r1]? = some vsum; exact Std.HashMap.getElem?_insert_self)
        (by show σ₇[s1]? = some (va + vb); rw [insert_ne (by vomega), insert_ne (by vomega)]; exact Std.HashMap.getElem?_insert_self)
        (by show σ₇[c1]? = some ((0 : Word) + (if va + vb < va then 1 else 0))
            rw [insert_ne (by vomega)]; exact Std.HashMap.getElem?_insert_self)
      have hvcout : ((0 : Word) + (if va + vb < va then 1 else 0)) +
          (if vsum < va + vb then 1 else 0) = vcout := addCarry_cout va vb vc
      dsimp only [Bool.false_eq_true, ↓reduceIte, row] at this ⊢
      rw [hvcout] at this
      exact this
    refine ⟨σ₈, ?_, limb_result fun u hlt => ?_⟩
    · rw [execSeq_append (by rw [execSeq_append (by rw [execSeq_append he₁, he₂]), he₃])]
      change execSeq σ₃ mem ctx [.zero z0,
        .op (row .add .w64 .MR) [s1] [.r a', .r b'],
        .fused (row .cmp .w64 .MR) [.r s1, .r a'] (row .adc .w64 .MI8) [c1] [.r z0, .i 0],
        .fused (row .cmp .w64 .MR) [.r z0, .r c'] (row .adc .w64 .MI8) [r1] [.r s1, .i 0],
        .fused (row .cmp .w64 .MR) [.r r1, .r s1] (row .adc .w64 .MI8) [r2] [.r c1, .i 0]] = some (σ₈, mem)
      simp only [execSeq, hs4, hs5, hs6, hs7, hs8, Option.bind_eq_bind, Option.bind_some]
    · by_cases h2 : r2 = u
      · subst h2; exact Std.HashMap.getElem?_insert_self.trans Std.HashMap.getElem?_insert_self.symm
      · rw [insert_ne h2, insert_ne h2]
        by_cases h1 : r1 = u
        · subst h1; exact Std.HashMap.getElem?_insert_self.trans Std.HashMap.getElem?_insert_self.symm
        · have huLt : u < st₃.next := Nat.lt_of_lt_of_le hlt hst₁₃
          rw [insert_ne h1, insert_ne h1]
          show σ₆[u]? = σ[u]?
          rw [insert_ne (by vomega), insert_ne (by vomega), insert_ne (by vomega), hab₁₃ u hlt]
  | subBorrow64 a b binArg =>
    unfold selectLimb at h
    rw [bind_ok] at h
    obtain ⟨⟨a', preA⟩, st₁, h₁, h⟩ := h
    rw [bind_ok] at h
    obtain ⟨⟨b', preB⟩, st₂, h₂, h⟩ := h
    rw [bind_ok] at h
    obtain ⟨⟨c', preC⟩, st₃, h₃, h⟩ := h
    sel_simp [Option.some.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hn₁, hc₁, -, hua, hla, hva⟩ := argReg_spec h₁
    obtain ⟨hn₂, hc₂, -, hub, hlb, hvb⟩ := argReg_spec h₂
    obtain ⟨hn₃, hc₃, -, huc, hlc, hvc⟩ := argReg_spec h₃
    have hst₁₂ : st.next ≤ st₂.next := Nat.le_trans hn₁ hn₂
    have hst₁₃ : st.next ≤ st₃.next := Nat.le_trans hst₁₂ hn₃
    refine ⟨(Ext.of_le hn₁ hc₁).trans ((Ext.of_le hn₂ hc₂).trans ((Ext.of_le hn₃ hc₃).trans
        (Ext.of_le (by simp; vomega) (by simp)))),
      fun N ρ σ ρ' mem mem' ctx hcl hN hu hd hx hp hag => ?_⟩
    simp only [Lir.Stmt.exec, Lir.LimbOp.eval, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq, Prod.mk.injEq] at hx
    obtain ⟨_, ⟨va, ha, vb, hb, vc, hc, rfl⟩, rfl, rfl⟩ := hx
    have hau : ∀ u ∈ a.uses, u < N := fun u hu' => hu u (by simp [Lir.Stmt.uses, Lir.LimbOp.uses, hu'])
    have hbu : ∀ u ∈ b.uses, u < N := fun u hu' => hu u (by simp [Lir.Stmt.uses, Lir.LimbOp.uses, hu'])
    have hcu : ∀ u ∈ binArg.uses, u < N := fun u hu' => hu u (by simp [Lir.Stmt.uses, Lir.LimbOp.uses, hu'])
    have hreads : ∀ u, u = a' ∨ u = b' ∨ u = c' →
        u ∈ readsOf (preA ++ preB ++ preC ++ [
          .zero st₃.next,
          .op (row .sub .w64 .MR) [st₃.next + 1] [.r a', .r b'],
          .fused (row .cmp .w64 .MR) [.r a', .r b'] (row .adc .w64 .MI8) [st₃.next + 1 + 1] [.r st₃.next, .i 0],
          .fused (row .cmp .w64 .MR) [.r st₃.next, .r c'] (row .sbb .w64 .MI8) [r1] [.r (st₃.next + 1), .i 0],
          .fused (row .cmp .w64 .MR) [.r (st₃.next + 1), .r r1] (row .adc .w64 .MI8) [r2] [.r (st₃.next + 1 + 1), .i 0]]) := by
      intro u hu'
      rw [readsOf_append]
      exact List.mem_append_right _ (by rcases hu' with rfl | rfl | rfl <;> simp [Inst.uses, xargsRegs, XArg.regs])
    have haσ : a.eval σ = some va := hag.arg (fun u hu' => hreads u (.inl (hua u hu'))) hau ha
    obtain ⟨σ₁, he₁, ha₁, hab₁⟩ := hva σ mem ctx va haσ
    have hbσ : b.eval σ₁ = some vb :=
      ((hag.mono fun u hu' => hreads u (.inr (.inl (hub u hu')))).above hab₁ hN).arg
        (fun _ hu' => hu') hbu hb
    obtain ⟨σ₂, he₂, hb₂, hab₂⟩ := hvb σ₁ mem ctx vb hbσ
    have hab₁₂ : ∀ u, u < st.next → σ₂[u]? = σ[u]? := above_trans hab₁ hab₂ hn₁
    have hcσ : binArg.eval σ₂ = some vc :=
      ((hag.mono fun u hu' => hreads u (.inr (.inr (huc u hu')))).above hab₁₂ hN).arg
        (fun _ hu' => hu') hcu hc
    obtain ⟨σ₃, he₃, hc₃', hab₃⟩ := hvc σ₂ mem ctx vc hcσ
    have hab₁₃ : ∀ u, u < st.next → σ₃[u]? = σ[u]? := above_trans hab₁₂ hab₃ hst₁₂
    have haLt : a' < st₃.next := Nat.lt_of_lt_of_le (hla fun u hu' => Nat.lt_of_lt_of_le (hau u hu') hN) (Nat.le_trans hn₂ hn₃)
    have hbLt : b' < st₃.next := Nat.lt_of_lt_of_le (hlb fun u hu' => Nat.lt_of_lt_of_le (hbu u hu') (Nat.le_trans hN hn₁)) hn₃
    have hcLt : c' < st₃.next := hlc fun u hu' => Nat.lt_of_lt_of_le (hcu u hu') (Nat.le_trans hN hst₁₂)
    have hr1Lt : r1 < st₃.next := Nat.lt_of_lt_of_le (hd r1 (by simp [Lir.Stmt.defs])) (Nat.le_trans hN hst₁₃)
    have ha₃ : σ₃[a']? = some va := by
      rw [hab₃ a' (Nat.lt_of_lt_of_le (hla fun u hu' => Nat.lt_of_lt_of_le (hau u hu') hN) hn₂),
        hab₂ a' (hla fun u hu' => Nat.lt_of_lt_of_le (hau u hu') hN)]; exact ha₁
    have hb₃ : σ₃[b']? = some vb := by
      rw [hab₃ b' (hlb fun u hu' => Nat.lt_of_lt_of_le (hbu u hu') (Nat.le_trans hN hn₁))]; exact hb₂
    let z0 := st₃.next
    let d1 := st₃.next + 1
    let b1 := st₃.next + 1 + 1
    let σ₄ := σ₃.insert z0 0
    let σ₅ := σ₄.insert d1 (va - vb)
    let σ₆ := σ₅.insert b1 ((0 : Word) + (if va < vb then 1 else 0))
    let bin : Nat := if vc == 0 then 0 else 1
    let vdiff := va - vb - UInt64.ofNat bin
    let vbout : Word := if va.toNat < vb.toNat + bin then 1 else 0
    let σ₇ := σ₆.insert r1 vdiff
    let σ₈ := σ₇.insert r2 vbout
    have hs4 : Inst.exec σ₃ mem ctx (.zero z0) = some (σ₄, mem) := exec_zero σ₃ mem ctx z0
    have hs5 : Inst.exec σ₄ mem ctx (.op (row .sub .w64 .MR) [d1] [.r a', .r b']) = some (σ₅, mem) := by
      have := exec_aluR .sub (.inr rfl) (x := d1) (mem := mem) (ctx := ctx)
        (by show σ₄[a']? = some va; rw [insert_ne (by vomega)]; exact ha₃)
        (by show σ₄[b']? = some vb; rw [insert_ne (by vomega)]; exact hb₃)
      simpa [σ₅, X86.Encode.truncate64, X86.AluOp.eval, X86.AluOp.mnemonic, row] using this
    have hs6 : Inst.exec σ₅ mem ctx
        (.fused (row .cmp .w64 .MR) [.r a', .r b'] (row .adc .w64 .MI8) [b1] [.r z0, .i 0]) = some (σ₆, mem) := by
      have := exec_fusedCarry false (u := a') (v := b') (x := b1) (src := z0) (mem := mem) (ctx := ctx)
        (by show σ₅[a']? = some va; rw [insert_ne (by vomega), insert_ne (by vomega)]; exact ha₃)
        (by show σ₅[b']? = some vb; rw [insert_ne (by vomega), insert_ne (by vomega)]; exact hb₃)
        (by show σ₅[z0]? = some 0; rw [insert_ne (by vomega)]; exact Std.HashMap.getElem?_insert_self)
      dsimp only [Bool.false_eq_true, ↓reduceIte, row] at this ⊢
      exact this
    have hs7 : Inst.exec σ₆ mem ctx
        (.fused (row .cmp .w64 .MR) [.r z0, .r c'] (row .sbb .w64 .MI8) [r1] [.r d1, .i 0]) = some (σ₇, mem) := by
      have := exec_fusedCarry true (u := z0) (v := c') (x := r1) (src := d1) (mem := mem) (ctx := ctx)
        (by show σ₆[z0]? = some 0; rw [insert_ne (by vomega), insert_ne (by vomega)]; exact Std.HashMap.getElem?_insert_self)
        (by show σ₆[c']? = some vc; rw [insert_ne (by vomega), insert_ne (by vomega), insert_ne (by vomega)]; exact hc₃')
        (by show σ₆[d1]? = some (va - vb); rw [insert_ne (by vomega)]; exact Std.HashMap.getElem?_insert_self)
      dsimp only [↓reduceIte, row] at this ⊢
      rw [zero_lt_iff_ne] at this
      exact this
    have hs8 : Inst.exec σ₇ mem ctx
        (.fused (row .cmp .w64 .MR) [.r d1, .r r1] (row .adc .w64 .MI8) [r2] [.r b1, .i 0]) = some (σ₈, mem) := by
      have := exec_fusedCarry false (u := d1) (v := r1) (x := r2) (src := b1) (mem := mem) (ctx := ctx)
        (by show σ₇[d1]? = some (va - vb); rw [insert_ne (by vomega), insert_ne (by vomega)]; exact Std.HashMap.getElem?_insert_self)
        (by show σ₇[r1]? = some vdiff; exact Std.HashMap.getElem?_insert_self)
        (by show σ₇[b1]? = some ((0 : Word) + (if va < vb then 1 else 0))
            rw [insert_ne (by vomega)]; exact Std.HashMap.getElem?_insert_self)
      have hvbout : ((0 : Word) + (if va < vb then 1 else 0)) +
          (if va - vb < vdiff then 1 else 0) = vbout := subBorrow_bout va vb vc
      dsimp only [Bool.false_eq_true, ↓reduceIte, row] at this ⊢
      rw [hvbout] at this
      exact this
    refine ⟨σ₈, ?_, limb_result fun u hlt => ?_⟩
    · rw [execSeq_append (by rw [execSeq_append (by rw [execSeq_append he₁, he₂]), he₃])]
      change execSeq σ₃ mem ctx [.zero z0,
        .op (row .sub .w64 .MR) [d1] [.r a', .r b'],
        .fused (row .cmp .w64 .MR) [.r a', .r b'] (row .adc .w64 .MI8) [b1] [.r z0, .i 0],
        .fused (row .cmp .w64 .MR) [.r z0, .r c'] (row .sbb .w64 .MI8) [r1] [.r d1, .i 0],
        .fused (row .cmp .w64 .MR) [.r d1, .r r1] (row .adc .w64 .MI8) [r2] [.r b1, .i 0]] = some (σ₈, mem)
      simp only [execSeq, hs4, hs5, hs6, hs7, hs8, Option.bind_eq_bind, Option.bind_some]
    · by_cases h2 : r2 = u
      · subst h2; exact Std.HashMap.getElem?_insert_self.trans Std.HashMap.getElem?_insert_self.symm
      · rw [insert_ne h2, insert_ne h2]
        by_cases h1 : r1 = u
        · subst h1; exact Std.HashMap.getElem?_insert_self.trans Std.HashMap.getElem?_insert_self.symm
        · have huLt : u < st₃.next := Nat.lt_of_lt_of_le hlt hst₁₃
          rw [insert_ne h1, insert_ne h1]
          show σ₆[u]? = σ[u]?
          rw [insert_ne (by vomega), insert_ne (by vomega), insert_ne (by vomega), hab₁₃ u hlt]

/-! ## Statements -/

theorem selectStmt_ok {i : Nat} {s : Lir.Stmt} {c : Ctx} {st st' : St} {is : List (Inst VReg)} (hi : c.pos = i)
    (hs : s.isCall = false) (h : selectStmt i s c st = .ok (is, st')) : StmtOk c st st' s is := by
  cases s with
  | assign x r => exact (selectAssign_ok hi h).stmt
  | limb r1 r2 op => exact selectLimb_ok hi h
  | store w m a => exact selectStore_ok h
  | call rs f as => simp [Lir.Stmt.isCall] at hs

/-- A call's arguments in registers, immediates materialized before it. -/
theorem selectCall_spec {i : Nat} {rs : List VReg} {f : Lir.FunId} {as : List Lir.Arg} {c : Ctx} {st st' : St}
    {is : List (Inst VReg)} (h : selectStmt i (.call rs f as) c st = .ok (is, st')) :
    ∃ vs pre, is = pre ++ [.call f vs rs] ∧ st.next ≤ st'.next ∧ st'.consumed = st.consumed ∧ readsOf pre = [] ∧
      (∀ u ∈ Lir.argsUses as, u ∈ vs) ∧
      ∀ σ mem ctx vals, (∀ u ∈ Lir.argsUses as, u < st.next) → Lir.evalArgs σ as = some vals →
        ∃ σ', execSeq σ mem ctx pre = some (σ', mem) ∧ readAll σ' vs = some vals ∧ ∀ u, u < st.next → σ'[u]? = σ[u]? := by
  simp only [selectStmt] at h
  rw [bind_ok] at h
  obtain ⟨⟨vs, pre⟩, st₁, h₁, h⟩ := h
  sel_simp [Option.some.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨hn, hc, hr, hu, -, hv⟩ := argRegs_spec h₁
  exact ⟨vs, pre, rfl, by simp [hn], by simp [hc], hr, hu, hv⟩

end IxCC.Xv.Select.Proof
