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

/-! ## Statements -/

theorem selectStmt_ok {i : Nat} {s : Lir.Stmt} {c : Ctx} {st st' : St} {is : List (Inst VReg)} (hi : c.pos = i)
    (hs : s.isCall = false) (h : selectStmt i s c st = .ok (is, st')) : StmtOk c st st' s is := by
  cases s with
  | assign x r => exact (selectAssign_ok hi h).stmt
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
