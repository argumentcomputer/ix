import IxCC.Xv.Select.Proof.Helpers

/-!
# Flag producers decide their Lir conditions (rules 1–3)

`Decides op args cond σ mem ctx b`: the producer row is a `cmp` or `test`
row whose operands, read at its width in `σ` and memory, set flags on which
`cond` tests `b`. A branch (`execJcc`), a fused `cmovcc` and a fused `setcc`
then run as their consumers' semantics say (`Decides.jcc`, `Decides.cmov`,
`Decides.setcc`).

`ProducerOk`: whatever `compareProducer` (and `cmpProducer`, `testProducer`)
selects, its prefix runs, writing fresh registers only, and its row decides
the Lir condition on the operands' values, a folded load read through its
address (rule 3) and an immediate narrowed (rule 2) included.
-/

namespace IxCC.Xv.Select.Proof

open IxCC.Lir (VReg Word Env)
open IxCC.X86 (Width)
open IxCC.Xv.Select

/-! ## Deciding rows -/

/-- A `cmp` or `test` row decides `b` under `cond`. -/
def Decides (op : X86.Op) (args : List (XArg VReg)) (cond : X86.Condition) (σ : Env) (mem : X86.Memory)
    (ctx : Word) (b : Bool) : Prop :=
  ∃ (k : Prod) (w : Width) (form : X86.OpEn) (a₁ a₂ : XArg VReg) (v₁ v₂ : Word),
    op = { mn := k.mnemonic, w, form } ∧ k.FormOk form ∧ args = [a₁, a₂] ∧
      a₁.valIn σ mem ctx w = some v₁ ∧ a₂.valIn σ mem ctx w = some v₂ ∧ (k.flags w v₁ v₂).test cond = some b

theorem Decides.jcc {op : X86.Op} {args : List (XArg VReg)} {cond : X86.Condition} {σ : Env}
    {mem : X86.Memory} {ctx : Word} {b : Bool} (h : Decides op args cond σ mem ctx b) :
    execJcc op args [] cond σ mem ctx = some (σ, mem, b) := by
  obtain ⟨k, w, form, a₁, a₂, v₁, v₂, rfl, hf, rfl, h₁, h₂, hb⟩ := h
  exact execJcc_prod k hf h₁ h₂ hb

theorem Decides.cmov {op : X86.Op} {args : List (XArg VReg)} {cond : X86.Condition} {σ : Env}
    {mem : X86.Memory} {ctx : Word} {b : Bool} (h : Decides op args cond σ mem ctx b) {x f : VReg}
    {t : XArg VReg} {vf vt : Word} (hfv : σ[f]? = some vf) (htv : t.valIn σ mem ctx .w64 = some vt)
    (hti : ∀ c, t ≠ .i c) :
    Inst.exec σ mem ctx (.fused op args (X86.Op.cmovRM cond .w64) [x] [.r f, t]) =
      some (σ.insert x (if b then vt else vf), mem) := by
  obtain ⟨k, w, form, a₁, a₂, v₁, v₂, rfl, hf, rfl, h₁, h₂, hb⟩ := h
  exact exec_fusedCmov k hf h₁ h₂ hb hfv htv hti

theorem Decides.setcc {op : X86.Op} {args : List (XArg VReg)} {cond : X86.Condition} {σ : Env}
    {mem : X86.Memory} {ctx : Word} {b : Bool} (h : Decides op args cond σ mem ctx b) (x : VReg) :
    Inst.exec σ mem ctx (.fused op args (X86.Op.setccM cond) [x] []) = some (σ.insert x (if b then 1 else 0), mem) := by
  obtain ⟨k, w, form, a₁, a₂, v₁, v₂, rfl, hf, rfl, h₁, h₂, hb⟩ := h
  exact exec_fusedSetcc k hf h₁ h₂ hb x

theorem valIn_m {am : Amode VReg} {σ : Env} {mem : X86.Memory} {ctx : Word} {w : Width} {addr v : Word}
    (ha : am.evalV σ ctx = some addr) (hr : mem.read? w addr = .ok v) : (XArg.m am).valIn σ mem ctx w = some v := by
  simp [XArg.valIn, ha, hr, Except.toOption]

/-- A memory operand whose registers the instructions read evaluates in `σ` as in `ρ`. -/
theorem Agree.amode {N : Nat} {S : List VReg} {ρ σ : Env} (h : Agree N S ρ σ) {am : Amode VReg} {ctx addr : Word}
    (hs : ∀ u ∈ am.regs, u ∈ S) (hN : ∀ u ∈ am.regs, u < N) (ha : am.evalV ρ ctx = some addr) :
    am.evalV σ ctx = some addr :=
  evalV_congr (fun u hu v hv => h u (hs u hu) (hN u hu) v hv) ha

/-! ## Producer operands -/

theorem producerArgs_spec {mn : X86.Mnemonic} {w : Width} {a : XArg VReg} {b : Lir.Arg} {tag : String}
    {imm8 : Bool} {c : Ctx} {st st' : St} {p : X86.Op} {args : List (XArg VReg)} {pre : List (Inst VReg)}
    (h : producerArgs mn w a b tag imm8 c st = .ok ((p, args, pre), st')) :
    st.next ≤ st'.next ∧ st'.consumed = st.consumed ∧ readsOf pre = [] ∧
      ∃ form b', p = row mn w form ∧ args = [a, b'] ∧ (form = .MR ∨ (imm8 = true ∧ form = .MI8) ∨ form = .MI) ∧
        ((form = .MR ∧ ∃ y, b' = .r y) ∨ (form ≠ .MR ∧ ∃ k, b' = .i k)) ∧ (∀ u ∈ b.uses, u ∈ b'.regs) ∧
        (∀ u ∈ b'.regs, u ∈ b.uses ∨ u < st'.next) ∧
        ∀ σ mem ctx vb, (∀ u ∈ b.uses, u < st.next) → b.eval σ = some vb →
          ∃ σ', execSeq σ mem ctx pre = some (σ', mem) ∧ (∀ u, u < st.next → σ'[u]? = σ[u]?) ∧
            ∃ v', b'.valIn σ' mem ctx w = some v' ∧ w.truncate v' = w.truncate vb := by
  unfold producerArgs at h
  cases b with
  | v y =>
    sel_simp [Option.some.injEq] at h
    obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
    refine ⟨by simp, by simp, rfl, .MR, .r y, rfl, rfl, .inl rfl, .inl ⟨rfl, _, rfl⟩, ?_, ?_,
      fun σ mem ctx vb _ hv => ⟨σ, rfl, fun _ _ => rfl, vb, hv, rfl⟩⟩
    all_goals simp [Lir.Arg.uses, Lir.Arg.vreg?, XArg.regs]
  | imm k =>
    simp only at h
    cases h8 : (if imm8 = true then imm8? w k else none) with
    | some c' =>
      have ⟨hi, h8'⟩ : imm8 = true ∧ imm8? w k = some c' := by
        cases imm8 <;> simp_all
      sel_simp [h8] at h
      obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
      refine ⟨by simp, by simp, rfl, .MI8, .i c', rfl, rfl, .inr (.inl ⟨hi, rfl⟩), .inr ⟨by decide, _, rfl⟩,
        by simp [Lir.Arg.uses, Lir.Arg.vreg?], by simp [XArg.regs], fun σ mem ctx vb _ hv => ⟨σ, rfl, fun _ _ => rfl, c', rfl, ?_⟩⟩
      simp only [Lir.Arg.eval, Option.some.injEq] at hv
      subst hv
      exact imm8?_low h8'
    | none =>
      sel_simp [h8] at h
      cases hf : immFull? w k with
      | some c' =>
        sel_simp [hf] at h
        obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
        refine ⟨by simp, by simp, rfl, .MI, .i c', rfl, rfl, .inr (.inr rfl), .inr ⟨by decide, _, rfl⟩,
          by simp [Lir.Arg.uses, Lir.Arg.vreg?], by simp [XArg.regs], fun σ mem ctx vb _ hv => ⟨σ, rfl, fun _ _ => rfl, c', rfl, ?_⟩⟩
        simp only [Lir.Arg.eval, Option.some.injEq] at hv
        subst hv
        exact immFull?_low hf
      | none =>
        sel_simp [hf] at h
        rw [bind_ok] at h
        obtain ⟨⟨t, pre'⟩, st₁, h₁, h⟩ := h
        sel_simp [Option.some.injEq] at h
        obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
        obtain ⟨rfl, hn, hc, hr, hv⟩ := materialize_spec h₁
        refine ⟨by simp [hn], by simp [hc], hr, .MR, .r st.next, rfl, rfl, .inl rfl, .inl ⟨rfl, _, rfl⟩,
          by simp [Lir.Arg.uses, Lir.Arg.vreg?], by simp [XArg.regs, hn],
          fun σ mem ctx vb _ hvb => ⟨_, hv σ mem ctx, insert_below (Nat.le_refl _), k, ?_, ?_⟩⟩
        · simp [XArg.valIn]
        · simp only [Lir.Arg.eval, Option.some.injEq] at hvb
          rw [hvb]

/-- A `cmp` row's operands (`producerArgs .cmp`) decide whatever the `cmp`
flags of their values decide. -/
theorem cmpArgs_run {w : Width} {a : XArg VReg} {b : Lir.Arg} {tag : String} {c : Ctx} {st st' : St}
    {p : X86.Op} {args : List (XArg VReg)} {pre : List (Inst VReg)}
    (h : producerArgs .cmp w a b tag true c st = .ok ((p, args, pre), st')) :
    st.next ≤ st'.next ∧ st'.consumed = st.consumed ∧ readsOf pre = [] ∧
      (∀ u ∈ a.regs, u ∈ xargsRegs args) ∧ (∀ u ∈ b.uses, u ∈ xargsRegs args) ∧
      ∀ σ mem ctx vb v₁ cond bres, (∀ u ∈ a.regs, u < st.next) → (∀ u ∈ b.uses, u < st.next) →
        a.valIn σ mem ctx w = some v₁ → b.eval σ = some vb →
        (∀ v', w.truncate v' = w.truncate vb → (Prod.cmp.flags w v₁ v').test cond = some bres) →
        ∃ σ', execSeq σ mem ctx pre = some (σ', mem) ∧ (∀ u, u < st.next → σ'[u]? = σ[u]?) ∧
          (∀ u ∈ xargsRegs args, u < st'.next) ∧ Decides p args cond σ' mem ctx bres := by
  obtain ⟨hn, hc, hr, form, b', rfl, rfl, hform, -, hbu, hbr, hv⟩ := producerArgs_spec h
  refine ⟨hn, hc, hr, fun u hu => by simp [xargsRegs, hu], fun u hu => by simp [xargsRegs, hbu u hu], ?_⟩
  intro σ mem ctx vb v₁ cond bres hal hbl ha hb hflags
  obtain ⟨σ', he, hab, v', hv', hvt⟩ := hv σ mem ctx vb hbl hb
  refine ⟨σ', he, hab, ?_, .cmp, w, form, a, b', v₁, v', rfl, ?_, rfl, ?_, hv', hflags v' hvt⟩
  · intro u hu
    simp only [xargsRegs, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] at hu
    rcases hu with hu | hu
    · exact Nat.lt_of_lt_of_le (hal u hu) hn
    · rcases hbr u hu with h | h
      · exact Nat.lt_of_lt_of_le (hbl u h) hn
      · exact h
  · rcases hform with h | ⟨-, h⟩ | h <;> simp [Prod.FormOk, h]
  · rw [valIn_above hal hab]; exact ha

/-! ## Comparisons (rules 1 and 3) -/

/-- What a selected flag producer guarantees, for the Lir condition `holds`
on operands `a` and `b`. -/
def ProducerOk (c : Ctx) (st st' : St) (a b : Lir.Arg) (holds : Word → Word → Bool) (pr : Producer) : Prop :=
  Ext c st st' ∧ readsOf pr.pre = [] ∧
    ∀ N (ρ σ : Env) mem ctx va vb, CtxLow c N → N ≤ st.next → (∀ u ∈ a.uses, u < N) → (∀ u ∈ b.uses, u < N) →
      a.eval ρ = some va → b.eval ρ = some vb → Pend c st st' ρ mem ctx → Agree N (xargsRegs pr.args) ρ σ →
      ∃ σ', execSeq σ mem ctx pr.pre = some (σ', mem) ∧ (∀ u, u < st.next → σ'[u]? = σ[u]?) ∧
        (∀ u ∈ xargsRegs pr.args, u < st'.next) ∧ Decides pr.op pr.args pr.cond σ' mem ctx (holds va vb)

theorem v_uses (x : VReg) : (Lir.Arg.v x).uses = [x] := rfl
theorem imm_uses (k : Word) : (Lir.Arg.imm k).uses = [] := rfl

/-- The `cmp` with a sunk load in the r/m slot. -/
theorem cmp_sunk {cx : X86.Condition} {w : Width} {y : VReg} {other : Lir.Arg} {site : Nat} {c : Ctx}
    {st st₁ st' : St} {m : Amode VReg} {p : X86.Op} {args : List (XArg VReg)} {pre : List (Inst VReg)}
    (hs : sinkLoad? y site w.bytes c st = .ok (some m, st₁)) (hsite : site = c.pos)
    (hp : producerArgs .cmp w (.m m) other "cmp.mem" true c st₁ = .ok ((p, args, pre), st'))
    (holds : Word → Word → Bool)
    (hflags : ∀ vy vo v', w.truncate v' = w.truncate vo →
      (Prod.cmp.flags w (w.truncate vy) v').test cx = some (holds vy vo)) :
    Ext c st st' ∧ readsOf pre = [] ∧
      ∀ N (ρ σ : Env) mem ctx vy vo, CtxLow c N → N ≤ st.next → (∀ u ∈ other.uses, u < N) →
        ρ[y]? = some vy → other.eval ρ = some vo → Pend c st st' ρ mem ctx → Agree N (xargsRegs args) ρ σ →
        ∃ σ', execSeq σ mem ctx pre = some (σ', mem) ∧ (∀ u, u < st.next → σ'[u]? = σ[u]?) ∧
          (∀ u ∈ xargsRegs args, u < st'.next) ∧ Decides p args cx σ' mem ctx (holds vy vo) := by
  obtain ⟨hext, hn₁, -, hsome⟩ := sinkLoad?_spec hs hsite
  obtain ⟨hlow, hval⟩ := hsome m rfl
  obtain ⟨hn, hc, hr, hau, hbu, hrun⟩ := cmpArgs_run hp
  refine ⟨hext.trans (Ext.of_le hn hc), hr, ?_⟩
  intro N ρ σ mem ctx vy vo hcl hN hol hy ho hpend hag
  obtain ⟨_, hmN⟩ := hlow N hcl
  obtain ⟨addr, vy', hy', haddr, hread⟩ := hval ρ mem ctx (hpend.left (Ext.of_le hn hc))
  rw [hy] at hy'
  cases hy'
  have hm : m.evalV σ ctx = some addr :=
    hag.amode (fun u hu => hau u (by simpa [XArg.regs] using hu)) hmN haddr
  have hv₁ : (XArg.m m).valIn σ mem ctx w = some (w.truncate vy) := valIn_m hm (hread w (Nat.le_refl _))
  have ho' : other.eval σ = some vo := hag.arg (fun u hu => hbu u hu) hol ho
  have := hrun σ mem ctx vo (w.truncate vy) cx (holds vy vo)
    (fun u hu => Nat.lt_of_lt_of_le (hmN u (by simpa [XArg.regs] using hu)) (by rw [hn₁]; exact hN))
    (fun u hu => Nat.lt_of_lt_of_le (hol u hu) (by rw [hn₁]; exact hN)) hv₁ ho' (hflags vy vo)
  rw [hn₁] at this
  exact this


/-- The `cmp` with a register in the r/m slot. -/
theorem cmp_reg {cx : X86.Condition} {w : Width} {y : VReg} {other : Lir.Arg} {c : Ctx} {st st' : St}
    {p : X86.Op} {args : List (XArg VReg)} {pre : List (Inst VReg)}
    (hp : producerArgs .cmp w (.r y) other "cmp" true c st = .ok ((p, args, pre), st'))
    (holds : Word → Word → Bool)
    (hflags : ∀ vy vo v', w.truncate v' = w.truncate vo → (Prod.cmp.flags w vy v').test cx = some (holds vy vo)) :
    Ext c st st' ∧ readsOf pre = [] ∧ y ∈ xargsRegs args ∧
      ∀ N (ρ σ : Env) mem ctx vy vo, N ≤ st.next → y < st.next → (∀ u ∈ other.uses, u < N) →
        σ[y]? = some vy → other.eval ρ = some vo → Agree N (xargsRegs args) ρ σ →
        ∃ σ', execSeq σ mem ctx pre = some (σ', mem) ∧ (∀ u, u < st.next → σ'[u]? = σ[u]?) ∧
          (∀ u ∈ xargsRegs args, u < st'.next) ∧ Decides p args cx σ' mem ctx (holds vy vo) := by
  obtain ⟨hn, hc, hr, hau, hbu, hrun⟩ := cmpArgs_run hp
  refine ⟨Ext.of_le hn hc, hr, hau y (by simp [XArg.regs]), ?_⟩
  intro N ρ σ mem ctx vy vo hN hy hol hyv ho hag
  have ho' : other.eval σ = some vo := hag.arg (fun u hu => hbu u hu) hol ho
  exact hrun σ mem ctx vo vy cx (holds vy vo) (fun u hu => by simp [XArg.regs] at hu; subst hu; exact hy)
    (fun u hu => Nat.lt_of_lt_of_le (hol u hu) hN) (by simpa [XArg.valIn] using hyv) ho' (hflags vy vo)

/-- `test a, a` decides every comparison with zero. -/
theorem test_self {cx : X86.Condition} {cond : Lir.Cond} (hcx : condX86 cond = some cx) {w : Width} {y : VReg}
    {σ : Env} {mem : X86.Memory} {ctx vy : Word} (hy : σ[y]? = some vy) :
    Decides (row .test w .MR) [.r y, .r y] cx σ mem ctx (cond.holds w vy 0) :=
  ⟨.test, w, .MR, .r y, .r y, vy, vy, rfl, .inl rfl, rfl, hy, hy, test_self_test hcx w vy⟩

theorem test_self_swap {cx : X86.Condition} {cond : Lir.Cond} (hcx : condX86 cond = some cx) {w : Width} {y : VReg}
    {σ : Env} {mem : X86.Memory} {ctx vy : Word} (hy : σ[y]? = some vy) :
    Decides (row .test w .MR) [.r y, .r y] (swapCond cx) σ mem ctx (cond.holds w 0 vy) := by
  refine ⟨.test, w, .MR, .r y, .r y, vy, vy, rfl, .inl rfl, rfl, hy, hy, ?_⟩
  simp only [Prod.flags]
  rw [test_self_flags]
  exact cmp_swap_test hcx w 0 vy

theorem truncate_idem (w : Width) (z : Word) : w.truncate (w.truncate z) = w.truncate z :=
  truncate_truncate_le (Nat.le_refl _) z

theorem cmpProducer_spec {cx : X86.Condition} {cond : Lir.Cond} (hcx : condX86 cond = some cx) {w : Width}
    {a b : Lir.Arg} {site : Nat} {c : Ctx} {st st' : St} {pr : Producer}
    (h : cmpProducer cx w a b site c st = .ok (pr, st')) (hsite : site = c.pos) :
    ProducerOk c st st' a b (cond.holds w) pr := by
  -- the flag facts of each shape
  have fl_sunkA : ∀ vy vo v', w.truncate v' = w.truncate vo →
      (Prod.cmp.flags w (w.truncate vy) v').test cx = some (cond.holds w vy vo) := by
    intro vy vo v' hv
    rw [show Prod.cmp.flags w (w.truncate vy) v' = X86.ByteEval.aluFlags .sub w (w.truncate vy) v' from rfl,
      cmp_test hcx, holds_congr (truncate_idem w vy) hv]
  have fl_sunkB : ∀ vy vo v', w.truncate v' = w.truncate vo →
      (Prod.cmp.flags w (w.truncate vy) v').test (swapCond cx) = some (cond.holds w vo vy) := by
    intro vy vo v' hv
    rw [show Prod.cmp.flags w (w.truncate vy) v' = X86.ByteEval.aluFlags .sub w (w.truncate vy) v' from rfl,
      cmp_swap_test hcx, holds_congr hv (truncate_idem w vy)]
  have fl_reg : ∀ vy vo v', w.truncate v' = w.truncate vo →
      (Prod.cmp.flags w vy v').test cx = some (cond.holds w vy vo) := by
    intro vy vo v' hv
    rw [show Prod.cmp.flags w vy v' = X86.ByteEval.aluFlags .sub w vy v' from rfl, cmp_test hcx,
      holds_congr rfl hv]
  have fl_swap : ∀ vy vo v', w.truncate v' = w.truncate vo →
      (Prod.cmp.flags w vy v').test (swapCond cx) = some (cond.holds w vo vy) := by
    intro vy vo v' hv
    rw [show Prod.cmp.flags w vy v' = X86.ByteEval.aluFlags .sub w vy v' from rfl, cmp_swap_test hcx,
      holds_congr hv rfl]
  -- a `cmp` with a sunk operand
  have sunk : ∀ {y : VReg} {other : Lir.Arg} {st₀ st₁ : St} {m : Amode VReg} {cc : X86.Condition}
      (holds : Word → Word → Bool), sinkLoad? y site w.bytes c st₀ = .ok (some m, st₁) →
      (∀ vy vo v', w.truncate v' = w.truncate vo → (Prod.cmp.flags w (w.truncate vy) v').test cc = some (holds vy vo)) →
      (producerArgs .cmp w (.m m) other "cmp.mem" >>= fun x =>
        pure { pre := x.2.snd, op := x.fst, args := x.2.fst, cond := cc }) c st₁ = .ok (pr, st') →
      Ext c st₀ st' ∧ readsOf pr.pre = [] ∧
        ∀ N (ρ σ : Env) mem ctx vy vo, CtxLow c N → N ≤ st₀.next → (∀ u ∈ other.uses, u < N) →
          ρ[y]? = some vy → other.eval ρ = some vo → Pend c st₀ st' ρ mem ctx → Agree N (xargsRegs pr.args) ρ σ →
          ∃ σ', execSeq σ mem ctx pr.pre = some (σ', mem) ∧ (∀ u, u < st₀.next → σ'[u]? = σ[u]?) ∧
            (∀ u ∈ xargsRegs pr.args, u < st'.next) ∧
            Decides pr.op pr.args pr.cond σ' mem ctx (holds vy vo) := by
    intro y other st₀ st₁ m cc holds hs hfl hp
    rw [bind_ok] at hp
    obtain ⟨⟨p, args, pre⟩, st₂, h₂, hp⟩ := hp
    sel_simp [Option.some.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    exact cmp_sunk hs hsite h₂ holds hfl
  -- a `cmp` with a register in the r/m slot
  have reg : ∀ {y : VReg} {other : Lir.Arg} {st₀ : St} {cc : X86.Condition} (holds : Word → Word → Bool),
      (∀ vy vo v', w.truncate v' = w.truncate vo → (Prod.cmp.flags w vy v').test cc = some (holds vy vo)) →
      (producerArgs .cmp w (.r y) other "cmp" >>= fun x =>
        pure { pre := x.2.snd, op := x.fst, args := x.2.fst, cond := cc }) c st₀ = .ok (pr, st') →
      Ext c st₀ st' ∧ readsOf pr.pre = [] ∧ y ∈ xargsRegs pr.args ∧
        ∀ N (ρ σ : Env) mem ctx vy vo, N ≤ st₀.next → y < st₀.next → (∀ u ∈ other.uses, u < N) →
          σ[y]? = some vy → other.eval ρ = some vo → Agree N (xargsRegs pr.args) ρ σ →
          ∃ σ', execSeq σ mem ctx pr.pre = some (σ', mem) ∧ (∀ u, u < st₀.next → σ'[u]? = σ[u]?) ∧
            (∀ u ∈ xargsRegs pr.args, u < st'.next) ∧
            Decides pr.op pr.args pr.cond σ' mem ctx (holds vy vo) := by
    intro y other st₀ cc holds hfl hp
    rw [bind_ok] at hp
    obtain ⟨⟨p, args, pre⟩, st₂, h₂, hp⟩ := hp
    sel_simp [Option.some.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    exact cmp_reg h₂ holds hfl
  have vlow : ∀ {N : Nat} {y : VReg}, (∀ u ∈ (Lir.Arg.v y).uses, u < N) → y < N :=
    fun h => h _ (by simp [Lir.Arg.uses, Lir.Arg.vreg?])
  unfold cmpProducer at h
  cases a with
  | v a' =>
    cases b with
    | v b' =>
      sel_simp [Option.some.injEq] at h
      rw [bind_ok] at h
      obtain ⟨r₁, st₁, h₁, h⟩ := h
      cases r₁ with
      | some m =>
        sel_simp [Option.some.injEq] at h
        obtain ⟨hext, hr, hval⟩ := sunk (cond.holds w) h₁ fl_sunkA h
        exact ⟨hext, hr, fun N ρ σ mem ctx va vb hcl hN _ hbl ha hb hp hag =>
          hval N ρ σ mem ctx va vb hcl hN hbl ha hb hp hag⟩
      | none =>
        obtain ⟨-, -, hnone, -⟩ := sinkLoad?_spec h₁ hsite
        obtain rfl := hnone rfl
        sel_simp [Option.some.injEq] at h
        rw [bind_ok] at h
        obtain ⟨r₂, st₂, h₂, h⟩ := h
        cases r₂ with
        | some m =>
          sel_simp [Option.some.injEq] at h
          obtain ⟨hext, hr, hval⟩ := sunk (fun vy vo => cond.holds w vo vy) h₂ fl_sunkB h
          exact ⟨hext, hr, fun N ρ σ mem ctx va vb hcl hN hal _ ha hb hp hag =>
            hval N ρ σ mem ctx vb va hcl hN hal hb ha hp hag⟩
        | none =>
          obtain ⟨-, -, hnone, -⟩ := sinkLoad?_spec h₂ hsite
          obtain rfl := hnone rfl
          sel_simp [Option.some.injEq] at h
          obtain ⟨hext, hr, hy, hval⟩ := reg (cond.holds w) fl_reg h
          refine ⟨hext, hr, fun N ρ σ mem ctx va vb hcl hN hal hbl ha hb hp hag => ?_⟩
          exact hval N ρ σ mem ctx va vb hN (Nat.lt_of_lt_of_le (vlow hal) hN) hbl
            (hag.get hy (vlow hal) ha) hb hag
    | imm k =>
      sel_simp [Option.some.injEq] at h
      rw [bind_ok] at h
      obtain ⟨r₁, st₁, h₁, h⟩ := h
      cases r₁ with
      | some m =>
        sel_simp [Option.some.injEq] at h
        obtain ⟨hext, hr, hval⟩ := sunk (cond.holds w) h₁ fl_sunkA h
        exact ⟨hext, hr, fun N ρ σ mem ctx va vb hcl hN _ hbl ha hb hp hag =>
          hval N ρ σ mem ctx va vb hcl hN hbl ha hb hp hag⟩
      | none =>
        obtain ⟨-, -, hnone, -⟩ := sinkLoad?_spec h₁ hsite
        obtain rfl := hnone rfl
        sel_simp [Option.some.injEq] at h
        by_cases hk : (w.truncate k == 0) = true
        · sel_simp [hk] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨Ext.fire c _ _, rfl, fun N ρ σ mem ctx va vb hcl hN hal hbl ha hb hp hag =>
            ⟨σ, rfl, fun _ _ => rfl, fun u hu => ?_, ?_⟩⟩
          · simp [xargsRegs, XArg.regs] at hu
            subst hu
            exact Nat.lt_of_lt_of_le (vlow hal) (by simpa using hN)
          simp only [Lir.Arg.eval, Option.some.injEq] at hb
          subst hb
          have hk' : w.truncate 0 = w.truncate k := by simp only [beq_iff_eq] at hk; rw [hk, truncate_zero]
          rw [← holds_congr rfl hk']
          exact test_self hcx (hag.get (by simp [xargsRegs, XArg.regs]) (vlow hal) ha)
        · sel_simp [hk] at h
          obtain ⟨hext, hr, hy, hval⟩ := reg (cond.holds w) fl_reg h
          refine ⟨hext, hr, fun N ρ σ mem ctx va vb hcl hN hal hbl ha hb hp hag => ?_⟩
          exact hval N ρ σ mem ctx va vb hN (Nat.lt_of_lt_of_le (vlow hal) hN) hbl
            (hag.get hy (vlow hal) ha) hb hag
  | imm ka =>
    cases b with
    | v b' =>
      sel_simp [Option.some.injEq] at h
      rw [bind_ok] at h
      obtain ⟨r₂, st₂, h₂, h⟩ := h
      cases r₂ with
      | some m =>
        sel_simp [Option.some.injEq] at h
        obtain ⟨hext, hr, hval⟩ := sunk (fun vy vo => cond.holds w vo vy) h₂ fl_sunkB h
        exact ⟨hext, hr, fun N ρ σ mem ctx va vb hcl hN hal _ ha hb hp hag =>
          hval N ρ σ mem ctx vb va hcl hN hal hb ha hp hag⟩
      | none =>
        obtain ⟨-, -, hnone, -⟩ := sinkLoad?_spec h₂ hsite
        obtain rfl := hnone rfl
        sel_simp [Option.some.injEq] at h
        by_cases hk : (w.truncate ka == 0) = true
        · sel_simp [hk] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨Ext.fire c _ _, rfl, fun N ρ σ mem ctx va vb hcl hN hal hbl ha hb hp hag =>
            ⟨σ, rfl, fun _ _ => rfl, fun u hu => ?_, ?_⟩⟩
          · simp [xargsRegs, XArg.regs] at hu
            subst hu
            exact Nat.lt_of_lt_of_le (vlow hbl) (by simpa using hN)
          simp only [Lir.Arg.eval, Option.some.injEq] at ha
          subst ha
          have hk' : w.truncate 0 = w.truncate ka := by simp only [beq_iff_eq] at hk; rw [hk, truncate_zero]
          rw [← holds_congr hk' rfl]
          exact test_self_swap hcx (hag.get (by simp [xargsRegs, XArg.regs]) (vlow hbl) hb)
        · sel_simp [hk] at h
          obtain ⟨hext, hr, hy, hval⟩ := reg (fun vy vo => cond.holds w vo vy) fl_swap h
          refine ⟨(Ext.fire c _ _).trans hext, hr, fun N ρ σ mem ctx va vb hcl hN hal hbl ha hb hp hag => ?_⟩
          have hN' : N ≤ (fireSt "cmp.swap" st₂).next := by simpa using hN
          have := hval N ρ σ mem ctx vb va hN' (Nat.lt_of_lt_of_le (vlow hbl) hN') hal
            (hag.get hy (vlow hbl) hb) ha hag
          simp only [fireSt_next] at this
          exact this
    | imm kb =>
      sel_simp [Option.some.injEq] at h
      rw [bind_ok] at h
      obtain ⟨⟨x, pre₁⟩, st₁, h₁, h⟩ := h
      rw [bind_ok] at h
      obtain ⟨⟨p, args, pre₂⟩, st₂, h₂, h⟩ := h
      sel_simp [Option.some.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨rfl, hn₁, hc₁, hr₁, hv₁⟩ := materialize_spec h₁
      obtain ⟨hext, hr, hy, hval⟩ := cmp_reg h₂ (cond.holds w) fl_reg
      refine ⟨(Ext.of_le (by rw [hn₁]; exact Nat.le_succ _) hc₁).trans hext, by simp [hr₁, hr], ?_⟩
      intro N ρ σ mem ctx va vb hcl hN hal hbl ha hb hp hag
      simp only [Lir.Arg.eval, Option.some.injEq] at ha hb
      subst ha hb
      obtain ⟨σ', he, hab, hbd, hd⟩ := hval N ρ (σ.insert st.next ka) mem ctx ka kb
        (by rw [hn₁]; exact Nat.le_succ_of_le hN) (by rw [hn₁]; exact Nat.lt_succ_self _)
        (by simp [Lir.Arg.uses, Lir.Arg.vreg?]) (by simp) rfl
        (fun u hu hu' v hv => by
          rw [insert_ne (by vomega)]; exact hag u hu hu' v hv)
      refine ⟨σ', by rw [execSeq_append (hv₁ σ mem ctx), he], fun u hu => ?_, hbd, hd⟩
      rw [hab u (by rw [hn₁]; vomega)]
      exact insert_below (Nat.le_refl _) u hu


/-! ## Tag tests (rules 2 and 3) -/

/-- The Lir tag test a `test` row's `je`/`jne` decides. -/
def tzCond (zero : Bool) : Lir.Cond := if zero then .tz else .tnz

theorem tz_flags (zero : Bool) (w : Width) (a b : Word) :
    (Prod.test.flags w a b).test (if zero then .eq else .ne) = some ((tzCond zero).holds w a b) := by
  cases zero
  · exact and_test_tnz w a b
  · exact and_test_tz w a b

theorem tz_comm (zero : Bool) (w : Width) (a b : Word) : (tzCond zero).holds w a b = (tzCond zero).holds w b a := by
  cases zero <;> simp [tzCond, Lir.Cond.holds, UInt64.and_comm]

theorem tz_trunc_left (zero : Bool) (w : Width) (a b : Word) :
    (tzCond zero).holds w (w.truncate a) b = (tzCond zero).holds w a b :=
  holds_trunc_left _ w a b

theorem tz_narrow' (zero : Bool) (w : Width) (a k c : Word) (hk : w.truncate k = k)
    (hc : (testWidth w k).truncate c = (testWidth w k).truncate k) :
    (tzCond zero).holds (testWidth w k) a c = (tzCond zero).holds w a k := by
  cases zero
  · exact tnz_narrow w a k c hk hc
  · exact tz_narrow w a k c hk hc

theorem immFull?_some {w : Width} (hw : w ≠ .w64) (k : Word) : ∃ c, immFull? w k = some c := by
  refine ⟨(X86.Table.fullImm w).norm k, ?_⟩
  have he : (w.truncate ((X86.Table.fullImm w).norm k) == w.truncate k) = true := by
    simp only [beq_iff_eq]
    apply UInt64.toNat_inj.mp
    rw [X86.Encode.truncate_nat, X86.Encode.truncate_nat]
    cases w with
    | w8 => simp only [X86.Table.fullImm, X86.ImmKind.norm, Width.bits]; rw [X86.Encode.signExtend8_low]; simp
    | w16 => simp only [X86.Table.fullImm, X86.ImmKind.norm, Width.bits]; rw [X86.Encode.signExtend16_low]; simp
    | w32 => simp only [X86.Table.fullImm, X86.ImmKind.norm, Width.bits]; rw [X86.Encode.signExtend32_low]; simp
    | w64 => exact absurd rfl hw
  simp only [immFull?, he, ↓reduceIte]

theorem testWidth_w64 {w : Width} {k : Word} (h : testWidth w k = .w64) : w = .w64 := by
  unfold testWidth at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · exact h

theorem testImm_spec {zero : Bool} {w : Width} {a : VReg} {k : Word} {site : Nat} {c : Ctx} {st st' : St}
    {pr : Producer} (h : testImm (if zero then .eq else .ne) w a k site c st = .ok (pr, st')) (hsite : site = c.pos) :
    Ext c st st' ∧ readsOf pr.pre = [] ∧
      ∀ N (ρ σ : Env) mem ctx va, CtxLow c N → N ≤ st.next → a < st.next → Pend c st st' ρ mem ctx →
        Agree N (xargsRegs pr.args) ρ σ → (a < N → ρ[a]? = some va) → (N ≤ a → σ[a]? = some va) →
        ∃ σ', execSeq σ mem ctx pr.pre = some (σ', mem) ∧ (∀ u, u < st.next → σ'[u]? = σ[u]?) ∧
          (∀ u ∈ xargsRegs pr.args, u < st'.next) ∧
          Decides pr.op pr.args pr.cond σ' mem ctx ((tzCond zero).holds w va k) := by
  have hk' : w.truncate (w.truncate k) = w.truncate k := truncate_idem w k
  -- the flag fact at the narrowed width
  have fl : ∀ va v₁ c', (testWidth w (w.truncate k)).truncate v₁ = (testWidth w (w.truncate k)).truncate va →
      (testWidth w (w.truncate k)).truncate c' = (testWidth w (w.truncate k)).truncate (w.truncate k) →
      (Prod.test.flags (testWidth w (w.truncate k)) v₁ c').test (if zero then .eq else .ne) =
        some ((tzCond zero).holds w va k) := by
    intro va v₁ c' hv hc
    rw [tz_flags, holds_congr hv rfl, tz_narrow' zero w va _ c' hk' hc, holds_trunc_right]
  have hav : ∀ {N : Nat} {ρ σ : Env} {va : Word} {S : List VReg}, a ∈ S → Agree N S ρ σ →
      (a < N → ρ[a]? = some va) → (N ≤ a → σ[a]? = some va) → σ[a]? = some va := by
    intro N ρ σ va S hS hag hρ hσ
    by_cases haN : a < N
    · exact hag.get hS haN (hρ haN)
    · exact hσ (by vomega)
  unfold testImm at h
  sel_simp [Option.some.injEq] at h
  rw [bind_ok] at h
  obtain ⟨r, st₁, h₁, h⟩ := h
  obtain ⟨hext₁, hn₁, hnone, hsome⟩ := sinkLoad?_spec h₁ hsite
  cases hf : immFull? (testWidth w (w.truncate k)) (w.truncate k) with
  | some c' =>
    have hc' := immFull?_low hf
    cases r with
    | some m =>
      sel_simp [hf] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hlow, hval⟩ := hsome m rfl
      refine ⟨hext₁.trans ((Ext.fire c _ _).trans (Ext.fire c _ _)), rfl, ?_⟩
      intro N ρ σ mem ctx va hcl hN ha hp hag hρ _
      obtain ⟨haN, hmN⟩ := hlow N hcl
      obtain ⟨addr, vy, hy, haddr, hread⟩ := hval ρ mem ctx (hp.left ((Ext.fire c _ _).trans (Ext.fire c _ _)))
      rw [hρ haN] at hy
      cases hy
      have hm := hag.amode (fun u hu => by simp [xargsRegs, XArg.regs, hu]) hmN haddr
      refine ⟨σ, rfl, fun _ _ => rfl, fun u hu => ?_, .test, _, .MI, .m m, .i c', _, c', rfl, .inr rfl, rfl,
        valIn_m hm (hread _ (Nat.le_refl _)), rfl, fl va _ c' (truncate_idem _ va) hc'⟩
      simp [xargsRegs, XArg.regs] at hu
      exact Nat.lt_of_lt_of_le (hmN u hu) (by simp [hn₁]; exact hN)
    | none =>
      obtain rfl := hnone rfl
      sel_simp [hf] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨Ext.fire c _ _, rfl, ?_⟩
      intro N ρ σ mem ctx va hcl hN ha hp hag hρ hσ
      refine ⟨σ, rfl, fun _ _ => rfl, fun u hu => ?_, .test, _, .MI, .r a, .i c', va, c', rfl, .inr rfl, rfl,
        hav (by simp [xargsRegs, XArg.regs]) hag hρ hσ, rfl, fl va va c' rfl hc'⟩
      simp [xargsRegs, XArg.regs] at hu
      subst hu
      simpa using ha
  | none =>
    have hw' : testWidth w (w.truncate k) = .w64 := by
      cases hT : testWidth w (w.truncate k)
      all_goals first
        | rfl
        | (obtain ⟨c', hc'⟩ := immFull?_some (w := testWidth w (w.truncate k)) (by rw [hT]; decide) (w.truncate k)
           rw [hc'] at hf
           cases hf)
    have hw := testWidth_w64 hw'
    -- the flag fact at the full width
    have fl' : ∀ va v₁, w.truncate v₁ = w.truncate va →
        (Prod.test.flags w v₁ (w.truncate k)).test (if zero then .eq else .ne) = some ((tzCond zero).holds w va k) := by
      intro va v₁ hv
      rw [tz_flags, holds_congr hv hk']
    cases r with
    | some m =>
      sel_simp [hf] at h
      rw [bind_ok] at h
      obtain ⟨⟨t, pre⟩, st₂, h₂, h⟩ := h
      sel_simp [Option.some.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨rfl, hn₂, hc₂, hr₂, hv₂⟩ := materialize_spec h₂
      obtain ⟨hlow, hval⟩ := hsome m rfl
      have hext₂ : Ext c st₁ (fireSt "test.rr" st₂) :=
        Ext.of_le (by simp [hn₂]) (by simp [hc₂])
      refine ⟨hext₁.trans hext₂, hr₂, ?_⟩
      intro N ρ σ mem ctx va hcl hN ha hp hag hρ _
      obtain ⟨haN, hmN⟩ := hlow N hcl
      obtain ⟨addr, vy, hy, haddr, hread⟩ := hval ρ mem ctx (hp.left hext₂)
      rw [hρ haN] at hy
      cases hy
      have hm := hag.amode (fun u hu => by simp [xargsRegs, XArg.regs, hu]) hmN haddr
      have hNt : N ≤ (fireSt "test.mem" st₁).next := by simp [hn₁]; exact hN
      have hvm : (XArg.m m).valIn (σ.insert (fireSt "test.mem" st₁).next (w.truncate k)) mem ctx w =
          some (w.truncate va) := by
        rw [valIn_above (fun u hu => Nat.lt_of_lt_of_le (hmN u (by simpa [XArg.regs] using hu)) hNt)
          (insert_below (Nat.le_refl _))]
        exact valIn_m hm (hread w (by rw [hw', hw]; exact Nat.le_refl _))
      refine ⟨_, hv₂ σ mem ctx, insert_below (by simp [hn₁]), fun u hu => ?_, .test, w, .MR, .m m, .r _,
        w.truncate va, w.truncate k, rfl, .inl rfl, rfl, hvm, by simp [XArg.valIn], fl' va _ (truncate_idem w va)⟩
      simp only [xargsRegs, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append, XArg.regs,
        List.mem_singleton] at hu
      rcases hu with hu | rfl
      · exact Nat.lt_of_lt_of_le (hmN u hu) (by simp [hn₂]; vomega)
      · simp [hn₂]
    | none =>
      obtain rfl := hnone rfl
      sel_simp [hf] at h
      rw [bind_ok] at h
      obtain ⟨⟨t, pre⟩, st₂, h₂, h⟩ := h
      sel_simp [Option.some.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨rfl, hn₂, hc₂, hr₂, hv₂⟩ := materialize_spec h₂
      refine ⟨Ext.of_le (by simp [hn₂]) (by simp [hc₂]), hr₂, ?_⟩
      intro N ρ σ mem ctx va hcl hN ha hp hag hρ hσ
      have ha' := hav (by simp [xargsRegs, XArg.regs]) hag hρ hσ
      refine ⟨_, hv₂ σ mem ctx, insert_below (Nat.le_refl _), fun u hu => ?_, .test, w, .MR, .r a, .r _, va,
        w.truncate k, rfl, .inl rfl, rfl, ?_, by simp [XArg.valIn], fl' va va rfl⟩
      · simp only [xargsRegs, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append, XArg.regs,
          List.mem_singleton] at hu
        rcases hu with rfl | rfl <;> simp [hn₂] <;> vomega
      simp only [XArg.valIn]
      rw [insert_ne (by vomega)]
      exact ha'


theorem testProducer_spec {zero : Bool} {w : Width} {a b : Lir.Arg} {site : Nat} {c : Ctx} {st st' : St}
    {pr : Producer} (h : testProducer zero w a b site c st = .ok (pr, st')) (hsite : site = c.pos) :
    ProducerOk c st st' a b ((tzCond zero).holds w) pr := by
  have vlow : ∀ {N : Nat} {y : VReg}, (∀ u ∈ (Lir.Arg.v y).uses, u < N) → y < N :=
    fun h => h _ (by simp [Lir.Arg.uses, Lir.Arg.vreg?])
  unfold testProducer at h
  cases a with
  | v a' =>
    cases b with
    | v b' =>
      sel_simp [Option.some.injEq] at h
      rw [bind_ok] at h
      obtain ⟨r₁, st₁, h₁, h⟩ := h
      obtain ⟨hext₁, hn₁, hnone₁, hsome₁⟩ := sinkLoad?_spec h₁ hsite
      cases r₁ with
      | some m =>
        sel_simp [Option.some.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hlow, hval⟩ := hsome₁ m rfl
        refine ⟨hext₁.trans (Ext.fire c _ _), rfl, ?_⟩
        intro N ρ σ mem ctx va vb hcl hN hal hbl ha hb hp hag
        obtain ⟨_, hmN⟩ := hlow N hcl
        obtain ⟨addr, vy, hy, haddr, hread⟩ := hval ρ mem ctx (hp.left (Ext.fire c _ _))
        simp only [Lir.Arg.eval] at ha
        rw [ha] at hy
        cases hy
        have hm := hag.amode (fun u hu => by simp [xargsRegs, XArg.regs, hu]) hmN haddr
        refine ⟨σ, rfl, fun _ _ => rfl, fun u hu => ?_, .test, w, .MR, .m m, .r b', w.truncate va, vb, rfl,
          .inl rfl, rfl, valIn_m hm (hread w (Nat.le_refl _)), hag.get (by simp [xargsRegs, XArg.regs]) (vlow hbl) hb, ?_⟩
        · simp only [xargsRegs, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append, XArg.regs,
            List.mem_singleton] at hu
          rcases hu with hu | rfl
          · exact Nat.lt_of_lt_of_le (hmN u hu) (by simpa [hn₁] using hN)
          · exact Nat.lt_of_lt_of_le (vlow hbl) (by simpa [hn₁] using hN)
        rw [tz_flags, tz_trunc_left]
      | none =>
        obtain rfl := hnone₁ rfl
        sel_simp [Option.some.injEq] at h
        rw [bind_ok] at h
        obtain ⟨r₂, st₂, h₂, h⟩ := h
        obtain ⟨hext₂, hn₂, hnone₂, hsome₂⟩ := sinkLoad?_spec h₂ hsite
        cases r₂ with
        | some m =>
          sel_simp [Option.some.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨hlow, hval⟩ := hsome₂ m rfl
          refine ⟨hext₂.trans (Ext.fire c _ _), rfl, ?_⟩
          intro N ρ σ mem ctx va vb hcl hN hal hbl ha hb hp hag
          obtain ⟨_, hmN⟩ := hlow N hcl
          obtain ⟨addr, vy, hy, haddr, hread⟩ := hval ρ mem ctx (hp.left (Ext.fire c _ _))
          simp only [Lir.Arg.eval] at hb
          rw [hb] at hy
          cases hy
          have hm := hag.amode (fun u hu => by simp [xargsRegs, XArg.regs, hu]) hmN haddr
          refine ⟨σ, rfl, fun _ _ => rfl, fun u hu => ?_, .test, w, .MR, .m m, .r a', w.truncate vb, va, rfl,
            .inl rfl, rfl, valIn_m hm (hread w (Nat.le_refl _)), hag.get (by simp [xargsRegs, XArg.regs]) (vlow hal) ha, ?_⟩
          · simp only [xargsRegs, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append, XArg.regs,
              List.mem_singleton] at hu
            rcases hu with hu | rfl
            · exact Nat.lt_of_lt_of_le (hmN u hu) (by simpa [hn₂] using hN)
            · exact Nat.lt_of_lt_of_le (vlow hal) (by simpa [hn₂] using hN)
          rw [tz_flags, tz_trunc_left, tz_comm]
        | none =>
          obtain rfl := hnone₂ rfl
          sel_simp [Option.some.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨Ext.fire c _ _, rfl, ?_⟩
          intro N ρ σ mem ctx va vb hcl hN hal hbl ha hb hp hag
          refine ⟨σ, rfl, fun _ _ => rfl, fun u hu => ?_, .test, w, .MR, .r a', .r b', va, vb, rfl, .inl rfl, rfl,
            hag.get (by simp [xargsRegs, XArg.regs]) (vlow hal) ha,
            hag.get (by simp [xargsRegs, XArg.regs]) (vlow hbl) hb, tz_flags zero w va vb⟩
          simp only [xargsRegs, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append, XArg.regs,
            List.mem_singleton] at hu
          rcases hu with rfl | rfl
          · exact Nat.lt_of_lt_of_le (vlow hal) (by simpa using hN)
          · exact Nat.lt_of_lt_of_le (vlow hbl) (by simpa using hN)
    | imm k =>
      sel_simp [Option.some.injEq] at h
      obtain ⟨hext, hr, hval⟩ := testImm_spec h hsite
      refine ⟨hext, hr, fun N ρ σ mem ctx va vb hcl hN hal hbl ha hb hp hag => ?_⟩
      simp only [Lir.Arg.eval, Option.some.injEq] at hb
      subst hb
      exact hval N ρ σ mem ctx va hcl hN (Nat.lt_of_lt_of_le (vlow hal) hN) hp hag (fun _ => ha)
        (fun h' => absurd (vlow hal) (by vomega))
  | imm k =>
    cases b with
    | v b' =>
      sel_simp [Option.some.injEq] at h
      obtain ⟨hext, hr, hval⟩ := testImm_spec h hsite
      refine ⟨hext, hr, fun N ρ σ mem ctx va vb hcl hN hal hbl ha hb hp hag => ?_⟩
      simp only [Lir.Arg.eval, Option.some.injEq] at ha
      subst ha
      rw [tz_comm]
      exact hval N ρ σ mem ctx vb hcl hN (Nat.lt_of_lt_of_le (vlow hbl) hN) hp hag (fun _ => hb)
        (fun h' => absurd (vlow hbl) (by vomega))
    | imm kb =>
      sel_simp [Option.some.injEq] at h
      rw [bind_ok] at h
      obtain ⟨⟨x, pre⟩, st₁, h₁, h⟩ := h
      rw [bind_ok] at h
      obtain ⟨p, st₂, h₂, h⟩ := h
      sel_simp [Option.some.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨rfl, hn₁, hc₁, hr₁, hv₁⟩ := materialize_spec h₁
      obtain ⟨hext, hr, hval⟩ := testImm_spec h₂ hsite
      have hext₁ : Ext c st st₁ := Ext.of_le (by rw [hn₁]; exact Nat.le_succ _) hc₁
      refine ⟨hext₁.trans hext, by simp [hr₁, hr], ?_⟩
      intro N ρ σ mem ctx va vb hcl hN hal hbl ha hb hp hag
      simp only [Lir.Arg.eval, Option.some.injEq] at ha hb
      subst ha hb
      obtain ⟨σ', he, hab, hbd, hd⟩ := hval N ρ (σ.insert st.next k) mem ctx k hcl
        (by rw [hn₁]; exact Nat.le_succ_of_le hN) (by rw [hn₁]; exact Nat.lt_succ_self _) (hp.right hext₁)
        (fun u hu hu' v hv => by rw [insert_ne (by vomega)]; exact hag u hu hu' v hv)
        (fun h' => absurd h' (by vomega)) (fun _ => by simp)
      refine ⟨σ', by rw [execSeq_append (hv₁ σ mem ctx), he], fun u hu => ?_, hbd, hd⟩
      rw [hab u (by rw [hn₁]; vomega)]
      exact insert_below (Nat.le_refl _) u hu

theorem compareProducer_spec {cond : Lir.Cond} {w : Width} {a b : Lir.Arg} {c : Ctx} {st st' : St}
    {pr : Producer} (h : compareProducer cond w a b c st = .ok (pr, st')) :
    ProducerOk c st st' a b (cond.holds w) pr := by
  unfold compareProducer at h
  sel_simp [Option.some.injEq] at h
  cases hc : condX86 cond with
  | some cx =>
    simp only [hc] at h
    exact cmpProducer_spec hc h rfl
  | none =>
    simp only [hc] at h
    have := testProducer_spec h rfl
    have hcond : tzCond (cond == .tz) = cond := by cases cond <;> simp_all [condX86, tzCond]
    rwa [hcond] at this

end IxCC.Xv.Select.Proof
