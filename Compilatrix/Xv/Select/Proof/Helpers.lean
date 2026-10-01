import Compilatrix.Xv.Select.Proof.Monad

/-!
# Selection's helpers run as specified

The vocabulary of the per-rule proofs and the specifications of the helpers
the rules share.

- `readsOf`: the registers a list of Xv instructions reads.
- `Agree N S ρ σ`: the Xv environment `σ` holds the Lir environment `ρ`'s
  value at every register of `S` below `N` that `ρ` defines. A rule may
  rely on it for the registers its instructions read.
- `Computes is σ mem ctx n x v`: the instructions run from `σ`, leave memory
  alone, put `v` in `x`, and change no other register below `n` (they write
  `x` and fresh registers only).

Helpers (`movImm`, `materialize`, `argReg`, `argRegs`, `truncTo`, `argTrunc`,
`aluImm`, `mulImm`, `tieOrder`, `narrowed`, `leaAdd?`) are specified over the
Xv environment: what they read, which registers they write, and the values
they leave.
-/

namespace Compilatrix.Xv.Select.Proof

open Compilatrix.Lir (VReg Word Env)
open Compilatrix.X86 (Width)
open Compilatrix.Xv.Select

/-! ## Truncated arithmetic -/

theorem truncate_add (w : Width) (a b : Word) :
    w.truncate (a + b) = w.truncate (w.truncate a + w.truncate b) := by
  apply UInt64.toNat_inj.mp
  rw [X86.Encode.truncate_nat, X86.Encode.truncate_nat, UInt64.toNat_add, UInt64.toNat_add,
    X86.Encode.truncate_nat, X86.Encode.truncate_nat]
  have := UInt64.toNat_lt a
  have := UInt64.toNat_lt b
  cases w <;> simp [Width.bits] <;> omega

theorem truncate_sub (w : Width) (a b : Word) :
    w.truncate (a - b) = w.truncate (w.truncate a - w.truncate b) := by
  apply UInt64.toNat_inj.mp
  rw [X86.Encode.truncate_nat, X86.Encode.truncate_nat, UInt64.toNat_sub, UInt64.toNat_sub,
    X86.Encode.truncate_nat, X86.Encode.truncate_nat]
  have := UInt64.toNat_lt a
  have := UInt64.toNat_lt b
  cases w <;> simp [Width.bits] <;> omega

theorem truncate_mul (w : Width) (a b : Word) :
    w.truncate (a * b) = w.truncate (w.truncate a * w.truncate b) := by
  apply UInt64.toNat_inj.mp
  rw [X86.Encode.truncate_nat, X86.Encode.truncate_nat, UInt64.toNat_mul, UInt64.toNat_mul,
    X86.Encode.truncate_nat, X86.Encode.truncate_nat]
  have hd : 2 ^ w.bits ∣ 2 ^ 64 := Nat.pow_dvd_pow 2 (by cases w <;> decide)
  rw [Nat.mod_mod_of_dvd _ hd, Nat.mod_mod_of_dvd _ hd, Nat.mul_mod, Nat.mul_mod (_ % _), Nat.mod_mod,
    Nat.mod_mod]

theorem truncate_and' (w : Width) (a b : Word) :
    w.truncate (a &&& b) = w.truncate (w.truncate a &&& w.truncate b) := by
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [Width.truncate, UInt64.toBitVec_and, BitVec.getLsbD_and]
  cases (w.mask.toBitVec.getLsbD i) <;> simp

theorem truncate_or (w : Width) (a b : Word) :
    w.truncate (a ||| b) = w.truncate (w.truncate a ||| w.truncate b) := by
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [Width.truncate, UInt64.toBitVec_and, UInt64.toBitVec_or, BitVec.getLsbD_and, BitVec.getLsbD_or]
  cases (w.mask.toBitVec.getLsbD i) <;> simp

theorem truncate_xor (w : Width) (a b : Word) :
    w.truncate (a ^^^ b) = w.truncate (w.truncate a ^^^ w.truncate b) := by
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [Width.truncate, UInt64.toBitVec_and, UInt64.toBitVec_xor, BitVec.getLsbD_and, BitVec.getLsbD_xor]
  cases (w.mask.toBitVec.getLsbD i) <;> simp

theorem alu_trunc (op : X86.AluOp) (w : Width) (a b : Word) :
    w.truncate (op.eval a b) = w.truncate (op.eval (w.truncate a) (w.truncate b)) := by
  cases op
  · exact truncate_add w a b
  · exact truncate_sub w a b
  · exact truncate_and' w a b
  · exact truncate_or w a b
  · exact truncate_xor w a b

/-- An ALU result's low bits depend only on its operands' low bits. -/
theorem alu_congr (op : X86.AluOp) {w : Width} {a a' b b' : Word} (ha : w.truncate a = w.truncate a')
    (hb : w.truncate b = w.truncate b') : w.truncate (op.eval a b) = w.truncate (op.eval a' b') := by
  rw [alu_trunc, ha, hb, ← alu_trunc]

theorem mul_congr {w : Width} {a a' b b' : Word} (ha : w.truncate a = w.truncate a')
    (hb : w.truncate b = w.truncate b') : w.truncate (a * b) = w.truncate (a' * b') := by
  rw [truncate_mul, ha, hb, ← truncate_mul]

theorem alu_comm (op : X86.AluOp) (hop : op ≠ .sub) (a b : Word) : op.eval a b = op.eval b a := by
  cases op
  · exact UInt64.add_comm a b
  · exact absurd rfl hop
  · exact UInt64.and_comm a b
  · exact UInt64.or_comm a b
  · exact UInt64.xor_comm a b

/-- The low bits of a value kept at a width at least as wide. -/
theorem truncate_low {w wo : Width} (h : w.bits ≤ wo.bits) {k c : Word} (hc : wo.truncate c = wo.truncate k) :
    w.truncate c = w.truncate k := by
  rw [← truncate_truncate_le h c, hc, truncate_truncate_le h]

theorem bits_opWidth (w : Width) : w.bits ≤ (opWidth w).bits := by
  cases w <;> decide

theorem opWidth_wide (w : Width) : opWidth w = .w32 ∨ opWidth w = .w64 := by
  cases w <;> simp [opWidth, narrowWidth]

theorem opWidth_of_not_narrow {w : Width} (h : narrowWidth w = false) : opWidth w = w := by
  simp [opWidth, h]

theorem narrow_cases {w : Width} (h : narrowWidth w = true) : w = .w8 ∨ w = .w16 := by
  cases w <;> simp [narrowWidth] at h ⊢

/-- The x86 ALU operation of a Lir ALU operation. -/
def aluOf : Lir.BinOp → X86.AluOp
  | .add => .add
  | .sub => .sub
  | .and => .and
  | .or => .or
  | _ => .xor

/-- The Lir operations `selectAlu` handles. -/
def IsAlu (o : Lir.BinOp) : Prop := o = .add ∨ o = .sub ∨ o = .and ∨ o = .or ∨ o = .xor

theorem aluOf_mnemonic {o : Lir.BinOp} (h : IsAlu o) : aluMnemonic o = (aluOf o).mnemonic := by
  rcases h with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem aluOf_eval {o : Lir.BinOp} (h : IsAlu o) (w : Width) (a b : Word) :
    o.eval w a b = some (w.truncate ((aluOf o).eval a b)) := by
  rcases h with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem aluOf_sub {o : Lir.BinOp} (h : IsAlu o) (hs : o ≠ .sub) : aluOf o ≠ .sub := by
  rcases h with rfl | rfl | rfl | rfl | rfl <;> simp_all [aluOf]

/-! ## Environments -/

/-- The registers a list of instructions reads. -/
def readsOf (is : List (Inst VReg)) : List VReg := is.flatMap Inst.uses

@[simp] theorem readsOf_nil : readsOf [] = [] := rfl

@[simp] theorem readsOf_cons (i : Inst VReg) (is : List (Inst VReg)) :
    readsOf (i :: is) = i.uses ++ readsOf is := by
  simp [readsOf]

@[simp] theorem readsOf_append (is js : List (Inst VReg)) : readsOf (is ++ js) = readsOf is ++ readsOf js := by
  simp [readsOf]

/-- `σ` holds `ρ`'s value at each register of `S` below `N` that `ρ` defines. -/
def Agree (N : Nat) (S : List VReg) (ρ σ : Env) : Prop :=
  ∀ u ∈ S, u < N → ∀ v, ρ[u]? = some v → σ[u]? = some v

theorem Agree.mono {N : Nat} {S S' : List VReg} {ρ σ : Env} (h : Agree N S ρ σ) (hs : ∀ u ∈ S', u ∈ S) :
    Agree N S' ρ σ :=
  fun u hu => h u (hs u hu)

theorem Agree.get {N : Nat} {S : List VReg} {ρ σ : Env} (h : Agree N S ρ σ) {u : VReg} {v : Word}
    (hu : u ∈ S) (hN : u < N) (hv : ρ[u]? = some v) : σ[u]? = some v :=
  h u hu hN v hv

/-- A Lir argument read by the instructions has its value in `σ`. -/
theorem Agree.arg {N : Nat} {S : List VReg} {ρ σ : Env} (h : Agree N S ρ σ) {a : Lir.Arg} {v : Word}
    (hu : ∀ u ∈ a.uses, u ∈ S) (hN : ∀ u ∈ a.uses, u < N) (hv : a.eval ρ = some v) : a.eval σ = some v := by
  cases a with
  | v x =>
    exact h x (hu x (by simp [Lir.Arg.uses, Lir.Arg.vreg?])) (hN x (by simp [Lir.Arg.uses, Lir.Arg.vreg?])) v hv
  | imm k => exact hv

theorem Agree.args {N : Nat} {S : List VReg} {ρ σ : Env} (h : Agree N S ρ σ) :
    ∀ {as : List Lir.Arg} {vals : List Word}, (∀ u ∈ Lir.argsUses as, u ∈ S) → (∀ u ∈ Lir.argsUses as, u < N) →
      Lir.evalArgs ρ as = some vals → Lir.evalArgs σ as = some vals
  | [], vals, _, _, hv => hv
  | a :: as, vals, hu, hN, hv => by
      simp only [Lir.evalArgs, List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at hv ⊢
      obtain ⟨v, hv, vs, hvs, rfl⟩ := hv
      refine ⟨v, h.arg (fun u hu' => hu u (by simp [Lir.argsUses, hu'])) (fun u hu' => hN u (by simp [Lir.argsUses, hu'])) hv,
        vs, ?_, rfl⟩
      exact h.args (as := as) (fun u hu' => hu u (by simp only [Lir.argsUses, List.flatMap_cons, List.mem_append] at hu' ⊢; exact .inr hu'))
        (fun u hu' => hN u (by simp only [Lir.argsUses, List.flatMap_cons, List.mem_append] at hu' ⊢; exact .inr hu')) hvs

/-- Instructions that run from `σ`, leave memory alone, put `v` in `x`, and
change no other register below `n`. -/
def Computes (is : List (Inst VReg)) (σ : Env) (mem : X86.Memory) (ctx : Word) (n : Nat) (x : VReg) (v : Word) :
    Prop :=
  ∃ σ', execSeq σ mem ctx is = some (σ', mem) ∧ σ'[x]? = some v ∧ ∀ u, u < n → u ≠ x → σ'[u]? = σ[u]?

theorem Computes.single {i : Inst VReg} {σ : Env} {mem : X86.Memory} {ctx : Word} {n : Nat} {x : VReg}
    {v : Word} (h : i.exec σ mem ctx = some (σ.insert x v, mem)) : Computes [i] σ mem ctx n x v := by
  refine ⟨σ.insert x v, by rw [execSeq_singleton, h], by simp, fun u _ hu => ?_⟩
  rw [Std.HashMap.getElem?_insert]
  have : (x == u) = false := by simpa using fun e => hu e.symm
  simp [this]

theorem Computes.append {is js : List (Inst VReg)} {σ σ₁ : Env} {mem : X86.Memory} {ctx : Word} {n : Nat}
    {x : VReg} {v : Word} (h : execSeq σ mem ctx is = some (σ₁, mem)) (h₁ : ∀ u, u < n → σ₁[u]? = σ[u]?)
    (h₂ : Computes js σ₁ mem ctx n x v) : Computes (is ++ js) σ mem ctx n x v := by
  obtain ⟨σ', he, hx, hu⟩ := h₂
  exact ⟨σ', by rw [execSeq_append h, he], hx, fun u hn hne => (hu u hn hne).trans (h₁ u hn)⟩

theorem Computes.mono {is : List (Inst VReg)} {σ : Env} {mem : X86.Memory} {ctx : Word} {n n' : Nat}
    {x : VReg} {v : Word} (h : Computes is σ mem ctx n x v) (hn : n' ≤ n) : Computes is σ mem ctx n' x v := by
  obtain ⟨σ', he, hx, hu⟩ := h
  exact ⟨σ', he, hx, fun u hu' hne => hu u (Nat.lt_of_lt_of_le hu' hn) hne⟩

theorem Computes.congr {is : List (Inst VReg)} {σ : Env} {mem : X86.Memory} {ctx : Word} {n : Nat}
    {x : VReg} {v v' : Word} (h : Computes is σ mem ctx n x v) (hv : v = v') : Computes is σ mem ctx n x v' :=
  hv ▸ h

/-- A fresh register leaves the registers below it alone. -/
theorem insert_below {σ : Env} {t : VReg} {k : Word} {n : Nat} (ht : n ≤ t) :
    ∀ u, u < n → (σ.insert t k)[u]? = σ[u]? := by
  intro u hu
  rw [Std.HashMap.getElem?_insert]
  have : (t == u) = false := by simp; vomega
  simp [this]

theorem insert_ne {σ : Env} {t u : VReg} {k : Word} (h : t ≠ u) : (σ.insert t k)[u]? = σ[u]? := by
  rw [Std.HashMap.getElem?_insert]
  have : (t == u) = false := by simpa using h
  simp [this]

/-- An argument's registers below `n` keep its value. -/
theorem valIn_above {a : XArg VReg} {σ σ' : Env} {mem : X86.Memory} {ctx : Word} {w : Width} {n : Nat}
    (ha : ∀ u ∈ a.regs, u < n) (h : ∀ u, u < n → σ'[u]? = σ[u]?) : a.valIn σ' mem ctx w = a.valIn σ mem ctx w := by
  cases a with
  | r x => simp only [XArg.valIn]; exact h x (ha x (by simp [XArg.regs]))
  | i k => rfl
  | m am =>
    simp only [XArg.valIn]
    congr 1
    rcases am with ⟨base, index, disp⟩
    rcases base with _ | (b | _) <;> rcases index with _ | ⟨i, s⟩ <;>
      simp only [Amode.evalV] <;>
      (try rw [h i (ha i (by simp [XArg.regs, Amode.regs]))]) <;>
      (try rw [h b (ha b (by simp [XArg.regs, Amode.regs]))])

theorem eval_above {a : Lir.Arg} {σ σ' : Env} {n : Nat} (ha : ∀ u ∈ a.uses, u < n)
    (h : ∀ u, u < n → σ'[u]? = σ[u]?) : a.eval σ' = a.eval σ := by
  cases a with
  | v x => exact h x (ha x (by simp [Lir.Arg.uses, Lir.Arg.vreg?]))
  | imm k => rfl

theorem evalArgs_above {σ σ' : Env} {n : Nat} (h : ∀ u, u < n → σ'[u]? = σ[u]?) :
    ∀ {as : List Lir.Arg}, (∀ u ∈ Lir.argsUses as, u < n) → Lir.evalArgs σ' as = Lir.evalArgs σ as
  | [], _ => rfl
  | a :: as, ha => by
      simp only [Lir.evalArgs, List.mapM_cons] at *
      rw [eval_above (fun u hu => ha u (by simp [Lir.argsUses, hu])) h]
      have := evalArgs_above h (as := as) (fun u hu => ha u (by
        simp only [Lir.argsUses, List.flatMap_cons, List.mem_append] at hu ⊢; exact .inr hu))
      simp only [Lir.evalArgs] at this
      rw [this]

/-! ## Immediates -/

theorem movImm_spec {x : VReg} {k : Word} {c : Ctx} {st st' : St} {is : List (Inst VReg)}
    (h : movImm x k c st = .ok (is, st')) :
    st'.next = st.next ∧ st'.consumed = st.consumed ∧ readsOf is = [] ∧
      ∀ σ mem ctx, execSeq σ mem ctx is = some (σ.insert x k, mem) := by
  unfold movImm at h
  by_cases h0 : (k == 0) = true
  · sel_simp [h0] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨by simp, by simp, rfl, fun σ mem ctx => ?_⟩
    rw [execSeq_singleton, exec_zero]
    simp only [beq_iff_eq] at h0
    rw [h0]
  · sel_simp [h0] at h
    by_cases h32 : k.toNat < 2 ^ 32
    · sel_simp [h32] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨by simp, by simp, rfl, fun σ mem ctx => ?_⟩
      rw [execSeq_singleton]
      have := exec_movImm (w := .w32) (form := .OI) (.inl ⟨rfl, rfl⟩) (ρ := σ) (mem := mem) (ctx := ctx) x
        (X86.ImmKind.imm32.norm k)
      rw [mov32_imm h32] at this
      exact this
    · sel_simp [h32] at h
      by_cases hs : (X86.ImmKind.imm32.norm k == k) = true
      · sel_simp [hs] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨by simp, by simp, rfl, fun σ mem ctx => ?_⟩
        rw [execSeq_singleton]
        have := exec_movImm (w := .w64) (form := .MI) (.inr (.inr ⟨rfl, rfl⟩)) (ρ := σ) (mem := mem)
          (ctx := ctx) x k
        rw [X86.Encode.truncate64] at this
        exact this
      · sel_simp [hs] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨by simp, by simp, rfl, fun σ mem ctx => ?_⟩
        rw [execSeq_singleton]
        have := exec_movImm (w := .w64) (form := .OI) (.inr (.inl ⟨rfl, rfl⟩)) (ρ := σ) (mem := mem)
          (ctx := ctx) x k
        rw [X86.Encode.truncate64] at this
        exact this

theorem materialize_spec {k : Word} {c : Ctx} {st st' : St} {t : VReg} {is : List (Inst VReg)}
    (h : materialize k c st = .ok ((t, is), st')) :
    t = st.next ∧ st'.next = st.next + 1 ∧ st'.consumed = st.consumed ∧ readsOf is = [] ∧
      ∀ σ mem ctx, execSeq σ mem ctx is = some (σ.insert t k, mem) := by
  unfold materialize at h
  sel_simp [Option.some.injEq] at h
  rw [bind_ok] at h
  obtain ⟨is', st₁, h₁, h⟩ := h
  sel_simp [Option.some.injEq] at h
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
  obtain ⟨hn, hc, hr, hv⟩ := movImm_spec h₁
  exact ⟨rfl, by simp [hn], by simp [hc], hr, hv⟩

/-! ## Operands in registers -/

theorem argReg_spec {a : Lir.Arg} {c : Ctx} {st st' : St} {y : VReg} {is : List (Inst VReg)}
    (h : argReg a c st = .ok ((y, is), st')) :
    st.next ≤ st'.next ∧ st'.consumed = st.consumed ∧ readsOf is = [] ∧ (∀ u ∈ a.uses, u = y) ∧
      ((∀ u ∈ a.uses, u < st.next) → y < st'.next) ∧
      ∀ σ mem ctx v, a.eval σ = some v → ∃ σ', execSeq σ mem ctx is = some (σ', mem) ∧ σ'[y]? = some v ∧
        ∀ u, u < st.next → σ'[u]? = σ[u]? := by
  cases a with
  | v x =>
    simp only [argReg, pure_run, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    refine ⟨Nat.le_refl _, rfl, rfl, by simp [Lir.Arg.uses, Lir.Arg.vreg?], fun h => h _ (by simp [Lir.Arg.uses, Lir.Arg.vreg?]),
      fun σ mem ctx v hv => ⟨σ, rfl, hv, fun _ _ => rfl⟩⟩
  | imm k =>
    simp only [argReg] at h
    obtain ⟨rfl, hn, hc, hr, hv⟩ := materialize_spec h
    refine ⟨by vomega, hc, hr, by simp [Lir.Arg.uses, Lir.Arg.vreg?], fun _ => by vomega, fun σ mem ctx v hv' => ?_⟩
    simp only [Lir.Arg.eval, Option.some.injEq] at hv'
    subst hv'
    exact ⟨_, hv σ mem ctx, by simp, insert_below (Nat.le_refl _)⟩

theorem argRegs_spec :
    ∀ {as : List Lir.Arg} {c : Ctx} {st st' : St} {vs : List VReg} {is : List (Inst VReg)},
      argRegs as c st = .ok ((vs, is), st') →
      st.next ≤ st'.next ∧ st'.consumed = st.consumed ∧ readsOf is = [] ∧ (∀ u ∈ Lir.argsUses as, u ∈ vs) ∧
        ((∀ u ∈ Lir.argsUses as, u < st.next) → ∀ y ∈ vs, y < st'.next) ∧
        ∀ σ mem ctx vals, (∀ u ∈ Lir.argsUses as, u < st.next) → Lir.evalArgs σ as = some vals →
          ∃ σ', execSeq σ mem ctx is = some (σ', mem) ∧ readAll σ' vs = some vals ∧
            ∀ u, u < st.next → σ'[u]? = σ[u]?
  | [], c, st, st', vs, is, h => by
      simp only [argRegs, pure_run, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      refine ⟨Nat.le_refl _, rfl, rfl, by simp [Lir.argsUses], by simp, fun σ mem ctx vals _ hv => ?_⟩
      simp only [Lir.evalArgs, List.mapM_nil, Option.pure_def, Option.some.injEq] at hv
      subst hv
      exact ⟨σ, rfl, rfl, fun _ _ => rfl⟩
  | a :: as, c, st, st', vs, is, h => by
      simp only [argRegs] at h
      rw [bind_ok] at h
      obtain ⟨⟨v, pre⟩, st₁, h₁, h⟩ := h
      rw [bind_ok] at h
      obtain ⟨⟨vs', pres⟩, st₂, h₂, h⟩ := h
      sel_simp [Option.some.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      obtain ⟨hn₁, hc₁, hr₁, hu₁, hl₁, hv₁⟩ := argReg_spec h₁
      obtain ⟨hn₂, hc₂, hr₂, hu₂, hl₂, hv₂⟩ := argRegs_spec h₂
      have hau : ∀ u ∈ a.uses, u ∈ Lir.argsUses (a :: as) := fun u hu => by simp [Lir.argsUses, hu]
      have hasu : ∀ u ∈ Lir.argsUses as, u ∈ Lir.argsUses (a :: as) := fun u hu => by
        simp only [Lir.argsUses, List.flatMap_cons, List.mem_append] at hu ⊢; exact .inr hu
      refine ⟨by vomega, by rw [hc₂, hc₁], by simp [hr₁, hr₂], ?_, ?_, ?_⟩
      · intro u hu
        simp only [Lir.argsUses, List.flatMap_cons, List.mem_append] at hu
        rcases hu with hu | hu
        · simp [hu₁ u hu]
        · exact List.mem_cons_of_mem _ (hu₂ u hu)
      · intro hlow y hy
        rcases List.mem_cons.1 hy with rfl | hy
        · exact Nat.lt_of_lt_of_le (hl₁ fun u hu => hlow u (hau u hu)) hn₂
        · exact hl₂ (fun u hu => Nat.lt_of_lt_of_le (hlow u (hasu u hu)) hn₁) y hy
      · intro σ mem ctx vals hlow hv
        simp only [Lir.evalArgs, List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
          Option.pure_def, Option.some.injEq] at hv
        obtain ⟨va, hva, vas, hvas, rfl⟩ := hv
        obtain ⟨σ₁, he₁, hy₁, hb₁⟩ := hv₁ σ mem ctx va hva
        have hlow' : ∀ u ∈ Lir.argsUses as, u < st₁.next :=
          fun u hu => Nat.lt_of_lt_of_le (hlow u (hasu u hu)) hn₁
        have hvas' : Lir.evalArgs σ₁ as = some vas := by
          rw [evalArgs_above hb₁ (fun u hu => hlow u (hasu u hu))]
          exact hvas
        obtain ⟨σ₂, he₂, hr, hb₂⟩ := hv₂ σ₁ mem ctx vas hlow' hvas'
        refine ⟨σ₂, by rw [execSeq_append he₁, he₂], ?_, ?_⟩
        · have hvl : v < st₁.next := hl₁ fun u hu => hlow u (hau u hu)
          simp only [readAll, List.mapM_cons, Option.bind_eq_bind] at hr ⊢
          rw [hb₂ v hvl, hy₁]
          simp only [Option.bind_some]
          rw [hr]
          rfl
        · intro u hu
          rw [hb₂ u (Nat.lt_of_lt_of_le hu hn₁), hb₁ u hu]

/-! ## Truncations -/

theorem exec_truncTo (w : Width) {σ : Env} {mem : X86.Memory} {ctx : Word} {x src : VReg} {v : Word}
    (h : σ[src]? = some v) : execSeq σ mem ctx (truncTo w x src) = some (σ.insert x (w.truncate v), mem) := by
  cases w with
  | w64 => simp [truncTo, execSeq_singleton, exec_move h]
  | w32 => simp only [truncTo, execSeq_singleton]; exact exec_mov32R h
  | w8 => simp only [truncTo, execSeq_singleton]; exact exec_movzxR (.inl rfl) h
  | w16 => simp only [truncTo, execSeq_singleton]; exact exec_movzxR (.inr rfl) h

theorem readsOf_truncTo (w : Width) (x src : VReg) : readsOf (truncTo w x src) = [src] := by
  cases w <;> rfl

theorem argTrunc_spec {w : Width} {a : Lir.Arg} {c : Ctx} {st st' : St} {y : VReg} {is : List (Inst VReg)}
    (h : argTrunc w a c st = .ok ((y, is), st')) :
    st.next ≤ st'.next ∧ st'.consumed = st.consumed ∧ (∀ u ∈ a.uses, u = y ∨ u ∈ readsOf is) ∧
      ((∀ u ∈ a.uses, u < st.next) → y < st'.next) ∧
      ∀ σ mem ctx v, (∀ u ∈ a.uses, u < st.next) → a.eval σ = some v →
        ∃ σ', execSeq σ mem ctx is = some (σ', mem) ∧ σ'[y]? = some (w.truncate v) ∧
          ∀ u, u < st.next → σ'[u]? = σ[u]? := by
  cases a with
  | imm k =>
    simp only [argTrunc] at h
    obtain ⟨rfl, hn, hc, hr, hv⟩ := materialize_spec h
    refine ⟨by vomega, hc, by simp [Lir.Arg.uses, Lir.Arg.vreg?], fun _ => by vomega, fun σ mem ctx v _ hv' => ?_⟩
    simp only [Lir.Arg.eval, Option.some.injEq] at hv'
    subst hv'
    exact ⟨_, hv σ mem ctx, by simp, insert_below (Nat.le_refl _)⟩
  | v z =>
    simp only [argTrunc] at h
    by_cases hw : (w == .w64) = true
    · sel_simp [hw] at h
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      simp only [beq_iff_eq] at hw
      subst hw
      refine ⟨Nat.le_refl _, rfl, by simp [Lir.Arg.uses, Lir.Arg.vreg?],
        fun h => h _ (by simp [Lir.Arg.uses, Lir.Arg.vreg?]), fun σ mem ctx v _ hv => ⟨σ, rfl, ?_, fun _ _ => rfl⟩⟩
      simpa using hv
    · sel_simp [hw] at h
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      refine ⟨by simp, rfl, by simp [Lir.Arg.uses, Lir.Arg.vreg?, readsOf_truncTo], fun _ => by simp,
        fun σ mem ctx v hlow hv => ⟨_, exec_truncTo w hv, by simp, insert_below (Nat.le_refl _)⟩⟩

/-! ## ALU and multiply rows with an immediate -/

theorem aluImm_spec (op : X86.AluOp) {wo : Width} (hw : wo = .w32 ∨ wo = .w64) {dst a : VReg} {k : Word}
    {c : Ctx} {st st' : St} {is : List (Inst VReg)} (h : aluImm op.mnemonic wo dst a k c st = .ok (is, st')) :
    st.next ≤ st'.next ∧ st'.consumed = st.consumed ∧ a ∈ readsOf is ∧
      ∀ σ mem ctx va, σ[a]? = some va → a < st.next →
        Computes is σ mem ctx st.next dst (wo.truncate (op.eval va k)) := by
  unfold aluImm at h
  cases h8 : imm8? wo k with
  | some c' =>
    sel_simp [h8] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨by simp, by simp, by simp [Inst.uses, xargsRegs, XArg.regs], fun σ mem ctx va ha _ => ?_⟩
    refine Computes.single ((exec_aluI op hw (.inl rfl) c' ha).trans ?_)
    rw [alu_congr op rfl (imm8?_low h8)]
  | none =>
    sel_simp [h8] at h
    cases hf : immFull? wo k with
    | some c' =>
      sel_simp [hf] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨by simp, by simp, by simp [Inst.uses, xargsRegs, XArg.regs], fun σ mem ctx va ha _ => ?_⟩
      refine Computes.single ((exec_aluI op hw (.inr rfl) c' ha).trans ?_)
      rw [alu_congr op rfl (immFull?_low hf)]
    | none =>
      sel_simp [hf] at h
      rw [bind_ok] at h
      obtain ⟨⟨t, pre⟩, st₁, h₁, h⟩ := h
      sel_simp [Option.some.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨rfl, hn, hc, hr, hv⟩ := materialize_spec h₁
      refine ⟨by simp [hn], by simp [hc], by simp [hr, Inst.uses, xargsRegs, XArg.regs], ?_⟩
      intro σ mem ctx va ha hal
      refine Computes.append (hv σ mem ctx) (insert_below (Nat.le_refl _)) (Computes.single ?_)
      have ha' : (σ.insert st.next k)[a]? = some va := by rw [insert_ne (by vomega)]; exact ha
      exact exec_aluR op hw ha' (by simp)

theorem mulImm_spec {wo : Width} (hw : wo = .w32 ∨ wo = .w64) {dst a : VReg} {k : Word}
    {c : Ctx} {st st' : St} {is : List (Inst VReg)} (h : mulImm wo dst a k c st = .ok (is, st')) :
    st.next ≤ st'.next ∧ st'.consumed = st.consumed ∧ a ∈ readsOf is ∧
      ∀ σ mem ctx va, σ[a]? = some va → a < st.next →
        Computes is σ mem ctx st.next dst (wo.truncate (va * k)) := by
  unfold mulImm at h
  cases h8 : imm8? wo k with
  | some c' =>
    sel_simp [h8] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨by simp, by simp, by simp [Inst.uses, xargsRegs, XArg.regs], fun σ mem ctx va ha _ => ?_⟩
    refine Computes.single ((exec_imulI hw (.inl rfl) c' ha).trans ?_)
    rw [mul_congr rfl (imm8?_low h8)]
  | none =>
    sel_simp [h8] at h
    cases hf : immFull? wo k with
    | some c' =>
      sel_simp [hf] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨by simp, by simp, by simp [Inst.uses, xargsRegs, XArg.regs], fun σ mem ctx va ha _ => ?_⟩
      refine Computes.single ((exec_imulI hw (.inr rfl) c' ha).trans ?_)
      rw [mul_congr rfl (immFull?_low hf)]
    | none =>
      sel_simp [hf] at h
      rw [bind_ok] at h
      obtain ⟨⟨t, pre⟩, st₁, h₁, h⟩ := h
      sel_simp [Option.some.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨rfl, hn, hc, hr, hv⟩ := materialize_spec h₁
      refine ⟨by simp [hn], by simp [hc], by simp [hr, Inst.uses, xargsRegs, XArg.regs], ?_⟩
      intro σ mem ctx va ha hal
      refine Computes.append (hv σ mem ctx) (insert_below (Nat.le_refl _)) (Computes.single ?_)
      have ha' : (σ.insert st.next k)[a]? = some va := by rw [insert_ne (by vomega)]; exact ha
      exact exec_imulR hw ha' (by simp)

/-! ## Operand order and narrow results -/

theorem tieOrder_spec {a b : VReg} {c : Ctx} {st st' : St} {p : VReg × VReg}
    (h : tieOrder a b c st = .ok (p, st')) :
    st'.next = st.next ∧ st'.consumed = st.consumed ∧ (p = (a, b) ∨ p = (b, a)) := by
  unfold tieOrder at h
  sel_simp [Option.some.injEq] at h
  split at h
  · sel_simp [Option.some.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by simp, by simp, .inr rfl⟩
  · sel_simp [Option.some.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl, .inl rfl⟩

theorem narrowed_spec {w : Width} {x dst : VReg} {body : List (Inst VReg)} {c : Ctx} {st st' : St}
    {is : List (Inst VReg)} (h : narrowed w x dst body c st = .ok (is, st')) :
    st'.next = st.next ∧ st'.consumed = st.consumed ∧ (∀ u ∈ readsOf body, u ∈ readsOf is) ∧
      ∀ σ mem ctx n z, (narrowWidth w = false → dst = x) → (narrowWidth w = true → n ≤ dst ∧ x < n) →
        Computes body σ mem ctx n dst z →
        Computes is σ mem ctx n x (if narrowWidth w then w.truncate z else z) := by
  unfold narrowed at h
  by_cases hn : narrowWidth w = true
  · sel_simp [hn] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨by simp, by simp, fun u hu => by simp [hu], fun σ mem ctx n z _ hd hc => ?_⟩
    obtain ⟨hnd, hxn⟩ := hd hn
    obtain ⟨σ₁, he, hz, hb⟩ := hc
    simp only [hn, ↓reduceIte]
    refine Computes.append he (fun u hu => hb u hu (by vomega)) (Computes.single ?_)
    exact exec_movzxR (narrow_cases hn) hz
  · sel_simp [hn] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Bool.not_eq_true] at hn
    refine ⟨rfl, rfl, fun u hu => hu, fun σ mem ctx n z hd _ hc => ?_⟩
    rw [hd hn] at hc
    simpa [hn] using hc

/-- The value a narrowed result leaves: the operation's low `w` bits. -/
theorem narrow_val (w : Width) (z : Word) :
    (if narrowWidth w then w.truncate ((opWidth w).truncate z) else (opWidth w).truncate z) = w.truncate z := by
  by_cases hn : narrowWidth w = true
  · simp only [hn, ↓reduceIte]
    exact truncate_truncate_le (bits_opWidth w) z
  · simp only [Bool.not_eq_true] at hn
    simp [hn, opWidth_of_not_narrow hn]

end Compilatrix.Xv.Select.Proof
