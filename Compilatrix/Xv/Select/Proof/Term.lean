import Compilatrix.Xv.Select.Proof.Stmt

/-!
# Terminator rules

`TermRun t pre t' ρ σ mem ctx n`: the Xv terminator `t'`, after its prefix
`pre`, does what the Lir terminator `t` does from `ρ`: `pre` runs (writing
registers from `n` on only), and

- a jump's edge carries the Lir edge's arguments (`EdgeRel`);
- a branch's producer decides the Lir condition (rules 1–3), and each edge
  carries its arguments;
- `brOvf`'s `add`/`sub` row defines `x` with Lir's result and branches on
  carry or borrow (rule 4, rule 9 for a folded load), the edges reading the
  new `x`;
- `ret` and `tail` read the Lir results and arguments; `fail` and `trap`
  are themselves.

`selectTerm_ok` proves it of every selected terminator (`TermOk`).
-/

namespace Compilatrix.Xv.Select.Proof

open Compilatrix.Lir (VReg Word Env)
open Compilatrix.X86 (Width)
open Compilatrix.Xv.Select

/-! ## Arguments in registers, against any pair of environments -/

theorem argReg_gen {a : Lir.Arg} {c : Ctx} {st st' : St} {y : VReg} {is : List (Inst VReg)}
    (h : argReg a c st = .ok ((y, is), st')) :
    st.next ≤ st'.next ∧ st'.consumed = st.consumed ∧ readsOf is = [] ∧ (∀ u ∈ a.uses, u = y) ∧
      (y ∈ a.uses ∨ (st.next ≤ y ∧ y < st'.next)) ∧
      ∀ σ mem ctx, ∃ σ', execSeq σ mem ctx is = some (σ', mem) ∧ (∀ u, u < st.next → σ'[u]? = σ[u]?) ∧
        ∀ (E E' : Env) v, (∀ u ∈ a.uses, ∀ v, E'[u]? = some v → E[u]? = some v) →
          (st.next ≤ y → E[y]? = σ'[y]?) → a.eval E' = some v → E[y]? = some v := by
  cases a with
  | v x =>
    simp only [argReg, pure_run, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    refine ⟨Nat.le_refl _, rfl, rfl, by simp [uses_v], .inl (by simp [uses_v]), fun σ mem ctx => ⟨σ, rfl, fun _ _ => rfl,
      fun E E' v hE _ hv => hE _ (by simp [uses_v]) v hv⟩⟩
  | imm k =>
    simp only [argReg] at h
    obtain ⟨rfl, hn, hc, hr, hv⟩ := materialize_spec h
    refine ⟨by rw [hn]; exact Nat.le_succ _, hc, hr, by simp [Lir.Arg.uses, Lir.Arg.vreg?],
      .inr ⟨Nat.le_refl _, by rw [hn]; exact Nat.lt_succ_self _⟩, fun σ mem ctx => ⟨_, hv σ mem ctx,
        insert_below (Nat.le_refl _), fun E E' v _ hy hk => ?_⟩⟩
    simp only [Lir.Arg.eval, Option.some.injEq] at hk
    subst hk
    rw [hy (Nat.le_refl _)]
    simp

theorem argRegs_gen :
    ∀ {as : List Lir.Arg} {c : Ctx} {st st' : St} {vs : List VReg} {pre : List (Inst VReg)},
      argRegs as c st = .ok ((vs, pre), st') →
      st.next ≤ st'.next ∧ st'.consumed = st.consumed ∧ readsOf pre = [] ∧ (∀ u ∈ Lir.argsUses as, u ∈ vs) ∧
        (∀ t ∈ vs, t ∈ Lir.argsUses as ∨ (st.next ≤ t ∧ t < st'.next)) ∧
        ∀ σ mem ctx, ∃ σ', execSeq σ mem ctx pre = some (σ', mem) ∧ (∀ u, u < st.next → σ'[u]? = σ[u]?) ∧
          ∀ (E E' : Env) vals, (∀ u ∈ Lir.argsUses as, ∀ v, E'[u]? = some v → E[u]? = some v) →
            (∀ t ∈ vs, st.next ≤ t → E[t]? = σ'[t]?) → (∀ u ∈ Lir.argsUses as, u < st.next) →
            Lir.evalArgs E' as = some vals → readAll E vs = some vals
  | [], c, st, st', vs, pre, h => by
      simp only [argRegs, pure_run, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      refine ⟨Nat.le_refl _, rfl, rfl, by simp [Lir.argsUses], by simp, fun σ mem ctx => ⟨σ, rfl, fun _ _ => rfl, ?_⟩⟩
      intro E E' vals _ _ _ hv
      simp only [Lir.evalArgs, List.mapM_nil, Option.pure_def, Option.some.injEq] at hv
      subst hv
      rfl
  | a :: as, c, st, st', vs, pre, h => by
      simp only [argRegs] at h
      rw [bind_ok] at h
      obtain ⟨⟨y, pre₁⟩, st₁, h₁, h⟩ := h
      rw [bind_ok] at h
      obtain ⟨⟨vs', pres⟩, st₂, h₂, h⟩ := h
      sel_simp [Option.some.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      obtain ⟨hn₁, hc₁, hr₁, hu₁, hy₁, hv₁⟩ := argReg_gen h₁
      obtain ⟨hn₂, hc₂, hr₂, hu₂, ht₂, hv₂⟩ := argRegs_gen h₂
      have hau : ∀ u ∈ a.uses, u ∈ Lir.argsUses (a :: as) := fun u hu => by simp [Lir.argsUses, hu]
      have hasu : ∀ u ∈ Lir.argsUses as, u ∈ Lir.argsUses (a :: as) := fun u hu => by
        simp only [Lir.argsUses, List.flatMap_cons, List.mem_append] at hu ⊢; exact .inr hu
      refine ⟨Nat.le_trans hn₁ hn₂, by rw [hc₂, hc₁], by simp [hr₁, hr₂], ?_, ?_, ?_⟩
      · intro u hu
        simp only [Lir.argsUses, List.flatMap_cons, List.mem_append] at hu
        rcases hu with hu | hu
        · simp [hu₁ u hu]
        · exact List.mem_cons_of_mem _ (hu₂ u hu)
      · intro t ht
        rcases List.mem_cons.1 ht with rfl | ht
        · rcases hy₁ with hy | ⟨hy₁, hy₂⟩
          · exact .inl (hau _ hy)
          · exact .inr ⟨hy₁, Nat.lt_of_lt_of_le hy₂ hn₂⟩
        · rcases ht₂ t ht with ht | ⟨ht₁, ht₂⟩
          · exact .inl (hasu t ht)
          · exact .inr ⟨Nat.le_trans hn₁ ht₁, ht₂⟩
      · intro σ mem ctx
        obtain ⟨σ₁, he₁, hab₁, hE₁⟩ := hv₁ σ mem ctx
        obtain ⟨σ₂, he₂, hab₂, hE₂⟩ := hv₂ σ₁ mem ctx
        refine ⟨σ₂, by rw [execSeq_append he₁, he₂], fun u hu => by rw [hab₂ u (Nat.lt_of_lt_of_le hu hn₁), hab₁ u hu],
          fun E E' vals hE hfresh hlow hvals => ?_⟩
        simp only [Lir.evalArgs, List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
          Option.pure_def, Option.some.injEq] at hvals
        obtain ⟨v, hv, vs'', hvs, rfl⟩ := hvals
        have hy : E[y]? = some v := hE₁ E E' v (fun u hu w hw => hE u (hau u hu) w hw)
          (fun hle => by
            rw [hfresh y (by simp) hle]
            rcases hy₁ with hy | ⟨_, hy₂⟩
            · exact absurd (hlow y (hau y hy)) (by vomega)
            · exact hab₂ y hy₂) hv
        have hrest := hE₂ E E' vs'' (fun u hu w hw => hE u (hasu u hu) w hw)
          (fun t ht hle => hfresh t (List.mem_cons_of_mem _ ht) (Nat.le_trans hn₁ hle))
          (fun u hu => Nat.lt_of_lt_of_le (hlow u (hasu u hu)) hn₁) hvs
        simp only [readAll, List.mapM_cons, Option.bind_eq_bind] at hrest ⊢
        rw [hy, hrest]
        rfl

/-! ## Edges -/

/-- An Xv edge carries a Lir edge's arguments. -/
def EdgeRel (e : Lir.Edge) (e' : Edge VReg) (ρ σ : Env) : Prop :=
  e'.target = e.target ∧ ∀ vals, Lir.evalArgs ρ e.args = some vals → readAll σ e'.args = some vals

theorem edgeArgs_spec {e : Lir.Edge} {c : Ctx} {st st' : St} {e' : Edge VReg} {pre : List (Inst VReg)}
    (h : edgeArgs e c st = .ok ((e', pre), st')) :
    st.next ≤ st'.next ∧ st'.consumed = st.consumed ∧ readsOf pre = [] ∧ e'.target = e.target ∧
      (∀ u ∈ Lir.argsUses e.args, u ∈ e'.args) ∧ (∀ t ∈ e'.args, t ∈ Lir.argsUses e.args ∨ (st.next ≤ t ∧ t < st'.next)) ∧
      ∀ σ mem ctx, ∃ σ', execSeq σ mem ctx pre = some (σ', mem) ∧ (∀ u, u < st.next → σ'[u]? = σ[u]?) ∧
        ∀ (E E' : Env), (∀ u ∈ Lir.argsUses e.args, ∀ v, E'[u]? = some v → E[u]? = some v) →
          (∀ t ∈ e'.args, st.next ≤ t → E[t]? = σ'[t]?) → (∀ u ∈ Lir.argsUses e.args, u < st.next) →
          EdgeRel e e' E' E := by
  unfold edgeArgs at h
  rw [bind_ok] at h
  obtain ⟨⟨vs, pre'⟩, st₁, h₁, h⟩ := h
  sel_simp [Option.some.injEq] at h
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
  obtain ⟨hn, hc, hr, hu, ht, hv⟩ := argRegs_gen h₁
  refine ⟨hn, hc, hr, rfl, hu, ht, fun σ mem ctx => ?_⟩
  obtain ⟨σ', he, hab, hE⟩ := hv σ mem ctx
  exact ⟨σ', he, hab, fun E E' hEE hf hl => ⟨rfl, fun vals hvals => hE E E' vals hEE hf hl hvals⟩⟩


/-! ## `brOvf` (rule 4) -/

/-- The row of a Lir overflow operation. -/
def ovfOp : Lir.Ovf → X86.AluOp
  | .addC => .add
  | .subB => .sub

theorem ovf_eval (o : Lir.Ovf) (a b : Word) : (o.eval a b).1 = (ovfOp o).eval a b := by
  cases o <;> rfl

theorem ovf_carry (o : Lir.Ovf) (a b : Word) :
    (X86.ByteEval.aluFlags (ovfOp o) .w64 a b).test .unsignedLt = some (o.eval a b).2 := by
  cases o
  · exact add_carry a b
  · exact sub_borrow a b

theorem carry_comm (a b : Word) : (Lir.Ovf.eval .addC b a) = (Lir.Ovf.eval .addC a b) := by
  simp only [Lir.Ovf.eval, Prod.mk.injEq]
  refine ⟨UInt64.add_comm b a, ?_⟩
  rw [UInt64.add_comm b a]
  simp only [decide_eq_decide, UInt64.lt_iff_toNat_lt, UInt64.toNat_add]
  have := a.toNat_lt_size
  have := b.toNat_lt_size
  simp only [UInt64.size] at *
  omega

/-- A branch on the carry (borrow) of `add`/`sub` defining `x`. -/
theorem execJcc_alu (op : X86.AluOp) {form : X86.OpEn} {s₁ s₂ : X86.Slot}
    (hrow : (form = .MR ∧ s₁ = X86.Table.rmSlot .w64 .readWrite ∧ s₂ = X86.Table.regSlot .w64 .read) ∨
      (form = .MI8 ∧ s₁ = X86.Table.rmSlot .w64 .readWrite ∧ s₂ = X86.Table.immSlot .imm8 .w64) ∨
      (form = .MI ∧ s₁ = X86.Table.rmSlot .w64 .readWrite ∧
        s₂ = X86.Table.immSlot (X86.Table.ImmKind.argKind (X86.Table.fullImm .w64)) .w64) ∨
      (form = .RM ∧ s₁ = X86.Table.regSlot .w64 .readWrite ∧ s₂ = X86.Table.rmSlot .w64 .read))
    {ρ : Env} {mem : X86.Memory} {ctx : Word} {x a : VReg} {b : XArg VReg} {va vb : Word} {cond : X86.Condition}
    {tk : Bool} (hbind : bindRow { mn := op.mnemonic, w := .w64, form } [x] [.r a, b] = some [.tied s₁ a x, .input s₂ b])
    (ha : ρ[a]? = some va) (hb : b.valIn ρ mem ctx .w64 = some vb)
    (hc : (X86.ByteEval.aluFlags op .w64 va vb).test cond = some tk) :
    execJcc { mn := op.mnemonic, w := .w64, form } [.r a, b] [x] cond ρ mem ctx =
      some (ρ.insert x (op.eval va vb), mem, tk) := by
  simp only [execJcc, hbind, Option.bind_eq_bind, Option.bind_some, bound_alu op (.inr rfl) hrow ha hb,
    jccTaken_eq hc, X86.Encode.truncate64]
  rfl

/-- The `brOvf` row and its operands' values: `x := a op b`, taken on carry. -/
theorem brOvf_jcc (o : Lir.Ovf) {form : X86.OpEn} {ρ : Env} {mem : X86.Memory} {ctx : Word} {x a : VReg}
    {b : XArg VReg} {va vb : Word}
    (hform : (form = .MR ∧ ∃ y, b = .r y) ∨ ((form = .MI8 ∨ form = .MI) ∧ ∃ k, b = .i k) ∨ (form = .RM ∧ ∃ m, b = .m m))
    (ha : ρ[a]? = some va) (hb : b.valIn ρ mem ctx .w64 = some vb) :
    execJcc (row (ovfOp o).mnemonic .w64 form) [.r a, b] [x] .unsignedLt ρ mem ctx =
      some (ρ.insert x (o.eval va vb).1, mem, (o.eval va vb).2) := by
  rw [ovf_eval]
  rcases hform with ⟨rfl, y, rfl⟩ | ⟨hf, k, rfl⟩ | ⟨rfl, m, rfl⟩
  · exact execJcc_alu (ovfOp o) (.inl ⟨rfl, rfl, rfl⟩) ((aluBind _ _ .MR _ _).trans rfl) ha hb (ovf_carry o va vb)
  · rcases hf with rfl | rfl
    · exact execJcc_alu (ovfOp o) (.inr (.inl ⟨rfl, rfl, rfl⟩)) ((aluBind _ _ .MI8 _ _).trans rfl) ha hb
        (ovf_carry o va vb)
    · exact execJcc_alu (ovfOp o) (.inr (.inr (.inl ⟨rfl, rfl, rfl⟩))) ((aluBind _ _ .MI _ _).trans rfl) ha hb
        (ovf_carry o va vb)
  · exact execJcc_alu (ovfOp o) (.inr (.inr (.inr ⟨rfl, rfl, rfl⟩))) ((aluBind _ _ .RM _ _).trans rfl) ha hb
      (ovf_carry o va vb)


/-- What `selectBrOvf` guarantees: its prefix runs and its row defines `x`
with Lir's result, taken on carry or borrow. -/
def OvfOk (c : Ctx) (st st' : St) (o : Lir.Ovf) (x : VReg) (a b : Lir.Arg) (pre : List (Inst VReg)) (p : X86.Op)
    (args : List (XArg VReg)) : Prop :=
  Ext c st st' ∧ readsOf pre = [] ∧
    ∀ N (ρ σ : Env) mem ctx va vb, CtxLow c N → N ≤ st.next → (∀ u ∈ a.uses, u < N) → (∀ u ∈ b.uses, u < N) →
      a.eval ρ = some va → b.eval ρ = some vb → Pend c st st' ρ mem ctx → Agree N (xargsRegs args) ρ σ →
      ∃ σ', execSeq σ mem ctx pre = some (σ', mem) ∧ (∀ u, u < st.next → σ'[u]? = σ[u]?) ∧
        execJcc p args [x] .unsignedLt σ' mem ctx = some (σ'.insert x (o.eval va vb).1, mem, (o.eval va vb).2)

/-- The general `brOvf` row: `add/sub r/m64, r` or `r/m64, imm`. -/
theorem ovf_general {o : Lir.Ovf} {x a : VReg} {b : Lir.Arg} {tag : String} {c : Ctx} {st st' : St} {p : X86.Op}
    {args : List (XArg VReg)} {pre : List (Inst VReg)}
    (h : producerArgs (ovfOp o).mnemonic .w64 (.r a) b tag true c st = .ok ((p, args, pre), st')) :
    st.next ≤ st'.next ∧ st'.consumed = st.consumed ∧ readsOf pre = [] ∧ a ∈ xargsRegs args ∧
      (∀ u ∈ b.uses, u ∈ xargsRegs args) ∧
      ∀ σ mem ctx va vb, σ[a]? = some va → a < st.next → (∀ u ∈ b.uses, u < st.next) → b.eval σ = some vb →
        ∃ σ', execSeq σ mem ctx pre = some (σ', mem) ∧ (∀ u, u < st.next → σ'[u]? = σ[u]?) ∧
          execJcc p args [x] .unsignedLt σ' mem ctx = some (σ'.insert x (o.eval va vb).1, mem, (o.eval va vb).2) := by
  obtain ⟨hn, hc, hr, form, b', rfl, rfl, hform, hshape, hbu, -, hv⟩ := producerArgs_spec h
  refine ⟨hn, hc, hr, by simp [xargsRegs, XArg.regs], fun u hu => by simp [xargsRegs, hbu u hu], ?_⟩
  intro σ mem ctx va vb ha hal hbl hb
  obtain ⟨σ', he, hab, v', hv', hvt⟩ := hv σ mem ctx vb hbl hb
  rw [X86.Encode.truncate64, X86.Encode.truncate64] at hvt
  subst hvt
  refine ⟨σ', he, hab, brOvf_jcc o ?_ (by rw [hab a hal]; exact ha) hv'⟩
  rcases hshape with ⟨rfl, y, rfl⟩ | ⟨hne, k, rfl⟩
  · exact .inl ⟨rfl, y, rfl⟩
  · refine .inr (.inl ⟨?_, k, rfl⟩)
    rcases hform with h' | ⟨_, h'⟩ | h'
    · exact absurd h' hne
    · exact .inl h'
    · exact .inr h'

/-- The general row on a Lir register and a Lir argument. -/
theorem ovf_reg {o : Lir.Ovf} {x : VReg} {a b : Lir.Arg} {a' : VReg} {b' : Lir.Arg} {tag : String} {c : Ctx}
    {st st' : St} {p : X86.Op} {args : List (XArg VReg)} {pre : List (Inst VReg)}
    (hval : ∀ (ρ : Env) va vb, a.eval ρ = some va → b.eval ρ = some vb →
      ∃ va' vb', ρ[a']? = some va' ∧ b'.eval ρ = some vb' ∧ o.eval va' vb' = o.eval va vb)
    (hlow : ∀ N, (∀ u ∈ a.uses, u < N) → (∀ u ∈ b.uses, u < N) → a' < N ∧ ∀ u ∈ b'.uses, u < N)
    (h : producerArgs (ovfOp o).mnemonic .w64 (.r a') b' tag true c st = .ok ((p, args, pre), st')) :
    OvfOk c st st' o x a b pre p args := by
  obtain ⟨hn, hc, hr, ha', hb', hv⟩ := ovf_general (x := x) h
  refine ⟨Ext.of_le hn hc, hr, fun N ρ σ mem ctx va vb hcl hN hal hbl ha hb hp hag => ?_⟩
  obtain ⟨va', vb', ha'', hb'', heq⟩ := hval ρ va vb ha hb
  obtain ⟨haN, hbN⟩ := hlow N hal hbl
  rw [← heq]
  exact hv σ mem ctx va' vb' (hag.get ha' haN ha'') (Nat.lt_of_lt_of_le haN hN)
    (fun u hu => Nat.lt_of_lt_of_le (hbN u hu) hN) (hag.arg hb' hbN hb'')

/-- The general row on a materialized immediate and a Lir argument. -/
theorem ovf_mat {o : Lir.Ovf} {x : VReg} {k : Word} {b : Lir.Arg} {tag : String} {c : Ctx}
    {st st₁ st' : St} {t : VReg} {pre₁ : List (Inst VReg)} {p : X86.Op} {args : List (XArg VReg)}
    {pre : List (Inst VReg)} (h₁ : materialize k c st = .ok ((t, pre₁), st₁))
    (h : producerArgs (ovfOp o).mnemonic .w64 (.r t) b tag true c st₁ = .ok ((p, args, pre), st')) :
    OvfOk c st st' o x (.imm k) b (pre₁ ++ pre) p args := by
  obtain ⟨rfl, hn₁, hc₁, hr₁, hv₁⟩ := materialize_spec h₁
  obtain ⟨hn, hc, hr, -, hb', hv⟩ := ovf_general (x := x) h
  refine ⟨(Ext.of_le (by rw [hn₁]; exact Nat.le_succ _) hc₁).trans (Ext.of_le hn hc), by simp [hr₁, hr],
    fun N ρ σ mem ctx va vb hcl hN hal hbl ha hb hp hag => ?_⟩
  simp only [Lir.Arg.eval, Option.some.injEq] at ha
  subst ha
  have hbσ : b.eval (σ.insert st.next k) = some vb := by
    rw [eval_above (n := st.next) (fun u hu => Nat.lt_of_lt_of_le (hbl u hu) hN) (insert_below (Nat.le_refl _))]
    exact hag.arg hb' hbl hb
  obtain ⟨σ', he, hab, hj⟩ := hv (σ.insert st.next k) mem ctx k vb (by simp) (by rw [hn₁]; exact Nat.lt_succ_self _)
    (fun u hu => by rw [hn₁]; exact Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le (hbl u hu) hN)) hbσ
  refine ⟨σ', by rw [execSeq_append (hv₁ σ mem ctx), he], fun u hu => ?_, hj⟩
  rw [hab u (by rw [hn₁]; exact Nat.lt_succ_of_lt hu)]
  exact insert_below (Nat.le_refl _) u hu

/-- `brOvf` with a sunk 64-bit load (rule 9). -/
theorem ovf_sunk {o : Lir.Ovf} {x a : VReg} {y : VReg} {site : Nat} {c : Ctx} {st st₁ : St} {m : Amode VReg}
    (hs : sinkLoad? y site 8 c st = .ok (some m, st₁)) (hsite : site = c.pos) :
    Ext c st st₁ ∧ st₁.next = st.next ∧
      ∀ N (ρ σ : Env) mem ctx va vy, CtxLow c N → N ≤ st.next → ρ[y]? = some vy → σ[a]? = some va →
        Pend c st st₁ ρ mem ctx → Agree N (m.regs) ρ σ →
        execJcc (row (ovfOp o).mnemonic .w64 .RM) [.r a, .m m] [x] .unsignedLt σ mem ctx =
          some (σ.insert x (o.eval va vy).1, mem, (o.eval va vy).2) := by
  obtain ⟨hext, hn, -, hsome⟩ := sinkLoad?_spec hs hsite
  obtain ⟨hlow, hval⟩ := hsome m rfl
  refine ⟨hext, hn, fun N ρ σ mem ctx va vy hcl hN hy ha hp hag => ?_⟩
  obtain ⟨_, hmN⟩ := hlow N hcl
  obtain ⟨addr, vy', hy', haddr, hread⟩ := hval ρ mem ctx hp
  rw [hy] at hy'
  cases hy'
  have hm := hag.amode (fun u hu => hu) hmN haddr
  have hr := hread .w64 (Nat.le_refl _)
  rw [X86.Encode.truncate64] at hr
  exact brOvf_jcc o (.inr (.inr ⟨rfl, m, rfl⟩)) ha (valIn_m hm hr)

theorem selectBrOvf_spec {o : Lir.Ovf} {x : VReg} {a b : Lir.Arg} {ok ovf : Edge VReg} {c : Ctx} {st st' : St}
    {pre : List (Inst VReg)} {t : Term VReg} (h : selectBrOvf o x a b ok ovf c st = .ok ((pre, t), st')) :
    ∃ p args, t = .jcc p args [x] .unsignedLt ovf ok ∧ OvfOk c st st' o x a b pre p args := by
  have vlow : ∀ {N : Nat} {y : VReg}, (∀ u ∈ (Lir.Arg.v y).uses, u < N) → y < N :=
    fun h => h _ (by simp [Lir.Arg.uses, Lir.Arg.vreg?])
  -- a sunk operand: the row reads the register and the load
  have sunk : ∀ {a' y : VReg} {st₁ : St} {m : Amode VReg} {name : String},
      sinkLoad? y (c.site.getD c.size) 8 c st = .ok (some m, st₁) →
      (∀ (ρ : Env) va vb, a.eval ρ = some va → b.eval ρ = some vb →
        ∃ va' vy, ρ[a']? = some va' ∧ ρ[y]? = some vy ∧ o.eval va' vy = o.eval va vb) →
      (∀ N, (∀ u ∈ a.uses, u < N) → (∀ u ∈ b.uses, u < N) → a' < N) →
      OvfOk c st (fireSt name st₁) o x a b [] (row (ovfOp o).mnemonic .w64 .RM) [.r a', .m m] := by
    intro a' y st₁ m name hs hval hlow
    obtain ⟨hext, hn, hv⟩ := ovf_sunk (o := o) (x := x) (a := a') hs rfl
    refine ⟨hext.trans (Ext.fire c _ _), rfl, fun N ρ σ mem ctx va vb hcl hN hal hbl ha hb hp hag => ?_⟩
    obtain ⟨va', vy, ha', hy, heq⟩ := hval ρ va vb ha hb
    rw [← heq]
    exact ⟨σ, rfl, fun _ _ => rfl, hv N ρ σ mem ctx va' vy hcl hN hy
      (hag.get (by simp [xargsRegs, XArg.regs]) (hlow N hal hbl) ha') (hp.left (Ext.fire c _ _))
      (hag.mono fun u hu => by simp [xargsRegs, XArg.regs, hu])⟩
  unfold selectBrOvf at h
  cases o <;> cases a <;> cases b
  -- addC, v, v
  case addC.v.v a' b' =>
    sel_simp [Option.some.injEq] at h
    rw [bind_ok] at h
    obtain ⟨r₁, st₁, h₁, h⟩ := h
    cases r₁ with
    | some m =>
      sel_simp [Option.some.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      refine ⟨_, _, rfl, sunk h₁ (fun ρ va vb ha hb => ⟨va, vb, ha, hb, rfl⟩) (fun N hal _ => vlow hal)⟩
    | none =>
      obtain rfl := (sinkLoad?_spec h₁ rfl).2.2.1 rfl
      sel_simp [Option.some.injEq, beq_self_eq_true] at h
      rw [bind_ok] at h
      obtain ⟨r₂, st₂, h₂, h⟩ := h
      cases r₂ with
      | some m =>
        sel_simp [Option.some.injEq] at h
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
        refine ⟨_, _, rfl, sunk h₂ (fun ρ va vb ha hb => ⟨vb, va, hb, ha, carry_comm va vb⟩) (fun N _ hbl => vlow hbl)⟩
      | none =>
        obtain rfl := (sinkLoad?_spec h₂ rfl).2.2.1 rfl
        sel_simp [Option.some.injEq] at h
        rw [bind_ok] at h
        obtain ⟨⟨p, args, pre₂⟩, st₃, h₃, h⟩ := h
        sel_simp [Option.some.injEq] at h
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
        refine ⟨_, _, rfl, ?_⟩
        simpa using ovf_reg (o := .addC) (x := x) (a := .v a') (b := .v b') (a' := a') (b' := .v b') (fun ρ va vb ha hb => ⟨va, vb, ha, hb, rfl⟩)
          (fun N hal hbl => ⟨vlow hal, hbl⟩) h₃
  case subB.v.v a' b' =>
    sel_simp [Option.some.injEq] at h
    rw [bind_ok] at h
    obtain ⟨r₁, st₁, h₁, h⟩ := h
    cases r₁ with
    | some m =>
      sel_simp [Option.some.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      refine ⟨_, _, rfl, sunk h₁ (fun ρ va vb ha hb => ⟨va, vb, ha, hb, rfl⟩) (fun N hal _ => vlow hal)⟩
    | none =>
      obtain rfl := (sinkLoad?_spec h₁ rfl).2.2.1 rfl
      sel_simp [Option.some.injEq, beq_iff_eq, reduceCtorEq] at h
      rw [bind_ok] at h
      obtain ⟨⟨p, args, pre₂⟩, st₃, h₃, h⟩ := h
      sel_simp [Option.some.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      refine ⟨_, _, rfl, ?_⟩
      simpa using ovf_reg (o := .subB) (x := x) (a := .v a') (b := .v b') (a' := a') (b' := .v b') (fun ρ va vb ha hb => ⟨va, vb, ha, hb, rfl⟩)
        (fun N hal hbl => ⟨vlow hal, hbl⟩) h₃
  case addC.v.imm a' k =>
    sel_simp [Option.some.injEq] at h
    rw [bind_ok] at h
    obtain ⟨⟨p, args, pre₂⟩, st₃, h₃, h⟩ := h
    sel_simp [Option.some.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    refine ⟨_, _, rfl, ?_⟩
    simpa using ovf_reg (o := .addC) (x := x) (a := .v a') (b := .imm k) (a' := a') (b' := .imm k)
      (fun ρ va vb ha hb => ⟨va, vb, ha, hb, rfl⟩) (fun N hal hbl => ⟨vlow hal, hbl⟩) h₃
  case subB.v.imm a' k =>
    sel_simp [Option.some.injEq] at h
    rw [bind_ok] at h
    obtain ⟨⟨p, args, pre₂⟩, st₃, h₃, h⟩ := h
    sel_simp [Option.some.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    refine ⟨_, _, rfl, ?_⟩
    simpa using ovf_reg (o := .subB) (x := x) (a := .v a') (b := .imm k) (a' := a') (b' := .imm k)
      (fun ρ va vb ha hb => ⟨va, vb, ha, hb, rfl⟩) (fun N hal hbl => ⟨vlow hal, hbl⟩) h₃
  case addC.imm.v k b' =>
    sel_simp [Option.some.injEq] at h
    rw [bind_ok] at h
    obtain ⟨⟨p, args, pre₂⟩, st₃, h₃, h⟩ := h
    sel_simp [Option.some.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    refine ⟨_, _, rfl, ?_⟩
    simpa using ovf_reg (o := .addC) (x := x) (a := .imm k) (b := .v b') (a' := b') (b' := .imm k)
      (fun ρ va vb ha hb => ⟨vb, va, hb, ha, carry_comm va vb⟩) (fun N _ hbl => ⟨vlow hbl, by simp [imm_uses]⟩) h₃
  case subB.imm.v k b' =>
    sel_simp [Option.some.injEq] at h
    rw [bind_ok] at h
    obtain ⟨⟨t', pre₁⟩, st₁, h₁, h⟩ := h
    sel_simp [Option.some.injEq] at h
    rw [bind_ok] at h
    obtain ⟨⟨p, args, pre₂⟩, st₃, h₃, h⟩ := h
    sel_simp [Option.some.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    exact ⟨_, _, rfl, ovf_mat (o := .subB) h₁ h₃⟩
  case addC.imm.imm ka kb =>
    sel_simp [Option.some.injEq] at h
    rw [bind_ok] at h
    obtain ⟨⟨t', pre₁⟩, st₁, h₁, h⟩ := h
    sel_simp [Option.some.injEq] at h
    rw [bind_ok] at h
    obtain ⟨⟨p, args, pre₂⟩, st₃, h₃, h⟩ := h
    sel_simp [Option.some.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    exact ⟨_, _, rfl, ovf_mat (o := .addC) h₁ h₃⟩
  case subB.imm.imm ka kb =>
    sel_simp [Option.some.injEq] at h
    rw [bind_ok] at h
    obtain ⟨⟨t', pre₁⟩, st₁, h₁, h⟩ := h
    sel_simp [Option.some.injEq] at h
    rw [bind_ok] at h
    obtain ⟨⟨p, args, pre₂⟩, st₃, h₃, h⟩ := h
    sel_simp [Option.some.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    exact ⟨_, _, rfl, ovf_mat (o := .subB) h₁ h₃⟩


/-! ## Terminators -/

/-- The Xv terminator `t'` after `pre` does what the Lir terminator `t` does
from `ρ`. -/
def TermRun (t : Lir.Term) (pre : List (Inst VReg)) (t' : Term VReg) (ρ σ : Env) (mem : X86.Memory) (ctx : Word)
    (n : Nat) : Prop :=
  match t with
  | .jump e => ∃ e', t' = .jmp e' ∧ ∃ σ', execSeq σ mem ctx pre = some (σ', mem) ∧
      (∀ u, u < n → σ'[u]? = σ[u]?) ∧ EdgeRel e e' ρ σ'
  | .br c w a b tt ff => ∃ p pargs cond tt' ff', t' = .jcc p pargs [] cond tt' ff' ∧
      ∀ va vb, a.eval ρ = some va → b.eval ρ = some vb →
        ∃ σ', execSeq σ mem ctx pre = some (σ', mem) ∧ (∀ u, u < n → σ'[u]? = σ[u]?) ∧
          execJcc p pargs [] cond σ' mem ctx = some (σ', mem, c.holds w va vb) ∧
          EdgeRel tt tt' ρ σ' ∧ EdgeRel ff ff' ρ σ'
  | .brOvf o x a b ok ovf => ∃ p pargs ok' ovf', t' = .jcc p pargs [x] .unsignedLt ovf' ok' ∧
      ∀ va vb, a.eval ρ = some va → b.eval ρ = some vb →
        ∃ σ', execSeq σ mem ctx pre = some (σ', mem) ∧ (∀ u, u < n → σ'[u]? = σ[u]?) ∧
          execJcc p pargs [x] .unsignedLt σ' mem ctx = some (σ'.insert x (o.eval va vb).1, mem, (o.eval va vb).2) ∧
          EdgeRel ok ok' (ρ.insert x (o.eval va vb).1) (σ'.insert x (o.eval va vb).1) ∧
          EdgeRel ovf ovf' (ρ.insert x (o.eval va vb).1) (σ'.insert x (o.eval va vb).1)
  | .ret as => ∃ vs, t' = .ret vs ∧ ∃ σ', execSeq σ mem ctx pre = some (σ', mem) ∧
      (∀ u, u < n → σ'[u]? = σ[u]?) ∧ ∀ vals, Lir.evalArgs ρ as = some vals → readAll σ' vs = some vals
  | .tail g as => ∃ vs, t' = .tail g vs ∧ ∃ σ', execSeq σ mem ctx pre = some (σ', mem) ∧
      (∀ u, u < n → σ'[u]? = σ[u]?) ∧ ∀ vals, Lir.evalArgs ρ as = some vals → readAll σ' vs = some vals
  | .fail r => t' = .fail r ∧ pre = []
  | .trap => t' = .trap ∧ pre = []

/-- What the instructions and terminator selected for a Lir terminator guarantee. -/
def TermOk (c : Ctx) (st st' : St) (t : Lir.Term) (pre : List (Inst VReg)) (t' : Term VReg) : Prop :=
  Ext c st st' ∧ ∀ N (ρ σ : Env) mem ctx, CtxLow c N → N ≤ st.next → (∀ u ∈ t.uses, u < N) →
    (∀ u ∈ t.defs, u < N) → (∀ u ∈ t.edgeUses, u < N) → Pend c st st' ρ mem ctx →
    Agree N (readsOf pre ++ t'.uses ++ t'.edgeUses) ρ σ → TermRun t pre t' ρ σ mem ctx st.next

/-- An edge's arguments, read after the prefix it shares. -/
theorem edge_rel {e : Lir.Edge} {e' : Edge VReg} {st₀ st₁ : St} {N : Nat} {ρ σ σ₁ σ' : Env}
    (hfresh : ∀ t ∈ e'.args, t ∈ Lir.argsUses e.args ∨ (st₀.next ≤ t ∧ t < st₁.next))
    (hE : ∀ (E E' : Env), (∀ u ∈ Lir.argsUses e.args, ∀ v, E'[u]? = some v → E[u]? = some v) →
      (∀ t ∈ e'.args, st₀.next ≤ t → E[t]? = σ₁[t]?) → (∀ u ∈ Lir.argsUses e.args, u < st₀.next) → EdgeRel e e' E' E)
    (hlow : ∀ u ∈ Lir.argsUses e.args, u < N) (hN : N ≤ st₀.next)
    (hag : Agree N (Lir.argsUses e.args) ρ σ) (hσ' : ∀ u, u < N → σ'[u]? = σ[u]?)
    (hσ₁ : ∀ t, st₀.next ≤ t → t < st₁.next → σ'[t]? = σ₁[t]?) : EdgeRel e e' ρ σ' := by
  refine hE σ' ρ (fun u hu v hv => ?_) (fun t ht hle => ?_) (fun u hu => Nat.lt_of_lt_of_le (hlow u hu) hN)
  · rw [hσ' u (hlow u hu)]; exact hag u hu (hlow u hu) v hv
  · rcases hfresh t ht with h' | ⟨_, h'⟩
    · exact absurd (Nat.lt_of_lt_of_le (hlow t h') hN) (by vomega)
    · exact hσ₁ t hle h'


theorem Agree.insert {N : Nat} {S : List VReg} {ρ σ : Env} (h : Agree N S ρ σ) (x : VReg) (v : Word) :
    Agree N S (ρ.insert x v) (σ.insert x v) := by
  intro u hu hN w hw
  by_cases hx : x = u
  · subst hx; simpa using hw
  · rw [insert_ne hx] at hw ⊢; exact h u hu hN w hw

theorem selectTerm_ok {t : Lir.Term} {c : Ctx} {st st' : St} {pre : List (Inst VReg)} {t' : Term VReg}
    (h : selectTerm t c st = .ok ((pre, t'), st')) : TermOk c st st' t pre t' := by
  cases t with
  | jump e =>
    simp only [selectTerm] at h
    rw [bind_ok] at h
    obtain ⟨⟨e', pe⟩, st₁, h₁, h⟩ := h
    sel_simp [Option.some.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    obtain ⟨hn, hc, hr, -, hu, hfr, hv⟩ := edgeArgs_spec h₁
    refine ⟨(Ext.of_le hn hc).trans (Ext.fire c _ _), fun N ρ σ mem ctx hcl hN htu htd hte hp hag => ⟨e', rfl, ?_⟩⟩
    obtain ⟨σ', hex, hab, hE⟩ := hv σ mem ctx
    have hlow : ∀ u ∈ Lir.argsUses e.args, u < N := fun u hu' => hte u (by simp [Lir.Term.edgeUses, Lir.Term.edges, hu'])
    refine ⟨σ', hex, hab, edge_rel hfr hE hlow hN (hag.mono fun u hu' => ?_) (fun u hu' => hab u (Nat.lt_of_lt_of_le hu' hN))
      (fun _ _ _ => rfl)⟩
    simp [Term.edgeUses, Term.edges, hu u hu']
  | br cond w a b tt ff =>
    simp only [selectTerm] at h
    rw [bind_ok] at h
    obtain ⟨⟨tt', pt⟩, st₁, h₁, h⟩ := h
    simp only at h
    rw [bind_ok] at h
    obtain ⟨⟨ff', pf⟩, st₂, h₂, h⟩ := h
    simp only at h
    rw [bind_ok] at h
    obtain ⟨pr, st₃, h₃, h⟩ := h
    sel_simp [Option.some.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    obtain ⟨hn₁, hc₁, hr₁, -, hu₁, hfr₁, hv₁⟩ := edgeArgs_spec h₁
    obtain ⟨hn₂, hc₂, hr₂, -, hu₂, hfr₂, hv₂⟩ := edgeArgs_spec h₂
    obtain ⟨hext₃, hr₃, hv₃⟩ := compareProducer_spec h₃
    have he₁₂ : Ext c st st₂ := (Ext.of_le hn₁ hc₁).trans (Ext.of_le hn₂ hc₂)
    refine ⟨he₁₂.trans (hext₃.trans (Ext.fire c _ _)), fun N ρ σ mem ctx hcl hN htu htd hte hp hag => ?_⟩
    refine ⟨pr.op, pr.args, pr.cond, tt', ff', rfl, fun va vb ha hb => ?_⟩
    have hlt : ∀ u ∈ Lir.argsUses tt.args, u < N := fun u hu' => hte u (by simp [Lir.Term.edgeUses, Lir.Term.edges, hu'])
    have hlf : ∀ u ∈ Lir.argsUses ff.args, u < N := fun u hu' => hte u (by simp [Lir.Term.edgeUses, Lir.Term.edges, hu'])
    obtain ⟨σ₁, he₁, hab₁, hE₁⟩ := hv₁ σ mem ctx
    obtain ⟨σ₂, he₂, hab₂, hE₂⟩ := hv₂ σ₁ mem ctx
    have hab₁₂ : ∀ u, u < st.next → σ₂[u]? = σ[u]? := above_trans hab₁ hab₂ hn₁
    obtain ⟨σ₃, he₃, hab₃, -, hd⟩ := hv₃ N ρ σ₂ mem ctx va vb hcl (Nat.le_trans hN he₁₂.next)
      (fun u hu' => htu u (by simp [Lir.Term.uses, hu'])) (fun u hu' => htu u (by simp [Lir.Term.uses, hu'])) ha hb
      ((hp.right he₁₂).left (Ext.fire c _ _))
      ((hag.mono fun u hu' => by simp [Term.uses, hu']).above hab₁₂ hN)
    have hab₃' : ∀ u, u < st.next → σ₃[u]? = σ[u]? := above_trans hab₁₂ hab₃ he₁₂.next
    refine ⟨σ₃, by rw [execSeq_append (by rw [execSeq_append he₁, he₂]), he₃], hab₃', hd.jcc, ?_, ?_⟩
    · exact edge_rel hfr₁ hE₁ hlt hN (hag.mono fun u hu' => by simp [Term.edgeUses, Term.edges, hu₁ u hu'])
        (fun u hu' => hab₃' u (Nat.lt_of_lt_of_le hu' hN))
        (fun t₀ _ ht₂ => by rw [hab₃ t₀ (Nat.lt_of_lt_of_le ht₂ hn₂), hab₂ t₀ ht₂])
    · exact edge_rel hfr₂ (fun E E' h₁' h₂' h₃' => hE₂ E E' h₁' h₂' h₃') hlf (Nat.le_trans hN hn₁)
        (hag.mono fun u hu' => by simp [Term.edgeUses, Term.edges, hu₂ u hu'])
        (fun u hu' => hab₃' u (Nat.lt_of_lt_of_le hu' hN))
        (fun t₀ _ ht₂ => hab₃ t₀ ht₂)
  | brOvf o x a b ok ovf =>
    simp only [selectTerm] at h
    rw [bind_ok] at h
    obtain ⟨⟨ok', p₁⟩, st₁, h₁, h⟩ := h
    simp only at h
    rw [bind_ok] at h
    obtain ⟨⟨ovf', p₂⟩, st₂, h₂, h⟩ := h
    simp only at h
    rw [bind_ok] at h
    obtain ⟨⟨pre₃, term⟩, st₃, h₃, h⟩ := h
    sel_simp [Option.some.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    obtain ⟨hn₁, hc₁, hr₁, -, hu₁, hfr₁, hv₁⟩ := edgeArgs_spec h₁
    obtain ⟨hn₂, hc₂, hr₂, -, hu₂, hfr₂, hv₂⟩ := edgeArgs_spec h₂
    obtain ⟨p, args, rfl, hext₃, hr₃, hv₃⟩ := selectBrOvf_spec h₃
    have he₁₂ : Ext c st st₂ := (Ext.of_le hn₁ hc₁).trans (Ext.of_le hn₂ hc₂)
    refine ⟨he₁₂.trans hext₃, fun N ρ σ mem ctx hcl hN htu htd hte hp hag => ?_⟩
    refine ⟨p, args, ok', ovf', rfl, fun va vb ha hb => ?_⟩
    have hxN : x < N := htd x (by simp [Lir.Term.defs])
    have hlo : ∀ u ∈ Lir.argsUses ok.args, u < N := fun u hu' => hte u (by simp [Lir.Term.edgeUses, Lir.Term.edges, hu'])
    have hlv : ∀ u ∈ Lir.argsUses ovf.args, u < N := fun u hu' => hte u (by simp [Lir.Term.edgeUses, Lir.Term.edges, hu'])
    obtain ⟨σ₁, he₁, hab₁, hE₁⟩ := hv₁ σ mem ctx
    obtain ⟨σ₂, he₂, hab₂, hE₂⟩ := hv₂ σ₁ mem ctx
    have hab₁₂ : ∀ u, u < st.next → σ₂[u]? = σ[u]? := above_trans hab₁ hab₂ hn₁
    obtain ⟨σ₃, he₃, hab₃, hj⟩ := hv₃ N ρ σ₂ mem ctx va vb hcl (Nat.le_trans hN he₁₂.next)
      (fun u hu' => htu u (by simp [Lir.Term.uses, hu'])) (fun u hu' => htu u (by simp [Lir.Term.uses, hu'])) ha hb
      (hp.right he₁₂) ((hag.mono fun u hu' => by simp [Term.uses, hu']).above hab₁₂ hN)
    have hab₃' : ∀ u, u < st.next → σ₃[u]? = σ[u]? := above_trans hab₁₂ hab₃ he₁₂.next
    have hins : ∀ u, u < N → (σ₃.insert x (o.eval va vb).1)[u]? = (σ.insert x (o.eval va vb).1)[u]? := by
      intro u hu'
      by_cases hux : x = u
      · subst hux; simp
      · rw [insert_ne hux, insert_ne hux]; exact hab₃' u (Nat.lt_of_lt_of_le hu' hN)
    have hxt : ∀ t₀, st.next ≤ t₀ → x ≠ t₀ := fun t₀ ht => by have := Nat.lt_of_lt_of_le hxN hN; vomega
    refine ⟨σ₃, by rw [execSeq_append (by rw [execSeq_append he₁, he₂]), he₃], hab₃', hj, ?_, ?_⟩
    · exact edge_rel hfr₁ hE₁ hlo hN
        ((hag.mono fun u hu' => by simp [Term.edgeUses, Term.edges, hu₁ u hu']).insert x _) hins
        (fun t₀ ht₀ ht₂ => by
          rw [insert_ne (hxt t₀ ht₀), hab₃ t₀ (Nat.lt_of_lt_of_le ht₂ hn₂), hab₂ t₀ ht₂])
    · exact edge_rel hfr₂ (fun E E' h₁' h₂' h₃' => hE₂ E E' h₁' h₂' h₃') hlv (Nat.le_trans hN hn₁)
        ((hag.mono fun u hu' => by simp [Term.edgeUses, Term.edges, hu₂ u hu']).insert x _) hins
        (fun t₀ ht₀ ht₂ => by rw [insert_ne (hxt t₀ (Nat.le_trans hn₁ ht₀)), hab₃ t₀ ht₂])
  | ret as =>
    simp only [selectTerm] at h
    rw [bind_ok] at h
    obtain ⟨⟨vs, pre'⟩, st₁, h₁, h⟩ := h
    sel_simp [Option.some.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    obtain ⟨hn, hc, hr, hu, hfr, hv⟩ := argRegs_gen h₁
    refine ⟨(Ext.of_le hn hc).trans (Ext.fire c _ _), fun N ρ σ mem ctx hcl hN htu htd hte hp hag => ⟨vs, rfl, ?_⟩⟩
    have hlow : ∀ u ∈ Lir.argsUses as, u < N := fun u hu' => htu u (by simpa [Lir.Term.uses] using hu')
    obtain ⟨σ', hex, hab, hE⟩ := hv σ mem ctx
    refine ⟨σ', hex, hab, fun vals hvals => hE σ' ρ vals (fun u hu' v hv' => ?_) (fun _ _ _ => rfl)
      (fun u hu' => Nat.lt_of_lt_of_le (hlow u hu') hN) hvals⟩
    rw [hab u (Nat.lt_of_lt_of_le (hlow u hu') hN)]
    exact hag u (by simp [Term.uses, hu u hu']) (hlow u hu') v hv'
  | tail g as =>
    simp only [selectTerm] at h
    rw [bind_ok] at h
    obtain ⟨⟨vs, pre'⟩, st₁, h₁, h⟩ := h
    sel_simp [Option.some.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    obtain ⟨hn, hc, hr, hu, hfr, hv⟩ := argRegs_gen h₁
    refine ⟨(Ext.of_le hn hc).trans (Ext.fire c _ _), fun N ρ σ mem ctx hcl hN htu htd hte hp hag => ⟨vs, rfl, ?_⟩⟩
    have hlow : ∀ u ∈ Lir.argsUses as, u < N := fun u hu' => htu u (by simpa [Lir.Term.uses] using hu')
    obtain ⟨σ', hex, hab, hE⟩ := hv σ mem ctx
    refine ⟨σ', hex, hab, fun vals hvals => hE σ' ρ vals (fun u hu' v hv' => ?_) (fun _ _ _ => rfl)
      (fun u hu' => Nat.lt_of_lt_of_le (hlow u hu') hN) hvals⟩
    rw [hab u (Nat.lt_of_lt_of_le (hlow u hu') hN)]
    exact hag u (by simp [Term.uses, hu u hu']) (hlow u hu') v hv'
  | fail r =>
    simp only [selectTerm] at h
    sel_simp [Option.some.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    exact ⟨Ext.fire c _ _, fun _ _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl, rfl⟩⟩
  | trap =>
    simp only [selectTerm] at h
    sel_simp [Option.some.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    exact ⟨Ext.fire c _ _, fun _ _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl, rfl⟩⟩

end Compilatrix.Xv.Select.Proof
