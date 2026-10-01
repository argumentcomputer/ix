import Compilatrix.Rt.Proof.SwitchSim

/-!
# Terminators

What each Cfg terminator's lowering leaves in the Lir function at the
position where its code starts: `jump` an edge (`term_jump`), `ret` and
`tcall` their Lir terminators or a `fail natOverflow` (an operand literal
without a word), `trap` a trap, and the fused `switch` on a comparison's
`Bool` a `br` on the comparison (`fused_sim`).
-/

set_option autoImplicit false

namespace Compilatrix.Rt.Proof

open Compilatrix.Lir (Word)
open Compilatrix.Rt.Lower
open Compilatrix.Src (NatMap)

/-- A block closed by the lowering, in the Lir function. -/
def ClosedAt (F : Lir.Func) (off : Nat) (st : St) (t : Lir.Term) : Prop :=
  ∃ lb, F.blocks[off + st.cur]? = some lb ∧ lb.body.size = st.acc.length ∧ lb.term = t

theorem closedAt_of {f : Fir.FunId} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock}
    (hH : Holds f F off starts C) {st stF : St} {t : PTerm} (hg : Grows (closeSt st t) stF) (hC : Ext C stF)
    {lt : Lir.Term} (hres : resolveTerm f off starts t = .ok lt) : ClosedAt F off st lt := by
  obtain ⟨lb, hlb, -, hsize, hterm⟩ := closed_block hH (close_ext hg hC)
  rw [hres] at hterm
  exact ⟨lb, hlb, hsize, (Except.ok.inj hterm).symm⟩

/-- A closed block's terminator fails. -/
theorem fails_closed {lp : Lir.Program} {fn : Nat} {F : Lir.Func} {off : Nat} {st : St}
    (hF : lp.funcs[fn]? = some F) (h : ClosedAt F off st (.fail .natOverflow)) (mem : X86.Memory) (ctx : Word)
    (ρl : Lir.Env) (rest : List Lir.Frame) :
    Sem.Fails (Lir.semStep lp) (Lir.atState mem ctx fn (off + st.cur) st.acc.length ρl rest) := by
  obtain ⟨lb, hlb, hsize, hterm⟩ := h
  exact ⟨0, _, .natOverflow, .refl _, Lir.semStep_fail.2 (Lir.fail_at hF hlb hsize.symm hterm)⟩

/-! ## `jump`, `ret`, `tcall`, `trap` -/

theorem term_jump {f : Fir.FunId} {T : Tables} {src : Nat} {e : Cfg.Edge} {st st' : St}
    (h : (term f T src (.jump e)).run st = .ok ((), st')) (hl : Labels st) (ho : Open st) :
    ∃ pe st₁, (edge f src e).run st = .ok (pe, st₁) ∧ st' = closeSt st₁ (.jump pe) ∧ Grows st st' ∧
      st₁.cur = st.cur ∧ st₁.acc = st.acc := by
  simp only [term] at h
  obtain ⟨pe, st₁, h₁, h₂⟩ := run_bind h
  rw [close_run] at h₂
  simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at h₂
  obtain ⟨-, hg, hl₁, hc, ha, -, -, ho₁, -⟩ := edge_facts h₁ hl
  exact ⟨pe, st₁, h₁, h₂.symm, h₂ ▸ hg.trans (grows_close (ho₁ ho) _), hc, ha⟩

theorem term_ret {f : Fir.FunId} {T : Tables} {src : Nat} {a : Fir.Arg} {st st' : St}
    (h : (term f T src (.ret a)).run st = .ok ((), st')) (ho : Open st) :
    Grows st st' ∧ ((∃ la, operand f a = .ok (some la) ∧ st' = closeSt st (.ret la)) ∨
      st' = closeSt st (.fail .natOverflow)) := by
  simp only [term] at h
  obtain ⟨b, st₁, h₁, h₂⟩ := run_bind h
  simp only [StateT.run, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq, true_and] at h₂
  subst h₂
  rcases withOperands_run h₁ with ⟨las, hops, -, hk⟩ | ⟨-, -, rfl⟩
  · obtain ⟨la, rfl, hop⟩ := operands_one hops
    rw [close_run] at hk
    simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hk
    subst hk
    exact ⟨grows_close ho _, .inl ⟨la, hop, rfl⟩⟩
  · exact ⟨grows_close ho _, .inr rfl⟩

theorem term_tcall {f : Fir.FunId} {T : Tables} {src : Nat} {g : Nat} {as : List Fir.Arg} {st st' : St}
    (h : (term f T src (.tcall g as)).run st = .ok ((), st')) (ho : Open st) :
    Grows st st' ∧ ((∃ las, operands f as = .ok (some las) ∧ st' = closeSt st (.tail g las)) ∨
      st' = closeSt st (.fail .natOverflow)) := by
  simp only [term] at h
  obtain ⟨b, st₁, h₁, h₂⟩ := run_bind h
  simp only [StateT.run, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq, true_and] at h₂
  subst h₂
  rcases withOperands_run h₁ with ⟨las, hops, -, hk⟩ | ⟨-, -, rfl⟩
  · rw [close_run] at hk
    simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hk
    subst hk
    exact ⟨grows_close ho _, .inl ⟨las, hops, rfl⟩⟩
  · exact ⟨grows_close ho _, .inr rfl⟩

theorem term_trap {f : Fir.FunId} {T : Tables} {src : Nat} {st st' : St}
    (h : (term f T src .trap).run st = .ok ((), st')) : st' = closeSt st .trap := by
  simp only [term] at h
  rw [close_run] at h
  simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at h
  exact h.symm

/-! ## Fused switches -/

theorem boolEdge_some (alts : List (Key.CtorKey × Cfg.Edge)) (d : Option Cfg.Edge) (k : Key.CtorKey) :
    boolEdge alts d (some k) = match Cfg.selectEdge k alts none with
      | some e => some e
      | none => d := by
  induction alts with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨k', e⟩ := p
    simp only [boolEdge, List.find?_cons, Cfg.selectEdge] at ih ⊢
    by_cases hk : k' = k
    · subst hk; simp
    · have : (some k == some k') = false := by simpa using Ne.symm hk
      simp only [this, hk, ↓reduceIte]
      exact ih

theorem fusedClose_run {c : Lir.Cond} {a b : Lir.Arg} {te fe : Option PEdge} {st st' : St}
    (h : (fusedClose c a b te fe).run st = .ok ((), st')) :
    ∃ t, st' = closeSt st t ∧
      (∀ pt pf, te = some pt → fe = some pf → t = .br c a b pt pf) ∧
      (∀ pt, te = some pt → fe = none → t = .jump pt) ∧
      (∀ pf, te = none → fe = some pf → t = .jump pf) := by
  unfold fusedClose at h
  split at h <;> rw [close_run] at h <;> simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at h <;> subst h <;>
    exact ⟨_, rfl, by simp, by simp, by simp⟩

/-- **A fused switch takes the edge Cfg's `switch` selects on the
comparison's `Bool`.** -/
theorem fused_sim {T : Tables} {f : Fir.FunId} {lp : Lir.Program} {fn : Nat} {F : Lir.Func} {off : Nat}
    {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F) (hH : Holds f F off starts C)
    {src : Nat} {c : Lir.Cond} {la lb : Lir.Arg} {alts : List (Key.CtorKey × Cfg.Edge)} {d : Option Cfg.Edge}
    {st st' stF : St} (hrun : (fusedSwitch f T src c la lb alts d).run st = .ok ((), st')) (hl : Labels st)
    (ho : Open st) (hg : Grows st' stF) (hC : Ext C stF) {mem : X86.Memory} {ctx : Word}
    {rest : List Lir.Frame} {ρl : Lir.Env} {wa wb : Word} (ha : la.eval ρl = some wa) (hb : lb.eval ρl = some wb)
    {key : Key.CtorKey}
    (hkey : (if c.holds .w64 wa wb then T.known.boolTrue else T.known.boolFalse) = some key)
    {e : Cfg.Edge} (hsel : Cfg.selectEdge key alts d = some e) :
    ∃ pe le, EdgeOk C f e pe ∧ e.back = decide (e.target ≤ src) ∧ resolveEdge f off starts pe = .ok le ∧
      ReachesEdge lp fn F mem ctx rest (off + st.cur) (Lir.atState mem ctx fn (off + st.cur) st.acc.length ρl rest)
        le ρl := by
  unfold fusedSwitch at hrun
  obtain ⟨te, st₁, h₁, h₂⟩ := run_bind hrun
  obtain ⟨fe, st₂, h₃, h₄⟩ := run_bind h₂
  obtain ⟨hg₁, hl₁, hc₁, ha₁, -, -, ho₁, hte⟩ := dflt_run h₁ hl
  obtain ⟨hg₂, hl₂, hc₂, ha₂, -, -, ho₂, hfe⟩ := dflt_run h₃ hl₁
  obtain ⟨t, rfl, hbr, hjt, hjf⟩ := fusedClose_run h₄
  have ho₂' := ho₂ (ho₁ ho)
  have hgF : Grows (closeSt st₂ t) stF := hg
  have hg₂F : Grows st₂ stF := (grows_close ho₂' t).trans hg
  have hcur : st₂.cur = st.cur := hc₂.trans hc₁
  have hacc : st₂.acc = st.acc := ha₂.trans ha₁
  rw [← hcur, ← hacc]
  have hsel' : boolEdge alts d (some key) = some e := by
    rw [boolEdge_some]; rw [selectEdge_dflt] at hsel
    cases h : Cfg.selectEdge key alts none <;> simp only [h] at hsel ⊢ <;> exact hsel
  have hte' := hte (hg₂.trans hg₂F) hC
  have hfe' := hfe hg₂F hC
  cases hcw : c.holds .w64 wa wb with
  | true =>
    simp only [hcw, ↓reduceIte] at hkey
    rw [hkey, hsel'] at hte'
    rcases hte' with ⟨h, -⟩ | ⟨e', pt, he', rfl, hok, hback⟩
    · cases h
    · cases he'
      cases hfe'' : fe with
      | some pf =>
        have := hbr pt pf rfl hfe''
        subst this
        obtain ⟨lt, lf, hlt, hlf, hr⟩ := closed_br (mem := mem) (ctx := ctx) (rest := rest) hF hH hgF hC ha hb
        rw [hcw] at hr
        exact ⟨pt, lt, hok, hback, hlt, hr⟩
      | none =>
        have := hjt pt rfl hfe''
        subst this
        obtain ⟨le, hle, hr⟩ := closed_jump (mem := mem) (ctx := ctx) (rest := rest) hF hH hgF hC ρl
        exact ⟨pt, le, hok, hback, hle, hr⟩
  | false =>
    simp only [hcw, Bool.false_eq_true, ↓reduceIte] at hkey
    rw [hkey, hsel'] at hfe'
    rcases hfe' with ⟨h, -⟩ | ⟨e', pf, he', rfl, hok, hback⟩
    · cases h
    · cases he'
      cases hte'' : te with
      | some pt =>
        have := hbr pt pf hte'' rfl
        subst this
        obtain ⟨lt, lf, hlt, hlf, hr⟩ := closed_br (mem := mem) (ctx := ctx) (rest := rest) hF hH hgF hC ha hb
        rw [hcw] at hr
        exact ⟨pf, lf, hok, hback, hlf, hr⟩
      | none =>
        have := hjf pf hte'' rfl
        subst this
        obtain ⟨le, hle, hr⟩ := closed_jump (mem := mem) (ctx := ctx) (rest := rest) hF hH hgF hC ρl
        exact ⟨pf, le, hok, hback, hle, hr⟩

end Compilatrix.Rt.Proof
