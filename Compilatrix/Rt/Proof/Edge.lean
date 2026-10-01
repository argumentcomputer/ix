import Compilatrix.Rt.Proof.Instr

/-!
# Edges and closed blocks

`edge f src e` lowers a Cfg edge to an edge into the target's chunk, or (an
argument literal without a word) into a new cold `fail natOverflow` block;
`EdgeOk` records which, as the final chunk holds it. `ReachesEdge` is where
a terminator's simulation ends: Lir reaches a block whose terminator takes
the lowered edge. `edge_complete` finishes it: Lir enters the target's
chunk with its parameters bound to the related argument words, charging
the clock when Cfg's edge is a back edge, or fails.

`closed_block`: a block the lowering closed with `t` sits in the Lir
function with the statements emitted into it and `t` resolved.
-/

set_option autoImplicit false

namespace Compilatrix.Rt.Proof

open Compilatrix.Lir (Word)
open Compilatrix.Rt.Lower
open Compilatrix.Src (NatMap)

/-! ## Binding parameters -/

/-- Edge arguments bind the target's parameters on both sides. -/
theorem bind_rel {T : Tables} {P : List Word} {D : Nat → Prop} {sup : Nat} :
    ∀ {ps : List Nat} {vs : List Own.RVal} {ws : List Word} {ρ : Own.Env} {ρl : Lir.Env},
      EnvRel T P D sup ρ ρl → ListRel (ValRel T P) vs ws → ps.length = vs.length → (∀ y ∈ ps, y < sup) →
      ∃ ρt, Lir.bindParams ρl ps ws = some ρt ∧ EnvRel T P D sup (Own.bindAll ρ ps vs) ρt
  | [], [], [], _, _, hρ, _, _, _ => ⟨_, rfl, hρ⟩
  | y :: ps, v :: vs, w :: ws, _, _, hρ, .cons hv hrel, hlen, hps => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    obtain ⟨ρt, h1, h2⟩ := bind_rel (hρ.insert (hps y (by simp)) hv) hrel hlen (fun z hz => hps z (by simp [hz]))
    exact ⟨ρt, h1, h2⟩
  | [], _ :: _, _, _, _, _, _, hlen, _ => by simp at hlen
  | _ :: _, [], _, _, _, _, _, hlen, _ => by simp at hlen

/-! ## Lowered edges -/

/-- The state after adding a cold block. -/
def coldSt (st : St) (t : PTerm) : St :=
  { st with done := st.done.insert st.next { term := t, cold := true }, next := st.next + 1 }

theorem edge_run {f : Fir.FunId} {src : Nat} {e : Cfg.Edge} {st st' : St} {pe : PEdge}
    (h : (edge f src e).run st = .ok (pe, st')) :
    e.back = decide (e.target ≤ src) ∧
      ((∃ las, operands f e.args = .ok (some las) ∧ pe = ⟨.blk e.target, las⟩ ∧ st' = st) ∨
       (operands f e.args = .ok none ∧ pe = loc st.next ∧ st' = coldSt st (.fail .natOverflow))) := by
  unfold edge at h
  by_cases hb : (e.back == decide (e.target ≤ src)) = true
  · have hb' : e.back = decide (e.target ≤ src) := by simpa using hb
    refine ⟨hb', ?_⟩
    simp only [hb, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    cases hop : operands f e.args with
    | error err =>
      simp [hop, bind, StateT.bind, StateT.run, MonadLift.monadLift, liftM, monadLift, StateT.lift, Except.bind,
        pure, StateT.pure, Except.pure] at h
    | ok o =>
      cases o with
      | none =>
        simp [hop, bind, StateT.bind, StateT.run, MonadLift.monadLift, liftM, monadLift, StateT.lift, Except.bind,
          pure, StateT.pure, Except.pure, coldBlock, newLabel, put, modify, modifyGet, MonadStateOf.modifyGet,
          StateT.modifyGet, MonadState.modifyGet] at h
        exact .inr ⟨rfl, h.1.symm, h.2.symm⟩
      | some las =>
        simp [hop, bind, StateT.bind, StateT.run, MonadLift.monadLift, liftM, monadLift, StateT.lift, Except.bind,
          pure, StateT.pure, Except.pure] at h
        exact .inl ⟨las, rfl, h.1.symm, h.2.symm⟩
  · simp only [Bool.not_eq_true] at hb
    simp [hb, throw, throwThe, MonadExceptOf.throw, StateT.lift, Except.bind, bind, StateT.bind, StateT.run] at h

/-- What the lowered edge `pe` of `e` is in the final chunk `C`. -/
def EdgeOk (C : List PBlock) (f : Fir.FunId) (e : Cfg.Edge) (pe : PEdge) : Prop :=
  (∃ las, operands f e.args = .ok (some las) ∧ pe = ⟨.blk e.target, las⟩) ∨
  (∃ l, operands f e.args = .ok none ∧ pe = loc l ∧ C[l]? = some { term := .fail .natOverflow, cold := true })

theorem grows_cold {st : St} (hl : Labels st) (t : PTerm) : Grows st (coldSt st t) where
  next := by simp [coldSt]
  fresh := Nat.le_refl _
  done {j b} h := by
    have := hl.done h
    simp only [coldSt, NatMap.get?_insert]
    rw [if_neg (by omega)]
    exact h
  cur ho := .inl ⟨rfl, by
    simp only [Open, coldSt, NatMap.get?_insert]
    rw [if_neg (by have := hl.cur; omega)]
    exact ho, rfl, List.prefix_refl _⟩

theorem labels_cold {st : St} (hl : Labels st) (t : PTerm) : Labels (coldSt st t) where
  cur := by have := hl.cur; simp [coldSt]; omega
  done {j b} h := by
    simp only [coldSt, NatMap.get?_insert] at h
    show j < st.next + 1
    split at h
    · omega
    · have := hl.done h; omega

/-- A lowered edge: the facts later steps need. -/
theorem edge_facts {f : Fir.FunId} {src : Nat} {e : Cfg.Edge} {st st' : St} {pe : PEdge}
    (h : (edge f src e).run st = .ok (pe, st')) (hl : Labels st) :
    e.back = decide (e.target ≤ src) ∧ Grows st st' ∧ Labels st' ∧ st'.cur = st.cur ∧ st'.acc = st.acc ∧
      st'.params = st.params ∧ st'.fresh = st.fresh ∧ (Open st → Open st') ∧
      ∀ {C : List PBlock} {stF : St}, Grows st' stF → Ext C stF → EdgeOk C f e pe := by
  obtain ⟨hb, ⟨las, hop, rfl, rfl⟩ | ⟨hop, rfl, rfl⟩⟩ := edge_run h
  · exact ⟨hb, Grows.refl _, hl, rfl, rfl, rfl, rfl, id, fun _ _ => .inl ⟨las, hop, rfl⟩⟩
  · have hg := grows_cold hl (.fail .natOverflow)
    refine ⟨hb, hg, labels_cold hl _, rfl, rfl, rfl, rfl, fun ho => ?_, fun hg' hC => ?_⟩
    · rcases hg.cur ho with ⟨-, ho', -⟩ | ⟨b, hb', -⟩
      · exact ho'
      · simp only [coldSt, NatMap.get?_insert] at hb'
        rw [if_neg (by have := hl.cur; omega)] at hb'
        rw [ho] at hb'; cases hb'
    · exact .inr ⟨st.next, hop, rfl, hC.done (hg'.done (by simp [coldSt, NatMap.get?_insert]))⟩

/-! ## Closed blocks in the Lir function -/

/-- A block closed with `t` at `st.cur`. -/
theorem closed_block {f : Fir.FunId} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock}
    (hH : Holds f F off starts C) {st : St} {t : PTerm}
    (hC : C[st.cur]? = some { params := st.params, body := st.acc.reverse, term := t }) :
    ∃ lb, F.blocks[off + st.cur]? = some lb ∧ lb.params = st.params ∧ lb.body.size = st.acc.length ∧
      resolveTerm f off starts t = .ok lb.term := by
  obtain ⟨lb, hres, hlb⟩ := hH hC
  obtain ⟨hp, hbody, hterm⟩ := resolveBlock_ok hres
  exact ⟨lb, hlb, hp, by rw [← Array.length_toList, hbody]; simp, hterm⟩

theorem close_ext {st : St} {t : PTerm} {C : List PBlock} {stF : St}
    (hg : Grows (closeSt st t) stF) (hC : Ext C stF) :
    C[st.cur]? = some { params := st.params, body := st.acc.reverse, term := t } :=
  hC.done (hg.done (by simp [closeSt, NatMap.get?_insert]))

/-! ## Reaching an edge -/

/-- Lir reaches, from `s`, a block at or after `low` whose terminator takes
the resolved edge `le` in registers `ρl'`. -/
def ReachesEdge (lp : Lir.Program) (fn : Nat) (F : Lir.Func) (mem : X86.Memory) (ctx : Word)
    (rest : List Lir.Frame) (low : Nat) (s : Lir.State) (le : Lir.Edge) (ρl' : Lir.Env) : Prop :=
  ∃ c L pos, low ≤ L ∧ Sem.Star (Lir.semStep lp) s c (Lir.atState mem ctx fn L pos ρl' rest) ∧
    ∀ vals tb ρt, Lir.evalArgs ρl' le.args = some vals → F.blocks[le.target]? = some tb →
      Lir.bindParams ρl' tb.params vals = some ρt →
      Lir.step lp (Lir.atState mem ctx fn L pos ρl' rest) =
        .next (Lir.atState mem ctx fn le.target 0 ρt rest) (decide (le.target ≤ L))

/-- A `jump` terminator reaches its edge. -/
theorem reachesEdge_jump {lp : Lir.Program} {fn : Nat} {F : Lir.Func} {mem : X86.Memory} {ctx : Word}
    {rest : List Lir.Frame} {L : Nat} {lb : Lir.Block} {le : Lir.Edge} {ρl : Lir.Env}
    (hF : lp.funcs[fn]? = some F) (hlb : F.blocks[L]? = some lb) (ht : lb.term = .jump le) :
    ReachesEdge lp fn F mem ctx rest L (Lir.atState mem ctx fn L lb.body.size ρl rest) le ρl :=
  ⟨0, L, lb.body.size, Nat.le_refl _, .refl _, fun _ _ _ ha htb hp => Lir.jump_at hF hlb rfl ht ha htb hp⟩

/-- A `br` terminator reaches the edge its condition picks. -/
theorem reachesEdge_br {lp : Lir.Program} {fn : Nat} {F : Lir.Func} {mem : X86.Memory} {ctx : Word}
    {rest : List Lir.Frame} {L : Nat} {lb : Lir.Block} {c : Lir.Cond} {w : Lir.Width} {a b : Lir.Arg}
    {t e : Lir.Edge} {ρl : Lir.Env} {va vb : Word} (hF : lp.funcs[fn]? = some F) (hlb : F.blocks[L]? = some lb)
    (ht : lb.term = .br c w a b t e) (hva : a.eval ρl = some va) (hvb : b.eval ρl = some vb) :
    ReachesEdge lp fn F mem ctx rest L (Lir.atState mem ctx fn L lb.body.size ρl rest)
      (if c.holds w va vb then t else e) ρl :=
  ⟨0, L, lb.body.size, Nat.le_refl _, .refl _, fun _ _ _ ha htb hp =>
    Lir.br_at hF hlb rfl ht hva hvb rfl ha htb hp⟩

theorem ReachesEdge.prepend {lp : Lir.Program} {fn : Nat} {F : Lir.Func} {mem : X86.Memory} {ctx : Word}
    {rest : List Lir.Frame} {low low' : Nat} {s s' : Lir.State} {le : Lir.Edge} {ρl : Lir.Env} {c : Nat}
    (h : ReachesEdge lp fn F mem ctx rest low' s' le ρl) (hs : Sem.Star (Lir.semStep lp) s c s')
    (hlow : low ≤ low') : ReachesEdge lp fn F mem ctx rest low s le ρl := by
  obtain ⟨c', L, pos, hL, hst, hstep⟩ := h
  exact ⟨c + c', L, pos, Nat.le_trans hlow hL, hs.trans hst, hstep⟩

/-! ## Completing an edge -/

/-- **A lowered edge enters the target's chunk** with the target block's
parameters bound to related words (charging the clock on a Cfg back edge),
or Lir fails. -/
theorem edge_complete {T : Tables} {P : List Word} {D : Nat → Prop} {sup : Nat} {f : Fir.FunId}
    {lp : Lir.Program} {fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock}
    {mem : X86.Memory} {ctx : Word} {rest : List Lir.Frame} {low : Nat} {s : Lir.State}
    (hF : lp.funcs[fn]? = some F) (hH : Holds f F off starts C) {e : Cfg.Edge} {pe : PEdge} {le : Lir.Edge}
    (hok : EdgeOk C f e pe) (hres : resolveEdge f off starts pe = .ok le) {ρ : Own.Env} {ρl : Lir.Env}
    (hreach : ReachesEdge lp fn F mem ctx rest low s le ρl) (hρ : EnvRel T P D sup ρ ρl)
    (hlive : ∀ a ∈ e.args, LiveArg D a) {vs : List Own.RVal} (hvs : Own.evalArgs ρ e.args = some vs)
    {ps : List Nat} (hlen : ps.length = vs.length) (hps : ∀ y ∈ ps, y < sup) {ot : Nat} {tb : Lir.Block}
    (ht : starts.get? e.target = some ot) (htb : F.blocks[ot]? = some tb) (htp : tb.params = ps)
    (hback : e.back = true → ot ≤ low) :
    Sem.Fails (Lir.semStep lp) s ∨
      ∃ c ρt, Sem.Star (Lir.semStep lp) s c (Lir.atState mem ctx fn ot 0 ρt rest) ∧ e.back.toNat ≤ c ∧
        EnvRel T P D sup (Own.bindAll ρ ps vs) ρt := by
  obtain ⟨c, L, pos, hL, hst, hstep⟩ := hreach
  rcases hok with ⟨las, hop, rfl⟩ | ⟨l, hop, rfl, hcold⟩
  · simp only [resolveEdge, resolveTgt, ht, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hres
    subst hres
    obtain ⟨ws, hws, hrel, -⟩ := operands_rel hρ hop hlive hvs
    obtain ⟨ρt, hbind, hρt⟩ := bind_rel hρ hrel hlen hps
    have h1 := hstep ws tb ρt hws htb (htp ▸ hbind)
    refine .inr ⟨c + (decide (ot ≤ L)).toNat, ρt, hst.trans (Lir.star_of_step h1), ?_, hρt⟩
    cases hb : e.back
    · simp
    · have := hback hb
      simp only [Bool.toNat_true]
      rw [decide_eq_true (by omega)]
      simp
  · simp only [resolveEdge, resolveTgt, loc, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hres
    subst hres
    obtain ⟨lb, hres', hlb⟩ := hH hcold
    obtain ⟨hp, hbody, hterm⟩ := resolveBlock_ok hres'
    simp only [resolveTerm, pure, Except.pure, Except.ok.injEq] at hterm
    have h1 := hstep [] lb ρl rfl hlb (by simp [hp, Lir.bindParams])
    refine .inl ⟨c + (decide (off + l ≤ L)).toNat, _, .natOverflow, hst.trans (Lir.star_of_step h1), ?_⟩
    exact Lir.semStep_fail.2 (Lir.fail_at hF hlb (by rw [← Array.length_toList, hbody]; rfl) hterm.symm)

end Compilatrix.Rt.Proof
