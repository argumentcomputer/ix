import Compilatrix.Rt.Proof.StepEdge

/-!
# Terminator steps

`step_term`: Cfg's step at the end of a block (a jump, a switch, a fused
switch on a comparison, a return, a tail call) is matched by Lir from the
terminator's code, or Lir fails. `final_trap`: a `trap` is Lir's trap.
-/

set_option autoImplicit false

namespace Compilatrix.Rt.Proof

open Compilatrix.Lir (Word)
open Compilatrix.Rt.Lower
open Compilatrix.Src (NatMap)

/-- The lowering at the end of a block's body: its terminator, or a fused
block's branch. -/
theorem rest_nil {f : Fir.FunId} {T : Tables} {uses : NatMap Nat} {src : Nat} {b : Cfg.Block} {st stF : St}
    (h : (restAct f T uses src b []).run st = .ok ((), stF)) :
    (match fusable T uses b with
      | some (_, c, a, a') => (fusedEnd f T src b c a a').run st
      | none => (term f T src b.term).run st) = .ok ((), stF) := by
  unfold restAct at h
  split at h <;> rename_i hf <;> simp only [hf] <;>
  · obtain ⟨bb, s, h₁, h₂⟩ := run_bind h
    simp only [List.dropLast_nil, instrs, StateT.run, pure, StateT.pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at h₁
    obtain ⟨rfl, rfl⟩ := h₁
    simpa using h₂

theorem takeEdge_charge {fd : Cfg.Fun} {fr : Cfg.Frame} {stk : List (Cfg.Frame × Nat)} {H : Own.Heap}
    {e : Cfg.Edge} {s : Cfg.State} {b : Bool} (h : Cfg.takeEdge fd fr stk H e = .next s b) : b = e.back := by
  simp only [Cfg.takeEdge] at h
  split at h
  · split at h
    · simp only [Sem.Step.next.injEq] at h
      exact h.2.symm
    · cases h
  · cases h

/-- Live operands of a block's terminator. -/
theorem term_live {T : Tables} {fd : Cfg.Fun} {i : Nat} {b : Cfg.Block} (hb : fd.blocks[i]? = some b)
    {as : List Fir.Arg} (has : ∀ y, Fir.Arg.var y ∈ as → y ∈ otherUses b) : ∀ a ∈ as, LiveArg (Fused T fd) a := by
  intro a ha y hy hD
  subst hy
  exact (fused_once hD hb).1 (has y ha)

theorem argVars_of_mem {as : List Fir.Arg} {y : Nat} (h : Fir.Arg.var y ∈ as) : y ∈ Cfg.Check.argVars as :=
  edge_live.argVars_mem h

theorem lir_evalArgs_two {ρ : Lir.Env} {a b : Lir.Arg} {wa wb : Word} (h : Lir.evalArgs ρ [a, b] = some [wa, wb]) :
    a.eval ρ = some wa ∧ b.eval ρ = some wb := by
  cases ha : a.eval ρ <;> cases hb : b.eval ρ <;>
    simp [Lir.evalArgs_cons, Lir.evalArgs_nil, ha, hb, Option.bind_eq_bind] at h ⊢ <;> exact h

/-- The key of a comparison's `Bool`. -/
theorem key_of_bool {T : Tables} {H : Own.Heap} {ko : Option Key.CtorKey} {v : Own.RVal}
    (h : (match ko with
      | some c => Sem.Result.ofOption (Own.ctor0Of (ownTables T) c)
      | none => .stuck) = .ok v)
    {key : Key.CtorKey} {fs : List Own.RVal} (hac : v.asCtor T.known H = some (key, fs)) : ko = some key := by
  cases ko with
  | none => cases h
  | some c =>
    simp only [Own.ctor0Of, ownTables] at h
    cases hk : Fir.CtorInfo.ofKey T.ctors c with
    | none => simp [hk, Sem.Result.ofOption] at h
    | some info =>
      simp only [hk] at h
      split at h
      · simp only [Sem.Result.ofOption, Sem.Result.ok.injEq] at h
        subst h
        simp only [Own.RVal.asCtor, Option.some.injEq, Prod.mk.injEq] at hac
        rw [← hac.1, ofKey_key hk]
      · simp [Sem.Result.ofOption] at h

theorem selectEdge_mem {key : Key.CtorKey} : ∀ {alts : List (Key.CtorKey × Cfg.Edge)} {e : Cfg.Edge},
    Cfg.selectEdge key alts none = some e → ∃ p ∈ alts, p.2 = e
  | [], e, h => by simp [Cfg.selectEdge] at h
  | (k, e') :: rest, e, h => by
    simp only [Cfg.selectEdge] at h
    split at h
    · cases h; exact ⟨(k, e'), by simp, rfl⟩
    · obtain ⟨p, hp, rfl⟩ := selectEdge_mem h
      exact ⟨p, by simp [hp], rfl⟩

/-- **A terminator simulates Cfg's step**, given `Dispatches` at a switch
Cfg steps on: a scrutinee related to a word under the heap invariant, whose
key selects an edge. -/
theorem step_term_sel {P : Cfg.Program} {lp : Lir.Program} {ctx : Word} (ht : Target P lp) {fr : Cfg.Frame}
    {stk : List (Cfg.Frame × Nat)} {H : Own.Heap} {s₂ : Lir.State} (hrel : Rel P lp ctx (.run fr stk H) s₂)
    (hfr : fr.rest = [])
    (hdisp : ∀ fd b x alts d v key fs e Pw w ctx' m, P.fun? fr.fn = some fd → fd.blocks[fr.blk]? = some b →
      fusable (tables P) (useCounts fd) b = none → b.term = .switch x alts d → fr.env.get? x = some v →
      ValRel (tables P) Pw v w → HeapInv (tables P) Pw H ctx' m → v.asCtor P.known H = some (key, fs) →
      Cfg.selectEdge key alts d = some e → Dispatches (tables P) H v alts)
    {s₁' : Cfg.State} {bb : Bool} (hs : Cfg.step .immortal P (.run fr stk H) = .next s₁' bb) :
    (∃ c s₂', Sem.Star (Lir.semStep lp) s₂ c s₂' ∧ bb.toNat ≤ c ∧ Rel P lp ctx s₁' s₂') ∨
      Sem.Fails (Lir.semStep lp) s₂ := by
  obtain ⟨hctx, Pw, hheap, lfr, lrest, hst, ⟨hd, fd, b, hpos, hρ, hfz⟩, hstk⟩ := hrel
  obtain ⟨F, starts, off, C, st, stF, hfd, hb, hF, hL, hoff, hH, hrun, hC, hl, ho, hsup, -, hfn, hlab,
    hposn⟩ := hpos
  rw [hfr] at hrun
  have hs₂ := state_eq hst hd
  rw [hfn, hlab, hposn] at hs₂
  have hcode := rest_nil hrun
  have hheap' : HeapInv (tables P) Pw H s₂.ctx s₂.mem := hctx ▸ hheap
  simp only [Cfg.step, hfr, hfd, Cfg.Fun.block?, hb] at hs
  cases hfus : fusable (tables P) (useCounts fd) b with
  | some p =>
    -- a fused switch: the comparison decides the branch
    obtain ⟨init, c, a, a'⟩ := p
    simp only [hfus] at hcode
    obtain ⟨x, op, alts, d, hbody, hcmp, hterm, -, -⟩ := fusable_some hfus
    rw [hterm] at hs
    simp only at hs
    obtain ⟨x', op', va, vb, v, hbody', hvs, hres, hxv⟩ := hfz init c a a' hfus hfr
    rw [hbody] at hbody'
    simp only [List.append_cancel_left_eq, List.cons.injEq, Cfg.Instr.bind.injEq, Own.Rhs.fir.injEq,
      Fir.Rhs.prim.injEq, and_true] at hbody'
    obtain ⟨rfl, rfl⟩ := hbody'
    rw [hxv] at hs
    simp only at hs
    cases hac : v.asCtor P.known H with
    | none => simp [hac] at hs
    | some kf =>
      obtain ⟨key, fs⟩ := kf
      simp only [hac] at hs
      cases hsel : Cfg.selectEdge key alts d with
      | none => simp [hsel] at hs
      | some e =>
        simp only [hsel] at hs
        have hbe := takeEdge_charge hs
        subst hbe
        have he : e ∈ b.term.edges := by
          rw [hterm]
          simp only [Cfg.Term.edges, List.mem_append, List.mem_map, Option.mem_toList]
          rw [selectEdge_dflt] at hsel
          cases hs0 : Cfg.selectEdge key alts none with
          | some e' =>
            rw [hs0] at hsel
            cases hsel
            exact .inl (selectEdge_mem hs0)
          | none => rw [hs0] at hsel; exact .inr hsel
        -- the operands' words
        have hlive : ∀ a₀ ∈ [a, a'], LiveArg (Fused (tables P) fd) a₀ :=
          term_live hb fun y hy => by
            simp only [otherUses, List.mem_append, List.mem_flatMap]
            exact .inl ⟨.bind x (.fir (.prim op [a, a'])), by rw [hbody]; simp,
              by simpa [instrUses, Cfg.Check.rhsVars] using argVars_of_mem hy⟩
        -- the fused branch's code
        unfold fusedEnd at hcode
        obtain ⟨o, st₁, h₁, h₂⟩ := run_bind hcode
        have hst₁ : st₁ = st ∧ operands fr.fn [a, a'] = .ok o := by
          simp only [StateT.run, MonadLift.monadLift, liftM, monadLift, StateT.lift, bind, Except.bind] at h₁
          split at h₁
          · cases h₁
          · rename_i o' ho'
            simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h₁
            obtain ⟨rfl, rfl⟩ := h₁
            exact ⟨rfl, ho'⟩
        obtain ⟨rfl, hops⟩ := hst₁
        split at h₂
        · rename_i la lb
          rw [hterm] at h₂
          simp only at h₂
          obtain ⟨ws, hws, hrelw, -⟩ := operands_rel hρ hops hlive hvs
          obtain ⟨wa, wb, rfl, hva, hvb⟩ : ∃ wa wb, ws = [wa, wb] ∧ ValRel (tables P) Pw va wa ∧
              ValRel (tables P) Pw vb wb := by
            rcases hrelw with _ | ⟨hva, hrelw'⟩
            rcases hrelw' with _ | ⟨hvb, hnil⟩
            cases hnil
            exact ⟨_, _, rfl, hva, hvb⟩
          obtain ⟨hwa, hwb⟩ := lir_evalArgs_two hws
          -- Cfg's comparison: `Nat` literals, and the key of its `Bool`
          have hkey : (if c.holds .w64 wa wb then (tables P).known.boolTrue else (tables P).known.boolFalse) =
              some key := by
            simp only [Own.primResult] at hres
            cases hn : Own.natArgs [va, vb] with
            | none => simp [hn] at hres
            | some ns =>
              obtain ⟨p, q, rfl, rfl, rfl⟩ := natArgs_two hn
              simp only [hn] at hres
              rw [cmp_sem hcmp hva hvb] at hres
              simp only at hres
              exact key_of_bool hres hac
          obtain ⟨pe, le, hok, -, hres', hreach⟩ := fused_sim (mem := s₂.mem) (ctx := s₂.ctx) (rest := lrest) hF hH
            h₂ hl ho (Grows.refl _) hC hwa hwb hkey hsel
          rw [← hs₂] at hreach
          exact take_edge hfd hb hF hL hoff hH (Nat.le_add_right _ _) hρ hheap hctx hstk he hok hres' hreach hs
        · -- an operand without a word: `fail natOverflow`
          rw [close_run] at h₂
          simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at h₂
          exact .inr (hs₂ ▸ fails_closed hF (closedAt_of hH (by rw [← h₂]; exact Grows.refl (closeSt _ _)) hC rfl) s₂.mem s₂.ctx lfr.env lrest)
  | none =>
    simp only [hfus] at hcode
    cases hterm : b.term with
    | jump e =>
      rw [hterm] at hs hcode
      have hbe := takeEdge_charge hs
      subst hbe
      obtain ⟨pe, st₁, h₁, rfl, -, hc₁, ha₁⟩ := term_jump hcode hl ho
      obtain ⟨-, -, -, -, -, -, -, ho₁, hok⟩ := edge_facts h₁ hl
      have hok' := hok (grows_close (ho₁ ho) _) hC
      obtain ⟨le, hle, hreach⟩ := closed_jump (mem := s₂.mem) (ctx := s₂.ctx) (rest := lrest) hF hH (Grows.refl _) hC
        lfr.env
      rw [hc₁, ha₁, ← hs₂] at hreach
      exact take_edge hfd hb hF hL hoff hH (Nat.le_add_right _ _) hρ hheap hctx hstk
        (by rw [hterm]; simp [Cfg.Term.edges]) hok' hle hreach hs
    | switch x alts d =>
      rw [hterm] at hs hcode
      simp only [term] at hcode
      simp only at hs
      cases hxv : fr.env.get? x with
      | none => simp [hxv] at hs
      | some v =>
        simp only [hxv] at hs
        cases hac : v.asCtor P.known H with
        | none => simp [hac] at hs
        | some kf =>
          obtain ⟨key, fs⟩ := kf
          simp only [hac] at hs
          cases hsel : Cfg.selectEdge key alts d with
          | none => simp [hsel] at hs
          | some e =>
            simp only [hsel] at hs
            have hbe := takeEdge_charge hs
            subst hbe
            have hxD : ¬ Fused (tables P) fd x := by
              intro hD
              have := (fused_once hD hb).2 alts d hterm
              rw [hfus] at this
              cases this
            obtain ⟨wx, -, hvx⟩ := hρ.val hxv hxD
            obtain ⟨pe, le, ρl', hok, -, hres', hreach, hρ'⟩ := switch_sim (mem := s₂.mem) (ctx := s₂.ctx) (rest := lrest)
              hF hH hcode hl ho (Grows.refl _) hC hheap' hρ hsup hxD hxv hac hsel
              (hdisp fd b x alts d v key fs e Pw wx s₂.ctx s₂.mem hfd hb hfus hterm hxv hvx hheap' hac hsel)
            rw [← hs₂] at hreach
            have he : e ∈ b.term.edges := by
              rw [hterm]
              simp only [Cfg.Term.edges, List.mem_append, List.mem_map, Option.mem_toList]
              rw [selectEdge_dflt] at hsel
              cases hs0 : Cfg.selectEdge key alts none with
              | some e' =>
                rw [hs0] at hsel
                cases hsel
                exact .inl (selectEdge_mem hs0)
              | none => rw [hs0] at hsel; exact .inr hsel
            exact take_edge hfd hb hF hL hoff hH (Nat.le_add_right _ _) hρ' hheap hctx hstk he hok hres' hreach hs
    | ret a =>
      rw [hterm] at hs hcode
      simp only at hs
      cases hav : Own.evalArg fr.env a with
      | none => simp [hav] at hs
      | some v =>
        simp only [hav, Sem.Step.next.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        obtain ⟨-, ⟨la, hop, rfl⟩ | rfl⟩ := term_ret hcode ho
        · have hlive : LiveArg (Fused (tables P) fd) a :=
            term_live hb (as := [a]) (fun y hy => by
              simp only [otherUses, hterm, List.mem_append]
              exact .inr (by simpa [Cfg.Check.termVars] using argVars_of_mem hy)) a (by simp)
          obtain ⟨w, hw, hvw, -⟩ := operand_rel hρ hop hlive hav
          obtain ⟨lb, hlb, hsize, hlt⟩ := closedAt_of hH (Grows.refl _) hC (t := .ret la) rfl
          refine .inl ⟨0, s₂, .refl _, Nat.le_refl _, hctx, Pw, hheap, lfr, lrest, w, hst, hvw,
            ⟨hd, F, lb, la, hfn ▸ hF, hlab ▸ hlb, hposn.trans hsize.symm, hlt, hw⟩, hstk⟩
        · exact .inr (hs₂ ▸ fails_closed hF (closedAt_of hH (Grows.refl _) hC rfl) s₂.mem s₂.ctx lfr.env lrest)
    | tcall g as =>
      rw [hterm] at hs hcode
      simp only at hs
      cases hvs : Own.evalArgs fr.env as with
      | none => simp [hvs] at hs
      | some vs =>
        simp only [hvs, Sem.Step.next.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        obtain ⟨-, ⟨las, hops, rfl⟩ | rfl⟩ := term_tcall hcode ho
        · have hlive : ∀ a ∈ as, LiveArg (Fused (tables P) fd) a :=
            term_live hb (fun y hy => by
              simp only [otherUses, hterm, List.mem_append]
              exact .inr (by simpa [Cfg.Check.termVars] using argVars_of_mem hy))
          obtain ⟨ws, hws, hrelw, -⟩ := operands_rel hρ hops hlive hvs
          obtain ⟨lb, hlb, hsize, hlt⟩ := closedAt_of hH (Grows.refl _) hC (t := .tail g las) rfl
          refine .inl ⟨0, s₂, .refl _, Nat.le_refl _, hctx, Pw, hheap, ws, lrest, hrelw, hstk, fun callee hent => ?_⟩
          have := Lir.step_tail (p := lp) (mem := s₂.mem) (ctx := s₂.ctx) (rest := lrest)
            (fr := { fn := fr.fn, label := off + st.cur, pos := st.acc.length, env := lfr.env }) hF hlb
            hsize.symm hlt hws hent
          rw [hs₂]
          exact this
        · exact .inr (hs₂ ▸ fails_closed hF (closedAt_of hH (Grows.refl _) hC rfl) s₂.mem s₂.ctx lfr.env lrest)
    | trap =>
      rw [hterm] at hs
      cases hs

/-- **A terminator simulates Cfg's step**, given `Dispatches` at every
switch the block ends in. -/
theorem step_term {P : Cfg.Program} {lp : Lir.Program} {ctx : Word} (ht : Target P lp) {fr : Cfg.Frame}
    {stk : List (Cfg.Frame × Nat)} {H : Own.Heap} {s₂ : Lir.State} (hrel : Rel P lp ctx (.run fr stk H) s₂)
    (hfr : fr.rest = [])
    (hdisp : ∀ fd b x alts d v, P.fun? fr.fn = some fd → fd.blocks[fr.blk]? = some b →
      fusable (tables P) (useCounts fd) b = none → b.term = .switch x alts d → fr.env.get? x = some v →
      Dispatches (tables P) H v alts)
    {s₁' : Cfg.State} {bb : Bool} (hs : Cfg.step .immortal P (.run fr stk H) = .next s₁' bb) :
    (∃ c s₂', Sem.Star (Lir.semStep lp) s₂ c s₂' ∧ bb.toNat ≤ c ∧ Rel P lp ctx s₁' s₂') ∨
      Sem.Fails (Lir.semStep lp) s₂ :=
  step_term_sel ht hrel hfr
    (fun fd b x alts d v _ _ _ _ _ _ _ h1 h2 h3 h4 h5 _ _ _ _ => hdisp fd b x alts d v h1 h2 h3 h4 h5) hs

theorem takeEdge_ne_trap {fd : Cfg.Fun} {fr : Cfg.Frame} {stk : List (Cfg.Frame × Nat)} {H : Own.Heap}
    {e : Cfg.Edge} : Cfg.takeEdge fd fr stk H e ≠ .trap := by
  simp only [Cfg.takeEdge]
  split
  · split <;> simp
  · simp

/-- **A `trap` is Lir's trap.** -/
theorem final_trap {P : Cfg.Program} {lp : Lir.Program} {ctx : Word} {fr : Cfg.Frame}
    {stk : List (Cfg.Frame × Nat)} {H : Own.Heap} {s₂ : Lir.State} (hrel : Rel P lp ctx (.run fr stk H) s₂)
    (hfr : fr.rest = []) (hs : Cfg.step .immortal P (.run fr stk H) = .trap) : Lir.step lp s₂ = .trap := by
  obtain ⟨hctx, Pw, hheap, lfr, lrest, hst, ⟨hd, fd, b, hpos, hρ, hfz⟩, hstk⟩ := hrel
  obtain ⟨F, starts, off, C, st, stF, hfd, hb, hF, hL, hoff, hH, hrun, hC, hl, ho, hsup, -, hfn, hlab,
    hposn⟩ := hpos
  rw [hfr] at hrun
  have hs₂ := state_eq hst hd
  rw [hfn, hlab, hposn] at hs₂
  have hcode := rest_nil hrun
  simp only [Cfg.step, hfr, hfd, Cfg.Fun.block?, hb] at hs
  have hterm : b.term = .trap := by
    cases ht : b.term with
    | jump e => rw [ht] at hs; exact absurd hs takeEdge_ne_trap
    | switch x alts d =>
      rw [ht] at hs
      simp only at hs
      split at hs
      · split at hs
        · split at hs
          · exact absurd hs takeEdge_ne_trap
          · cases hs
        · cases hs
      · cases hs
    | ret a => rw [ht] at hs; simp only at hs; split at hs <;> cases hs
    | tcall g as => rw [ht] at hs; simp only at hs; split at hs <;> cases hs
    | trap => rfl
  cases hfus : fusable (tables P) (useCounts fd) b with
  | some p =>
    obtain ⟨init, c, a, a'⟩ := p
    obtain ⟨x, op, alts, d, -, -, hsw, -⟩ := fusable_some hfus
    rw [hterm] at hsw
    cases hsw
  | none =>
    simp only [hfus, hterm] at hcode
    have := term_trap hcode
    subst this
    obtain ⟨lb, hlb, hsize, hlt⟩ := closedAt_of hH (Grows.refl _) hC (t := .trap) rfl
    rw [hs₂]
    exact Lir.trap_at hF hlb hsize.symm hlt

/-- Cfg's immortal instructions neither fail nor trap. -/
theorem evalRhs_ok_or_stuck {T : Own.Tables} {ρ : Own.Env} {H : Own.Heap} (r : Own.Rhs) :
    (∃ p, Own.evalRhs .immortal T ρ H r = .ok p) ∨ Own.evalRhs .immortal T ρ H r = .stuck := by
  cases r with
  | fir e =>
    cases e with
    | arg a => simp only [Own.evalRhs]; split <;> simp
    | prim op as =>
      simp only [Own.evalRhs]
      split
      · simp only [Own.primResult]
        split
        · split
          · simp [Sem.Result.map, Sem.Result.bind]
          · split
            · simp only [Sem.Result.ofOption]; split <;> simp [Sem.Result.map, Sem.Result.bind]
            · simp [Sem.Result.map, Sem.Result.bind]
          · simp [Sem.Result.map, Sem.Result.bind]
        · simp [Sem.Result.map, Sem.Result.bind]
      · simp
    | _ => simp [Own.evalRhs]
  | alloc c as κ =>
    simp only [Own.evalRhs]
    split
    · split
      · split <;> simp
      · simp
    · simp
  | proj y c i =>
    simp only [Own.evalRhs]
    split
    · split
      · split
        · simp only [Sem.Result.ofOption]; split <;> simp [Sem.Result.map, Sem.Result.bind]
        · simp
      · simp
    · simp

end Compilatrix.Rt.Proof
