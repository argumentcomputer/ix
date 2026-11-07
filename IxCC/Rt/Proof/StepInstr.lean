import IxCC.Rt.Proof.StepFrame

/-!
# Instruction steps

`step_instr`: Cfg's step over an instruction other than a call is Lir's
run over its expansion (`instr_sim`), or Lir fails; a fused block's
comparison is no Lir step at all. `step_call_instr`: Cfg's call
instruction is the Lir state at the call statement, which enters the
callee with the caller suspended after the call.
-/

set_option autoImplicit false

namespace IxCC.Rt.Proof

open IxCC.Lir (Word)
open IxCC.Rt.Lower
open IxCC.Src (NatMap)

/-- A Lir state with a running frame without pending results is an
`atState`. -/
theorem state_eq {s : Lir.State} {lfr : Lir.Frame} {lrest : List Lir.Frame} (hst : s.stack = lfr :: lrest)
    (hd : lfr.dsts = []) : s = Lir.atState s.mem s.ctx lfr.fn lfr.label lfr.pos lfr.env lrest := by
  obtain ⟨mem, ctx, stack⟩ := s
  obtain ⟨fn, label, pos, env, dsts⟩ := lfr
  simp only at hst hd
  subst hst hd
  rfl

/-- A variable an instruction of a block defines is below the supply. -/
theorem instr_def_lt {fd : Cfg.Fun} {i : Nat} {b : Cfg.Block} (hb : fd.blocks[i]? = some b) {pre is : List Cfg.Instr}
    {x : Nat} {r : Own.Rhs} (hpre : pre ++ Cfg.Instr.bind x r :: is = b.body) : x < supOf fd := by
  refine defs_lt_sup hb ?_
  simp only [Cfg.Check.blockDefs, Cfg.Check.instrDefs, List.mem_append, List.mem_map]
  right
  exact ⟨.bind x r, by rw [← hpre]; simp, rfl⟩

/-- An instruction's operands are live. -/
theorem instr_live {T : Tables} {fd : Cfg.Fun} {i : Nat} {b : Cfg.Block} (hb : fd.blocks[i]? = some b)
    {pre is : List Cfg.Instr} {x : Nat} {r : Own.Rhs} (hpre : pre ++ Cfg.Instr.bind x r :: is = b.body) :
    ∀ y ∈ Cfg.Check.rhsVars r, ¬ Fused T fd y := by
  intro y hy hD
  apply (fused_once hD hb).1
  simp only [otherUses, List.mem_append, List.mem_flatMap]
  left
  exact ⟨.bind x r, by rw [← hpre]; simp, hy⟩

/-- The body's last instruction of a fused block is its comparison. -/
theorem fused_last {T : Tables} {uses : NatMap Nat} {b : Cfg.Block} {init : List Cfg.Instr} {c : Lir.Cond}
    {a a' : Fir.Arg} (hf : fusable T uses b = some (init, c, a, a')) {pre : List Cfg.Instr} {i : Cfg.Instr}
    (hpre : pre ++ [i] = b.body) :
    ∃ x op alts d, i = .bind x (.fir (.prim op [a, a'])) ∧ pre = init ∧ compareOf op = some c ∧
      b.term = .switch x alts d := by
  obtain ⟨x, op, alts, d, hbody, hc, ht, -⟩ := fusable_some hf
  rw [hbody] at hpre
  obtain ⟨h1, h2⟩ := List.append_inj' hpre rfl
  simp only [List.cons.injEq, and_true] at h2
  exact ⟨x, op, alts, d, h2, h1, hc, ht⟩

theorem evalArg_insert_irrel {ρ : Own.Env} {x : Nat} {v : Own.RVal} {a : Fir.Arg}
    (h : ∀ y ∈ Cfg.Check.argVars [a], y ≠ x) : Own.evalArg (ρ.insert x v) a = Own.evalArg ρ a := by
  cases a with
  | var y =>
    simp only [Own.evalArg, NatMap.get?_insert]
    rw [if_neg (h y (by simp [Cfg.Check.argVars]))]
  | lit l => rfl
  | erased => rfl

theorem evalArgs_insert_irrel {ρ : Own.Env} {x : Nat} {v : Own.RVal} :
    ∀ {as : List Fir.Arg}, (∀ y ∈ Cfg.Check.argVars as, y ≠ x) →
      Own.evalArgs (ρ.insert x v) as = Own.evalArgs ρ as
  | [], _ => rfl
  | a :: as, h => by
    simp only [Own.evalArgs]
    rw [evalArg_insert_irrel (fun y hy => h y ?_), evalArgs_insert_irrel (fun y hy => h y ?_)]
    · cases a <;> simp_all [Cfg.Check.argVars]
    · cases a <;> simp_all [Cfg.Check.argVars]

theorem evalArgs_two {ρ : Own.Env} {a a' : Fir.Arg} {vs : List Own.RVal} (h : Own.evalArgs ρ [a, a'] = some vs) :
    ∃ va vb, vs = [va, vb] := by
  cases ha : Own.evalArg ρ a <;> cases hb : Own.evalArg ρ a' <;> simp [Own.evalArgs, ha, hb] at h
  exact ⟨_, _, h.symm⟩

/-- **An instruction other than a call simulates Cfg's.** -/
theorem step_instr {P : Cfg.Program} {lp : Lir.Program} {ctx : Word} (ht : Target P lp) {fr : Cfg.Frame}
    {stk : List (Cfg.Frame × Nat)} {H : Own.Heap} {s₂ : Lir.State} (hrel : Rel P lp ctx (.run fr stk H) s₂)
    {x : Nat} {r : Own.Rhs} {is : List Cfg.Instr} (hfr : fr.rest = .bind x r :: is)
    (hnc : ∀ g as, r ≠ .fir (.call g as)) {v : Own.RVal} {H' : Own.Heap}
    (hev : Own.evalRhs .immortal P.tables fr.env H r = .ok (v, H')) :
    (∃ c s₂', Sem.Star (Lir.semStep lp) s₂ c s₂' ∧
      Rel P lp ctx (.run { fr with rest := is, env := fr.env.insert x v } stk H') s₂') ∨
    Sem.Fails (Lir.semStep lp) s₂ := by
  obtain ⟨hctx, Pw, hheap, lfr, lrest, hst, ⟨hd, fd, b, hpos, hρ, hfz⟩, hstk⟩ := hrel
  obtain ⟨F, starts, off, C, st, stF, hfd, hb, hF, hL, hoff, hH, hrun, hC, hl, ho, hsup, ⟨pre, hpre⟩, hfn, hlab,
    hposn⟩ := hpos
  rw [hfr] at hrun hpre
  have hs₂ := state_eq hst hd
  rw [hfn, hlab, hposn] at hs₂
  have hx := instr_def_lt hb hpre
  have hlive := instr_live (T := tables P) hb hpre
  by_cases hcmp : (fusable (tables P) (useCounts fd) b).isSome = true ∧ is = []
  · -- a fused block's comparison: Lir does nothing
    obtain ⟨hfs, rfl⟩ := hcmp
    obtain ⟨⟨init, c, a, a'⟩, hf⟩ := Option.isSome_iff_exists.1 hfs
    obtain ⟨y, op, alts, d, hi, rfl, hc, hterm⟩ := fused_last hf hpre
    simp only [Cfg.Instr.bind.injEq] at hi
    obtain ⟨rfl, rfl⟩ := hi
    have hD : Fused (tables P) fd x := ⟨fr.blk, b, pre, c, a, a', alts, d, hb, hf, hterm⟩
    obtain ⟨rfl, vs, hvs, hres⟩ := evalRhs_prim hev
    obtain ⟨va, vb, rfl⟩ := evalArgs_two hvs
    have hnx : ∀ y ∈ Cfg.Check.argVars [a, a'], y ≠ x := by
      intro y hy e
      subst e
      exact hlive y (by simpa [Cfg.Check.rhsVars] using hy) hD
    refine .inl ⟨0, s₂, .refl _, hctx, Pw, hheap, lfr, lrest, hst, ⟨hd, fd, b, ?_, hρ.insert_dead hx hD, ?_⟩, hstk⟩
    · refine ⟨F, starts, off, C, st, stF, hfd, hb, hF, hL, hoff, hH, ?_, hC, hl, ho, hsup,
        ⟨pre ++ [.bind x (.fir (.prim op [a, a']))], by simpa using hpre⟩, hfn, hlab, hposn⟩
      unfold restAct at hrun ⊢
      simp only [hf] at hrun ⊢
      simpa using hrun
    · intro init' c' a₁ a₁' hf' _
      rw [hf] at hf'
      simp only [Option.some.injEq, Prod.mk.injEq] at hf'
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hf'
      exact ⟨x, op, va, vb, v, hpre.symm, by rw [evalArgs_insert_irrel hnx]; exact hvs, hres,
        by simp [NatMap.get?_insert]⟩
  · -- the instruction's expansion
    have hfused : (fusable (tables P) (useCounts fd) b).isSome = true → is ≠ [] := fun h e => hcmp ⟨h, e⟩
    obtain ⟨b₁, st₁, h₁, ⟨rfl, hrest⟩ | ⟨rfl, rfl⟩⟩ := rest_cons hrun hfused
    · obtain ⟨hg₁, hl₁, ho₁⟩ := instr_mono h₁ hl ho
      have hC₁ : Ext C st₁ := (rest_grows hrest hl₁ ho₁).ext hC
      have hsim := instr_sim (tables_boolsOk P) hF hH ht.pow ht.gcd hnc h₁ hC₁ hl ho hsup hx hlive
        (ctx := s₂.ctx) (D := Fused (tables P) fd)
      rcases hsim Pw H fr.env lfr.env s₂.mem lrest v H' (hctx ▸ hheap) hρ hev with
        ⟨c, ρl', mem', Pw', hstar, hheap', hPw, hρ'⟩ | hfail
      · refine .inl ⟨c, Lir.atState mem' s₂.ctx fr.fn (off + st₁.cur) st₁.acc.length ρl' lrest, hs₂ ▸ hstar, hctx,
          Pw', hctx ▸ hheap', { fn := fr.fn, label := off + st₁.cur, pos := st₁.acc.length, env := ρl' }, lrest, rfl,
          ⟨rfl, fd, b, ⟨F, starts, off, C, st₁, stF, hfd, hb, hF, hL, hoff, hH, hrest, hC, hl₁, ho₁,
            Nat.le_trans hsup hg₁.fresh, ⟨pre ++ [.bind x r], by simpa using hpre⟩, rfl, rfl, rfl⟩, hρ', ?_⟩,
          stack_mono hPw hstk⟩
        intro init c a a' hf hr
        exact absurd hr (hfused (by simp [hf]))
      · exact .inr (hs₂ ▸ hfail)
    · exact .inr (hs₂ ▸ instr_fails hF hH h₁ hC ho s₂.mem lfr.env lrest)


/-- **Cfg's call instruction is Lir's call statement**, which enters the
callee with the caller suspended after it. -/
theorem step_call_instr {P : Cfg.Program} {lp : Lir.Program} {ctx : Word} {fr : Cfg.Frame}
    {stk : List (Cfg.Frame × Nat)} {H : Own.Heap} {s₂ : Lir.State} (hrel : Rel P lp ctx (.run fr stk H) s₂)
    {x g : Nat} {as : List Fir.Arg} {is : List Cfg.Instr} (hfr : fr.rest = .bind x (.fir (.call g as)) :: is)
    {vs : List Own.RVal} (hvs : Own.evalArgs fr.env as = some vs) :
    Rel P lp ctx (.call g vs (({ fr with rest := is }, x) :: stk) H) s₂ ∨ Sem.Fails (Lir.semStep lp) s₂ := by
  obtain ⟨hctx, Pw, hheap, lfr, lrest, hst, ⟨hd, fd, b, hpos, hρ, hfz⟩, hstk⟩ := hrel
  obtain ⟨F, starts, off, C, st, stF, hfd, hb, hF, hL, hoff, hH, hrun, hC, hl, ho, hsup, ⟨pre, hpre⟩, hfn, hlab,
    hposn⟩ := hpos
  rw [hfr] at hrun hpre
  have hs₂ := state_eq hst hd
  rw [hfn, hlab, hposn] at hs₂
  have hx := instr_def_lt hb hpre
  have hlive := instr_live (T := tables P) hb hpre
  have hfused : (fusable (tables P) (useCounts fd) b).isSome = true → is ≠ [] := by
    intro hfs e
    subst e
    obtain ⟨⟨init, c, a, a'⟩, hf⟩ := Option.isSome_iff_exists.1 hfs
    obtain ⟨y, op, -, -, hi, -⟩ := fused_last hf hpre
    simp only [Cfg.Instr.bind.injEq] at hi
    cases hi.2
  obtain ⟨b₁, st₁, h₁, ⟨rfl, hrest⟩ | ⟨rfl, rfl⟩⟩ := rest_cons hrun hfused
  · obtain ⟨hg₁, hl₁, ho₁⟩ := instr_mono h₁ hl ho
    have hC₁ : Ext C st₁ := (rest_grows hrest hl₁ ho₁).ext hC
    rcases withOperands_run h₁ with ⟨las, hops, -, hk⟩ | ⟨-, hb₁, -⟩
    · rw [emit_run] at hk
      simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hk
      subst hk
      obtain ⟨ws, hws, hrel, -⟩ := operands_rel hρ hops
        (liveArgs_of (fun y hy => hlive y (by simpa [Cfg.Check.rhsVars] using hy))) hvs
      obtain ⟨lb, post, hlb, -, hbody⟩ := holds_open hH [Lir.Stmt.call [x] g las] st.fresh hC₁ ho
      have hposb : st.acc.length < lb.body.size := by
        rw [← Array.length_toList, hbody]; simp
      have hcall : lb.body[st.acc.length] = .call [x] g las := by
        rw [← Array.getElem_toList (h := hposb)]
        simp only [hbody]
        rw [List.getElem_append_left (by simp), List.getElem_append_right (by simp)]
        simp
      refine .inl ⟨hctx, Pw, hheap, ws, { lfr with pos := lfr.pos + 1, dsts := [x] } :: lrest, hrel,
        .cons ⟨rfl, fd, b, ?_, hρ, hx, ?_⟩ hstk, fun callee he => ?_⟩
      · exact ⟨F, starts, off, C, { st with acc := Lir.Stmt.call [x] g las :: st.acc }, stF, hfd, hb, hF, hL, hoff,
          hH, hrest, hC, hl₁, ho₁, hsup, ⟨pre ++ [.bind x (.fir (.call g as))], by simpa using hpre⟩, hfn, hlab,
          by simp [hposn]⟩
      · cases hfs : (fusable (tables P) (useCounts fd) b).isSome
        · exact .inl (by simpa using hfs)
        · exact .inr (hfused hfs)
      · have := Lir.step_call (p := lp) (mem := s₂.mem) (ctx := s₂.ctx) (rest := lrest)
          (fr := { fn := fr.fn, label := off + st.cur, pos := st.acc.length, env := lfr.env }) hF hlb hposb hcall hws he
        rw [hs₂]
        simp only [Lir.atState] at this ⊢
        rw [this]
        obtain ⟨fn, label, pos, env, dsts⟩ := lfr
        simp only at hfn hlab hposn hd
        subst hfn hlab hposn hd
        rfl
    · cases hb₁
  · exact .inr (hs₂ ▸ instr_fails hF hH h₁ hC ho s₂.mem lfr.env lrest)

end IxCC.Rt.Proof
