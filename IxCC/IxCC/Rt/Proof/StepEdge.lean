import IxCC.Rt.Proof.StepInstr

/-!
# Taking an edge

`take_edge`: where a terminator's Lir code reaches the block that takes the
lowered edge of the Cfg edge Cfg takes, Lir enters the target block's chunk
with its parameters bound to related words, charging the clock on a Cfg back
edge (`Lowered.edges`, `Lowered.mono`), or fails.
-/

set_option autoImplicit false

namespace IxCC.Rt.Proof

open IxCC.Lir (Word)
open IxCC.Rt.Lower
open IxCC.Src (NatMap)

/-- An edge's arguments are live. -/
theorem edge_live {T : Tables} {fd : Cfg.Fun} {i : Nat} {b : Cfg.Block} (hb : fd.blocks[i]? = some b)
    {e : Cfg.Edge} (he : e ∈ b.term.edges) : ∀ a ∈ e.args, LiveArg (Fused T fd) a := by
  intro a ha y hy hD
  subst hy
  apply (fused_once hD hb).1
  simp only [otherUses, List.mem_append]
  right
  cases ht : b.term with
  | jump e' =>
    rw [ht] at he
    simp only [Cfg.Term.edges, List.mem_singleton] at he
    subst he
    simp only [Cfg.Check.termVars]
    exact argVars_mem ha
  | switch z alts d =>
    rw [ht] at he
    simp only [Cfg.Term.edges] at he
    exact List.mem_flatMap.2 ⟨e, he, argVars_mem ha⟩
  | ret _ => rw [ht] at he; simp [Cfg.Term.edges] at he
  | tcall _ _ => rw [ht] at he; simp [Cfg.Term.edges] at he
  | trap => rw [ht] at he; simp [Cfg.Term.edges] at he
where
  argVars_mem {as : List Fir.Arg} {y : Nat} (h : Fir.Arg.var y ∈ as) : y ∈ Cfg.Check.argVars as := by
    induction as with
    | nil => cases h
    | cons a as ih =>
      rcases List.mem_cons.1 h with rfl | h'
      · simp [Cfg.Check.argVars]
      · cases a <;> simp [Cfg.Check.argVars, ih h']

/-- With block 0 the entry, no edge targets it. -/
theorem merged_target {fd : Cfg.Fun} (hm : mergedOf fd = true) {i : Nat} {b : Cfg.Block}
    (hb : fd.blocks[i]? = some b) {e : Cfg.Edge} (he : e ∈ b.term.edges) : e.target ≠ 0 := by
  unfold mergedOf at hm
  simp only [Bool.not_eq_true', List.any_eq_false, Bool.not_eq_true, List.any_eq_true, beq_iff_eq,
    not_exists, not_and] at hm
  intro h0
  exact hm b (List.mem_of_getElem? hb) e he h0

/-- **Taking a Cfg edge.** -/
theorem take_edge {P : Cfg.Program} {lp : Lir.Program} {ctx : Word} {fr : Cfg.Frame}
    {stk : List (Cfg.Frame × Nat)} {H : Own.Heap} {fd : Cfg.Fun} {b : Cfg.Block} {F : Lir.Func}
    {starts : NatMap Nat} {off : Nat} {C : List PBlock} {low : Nat} {Pw : List Word} {s₂ : Lir.State}
    {ρl : Lir.Env} {lrest : List Lir.Frame}
    (hfd : P.fun? fr.fn = some fd) (hb : fd.blocks[fr.blk]? = some b) (hF : lp.funcs[fr.fn]? = some F)
    (hL : Lowered (tables P) fr.fn fd F starts) (hoff : starts.get? fr.blk = some off)
    (hH : Holds fr.fn F off starts C) (hlow : off ≤ low)
    (hρ : EnvRel (tables P) Pw (Fused (tables P) fd) (supOf fd) fr.env ρl)
    (hheap : HeapInv (tables P) Pw H ctx s₂.mem) (hctx : s₂.ctx = ctx)
    (hstk : ListRel (SuspAt P lp Pw) stk lrest)
    {e : Cfg.Edge} (he : e ∈ b.term.edges) {pe : PEdge} {le : Lir.Edge} (hok : EdgeOk C fr.fn e pe)
    (hres : resolveEdge fr.fn off starts pe = .ok le)
    (hreach : ReachesEdge lp fr.fn F s₂.mem s₂.ctx lrest low s₂ le ρl)
    {s₁' : Cfg.State} (hs : Cfg.takeEdge fd fr stk H e = .next s₁' e.back) :
    (∃ c s₂', Sem.Star (Lir.semStep lp) s₂ c s₂' ∧ e.back.toNat ≤ c ∧ Rel P lp ctx s₁' s₂') ∨
      Sem.Fails (Lir.semStep lp) s₂ := by
  simp only [Cfg.takeEdge, Cfg.Fun.block?] at hs
  cases hbt : fd.blocks[e.target]? with
  | none => simp [hbt] at hs
  | some bt =>
    cases hvs : Own.evalArgs fr.env e.args with
    | none => simp [hbt, hvs] at hs
    | some vs =>
      simp only [hbt, hvs] at hs
      split at hs
      · rename_i hlen
        simp only [Sem.Step.next.injEq, and_true] at hs
        subst hs
        obtain ⟨ot, C', fr', stF', hot, -, -, -, -, -⟩ := hL.chunk hbt
        obtain ⟨tb, htb, htp⟩ := hL.head hbt hot
        have hhead : headParams fd e.target bt = bt.params.map (·.1) := by
          unfold headParams
          cases hm : mergedOf fd
          · simp
          · simp [merged_target hm hb he]
        have hback : e.back = true → ot ≤ low := by
          intro hbk
          rw [hL.edges hb he] at hbk
          have := hL.mono hot hoff (of_decide_eq_true hbk)
          omega
        rcases edge_complete (D := Fused (tables P) fd) (sup := supOf fd) hF hH hok hres hreach hρ
          (edge_live hb he) hvs (by simpa using hlen.symm) (params_lt_sup hbt) hot htb (htp.trans hhead) hback with
          hfail | ⟨c, ρt, hstar, hc, hρt⟩
        · exact .inr hfail
        · refine .inl ⟨c, _, hstar, hc, hctx, Pw, hheap, _, lrest, rfl, ?_, hstk⟩
          exact runAt_head hfd hF hL hbt hot hρt
      · cases hs

end IxCC.Rt.Proof
