import Compilatrix.Rt.Proof.Rel

/-!
# Entering and leaving functions

`step_enter`: Cfg's charged entry of a function is Lir's charged call (or
tail call) step, then (when block 0 has predecessors) the entry block's
jump to block 0's chunk, with the arguments bound to related words.
`step_return`: Cfg's return to a caller is Lir's `ret` to the suspended
frame, binding the call's variable. `final_return`: the last return is
Lir's.
-/

set_option autoImplicit false

namespace Compilatrix.Rt.Proof

open Compilatrix.Lir (Word)
open Compilatrix.Rt.Lower
open Compilatrix.Src (NatMap)

/-! ## Binding parameters -/

theorem bindParams_some : ∀ (ρ : Lir.Env) {ps : List Nat} {ws : List Word}, ps.length = ws.length →
    ∃ ρ', Lir.bindParams ρ ps ws = some ρ'
  | ρ, [], [], _ => ⟨ρ, rfl⟩
  | ρ, p :: ps, w :: ws, h => bindParams_some (ρ.insert p w) (by simpa using h)
  | _, [], _ :: _, h => by simp at h
  | _, _ :: _, [], h => by simp at h

theorem bindParams_get_not_mem : ∀ {ρ ρ' : Lir.Env} {ps : List Nat} {ws : List Word} {y : Nat},
    y ∉ ps → Lir.bindParams ρ ps ws = some ρ' → ρ'[y]? = ρ[y]?
  | ρ, ρ', [], [], y, _, h => by simp [Lir.bindParams] at h; subst h; rfl
  | ρ, ρ', p :: ps, w :: ws, y, hy, h => by
    simp only [Lir.bindParams] at h
    rw [bindParams_get_not_mem (fun h' => hy (by simp [h'])) h]
    exact Lir.env_insert_ne _ _ (fun e => hy (by simp [e]))
  | _, _, [], _ :: _, _, _, h => by simp [Lir.bindParams] at h
  | _, _, _ :: _, [], _, _, h => by simp [Lir.bindParams] at h

/-- Distinct parameters read back the words bound to them. -/
theorem evalArgs_bindParams : ∀ {ρ ρ' : Lir.Env} {ps : List Nat} {ws : List Word}, ps.Nodup →
    Lir.bindParams ρ ps ws = some ρ' → Lir.evalArgs ρ' (ps.map .v) = some ws
  | ρ, ρ', [], [], _, h => by simp [Lir.bindParams] at h; rfl
  | ρ, ρ', p :: ps, w :: ws, hnd, h => by
    simp only [Lir.bindParams] at h
    have hnd' := List.nodup_cons.1 hnd
    have ih := evalArgs_bindParams hnd'.2 h
    have hp : ρ'[p]? = some w := by
      rw [bindParams_get_not_mem hnd'.1 h]
      exact Lir.env_insert_self _ _ _
    simp only [List.map_cons, Lir.evalArgs_cons, Lir.Arg.eval_v, hp, ih, Option.bind_eq_bind, Option.bind_some]
    rfl
  | _, _, [], _ :: _, _, h => by simp [Lir.bindParams] at h
  | _, _, _ :: _, [], _, h => by simp [Lir.bindParams] at h

/-- Any Lir registers relate to Cfg's empty environment. -/
theorem envRel_leaf (T : Tables) (P : List Word) (D : Nat → Prop) (sup : Nat) (ρl : Lir.Env) :
    EnvRel T P D sup .leaf ρl where
  dom h := by simp [NatMap.get?] at h
  val h := by simp [NatMap.get?] at h

/-- Block parameters are below the supply. -/
theorem params_lt_sup {fd : Cfg.Fun} {i : Nat} {b : Cfg.Block} (hb : fd.blocks[i]? = some b) :
    ∀ y ∈ b.params.map (·.1), y < supOf fd :=
  fun y hy => defs_lt_sup hb (by simp only [Cfg.Check.blockDefs]; exact List.mem_append_left _ hy)

/-- A fused block's body is not empty. -/
theorem fusable_body_ne {T : Tables} {uses : NatMap Nat} {b : Cfg.Block} {init : List Cfg.Instr} {c : Lir.Cond}
    {a a' : Fir.Arg} (h : fusable T uses b = some (init, c, a, a')) : b.body ≠ [] := by
  obtain ⟨x, op, -, -, hbody, -⟩ := fusable_some h
  rw [hbody]
  simp

/-- A frame at the start of block `i`'s code. -/
theorem runAt_head {P : Cfg.Program} {lp : Lir.Program} {Pw : List Word} {f : Nat} {fd : Cfg.Fun}
    {F : Lir.Func} {starts : NatMap Nat} (hfd : P.fun? f = some fd) (hF : lp.funcs[f]? = some F)
    (hL : Lowered (tables P) f fd F starts) {i : Nat} {b : Cfg.Block} (hb : fd.blocks[i]? = some b)
    {o : Nat} (ho : starts.get? i = some o) {env : Own.Env} {ρl : Lir.Env}
    (hρ : EnvRel (tables P) Pw (Fused (tables P) fd) (supOf fd) env ρl) :
    RunAt P lp Pw { fn := f, blk := i, rest := b.body, env } { fn := f, label := o, pos := 0, env := ρl } := by
  obtain ⟨off, C, fr, stF, hoff, hH, hsup, hrun, hC, -⟩ := hL.chunk hb
  rw [ho] at hoff
  cases hoff
  refine ⟨rfl, fd, b, ⟨F, starts, o, C, openSt fr (headParams fd i b), stF, hfd, hb, hF, hL, ho, hH, ?_, hC,
    labels_openSt _ _, open_openSt _ _, hsup, ⟨[], rfl⟩, rfl, by simp [openSt], by simp [openSt]⟩, hρ, ?_⟩
  · rw [restAct_body]; exact hrun
  · intro init c a a' hf hr
    exact absurd hr (fusable_body_ne hf)

/-! ## Entry -/

/-- **Cfg's entry of a function is Lir's.** -/
theorem step_enter {P : Cfg.Program} {lp : Lir.Program} {ctx : Word} (ht : Target P lp) {g : Nat}
    {vs : List Own.RVal} {stk : List (Cfg.Frame × Nat)} {H : Own.Heap} {s₂ : Lir.State}
    (hrel : Rel P lp ctx (.call g vs stk H) s₂) {s₁' : Cfg.State}
    (hs : Cfg.step .immortal P (.call g vs stk H) = .next s₁' true) :
    ∃ c s₂', Sem.Star (Lir.semStep lp) s₂ c s₂' ∧ 1 ≤ c ∧ Rel P lp ctx s₁' s₂' := by
  obtain ⟨hctx, Pw, hheap, ws, lrest, hws, hstk, hstep⟩ := hrel
  simp only [Cfg.step] at hs
  cases hfd : P.fun? g with
  | none => simp [hfd] at hs
  | some fd =>
    simp only [hfd, Cfg.Fun.block?] at hs
    cases hb0 : fd.blocks[0]? with
    | none => simp [hb0] at hs
    | some b0 =>
      simp only [hb0] at hs
      split at hs
      · rename_i hlen
        simp only [Sem.Step.next.injEq, and_true] at hs
        subst hs
        obtain ⟨F, starts, hF, hL⟩ := ht.fn hfd
        obtain ⟨o0, ho0, hentry⟩ := hL.entry hb0
        have hwlen : ws.length = b0.params.length := hws.length_eq.symm.trans hlen
        have hρ0 : EnvRel (tables P) Pw (Fused (tables P) fd) (supOf fd) .leaf {} :=
          envRel_leaf _ _ _ _ _
        rcases hentry with ⟨hm, rfl, hps⟩ | ⟨hm, hF0, hpos, hnd, hge, hplen⟩
        · -- block 0 is the entry: its parameters are the function's
          obtain ⟨ρ0, hbind⟩ := bindParams_some {} (ps := F.params) (ws := ws) (by rw [hps]; simpa using hwlen.symm)
          have henter : Lir.enter lp g ws = some { fn := g, label := 0, pos := 0, env := ρ0 } := by
            simp [Lir.enter, hF, hbind]
          have h1 := hstep _ henter
          obtain ⟨ρ0', hb', hρ⟩ := bind_rel hρ0 hws (by simp [hlen]) (params_lt_sup hb0)
          rw [hps] at hbind
          rw [hbind] at hb'
          cases hb'
          refine ⟨1, _, Lir.star_of_step h1, Nat.le_refl _, hctx, Pw, hheap, _, lrest, rfl, ?_, hstk⟩
          have := runAt_head (Pw := Pw) hfd hF hL hb0 ho0 hρ
          simpa [headParams, hm] using this
        · -- the entry block jumps to block 0's chunk
          obtain ⟨ρ0, hbind⟩ := bindParams_some {} (ps := F.params) (ws := ws) (by rw [hplen, hwlen])
          have henter : Lir.enter lp g ws = some { fn := g, label := 0, pos := 0, env := ρ0 } := by
            simp [Lir.enter, hF, hbind]
          have h1 := hstep _ henter
          obtain ⟨tb, htb, htp⟩ := hL.head hb0 ho0
          have htp' : tb.params = b0.params.map (·.1) := by rw [htp]; simp [headParams, hm]
          obtain ⟨ρ1, hb1, hρ⟩ := bind_rel (envRel_leaf (tables P) Pw (Fused (tables P) fd) (supOf fd) ρ0) hws
            (by simp [hlen]) (params_lt_sup hb0)
          have h2 := Lir.jump_at (p := lp) (mem := s₂.mem) (ctx := s₂.ctx) (rest := lrest) (pos := 0) (ρ := ρ0)
            (e := { target := o0, args := F.params.map .v }) (vals := ws) (ρ' := ρ1) hF hF0 rfl rfl
            (evalArgs_bindParams hnd hbind) htb (by rw [htp']; exact hb1)
          have hc : decide (o0 ≤ 0) = false := by simp; omega
          rw [hc] at h2
          refine ⟨1 + 0, _, (Lir.star_of_step h1).trans (Lir.star_of_step h2), by omega, hctx, Pw, hheap, _, lrest,
            rfl, runAt_head hfd hF hL hb0 ho0 hρ, hstk⟩
      · cases hs

/-! ## Return -/

/-- **Cfg's return to a caller is Lir's.** -/
theorem step_return {P : Cfg.Program} {lp : Lir.Program} {ctx : Word} {v : Own.RVal} {fr : Cfg.Frame} {x : Nat}
    {stk : List (Cfg.Frame × Nat)} {H : Own.Heap} {s₂ : Lir.State}
    (hrel : Rel P lp ctx (.ret v ((fr, x) :: stk) H) s₂) :
    ∃ s₂', Lir.step lp s₂ = .next s₂' false ∧
      Rel P lp ctx (.run { fr with env := fr.env.insert x v } stk H) s₂' := by
  obtain ⟨hctx, Pw, hheap, lfr, lrest, w, hst, hvw, ⟨hd, F, lb, la, hF, hlb, hpos, hterm, hla⟩, hstk⟩ := hrel
  cases hstk with
  | cons hsusp hstk' =>
    rename_i lfr' lrest'
    obtain ⟨hd', fd, b, hpos', hρ, hx, hfz⟩ := hsusp
    have h1 := Lir.step_ret_caller (p := lp) (mem := s₂.mem) (ctx := s₂.ctx) (fr := lfr) (caller := lfr')
      (rest' := lrest') (ρ := lfr'.env.insert x w) (vals := [w]) hF hlb hpos hterm
      (by simp [Lir.evalArgs_cons, Lir.evalArgs_nil, hla]) (by rw [hd']; simp [Lir.bindParams])
    have hs₂ : s₂ = { mem := s₂.mem, ctx := s₂.ctx, stack := lfr :: lfr' :: lrest' } := by
      cases s₂; simp_all
    refine ⟨{ mem := s₂.mem, ctx := s₂.ctx, stack := { lfr' with env := lfr'.env.insert x w, dsts := [] } :: lrest' },
      hs₂ ▸ h1, hctx, Pw, hheap, _, lrest', rfl, ⟨rfl, fd, b, ?_, hρ.insert hx hvw, ?_⟩, hstk'⟩
    · obtain ⟨F, starts, off, C, st, stF, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := hpos'
      exact ⟨F, starts, off, C, st, stF, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
    · intro init c a a' hf hr
      rcases hfz with hn | hne
      · simp [hf] at hn
      · exact absurd hr hne

/-- **The last return is Lir's.** -/
theorem final_return {P : Cfg.Program} {lp : Lir.Program} {ctx : Word} {v : Own.RVal} {H : Own.Heap}
    {s₂ : Lir.State} (hrel : Rel P lp ctx (.ret v [] H) s₂) :
    ∃ w, Lir.step lp s₂ = .done [w] s₂.mem ∧ Res P ctx (v, H) ([w], s₂.mem) := by
  obtain ⟨hctx, Pw, hheap, lfr, lrest, w, hst, hvw, ⟨hd, F, lb, la, hF, hlb, hpos, hterm, hla⟩, hstk⟩ := hrel
  cases hstk
  have h1 := Lir.step_ret_done (p := lp) (mem := s₂.mem) (ctx := s₂.ctx) (fr := lfr) (vals := [w]) hF hlb hpos hterm
    (by simp [Lir.evalArgs_cons, Lir.evalArgs_nil, hla])
  have hs₂ : s₂ = { mem := s₂.mem, ctx := s₂.ctx, stack := [lfr] } := by
    cases s₂; simp_all
  exact ⟨w, hs₂ ▸ h1, Pw, w, rfl, hvw, hheap⟩

end Compilatrix.Rt.Proof
