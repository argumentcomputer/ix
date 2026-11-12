import IxCC.Own.Plain.Proof.Owned.Joins
import IxCC.Own.Plain.Proof.Owned.Actions
import IxCC.Own.Plain.Proof.Owned.Inversion
import IxCC.Own.Plain.Proof.ResultCompose
import IxCC.Own.Plain.Proof.Admission
import IxCC.Fir.Proof.Unfold

/-! # The Own-level induction over an accepted body

`owned_eval` inducts on the **Own** code (an action is a source stutter), with the source code
its erasure, under the lexicographic clock / code-and-join-stack measure of `Own.Plain.eval`.
Calls and charged jumps use the hypothesis at smaller clocks (`AtClockOwned`). -/

set_option autoImplicit false

namespace IxCC.Own.Plain

open Rc
open IxCC.Sem (Result)
open IxCC.Fir (Var Arg)

theorem own_jump_measure {j : Fir.JoinId} {J : List JEntry} {e : JEntry} {rest : List JEntry}
    (h : lookupJ j J = some (e, rest)) (hc : e.charged = false) (args : List Arg) :
    e.body.size + jweight (e.after rest) < (Code.jmp j args).size + jweight J := by
  have hw := lookupJ_weight j h
  rw [JEntry.jweight_after]
  simp only [JEntry.weight, hc, Bool.false_eq_true, ↓reduceIte] at hw
  simp only [Code.size]
  omega

/-- Function entry: parameters own one token each. -/
theorem ownedState_entry (functions : Signatures) (H : Heap) (external : Nat → Nat)
    (params : List Fir.Var) (vs : List RVal) (ws : List Fir.Val)
    (hd : Sem.Forall2 (Proof.Den H) vs ws) (hl : vs.length = params.length)
    (hf : fresh [] params = true) (hb : Balance H external vs) :
    ∃ owned, OwnedState functions H external params (Ctx.entry params)
      (Fir.bindAll .leaf params ws) (Own.bindAll .leaf params vs) owned [] .leaf [] [] ∧
      Balance H external owned := by
  have hn : params.Nodup := by simpa using fresh_nodup_append List.nodup_nil hf
  have htok := Ctx.Tokens.entry params hn
  have hroots : EnvRoots (Own.bindAll .leaf params vs) params vs := by
    simpa using (EnvRoots.nil (.leaf : Own.Env)).bindAll params vs hl hf
  have hden0 : EnvDen H [] (.leaf : Fir.Env) (.leaf : Own.Env) := by intro x hx; simp at hx
  have hden : EnvDen H params (Fir.bindAll .leaf params ws) (Own.bindAll .leaf params vs) := by
    simpa using hden0.bindAll params hd hl
  have himm : ∀ y, (Ctx.entry params).isImm y = false := fun _ => rfl
  have hbrw : ∀ y, (Ctx.entry params).brw.get? y = none := fun _ => rfl
  refine ⟨vs, ⟨fun y hy => ?_, ⟨params, htok, hroots⟩, hb, fun y hy => ?_, hn,
    fun y hy => absurd hy (by simp [himm y]), fun y hy => ?_, fun y e hy => ?_, .nil _ _ _,
    .nil _⟩, hb⟩
  · simp only [Ctx.avail_eq, himm, Ctx.borrowed_eq, hbrw, Bool.false_or, Bool.or_eq_true,
      decide_eq_true_eq] at hy
    rcases hy with hp | hb'
    · exact hden y (htok.mem hp)
    · simp at hb'
  · simp only [Ctx.known_eq, himm, hbrw, Option.isSome_none, Bool.or_false, Bool.false_or] at hy
    exact Ctx.ownHas_ofList hn hy
  · simp [Ctx.borrowed_eq, hbrw] at hy
  · simp [hbrw] at hy

/-- The accepted bodies, for the call step. -/
def BodiesChecked (F : Fir.Program) (candidate : Src.NatMap Code) : Prop :=
  ∀ f fd, f < F.size → F.fun? f = some fd → ∃ body, candidate.get? f = some body ∧
    eraseCode body = fd.body ∧ checkCode .leaf (Ctx.entry (fd.params.map (·.1))) body = .ok ()

theorem owned_call_of_smaller {F : Fir.Program} {candidate : Src.NatMap Code} {k : Nat}
    (domain : contractProgramDomain F = true) (bodies : BodiesChecked F candidate)
    (ih : ∀ j, j < k → AtClockOwned F candidate j)
    {f : Fir.FunId} (hf : f < F.size) {H : Heap} {external : Nat → Nat}
    {vs : List RVal} {ws : List Fir.Val} (hd : Sem.Forall2 (Proof.Den H) vs ws)
    (hb : Balance H external vs) :
    ResultRel H external (Fir.evalCall F k f ws)
      (evalCall { source := F, bodies := candidate } k f vs H) := by
  cases hfd : F.fun? f with
  | none =>
    rw [Fir.evalCall_eq, hfd]
    exact .stuck
  | some fd =>
    obtain ⟨body, hbody, herase, htyped⟩ := bodies f fd hf hfd
    rw [Fir.evalCall_eq, hfd, evalCall_of _ _ _ hfd hbody]
    simp only [Result.ofOption, Result.bind_ok, Fir.callFun, callFun]
    obtain ⟨_, freshParams, scopeBody⟩ := contractProgramDomain_function domain hf hfd
    by_cases hl : ws.length = fd.params.length
    · have hl' : vs.length = fd.params.length := hd.length.trans hl
      simp only [hl, hl', ↓reduceIte]
      refine ResultRel.later fun j hj => ?_
      obtain ⟨owned, st, _⟩ := ownedState_entry (signatures F) H external (fd.params.map (·.1))
        vs ws hd (by simpa using hl') freshParams hb
      have := ih j hj body st (by rw [herase]; exact scopeBody) htyped
      rwa [herase] at this
    · have hl' : ¬vs.length = fd.params.length := by rw [hd.length]; exact hl
      simp only [hl, hl', ↓reduceIte]
      exact .stuck

section
variable {F : Fir.Program} {candidate : Src.NatMap Code}
  (domain : contractProgramDomain F = true) (pins : BoolPinsOk F)
  (bodies : BodiesChecked F candidate)
variable {k : Nat} (smaller : ∀ j, j < k → AtClockOwned F candidate j)
include domain pins bodies smaller

mutual
theorem owned_eval {H : Heap} {external : Nat → Nat} {live : List Var} {Γ : Ctx} {Δ : JCtx}
    {ρf : Fir.Env} {ρo : Own.Env} {owned : List RVal} {lex : Joins}
    {Jf : List Fir.JEntry} {Jo : List JEntry} (c : Code)
    (st : OwnedState (signatures F) H external live Γ ρf ρo owned lex Δ Jf Jo)
    (scope : scopeOk (signatures F) live (stackArities Jf) (eraseCode c) = true)
    (typed : checkCode Δ Γ c = .ok ()) :
    ResultRel H external (Fir.eval F k ρf Jf (eraseCode c))
      (eval { source := F, bodies := candidate } k ρo Jo H c) := by
  match c with
  | .act (.inc x n) c' =>
    obtain ⟨Γ', hc, typed'⟩ := checkCode_inc typed
    obtain ⟨H', owned', hact, st', hpres⟩ := inc_step st hc
    rw [eval_act, hact, Result.bind_ok]
    exact (owned_eval c' st' scope typed').preheap hpres
  | .act (.dec x) c' =>
    obtain ⟨Γ', hc, typed'⟩ := checkCode_dec typed
    obtain ⟨H', owned', hact, st', hpres⟩ := dec_step st hc
    rw [eval_act, hact, Result.bind_ok]
    exact (owned_eval c' st' scope typed').preheap hpres
  | .bind x r c' =>
    have parts : x ∉ live ∧ rhsIn (signatures F) live r = true ∧
        scopeOk (signatures F) (live ++ [x]) (stackArities Jf) (eraseCode c') = true := by
      simpa [eraseCode, scopeOk, Bool.and_eq_true, and_assoc] using scope
    obtain ⟨hx, hr, hc'⟩ := parts
    obtain ⟨Γ', hbc, typed'⟩ := checkCode_bind typed
    by_cases call : ∃ f args, r = .call f args
    · obtain ⟨f, args, rfl⟩ := call
      have hs : (signatures F).lookup f = some args.length ∧ args.all (argIn live) = true := by
        simpa [rhsIn, Bool.and_eq_true] using hr
      obtain ⟨fd, hf, _, _⟩ := signatures_lookup hs.1
      obtain ⟨Γ₁, ht, hΓ⟩ := except_bind_ok hbc
      have hΓ := except_pure_ok hΓ
      subst hΓ
      obtain ⟨vs, ws, owned₁, hvs, hws, hds, inv₁, hs₁, hw₁⟩ := takeArgs_sem st.takeInv ht
      have hcall := owned_call_of_smaller domain bodies smaller hf hds
        (balance_hold.mp (hs₁.balance st.counts))
      show ResultRel H external (Fir.eval F k ρf Jf (.bind x (.call f args) (eraseCode c'))) _
      rw [Fir.eval_bindCall, hws, eval_bindCall, hvs]
      simp only [Result.ofOption, Result.bind_ok]
      apply ResultRel.bind_frame hcall
      intro w v H' hd' hb' hp'
      have pre₁ := st.pre.weaker hw₁ inv₁.roots
      have pre₂ := pre₁.release.call (release_borrowed pre₁.epochs) hp'
      have st' := pre₂.bindOwned hx hd'
        ((SameRefs.comm _ _).balance (balance_resume hb'))
      exact (owned_eval c' st' hc' typed').preheap
        (fun root w' hr' hd'' => hp' root w' (external_hold hr') hd'')
    · have hn : ∀ f args, r ≠ .call f args := fun f args h => call ⟨f, args, h⟩
      show ResultRel H external (Fir.eval F k ρf Jf (.bind x r (eraseCode c'))) _
      rw [Fir.eval_bindRhs F k ρf Jf x r (eraseCode c') hn,
        eval_bindRhs _ k ρo Jo H x r c' hn]
      rcases fir_rhs_pure F ρf r with hstuck | ⟨w, hw⟩
      · rw [hstuck]; exact .stuck
      · obtain ⟨v, H', owned', hev, st', hpres⟩ := rhs_step pins st hx hn hbc hw
        rw [hw, Result.bind_ok]
        change ResultRel H external _
          ((evalRhs { ctors := F.ctors, known := F.known } ρo H r).bind _)
        rw [hev, Result.bind_ok]
        exact (owned_eval c' st' hc' typed').preheap hpres
  | .jp j ps captured rec body c' =>
    obtain ⟨hnd, hneed, htb, htk⟩ := checkCode_jp typed
    have parts : (stackArities Jf).lookup j = none ∧ fresh live ps = true ∧
        scopeOk (signatures F) (live ++ ps)
          (if rec then (j, ps.length) :: stackArities Jf else stackArities Jf) (eraseCode body) = true ∧
        scopeOk (signatures F) live ((j, ps.length) :: stackArities Jf) (eraseCode c') = true := by
      simpa [eraseCode, scopeOk, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using scope
    obtain ⟨hnone, hf, hb, hc'⟩ := parts
    have st' := st.declare hnd hneed htb hnone hf hb
    show ResultRel H external (Fir.eval F k ρf Jf (.jp j ps rec (eraseCode body) (eraseCode c'))) _
    rw [Fir.eval_jp, eval_jp]
    exact owned_eval c' st' (by simpa [stackArities] using hc') htk
  | .jmp j args =>
    obtain ⟨captured, Γ₁, Γ₂, hΔ, h1, h2, h3⟩ := checkCode_jmp typed
    have hs : (stackArities Jf).lookup j = some args.length := by
      have : decide ((stackArities Jf).lookup j = some args.length) = true ∧
          args.all (argIn live) = true := by
        simpa only [eraseCode, scopeOk, Bool.and_eq_true] using scope
      simpa using this.1
    obtain ⟨ef, restf, hl, _⟩ := Fir.lookupJ_of_arity hs
    obtain ⟨vs, ws, eo, resto, hvs, hws, hlen', hlo, hpar, hch, hbody⟩ :=
      jump_body st hΔ h1 h2 h3 hl
    show ResultRel H external (Fir.eval F k ρf Jf (.jmp j args)) _
    rw [Fir.eval_jmp_of F k ρf Jf hl hws, eval_jmp, hlo, hvs]
    simp only [Result.ofOption, Result.bind_ok]
    unfold Fir.jumpTo jumpTo
    by_cases hlen : ws.length = ef.params.length
    · have hlo' : vs.length = eo.params.length := by rw [hpar, hlen', hlen]
      simp only [hlen, hlo', ↓reduceIte, hch]
      obtain ⟨Δb, Γb, lexd, lexb, owned', st', typed', herase, scope'⟩ := hbody hlen
      cases hc : ef.charged with
      | true =>
        simp only [↓reduceIte]
        refine ResultRel.later fun j' hj' => ?_
        have := smaller j' hj' eo.body st' (by rw [herase]; exact scope') typed'
        rwa [herase] at this
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        have hco : eo.charged = false := by rw [hch]; exact hc
        have := own_jump_measure hlo hco args
        have := owned_eval eo.body st' (by rw [herase]; exact scope') typed'
        rwa [herase] at this
    · simp only [hlen, ↓reduceIte]
      exact .stuck
  | .case x alts d =>
    obtain ⟨hneed, halts, hopt⟩ := checkCode_case typed
    have parts : x ∈ live ∧ scopeAlts (signatures F) live (stackArities Jf) (eraseAlts alts) = true ∧
        scopeOpt (signatures F) live (stackArities Jf) (eraseOpt d) = true := by
      simpa [eraseCode, scopeOk, Bool.and_eq_true, and_assoc] using scope
    obtain ⟨v, w, hv, hw, hd⟩ := st.den x (Ctx.need_avail hneed)
    show ResultRel H external (Fir.eval F k ρf Jf (.case x (eraseAlts alts) (eraseOpt d))) _
    rw [Fir.eval_case, hw, eval_case, hv]
    simp only [Result.ofOption, Result.bind_ok]
    cases hk : w.asCtor F.known with
    | none => exact .stuck
    | some p =>
      obtain ⟨key, fs⟩ := p
      obtain ⟨fields, hfields, _⟩ := (Values.asCtor_den F.known hd).1 key fs hk
      simp only [hfields]
      exact owned_evalAlts key alts d st parts.2.1 parts.2.2 halts hopt
  | .ret a =>
    obtain ⟨Γ', ht, hcl⟩ := checkCode_ret typed
    obtain ⟨v, w, owned₁, hev, hfa, hd, inv₁, hs, _⟩ := takeArg_sem st.takeInv ht
    obtain ⟨toks₁, htok₁, hr₁⟩ := inv₁.roots
    have hnil := closed_nil htok₁ hcl
    subst hnil
    have ho := EnvRoots.nil_inv hr₁
    subst ho
    show ResultRel H external (Fir.eval F k ρf Jf (.ret a)) _
    rw [Fir.eval_ret, hfa, eval_ret, hev]
    simp only [Result.ofOption, Result.bind_ok]
    exact .ok hd (hs.balance st.counts) (fun _ _ _ h => h)
  | .tcall f args =>
    obtain ⟨Γ', ht, hcl⟩ := checkCode_tcall typed
    have hs : (signatures F).lookup f = some args.length := by
      have : decide ((signatures F).lookup f = some args.length) = true ∧
          args.all (argIn live) = true := by
        simpa only [eraseCode, scopeOk, Bool.and_eq_true] using scope
      simpa using this.1
    obtain ⟨fd, hf, _, _⟩ := signatures_lookup hs
    obtain ⟨vs, ws, owned₁, hvs, hws, hds, inv₁, hs₁, _⟩ := takeArgs_sem st.takeInv ht
    obtain ⟨toks₁, htok₁, hr₁⟩ := inv₁.roots
    have hnil := closed_nil htok₁ hcl
    subst hnil
    have ho := EnvRoots.nil_inv hr₁
    subst ho
    show ResultRel H external (Fir.eval F k ρf Jf (.tcall f args)) _
    rw [Fir.eval_tcall, hws, eval_tcall, hvs]
    simp only [Result.ofOption, Result.bind_ok]
    exact owned_call_of_smaller domain bodies smaller hf hds
      ((by simpa using hs₁ : SameRefs owned vs).balance st.counts)
  | .trap =>
    show ResultRel H external (Fir.eval F k ρf Jf .trap) _
    rw [Fir.eval_trap, eval_trap]
    exact .trap
termination_by c.size + jweight Jo
decreasing_by
  all_goals simp_wf
  all_goals first
    | (simp only [Code.size]; omega)
    | (simp only [Code.size, jweight, JEntry.weight, Bool.false_eq_true, ↓reduceIte]; omega)
    | omega

theorem owned_evalAlts {H : Heap} {external : Nat → Nat} {live : List Var} {Γ : Ctx} {Δ : JCtx}
    {ρf : Fir.Env} {ρo : Own.Env} {owned : List RVal} {lex : Joins}
    {Jf : List Fir.JEntry} {Jo : List JEntry} (key : Key.CtorKey) (alts : List Alt)
    (d : Option Code)
    (st : OwnedState (signatures F) H external live Γ ρf ρo owned lex Δ Jf Jo)
    (ha : scopeAlts (signatures F) live (stackArities Jf) (eraseAlts alts) = true)
    (hd : scopeOpt (signatures F) live (stackArities Jf) (eraseOpt d) = true)
    (typedAlts : checkAlts Δ Γ alts = .ok ()) (typedOpt : checkOpt Δ Γ d = .ok ()) :
    ResultRel H external (Fir.evalAlts F k ρf Jf key (eraseAlts alts) (eraseOpt d))
      (evalAlts { source := F, bodies := candidate } k ρo Jo H key alts d) := by
  match alts, d with
  | [], some c =>
    simp only [eraseAlts, eraseOpt]
    rw [Fir.evalAlts_nil, evalAlts_nil]
    exact owned_eval c st (by simpa [eraseOpt, scopeOpt] using hd)
      (by simpa [checkOpt] using typedOpt)
  | [], none =>
    simp only [eraseAlts, eraseOpt]
    rw [Fir.evalAlts_nil]
    exact .stuck
  | .mk key' body :: rest, d =>
    obtain ⟨tb, tr⟩ := checkAlts_cons typedAlts
    have hs : scopeOk (signatures F) live (stackArities Jf) (eraseCode body) = true ∧
        scopeAlts (signatures F) live (stackArities Jf) (eraseAlts rest) = true := by
      simpa only [eraseAlts, scopeAlts, Bool.and_eq_true] using ha
    simp only [eraseAlts]
    rw [Fir.evalAlts_cons, evalAlts_cons]
    split
    · exact owned_eval body st hs.1 tb
    · exact owned_evalAlts key rest d st hs.2 hd tr typedOpt
termination_by Code.altsSize alts + Code.optSize d + jweight Jo + 1
decreasing_by
  all_goals simp_wf
  all_goals simp only [Code.altsSize, Code.optSize]
  all_goals first
    | omega
    | (have := Code.size_pos body; omega)
end

end

/-- **The milestone-1 induction**. -/
theorem owned_refines_of {F : Fir.Program} {candidate : Src.NatMap Code}
    (domain : contractProgramDomain F = true) (pins : BoolPinsOk F)
    (bodies : BodiesChecked F candidate) : ∀ k, AtClockOwned F candidate k := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro H external live Γ Δ ρf ρo owned lex Jf Jo c st scope typed
    exact owned_eval domain pins bodies ih c st scope typed

end IxCC.Own.Plain
