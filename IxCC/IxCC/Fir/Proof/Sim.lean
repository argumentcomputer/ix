import IxCC.Fir.Proof.Corr

/-! # The Anf → Fir simulation

For an Anf program `A` lowered to `F` (`Fir.lower A = .ok F`) and its tick
bound `N` (`Fir.tickBound A`), every Anf configuration the lowering
relates to a Fir one satisfies `Corr` at every clock (`stmt`): by strong
induction on Anf's clock, and within one clock by recursion on the Anf
term. Each construct inverts the lowering (`Fir.Proof.Lowering`), unfolds
both evaluators in bind form, and chains the `Corr` combinators:

* `bind`: the right-hand side, then the rest under one more name
  (`EnvR.push1`); a call is a charge on both sides (`call_corr`), a tail
  call through ticks a call whose value is returned once the ticks pass
  (`Corr.bindTail`);
* `join`: Anf pushes a join closure, Fir a join entry (`JRel.cons`);
* `jump`: Anf's index and Fir's id find the same position (`JRel.lookup`);
  a jump into a recursive join point's own body is a charge on both sides,
  any other jump an Anf-only charge (`Corr.tick`) whose cost the tick bound
  counts;
* `case`: the scrutinee reads as the same constructor; Fir selects by key
  alone, Anf by key and arity, which agree because related constructors
  have the table's field count (`asCtor_arity`); an arm's projections bind
  the fields its body uses (`projections_run`, `EnvR.arm`);
* `tick`: an Anf-only charge. -/

set_option autoImplicit false

namespace IxCC.Fir.Proof

open IxCC.Sem (Result later ClockMono)
open IxCC.Fir.Lower

/-- What the simulation needs of the lowered program. -/
structure Setting (A : Anf.Program) (F : Program) (N : Nat) : Prop where
  pos : 0 < N
  known : F.known = A.known
  ctors : F.ctors = A.ctors
  pins : pinsOk A = true
  funs : ∀ {h : Anf.GlobalId} {gd : Anf.GDef}, A.global? h = some gd → h < A.size →
    ∃ fd, F.fun? h = some fd ∧ function A h gd = .ok fd
  depth : ∀ {h : Anf.GlobalId} {gd : Anf.GDef}, A.global? h = some gd → h < A.size → tickDepth gd < N

/-- `Fir.lower`'s output, with the tick bound. -/
theorem setting_of {A : Anf.Program} {F : Program} (h : lower A = .ok F) : Setting A F (tickBound A) where
  pos := by unfold tickBound; fir_omega
  known := (lower_fields h).2.2.2
  ctors := (lower_fields h).2.2.1
  pins := (lower_ok h).2.1
  funs hg hs := lower_fun h hg hs
  depth hg hs := tickDepth_lt hg hs

/-- The simulation at Anf clock `a`, for every related configuration. -/
def Stmt (A : Anf.Program) (F : Program) (N a : Nat) : Prop :=
  ∀ (g : Anf.GlobalId) (e : Anf.Exp) (ρ : List Var) (J : List JoinId) (st : St) (c : Code) (st' : St)
    (cs : List Nat) (ρa : List Anf.Val) (ρf : Env) (Ja : List Anf.JClo) (Jf : List JEntry),
    exp A g ρ J st e = .ok (c, st') → (∀ x ∈ ρ, x < st.vars) → (∀ j ∈ J, j < st.joins) →
    (TickBound.exp cs e).2 < N → EnvR A (fun i => 0 < e.occ i) ρ ρa ρf → JRel A N g J cs Ja Jf →
    Corr A N a (TickBound.exp cs e).1 (Anf.eval A a ρa Ja e) (fun k => eval F k ρf Jf c)

/-! ## Calls -/

theorem range_reverse_lt {n : Nat} : ∀ x ∈ (List.range n).reverse, x < n := by
  intro x hx; simpa using hx

/-- Entering a global: a charge on both sides, then the body. -/
theorem call_corr {A : Anf.Program} {F : Program} {N a : Nat} (S : Setting A F N)
    (ih : ∀ a' < a, Stmt A F N a') {h : Anf.GlobalId} {gd : Anf.GDef} (hg : A.global? h = some gd)
    (hs : h < A.size) {fd : Fun} (hfd : function A h gd = .ok fd) {vs : List Anf.Val} {ws : List Val}
    (hvs : VRs A vs ws) (hl : vs.length = gd.ps.length) :
    Corr A N a 0 (Anf.callVal A a gd vs) (fun k => callFun F k fd ws) := by
  obtain ⟨st, hlow, hps⟩ := function_ok hfd
  have hmap : fd.params.map (·.1) = List.range gd.ps.length := by rw [hps]; simp [Function.comp_def]
  have hwl : ws.length = fd.params.length := by rw [← hvs.length, hl, hps]; simp
  have hD := tickDepth_ge gd
  have hdep := S.depth hg hs
  unfold Anf.callVal callFun
  simp only [hl, hwl, hmap, ↓reduceIte]
  refine Corr.charge (D := (TickBound.exp [] gd.body).1) (by fir_omega) fun a' ha => ?_
  refine ih a' (by fir_omega) h gd.body _ [] _ fd.body st [] vs.reverse _ [] [] hlow (fun x hx => by simpa using hx)
    (fun _ h => by cases h) (by fir_omega) ?_ .nil
  have := EnvR.push (live := fun i => 0 < gd.body.occ i) (n := gd.ps.length) (ρ := []) (ρa := []) (ρf := .leaf) ⟨rfl, fun _ _ _ _ h => by simp at h⟩
    (ps := List.range gd.ps.length) List.nodup_range (fun _ _ h => by simp at h) (by simp) hvs hl
  simpa using this

theorem globVal_eq {A : Anf.Program} {a : Nat} {gd : Anf.GDef} (h : gd.ps = []) :
    Anf.globVal A a gd = Anf.callVal A a gd [] := by
  unfold Anf.globVal Anf.callVal
  rw [h]
  simp

/-! ## Tail calls through ticks -/

/-- The ticks before a tail call's `ret`. -/
def tailTicks : Anf.Exp → Nat
  | .tick e => tailTicks e + 1
  | _ => 0

theorem returnsTop_spec {A : Anf.Program} :
    ∀ {e : Anf.Exp}, returnsTop e = true →
      (∀ cs, TickBound.exp cs e = (tailTicks e, 0)) ∧
        ∀ a v ρa Ja, Anf.eval A a (v :: ρa) Ja e = if tailTicks e ≤ a then .ok v else .timeout
  | .ret (.var 0), _ => by
    refine ⟨fun cs => rfl, fun a v ρa Ja => ?_⟩
    rw [Anf.eval_ret']
    simp [tailTicks, Anf.Atom.eval, Result.ofOption]
  | .tick e, h => by
    simp only [returnsTop] at h
    obtain ⟨hcs, hev⟩ := returnsTop_spec h
    refine ⟨fun cs => by simp [TickBound.exp, hcs cs, tailTicks], fun a v ρa Ja => ?_⟩
    rw [Anf.eval_tick]
    cases a with
    | zero => simp [tailTicks]
    | succ a => rw [IxCC.Sem.later_succ, hev]; simp [tailTicks]
  | .ret (.var (_ + 1)), h | .ret (.lit _), h | .ret .box, h | .bind .., h | .join .., h | .jump .., h
  | .case .., h | .trap, h => by simp [returnsTop] at h

/-! ## Projections -/

theorem projVal_rel {A : Anf.Program} {F : Program} {key : Key.CtorKey}
    {i : Nat} {v : Anf.Val} {w : Val} (h : VR A v w) :
    (∀ v', Anf.projVal key i v = .ok v' → ∃ w', projVal F key i w = .ok w' ∧ VR A v' w') ∧
      (Anf.projVal key i v = .stuck ∨ ∃ v', Anf.projVal key i v = .ok v') := by
  cases h with
  | lit l => exact ⟨fun _ h => by simp [Anf.projVal] at h, .inl rfl⟩
  | box => exact ⟨fun _ h => by simp [Anf.projVal] at h, .inl rfl⟩
  | @con c info vs ws hi hvs hl =>
    unfold Anf.projVal
    by_cases hc : c = key
    · subst hc
      simp only [↓reduceIte]
      refine ⟨fun v' hv' => ?_, ?_⟩
      · cases hvi : vs[i]? with
        | none => rw [hvi] at hv'; cases hv'
        | some v'' =>
          rw [hvi] at hv'
          cases hv'
          obtain ⟨w', hw', hvw'⟩ := hvs.get hvi
          refine ⟨w', ?_, hvw'⟩
          simp [projVal, Val.asCtor, ofKey_key hi, hw', Result.ofOption]
      · cases vs[i]? with
        | none => exact .inl rfl
        | some v'' => exact .inr ⟨v'', rfl⟩
    · simp only [hc, ↓reduceIte]
      exact ⟨(fun _ h => by cases h), .inl trivial⟩

/-! ## The step -/

section

variable {A : Anf.Program} {F : Program} {N a : Nat} (S : Setting A F N)
  (ih : ∀ a' < a, Stmt A F N a')
include S ih

set_option maxHeartbeats 1000000 in
set_option linter.unusedSectionVars false in
mutual

theorem step_exp (g : Anf.GlobalId) (e : Anf.Exp) (ρ : List Var) (J : List JoinId) (st : St) (c : Code)
    (st' : St) (cs : List Nat) (ρa : List Anf.Val) (ρf : Env) (Ja : List Anf.JClo) (Jf : List JEntry)
    (hlow : exp A g ρ J st e = .ok (c, st')) (hρ : ∀ x ∈ ρ, x < st.vars) (hJ : ∀ j ∈ J, j < st.joins)
    (hs : (TickBound.exp cs e).2 < N) (henv : EnvR A (fun i => 0 < e.occ i) ρ ρa ρf)
    (hjr : JRel A N g J cs Ja Jf) :
    Corr A N a (TickBound.exp cs e).1 (Anf.eval A a ρa Ja e) (fun k => eval F k ρf Jf c) := by
  match e with
  | .bind cc b e' =>
    have hs' : (TickBound.exp cs e').2 < N := hs
    have hD : (TickBound.exp cs (.bind cc b e')).1 = (TickBound.exp cs e').1 := rfl
    rw [hD, Anf.eval_bind]
    -- the rest under one more name
    have hrest : ∀ (x : Var) (st₁ : St) (kc : Code) (v : Anf.Val) (w : Val),
        (∀ y ∈ ρ, y < x) → st₁.vars = x + 1 → st₁.joins = st.joins →
        exp A g (x :: ρ) J st₁ e' = .ok (kc, st') → VR A v w →
        Corr A N a (TickBound.exp cs e').1 (Anf.eval A a (v :: ρa) Ja e')
          (fun k => eval F k (ρf.insert x w) Jf kc) := by
      intro x st₁ kc v w hx hv hj hk hvw
      have hρ' : ∀ y ∈ x :: ρ, y < st₁.vars := by
        intro y hy
        rw [hv]
        rcases List.mem_cons.1 hy with h | h
        · exact h ▸ Nat.lt_succ_self x
        · exact Nat.lt_succ_of_lt (hx y h)
      have hJ' : ∀ j ∈ J, j < st₁.joins := by
        intro j hj'
        rw [hj]
        exact hJ j hj'
      have henv' : EnvR A (fun i => 0 < e'.occ i) (x :: ρ) (v :: ρa) (ρf.insert x w) := by
        refine EnvR.push1 (henv.mono fun i hi => ?_) (fun hm => Nat.lt_irrefl _ (hx x hm)) hvw
        simp only [Anf.Exp.occ]
        exact Nat.lt_of_lt_of_le hi (Nat.le_add_left _ _)
      exact step_exp g e' (x :: ρ) J st₁ kc st' cs (v :: ρa) (ρf.insert x w) Ja Jf hk hρ' hJ' hs' henv' hjr
    cases b with
    | call h0 as =>
      obtain ⟨args, hargs, hsz, hcase⟩ := exp_call hlow
      rw [Anf.evalBind_call, Result.bind_assoc]
      refine Corr.ofOption fun gd hg => ?_
      rw [Result.bind_assoc]
      refine Corr.ofOption fun vs hvs => ?_
      obtain ⟨ws, hws, hvws⟩ := atoms_rel henv hargs (fun i hi => by simp only [Anf.Exp.occ, Anf.Bind.occ]; fir_omega) hvs
      obtain ⟨fd, hfd, hfun⟩ := S.funs hg hsz
      by_cases hl : vs.length = gd.ps.length
      · have hcall := call_corr S ih hg hsz hfun hvws hl
        rcases hcase with ⟨htop, rfl, rfl⟩ | ⟨htop, kc, hk, rfl⟩
        · obtain ⟨hcs, hev⟩ := returnsTop_spec (A := A) htop
          rw [hcs]
          refine (Corr.bindTail hcall).ofEq (Result.bind_congr _ fun v => hev a v ρa Ja) |>.congr fun k => ?_
          rw [eval_tcall, hws]
          exact evalCall_of F k hfd ws
        · refine (Corr.bind S.pos (callFun_mono F fd ws) hcall fun v w _ _ hvw =>
            hrest _ _ kc v w hρ (by simp) (by simp) hk hvw).congr fun k => ?_
          rw [eval_bindCall, hws]
          simp only [Result.ofOption, Result.bind_ok]
          rw [evalCall_of F k hfd ws]
      · simp only [Anf.callVal, hl, ↓reduceIte]; exact Corr.stuck _
    | glob h0 =>
      obtain ⟨hsz, hd, hg, hps, hcase⟩ := exp_glob hlow
      rw [Anf.evalBind_glob, hg]
      simp only [Result.ofOption, Result.bind_ok]
      rw [globVal_eq hps]
      obtain ⟨fd, hfd, hfun⟩ := S.funs hg hsz
      have hcall := call_corr S ih hg hsz hfun (vs := []) (ws := []) .nil (by simp [hps])
      rcases hcase with ⟨htop, rfl, rfl⟩ | ⟨htop, kc, hk, rfl⟩
      · obtain ⟨hcs, hev⟩ := returnsTop_spec (A := A) htop
        rw [hcs]
        refine (Corr.bindTail hcall).ofEq (Result.bind_congr _ fun v => hev a v ρa Ja) |>.congr fun k => ?_
        rw [eval_tcall]
        exact evalCall_of F k hfd []
      · refine (Corr.bind S.pos (callFun_mono F fd []) hcall fun v w _ _ hvw =>
          hrest _ _ kc v w hρ (by simp) (by simp) hk hvw).congr fun k => ?_
        rw [eval_bindCall]
        simp only [evalArgs, Result.ofOption, Result.bind_ok]
        rw [evalCall_of F k hfd []]
    | atom a0 =>
      obtain ⟨arg, kc, harg, hk, rfl⟩ := exp_atom hlow
      rw [Anf.evalBind_atom]
      refine Corr.ofOption fun v hv => ?_
      obtain ⟨w, hw, hvw⟩ := atom_rel henv harg (fun i hi => by simp only [Anf.Exp.occ, Anf.Bind.occ]; fir_omega) hv
      refine (hrest _ _ kc v w hρ (by simp) (by simp) hk hvw).congr fun k => ?_
      rw [eval_bind_arg, evalRhs_arg, hw]
      rfl
    | con key as =>
      obtain ⟨args, info, kc, hargs, hi, hal, hk, rfl⟩ := exp_con hlow
      rw [Anf.evalBind_con, Result.bind_assoc]
      refine Corr.ofOption fun vs hvs => ?_
      obtain ⟨ws, hws, hvws⟩ := atoms_rel henv hargs (fun i hi => by simp only [Anf.Exp.occ, Anf.Bind.occ]; fir_omega) hvs
      have hwl : ws.length = info.arity := by
        rw [← hvws.length, Anf.evalAtoms_length _ hvs, hal]
      simp only [Result.bind_ok]
      refine (hrest _ _ kc _ _ hρ (by simp) (by simp) hk (.con hi hvws hwl)).congr fun k => ?_
      rw [eval_bind_ctor, evalRhs_ctor, hws]
      simp [Result.ofOption, hwl]
    | proj key i a0 =>
      obtain ⟨y, pre, st₁, kc, hav, hk, rfl⟩ := exp_proj hlow
      rw [Anf.evalBind_proj, Result.bind_assoc]
      refine Corr.ofOption fun v hv => ?_
      rcases atomVar_inv hav with ⟨j, rfl, hy, rfl, rfl⟩ | ⟨arg, hnv, harg, rfl, rfl, rfl⟩
      · obtain ⟨w, hw, hvw⟩ := henv.2 j y v (by simp only [Anf.Exp.occ, Anf.Bind.occ, Anf.Atom.occ, beq_self_eq_true, ↓reduceIte]; fir_omega)
          hy hv
        obtain ⟨hpv, hcases⟩ := projVal_rel (F := F) (key := key) (i := i) hvw
        rcases hcases with hst | ⟨v', hv'⟩
        · rw [hst]; exact Corr.stuck _
        · rw [hv', Result.bind_ok]
          obtain ⟨w', hw', hvw'⟩ := hpv v' hv'
          refine (hrest _ _ kc v' w' hρ (by simp) (by simp) hk hvw').congr fun k => ?_
          simp only [id]
          rw [eval_bind_proj, evalRhs_proj, hw]
          simp only [Result.ofOption, Result.bind_ok, hw']
      · -- a literal or □ source: Anf's projection is stuck
        have : Anf.projVal key i v = .stuck := by
          cases a0 with
          | var j => exact absurd rfl (hnv j)
          | lit l => simp only [Anf.Atom.eval, Option.some.injEq] at hv; subst hv; rfl
          | box => simp only [Anf.Atom.eval, Option.some.injEq] at hv; subst hv; rfl
        rw [this]
        exact Corr.stuck _
    | prim p as =>
      obtain ⟨args, kc, hargs, hb, hk, rfl⟩ := exp_prim hlow
      rw [Anf.evalBind_prim, Result.bind_assoc]
      refine Corr.ofOption fun vs hvs => ?_
      obtain ⟨ws, hws, hvws⟩ := atoms_rel henv hargs (fun i hi => by simp only [Anf.Exp.occ, Anf.Bind.occ]; fir_omega) hvs
      obtain ⟨hpv, hcases⟩ := primResult_rel S.known S.ctors hb hvws
      rcases hcases with hst | ⟨v, hv⟩
      · rw [hst]; exact Corr.stuck _
      · rw [hv, Result.bind_ok]
        obtain ⟨w, hw, hvw⟩ := hpv v hv
        refine (hrest _ _ kc v w hρ (by simp) (by simp) hk hvw).congr fun k => ?_
        rw [eval_bind_prim, evalRhs_prim, hws]
        simp only [Result.ofOption, Result.bind_ok, hw]
    | app f as => exact (exp_app hlow).elim
    | fn ps b' => exact (exp_fn hlow).elim
  | .join n r b e' =>
    obtain ⟨st₀, body, st₁, kc, h₀v, h₀j, hb, hk, rfl⟩ := exp_join hlow
    have g₀₁ := exp_grows hb
    rw [Anf.eval_join']; simp only [eval_jp]
    have hD : (TickBound.exp cs (.join n r b e')).1 =
        (TickBound.exp (((TickBound.exp (if r then 0 :: cs else cs) b).1 + 1) :: cs) e').1 := rfl
    have hsj : (TickBound.exp cs (.join n r b e')).2 =
        max (max (TickBound.exp (if r then 0 :: cs else cs) b).2
          (TickBound.exp (((TickBound.exp (if r then 0 :: cs else cs) b).1 + 1) :: cs) e').2)
          (if r then (TickBound.exp (if r then 0 :: cs else cs) b).1 else 0) := rfl
    rw [hD]
    have hv₁ := g₀₁.1
    have hj₁ := g₀₁.2
    have hρ₁ : ∀ x ∈ ρ, x < st₁.vars := fun x hx => by have := hρ x hx; fir_omega
    have hJ₁ : ∀ j ∈ st.joins :: J, j < st₁.joins := by
      intro j hj
      rcases List.mem_cons.1 hj with rfl | hj
      · fir_omega
      · have := hJ j hj; fir_omega
    have hJ₀ : ∀ j ∈ (if r then st.joins :: J else J), j < st₀.joins := by
      intro j hj
      cases r
      · simp only [Bool.false_eq_true, ↓reduceIte] at hj; have := hJ j hj; fir_omega
      · simp only [↓reduceIte] at hj
        rcases List.mem_cons.1 hj with rfl | hj
        · fir_omega
        · have := hJ j hj; fir_omega
    have hsb : (TickBound.exp (if r then 0 :: cs else cs) b).2 < N := by
      fir_omega
    have hdb : r = true → (TickBound.exp (0 :: cs) b).1 < N := by
      intro hr; subst hr; simp only [↓reduceIte] at hsj ⊢; fir_omega
    have hent : EntryR A N g J cs Ja (.mk ρa Ja n b r)
        { id := st.joins, charged := false, env := ρf, params := List.range' st.vars n, body := body
          isRec := r } ((TickBound.exp (if r then 0 :: cs else cs) b).1 + 1) :=
      ⟨ρa, n, b, ρ, st.vars, st₀, st₁, rfl, (fun h => by cases h), rfl, hρ, (by fir_omega), hJ₀, hb,
        henv.mono (fun i hi => by simp only [Anf.Exp.occ]; fir_omega), hsb, hdb, (by simp)⟩
    exact step_exp g e' ρ (st.joins :: J) st₁ kc st' _ ρa _ (.mk ρa Ja n b r :: Ja) _ hk hρ₁ hJ₁
      (by fir_omega) (henv.mono fun i hi => by simp only [Anf.Exp.occ]; fir_omega)
      (.cons hjr rfl (fun hm => Nat.lt_irrefl _ (hJ _ hm)) hent)
  | .jump j as =>
    obtain ⟨args, j', hargs, hj, rfl, rfl⟩ := exp_jump hlow
    obtain ⟨jc, ent, hjc, hlk, hent, hrest, hid, hnot⟩ := hjr.lookup hj
    have hD : (TickBound.exp cs (.jump j as)).1 = cs.getD j 0 := rfl
    rw [hD, Anf.eval_jump, hjc]
    simp only [Result.ofOption, Result.bind_ok]
    obtain ⟨ρa', n, b, names, s₀, stb, stb', rfl, hch, hps, hnm, hs₀, hjs, hlowb, henvb, hsb, hdb, hcost⟩ :=
      hent
    cases hvs : Anf.evalAtoms ρa as with
    | none => exact Corr.stuck _
    | some vs =>
      simp only [Result.bind_ok]
      obtain ⟨ws, hws, hvws⟩ := atoms_rel henv hargs (fun i hi => by simpa [Anf.Exp.occ] using hi) hvs
      have hfir : ∀ k, eval F k ρf Jf (.jmp j' args) = jumpTo F k ent (Jf.drop (j + 1)) ws := fun k =>
        eval_jmp_of F k ρf Jf hlk hws
      simp only [Anf.jumpTo]
      by_cases hn : vs.length = n
      · simp only [hn, ↓reduceIte]
        have hwl : ws.length = ent.params.length := by rw [← hvws.length, hn, hps]; simp
        have hnot' : ent.id ∉ J.drop (j + 1) := by rw [hid]; exact hnot
        have hbody : ∀ a', a' < a → Corr A N a' (TickBound.exp (if ent.isRec then 0 :: cs.drop (j + 1)
              else cs.drop (j + 1)) b).1
            (Anf.eval A a' (vs.reverse ++ ρa') (if ent.isRec then .mk ρa' (Ja.drop (j + 1)) n b ent.isRec ::
              Ja.drop (j + 1) else Ja.drop (j + 1)) b)
            (fun k => eval F k (bindAll ent.env ent.params ws) (ent.after (Jf.drop (j + 1))) ent.body) := by
          intro a' ha'
          have hρb : ∀ x ∈ ent.params.reverse ++ names, x < stb.vars := by
            intro x hx
            rcases List.mem_append.1 hx with hx | hx
            · rw [hps] at hx; simp at hx; fir_omega
            · have := hnm x hx; fir_omega
          have henvb' : EnvR A (fun i => 0 < b.occ i) (ent.params.reverse ++ names) (vs.reverse ++ ρa')
              (bindAll ent.env ent.params ws) := by
            rw [hps]
            refine henvb.push List.nodup_range' (fun p hp hpn => ?_) (by simp) hvws hn
            have := hnm p hpn; simp at hp; fir_omega
          have hjrb := hrest.after (cost := cs.getD j 0) ⟨ρa', n, b, names, s₀, stb, stb', rfl, hch, hps, hnm,
            hs₀, hjs, hlowb, henvb, hsb, hdb, hcost⟩ hnot'
          exact ih a' ha' g b (ent.params.reverse ++ names) (if ent.isRec then ent.id :: J.drop (j + 1)
            else J.drop (j + 1)) stb ent.body stb' _ (vs.reverse ++ ρa') _ _ _ hlowb hρb hjs hsb henvb' hjrb
        cases hc : ent.charged with
        | true =>
          have hr := hch hc
          rw [hcost, hc]
          simp only [↓reduceIte]
          have hdb' : (TickBound.exp (if ent.isRec then 0 :: cs.drop (j + 1) else cs.drop (j + 1)) b).1 < N := by
            rw [hr]; exact hdb hr
          refine (Corr.charge hdb' fun a' ha => hbody a' (by fir_omega)).congr fun k => ?_
          rw [hfir]; unfold jumpTo; simp only [hwl, hc, ↓reduceIte]
        | false =>
          rw [hcost, hc]
          simp only [Bool.false_eq_true, ↓reduceIte]
          refine (Corr.tick (eval_mono F _ _ _) fun a' ha => hbody a' (by fir_omega)).congr fun k => ?_
          rw [hfir]; unfold jumpTo; simp only [hwl, hc, Bool.false_eq_true, ↓reduceIte]
      · simp only [hn, ↓reduceIte]; exact Corr.stuck _
  | .case x alts d =>
    obtain ⟨y, pre, st₁, alts', st₂, d', hav, has, hd, rfl⟩ := exp_case hlow
    have g₀ := atomVar_grows hav
    have gₐ := exps_grows has
    have hD : TickBound.exp cs (.case x alts d) =
        TickBound.maxPair (TickBound.alts' cs alts) (TickBound.opt cs d) := rfl
    rw [hD] at hs ⊢
    rw [Anf.eval_case]
    refine Corr.ofOption fun v hv => ?_
    -- the scrutinee in Fir's environment (after binding a literal or □ first)
    obtain ⟨ρf₁, w, hρf₁, hw, hvw, henv₁, hy⟩ : ∃ ρf₁ w, (∀ k, eval F k ρf Jf (pre (.case y alts' d')) =
          eval F k ρf₁ Jf (.case y alts' d')) ∧ ρf₁.get? y = some w ∧ VR A v w ∧
        EnvR A (fun i => 0 < Anf.Exp.altsOcc i alts + Anf.Exp.optOcc i d) ρ ρa ρf₁ ∧ y < st₁.vars := by
      rcases atomVar_inv hav with ⟨i, rfl, hyi, rfl, rfl⟩ | ⟨arg, hnv, harg, rfl, rfl, rfl⟩
      · obtain ⟨w, hw, hvw⟩ := henv.2 i y v (by simp only [Anf.Exp.occ, Anf.Atom.occ, beq_self_eq_true, ↓reduceIte]; fir_omega) hyi hv
        exact ⟨ρf, w, fun _ => rfl, hw, hvw, henv.mono fun i hi => by simp only [Anf.Exp.occ]; fir_omega,
          hρ y (List.mem_of_getElem? hyi)⟩
      · obtain ⟨w, hw, hvw⟩ := atom_rel henv harg (fun i hi => by
          cases x with
          | var j => exact absurd rfl (hnv j)
          | _ => simp [Anf.Atom.occ] at hi) hv
        refine ⟨ρf.insert st.vars w, w, fun k => ?_, by simp [Src.NatMap.get?_insert_self], hvw,
          (henv.mono fun i hi => by simp only [Anf.Exp.occ]; fir_omega).insert
            (fun hm => Nat.lt_irrefl _ (hρ _ hm)) w, by simp⟩
        rw [eval_bind_arg, evalRhs_arg, hw]
        rfl
    refine Corr.congr ?_ fun k => (hρf₁ k).trans (eval_case F k ρf₁ Jf y alts' d')
    simp only [hw]
    simp only [Result.ofOption, Result.bind_ok, S.known]
    obtain ⟨hsome, hnone⟩ := asCtor_rel (K := A.known) hvw
    cases hac : v.asCtor A.known with
    | none => simp only [hnone hac]; exact Corr.stuck _
    | some cf =>
      obtain ⟨c, vs⟩ := cf
      obtain ⟨ws, hws, hvws⟩ := hsome c vs hac
      simp only [hws]
      exact step_alts g alts d ρ J y st₁ st₂ st' alts' d' cs ρa ρf₁ Ja Jf c vs w ws has hd
        (fun x hx => by have := hρ x hx; exact Nat.lt_of_lt_of_le this g₀.1) hy (fun j hj => by
          have := hJ j hj; exact Nat.lt_of_lt_of_le this g₀.2) hs henv₁ hjr hw
        (by rw [S.known]; exact hws) hvws (fun info hi => asCtor_arity S.pins hvw hac hi)
  | .ret a0 =>
    obtain ⟨arg, harg, rfl, rfl⟩ := exp_ret hlow
    rw [Anf.eval_ret']
    cases hv : a0.eval ρa with
    | none => exact Corr.stuck _
    | some v =>
      obtain ⟨w, hw, hvw⟩ := atom_rel henv harg (fun i hi => by simpa [Anf.Exp.occ] using hi) hv
      exact Corr.okv hvw (by rw [eval_ret, hw]; rfl)
  | .tick e' =>
    have hlow' := exp_tick hlow
    have hD : (TickBound.exp cs (.tick e')).1 = (TickBound.exp cs e').1 + 1 := rfl
    have hs' : (TickBound.exp cs e').2 < N := hs
    rw [hD, Anf.eval_tick]
    exact Corr.tick (eval_mono F _ _ _) fun a' ha =>
      ih a' (by fir_omega) g e' ρ J st c st' cs ρa ρf Ja Jf hlow' hρ hJ hs' henv hjr
  | .trap =>
    obtain ⟨rfl, rfl⟩ := exp_trap hlow
    rw [Anf.eval_trap']
    exact Corr.trapv (eval_trap F a ρf Jf)
termination_by sizeOf e
decreasing_by all_goals simp_wf <;> fir_omega

theorem step_alts (g : Anf.GlobalId) (alts : List Anf.Alt) (d : Option Anf.Exp) (ρ : List Var)
    (J : List JoinId) (y : Var) (st₁ st₂ st' : St) (alts' : List Alt) (d' : Option Code) (cs : List Nat)
    (ρa : List Anf.Val) (ρf : Env) (Ja : List Anf.JClo) (Jf : List JEntry) (c : Key.CtorKey)
    (vs : List Anf.Val) (wv : Val) (ws : List Val)
    (has : exps A g ρ J y st₁ alts = .ok (alts', st₂)) (hd : opt A g ρ J st₂ d = .ok (d', st'))
    (hρ : ∀ x ∈ ρ, x < st₁.vars) (hy : y < st₁.vars) (hJ : ∀ j ∈ J, j < st₁.joins)
    (hs : (TickBound.maxPair (TickBound.alts' cs alts) (TickBound.opt cs d)).2 < N)
    (henv : EnvR A (fun i => 0 < Anf.Exp.altsOcc i alts + Anf.Exp.optOcc i d) ρ ρa ρf)
    (hjr : JRel A N g J cs Ja Jf) (hwv : ρf.get? y = some wv) (hac : wv.asCtor F.known = some (c, ws))
    (hvws : VRs A vs ws) (har : ∀ info, CtorInfo.ofKey A.ctors c = some info → vs.length = info.arity) :
    Corr A N a (TickBound.maxPair (TickBound.alts' cs alts) (TickBound.opt cs d)).1
      (Anf.evalAlts A a ρa Ja c vs alts d) (fun k => evalAlts F k ρf Jf c alts' d') := by
  match alts, d with
  | [], none =>
    obtain ⟨rfl, hst⟩ := exps_nil has
    rw [Anf.evalAlts_nil]
    exact Corr.stuck _
  | [], some e =>
    obtain ⟨rfl, hst⟩ := exps_nil has
    rw [hst] at hd
    rw [Anf.evalAlts_nil]
    obtain ⟨ce, hce, rfl⟩ := opt_some hd
    have hDs : TickBound.maxPair (TickBound.alts' cs []) (TickBound.opt cs (some e)) =
        (max 0 (TickBound.exp cs e).1, max 0 (TickBound.exp cs e).2) := rfl
    rw [hDs] at hs ⊢
    refine (step_exp g e ρ J st₁ ce st' cs ρa ρf Ja Jf hce hρ hJ (by fir_omega)
      (henv.mono fun i hi => by simp only [Anf.Exp.altsOcc, Anf.Exp.optOcc]; fir_omega) hjr).weaken
      (by fir_omega) |>.congr fun k => ?_
    rw [evalAlts_nil]
  | .mk key n body :: rest, d =>
    obtain ⟨hn, b, st₃, rest', hb, hr, rfl⟩ := exps_cons has
    have g₃ := exp_grows hb
    have hfv := St.freshN_vars st₁ n
    have hfj := St.freshN_joins st₁ n
    have hDs : TickBound.maxPair (TickBound.alts' cs (.mk key n body :: rest)) (TickBound.opt cs d) =
        TickBound.maxPair (TickBound.maxPair (TickBound.exp cs body) (TickBound.alts' cs rest))
          (TickBound.opt cs d) := rfl
    rw [hDs] at hs ⊢
    simp only [TickBound.maxPair] at hs ⊢
    rw [Anf.evalAlts_cons]
    by_cases hkc : key = c
    · subst hkc
      obtain ⟨info, hi, hia⟩ : ∃ info, CtorInfo.ofKey A.ctors key = some info ∧ info.arity = n := by
        cases hk : CtorInfo.ofKey A.ctors key with
        | none => rw [hk] at hn; cases hn
        | some info => rw [hk] at hn; exact ⟨info, rfl, by simpa using hn⟩
      have hvl : vs.length = n := by rw [har info hi, hia]
      simp only [hvl, and_self, ↓reduceIte]
      obtain ⟨ρf', hrun, hkeep, hset⟩ := projections_run F (body := body) hac Jf b (List.range' st₁.vars n) 0 ρf
        hwv (by intro hm; simp only [List.mem_range'] at hm; fir_omega) List.nodup_range' (by rw [← hvws.length]; simp [hvl])
      refine (step_exp g body _ J _ b st₃ cs (vs.reverse ++ ρa) ρf' Ja Jf hb (fun x hx => ?_)
        (fun j hj => by simpa using hJ j hj) (by fir_omega) ?_ hjr).weaken ?_ |>.congr fun k => ?_
      · rcases List.mem_append.1 hx with hx | hx
        · simp at hx; simp; fir_omega
        · have := hρ x hx; simp; fir_omega
      · refine EnvR.arm (n := n) (henv.mono fun i hi => by
            simp only [Anf.Exp.altsOcc]; fir_omega) (fun x hx hxr => ?_) (by simp) hvws hvl
          hkeep fun j x hj hl => ?_
        · have := hρ x hxr; simp at hx; fir_omega
        · rw [hset j x hj (by simpa using hl)]
          simp
      · fir_omega
      · simp only [evalAlts_cons, ↓reduceIte, hrun]
    · simp only [show (key = c ∧ n = vs.length) = False from eq_false (fun h => hkc h.1), ↓reduceIte]
      refine (step_alts g rest d ρ J y st₃ st₂ st' rest' d' cs ρa ρf Ja Jf c vs wv ws hr hd
        (fun x hx => by have := hρ x hx; have := g₃.1; fir_omega) (by have := g₃.1; fir_omega)
        (fun j hj => by have := hJ j hj; have := g₃.2; fir_omega) (by simp only [TickBound.maxPair] at hs ⊢; fir_omega)
        (henv.mono fun i hi => by simp only [Anf.Exp.altsOcc] at hi ⊢; fir_omega) hjr hwv hac
        hvws har).weaken (by simp [TickBound.maxPair]; fir_omega) |>.congr fun k => ?_
      simp only [evalAlts_cons, hkc, ↓reduceIte]
termination_by sizeOf alts + sizeOf d
decreasing_by all_goals simp_wf <;> fir_omega

end

end

/-- **The simulation at every clock.** -/
theorem stmt {A : Anf.Program} {F : Program} {N : Nat} (S : Setting A F N) : ∀ a, Stmt A F N a := by
  intro a
  induction a using Nat.strongRecOn with
  | _ a ih => exact fun g e ρ J st c st' cs ρa ρf Ja Jf =>
      step_exp S ih g e ρ J st c st' cs ρa ρf Ja Jf

end IxCC.Fir.Proof
