import IxCC.Anf.Proof.Walk.BindApp

/-! # The rewriting walk: β-reduction and the `app` step

β-reduction of a local function inlined at its single application, and the
whole `app` case of the walk's simulation. -/

set_option autoImplicit false

namespace IxCC.Anf.WalkProof

open IxCC.Sem (Result ClockMono SimUpTo later later_succ later_zero)
open IxCC.Anf.Rel (Pw)
open Walk (Ent JEnt Fact Here Cfg Kont Fires)

theorem fieldOpds_get (d m : Nat) {q : Nat} (hq : q < m) : (Walk.fieldOpds d m)[q]? = some (.lvl (d + q)) := by
  simp [Walk.fieldOpds, hq]

variable {P Q : Program} {Valid : Cfg → List Val → List Val → List (Val × Val) → Prop} {Xc : Nat → List Val → Exp → Exp → Prop} {C : Cfg} {n fuel : Nat}

/-- The inlined body of an exactly or over-applied local function, behind
the application's charge. -/
theorem beta_tick (hW : WalkAt P Q Valid Xc n fuel) {C : Cfg} {here : Here} {σf : List Ent} {livef : List Bool}
    {ρf : List Val} {nf : Nat} {fb : Exp} {k' : Kont} {o : Exp} {s s' : Fires} {os : List Opd}
    (hrun : (Walk.walk C fuel { σ := Walk.entsOf (os.take nf).reverse ++ σf, jσ := [] } here fb k').run s =
      .ok (o, s'))
    {ρ : List Val} {J : List JClo} {ρ' : List Val} {J' : List JClo} {SK : Val → Nat → Result Val}
    {body : Exp} (henvf : WEnv Q Valid Xc C livef σf ρf ρ')
    (hndf : NoDead (List.replicate nf true ++ livef) [] fb) (hpos : 0 < nf) (hl : nf ≤ os.length)
    {vs ws : List Val} (hws : os.mapM (·.val ρ') = some ws) (hvws : WVs Q Valid Xc vs ws)
    (hV : VOk Q Valid Xc C ((vs.take nf).reverse ++ ρf) ρ')
    (hd : here.d = ρ'.length) (hdj : here.dj = J'.length) (hf : FactsOk Q Valid here.facts ρ')
    (hk' : KontW Q Valid Xc n k' (fun r k => (applyN P k r (vs.drop nf)).bind fun v =>
      (eval P k (v :: ρ) J body).bind (SK · k)) ρ' J') :
    SimUpTo (WV Q Valid Xc) n
      (fun k => (applyN P k (.clos ρf nf fb []) vs).bind fun v => (eval P k (v :: ρ) J body).bind (SK · k))
      (fun k => eval Q k ρ' J' (.tick o)) := by
  have hvl : vs.length = os.length := by rw [← hvws.length, mapM_length hws]
  have henvb := WEnv.pushOpds (mapM_reverse (mapM_take hws nf)) (hvws.take nf).reverse henvf
  have htl : (os.take nf).reverse.length = nf := by simp; omega
  rw [htl] at henvb
  have hin := hW.walk hrun ((vs.take nf).reverse ++ ρf) [] ρ' J' _ [] _ hV henvb .nil hd hdj hf hndf hk'
  refine (SimUpTo.tick (eval_mono P _ [] fb) (eval_mono Q ρ' J' o) hin).congr (fun k => ?_)
    (fun k => eval_tick Q k ρ' J' o)
  rw [applyN_enter hpos (by omega)]
  cases k with
  | zero => rfl
  | succ k => simp only [later_succ, Sem.Result.bind_assoc]

theorem walkBind_app (hctx : Ctx P Q Valid Xc n) (hW : WalkAt P Q Valid Xc n fuel) {C : Cfg} {env : Walk.Env}
    {here : Here} {c : Ixon.V3.LetContract} {f : Atom} {as : List Atom} {body : Exp} {k : Kont}
    {out : Exp} {s s' : Fires}
    (h : (Walk.walkBind C (fuel + 1) env here c (.app f as) body k).run s = .ok (out, s')) :
    ExpSim P Q Valid Xc n C out env here k (.bind c (.app f as) body) := by
  intro ρ J ρ' J' live jlive SK hV henv hJ hd hdj hf hnd hk
  rw [Walk.walkBind.eq_def] at h
  dsimp only at h
  obtain ⟨os, s1, h1, h2⟩ := Walk.run_bind_ok h
  have hocc := hnd.bind_rhs
  obtain ⟨rfl, vs, ws, hvs, hws, hvws⟩ := resolveList_rel' henv h1 fun i hi => by
    have := hocc i hi; simp only [Bind.occ] at this; omega
  have hvl : vs.length = os.length := by rw [← hvws.length, mapM_length hws]
  have hsrcf : ∀ {x : Val}, f.eval ρ = some x → ∀ k, evalBind P k ρ (.app f as) = applyN P k x vs := by
    intro x hx k; rw [evalBind_app, hx, hvs]; rfl
  have hcongr : ∀ {x : Val}, f.eval ρ = some x → ∀ k,
      (eval P k ρ J (.bind c (.app f as) body)).bind (SK · k) =
        (applyN P k x vs).bind fun v => (eval P k (v :: ρ) J body).bind (SK · k) := by
    intro x hx k; rw [eval_bind, hsrcf hx, bind_assoc']
  split at h2
  · -- a local function inlined at its application
    next σf nf fb hloc =>
    obtain ⟨i, rfl, hσi⟩ : ∃ i, f = .var i ∧ env.σ[i]? = some (.fn σf nf fb) := by
      cases f with
      | var i =>
        refine ⟨i, rfl, ?_⟩
        dsimp only at hloc
        split at hloc
        · next σf' n' fb' heq =>
          simp only [Option.some.injEq, Prod.mk.injEq] at hloc
          obtain ⟨rfl, rfl, rfl⟩ := hloc
          exact heq
        · cases hloc
      | lit l => cases hloc
      | box => cases hloc
    have hlen := henv.length
    have hli : live[i]? = some true :=
      atom_live (hlen.1.trans hlen.2.symm)
        (fun j hj => by have := hocc j hj; simp only [Bind.occ] at this; omega) i rfl
        (by rw [hσi]; simp)
    obtain ⟨xf, hxf, hent⟩ := henv.get hσi hli
    obtain ⟨ρf, livef, rfl, henvf, hndf, hpos, hvf⟩ : ∃ ρf livef, xf = .clos ρf nf fb [] ∧
        WEnv Q Valid Xc C livef σf ρf ρ' ∧ NoDead (List.replicate nf true ++ livef) [] fb ∧ 0 < nf ∧
        (∀ ρ'', ρ' <:+ ρ'' → VOk Q Valid Xc C ρf ρ'') := by
      cases hent with
      | fn henvf hndf hpos hvf => exact ⟨_, _, rfl, henvf, hndf, hpos, hvf⟩
    split at h2
    · -- exactly or over-applied
      next hge =>
      have h' := run_fire_then h2
      split at h'
      · next hemp =>
        obtain ⟨k', s2, h3, h4⟩ := Walk.run_bind_ok h'
        obtain ⟨o, s3, h5, h6⟩ := Walk.run_bind_ok h4
        obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h6
        have hk' := hW.after h3 ρ J ρ' J' live jlive SK hV henv hJ (hnd.bind_body true fun e => nomatch e) hk
        have hdrop : vs.drop nf = [] := by
          rw [List.drop_eq_nil_iff, hvl]
          rw [List.isEmpty_iff, List.drop_eq_nil_iff] at hemp
          exact hemp
        have hk'' : KontW Q Valid Xc n k' (fun r k => (applyN P k r (vs.drop nf)).bind fun v =>
            (eval P k (v :: ρ) J body).bind (SK · k)) ρ' J' := by
          have e : (fun r k => (applyN P k r (vs.drop nf)).bind fun v => (eval P k (v :: ρ) J body).bind (SK · k)) =
              (fun v k => (eval P k (v :: ρ) J body).bind (SK · k)) := by
            funext r k; rw [hdrop, applyN_nil']; rfl
          rw [e]; exact hk'
        exact (beta_tick hW h5 henvf hndf hpos hge hws hvws
          (hctx.vsuffix (hvf ρ' (List.suffix_refl _)) (List.suffix_append _ _) (List.suffix_refl _)) hd hdj hf hk'').congr (hcongr hxf)
          (fun _ => rfl)
      · next hemp =>
        obtain ⟨k', s2, h3, h4⟩ := Walk.run_bind_ok h'
        obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h3
        obtain ⟨o, s3, h5, h6⟩ := Walk.run_bind_ok h4
        obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h6
        refine (beta_tick hW h5 henvf hndf hpos hge hws hvws
          (hctx.vsuffix (hvf ρ' (List.suffix_refl _)) (List.suffix_append _ _) (List.suffix_refl _)) hd hdj hf ?_).congr (hcongr hxf)
          (fun _ => rfl)
        -- the over-application's meta-continuation
        intro here' o' e s4 s5 ρ'' J'' hF hρ hJ' hd' hdj' hf' x w' hw' hxw'
        obtain ⟨e0, s6, h7, h8⟩ := Walk.run_bind_ok hF
        obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h8
        have hrest : (os.drop nf).mapM (·.val ρ'') = some (ws.drop nf) := opds_suffix hρ (mapM_drop hws _)
        refine (SimUpTo.bind (evalBind_mono Q ρ'' _) (fun u => eval_mono Q (u :: ρ'') J'' e0)
          ((hctx.app hxw' (pw_of (hvws.drop nf))).congr (fun _ => rfl) (fun k => ?_)) fun v u hvu => ?_).congr
          (fun _ => rfl) (fun k => eval_bind Q k ρ'' J'' c _ e0)
        · rw [evalBind_app, hd', Opd.val_atom hw', Walk.atoms, opds_eval hrest]; rfl
        · have hsuf : ρ'' <:+ u :: ρ'' := List.suffix_cons _ _
          have hsuf' : ρ' <:+ u :: ρ'' := hρ.trans hsuf
          exact hW.walk h7 (v :: ρ) J (u :: ρ'') J'' (true :: live) jlive SK (hctx.vsuffix hV (List.suffix_cons _ _) hsuf')
            (.live (.opd (lvl_top hd' u) hvu) (henv.suffix hsuf')) (hJ.suffixK hsuf' hJ') (by simp [hd'])
            hdj' (hf'.push u) (hnd.bind_body true fun e => nomatch e) (hk.suffix hsuf' hJ')
    · -- under-applied: the rest of the function, its first parameters bound
      next hlt =>
      have hlt' : os.length < nf := by omega
      have h' := run_fire_then h2
      obtain ⟨fb', s2, h3, h4⟩ := Walk.run_bind_ok h'
      obtain ⟨e, s3, h5, h6⟩ := Walk.run_bind_ok h4
      obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h6
      have hm : 0 < nf - os.length := by omega
      rw [hd] at h3
      have hwv : WV Q Valid Xc (.clos ρf nf fb vs) (.clos ρ' (nf - os.length) fb' []) := by
        refine .walkc (σP := Walk.entsOf (os ++ Walk.fieldOpds ρ'.length (nf - os.length)).reverse)
          (got' := []) (oOf := fun p => (os[p]?).getD .box) (wOf := fun p => (ws[p]?).getD .box)
          (hvf ρ' (List.suffix_refl _)) h3 henvf hf hndf (by simp [Walk.entsOf, fieldOpds_length]; omega) (by omega) (by omega)
          (by omega) (by simp; omega) (fun p hp => ?_) (fun p v hp hv => ?_) (fun p hp1 hp2 => ?_)
          (fun p v w _ _ _ hw => by simp at hw)
        · have hpl : p < os.length := by omega
          have hL : (os ++ Walk.fieldOpds ρ'.length (nf - os.length)).length = nf := by
            simp [fieldOpds_length]; omega
          have := entsOf_rev_get (os ++ Walk.fieldOpds ρ'.length (nf - os.length)) (p := p) (by omega)
          rw [hL, List.getElem?_append_left hpl] at this
          refine ⟨?_, ?_⟩
          · rw [this, List.getElem?_eq_getElem hpl]; rfl
          · rw [List.getElem?_eq_getElem hpl, Option.getD_some, mapM_get hws p hpl,
              List.getElem?_eq_getElem (by rw [mapM_length hws]; exact hpl)]
            rfl
        · have hpl : p < ws.length := by rw [mapM_length hws]; omega
          rcases hvws.get p with ⟨h1, _⟩ | ⟨v1, w1, hv1, hw1, hvw1⟩
          · rw [h1] at hv; cases hv
          · rw [hv1] at hv; cases hv
            rw [hw1]; exact hvw1
        · have hL : (os ++ Walk.fieldOpds ρ'.length (nf - os.length)).length = nf := by
            simp [fieldOpds_length]; omega
          have := entsOf_rev_get (os ++ Walk.fieldOpds ρ'.length (nf - os.length)) (p := p) (by omega)
          rw [hL, List.getElem?_append_right (by omega), fieldOpds_get _ _ (by omega)] at this
          rw [this]
          simp; omega
      have hin : SimUpTo (WV Q Valid Xc) n (fun k => (eval P k (.clos ρf nf fb vs :: ρ) J body).bind (SK · k))
          (fun k => eval Q k ρ' J' (.bind c (.fn (List.replicate (nf - os.length) {}) fb') e)) := by
        have hsuf : ρ' <:+ Val.clos ρ' (nf - os.length) fb' [] :: ρ' := List.suffix_cons _ _
        refine (hW.walk h5 (.clos ρf nf fb vs :: ρ) J _ J' (true :: live) jlive SK (hctx.vsuffix hV (List.suffix_cons _ _) hsuf)
          (.live (.opd (lvl_top hd _) hwv) (henv.suffix hsuf)) (hJ.suffixK hsuf (List.suffix_refl _))
          (by simp [hd]) hdj (hf.push _) (hnd.bind_body true fun e => nomatch e)
          (hk.suffix hsuf (List.suffix_refl _))).congr (fun _ => rfl) (fun k => ?_)
        rw [eval_bind, evalBind_fn Q k ρ' _ fb' (by simp; omega)]
        simp
      by_cases hv : vs = []
      · subst hv
        refine (hin.laterR (eval_mono Q ρ' J' _)).congr (fun k => ?_) (fun k => eval_tick Q k ρ' J' _)
        rw [hcongr hxf, applyN_nil']; rfl
      · refine (SimUpTo.tick (c := fun _ => .ok (.clos ρf nf fb vs))
          (d := fun v k => (eval P k (v :: ρ) J body).bind (SK · k)) (fun _ _ _ _ => rfl)
          (eval_mono Q ρ' J' _) (hin.congr (fun _ => rfl) (fun _ => rfl))).congr (fun k => ?_)
          (fun k => eval_tick Q k ρ' J' _)
        rw [hcongr hxf, applyN_under (by simp; omega) hv]
        simp
  · -- the head's value
    next hloc =>
    obtain ⟨fo, s2, h3, h4⟩ := Walk.run_bind_ok h2
    obtain ⟨rfl, x, w, hx, hw, hxw⟩ := resolve_rel' henv h3 fun i hi => by
      have := hocc i hi; simp only [Bind.occ] at this; omega
    split at h4
    · next g as0 hkh =>
      have hkh' : Walk.knownHead here fo = some (g, as0) := by
        split at hkh
        · exact hkh
        · cases hkh
      exact app_known hctx hW hV henv hJ hd hdj hf hnd hk hws hvws hxw (hsrcf hx) hw hkh' h4
    · obtain ⟨e, s3, h5, h6⟩ := Walk.run_bind_ok h4
      obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h6
      refine emit_sim hctx hW h5 hV henv hJ hd hdj hnd hk ?_
      refine ((hctx.app hxw (pw_of hvws)).strengthen (S := fun w => FactsOk Q Valid here.facts (w :: ρ'))
        fun _ w _ => hf.push w).congr (hsrcf hx) (fun k => ?_)
      rw [evalBind_app, hd, Opd.val_atom hw, Walk.atoms, opds_eval hws]; rfl

end IxCC.Anf.WalkProof
