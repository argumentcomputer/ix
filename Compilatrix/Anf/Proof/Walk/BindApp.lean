import Compilatrix.Anf.Proof.Walk.BindCall

/-! # The rewriting walk: applications

One fuel level of the walk's simulation for `app` bindings: β-reduction of
a local function inlined at its single application (exact, over-applied:
the result applied to the rest, under-applied: a `walkc` closure of the
remaining parameters), known calls (an application of a function global's
closure or partial application becomes a call; over-saturated, a call then
an application of the rest; a dead partial application becomes a tick), and
kept applications (with the partial-application fact) (M2.3). -/

set_option autoImplicit false

namespace Compilatrix.Anf.WalkProof

open Compilatrix.Sem (Result ClockMono SimUpTo later later_succ later_zero)
open Compilatrix.Anf.Rel (Pw)
open Walk (Ent JEnt Fact Here Cfg Kont Fires)

theorem entsOf_rev_get (L : List Opd) {p : Nat} (hp : p < L.length) :
    (Walk.entsOf L.reverse)[L.length - 1 - p]? = (L[p]?).map Ent.opd := by
  simp only [Walk.entsOf, List.getElem?_map]
  rw [List.getElem?_reverse (by omega)]
  congr 2; omega

/-- Applying a closure without arguments to at least as many arguments as
it takes: its body one clock down, then the result applied to the rest. -/
theorem applyN_enter {P : Program} {k n : Nat} {ρ : List Val} {b : Exp} {vs : List Val} (hn : 0 < n)
    (hl : n ≤ vs.length) :
    applyN P k (.clos ρ n b []) vs =
      later k fun k' => (eval P k' ((vs.take n).reverse ++ ρ) [] b).bind fun r => applyN P (k' + 1) r (vs.drop n) := by
  cases vs with
  | nil => simp at hl; omega
  | cons v rest =>
    rw [applyN_clos]
    have h1 : ¬ (0 + (v :: rest).length < n) := by simp at hl ⊢; omega
    simp only [List.length_nil, hn, if_true, List.nil_append, enter]
    simp only [h1, if_false]

variable {P Q : Program} {Valid : Cfg → List Val → Prop} {Xc : Nat → List Val → Exp → Exp → Prop} {n fuel : Nat}

/-- An application of a known function global's closure or partial
application: a call when saturated (over-saturated: a call, then the rest
applied), a tick when dead and unsaturated, else kept with the
partial-application fact. -/
theorem app_known (hctx : Ctx P Q Valid Xc n) (hW : WalkAt P Q Valid Xc n fuel) {C : Cfg} {env : Walk.Env}
    {here : Here} {c : Ixon.V3.LetContract} {f : Atom} {as : List Atom} {body : Exp} {k : Kont}
    {ρ : List Val} {J : List JClo} {ρ' : List Val} {J' : List JClo} {live jlive : List Bool}
    {SK : Val → Nat → Result Val} (hV : Valid C ρ') (henv : WEnv Q Valid Xc live env.σ ρ ρ')
    (hJ : JEnv P Q Valid Xc n (KT Q k J') ρ' J' jlive env.jσ J) (hd : here.d = ρ'.length)
    (hdj : here.dj = J'.length) (hf : FactsOk Q Valid here.facts ρ') (hnd : NoDead live jlive (.bind c (.app f as) body))
    (hk : KontW Q Valid Xc n k SK ρ' J') {os : List Opd} {vs ws : List Val} (hws : os.mapM (·.val ρ') = some ws)
    (hvws : WVs Q Valid Xc vs ws) {x w : Val} (hxw : WV Q Valid Xc x w)
    (hsrc : ∀ k, evalBind P k ρ (.app f as) = applyN P k x vs) {fo : Opd} (hw : fo.val ρ' = some w)
    {g : GlobalId} {as0 : List Opd} (hkh : Walk.knownHead here fo = some (g, as0))
    {out : Exp} {s0 s0' : Fires}
    (h : (if ((as0 ++ os).length == (C.prog.arity? g).getD 0) = true then do
          Walk.fire fun f => { f with knownCall := f.knownCall + 1 }
          let e ← Walk.walk C fuel { σ := .opd (.lvl here.d) :: env.σ, jσ := env.jσ }
            { d := here.d + 1, dj := here.dj, facts := here.facts } body k
          pure (Exp.bind c (.call g (Walk.atoms here.d (as0 ++ os))) e)
        else if (as0 ++ os).length > (C.prog.arity? g).getD 0 then do
          Walk.fire fun f => { f with knownCall := f.knownCall + 1 }
          let e ← Walk.walk C fuel { σ := .opd (.lvl (here.d + 1)) :: env.σ, jσ := env.jσ }
            { d := here.d + 2, dj := here.dj, facts := here.facts } body k
          pure (Exp.bind freshLet
            (.call g (Walk.atoms here.d (List.take ((C.prog.arity? g).getD 0) (as0 ++ os))))
            (Exp.bind c (.app (.var 0)
              (Walk.atoms (here.d + 1) (List.drop ((C.prog.arity? g).getD 0) (as0 ++ os)))) e))
        else if (C.shrink && Exp.occ 0 body == 0) = true then do
          Walk.fire fun f => { f with deadPap := f.deadPap + 1 }
          let e ← Walk.walk C fuel { σ := .opd .box :: env.σ, jσ := env.jσ } here body k
          pure e.tick
        else do
          let e ← Walk.walk C fuel { σ := .opd (.lvl here.d) :: env.σ, jσ := env.jσ }
            { d := here.d + 1, dj := here.dj, facts := here.facts.insert here.d (.pap g (as0 ++ os)) } body k
          pure (Exp.bind c (.app (fo.atom here.d) (Walk.atoms here.d os)) e)).run s0 = .ok (out, s0')) :
    SimUpTo (WV Q Valid Xc) n (fun k => (eval P k ρ J (.bind c (.app f as) body)).bind (SK · k))
      (fun k => eval Q k ρ' J' out) := by
  obtain ⟨gd, ws0, hgQ, hws0, harity, hlt, rfl⟩ := knownHead_sound hf hkh hw
  have hN : (C.prog.arity? g).getD 0 = gd.ps.length := by rw [harity C ρ' hV]; rfl
  rw [hN] at h
  have hall : (as0 ++ os).mapM (·.val ρ') = some (ws0 ++ ws) := mapM_append hws0 hws
  have hl0 := mapM_length hws0
  have hl1 := mapM_length hws
  have happ := hctx.app hxw (pw_of hvws)
  split at h
  · -- saturated: a call
    next heq =>
    have heq' : ws0.length + ws.length = gd.ps.length := by
      simp only [List.length_append, beq_iff_eq] at heq; omega
    obtain ⟨e, s2, h3, h4⟩ := Walk.run_bind_ok (run_fire_then h)
    obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h4
    refine emit_sim hctx hW h3 hV henv hJ hd hdj hnd hk ?_
    refine (happ.strengthen (S := fun w => FactsOk Q Valid here.facts (w :: ρ')) fun _ w _ => hf.push w).congr
      hsrc (fun k => ?_)
    rw [applyN_exact_call (by omega) heq' rfl rfl, evalBind_call, hgQ, hd, Walk.atoms, opds_eval hall]; rfl
  · split at h
    · -- over-saturated: a call, then the rest applied
      next hneq hgt =>
      have hgt' : gd.ps.length < ws0.length + ws.length := by simp at hgt; omega
      obtain ⟨e, s2, h3, h4⟩ := Walk.run_bind_ok (run_fire_then h)
      obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h4
      let T : Nat → Result (Val × Val) := fun k =>
        (callVal Q k gd ((ws0 ++ ws).take gd.ps.length)).bind fun r =>
          (applyN Q k r ((ws0 ++ ws).drop gd.ps.length)).map fun u => (r, u)
      have hT : ∀ k, applyN Q k (.clos [] gd.ps.length gd.body ws0) ws = (T k).map Prod.snd := by
        intro k
        rw [applyN_over_call (by omega) hgt' rfl rfl]
        simp only [T, Result.map, Sem.Result.bind_assoc]
        congr 1; funext r
        cases applyN Q k r ((ws0 ++ ws).drop gd.ps.length) <;> rfl
      have hTm : ClockMono T := ClockMono.bind (callVal_mono Q gd _) fun r => clockMono_map (applyN_mono Q r _)
      have hsim := happ.unmap hT
      refine (SimUpTo.bind (d := fun v k => (eval P k (v :: ρ) J body).bind (SK · k))
        (d' := fun p k => eval Q k (p.2 :: p.1 :: ρ') J' e) hTm (fun p => eval_mono Q _ J' e) hsim
        fun v p hvp => ?_).congr (fun k => ?_) (fun k => ?_)
      · have hsuf : ρ' <:+ p.2 :: p.1 :: ρ' := (List.suffix_cons _ _).trans (List.suffix_cons _ _)
        have hval : (Opd.lvl (here.d + 1)).val (p.2 :: p.1 :: ρ') = some p.2 := by
          simp [Opd.val, hd]
        exact hW.walk h3 (v :: ρ) J (p.2 :: p.1 :: ρ') J' (true :: live) jlive SK (hctx.suffix C ρ' _ hV hsuf)
          (.live (.opd hval hvp) (henv.suffix hsuf)) (hJ.suffixK hsuf (List.suffix_refl _)) (by simp [hd])
          hdj (hf.suffix hsuf) (hnd.bind_body true fun e => nomatch e) (hk.suffix hsuf (List.suffix_refl _))
      · rw [eval_bind, hsrc, bind_assoc']
      · rw [eval_bind, evalBind_call, hgQ, hd, Walk.atoms, opds_eval (mapM_take hall _)]
        simp only [Result.ofOption, Result.bind_ok, T, Result.map, Sem.Result.bind_assoc]
        congr 1; funext r
        rw [eval_bind, evalBind_app]
        have hdrop : ((as0 ++ os).drop gd.ps.length).mapM (·.val (r :: ρ')) = some ((ws0 ++ ws).drop gd.ps.length) :=
          opds_suffix (List.suffix_cons _ _) (mapM_drop hall _)
        have hlen : ρ'.length + 1 = (r :: ρ').length := rfl
        rw [hlen, Walk.atoms, opds_eval hdrop]
        simp only [Atom.eval, List.getElem?_cons_zero, Result.ofOption, Result.bind_ok]
    · split at h
      · -- a dead partial application: a tick
        next hneq hngt hc =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        have hlt' : ws0.length + ws.length < gd.ps.length := by
          simp only [List.length_append, beq_iff_eq] at hneq hngt; omega
        obtain ⟨e, s2, h3, h4⟩ := Walk.run_bind_ok (run_fire_then h)
        obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h4
        obtain ⟨ρx, nx, bx, gotx, rfl, hgx, hnx⟩ := WV.clos_inv hxw hlt
        have hvl : vs.length = ws.length := hvws.length.symm
        by_cases hv : vs = []
        · subst hv
          exact skip_tick_sim hW h3 hV henv hJ hd hdj hf hnd hk
            (.inr fun k => by rw [hsrc, applyN_nil']) (.inr ⟨rfl, hc.2⟩)
        · exact skip_tick_sim hW h3 hV henv hJ hd hdj hf hnd hk
            (.inl fun k => by rw [hsrc, applyN_under (by omega) hv]) (.inr ⟨rfl, hc.2⟩)
      · -- kept, with the partial-application fact
        next hneq hngt hc =>
        have hlt' : ws0.length + ws.length < gd.ps.length := by
          simp only [List.length_append, beq_iff_eq] at hneq hngt; omega
        obtain ⟨e, s2, h3, h4⟩ := Walk.run_bind_ok h
        obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h4
        refine emit_sim hctx hW h3 hV henv hJ hd hdj hnd hk ?_
        have htgt : ∀ k, evalBind Q k ρ' (.app (fo.atom here.d) (Walk.atoms here.d os)) =
            applyN Q k (.clos [] gd.ps.length gd.body ws0) ws := by
          intro k
          rw [evalBind_app, hd, Opd.val_atom hw, Walk.atoms, opds_eval hws]; rfl
        refine (happ.strengthen (S := fun u => FactsOk Q Valid (here.facts.insert here.d (.pap g (as0 ++ os)))
          (u :: ρ')) fun k u hu => hf.insert' hd ?_).congr hsrc (fun k => htgt k)
        have hu' : u = .clos [] gd.ps.length gd.body (ws0 ++ ws) := by
          by_cases hv : ws = []
          · subst hv; rw [applyN_nil'] at hu; cases hu; simp
          · rw [applyN_under (by omega) hv] at hu
            cases k with
            | zero => cases hu
            | succ k => cases hu; rfl
        subst hu'
        exact ⟨gd, ws0 ++ ws, hgQ, opds_suffix (List.suffix_cons _ _) hall, harity, by simpa using hlt',
          lvl_top hd _⟩

end Compilatrix.Anf.WalkProof
