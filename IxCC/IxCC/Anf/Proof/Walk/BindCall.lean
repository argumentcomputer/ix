import IxCC.Anf.Proof.Walk.BindPrim

/-! # The rewriting walk: globals and calls

One fuel level of the walk's simulation for `glob` bindings (a CAF inlined
behind a tick for its charge, a CAF or function global kept, a dead
function global's closure dropped) and `call` bindings (redirected to a
specialisation, inlined behind a tick, or kept) (M2.3). -/

set_option autoImplicit false

namespace IxCC.Anf.WalkProof

open IxCC.Sem (Result ClockMono SimUpTo later later_succ later_zero)
open IxCC.Anf.Rel (Pw)
open Walk (Ent JEnt Fact Here Cfg Kont Fires)

variable {P Q : Program} {Valid : Cfg → List Val → List Val → List (Val × Val) → Prop} {Xc : Nat → List Val → Exp → Exp → Prop} {C : Cfg} {n fuel : Nat}

/-- A walk configuration's global has a source global of the same arity,
and a target one. -/
theorem Ctx.globals (hctx : Ctx P Q Valid Xc n) {C : Cfg} {ρ ρ' : List Val} (hV : VOk Q Valid Xc C ρ ρ') {g : GlobalId}
    {gd : GDef} (hgd : C.prog.global? g = some gd) :
    ∃ gdP gdQ, P.global? g = some gdP ∧ gdP.ps.length = gd.ps.length ∧ Q.global? g = some gdQ ∧
      gdQ.ps.length = gd.ps.length := by
  have hcg := hctx.vglob hV g
  rw [hgd] at hcg
  cases hP : P.global? g with
  | none => rw [hP] at hcg; cases hcg
  | some gdP =>
    rw [hP] at hcg
    simp only [Option.map_some, Option.some.injEq] at hcg
    obtain ⟨gdQ, hQ, hlen⟩ := hctx.arity g gdP hP
    exact ⟨gdP, gdQ, rfl, hcg.symm, hQ, by rw [hlen, ← hcg]⟩

/-- Every valid configuration reads a global's arity as the target's. -/
theorem Ctx.arity_of (hctx : Ctx P Q Valid Xc n) {g : GlobalId} {gdP gdQ : GDef} (hP : P.global? g = some gdP)
    (hlen : gdQ.ps.length = gdP.ps.length) :
    ∀ C ρ ρ' prs, Valid C ρ ρ' prs → C.prog.arity? g = some gdQ.ps.length := by
  intro C ρ ρ' prs hV
  have hcg := hctx.cglob C ρ ρ' prs hV g
  rw [hP] at hcg
  unfold Program.arity?
  cases hC : C.prog.global? g with
  | none => rw [hC] at hcg; cases hcg
  | some gdC =>
    rw [hC] at hcg
    simp only [Option.map_some, Option.some.injEq] at hcg
    simp [GDef.arity, hcg, hlen]

theorem walkBind_glob (hctx : Ctx P Q Valid Xc n) (hW : WalkAt P Q Valid Xc n fuel) {C : Cfg} {env : Walk.Env}
    {here : Here} {c : Ixon.V3.LetContract} {g : GlobalId} {body : Exp} {k : Kont} {out : Exp} {s s' : Fires}
    (h : (Walk.walkBind C (fuel + 1) env here c (.glob g) body k).run s = .ok (out, s')) :
    ExpSim P Q Valid Xc n C out env here k (.bind c (.glob g) body) := by
  intro ρ J ρ' J' live jlive SK hV henv hJ hd hdj hf hnd hk
  rw [Walk.walkBind] at h
  dsimp only at h
  split at h
  · next gd hgd =>
    obtain ⟨gdP, gdQ, hP, hlenP, hQ, hlenQ⟩ := hctx.globals hV hgd
    have hsrc : ∀ k, evalBind P k ρ (.glob g) = globVal P k gdP := fun k => by
      rw [evalBind_glob, hP]; rfl
    have hemit : ∀ {e : Exp} {s0 s0' : Fires} {facts' : Src.NatMap Fact},
        (Walk.walk C fuel { σ := .opd (.lvl here.d) :: env.σ, jσ := env.jσ }
          { d := here.d + 1, dj := here.dj, facts := facts', lvl := here.lvl } body k).run s0 = .ok (e, s0') →
        (∀ k w, evalBind Q k ρ' (.glob g) = .ok w → FactsOk Q Valid facts' (w :: ρ')) →
        SimUpTo (WV Q Valid Xc) n (fun k => (eval P k ρ J (.bind c (.glob g) body)).bind (SK · k))
          (fun k => eval Q k ρ' J' (.bind c (.glob g) e)) := by
      intro e s0 s0' facts' he hfacts
      exact emit_sim hctx hW he hV henv hJ hd hdj hnd hk
        ((Rel.compat_glob structural.toBase hctx.glob ρ ρ' g).strengthen hfacts)
    split at h
    · next hps =>
      have hpsP : gdP.ps = [] := List.eq_nil_of_length_eq_zero (by rw [hlenP, hps]; rfl)
      split at h
      · -- a CAF inlined
        next hin =>
        have hgdP : gd = gdP := by
          have := hctx.vbody hV g hin
          rw [hgd, hP] at this; exact Option.some.inj this
        subst hgdP
        have h' := run_fire_then h
        obtain ⟨k', s2, h2, h3⟩ := Walk.run_bind_ok h'
        obtain ⟨o, s3, h4, h5⟩ := Walk.run_bind_ok h3
        obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h5
        have hk' := hW.after h2 ρ J ρ' J' live jlive SK hV henv hJ (hnd.bind_body true fun e => nomatch e) hk
        have hin' := hW.walk h4 [] [] ρ' J' [] [] _ (hctx.vinl [] hV) .nil .nil hd hdj hf
          ⟨fun i hi => by simp at hi, fun j hj => by simp at hj⟩ hk'
        refine (SimUpTo.tick (eval_mono P [] [] gd.body) (eval_mono Q ρ' J' o) hin').congr
          (fun k => ?_) (fun k => eval_tick Q k ρ' J' o)
        rw [eval_bind, hsrc, bind_assoc']
        unfold globVal
        rw [hpsP]
      · -- a CAF kept
        obtain ⟨e, s2, h3, h4⟩ := Walk.run_bind_ok h
        obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h4
        exact hemit h3 fun _ w _ => hf.push w
    · -- a function global
      next hd0 tl hps =>
      have hpsP : gdP.ps ≠ [] := by
        intro he; rw [he, hps] at hlenP; simp at hlenP
      have hpsQ : gdQ.ps ≠ [] := by
        intro he; rw [he, hps] at hlenQ; simp at hlenQ
      have hval : ∀ k, evalBind P k ρ (.glob g) = .ok (.clos [] gdP.ps.length gdP.body []) := by
        intro k; rw [hsrc]; unfold globVal
        cases hp : gdP.ps with
        | nil => exact absurd hp hpsP
        | cons _ _ => rfl
      split at h
      · next hc =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        exact skip_sim hW (run_fire_then h) (hctx.push hV) henv hJ hd hdj hf hnd hk
          (.inr ⟨_, hval, .inr ⟨rfl, hc.2⟩⟩)
      · obtain ⟨e, s2, h3, h4⟩ := Walk.run_bind_ok h
        obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h4
        refine hemit h3 fun k w hw => hf.insert' hd ?_
        rw [evalBind_glob, hQ] at hw
        simp only [Result.ofOption, Result.bind_ok] at hw
        unfold globVal at hw
        cases hp : gdQ.ps with
        | nil => exact absurd hp hpsQ
        | cons _ _ =>
          rw [hp] at hw
          cases hw
          refine ⟨gdQ, hQ, hpsQ, hctx.arity_of hP (by rw [hlenQ, hlenP]), ?_⟩
          rw [lvl_top hd, hp]
  · exact absurd h (fun h => Walk.run_throw_ok h)

theorem walkBind_call (hctx : Ctx P Q Valid Xc n) (hW : WalkAt P Q Valid Xc n fuel) {C : Cfg} {env : Walk.Env}
    {here : Here} {c : Ixon.V3.LetContract} {g : GlobalId} {as : List Atom} {body : Exp} {k : Kont}
    {out : Exp} {s s' : Fires}
    (h : (Walk.walkBind C (fuel + 1) env here c (.call g as) body k).run s = .ok (out, s')) :
    ExpSim P Q Valid Xc n C out env here k (.bind c (.call g as) body) := by
  intro ρ J ρ' J' live jlive SK hV henv hJ hd hdj hf hnd hk
  rw [Walk.walkBind] at h
  dsimp only at h
  obtain ⟨os, s1, h1, h2⟩ := Walk.run_bind_ok h
  try dsimp only at h2
  obtain ⟨rfl, vs, ws, hvs, hws, hvws⟩ := resolveList_rel' henv h1 fun i hi => by
    simpa [Bind.occ] using hnd.bind_rhs i hi
  have hsrc : ∀ k, evalBind P k ρ (.call g as) =
      (Result.ofOption (P.global? g)).bind (callVal P k · vs) := fun k => by
    rw [evalBind_call, hvs]; rfl
  split at h2
  · -- redirected
    next sp os' hred =>
    obtain ⟨r, hr, hr'⟩ := Option.bind_eq_some_iff.1 hred
    split at hr'
    · next hg =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hg
      obtain ⟨hg', hfix⟩ := hg
      rw [henv.length.1] at hfix
      subst hg'
      obtain ⟨os'', hargs, he⟩ := Option.map_eq_some_iff.1 hr'
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have h2' := run_fire_then h2
      obtain ⟨e, s2, h3, h4⟩ := Walk.run_bind_ok h2'
      obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h4
      obtain ⟨ws', hws', hsim⟩ := hctx.red C ρ ρ' r hV hr as os os'' vs ws hfix hargs hvs hws hvws
      refine emit_sim hctx hW h3 hV henv hJ hd hdj hnd hk ?_
      refine (hsim.strengthen (S := fun w => FactsOk Q Valid here.facts (w :: ρ')) fun _ w _ => hf.push w).congr
        hsrc (fun k => ?_)
      rw [evalBind_call, hd, Walk.atoms, opds_eval hws']; rfl
    · cases hr'
  · split at h2
    · next gd hgd =>
      obtain ⟨gdP, gdQ, hP, hlenP, hQ, hlenQ⟩ := hctx.globals hV hgd
      split at h2
      · -- inlined
        next hc =>
        simp only [Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq] at hc
        have hgdP : gd = gdP := by
          have := hctx.vbody hV g (by simp [hc.1])
          rw [hgd, hP] at this; exact Option.some.inj this
        subst hgdP
        have hvl : vs.length = gd.ps.length := by rw [← hvws.length, mapM_length hws, hc.2]
        have h' := run_fire_then h2
        obtain ⟨k', s2, h3, h4⟩ := Walk.run_bind_ok h'
        obtain ⟨o, s3, h5, h6⟩ := Walk.run_bind_ok h4
        obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h6
        have hk' := hW.after h3 ρ J ρ' J' live jlive SK hV henv hJ (hnd.bind_body true fun e => nomatch e) hk
        have henvb := WEnv.pushOpds (mapM_reverse hws) hvws.reverse (WEnv.nil (Q := Q) (Valid := Valid) (Xc := Xc) (C := { C with inline := [], redirect := none }) (ρ' := ρ'))
        simp only [List.append_nil, List.length_reverse] at henvb
        have hin' := hW.walk h5 vs.reverse [] ρ' J' _ [] _ (hctx.vinl vs.reverse hV) henvb .nil hd hdj hf
          ⟨fun i hi => by simp [List.getElem?_replicate] at hi, fun j hj => by simp at hj⟩ hk'
        refine (SimUpTo.tick (eval_mono P vs.reverse [] gd.body) (eval_mono Q ρ' J' o) hin').congr
          (fun k => ?_) (fun k => eval_tick Q k ρ' J' o)
        rw [eval_bind, hsrc, bind_assoc', hP]
        simp only [Result.ofOption, Result.bind_ok, callVal, hvl, if_true]
      · -- kept
        obtain ⟨e, s2, h3, h4⟩ := Walk.run_bind_ok h2
        obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h4
        refine emit_sim hctx hW h3 hV henv hJ hd hdj hnd hk ?_
        refine ((hctx.call g (pw_of hvws)).strengthen (S := fun w => FactsOk Q Valid here.facts (w :: ρ'))
          fun _ w _ => hf.push w).congr hsrc (fun k => ?_)
        rw [evalBind_call, hd, Walk.atoms, opds_eval hws]; rfl
    · exact absurd h2 (fun h => Walk.run_throw_ok h)

end IxCC.Anf.WalkProof
