import Compilatrix.Anf.Proof.Walk.BindPure

/-! # The rewriting walk: primitives and local functions

One fuel level of the walk's simulation for primitive bindings (literal
folding to a literal or a `Bool` constructor, dead pure primitives, and kept
ones with the `y + 1` fact) and local function bindings (dead, inlined at
their single application, or walked under their parameters) (M2.3). -/

set_option autoImplicit false

namespace Compilatrix.Anf.WalkProof

open Compilatrix.Sem (Result ClockMono SimUpTo later later_succ later_zero)
open Compilatrix.Anf.Rel (Pw)
open Walk (Ent JEnt Fact Here Cfg Kont Fires)

variable {P Q : Program} {Valid : Cfg → List Val → List Val → Prop} {Xc : Nat → List Val → Exp → Exp → Prop} {C : Cfg} {n fuel : Nat}

theorem NoDead.fn_body {live : List Bool} {ps : List Ixon.V3.BinderContract} {fb : Exp}
    (h : ∀ i, live[i]? = some false → Bind.occ i (.fn ps fb) = 0) :
    NoDead (List.replicate ps.length true ++ live) [] fb := by
  refine ⟨fun i hi => ?_, fun j hj => by simp at hj⟩
  by_cases hlt : i < ps.length
  · rw [getElem?_replicate_lt true live hlt] at hi; cases hi
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + ps.length := ⟨i - ps.length, by omega⟩
    rw [getElem?_replicate_append] at hi
    simpa [Bind.occ] using h i' hi

theorem walkBind_prim (hctx : Ctx P Q Valid Xc n) (hW : WalkAt P Q Valid Xc n fuel) {C : Cfg} {env : Walk.Env}
    {here : Here} {c : Ixon.V3.LetContract} {p : Lam.Prim} {as : List Atom} {body : Exp} {k : Kont}
    {out : Exp} {s s' : Fires}
    (h : (Walk.walkBind C (fuel + 1) env here c (.prim p as) body k).run s = .ok (out, s')) :
    ExpSim P Q Valid Xc n C out env here k (.bind c (.prim p as) body) := by
  intro ρ J ρ' J' live jlive SK hV henv hJ hd hdj hf hnd hk
  rw [Walk.walkBind] at h
  dsimp only at h
  obtain ⟨os, s1, h1, h2⟩ := Walk.run_bind_ok h
  try dsimp only at h2
  obtain ⟨rfl, vs, ws, hvs, hws, hvws⟩ := resolveList_rel' henv h1 fun i hi => by
    simpa [Bind.occ] using hnd.bind_rhs i hi
  have hK : C.prog.known = P.known := hctx.cknown C ρ ρ' hV
  have hsrc : ∀ k, evalBind P k ρ (.prim p as) = primResult P.known p vs := fun k => by
    rw [evalBind_prim, hvs]; rfl
  have hnat : natArgs ws = natArgs vs := Rel.natArgs_rel structural.toBase (pw_of hvws)
  have htgt : ∀ k, evalBind Q k ρ' (.prim p (Walk.atoms here.d os)) = primResult P.known p vs := by
    intro k
    rw [evalBind_prim, hd, Walk.atoms, opds_eval hws]
    simp only [Result.ofOption, Result.bind_ok]
    rw [hctx.known]; unfold primResult; rw [hnat]
  have hdead : ∀ {e : Exp} {s0 s0' : Fires}, body.occ 0 = 0 →
      (Walk.walk C fuel { σ := .opd .box :: env.σ, jσ := env.jσ } here body k).run s0 = .ok (e, s0') →
      SimUpTo (WV Q Valid Xc) n (fun k => (eval P k ρ J (.bind c (.prim p as) body)).bind (SK · k))
        (fun k => eval Q k ρ' J' e) := by
    intro e s0 s0' hocc he
    refine skip_sim hW he (hctx.push hV) henv hJ hd hdj hf hnd hk ?_
    rcases primResult_cases P.known p vs with hst | ⟨u, hu, _⟩
    · exact .inl fun k => by rw [hsrc, hst]
    · exact .inr ⟨u, fun k => by rw [hsrc, hu], .inr ⟨rfl, hocc⟩⟩
  have hemit : ∀ {e : Exp} {s0 s0' : Fires} {facts' : Src.NatMap Fact},
      (Walk.walk C fuel { σ := .opd (.lvl here.d) :: env.σ, jσ := env.jσ }
        { d := here.d + 1, dj := here.dj, facts := facts' } body k).run s0 = .ok (e, s0') →
      (∀ u, primResult P.known p vs = .ok u → FactsOk Q Valid facts' (u :: ρ')) →
      SimUpTo (WV Q Valid Xc) n (fun k => (eval P k ρ J (.bind c (.prim p as) body)).bind (SK · k))
        (fun k => eval Q k ρ' J' (.bind c (.prim p (Walk.atoms here.d os)) e)) := by
    intro e s0 s0' facts' he hfacts
    refine emit_sim hctx hW he hV henv hJ hd hdj hnd hk ?_
    rcases primResult_cases P.known p vs with hst | ⟨u, hu, hlu⟩
    · exact (SimUpTo.stuck _).congr (fun k => by rw [hsrc, hst]) (fun _ => rfl)
    · exact (SimUpTo.ok ⟨WV.lit_or_con hlu, hfacts u hu⟩).congr (fun k => by rw [hsrc, hu])
        (fun k => by rw [htgt, hu])
  -- the fact `y + 1` about a kept `natAdd [y, 1]`
  have hsucc : ∀ (y : Opd) (u : Val), p = .natAdd → os = [y, .lit (.nat 1)] →
      primResult P.known p vs = .ok u → FactOk Q Valid (u :: ρ') here.d (.succ y) := by
    intro y u hp hos hu
    subst hp hos
    obtain ⟨wy, hwy, rfl⟩ : ∃ wy, y.val ρ' = some wy ∧ ws = [wy, .lit (.nat 1)] := by
      cases hy : y.val ρ' with
      | none => simp [List.mapM_cons, hy] at hws
      | some wy =>
        have h1 : (Opd.lit (.nat 1)).val ρ' = some (.lit (.nat 1)) := rfl
        exact ⟨wy, rfl, by simp [List.mapM_cons, hy, h1] at hws; exact hws.symm⟩
    obtain ⟨vy, v1, rfl, hvy, hv1⟩ : ∃ vy v1, vs = [vy, v1] ∧ WV Q Valid Xc vy wy ∧ WV Q Valid Xc v1 (.lit (.nat 1)) := by
      cases hvws with
      | cons h1 hrest => cases hrest with
        | cons h2 hrest2 => cases hrest2; exact ⟨_, _, rfl, h1, h2⟩
    cases hv1
    unfold primResult at hu
    cases vy with
    | lit l =>
      cases l with
      | nat m =>
        cases hvy
        simp only [natArgs, Option.map_some] at hu
        simp only [Lam.Prim.sem, Lam.Prim.sem.srcOp, Src.PrimOp.eval2] at hu
        cases hu
        exact ⟨m, lvl_top hd _, Opd.val_suffix (List.suffix_cons _ _) hwy⟩
      | str _ => simp [natArgs] at hu
    | clos => simp [natArgs] at hu
    | con => simp [natArgs] at hu
    | box => simp [natArgs] at hu
  have hsuccFacts : ∀ u, primResult P.known p vs = .ok u →
      FactsOk Q Valid (match (match p, os with
        | .natAdd, [y, .lit (.nat 1)] => some (Fact.succ y)
        | _, _ => none) with
        | some f => here.facts.insert here.d f
        | none => here.facts) (u :: ρ') := by
    intro u hu
    split
    · next f hf' =>
      split at hf'
      · next y =>
        simp only [Option.some.injEq] at hf'
        subst hf'
        exact hf.insert' hd (hsucc y u rfl rfl hu)
      · cases hf'
    · exact hf.push u
  split at h2
  · -- folded to a literal
    next m0 hfold =>
    split at hfold
    · unfold Walk.fold at hfold
      obtain ⟨ns, hlits, hsem⟩ := Option.bind_eq_some_iff.1 hfold
      have hna := fold_lits hlits hws
      rw [hnat] at hna
      refine skip_sim hW (run_fire_then h2) (hctx.push hV) henv hJ hd hdj hf hnd hk
        (.inr ⟨.lit (.nat m0), fun k => ?_, .inl (.opd rfl .lit)⟩)
      rw [hsrc]; unfold primResult; rw [hna]; dsimp only; rw [hsem]
    · cases hfold
  · -- folded to a `Bool`
    next bv hfold =>
    have hfold' : Walk.fold p os = some (.bool bv) := by
      split at hfold
      · exact hfold
      · cases hfold
    unfold Walk.fold at hfold'
    obtain ⟨ns, hlits, hsem⟩ := Option.bind_eq_some_iff.1 hfold'
    have hna := fold_lits hlits hws
    rw [hnat] at hna
    split at h2
    · next key hkey =>
      have hu : primResult P.known p vs = .ok (.con key []) := by
        unfold primResult; rw [hna]; dsimp only; rw [hsem]; dsimp only; rw [← hK, hkey]
      have h2' := run_fire_then h2
      split at h2'
      · next hc =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        exact skip_sim hW h2' (hctx.push hV) henv hJ hd hdj hf hnd hk
          (.inr ⟨_, fun k => by rw [hsrc, hu], .inr ⟨rfl, hc.2⟩⟩)
      · obtain ⟨e, s2, h3, h4⟩ := Walk.run_bind_ok h2'
        obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h4
        refine emit_sim hctx hW h3 hV henv hJ hd hdj hnd hk ?_
        refine (SimUpTo.ok ⟨.con .nil, hf.insert' hd ⟨_, [], lvl_top hd _, rfl, rfl⟩⟩).congr
          (fun k => by rw [hsrc, hu]) (fun k => ?_)
        rw [evalBind_con]; rfl
    · obtain ⟨e, s2, h3, h4⟩ := Walk.run_bind_ok h2
      obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h4
      exact hemit h3 hsuccFacts
  · -- not folded
    split at h2
    · next hc =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      exact hdead hc.2 (run_fire_then h2)
    · obtain ⟨e, s2, h3, h4⟩ := Walk.run_bind_ok h2
      obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h4
      exact hemit h3 hsuccFacts

theorem walkBind_fn (hctx : Ctx P Q Valid Xc n) (hW : WalkAt P Q Valid Xc n fuel) {C : Cfg} {env : Walk.Env}
    {here : Here} {c : Ixon.V3.LetContract} {ps : List Ixon.V3.BinderContract} {fb : Exp} {body : Exp}
    {k : Kont} {out : Exp} {s s' : Fires}
    (h : (Walk.walkBind C (fuel + 1) env here c (.fn ps fb) body k).run s = .ok (out, s')) :
    ExpSim P Q Valid Xc n C out env here k (.bind c (.fn ps fb) body) := by
  intro ρ J ρ' J' live jlive SK hV henv hJ hd hdj hf hnd hk
  rw [Walk.walkBind] at h
  dsimp only at h
  have hndfb := NoDead.fn_body (hnd.bind_rhs)
  have hpure : ∀ (ent : Ent), (ps ≠ [] → WEnt Q Valid Xc C ent (.clos ρ ps.length fb []) ρ' ∨
      (ent = .opd .box ∧ body.occ 0 = 0)) →
      (∀ k, evalBind P k ρ (.fn ps fb) = .stuck) ∨ ∃ u, (∀ k, evalBind P k ρ (.fn ps fb) = .ok u) ∧
        (WEnt Q Valid Xc C ent u ρ' ∨ (ent = .opd .box ∧ body.occ 0 = 0)) := by
    intro ent hent
    by_cases hps : ps = []
    · subst hps; exact .inl fun k => evalBind_fn_nil P k ρ fb
    · exact .inr ⟨_, fun k => evalBind_fn P k ρ ps fb hps, hent hps⟩
  split at h
  · next hc =>
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact skip_sim hW (run_fire_then h) (hctx.push hV) henv hJ hd hdj hf hnd hk (hpure _ fun _ => .inr ⟨rfl, hc.2⟩)
  · split at h
    · exact skip_sim hW h (hctx.push hV) henv hJ hd hdj hf hnd hk
        (hpure _ fun hps => .inl (.fn henv hndfb (List.length_pos_iff.2 hps) (hctx.ext hV)))
    · obtain ⟨fb', s1, h1, h2⟩ := Walk.run_bind_ok h
      obtain ⟨e, s2, h3, h4⟩ := Walk.run_bind_ok h2
      obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h4
      by_cases hps : ps = []
      · subst hps
        exact (SimUpTo.stuck _).congr (fun k => by rw [eval_bind, evalBind_fn_nil]; rfl) (fun _ => rfl)
      have hpos : 0 < ps.length := List.length_pos_iff.2 hps
      rw [hd] at h1
      have hwv : WV Q Valid Xc (.clos ρ ps.length fb []) (.clos ρ' ps.length fb' []) :=
        .walkc (σP := Walk.entsOf (paramOpds ρ'.length ps.length)) (got := []) (got' := [])
          (oOf := fun _ => .box) (wOf := fun _ => .box) hV h1 henv hf hndfb
          (by simp [Walk.entsOf, paramOpds_length]) (Nat.le_refl _) (by simp) (by simpa using hpos)
          (by simp) (fun p hp => by omega) (fun p v hp => by omega)
          (fun p _ hp2 => by
            simp only [Walk.entsOf, List.getElem?_map, paramOpds_get _ _ hp2, Option.map_some]
            simp)
          (fun p v w _ _ hv => by simp at hv)
      refine emit_sim hctx hW h3 hV henv hJ hd hdj hnd hk ?_
      exact (SimUpTo.ok ⟨hwv, hf.push _⟩).congr (fun k => evalBind_fn P k ρ ps fb hps)
        (fun k => evalBind_fn Q k ρ' ps fb' hps)

end Compilatrix.Anf.WalkProof
