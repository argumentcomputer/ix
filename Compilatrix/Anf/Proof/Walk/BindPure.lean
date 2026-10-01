import Compilatrix.Anf.Proof.Walk.Emit

/-! # The rewriting walk: pure bindings

One fuel level of the walk's simulation for the bindings that never charge:
atoms (copy propagation), constructors, projections (of a known
constructor), primitives (literal folding) and local functions (dead,
inlined at their single application, or walked under their parameters as a
`walkc` closure) (M2.3). -/

set_option autoImplicit false

namespace Compilatrix.Anf.WalkProof

open Compilatrix.Sem (Result ClockMono SimUpTo later later_succ later_zero)
open Compilatrix.Anf.Rel (Pw)
open Walk (Ent JEnt Fact Here Cfg Kont Fires)

variable {P Q : Program} {Valid : Cfg → List Val → Prop} {Xc : Nat → List Val → Exp → Exp → Prop} {n fuel : Nat}

theorem FactsOk.insert' {facts : Src.NatMap Fact} {ρ' : List Val} (h : FactsOk Q Valid facts ρ') {d : Nat}
    (hd : d = ρ'.length) {w : Val} {f : Fact} (hf : FactOk Q Valid (w :: ρ') d f) :
    FactsOk Q Valid (facts.insert d f) (w :: ρ') := by
  subst hd; exact h.insert hf

theorem lvl_top {d : Nat} {ρ' : List Val} (hd : d = ρ'.length) (w : Val) :
    (Opd.lvl d).val (w :: ρ') = some w := by
  subst hd; exact Opd.val_lvl_top ρ' w

/-- A value related to itself: literals and field-free constructors (the
results of primitives). -/
theorem WV.lit_or_con {u : Val} (h : (∃ l, u = .lit l) ∨ ∃ key, u = .con key []) : WV Q Valid Xc u u := by
  rcases h with ⟨l, rfl⟩ | ⟨key, rfl⟩
  · exact .lit
  · exact .con .nil

theorem primResult_cases (K : Lam.Known) (p : Lam.Prim) (vs : List Val) :
    primResult K p vs = .stuck ∨ ∃ u, primResult K p vs = .ok u ∧ ((∃ l, u = .lit l) ∨ ∃ key, u = .con key []) := by
  unfold primResult
  split
  · split
    · exact .inr ⟨_, rfl, .inl ⟨_, rfl⟩⟩
    · split
      · exact .inr ⟨_, rfl, .inr ⟨_, rfl⟩⟩
      · exact .inl rfl
    · exact .inl rfl
  · exact .inl rfl

theorem fold_lits {ρ' : List Val} : ∀ {os : List Opd} {ns : List Nat} {ws : List Val},
    Walk.fold.lits os = some ns → os.mapM (·.val ρ') = some ws → natArgs ws = some ns
  | [], ns, ws, h, hw => by
    simp [Walk.fold.lits] at h; simp at hw; subst h hw; rfl
  | o :: os, ns, ws, h, hw => by
    cases o with
    | lit l =>
      cases l with
      | nat m =>
        simp only [Walk.fold.lits] at h
        obtain ⟨ns', hns', rfl⟩ := Option.map_eq_some_iff.1 h
        simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
          Option.some.injEq, Opd.val] at hw
        obtain ⟨w, hw', ws', hws', rfl⟩ := hw
        cases hw'
        simp [natArgs, fold_lits hns' hws']
      | str s => simp [Walk.fold.lits] at h
    | lvl l => simp [Walk.fold.lits] at h
    | box => simp [Walk.fold.lits] at h

/-- The value of a projection is stuck or a field. -/
theorem projVal_cases (c : Key.CtorKey) (i : Nat) (v : Val) :
    projVal c i v = .stuck ∨ ∃ u, projVal c i v = .ok u := by
  unfold projVal
  split
  · split
    · cases _ : (‹List Val›)[i]? <;> simp_all [Result.ofOption]
    · exact .inl rfl
  · exact .inl rfl

theorem walkBind_atom (hctx : Ctx P Q Valid Xc n) (hW : WalkAt P Q Valid Xc n fuel) {C : Cfg} {env : Walk.Env}
    {here : Here} {c : Ixon.V3.LetContract} {a : Atom} {body : Exp} {k : Kont} {out : Exp} {s s' : Fires}
    (h : (Walk.walkBind C (fuel + 1) env here c (.atom a) body k).run s = .ok (out, s')) :
    ExpSim P Q Valid Xc n C out env here k (.bind c (.atom a) body) := by
  intro ρ J ρ' J' live jlive SK hV henv hJ hd hdj hf hnd hk
  rw [Walk.walkBind] at h
  dsimp only at h
  obtain ⟨o, s1, h1, h2⟩ := Walk.run_bind_ok h
  try dsimp only at h2
  obtain ⟨rfl, v, w, hv, hw, hvw⟩ := resolve_rel' henv h1 fun i hi => by
    simpa [Bind.occ] using hnd.bind_rhs i hi
  have hsrc : ∀ k, evalBind P k ρ (.atom a) = .ok v := fun k => by rw [evalBind_atom, hv]; rfl
  split at h2
  · exact skip_sim hW (run_fire_then h2) hV henv hJ hd hdj hf hnd hk (.inr ⟨v, hsrc, .inl (.opd hw hvw)⟩)
  · obtain ⟨e, s2, h3, h4⟩ := Walk.run_bind_ok h2
    obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h4
    refine emit_sim hctx hW h3 hV henv hJ hd hdj hnd hk ?_
    refine (SimUpTo.ok ⟨hvw, hf.push w⟩).congr hsrc (fun k => ?_)
    rw [evalBind_atom, hd, Opd.val_atom hw]; rfl

theorem walkBind_con (hctx : Ctx P Q Valid Xc n) (hW : WalkAt P Q Valid Xc n fuel) {C : Cfg} {env : Walk.Env}
    {here : Here} {c : Ixon.V3.LetContract} {cc : Key.CtorKey} {as : List Atom} {body : Exp} {k : Kont}
    {out : Exp} {s s' : Fires}
    (h : (Walk.walkBind C (fuel + 1) env here c (.con cc as) body k).run s = .ok (out, s')) :
    ExpSim P Q Valid Xc n C out env here k (.bind c (.con cc as) body) := by
  intro ρ J ρ' J' live jlive SK hV henv hJ hd hdj hf hnd hk
  rw [Walk.walkBind] at h
  dsimp only at h
  obtain ⟨os, s1, h1, h2⟩ := Walk.run_bind_ok h
  try dsimp only at h2
  obtain ⟨rfl, vs, ws, hvs, hws, hvws⟩ := resolveList_rel' henv h1 fun i hi => by
    simpa [Bind.occ] using hnd.bind_rhs i hi
  have hsrc : ∀ k, evalBind P k ρ (.con cc as) = .ok (.con cc vs) := fun k => by
    rw [evalBind_con, hvs]; rfl
  split at h2
  · next hc =>
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact skip_sim hW (run_fire_then h2) hV henv hJ hd hdj hf hnd hk
      (.inr ⟨_, hsrc, .inr ⟨rfl, hc.2⟩⟩)
  · obtain ⟨e, s2, h3, h4⟩ := Walk.run_bind_ok h2
    obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h4
    refine emit_sim hctx hW h3 hV henv hJ hd hdj hnd hk ?_
    refine (SimUpTo.ok ⟨.con hvws, hf.insert' hd ⟨_, ws, lvl_top hd _,
      opds_suffix (List.suffix_cons _ _) hws, rfl⟩⟩).congr hsrc (fun k => ?_)
    rw [evalBind_con, hd, Walk.atoms, opds_eval hws]; rfl

theorem walkBind_proj (hctx : Ctx P Q Valid Xc n) (hW : WalkAt P Q Valid Xc n fuel) {C : Cfg} {env : Walk.Env}
    {here : Here} {c : Ixon.V3.LetContract} {cc : Key.CtorKey} {i : Nat} {x : Atom} {body : Exp}
    {k : Kont} {out : Exp} {s s' : Fires}
    (h : (Walk.walkBind C (fuel + 1) env here c (.proj cc i x) body k).run s = .ok (out, s')) :
    ExpSim P Q Valid Xc n C out env here k (.bind c (.proj cc i x) body) := by
  intro ρ J ρ' J' live jlive SK hV henv hJ hd hdj hf hnd hk
  rw [Walk.walkBind] at h
  dsimp only at h
  obtain ⟨xo, s1, h1, h2⟩ := Walk.run_bind_ok h
  try dsimp only at h2
  obtain ⟨rfl, v, w, hv, hw, hvw⟩ := resolve_rel' henv h1 fun i hi => by
    simpa [Bind.occ] using hnd.bind_rhs i hi
  have hsrc : ∀ k, evalBind P k ρ (.proj cc i x) = projVal cc i v := fun k => by
    rw [evalBind_proj, hv]; rfl
  have hpure : ∀ (ent : Ent), (∀ u, projVal cc i v = .ok u → WEnt Q Valid Xc ent u ρ' ∨
      (ent = .opd .box ∧ body.occ 0 = 0)) →
      (∀ k, evalBind P k ρ (.proj cc i x) = .stuck) ∨ ∃ u, (∀ k, evalBind P k ρ (.proj cc i x) = .ok u) ∧
        (WEnt Q Valid Xc ent u ρ' ∨ (ent = .opd .box ∧ body.occ 0 = 0)) := by
    intro ent hent
    rcases projVal_cases cc i v with hst | ⟨u, hu⟩
    · exact .inl fun k => by rw [hsrc, hst]
    · exact .inr ⟨u, fun k => by rw [hsrc, hu], hent u hu⟩
  split at h2
  · -- a projection of a known constructor
    next o hhit =>
    split at hhit
    · split at hhit
      · next c' fs hkn =>
        split at hhit
        · next hc' =>
          simp only [decide_eq_true_eq] at hc'
          subst hc'
          have hK : Q.known = C.prog.known := by rw [hctx.known, hctx.cknown C ρ' hV]
          obtain ⟨wfs, hwfs, hwc⟩ := known_sound hK hf hkn hw
          refine skip_sim hW (run_fire_then h2) hV henv hJ hd hdj hf hnd hk (hpure _ fun u hu => .inl ?_)
          cases v with
          | con c'' fsv =>
            obtain ⟨wsw, rfl, hpw⟩ := structural.invCon c'' fsv w hvw
            simp only [Val.asCtor, Option.some.injEq, Prod.mk.injEq] at hwc
            obtain ⟨rfl, rfl⟩ := hwc
            simp only [projVal, if_true] at hu
            cases hfi : fsv[i]? with
            | none => rw [hfi] at hu; cases hu
            | some u' =>
              rw [hfi] at hu; cases hu
              rcases (of_pw hpw).get i with ⟨h1, _⟩ | ⟨v1, w1, hv1, hw1, hvw1⟩
              · rw [hfi] at h1; cases h1
              · rw [hfi] at hv1; cases hv1
                have hil : i < fs.length := by
                  rcases Nat.lt_or_ge i fs.length with hl | hl
                  · exact hl
                  · rw [List.getElem?_eq_none hl] at hhit; cases hhit
                have := mapM_get hwfs i hil
                rw [List.getElem?_eq_getElem hil] at hhit
                cases hhit
                rw [hw1] at this
                exact .opd this hvw1
          | lit l => simp [projVal] at hu
          | clos => simp [projVal] at hu
          | box => simp [projVal] at hu
        · cases hhit
      · cases hhit
    · cases hhit
  · split at h2
    · next hc =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      exact skip_sim hW (run_fire_then h2) hV henv hJ hd hdj hf hnd hk
        (hpure _ fun _ _ => .inr ⟨rfl, hc.2⟩)
    · obtain ⟨e, s2, h3, h4⟩ := Walk.run_bind_ok h2
      obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h4
      refine emit_sim hctx hW h3 hV henv hJ hd hdj hnd hk ?_
      refine ((Rel.proj_rel structural.toBase cc i hvw).strengthen (S := fun w => FactsOk Q Valid here.facts (w :: ρ'))
        fun _ w _ => hf.push w).congr hsrc (fun k => ?_)
      rw [evalBind_proj, hd, Opd.val_atom hw]; rfl

end Compilatrix.Anf.WalkProof
