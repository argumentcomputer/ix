import Compilatrix.Anf.Proof.Walk.Lemmas

/-! # The rewriting walk: dispatch, continuations and branching

One fuel level of the walk's simulation for `walk` itself (returns, ticks,
traps; the other forms dispatch to their walk functions), for `after` (the
continuation of an inlined term: the caller's continuation, a jump to an
emitted join point, or a meta-continuation) and for `branch` (a
meta-continuation becomes a join point before the walk branches) (M2.3). -/

set_option autoImplicit false

namespace Compilatrix.Anf.WalkProof

open Compilatrix.Sem (Result ClockMono SimUpTo later later_succ later_zero)
open Compilatrix.Anf.Rel (Pw)
open Walk (Ent JEnt Fact Here Cfg Kont Fires)

theorem run_fire_then {α : Type} {f : Fires → Fires} {x : Walk.M α} {s s' : Fires} {a : α}
    (h : (Walk.fire f >>= fun _ => x).run s = .ok (a, s')) : x.run (f s) = .ok (a, s') := by
  obtain ⟨u, s1, h1, h2⟩ := Walk.run_bind_ok h
  cases Walk.run_fire_ok h1
  exact h2

variable {P Q : Program} {Valid : Cfg → List Val → Prop}

/-! ## Resolving atoms that occur -/

theorem resolve_rel' {env : Walk.Env} {live : List Bool} {ρ ρ' : List Val}
    (henv : WEnv Q Valid live env.σ ρ ρ') {a : Atom} {o : Opd} {s s' : Fires}
    (h : (Walk.resolve env a).run s = .ok (o, s'))
    (hocc : ∀ i, live[i]? = some false → a.occ i = 0) :
    s' = s ∧ ∃ v w, a.eval ρ = some v ∧ o.val ρ' = some w ∧ WV Q Valid v w := by
  refine resolve_rel henv h fun i hi => ?_
  have hlen : env.σ.length = live.length := by
    have := henv.length; omega
  refine atom_live hlen hocc i hi fun hn => ?_
  subst hi
  simp only [Walk.resolve, hn] at h
  cases h

theorem resolveList_rel' {env : Walk.Env} {live : List Bool} {ρ ρ' : List Val}
    (henv : WEnv Q Valid live env.σ ρ ρ') : ∀ {as : List Atom} {os : List Opd} {s s' : Fires},
    (Walk.resolveList env as).run s = .ok (os, s') →
    (∀ i, live[i]? = some false → Atom.occList i as = 0) →
    s' = s ∧ ∃ vs ws, evalAtoms ρ as = some vs ∧ os.mapM (·.val ρ') = some ws ∧ WVs Q Valid vs ws
  | [], os, s, s', h, _ => by
    simp only [Walk.resolveList] at h
    obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h
    exact ⟨rfl, [], [], rfl, rfl, .nil⟩
  | a :: as, os, s, s', h, hocc => by
    simp only [Walk.resolveList] at h
    obtain ⟨o, s1, h1, h⟩ := Walk.run_bind_ok h
    obtain ⟨os', s2, h2, h⟩ := Walk.run_bind_ok h
    obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h
    obtain ⟨rfl, v, w, hv, hw, hvw⟩ := resolve_rel' henv h1 fun i hi => by
      have := hocc i hi; simp only [Atom.occList] at this; omega
    obtain ⟨rfl, vs, ws, hvs, hws, hvws⟩ := resolveList_rel' henv h2 fun i hi => by
      have := hocc i hi; simp only [Atom.occList] at this; omega
    refine ⟨rfl, v :: vs, w :: ws, ?_, ?_, .cons hvw hvws⟩
    · simp [evalAtoms_cons, hv, hvs]
    · simp [List.mapM_cons, hw, hws]

/-! ## Source-side unfolding -/

theorem bind_assoc' {α β γ : Type} (r : Result α) (f : α → Result β) (g : β → Result γ) :
    (r.bind f).bind g = r.bind fun a => (f a).bind g :=
  Sem.Result.bind_assoc r f g

/-- A charge followed by a continuation at the outer clock is a charge over
the continuation one clock up. -/
theorem later_bind_shift {α β : Type} (k : Nat) (c : Nat → Result α) (d : α → Nat → Result β) :
    (later k c).bind (d · k) = later k fun j => (c j).bind (d · (j + 1)) := by
  cases k <;> rfl

variable {n fuel : Nat}

/-! ## Branching -/

/-- `branch`: a meta-continuation becomes a join point whose body is the
continuation's walk on the join parameter; the walk then continues with a
jump to it. -/
theorem branch_sim {here : Here} {k : Kont} {body : Here → Kont → Walk.M Exp} {out : Exp}
    {s s' : Fires} (h : (Walk.branch here k body).run s = .ok (out, s')) {ρ' : List Val}
    {J' : List JClo} (hd : here.d = ρ'.length) (hdj : here.dj = J'.length)
    (hfacts : FactsOk Q Valid here.facts ρ') {SK : Val → Nat → Result Val}
    (hk : KontW Q Valid n k SK ρ' J') {c : Nat → Result Val}
    (hbody : ∀ (here0 : Here) (k0 : Kont) (out0 : Exp) (s0 s0' : Fires) (J'0 : List JClo),
      (body here0 k0).run s0 = .ok (out0, s0') → here0.d = here.d → here0.facts = here.facts →
      here0.dj = J'0.length → J' <:+ J'0 → (∃ T, KT Q k0 J'0 = some T) →
      (KT Q k J' = none ∨ KT Q k0 J'0 = KT Q k J') →
      KontW Q Valid n k0 SK ρ' J'0 →
      SimUpTo (WV Q Valid) n c (fun k => eval Q k ρ' J'0 out0)) :
    SimUpTo (WV Q Valid) n c (fun k => eval Q k ρ' J' out) := by
  cases k with
  | cont f =>
    simp only [Walk.branch] at h
    obtain ⟨jb, s1, h1, h⟩ := Walk.run_bind_ok h
    obtain ⟨e, s2, h2, h⟩ := Walk.run_bind_ok h
    obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h
    have hJ0 : J' <:+ JClo.mk ρ' J' 1 jb false :: J' := List.suffix_cons _ _
    have hKT : KT Q (.jump here.dj) (JClo.mk ρ' J' 1 jb false :: J') =
        some fun w k => jumpTo Q k (JClo.mk ρ' J' 1 jb false) [w] := by
      simp only [KT, hdj, List.length_cons, Nat.lt_succ_self, if_true]
      rw [show J'.length + 1 - 1 - J'.length = 0 by omega]; rfl
    refine (hbody _ _ e s1 s2 _ h2 rfl rfl (by simp [hdj]) hJ0 ⟨_, hKT⟩ (.inl rfl) ?_).congr
      (fun _ => rfl) (fun k => eval_join' Q k ρ' J' 1 false jb e)
    refine ⟨_, hKT, fun x w hxw => ?_⟩
    have hs := hk { here with d := here.d + 1 } (.lvl here.d) jb s s1 (w :: ρ') J' h1
      (List.suffix_cons _ _) (List.suffix_refl _) (by simp [hd]) hdj
      (hfacts.suffix (List.suffix_cons _ _)) x w (by rw [hd]; exact Opd.val_lvl_top ρ' w) hxw
    refine (hs.laterR (eval_mono Q _ _ _)).congr (fun _ => rfl) (fun k => ?_)
    simp [jumpTo]
  | ret =>
    simp only [Walk.branch] at h
    obtain ⟨T, hT, _⟩ := hk
    exact hbody here .ret out s s' J' h rfl rfl hdj (List.suffix_refl _) ⟨T, hT⟩ (.inr rfl) ⟨T, hT, ‹_›⟩
  | jump l =>
    simp only [Walk.branch] at h
    obtain ⟨T, hT, hs⟩ := hk
    exact hbody here (.jump l) out s s' J' h rfl rfl hdj (List.suffix_refl _) ⟨T, hT⟩ (.inr rfl)
      ⟨T, hT, hs⟩

end Compilatrix.Anf.WalkProof
