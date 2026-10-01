import Compilatrix.Anf.Proof.Walk.Rel

/-! # The rewriting walk: basic facts

The walk relation is structural (an `Anf.Rel` instance); environments,
facts, join entries and continuations stay valid when the target
environments grow (levels keep their values); resolving a live atom gives
an operand whose value is related to the atom's source value (M2.3). -/

set_option autoImplicit false

namespace Compilatrix.Anf.WalkProof

open Compilatrix.Sem (Result ClockMono SimUpTo later later_succ later_zero)
open Compilatrix.Anf.Rel (Pw)
open Walk (Ent JEnt Fact Here Cfg Kont Fires)

variable {Q : Program} {Valid : Cfg → List Val → Prop} {Xc : Nat → List Val → Exp → Exp → Prop}

/-! ## Structure -/

theorem pw_of : ∀ {vs ws : List Val}, WVs Q Valid Xc vs ws → Pw (WV Q Valid Xc) vs ws
  | _, _, .nil => .nil
  | _, _, .cons h hs => .cons h (pw_of hs)

theorem of_pw : ∀ {vs ws : List Val}, Pw (WV Q Valid Xc) vs ws → WVs Q Valid Xc vs ws
  | _, _, .nil => .nil
  | _, _, .cons h hs => .cons h (of_pw hs)

theorem structural : Rel.Structural (WV Q Valid Xc) where
  lit _ := .lit
  box := .box
  con _ _ _ h := .con (of_pw h)
  idc _ _ _ _ _ _ hρ hg := .idc (of_pw hρ) (of_pw hg)
  invLit l w h := by cases h; rfl
  invBox w h := by cases h; rfl
  invCon c vs w h := by cases h with | con h => exact ⟨_, rfl, pw_of h⟩
  invClos ρ n b got w h := by
    cases h with
    | idc _ _ => exact ⟨_, _, _, _, rfl⟩
    | walkc => exact ⟨_, _, _, _, rfl⟩
    | xc _ _ _ => exact ⟨_, _, _, _, rfl⟩

mutual

theorem obs : ∀ {v w : Val}, WV Q Valid Xc v w → obsV v = obsV w
  | _, _, .lit => rfl
  | _, _, .box => rfl
  | _, _, .con h => by
    rename_i c _ _
    cases c with
    | src c => simp only [obsV, obsList_eq h]
    | clo f j => rfl
  | _, _, .idc _ _ => rfl
  | _, _, .walkc _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl
  | _, _, .xc _ _ _ => rfl

theorem obsList_eq : ∀ {vs ws : List Val}, WVs Q Valid Xc vs ws → obsList vs = obsList ws
  | _, _, .nil => rfl
  | _, _, .cons h hs => by simp only [obsList, obs h, obsList_eq hs]

end

theorem WVs.length : ∀ {vs ws : List Val}, WVs Q Valid Xc vs ws → ws.length = vs.length
  | _, _, .nil => rfl
  | _, _, .cons _ h => by simp [h.length]

theorem WVs.append : ∀ {vs ws : List Val}, WVs Q Valid Xc vs ws → ∀ {vs' ws' : List Val},
    WVs Q Valid Xc vs' ws' → WVs Q Valid Xc (vs ++ vs') (ws ++ ws')
  | _, _, .nil, _, _, h' => h'
  | _, _, .cons h hs, _, _, h' => .cons h (hs.append h')

theorem WVs.get : ∀ {vs ws : List Val}, WVs Q Valid Xc vs ws → ∀ (i : Nat),
    (vs[i]? = none ∧ ws[i]? = none) ∨ ∃ v w, vs[i]? = some v ∧ ws[i]? = some w ∧ WV Q Valid Xc v w
  | _, _, .nil, _ => .inl ⟨rfl, rfl⟩
  | _, _, .cons h _, 0 => .inr ⟨_, _, rfl, rfl, h⟩
  | _, _, .cons _ h, i + 1 => by simpa using h.get i

/-! ## Growing target environments -/

theorem opds_suffix {ρ ρ₂ : List Val} (hs : ρ <:+ ρ₂) : ∀ {os : List Opd} {ws : List Val},
    os.mapM (·.val ρ) = some ws → os.mapM (·.val ρ₂) = some ws
  | [], ws, h => h
  | o :: os, ws, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h ⊢
    obtain ⟨w, hw, ws', hws, rfl⟩ := h
    exact ⟨w, Opd.val_suffix hs hw, ws', opds_suffix hs hws, rfl⟩

theorem opds_eval {ρ : List Val} : ∀ {os : List Opd} {ws : List Val}, os.mapM (·.val ρ) = some ws →
    evalAtoms ρ (os.map (·.atom ρ.length)) = some ws
  | [], ws, h => by simp at h; subst h; rfl
  | o :: os, ws, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨w, hw, ws', hws, rfl⟩ := h
    simp only [List.map_cons, evalAtoms_cons, Opd.val_atom hw, opds_eval hws, Option.bind_some,
      Option.map_some]

theorem FactOk.suffix {ρ ρ₂ : List Val} (hs : ρ <:+ ρ₂) {l : Nat} :
    ∀ {f : Fact}, FactOk Q Valid ρ l f → FactOk Q Valid ρ₂ l f
  | .ctor _ _, ⟨w, ws, hw, hws, hc⟩ => ⟨w, ws, Opd.val_suffix hs hw, opds_suffix hs hws, hc⟩
  | .succ _, ⟨m, hl, hy⟩ => ⟨m, Opd.val_suffix hs hl, Opd.val_suffix hs hy⟩
  | .glob _, ⟨gd, hg, hps, ha, hl⟩ => ⟨gd, hg, hps, ha, Opd.val_suffix hs hl⟩
  | .pap _ _, ⟨gd, ws, hg, hws, ha, hlt, hl⟩ =>
    ⟨gd, ws, hg, opds_suffix hs hws, ha, hlt, Opd.val_suffix hs hl⟩

theorem FactsOk.suffix {facts : Src.NatMap Fact} {ρ ρ₂ : List Val} (h : FactsOk Q Valid facts ρ)
    (hs : ρ <:+ ρ₂) : FactsOk Q Valid facts ρ₂ := fun l f hf => (h l f hf).suffix hs

mutual

theorem WEnt.suffix {ρ' ρ₂ : List Val} (hs : ρ' <:+ ρ₂) :
    ∀ {e : Ent} {v : Val}, WEnt Q Valid Xc e v ρ' → WEnt Q Valid Xc e v ρ₂
  | _, _, .opd hw hv => .opd (Opd.val_suffix hs hw) hv
  | _, _, .fn henv hnd hn => .fn (WEnv.suffix hs henv) hnd hn

theorem WEnv.suffix {ρ' ρ₂ : List Val} (hs : ρ' <:+ ρ₂) :
    ∀ {live : List Bool} {σ : List Ent} {ρ : List Val}, WEnv Q Valid Xc live σ ρ ρ' → WEnv Q Valid Xc live σ ρ ρ₂
  | _, _, _, .nil => .nil
  | _, _, _, .live he h => .live (WEnt.suffix hs he) (WEnv.suffix hs h)
  | _, _, _, .dead h => .dead (WEnv.suffix hs h)

end

theorem WEnv.length : ∀ {live : List Bool} {σ : List Ent} {ρ ρ' : List Val},
    WEnv Q Valid Xc live σ ρ ρ' → σ.length = ρ.length ∧ live.length = ρ.length
  | _, _, _, _, .nil => ⟨rfl, rfl⟩
  | _, _, _, _, .live _ h => by have := h.length; simp [this.1, this.2]
  | _, _, _, _, .dead h => by have := h.length; simp [this.1, this.2]

/-- A live entry of the walk environment. -/
theorem WEnv.get : ∀ {live : List Bool} {σ : List Ent} {ρ ρ' : List Val},
    WEnv Q Valid Xc live σ ρ ρ' → ∀ {i : Nat} {e : Ent}, σ[i]? = some e → live[i]? = some true →
    ∃ v, ρ[i]? = some v ∧ WEnt Q Valid Xc e v ρ'
  | _, _, _, _, .nil, _, _, h, _ => by simp at h
  | _, _, _, _, .live he _, 0, _, h, _ => by simp at h; subst h; exact ⟨_, rfl, he⟩
  | _, _, _, _, .dead _, 0, _, _, hl => by simp at hl
  | _, _, _, _, .live _ h, i + 1, _, he, hl => by simpa using h.get (by simpa using he) (by simpa using hl)
  | _, _, _, _, .dead h, i + 1, _, he, hl => by simpa using h.get (by simpa using he) (by simpa using hl)

/-! ## Resolving atoms -/

/-- An atom that reads no dropped variable resolves to an operand whose
value is related to the atom's source value. -/
theorem resolve_rel {env : Walk.Env} {live : List Bool} {ρ ρ' : List Val}
    (henv : WEnv Q Valid Xc live env.σ ρ ρ') {a : Atom} {o : Opd} {s s' : Fires}
    (h : (Walk.resolve env a).run s = .ok (o, s'))
    (hlive : ∀ i, a = .var i → live[i]? = some true) :
    s' = s ∧ ∃ v w, a.eval ρ = some v ∧ o.val ρ' = some w ∧ WV Q Valid Xc v w := by
  cases a with
  | var i =>
    simp only [Walk.resolve] at h
    cases he : env.σ[i]? with
    | none => rw [he] at h; cases h
    | some e =>
      rw [he] at h
      cases e with
      | opd o' =>
        obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h
        obtain ⟨v, hv, hent⟩ := henv.get he (hlive i rfl)
        cases hent with
        | opd hw hvw => exact ⟨rfl, v, _, by simp [Atom.eval, hv], hw, hvw⟩
      | fn _ _ _ => cases h
  | lit l =>
    simp only [Walk.resolve] at h
    obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h
    exact ⟨rfl, _, _, rfl, rfl, .lit⟩
  | box =>
    simp only [Walk.resolve] at h
    obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h
    exact ⟨rfl, _, _, rfl, rfl, .box⟩

theorem resolveList_rel {env : Walk.Env} {live : List Bool} {ρ ρ' : List Val}
    (henv : WEnv Q Valid Xc live env.σ ρ ρ') : ∀ {as : List Atom} {os : List Opd} {s s' : Fires},
    (Walk.resolveList env as).run s = .ok (os, s') →
    (∀ i, Atom.var i ∈ as → live[i]? = some true) →
    s' = s ∧ ∃ vs ws, evalAtoms ρ as = some vs ∧ os.mapM (·.val ρ') = some ws ∧ WVs Q Valid Xc vs ws
  | [], os, s, s', h, _ => by
    simp only [Walk.resolveList] at h
    obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h
    exact ⟨rfl, [], [], rfl, rfl, .nil⟩
  | a :: as, os, s, s', h, hlive => by
    simp only [Walk.resolveList] at h
    obtain ⟨o, s1, h1, h⟩ := Walk.run_bind_ok h
    obtain ⟨os', s2, h2, h⟩ := Walk.run_bind_ok h
    obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h
    obtain ⟨rfl, v, w, hv, hw, hvw⟩ := resolve_rel henv h1 fun i e => hlive i (by simp [e])
    obtain ⟨rfl, vs, ws, hvs, hws, hvws⟩ := resolveList_rel henv h2 fun i hi => hlive i (by simp [hi])
    refine ⟨rfl, v :: vs, w :: ws, ?_, ?_, .cons hvw hvws⟩
    · simp [evalAtoms_cons, hv, hvs]
    · simp [List.mapM_cons, hw, hws]

end Compilatrix.Anf.WalkProof
