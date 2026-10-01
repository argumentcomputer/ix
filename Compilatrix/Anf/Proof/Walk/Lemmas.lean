import Compilatrix.Anf.Proof.Walk.Occ

/-! # The rewriting walk: supporting lemmas

Operand lists and the environments the walk pushes (parameters, fields,
arguments), join-entry lookups, the target meaning of a continuation under
growth, and what the walk's syntactic tests (`known`, `knownHead`,
`select`, `stripTicks`, `fold`) say about values (M2.3). -/

set_option autoImplicit false

namespace Compilatrix.Anf.WalkProof

open Compilatrix.Sem (Result ClockMono SimUpTo later later_succ later_zero)
open Compilatrix.Anf.Rel (Pw)
open Walk (Ent JEnt Fact Here Cfg Kont Fires)

/-! ## Operand lists -/

theorem mapM_length {α β : Type} {f : α → Option β} : ∀ {xs : List α} {ys : List β},
    xs.mapM f = some ys → ys.length = xs.length
  | [], ys, h => by simp at h; subst h; rfl
  | x :: xs, ys, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨y, _, ys', hys, rfl⟩ := h
    simp [mapM_length hys]

theorem mapM_get {α β : Type} {f : α → Option β} : ∀ {xs : List α} {ys : List β},
    xs.mapM f = some ys → ∀ i (hi : i < xs.length), f xs[i] = ys[i]?
  | [], _, _, _, hi => by simp at hi
  | x :: xs, ys, h, i, hi => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨y, hy, ys', hys, rfl⟩ := h
    cases i with
    | zero => simpa using hy
    | succ i => simpa using mapM_get hys i (by simpa using hi)

theorem mapM_of_get {α β : Type} {f : α → Option β} : ∀ {xs : List α} {ys : List β},
    xs.length = ys.length → (∀ i (hi : i < xs.length), f xs[i] = ys[i]?) → xs.mapM f = some ys
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | x :: xs, y :: ys, hl, h => by
    have h0 := h 0 (by simp)
    simp only [List.getElem_cons_zero, List.getElem?_cons_zero] at h0
    have hr := mapM_of_get (xs := xs) (ys := ys) (by simpa using hl)
      (fun i hi => by
        have := h (i + 1) (by simp; omega)
        simp only [List.getElem_cons_succ, List.getElem?_cons_succ] at this; exact this)
    simp [List.mapM_cons, h0, hr]

theorem mapM_reverse {α β : Type} {f : α → Option β} {xs : List α} {ys : List β}
    (h : xs.mapM f = some ys) : xs.reverse.mapM f = some ys.reverse := by
  have hl := mapM_length h
  refine mapM_of_get (by simp [hl]) fun i hi => ?_
  simp only [List.length_reverse] at hi
  rw [List.getElem_reverse, mapM_get h _ (by omega), List.getElem?_reverse (by omega), hl]

theorem mapM_append {α β : Type} {f : α → Option β} {xs xs' : List α} {ys ys' : List β}
    (h : xs.mapM f = some ys) (h' : xs'.mapM f = some ys') : (xs ++ xs').mapM f = some (ys ++ ys') := by
  have hl := mapM_length h
  have hl' := mapM_length h'
  refine mapM_of_get (by simp [hl, hl']) fun i hi => ?_
  by_cases hi' : i < xs.length
  · rw [List.getElem_append_left hi', mapM_get h _ hi', List.getElem?_append_left (by omega)]
  · rw [List.getElem_append_right (by omega), mapM_get h' _ (by simp at hi; omega),
      List.getElem?_append_right (by omega), hl]

theorem mapM_take {α β : Type} {f : α → Option β} {xs : List α} {ys : List β}
    (h : xs.mapM f = some ys) (n : Nat) : (xs.take n).mapM f = some (ys.take n) := by
  have hl := mapM_length h
  refine mapM_of_get (by simp [hl]) fun i hi => ?_
  simp only [List.length_take] at hi
  rw [List.getElem_take, mapM_get h _ (by omega), List.getElem?_take, if_pos (by omega)]

theorem mapM_drop {α β : Type} {f : α → Option β} {xs : List α} {ys : List β}
    (h : xs.mapM f = some ys) (n : Nat) : (xs.drop n).mapM f = some (ys.drop n) := by
  have hl := mapM_length h
  refine mapM_of_get (by simp [hl]) fun i hi => ?_
  simp only [List.length_drop] at hi
  rw [List.getElem_drop, mapM_get h _ (by omega), List.getElem?_drop]

theorem lvl_val_ext (ρ' ext : List Val) {i : Nat} (hi : i < ext.length) :
    (Opd.lvl (ρ'.length + i)).val (ext ++ ρ') = ext[ext.length - 1 - i]? := by
  simp only [Opd.val, List.length_append]
  rw [if_pos (by omega), List.getElem?_append_left (by omega)]
  congr 1; omega

theorem fieldOpds_val (ρ' ws : List Val) :
    (Walk.fieldOpds ρ'.length ws.length).mapM (·.val (ws.reverse ++ ρ')) = some ws := by
  refine mapM_of_get (by simp [Walk.fieldOpds]) fun i hi => ?_
  simp only [Walk.fieldOpds, List.length_map, List.length_range] at hi
  simp only [Walk.fieldOpds, List.getElem_map, List.getElem_range]
  rw [lvl_val_ext ρ' _ (by simp; omega), List.getElem?_reverse (by simp; omega)]
  congr 1; simp; omega

theorem paramOpds_val (ρ' ws : List Val) :
    (paramOpds ρ'.length ws.length).mapM (·.val (ws.reverse ++ ρ')) = some ws.reverse :=
  mapM_reverse (fieldOpds_val ρ' ws)

theorem paramOpds_get (d n : Nat) {p : Nat} (hp : p < n) :
    (paramOpds d n)[n - 1 - p]? = some (.lvl (d + p)) := by
  simp only [paramOpds]
  rw [List.getElem?_reverse (by simp; omega)]
  simp only [List.length_map, List.length_range]
  rw [show n - 1 - (n - 1 - p) = p by omega]
  simp [hp]

theorem paramOpds_length (d n : Nat) : (paramOpds d n).length = n := by simp [paramOpds]

theorem fieldOpds_length (d n : Nat) : (Walk.fieldOpds d n).length = n := by simp [Walk.fieldOpds]

variable {Q : Program} {Valid : Cfg → List Val → Prop} {Xc : Nat → List Val → Exp → Exp → Prop}

/-! ## Value lists -/

theorem WVs.reverse {vs ws : List Val} (h : WVs Q Valid Xc vs ws) : WVs Q Valid Xc vs.reverse ws.reverse :=
  of_pw (pw_of h).reverse

theorem WVs.take {vs ws : List Val} (h : WVs Q Valid Xc vs ws) (n : Nat) :
    WVs Q Valid Xc (vs.take n) (ws.take n) :=
  of_pw ((pw_of h).take n)

theorem WVs.drop {vs ws : List Val} (h : WVs Q Valid Xc vs ws) (n : Nat) :
    WVs Q Valid Xc (vs.drop n) (ws.drop n) :=
  of_pw ((pw_of h).drop n)

/-! ## Pushing operands -/

/-- Operands with related values pushed on a walk environment. -/
theorem WEnv.pushOpds {ρ' : List Val} : ∀ {os : List Opd} {vs ws : List Val},
    os.mapM (·.val ρ') = some ws → WVs Q Valid Xc vs ws →
    ∀ {live : List Bool} {σ : List Ent} {ρ : List Val}, WEnv Q Valid Xc live σ ρ ρ' →
    WEnv Q Valid Xc (List.replicate os.length true ++ live) (Walk.entsOf os ++ σ) (vs ++ ρ) ρ'
  | [], vs, ws, h, hv, _, _, _, he => by
    simp at h; subst h; cases hv; exact he
  | o :: os, vs, ws, h, hv, _, _, _, he => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨w, hw, ws', hws, rfl⟩ := h
    cases hv with
    | cons hvw hvs =>
      exact .live (.opd hw hvw) (WEnv.pushOpds hws hvs he)

/-- An environment prefix given entry by entry. -/
theorem WEnv.pushIdx {ρ' : List Val} : ∀ {σP : List Ent} {V : List Val}, σP.length = V.length →
    (∀ i (hi : i < σP.length), ∃ o w, σP[i] = .opd o ∧ o.val ρ' = some w ∧ ∃ v, V[i]? = some v ∧ WV Q Valid Xc v w) →
    ∀ {live : List Bool} {σ : List Ent} {ρ : List Val}, WEnv Q Valid Xc live σ ρ ρ' →
    WEnv Q Valid Xc (List.replicate σP.length true ++ live) (σP ++ σ) (V ++ ρ) ρ'
  | [], [], _, _, _, _, _, he => he
  | [], _ :: _, hl, _, _, _, _, _ => by simp at hl
  | _ :: _, [], hl, _, _, _, _, _ => by simp at hl
  | e :: σP, v :: V, hl, h, _, _, _, he => by
    obtain ⟨o, w, he0, hw, v', hv', hvw⟩ := h 0 (by simp)
    simp only [List.getElem_cons_zero] at he0
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hv'
    subst he0 hv'
    exact .live (.opd hw hvw) (WEnv.pushIdx (by simpa using hl)
      (fun i hi => by
        have := h (i + 1) (by simp; omega)
        simp only [List.getElem_cons_succ, List.getElem?_cons_succ] at this; exact this) he)

/-! ## Join entries -/

variable {P : Program}

theorem KT_mono {k : Kont} {J' : List JClo} {T : Val → Nat → Result Val} (h : KT Q k J' = some T)
    (w : Val) : ClockMono (T w) := by
  cases k with
  | ret =>
    simp only [KT, Option.some.injEq] at h; subst h
    intro _ _ _ _; rfl
  | jump l =>
    simp only [KT] at h
    split at h
    · obtain ⟨jcl, _, rfl⟩ := Option.map_eq_some_iff.1 h
      exact jumpTo_mono Q jcl [w]
    · cases h
  | cont f => cases h

/-- Join entries under growing target environments, for the target meaning
of the same continuation. -/
theorem JEnv.suffixK {n : Nat} {k : Kont} {ρ' ρ'' : List Val} {J' J'' : List JClo}
    {jl : List Bool} {jσ : List JEnt} {J : List JClo}
    (h : JEnv P Q Valid Xc n (KT Q k J') ρ' J' jl jσ J) (hρ : ρ' <:+ ρ'') (hJ : J' <:+ J'') :
    JEnv P Q Valid Xc n (KT Q k J'') ρ'' J'' jl jσ J := by
  cases hT : KT Q k J' with
  | none =>
    rw [hT] at h
    exact (JEnv.retarget (J₂ := J'') h).suffix hρ (List.suffix_refl _)
  | some T =>
    rw [hT] at h
    rw [KT_suffix hJ hT]
    exact h.suffix hρ hJ

/-- An emitted join entry that is live. -/
theorem JEnv.get_emitted {n : Nat} {T : Option (Val → Nat → Result Val)} {ρ' : List Val}
    {J' : List JClo} : ∀ {jl : List Bool} {jσ : List JEnt} {J : List JClo},
    JEnv P Q Valid Xc n T ρ' J' jl jσ J → ∀ {j l ar : Nat} {r : Bool} {σj : List Ent} {jσj : List JEnt}
    {b : Exp}, jσ[j]? = some (.mk (some l) σj jσj ar r b) → jl[j]? = some true →
    ∃ ρj Jj livej jlj jc' Tk, J[j]? = some (.mk ρj Jj ar b r) ∧ l < J'.length ∧
      J'[J'.length - 1 - l]? = some jc' ∧ T = some Tk ∧ JoinR P Q Valid Xc n Tk (.mk ρj Jj ar b r) jc' ∧
      WEnv Q Valid Xc livej σj ρj ρ' ∧ JEnv P Q Valid Xc n T ρ' J' jlj jσj Jj ∧
      NoDead (List.replicate ar true ++ livej) (if r then true :: jlj else jlj) b
  | _, _, _, .nil, _, _, _, _, _, _, _, h, _ => by simp at h
  | _, _, _, .emitted hl hjc hT hR henv hJj hnd _, 0, _, _, _, _, _, _, h, _ => by
    simp only [List.getElem?_cons_zero, Option.some.injEq, JEnt.mk.injEq] at h
    obtain ⟨⟨rfl⟩, rfl, rfl, rfl, rfl, rfl⟩ := h
    exact ⟨_, _, _, _, _, _, rfl, hl, hjc, hT, hR, henv, hJj, hnd⟩
  | _, _, _, .once _ _ _ _, 0, _, _, _, _, _, _, h, _ => by
    simp only [List.getElem?_cons_zero, Option.some.injEq, JEnt.mk.injEq] at h
    cases h.1
  | _, _, _, .dead _, 0, _, _, _, _, _, _, _, hl => by simp at hl
  | _, _, _, .emitted _ _ _ _ _ _ _ h, j + 1, _, _, _, _, _, _, he, hl => by
    simpa using h.get_emitted (by simpa using he) (by simpa using hl)
  | _, _, _, .once _ _ _ h, j + 1, _, _, _, _, _, _, he, hl => by
    simpa using h.get_emitted (by simpa using he) (by simpa using hl)
  | _, _, _, .dead h, j + 1, _, _, _, _, _, _, he, hl => by
    simpa using h.get_emitted (by simpa using he) (by simpa using hl)

/-- A join entry inlined at its single jump, live. -/
theorem JEnv.get_once {n : Nat} {T : Option (Val → Nat → Result Val)} {ρ' : List Val}
    {J' : List JClo} : ∀ {jl : List Bool} {jσ : List JEnt} {J : List JClo},
    JEnv P Q Valid Xc n T ρ' J' jl jσ J → ∀ {j ar : Nat} {r : Bool} {σj : List Ent} {jσj : List JEnt}
    {b : Exp}, jσ[j]? = some (.mk none σj jσj ar r b) → jl[j]? = some true →
    r = false ∧ ∃ ρj Jj livej jlj, J[j]? = some (.mk ρj Jj ar b false) ∧
      WEnv Q Valid Xc livej σj ρj ρ' ∧ JEnv P Q Valid Xc n T ρ' J' jlj jσj Jj ∧
      NoDead (List.replicate ar true ++ livej) jlj b
  | _, _, _, .nil, _, _, _, _, _, _, h, _ => by simp at h
  | _, _, _, .emitted _ _ _ _ _ _ _ _, 0, _, _, _, _, _, h, _ => by
    simp only [List.getElem?_cons_zero, Option.some.injEq, JEnt.mk.injEq] at h
    cases h.1
  | _, _, _, .once henv hJj hnd _, 0, _, _, _, _, _, h, _ => by
    simp only [List.getElem?_cons_zero, Option.some.injEq, JEnt.mk.injEq] at h
    obtain ⟨-, rfl, rfl, rfl, rfl, rfl⟩ := h
    exact ⟨rfl, _, _, _, _, rfl, henv, hJj, hnd⟩
  | _, _, _, .dead _, 0, _, _, _, _, _, _, hl => by simp at hl
  | _, _, _, .emitted _ _ _ _ _ _ _ h, j + 1, _, _, _, _, _, he, hl => by
    simpa using h.get_once (by simpa using he) (by simpa using hl)
  | _, _, _, .once _ _ _ h, j + 1, _, _, _, _, _, he, hl => by
    simpa using h.get_once (by simpa using he) (by simpa using hl)
  | _, _, _, .dead h, j + 1, _, _, _, _, _, he, hl => by
    simpa using h.get_once (by simpa using he) (by simpa using hl)

/-- A jump's target is live: it occurs. -/
theorem jlive_of_occ {jl : List Bool} {jσ : List JEnt} {j : Nat} {je : JEnt}
    (hlen : jσ.length = jl.length) (he : jσ[j]? = some je)
    (hocc : ∀ j', jl[j']? = some false → j' = j → False) : jl[j]? = some true := by
  have hj : j < jl.length := by
    rw [← hlen]
    rcases Nat.lt_or_ge j jσ.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at he; cases he
  cases hb : jl[j] with
  | true => rw [List.getElem?_eq_getElem hj, hb]
  | false => exact absurd rfl (hocc j (by rw [List.getElem?_eq_getElem hj, hb]))

/-! ## The walk's tests -/

/-- A known constructor view of an operand holds of its value. -/
theorem known_sound {K : Lam.Known} (hK : Q.known = K) {here : Here} {ρ' : List Val}
    (hf : FactsOk Q Valid here.facts ρ') {o : Opd} {c : Key.CtorKey} {fs : List Opd}
    (h : Walk.known K here o = some (c, fs)) {w : Val} (hw : o.val ρ' = some w) :
    ∃ ws, fs.mapM (·.val ρ') = some ws ∧ w.asCtor Q.known = some (c, ws) := by
  subst hK
  cases o with
  | lit l =>
    simp only [Opd.val, Option.some.injEq] at hw
    subst hw
    cases l with
    | nat m =>
      cases m with
      | zero =>
        simp only [Walk.known] at h
        obtain ⟨c', hc', he⟩ := Option.map_eq_some_iff.1 h
        cases he
        exact ⟨[], rfl, by simp [Val.asCtor, hc']⟩
      | succ m =>
        simp only [Walk.known] at h
        obtain ⟨c', hc', he⟩ := Option.map_eq_some_iff.1 h
        cases he
        exact ⟨[.lit (.nat m)], rfl, by simp [Val.asCtor, hc']⟩
    | str s => simp [Walk.known] at h
  | box => simp [Walk.known] at h
  | lvl l =>
    simp only [Walk.known] at h
    cases hl : here.facts.get? l with
    | none => rw [hl] at h; cases h
    | some f =>
      rw [hl] at h
      have hok := hf l f hl
      cases f with
      | ctor c' fs' =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨w', ws, hw', hws, hc⟩ := hok
        rw [hw] at hw'; cases hw'
        exact ⟨ws, hws, hc⟩
      | succ y =>
        obtain ⟨c', hc', he⟩ := Option.map_eq_some_iff.1 h
        cases he
        obtain ⟨m, hl', hy⟩ := hok
        rw [hw] at hl'; cases hl'
        exact ⟨[.lit (.nat m)], by simp [hy], by simp [Val.asCtor, hc']⟩
      | glob g => cases h
      | pap g as => cases h

/-- A known function head: the target value is a function global's closure
with the arguments it has. -/
theorem knownHead_sound {here : Here} {ρ' : List Val} (hf : FactsOk Q Valid here.facts ρ') {o : Opd}
    {g : GlobalId} {as0 : List Opd} (h : Walk.knownHead here o = some (g, as0)) {w : Val}
    (hw : o.val ρ' = some w) :
    ∃ gd ws0, Q.global? g = some gd ∧ as0.mapM (·.val ρ') = some ws0 ∧
      (∀ C ρ, Valid C ρ → C.prog.arity? g = some gd.ps.length) ∧ ws0.length < gd.ps.length ∧
      w = .clos [] gd.ps.length gd.body ws0 := by
  cases o with
  | lit l => simp [Walk.knownHead] at h
  | box => simp [Walk.knownHead] at h
  | lvl l =>
    simp only [Walk.knownHead] at h
    cases hl : here.facts.get? l with
    | none => rw [hl] at h; cases h
    | some f =>
      rw [hl] at h
      have hok := hf l f hl
      cases f with
      | glob g' =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨gd, hg, hps, ha, hl'⟩ := hok
        rw [hw] at hl'; cases hl'
        refine ⟨gd, [], hg, rfl, ha, ?_, rfl⟩
        cases hp : gd.ps with
        | nil => exact absurd hp hps
        | cons _ _ => simp
      | pap g' as' =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨gd, ws, hg, hws, ha, hlt, hl'⟩ := hok
        rw [hw] at hl'; cases hl'
        exact ⟨gd, ws, hg, hws, ha, hlt, rfl⟩
      | ctor _ _ => cases h
      | succ _ => cases h

/-- `tick^m e` charges `m` times. -/
theorem eval_ticks (k : Nat) (ρ : List Val) (J : List JClo) :
    ∀ (m : Nat) (e : Exp), eval P k ρ J (Walk.ticks m e) = Nat.repeat (fun f k => later k f) m
      (fun k => eval P k ρ J e) k
  | 0, e => rfl
  | m + 1, e => by
    simp only [Walk.ticks, Nat.repeat]
    rw [eval_tick]
    congr 1
    funext k'
    exact eval_ticks k' ρ J m e

theorem stripTicks_eq : ∀ {e : Exp} {m : Nat} {r : Exp}, Walk.stripTicks e = (m, r) → e = Walk.ticks m r
  | .tick e, m, r, h => by
    simp only [Walk.stripTicks] at h
    cases h' : Walk.stripTicks e with
    | mk m' r' =>
      rw [h'] at h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [stripTicks_eq h']; rfl
  | .bind .., m, r, h | .join .., m, r, h | .jump .., m, r, h | .case .., m, r, h | .ret _, m, r, h
  | .trap, m, r, h => by
    simp only [Walk.stripTicks, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; rfl

end Compilatrix.Anf.WalkProof
