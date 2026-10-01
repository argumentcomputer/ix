import Compilatrix.Anf.Proof.Walk.CaseStep

/-! # The rewriting walk: kept and dropped bindings

The two ways the walk continues past a binding: it **emits** a target
binding whose value simulates the source's (and satisfies the fact the walk
records about it), or it **skips** it, mapping the source variable to an
operand, an inlined local function, or □ when nothing reads it. Also the
application equations behind known calls (a saturated application of a
function global's closure is a call; an over-saturated one is a call, then
an application of the rest) (M2.3). -/

set_option autoImplicit false

namespace Compilatrix.Anf.WalkProof

open Compilatrix.Sem (Result ClockMono SimUpTo later later_succ later_zero)
open Compilatrix.Anf.Rel (Pw)
open Walk (Ent JEnt Fact Here Cfg Kont Fires)

/-! ## Simulations with more about the target value -/

theorem refines_strengthen {α β : Type} {R : α → β → Prop} {S : β → Prop} :
    ∀ {s : Result α} {t : Result β}, Sem.Result.Refines R s t → (∀ w, t = .ok w → S w) →
      Sem.Result.Refines (fun v w => R v w ∧ S w) s t
  | _, _, .ok hvw, hS => .ok ⟨hvw, hS _ rfl⟩
  | _, _, .timeout, _ => .timeout
  | _, _, .trap, _ => .trap
  | _, _, .stuck, _ => .stuck
  | _, _, .resource f, _ => .resource f

theorem _root_.Compilatrix.Sem.SimUpTo.strengthen {α β : Type} {R : α → β → Prop} {S : β → Prop} {n : Nat}
    {c₁ : Nat → Result α} {c₂ : Nat → Result β} (h : SimUpTo R n c₁ c₂)
    (hS : ∀ k w, c₂ k = .ok w → S w) : SimUpTo (fun v w => R v w ∧ S w) n c₁ c₂ where
  fwd k hk hne := by
    obtain ⟨k', h'⟩ := h.fwd k hk hne
    exact ⟨k', refines_strengthen h' fun w hw => hS k' w hw⟩
  tmo := h.tmo

theorem refines_unmap {α β γ : Type} {R : α → β → Prop} {f : γ → β} {s : Result α} :
    ∀ {t : Result γ}, Sem.Result.Refines R s (t.map f) → Sem.Result.Refines (fun v w => R v (f w)) s t
  | .ok w, h => by
    simp only [Result.map, Result.bind] at h
    cases h with
    | ok hvw => exact .ok hvw
    | stuck => exact .stuck
  | .timeout, h => by cases h with | timeout => exact .timeout | stuck => exact .stuck
  | .trap, h => by cases h with | trap => exact .trap | stuck => exact .stuck
  | .stuck, h => by cases h with | stuck => exact .stuck
  | .resource r, h => by
    simp only [Result.map, Result.bind] at h
    exact .resource r

theorem _root_.Compilatrix.Sem.SimUpTo.unmap {α β γ : Type} {R : α → β → Prop} {f : γ → β} {n : Nat}
    {c₁ : Nat → Result α} {c₂ : Nat → Result β} {c₂' : Nat → Result γ} (h : SimUpTo R n c₁ c₂)
    (hmap : ∀ k, c₂ k = (c₂' k).map f) : SimUpTo (fun v w => R v (f w)) n c₁ c₂' where
  fwd k hk hne := by
    obtain ⟨k', h'⟩ := h.fwd k hk hne
    rw [hmap] at h'
    exact ⟨k', refines_unmap h'⟩
  tmo k hk ht := by
    have := h.tmo k hk ht
    rw [hmap] at this
    cases hc : c₂' k with
    | timeout => exact .inl rfl
    | resource r => exact .inr ⟨r, rfl⟩
    | ok w => rw [hc] at this; simp [Result.map, Result.bind] at this
    | trap => rw [hc] at this; simp [Result.map, Result.bind] at this
    | stuck => rw [hc] at this; simp [Result.map, Result.bind] at this

theorem clockMono_map {α β : Type} {c : Nat → Result α} {f : α → β} (h : ClockMono c) :
    ClockMono fun k => (c k).map f :=
  ClockMono.bind h fun _ => fun _ _ _ _ => rfl

/-! ## Applications of known closures -/

variable {Q : Program}

theorem applyN_exact_call {k N : Nat} {body : Exp} {ws0 ws : List Val} (hlt : ws0.length < N)
    (heq : ws0.length + ws.length = N) {gd : GDef} (hgd : gd.ps.length = N) (hb : gd.body = body) :
    applyN Q k (.clos [] N body ws0) ws = callVal Q k gd (ws0 ++ ws) := by
  cases ws with
  | nil => simp at heq; omega
  | cons w rest =>
    simp only [List.length_cons] at heq
    have hall : (ws0 ++ w :: rest).length = N := by simp; omega
    have hn : ¬ (ws0.length + (w :: rest).length < N) := by simp; omega
    rw [applyN_clos]
    simp only [if_pos hlt, if_neg hn]
    unfold callVal
    rw [if_pos (by rw [hall, hgd])]
    cases k with
    | zero => rfl
    | succ k =>
      simp only [later_succ, enter, List.append_nil, hb]
      rw [List.take_of_length_le (by omega), List.drop_of_length_le (by omega)]
      simp only [applyN_nil']
      cases eval Q k (ws0 ++ w :: rest).reverse [] body <;> rfl

theorem applyN_over_call {k N : Nat} {body : Exp} {ws0 ws : List Val} (hlt : ws0.length < N)
    (hgt : N < ws0.length + ws.length) {gd : GDef} (hgd : gd.ps.length = N) (hb : gd.body = body) :
    applyN Q k (.clos [] N body ws0) ws =
      (callVal Q k gd ((ws0 ++ ws).take N)).bind fun r => applyN Q k r ((ws0 ++ ws).drop N) := by
  cases ws with
  | nil => simp at hgt; omega
  | cons w rest =>
    simp only [List.length_cons] at hgt
    have hn : ¬ (ws0.length + (w :: rest).length < N) := by simp; omega
    have htl : ((ws0 ++ w :: rest).take N).length = gd.ps.length := by
      rw [List.length_take, hgd]; simp; omega
    rw [applyN_clos]
    simp only [if_pos hlt, if_neg hn]
    unfold callVal
    rw [if_pos htl]
    cases k with
    | zero => rfl
    | succ k => simp only [later_succ, enter, List.append_nil, hb]

theorem applyN_under {k N : Nat} {ρ : List Val} {body : Exp} {got vs : List Val}
    (hlt : got.length + vs.length < N) (hv : vs ≠ []) :
    applyN Q k (.clos ρ N body got) vs = later k fun _ => .ok (.clos ρ N body (got ++ vs)) := by
  cases vs with
  | nil => exact absurd rfl hv
  | cons v rest =>
    rw [applyN_clos]
    have h1 : got.length < N := by simp at hlt; omega
    simp only [h1, if_true, hlt]

variable {Valid : Cfg → List Val → List Val → List (Val × Val) → Prop} {Xc : Nat → List Val → Exp → Exp → Prop} {C : Cfg}

/-- A source value related to an unsaturated target closure is an
unsaturated closure missing as many arguments. -/
theorem WV.clos_inv {v : Val} {ρ' : List Val} {m : Nat} {b' : Exp} {got' : List Val}
    (h : WV Q Valid Xc v (.clos ρ' m b' got')) (hlt : got'.length < m) :
    ∃ ρ n b got, v = .clos ρ n b got ∧ got.length < n ∧ n - got.length = m - got'.length := by
  cases h with
  | idc hρ hg => have := hg.length; exact ⟨_, _, _, _, rfl, by omega, by omega⟩
  | walkc _ _ _ _ _ _ hmn hng hgn hgg _ _ _ _ => exact ⟨_, _, _, _, rfl, hgn, by omega⟩
  | xc hρ hg _ => have := hg.length; exact ⟨_, _, _, _, rfl, by omega, by omega⟩

/-! ## Emitting and skipping a binding -/

variable {P : Program} {n fuel : Nat}

theorem FactsOk.push {facts : Src.NatMap Fact} {ρ' : List Val} (h : FactsOk Q Valid facts ρ') (w : Val) :
    FactsOk Q Valid facts (w :: ρ') :=
  h.suffix (List.suffix_cons _ _)

theorem FactsOk.insert {facts : Src.NatMap Fact} {ρ' : List Val} (h : FactsOk Q Valid facts ρ') {w : Val}
    {f : Fact} (hf : FactOk Q Valid (w :: ρ') ρ'.length f) :
    FactsOk Q Valid (facts.insert ρ'.length f) (w :: ρ') := by
  intro l f' hl
  rw [Src.NatMap.get?_insert] at hl
  split at hl
  · next hll => subst hll; simp only [Option.some.injEq] at hl; subst hl; exact hf
  · exact (h l f' hl).suffix (List.suffix_cons _ _)

/-- A kept binding: its value simulates, and the facts recorded about it
hold of the target value. -/
theorem emit_sim (hctx : Ctx P Q Valid Xc n) (hW : WalkAt P Q Valid Xc n fuel) {C : Cfg} {env : Walk.Env}
    {here : Here} {c c' : Ixon.V3.LetContract} {b b' : Bind} {body e : Exp} {k : Kont} {s s' : Fires}
    {facts' : Src.NatMap Fact}
    (he : (Walk.walk C fuel { σ := .opd (.lvl here.d) :: env.σ, jσ := env.jσ }
      { d := here.d + 1, dj := here.dj, facts := facts' } body k).run s = .ok (e, s'))
    {ρ : List Val} {J : List JClo} {ρ' : List Val} {J' : List JClo} {live jlive : List Bool}
    {SK : Val → Nat → Result Val} (hV : VOk Q Valid Xc C ρ ρ') (henv : WEnv Q Valid Xc C live env.σ ρ ρ')
    (hJ : JEnv P Q Valid Xc C n (KT Q k J') ρ' J' jlive env.jσ J) (hd : here.d = ρ'.length)
    (hdj : here.dj = J'.length) (hnd : NoDead live jlive (.bind c b body)) (hk : KontW Q Valid Xc n k SK ρ' J')
    (hb : SimUpTo (fun v w => WV Q Valid Xc v w ∧ FactsOk Q Valid facts' (w :: ρ')) n
      (fun k => evalBind P k ρ b) (fun k => evalBind Q k ρ' b')) :
    SimUpTo (WV Q Valid Xc) n (fun k => (eval P k ρ J (.bind c b body)).bind (SK · k))
      (fun k => eval Q k ρ' J' (.bind c' b' e)) := by
  refine (SimUpTo.bind (d := fun v k => (eval P k (v :: ρ) J body).bind (SK · k)) (evalBind_mono Q ρ' b') (fun w => eval_mono Q (w :: ρ') J' e) hb
    fun v w hvw => ?_).congr (fun k => ?_) (fun k => eval_bind Q k ρ' J' c' b' e)
  · have hsuf : ρ' <:+ w :: ρ' := List.suffix_cons _ _
    exact hW.walk he (v :: ρ) J (w :: ρ') J' (true :: live) jlive SK (hctx.vsuffix hV (List.suffix_cons _ _) hsuf)
      (.live (.opd (by rw [hd]; exact Opd.val_lvl_top ρ' w) hvw.1) (henv.suffix hsuf))
      (hJ.suffixK hsuf (List.suffix_refl _)) (by simp [hd]) hdj hvw.2
      (hnd.bind_body true fun e => nomatch e) (hk.suffix hsuf (List.suffix_refl _))
  · rw [eval_bind, bind_assoc']

/-- The body after a skipped binding, for a source value the entry
describes (or □ for a value nothing reads). -/
theorem skip_core (hW : WalkAt P Q Valid Xc n fuel) {C : Cfg} {env : Walk.Env} {here : Here}
    {c : Ixon.V3.LetContract} {b : Bind} {body e : Exp} {k : Kont} {s s' : Fires} {ent : Ent}
    (he : (Walk.walk C fuel { σ := ent :: env.σ, jσ := env.jσ } here body k).run s = .ok (e, s'))
    {ρ : List Val} {J : List JClo} {ρ' : List Val} {J' : List JClo} {live jlive : List Bool}
    {SK : Val → Nat → Result Val} (hV : ∀ v, VOk Q Valid Xc C (v :: ρ) ρ') (henv : WEnv Q Valid Xc C live env.σ ρ ρ')
    (hJ : JEnv P Q Valid Xc C n (KT Q k J') ρ' J' jlive env.jσ J) (hd : here.d = ρ'.length)
    (hdj : here.dj = J'.length) (hf : FactsOk Q Valid here.facts ρ') (hnd : NoDead live jlive (.bind c b body))
    (hk : KontW Q Valid Xc n k SK ρ' J') {v : Val}
    (hent : WEnt Q Valid Xc C ent v ρ' ∨ (ent = .opd .box ∧ body.occ 0 = 0)) :
    SimUpTo (WV Q Valid Xc) n (fun k => (eval P k (v :: ρ) J body).bind (SK · k)) (fun k => eval Q k ρ' J' e) := by
  rcases hent with hent | ⟨rfl, hocc⟩
  · exact hW.walk he (v :: ρ) J ρ' J' (true :: live) jlive SK (hV v) (.live hent henv) hJ hd hdj hf
      (hnd.bind_body true fun e => nomatch e) hk
  · exact hW.walk he (v :: ρ) J ρ' J' (false :: live) jlive SK (hV v) (.dead henv) hJ hd hdj hf
      (hnd.bind_body false fun _ => hocc) hk

/-- A skipped binding whose right-hand side is pure (no clock). -/
theorem skip_sim (hW : WalkAt P Q Valid Xc n fuel) {C : Cfg} {env : Walk.Env} {here : Here}
    {c : Ixon.V3.LetContract} {b : Bind} {body e : Exp} {k : Kont} {s s' : Fires} {ent : Ent}
    (he : (Walk.walk C fuel { σ := ent :: env.σ, jσ := env.jσ } here body k).run s = .ok (e, s'))
    {ρ : List Val} {J : List JClo} {ρ' : List Val} {J' : List JClo} {live jlive : List Bool}
    {SK : Val → Nat → Result Val} (hV : ∀ v, VOk Q Valid Xc C (v :: ρ) ρ') (henv : WEnv Q Valid Xc C live env.σ ρ ρ')
    (hJ : JEnv P Q Valid Xc C n (KT Q k J') ρ' J' jlive env.jσ J) (hd : here.d = ρ'.length)
    (hdj : here.dj = J'.length) (hf : FactsOk Q Valid here.facts ρ') (hnd : NoDead live jlive (.bind c b body))
    (hk : KontW Q Valid Xc n k SK ρ' J')
    (hr : (∀ k, evalBind P k ρ b = .stuck) ∨ ∃ v, (∀ k, evalBind P k ρ b = .ok v) ∧
      (WEnt Q Valid Xc C ent v ρ' ∨ (ent = .opd .box ∧ body.occ 0 = 0))) :
    SimUpTo (WV Q Valid Xc) n (fun k => (eval P k ρ J (.bind c b body)).bind (SK · k))
      (fun k => eval Q k ρ' J' e) := by
  rcases hr with hst | ⟨v, hv, hent⟩
  · exact (SimUpTo.stuck _).congr (fun k => by rw [eval_bind, hst]; rfl) (fun _ => rfl)
  · exact (skip_core hW he hV henv hJ hd hdj hf hnd hk hent).congr
      (fun k => by rw [eval_bind, hv]; rfl) (fun _ => rfl)

/-- A skipped binding that charges once (an unsaturated application): the
charge becomes a tick. -/
theorem skip_tick_sim (hW : WalkAt P Q Valid Xc n fuel) {C : Cfg} {env : Walk.Env} {here : Here}
    {c : Ixon.V3.LetContract} {b : Bind} {body e : Exp} {k : Kont} {s s' : Fires} {ent : Ent}
    (he : (Walk.walk C fuel { σ := ent :: env.σ, jσ := env.jσ } here body k).run s = .ok (e, s'))
    {ρ : List Val} {J : List JClo} {ρ' : List Val} {J' : List JClo} {live jlive : List Bool}
    {SK : Val → Nat → Result Val} (hV : ∀ v, VOk Q Valid Xc C (v :: ρ) ρ') (henv : WEnv Q Valid Xc C live env.σ ρ ρ')
    (hJ : JEnv P Q Valid Xc C n (KT Q k J') ρ' J' jlive env.jσ J) (hd : here.d = ρ'.length)
    (hdj : here.dj = J'.length) (hf : FactsOk Q Valid here.facts ρ') (hnd : NoDead live jlive (.bind c b body))
    (hk : KontW Q Valid Xc n k SK ρ' J') {v : Val}
    (hr : (∀ k, evalBind P k ρ b = later k fun _ => .ok v) ∨ (∀ k, evalBind P k ρ b = .ok v))
    (hent : WEnt Q Valid Xc C ent v ρ' ∨ (ent = .opd .box ∧ body.occ 0 = 0)) :
    SimUpTo (WV Q Valid Xc) n (fun k => (eval P k ρ J (.bind c b body)).bind (SK · k))
      (fun k => eval Q k ρ' J' (.tick e)) := by
  have hin := skip_core hW he hV henv hJ hd hdj hf hnd hk hent
  rcases hr with hr | hr
  · refine (SimUpTo.tick (c := fun _ => .ok v) (d := fun v k => (eval P k (v :: ρ) J body).bind (SK · k))
      (fun _ _ _ _ => rfl) (eval_mono Q ρ' J' e) (hin.congr (fun _ => rfl) (fun _ => rfl))).congr
      (fun k => ?_) (fun k => eval_tick Q k ρ' J' e)
    rw [eval_bind, hr, bind_assoc']
  · refine (hin.laterR (eval_mono Q ρ' J' e)).congr (fun k => ?_) (fun k => eval_tick Q k ρ' J' e)
    rw [eval_bind, hr]; rfl

end Compilatrix.Anf.WalkProof
