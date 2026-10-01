import Compilatrix.Anf.Proof.Walk.StepA

/-! # The rewriting walk: terms, continuations and join points

One fuel level of the walk's simulation for `walk` (returns, ticks, traps;
dispatch), `after` and `walkJoin` (dead join points, join points inlined at
their single jump, and emitted ones). An emitted join point's `JoinR` is
proved by Löb induction on the bound: its body is the walk of the source
body one clock down, with the join point itself (when recursive) related at
the smaller bound (M2.3). -/

set_option autoImplicit false

namespace Compilatrix.Anf.WalkProof

open Compilatrix.Sem (Result ClockMono SimUpTo later later_succ later_zero)
open Compilatrix.Anf.Rel (Pw)
open Walk (Ent JEnt Fact Here Cfg Kont Fires)

variable {P Q : Program} {Valid : Cfg → List Val → Prop} {Xc : Nat → List Val → Exp → Exp → Prop} {n fuel : Nat}

theorem KontW.of_KT {k : Kont} {J' : List JClo} {T : Val → Nat → Result Val} {SK : Val → Nat → Result Val}
    {ρ' : List Val} (hT : KT Q k J' = some T)
    (hs : ∀ x w, WV Q Valid Xc x w → SimUpTo (WV Q Valid Xc) n (SK x) (T w)) : KontW Q Valid Xc n k SK ρ' J' := by
  cases k with
  | cont f => cases hT
  | ret => exact ⟨T, hT, hs⟩
  | jump l => exact ⟨T, hT, hs⟩

/-! ## Terms -/

theorem walk_step (hW : WalkAt P Q Valid Xc n fuel) {C : Cfg} {env : Walk.Env} {here : Here} {e : Exp}
    {k : Kont} {out : Exp} {s s' : Fires} (h : (Walk.walk C (fuel + 1) env here e k).run s = .ok (out, s')) :
    ExpSim P Q Valid Xc n C out env here k e := by
  cases e with
  | bind c b body => rw [Walk.walk] at h; exact hW.walkBind h
  | join ar r b body => rw [Walk.walk] at h; exact hW.walkJoin h
  | jump j as => rw [Walk.walk] at h; exact hW.walkJump h
  | case x alts d => rw [Walk.walk] at h; exact hW.walkCase h
  | ret a =>
    rw [Walk.walk] at h
    obtain ⟨o, s1, h1, h2⟩ := Walk.run_bind_ok h
    intro ρ J ρ' J' live jlive SK hV henv hJ hd hdj hf hnd hk
    obtain ⟨rfl, v, w, hv, hw, hvw⟩ := resolve_rel' henv h1 fun i hi => by
      simpa [Exp.occ] using hnd.1 i hi
    exact (pass_sim h2 hd hdj hf hk hw hvw).congr (fun k => by rw [eval_ret', hv]; rfl) (fun _ => rfl)
  | tick body =>
    rw [Walk.walk] at h
    obtain ⟨o, s1, h1, h2⟩ := Walk.run_bind_ok h
    obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h2
    intro ρ J ρ' J' live jlive SK hV henv hJ hd hdj hf hnd hk
    have := hW.walk h1 ρ J ρ' J' live jlive SK hV henv hJ hd hdj hf hnd.tick hk
    exact (SimUpTo.tick (eval_mono P ρ J body) (eval_mono Q ρ' J' o) this).congr
      (fun k => by rw [eval_tick]) (fun k => by rw [eval_tick])
  | trap =>
    rw [Walk.walk] at h
    obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h
    intro ρ J ρ' J' live jlive SK hV henv hJ hd hdj hf hnd hk
    exact SimUpTo.trap.congr (fun k => by rw [eval_trap']; rfl) (fun k => eval_trap' Q k ρ' J')

/-! ## Continuations of inlined terms -/

/-- The meta-continuation that walks the rest of the caller. -/
theorem after_cont (hctx : Ctx P Q Valid Xc n) (hW : WalkAt P Q Valid Xc n fuel) {C : Cfg} {env : Walk.Env}
    {body : Exp} {k : Kont} {ρ : List Val} {J : List JClo} {ρ' : List Val} {J' : List JClo}
    {live jlive : List Bool} {SK : Val → Nat → Result Val} (hV : Valid C ρ')
    (henv : WEnv Q Valid Xc live env.σ ρ ρ') (hJ : JEnv P Q Valid Xc n (KT Q k J') ρ' J' jlive env.jσ J)
    (hnd : NoDead (true :: live) jlive body) (hk : KontW Q Valid Xc n k SK ρ' J') :
    KontW Q Valid Xc n (.cont fun here o => Walk.walk C fuel { σ := .opd o :: env.σ, jσ := env.jσ } here body k)
      (fun v k => (eval P k (v :: ρ) J body).bind (SK · k)) ρ' J' := by
  intro here' o e s s' ρ'' J'' hf hρ hJ' hd hdj hfacts x w hw hxw
  exact hW.walk hf (x :: ρ) J ρ'' J'' (true :: live) jlive SK (hctx.suffix C ρ' ρ'' hV hρ)
    (.live (.opd hw hxw) (henv.suffix hρ)) (hJ.suffixK hρ hJ') hd hdj hfacts hnd (hk.suffix hρ hJ')

theorem after_step (hctx : Ctx P Q Valid Xc n) (hW : WalkAt P Q Valid Xc n fuel) {C : Cfg} {env : Walk.Env}
    {body : Exp} {k k' : Kont} {s s' : Fires} (h : (Walk.after C (fuel + 1) env body k).run s = .ok (k', s'))
    (ρ : List Val) (J : List JClo) (ρ' : List Val) (J' : List JClo) (live jlive : List Bool)
    (SK : Val → Nat → Result Val) (hV : Valid C ρ') (henv : WEnv Q Valid Xc live env.σ ρ ρ')
    (hJ : JEnv P Q Valid Xc n (KT Q k J') ρ' J' jlive env.jσ J) (hnd : NoDead (true :: live) jlive body)
    (hk : KontW Q Valid Xc n k SK ρ' J') :
    KontW Q Valid Xc n k' (fun v k => (eval P k (v :: ρ) J body).bind (SK · k)) ρ' J' := by
  have hcont := after_cont hctx hW hV henv hJ hnd hk
  by_cases hret : body = .ret (.var 0)
  · subst hret
    rw [Walk.after] at h
    obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h
    have e : (fun v k => (eval P k (v :: ρ) J (.ret (.var 0))).bind (SK · k)) = SK := by
      funext v k; rw [eval_ret']; rfl
    rw [e]; exact hk
  by_cases hjmp : ∃ j, body = .jump j [.var 0]
  · obtain ⟨j, rfl⟩ := hjmp
    rw [Walk.after] at h
    split at h
    · next l σj jσj ar r b hj =>
      obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h
      have hlen := hJ.length
      have hjl := jlive_of_occ (hlen.1.trans hlen.2.symm) hj fun j' hj' e => by
        subst e; have := hnd.2 j' hj'; simp [Exp.jocc] at this
      obtain ⟨ρj, Jj, livej, jlj, jc', Tk, hJj, hl, hjc', hT, hR, -, -, -⟩ := hJ.get_emitted hj hjl
      have hKT : KT Q (.jump l) J' = some fun w k => jumpTo Q k jc' [w] := by
        simp only [KT, hl, if_true, hjc', Option.map_some]
      have hSK := hk.meaning hT
      refine KontW.of_KT hKT fun x w hxw => ?_
      refine (hR n (Nat.le_refl n) SK hSK [x] [w] (.cons hxw .nil)).congr (fun k => ?_) (fun _ => rfl)
      rw [eval_jump, hJj]; rfl
    · obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h
      exact hcont
  · rw [Walk.after.eq_4 C env body k fuel hret fun j e => hjmp ⟨j, e⟩] at h
    obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok h
    exact hcont

/-! ## Join points -/

/-- An emitted join point: jumping to the source and target join closures,
then continuations that match the walk continuation's target meaning,
simulates at every bound up to `n` (Löb induction on the bound). -/
theorem joinR_emit (hctx : Ctx P Q Valid Xc n) (hlow : ∀ m < n, WalkAt P Q Valid Xc m fuel) {C : Cfg}
    {env : Walk.Env} {here0 : Here} {ar : Nat} {r : Bool} {b b' : Exp} {k0 : Kont} {s s' : Fires}
    (hb : (Walk.walk C fuel
      { σ := Walk.entsOf (paramOpds here0.d ar) ++ env.σ,
        jσ := if r then JEnt.mk (some here0.dj) env.σ env.jσ ar r b :: env.jσ else env.jσ }
      { d := here0.d + ar, dj := if r then here0.dj + 1 else here0.dj, facts := here0.facts } b k0).run s =
        .ok (b', s'))
    {ρ ρ' : List Val} {J J'0 : List JClo} {live jlive : List Bool} {Tk : Val → Nat → Result Val}
    (hV : Valid C ρ') (henv : WEnv Q Valid Xc live env.σ ρ ρ')
    (hJ : JEnv P Q Valid Xc n (KT Q k0 J'0) ρ' J'0 jlive env.jσ J)
    (hd : here0.d = ρ'.length) (hdj : here0.dj = J'0.length) (hf : FactsOk Q Valid here0.facts ρ')
    (hnd : NoDead (List.replicate ar true ++ live) (if r then true :: jlive else jlive) b)
    (hT : KT Q k0 J'0 = some Tk) :
    JoinR P Q Valid Xc n Tk (.mk ρ J ar b r) (.mk ρ' J'0 ar b' r) := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
  intro hm SK hSK vs ws hvs
  have hwl := hvs.length
  by_cases har : vs.length = ar
  · have har' : ws.length = ar := by rw [hwl]; exact har
    refine (SimUpTo.later (c₁ := fun j => (eval P j (vs.reverse ++ ρ)
        (if r then JClo.mk ρ J ar b r :: J else J) b).bind (SK · (j + 1)))
      (c₂ := fun j => eval Q j (ws.reverse ++ ρ') (if r then JClo.mk ρ' J'0 ar b' r :: J'0 else J'0) b')
      fun m' hm' => ?_).congr (fun k => ?_) (fun k => ?_)
    · -- the body one clock down
      have hsuf : ρ' <:+ ws.reverse ++ ρ' := List.suffix_append _ _
      have hJsuf : J'0 <:+ (if r then JClo.mk ρ' J'0 ar b' r :: J'0 else J'0) := by
        split
        · exact List.suffix_cons _ _
        · exact List.suffix_refl _
      have hTb : KT Q k0 (if r then JClo.mk ρ' J'0 ar b' r :: J'0 else J'0) = some Tk := KT_suffix hJsuf hT
      have hJm := (hJ.mono (show m' ≤ n by omega)).suffixK hsuf hJsuf
      have henvb : WEnv Q Valid Xc (List.replicate ar true ++ live)
          (Walk.entsOf (paramOpds here0.d ar) ++ env.σ) (vs.reverse ++ ρ) (ws.reverse ++ ρ') := by
        have hp := paramOpds_val ρ' ws
        rw [har'] at hp
        have := WEnv.pushOpds hp hvs.reverse (henv.suffix hsuf)
        rw [paramOpds_length] at this; rw [hd]; exact this
      have hJb : JEnv P Q Valid Xc m' (KT Q k0 (if r then JClo.mk ρ' J'0 ar b' r :: J'0 else J'0))
          (ws.reverse ++ ρ') (if r then JClo.mk ρ' J'0 ar b' r :: J'0 else J'0)
          (if r then true :: jlive else jlive)
          (if r then JEnt.mk (some here0.dj) env.σ env.jσ ar r b :: env.jσ else env.jσ)
          (if r then JClo.mk ρ J ar b r :: J else J) := by
        cases r with
        | false => exact hJm
        | true =>
          simp only [if_true] at hJm hTb ⊢
          refine .emitted (by simp [hdj]) (by simp [hdj]) hTb
            (fun i hi => ih i (by omega) (by omega)) (henv.suffix hsuf) hJm (by simpa using hnd) hJm
      have hkb : KontW Q Valid Xc m' k0 (fun x j => SK x (j + 1)) (ws.reverse ++ ρ')
          (if r then JClo.mk ρ' J'0 ar b' r :: J'0 else J'0) :=
        KontW.of_KT hTb fun x w hxw =>
          SimUpTo.shift (KT_mono hT w) (((hSK x w hxw).mono_n (show m' + 1 ≤ m by omega)))
      exact (hlow m' (by omega)).walk hb (vs.reverse ++ ρ) _ (ws.reverse ++ ρ') _ _ _
        (fun x j => SK x (j + 1)) (hctx.suffix C ρ' _ hV hsuf) henvb hJb
        (by simp [hd, har']; omega) (by cases r <;> simp [hdj]) (hf.suffix hsuf) hnd hkb
    · simp only [jumpTo, har, if_true]
      exact later_bind_shift k _ _
    · simp only [jumpTo, har', if_true]
  · refine (SimUpTo.stuck (fun k => jumpTo Q k (.mk ρ' J'0 ar b' r) ws)).congr (fun k => ?_) (fun _ => rfl)
    simp only [jumpTo, har, if_false]; rfl

theorem walkJoin_step (hctx : Ctx P Q Valid Xc n) (hW : WalkAt P Q Valid Xc n fuel)
    (hlow : ∀ m < n, WalkAt P Q Valid Xc m fuel) {C : Cfg} {env : Walk.Env} {here : Here} {ar : Nat}
    {r : Bool} {b body : Exp} {k : Kont} {out : Exp} {s s' : Fires}
    (h : (Walk.walkJoin C (fuel + 1) env here ar r b body k).run s = .ok (out, s')) :
    ExpSim P Q Valid Xc n C out env here k (.join ar r b body) := by
  intro ρ J ρ' J' live jlive SK hV henv hJ hd hdj hf hnd hk
  rw [Walk.walkJoin] at h
  split at h
  · -- a dead join point
    next hc =>
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hc
    have h' := run_fire_then h
    exact (hW.walk h' ρ (.mk ρ J ar b r :: J) ρ' J' live (false :: jlive) SK hV henv (.dead hJ) hd hdj hf
      (hnd.join_rest false fun _ => hc.2) hk).congr (fun k => by rw [eval_join']) (fun _ => rfl)
  · split at h
    · -- inlined at its single jump
      next _ hc =>
      simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hc
      obtain ⟨⟨-, rfl⟩, -⟩ := hc
      have hb := hnd.join_body
      simp only [Bool.false_eq_true, if_false] at hb
      exact (hW.walk h ρ (.mk ρ J ar b false :: J) ρ' J' live (true :: jlive) SK hV henv
        (.once henv hJ hb hJ) hd hdj hf (hnd.join_rest true fun e => nomatch e) hk).congr
        (fun k => by rw [eval_join']) (fun _ => rfl)
    · -- emitted
      refine branch_sim h hd hdj hf hk fun here0 k0 out0 s0 s0' J'0 hrun hd0 hf0 hdj0 hJsuf hT0 hKT hk0 => ?_
      obtain ⟨b', s1, h1, hrun⟩ := Walk.run_bind_ok hrun
      obtain ⟨e', s2, h2, hrun⟩ := Walk.run_bind_ok hrun
      obtain ⟨rfl, rfl⟩ := Walk.run_pure_ok hrun
      obtain ⟨Tk, hTk⟩ := hT0
      have hJ0 : JEnv P Q Valid Xc n (KT Q k0 J'0) ρ' J'0 jlive env.jσ J := by
        rcases hKT with hKT | hKT
        · rw [hKT] at hJ; exact JEnv.retarget hJ
        · rw [hKT]; exact hJ.suffix (List.suffix_refl _) hJsuf
      have hd0' : here0.d = ρ'.length := by rw [hd0, hd]
      have hf0' : FactsOk Q Valid here0.facts ρ' := by rw [hf0]; exact hf
      have hR := joinR_emit hctx hlow h1 hV henv hJ0 hd0' hdj0 hf0' hnd.join_body hTk
      have hsuf : J'0 <:+ JClo.mk ρ' J'0 ar b' r :: J'0 := List.suffix_cons _ _
      have hJe := hJ0.suffixK (List.suffix_refl _) hsuf
      refine (hW.walk h2 ρ (.mk ρ J ar b r :: J) ρ' (.mk ρ' J'0 ar b' r :: J'0) live (true :: jlive) SK hV
        henv (.emitted (by simp [hdj0]) (by simp [hdj0]) (KT_suffix hsuf hTk) hR henv hJe hnd.join_body hJe)
        hd0' (by simp [hdj0]) hf0' (hnd.join_rest true fun e => nomatch e) (hk0.suffix (List.suffix_refl _) hsuf)).congr
        (fun k => by rw [eval_join']) (fun k => by rw [eval_join'])

end Compilatrix.Anf.WalkProof
