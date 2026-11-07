import IxCC.Anf.Proof.Convert.SpineVar

/-! # ANF conversion: spines headed by a function global

With at least its arity of arguments, the spine becomes the arguments
followed by one `call`; Lam evaluates the global's value (one charge) before
the arguments, and its partial applications at a positive clock only build
closures, so the grouped Lam order (`call_source`) simulates; an impure
argument gets a leading `tick` (`SimUpTo.tickConst`). With fewer arguments,
the global's closure (free in Anf) is applied in groups, behind a `tick` when
the first argument is impure (P1, M2.3). -/

set_option autoImplicit false

namespace IxCC.Anf.Convert.Proof

open IxCC.Sem (Result ClockMono SimUpTo later later_succ later_zero)
open IxCC.Lam (Kind Mode argSlot applyArgs)
open IxCC.Lam.ModesOk (TermOk NameArgOk ArgsOk GInfo hasName expected covered KindsSpec sigsOf)
open IxCC.Ixon

namespace Setting

variable {S : Setting} {n fuel : Nat}

/-- Lam's spine on a function global's closure, at a positive clock: the
call's arguments in order, then the body one clock down, then the rest. -/
theorem call_source (k : Nat) (hk : 1 ≤ k) (ρ : Lam.Env) {ps : List (Mode × V3.BinderContract)}
    {body : Lam.Term} {args : List (Lam.Term × Mode)}
    (hle : ps.length + 1 ≤ args.length) (SK : Lam.Val → Nat → Result Lam.Val) :
    (applyArgs S.L k ρ (.clos [] (lamsWith ps body)) args).bind (SK · k) =
      lamArgs S.L k ρ (args.take (ps.length + 1)) fun ss k =>
        (later k fun k => Lam.eval S.L k ss.reverse body).bind fun r =>
          (applyArgs S.L k ρ r (args.drop (ps.length + 1))).bind (SK · k) := by
  conv => lhs; rw [← List.take_append_drop (ps.length + 1) args]
  rw [Lam.applyArgs_append, applyArgs_tele S.L k hk ρ body _ ps [] (by simp; omega),
    Result.bind_assoc, lamArgs_bind]
  refine lamArgs_congr_len S.L k ρ _ fun ss hss => ?_
  rw [applyAll_tele S.L k body ps [] ss (by simp at hss; omega)]
  simp only [List.append_nil, Result.bind_assoc]

/-- Applying a closure at clock zero after a pure first argument times out. -/
theorem applyArgs_zero_pure {ks : List Kind} {vars : List VarInfo} {ρ : Lam.Env} {ρt : List Val}
    (henv : EnvR S.A S.G ks vars ρ ρt) {a1 : Lam.Term × Mode} {rest : List (Lam.Term × Mode)}
    (hp : pureArg vars a1 = true) (ρc : Lam.Env) (b : Lam.Term) (X : Lam.Val → Result Lam.Val) :
    (applyArgs S.L 0 ρ (.clos ρc b) (a1 :: rest)).bind X = .timeout := by
  obtain ⟨ss, hss⟩ := pure_slots (L := S.L) henv [a1] (by simpa using hp)
  obtain ⟨s, _, rfl, hs, _⟩ := hss 0
  rw [Lam.applyArgs_cons, hs, Result.bind_ok, apply_clos_later]
  rfl

theorem spine_fun (ih : S.ConvAt n fuel) (hb : ∀ m < n, BodySim S.L S.Q S.A S.G m)
    {cx : Cx} {f a : Lam.Term} {m : Mode} {k : Kont} {e : Exp} {ρ : Lam.Env} {ρ' : List Val}
    {J' : List JClo} {ks : List Kind} {SK : Lam.Val → Nat → Result Lam.Val}
    (henv : EnvR S.A S.G ks cx.vars ρ ρ') (hd : ρ'.length = cx.d) (hdj : J'.length = cx.dj)
    (hk : S.KontR n cx.dj k SK ρ' J') {g : Lam.GlobalId} {args : List (Lam.Term × Mode)}
    (hsp : (Lam.Term.app f a m).spine = (.glob g, args)) {nn : Nat}
    (hA : S.A.get? g = some (nn + 1))
    (hcov : covered ((S.G.get? g).getD {}).tele args.length = true)
    (hargs : ArgsOk S.G ks ((S.G.get? g).getD {}).tele ((S.G.get? g).getD {}).sigs 0 args)
    (h : spine S.A (fuel + 1) cx (.app f a m) k = .ok e) :
    SimUpTo S.V n (fun k => (Lam.eval S.L k ρ (.glob g)).bind fun fv =>
      (applyArgs S.L k ρ fv args).bind (SK · k)) (fun k => eval S.Q k ρ' J' e) := by
  have hne : args ≠ [] := by have := spine_app_ne f a m; rwa [hsp] at this
  rw [spine.eq_2, hsp] at h
  simp only [hA] at h
  obtain ⟨gl, gd, gi, kinds, hgl, hgd, hgi, hn, hps, hconv, htele, hsigs, hma, htm⟩ := S.glob hA
  rw [hgi] at hcov hargs
  simp only [Option.getD_some] at hcov hargs
  have hcov' := covered_spec hcov
  have hcomp : Compat gi.tele gi.sigs kinds := by rw [htele, hsigs]; exact compat_glob hma
  have hbody : gl.body = lamsWith (telescope gl.body).1 (telescope gl.body).2 :=
    (lamsWith_telescope gl.body).symm
  have hnl := notLam_telescope gl.body
  generalize (telescope gl.body).1 = ps at hn hconv htele hma hbody
  generalize (telescope gl.body).2 = body at hconv htm hbody hnl
  have hkl : kinds.length = ps.length := hma.1.symm
  obtain ⟨p, ps', rfl⟩ : ∃ p ps', ps = p :: ps' := by
    cases ps with
    | nil => simp at hn
    | cons p ps' => exact ⟨p, ps', rfl⟩
  have hnn : nn = ps'.length := by simp at hn; omega
  subst hnn
  -- the global's closures
  have hevalL : ∀ k, Lam.eval S.L k ρ (.glob g) = later k fun _ => .ok (.clos [] (lamsWith ps' body)) :=
    fun k => lam_eval_glob_fun S.L hgl hbody k ρ
  have hglobQ : ∀ k ρ'', evalBind S.Q k ρ'' (.glob g) = .ok (.clos [] (ps'.length + 1) gd.body []) := by
    intro k ρ''
    rw [evalBind_glob, hgd]
    simp only [Result.ofOption, Result.bind_ok, globVal]
    split
    · next hg => rw [hg] at hps; simp at hps
    · rw [hps]
  have hconv' : conv S.A (fuelFor gl.body)
      { vars := pushParams [] ([] : List Val).length ((p :: ps').map (·.1 == .name)),
        d := ([] : List Val).length + (p :: ps').length, dj := 0 } body .ret = .ok gd.body := by
    rw [modesAgree_thunks hma]; simpa using hconv
  have hclo : CloR S.A S.G kinds 0 (.clos [] (lamsWith ps' body)) (.clos [] (ps'.length + 1) gd.body []) :=
    .mk (ss := []) (got := []) hnl hma (by simp) .nil .nil hconv' (by simpa using htm) rfl
      (by simp) (by simp)
  by_cases hle : ps'.length + 1 ≤ args.length
  · -- a call: the arguments, then the call, then the rest in groups
    rw [if_pos hle] at h
    obtain ⟨e0, he0, rfl⟩ := except_map_ok h
    obtain ⟨hargs₁, hargs₂⟩ := argsOk_append (S := S) (args.take (ps'.length + 1))
      (args.drop (ps'.length + 1)) (by rwa [List.take_append_drop])
    have hD := ih.convArgs he0 henv hd hdj (SKS := fun ss k =>
        (later k fun k => Lam.eval S.L k ss.reverse body).bind fun r =>
          (applyArgs S.L k ρ r (args.drop (ps'.length + 1))).bind (SK · k)) ?_ hargs₁
    · cases himp : (args.take (ps'.length + 1)).all (pureArg cx.vars)
      · -- an impure argument: a leading tick
        simp only [himp, Bool.not_false, if_true]
        refine (SimUpTo.tickConst (eval_mono S.Q ρ' J' e0) hD fun k hk => ?_).congr
          (fun k => by rw [hevalL]) (fun k => eval_tick S.Q k ρ' J' e0)
        exact call_source k hk ρ (by simpa using hle) SK
      · -- pure arguments: Lam's charge at the global is Anf's at the call
        simp only [himp, Bool.not_true, Bool.false_eq_true, if_false]
        refine hD.congr (fun k => ?_) (fun _ => rfl)
        cases k with
        | zero =>
          rw [hevalL]
          obtain ⟨ss, hss⟩ := pure_slots (L := S.L) henv (args.take (ps'.length + 1))
            (fun x hx => List.all_eq_true.1 himp x hx)
          rw [lamArgs_const (hss 0)]
          rfl
        | succ k =>
          rw [hevalL, later_succ, Result.bind_ok]
          exact call_source (k + 1) (by omega) ρ (by simpa using hle) SK
    · intro d' dj' os e'' ρ'' J'' hf hd' hρ hdj' hJ ss ⟨⟨ws, hws, hss⟩, hlen⟩
      dsimp only at hf
      have hsl : ss.length = ps'.length + 1 := by rw [hlen]; simp; omega
      have hwl : ws.length = ps'.length + 1 := by rw [hss.length, hsl]
      have hslots : SlotsR S.A S.G kinds ss ws := by
        have := (hss.argsR hcomp).slots (by simp [hsl, hkl])
        simpa using this
      have henvb : EnvR S.A S.G kinds.reverse (pushParams [] 0 (kinds.map Kind.isName)) ss.reverse
          ws.reverse := by
        simpa using (EnvR.nil (A := S.A) (G := S.G) (ρt := [])).push hslots (by rw [hkl, hsl]; simp)
      have hcall : ∀ k, evalBind S.Q k ρ'' (.call g (os.map (·.atom d'))) =
          later k fun k => eval S.Q k ws.reverse [] gd.body := fun k =>
        evalBind_call_of S.Q k ρ'' hgd (by rw [← hd']; exact opds_eval hws) (by rw [hwl, hps])
      have hbodysim : SimUpTo S.V n (fun k => later k fun k => Lam.eval S.L k ss.reverse body)
          (fun k => evalBind S.Q k ρ'' (.call g (os.map (·.atom d')))) :=
        (SimUpTo.later fun m' hm' => hb m' (by omega) hconv (by simp [hwl]) henvb
          (by simpa using htm)).congr (fun _ => rfl) hcall
      cases hrest : args.drop (ps'.length + 1) with
      | nil =>
        rw [hrest] at hf
        exact (emit_sim hf hd' hdj' (hk.suffix hρ hJ hdj hdj') hbodysim).congr
          (fun k => by simp only [Lam.applyArgs_nil, Result.bind_assoc, Result.bind_ok]) (fun _ => rfl)
      | cons x xs =>
        rw [hrest] at hf hargs₂
        rw [emit] at hf
        obtain ⟨e3, he3, hf⟩ := Lam.ModesOk.bind_ok hf
        cases hf
        refine (SimUpTo.bind (evalBind_mono S.Q ρ'' _) (fun r' => eval_mono S.Q (r' :: ρ'') J'' e3)
          hbodysim fun r r' hrr => ?_).congr (fun _ => rfl) (fun k => eval_bind S.Q k ρ'' J'' _ _ e3)
        refine ih.groups (tele := gi.tele) (sigs := gi.sigs) (i := ps'.length + 1) he3
          ((henv.suffix hρ).cons' r') (by simp [hd']) hdj'
          ((hk.suffix hρ hJ hdj hdj').suffix (List.suffix_cons r' ρ'') (List.suffix_refl _) hdj' hdj')
          (by rw [← hd']; exact Opd.val_lvl_top ρ'' r') (.inl ⟨hrr, fun p' hp' => ?_⟩) ?_ ?_
        · rw [htele, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]; rfl
        · simpa [Nat.min_eq_left hle] using hargs₂
        · intro p' hp'
          have := hcov' p' hp'
          have hlen' : args.length = ps'.length + 1 + (x :: xs).length := by
            rw [← hrest, List.length_drop]; omega
          omega
  · -- a partial application: the closure, then the arguments in groups
    rw [if_neg hle] at h
    obtain ⟨e0, he0, rfl⟩ := except_map_ok h
    rw [emit] at he0
    obtain ⟨e3, he3, he0⟩ := Lam.ModesOk.bind_ok he0
    cases he0
    have hG := ih.groups he3 (henv.cons' (.clos [] (ps'.length + 1) gd.body [])) (by simp [hd]) hdj
      (hk.suffix (List.suffix_cons _ ρ') (List.suffix_refl _) hdj hdj)
      (by rw [← hd]; exact Opd.val_lvl_top ρ' _) (.inr ⟨kinds, hclo, hcomp⟩) hargs
      (fun p' hp' => by have := hcov' p' hp'; omega)
    have hT : ∀ k, eval S.Q k ρ' J' (.bind freshLet (.glob g) e3) =
        eval S.Q k (.clos [] (ps'.length + 1) gd.body [] :: ρ') J' e3 := fun k => by
      rw [eval_bind, hglobQ]; rfl
    obtain ⟨a1, rest1, rfl⟩ := List.exists_cons_of_ne_nil hne
    cases himp : pureArg cx.vars a1
    · -- an impure first argument: a leading tick
      simp only [himp, Bool.not_false, if_true]
      refine (SimUpTo.tickConst (eval_mono S.Q _ J' e3) hG fun k _ => rfl).congr
        (fun k => by rw [hevalL]) (fun k => by rw [eval_tick, later_congr k hT])
    · simp only [himp, Bool.not_true, Bool.false_eq_true, if_false]
      refine hG.congr (fun k => ?_) hT
      cases k with
      | zero => rw [hevalL, later_zero, applyArgs_zero_pure henv himp]; rfl
      | succ k => rw [hevalL, later_succ, Result.bind_ok]

end Setting

end IxCC.Anf.Convert.Proof
