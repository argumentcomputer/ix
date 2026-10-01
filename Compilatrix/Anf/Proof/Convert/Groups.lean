import Compilatrix.Anf.Proof.Convert.Cases

/-! # ANF conversion: applying a spine in groups

`groups` applies the head's operand to the spine's arguments group by
group: each group is an argument followed by the pure arguments after it,
evaluated first and applied with one `app` (one charge). On the Lam side the
pure arguments of a group evaluate to the same slots at every clock, so
evaluating them before the group's applications changes nothing
(`applyArgs_group`); applying the group is `app_sim`. The head of each next
group is the previous application's value (P1, M2.3). -/

set_option autoImplicit false

namespace Compilatrix.Anf.Convert.Proof

open Compilatrix.Sem (Result ClockMono SimUpTo later later_succ later_zero)
open Compilatrix.Lam (Kind Mode argSlot applyArgs)
open Compilatrix.Lam.ModesOk (TermOk NameArgOk ArgsOk GInfo hasName expected covered KindsSpec)
open Compilatrix.Ixon

theorem takeWhile_all {α : Type} (p : α → Bool) : ∀ (l : List α), ∀ x ∈ l.takeWhile p, p x = true
  | [], x, hx => by simp at hx
  | a :: l, x, hx => by
    simp only [List.takeWhile_cons] at hx
    split at hx
    · next hp =>
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hp
      · exact takeWhile_all p l x hx
    · simp at hx

theorem takeWhile_split {α : Type} (p : α → Bool) (l : List α) :
    l = l.takeWhile p ++ l.drop (l.takeWhile p).length := by
  conv => lhs; rw [← List.take_append_drop (l.takeWhile p).length l]
  rw [← List.prefix_iff_eq_take.1 (List.takeWhile_prefix p)]

/-- A group's pure arguments: Lam's interleaved order is the grouped one. -/
theorem applyArgs_group (L : Lam.Program) (k : Nat) (ρ : Lam.Env) (fv : Lam.Val)
    (a : Lam.Term × Mode) (run rest : List (Lam.Term × Mode)) (ss₀ : List Lam.Slot)
    (hrun : SlotsConst L k ρ run ss₀) (X : Lam.Val → Nat → Result Lam.Val) :
    (applyArgs L k ρ fv (a :: run ++ rest)).bind (X · k) =
      lamArgs L k ρ (a :: run) fun ss k =>
        (Lam.applyAll L k fv ss).bind fun g => (applyArgs L k ρ g rest).bind (X · k) := by
  rw [Lam.applyArgs_append, Result.bind_assoc, Lam.applyArgs_cons, lamArgs_cons, Result.bind_assoc]
  refine Result.bind_congr _ fun s => ?_
  have := lamArgs_pure L k ρ (fun g k => (applyArgs L k ρ g rest).bind (X · k)) run ss₀ hrun fv [s]
  simp only [List.singleton_append] at this
  rw [this]
  simp only [Lam.applyAll_cons, Lam.applyAll_nil, Result.bind_assoc, Result.bind_ok]

namespace Setting

variable {S : Setting} {n fuel : Nat}

theorem groups_step (ih : S.ConvAt n fuel) (hb : ∀ m < n, BodySim S.L S.Q S.A S.G m)
    {cx : Cx} {fo : Opd} {args : List (Lam.Term × Mode)} {k : Kont} {e : Exp} {ρ : Lam.Env}
    {ρ' : List Val} {J' : List JClo} {ks : List Kind} {SK : Lam.Val → Nat → Result Lam.Val}
    {tele : List Mode} {sigs : List (List Mode)} {i : Nat} {fv : Lam.Val} {w : Val}
    (h : groups S.A (fuel + 1) cx fo args k = .ok e) (henv : EnvR S.A S.G ks cx.vars ρ ρ')
    (hd : ρ'.length = cx.d) (hdj : J'.length = cx.dj) (hk : S.KontR n cx.dj k SK ρ' J')
    (hfo : fo.val ρ' = some w) (hhead : S.GroupHead tele sigs i fv w)
    (hargs : ArgsOk S.G ks tele sigs i args)
    (hcov : ∀ p, tele.getD p .strict = .name → p < i + args.length) :
    SimUpTo S.V n (fun k => (applyArgs S.L k ρ fv args).bind (SK · k))
      (fun k => eval S.Q k ρ' J' e) := by
  cases args with
  | nil =>
    rw [groups.eq_2 S.A (fuel + 1) cx fo k (Nat.succ_ne_zero _)] at h
    exact (pass_sim h hd hdj hk hfo (hhead.vr (by simpa using hcov))).congr
      (fun k => by rw [Lam.applyArgs_nil]; rfl) (fun _ => rfl)
  | cons a rest =>
    rw [groups.eq_3] at h
    have hsplit := takeWhile_split (pureArg cx.vars) rest
    have hpure := takeWhile_all (pureArg cx.vars) rest
    generalize rest.takeWhile (pureArg cx.vars) = run at h hsplit hpure
    generalize hr : rest.drop run.length = rest' at h hsplit
    subst hsplit
    obtain ⟨hargs₁, hargs₂⟩ := argsOk_append (S := S) (a :: run) rest' hargs
    obtain ⟨ss₀, hss₀⟩ := pure_slots (L := S.L) henv run hpure
    refine (ih.convArgs h henv hd hdj ?_ hargs₁).congr
      (fun k => applyArgs_group S.L k ρ fv a run rest' ss₀ (hss₀ k) SK) (fun _ => rfl)
    intro d' dj' os e'' ρ'' J'' hf hd' hρ hdj' hJ ss ⟨⟨ws, hws, hss⟩, hlen⟩
    dsimp only at hf
    have hw'' : fo.val ρ'' = some w := Opd.val_suffix hρ hfo
    have hbeval : ∀ k, evalBind S.Q k ρ'' (.app (fo.atom d') (os.map (·.atom d'))) =
        applyN S.Q k w ws := fun k => by
      rw [evalBind_app, ← hd', Opd.val_atom hw'', opds_eval hws]; rfl
    have hne : ss ≠ [] := by intro hs; rw [hs] at hlen; simp at hlen
    have hwl := hss.length
    -- the group's application
    have happ : SimUpTo (S.GroupHead tele sigs (i + ss.length)) n
        (fun k => Lam.applyAll S.L k fv ss) (fun k => applyN S.Q k w ws) := by
      rcases hhead with ⟨hv, hst⟩ | ⟨tk, hc, hcomp⟩
      · exact ((app_sim n hb ss.length).2 (Nat.le_refl _) hv (hss.strict hst 0) hne).weaken
          fun x y hxy => .inl ⟨hxy, fun p hp => hst p (by omega)⟩
      · exact ((app_sim n hb ss.length).1 (Nat.le_refl _) hc (hss.argsR hcomp) hne).weaken
          fun x y hxy => GroupHead.of_res hcomp hxy
    cases rest' with
    | nil =>
      -- the last group: a plain value for the continuation
      have hv : SimUpTo S.V n (fun k => Lam.applyAll S.L k fv ss)
          (fun k => evalBind S.Q k ρ'' (.app (fo.atom d') (os.map (·.atom d')))) :=
        (happ.weaken fun x y hxy => hxy.vr fun p hp => by
          have := hcov p hp; simp at this hlen ⊢; omega).congr (fun _ => rfl) hbeval
      exact (emit_sim hf hd' hdj' (hk.suffix hρ hJ hdj hdj') hv).congr
        (fun k => by simp only [Lam.applyArgs_nil, Result.bind_assoc, Result.bind_ok]) (fun _ => rfl)
    | cons x xs =>
      rw [emit] at hf
      obtain ⟨e3, he3, hf⟩ := Lam.ModesOk.bind_ok hf
      cases hf
      refine (SimUpTo.bind (evalBind_mono S.Q ρ'' _) (fun r' => eval_mono S.Q (r' :: ρ'') J'' e3)
        (happ.congr (fun _ => rfl) hbeval) fun r r' hrr => ?_).congr (fun _ => rfl)
        (fun k => eval_bind S.Q k ρ'' J'' _ _ e3)
      refine ih.groups he3 ((henv.suffix hρ).cons' r') (by simp [hd']) hdj'
        ((hk.suffix hρ hJ hdj hdj').suffix (List.suffix_cons r' ρ'') (List.suffix_refl _) hdj' hdj')
        (by rw [← hd']; exact Opd.val_lvl_top ρ'' r') hrr ?_ ?_
      · rw [hlen]; exact hargs₂
      · intro p hp; have := hcov p hp; simp at this hlen ⊢; omega

end Setting

end Compilatrix.Anf.Convert.Proof
