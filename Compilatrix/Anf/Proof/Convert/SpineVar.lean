import Compilatrix.Anf.Proof.Convert.SpineBase

/-! # ANF conversion: spines headed by a variable or another term

A `name` variable's thunk is forced (`app x [□]`), giving a minor
telescope closure or a plain value; a strict variable's value and any other
head's value are plain. Then the arguments are applied in groups (P1,
M2.3). -/

set_option autoImplicit false

namespace Compilatrix.Anf.Convert.Proof

open Compilatrix.Sem (Result ClockMono SimUpTo later later_succ later_zero)
open Compilatrix.Lam (Kind Mode argSlot applyArgs)
open Compilatrix.Lam.ModesOk (TermOk NameArgOk ArgsOk GInfo hasName expected covered KindsSpec sigsOf)
open Compilatrix.Ixon

theorem hasName_false_getD {ms : List Mode} (h : hasName ms = false) (p : Nat) :
    ms.getD p .strict = .strict := by
  unfold hasName at h
  rw [List.any_eq_false] at h
  rcases Nat.lt_or_ge p ms.length with hp | hp
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp, Option.getD_some]
    have := h ms[p] (List.getElem_mem hp)
    cases hm : ms[p] with
    | strict => rfl
    | name => rw [hm] at this; simp at this
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hp]; rfl

namespace Setting

variable {S : Setting} {n fuel : Nat}

theorem spine_name (ih : S.ConvAt n fuel) (hb : ∀ m < n, BodySim S.L S.Q S.A S.G m)
    {cx : Cx} {f a : Lam.Term} {m : Mode} {k : Kont} {e : Exp} {ρ : Lam.Env} {ρ' : List Val}
    {J' : List JClo} {ks : List Kind} {SK : Lam.Val → Nat → Result Lam.Val}
    (henv : EnvR S.A S.G ks cx.vars ρ ρ') (hd : ρ'.length = cx.d) (hdj : J'.length = cx.dj)
    (hk : S.KontR n cx.dj k SK ρ' J') {i : Nat} {sig : List Mode} {args : List (Lam.Term × Mode)}
    (hsp : (Lam.Term.app f a m).spine = (.var i, args)) (hi : ks[i]? = some (.name sig))
    (hcov : ∀ p, sig.getD p .strict = .name → p < args.length) (hargs : ArgsOk S.G ks sig [] 0 args)
    (h : spine S.A (fuel + 1) cx (.app f a m) k = .ok e) :
    SimUpTo S.V n (fun k => (Lam.eval S.L k ρ (.var i)).bind fun fv =>
      (applyArgs S.L k ρ fv args).bind (SK · k)) (fun k => eval S.Q k ρ' J' e) := by
  rw [spine.eq_2, hsp] at h
  simp only at h
  obtain ⟨vi, hvi⟩ := henv.get_kind hi
  obtain ⟨q, s, w, hq, hs, hw, hsr, hth⟩ := henv.get hvi
  rw [hi] at hq
  cases hq
  rw [hvi] at h
  simp only [hth, Kind.isName, if_true] at h
  rw [emit] at h
  obtain ⟨e3, he3, h⟩ := Lam.ModesOk.bind_ok h
  cases h
  cases hsr with
  | name hthk =>
  rename_i ρs ts
  have hforce : SimUpTo (S.GroupHead sig [] 0) n (fun k => Lam.force S.L k (.name ρs ts))
      (fun k => applyN S.Q k w [.box]) := by
    cases hsig : hasName sig
    · exact (force_sim hb hsig hthk).weaken fun x y hxy =>
        .inl ⟨hxy, fun p _ => hasName_false_getD hsig p⟩
    · exact (minor_sim n hsig hthk).weaken fun x y ⟨tk, hc, hcomp⟩ => .inr ⟨tk, hc, hcomp⟩
  have happ : ∀ k, evalBind S.Q k ρ' (.app (vi.opd.atom cx.d) [.box]) = applyN S.Q k w [.box] :=
    fun k => by rw [evalBind_app, ← hd, Opd.val_atom hw]; rfl
  refine (SimUpTo.bind (applyN_mono S.Q w _) (fun r => eval_mono S.Q (r :: ρ') J' e3)
    hforce fun fv r hfr => ?_).congr (fun k => by rw [Lam.eval_var_of S.L k ρ hs])
    (fun k => by rw [eval_bind, happ])
  exact ih.groups he3 (henv.cons' r) (by simp [hd]) hdj
    (hk.suffix (List.suffix_cons r ρ') (List.suffix_refl _) hdj hdj)
    (by rw [← hd]; exact Opd.val_lvl_top ρ' r) hfr hargs (fun p hp => by simpa using hcov p hp)

theorem spine_strict (ih : S.ConvAt n fuel)
    {cx : Cx} {f a : Lam.Term} {m : Mode} {k : Kont} {e : Exp} {ρ : Lam.Env} {ρ' : List Val}
    {J' : List JClo} {ks : List Kind} {SK : Lam.Val → Nat → Result Lam.Val}
    (henv : EnvR S.A S.G ks cx.vars ρ ρ') (hd : ρ'.length = cx.d) (hdj : J'.length = cx.dj)
    (hk : S.KontR n cx.dj k SK ρ' J') {i : Nat} {args : List (Lam.Term × Mode)}
    (hsp : (Lam.Term.app f a m).spine = (.var i, args)) (hi : ks[i]? = some .strict)
    (hargs : ArgsOk S.G ks [] [] 0 args) (h : spine S.A (fuel + 1) cx (.app f a m) k = .ok e) :
    SimUpTo S.V n (fun k => (Lam.eval S.L k ρ (.var i)).bind fun fv =>
      (applyArgs S.L k ρ fv args).bind (SK · k)) (fun k => eval S.Q k ρ' J' e) := by
  rw [spine.eq_2, hsp] at h
  simp only at h
  obtain ⟨vi, hvi⟩ := henv.get_kind hi
  obtain ⟨q, s, w, hq, hs, hw, hsr, hth⟩ := henv.get hvi
  rw [hi] at hq
  cases hq
  rw [hvi] at h
  simp only [hth, Kind.isName, Bool.false_eq_true, if_false] at h
  cases hsr with
  | val hv =>
  exact (ih.groups h henv hd hdj hk hw (.inl ⟨hv, fun p _ => by simp⟩) hargs
    (fun p hp => by simp at hp)).congr
    (fun k => by rw [Lam.eval_var_of S.L k ρ hs, Lam.force_val, Result.bind_ok]) (fun _ => rfl)

theorem spine_other (ih : S.ConvAt n fuel)
    {cx : Cx} {f a : Lam.Term} {m : Mode} {k : Kont} {e : Exp} {ρ : Lam.Env} {ρ' : List Val}
    {J' : List JClo} {ks : List Kind} {SK : Lam.Val → Nat → Result Lam.Val}
    (henv : EnvR S.A S.G ks cx.vars ρ ρ') (hd : ρ'.length = cx.d) (hdj : J'.length = cx.dj)
    (hk : S.KontR n cx.dj k SK ρ' J') {h0 : Lam.Term} {args : List (Lam.Term × Mode)}
    (hsp : (Lam.Term.app f a m).spine = (h0, args)) (hng : ∀ g, h0 ≠ .glob g)
    (hnv : ∀ i, h0 ≠ .var i) (hth : TermOk S.G ks h0) (hargs : ArgsOk S.G ks [] [] 0 args)
    (h : spine S.A (fuel + 1) cx (.app f a m) k = .ok e) :
    SimUpTo S.V n (fun k => (Lam.eval S.L k ρ h0).bind fun fv =>
      (applyArgs S.L k ρ fv args).bind (SK · k)) (fun k => eval S.Q k ρ' J' e) := by
  rw [spine.eq_2, hsp] at h
  simp only at h
  refine ih.conv (SK := fun fv k => (applyArgs S.L k ρ fv args).bind (SK · k)) h henv hd hdj
    ?_ hth
  intro d' dj' o e'' ρ'' J'' hf hd' hρ hdj' hJ fv ⟨w, hw, hv⟩
  exact ih.groups hf (henv.suffix hρ) hd' hdj' (hk.suffix hρ hJ hdj hdj') hw
    (.inl ⟨hv, fun _ _ => by simp⟩) hargs (fun p hp => by simp at hp)

end Setting

end Compilatrix.Anf.Convert.Proof
