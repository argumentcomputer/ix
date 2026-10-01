import Compilatrix.Anf.Proof.Convert.SpineGlob

/-! # ANF conversion: application spines

`spine` converts an application spine by its head (P1, M2.3): a CAF's value
(one charge, as Lam's δ) then the arguments in groups; a function global
(`spine_fun`); a `name` variable's forced thunk, a strict variable's value,
or any other head's value (`Convert/SpineVar`), then the arguments in
groups. Lam evaluates the spine as its head, then one application per
argument (`Lam.eval_apps`). -/

set_option autoImplicit false

namespace Compilatrix.Anf.Convert.Proof

open Compilatrix.Sem (Result ClockMono SimUpTo later later_succ later_zero)
open Compilatrix.Lam (Kind Mode argSlot applyArgs)
open Compilatrix.Lam.ModesOk (TermOk NameArgOk ArgsOk GInfo hasName expected covered KindsSpec sigsOf)
open Compilatrix.Ixon

namespace Setting

variable {S : Setting} {n fuel : Nat}

theorem spine_glob (ih : S.ConvAt n fuel) (hb : ∀ m < n, BodySim S.L S.Q S.A S.G m)
    {cx : Cx} {f a : Lam.Term} {m : Mode} {k : Kont} {e : Exp} {ρ : Lam.Env} {ρ' : List Val}
    {J' : List JClo} {ks : List Kind} {SK : Lam.Val → Nat → Result Lam.Val}
    (henv : EnvR S.A S.G ks cx.vars ρ ρ') (hd : ρ'.length = cx.d) (hdj : J'.length = cx.dj)
    (hk : S.KontR n cx.dj k SK ρ' J') {g : Lam.GlobalId} {args : List (Lam.Term × Mode)}
    (hsp : (Lam.Term.app f a m).spine = (.glob g, args))
    (hcov : covered ((S.G.get? g).getD {}).tele args.length = true)
    (hargs : ArgsOk S.G ks ((S.G.get? g).getD {}).tele ((S.G.get? g).getD {}).sigs 0 args)
    (h : spine S.A (fuel + 1) cx (.app f a m) k = .ok e) :
    SimUpTo S.V n (fun k => (Lam.eval S.L k ρ (.glob g)).bind fun fv =>
      (applyArgs S.L k ρ fv args).bind (SK · k)) (fun k => eval S.Q k ρ' J' e) := by
  cases hA : S.A.get? g with
  | none =>
    rw [spine.eq_2, hsp] at h
    simp only [hA] at h
    cases h
  | some nA =>
  cases nA with
  | succ nn => exact spine_fun ih hb henv hd hdj hk hsp hA hcov hargs h
  | zero =>
  -- a CAF: its value one clock down, then the arguments in groups
  rw [spine.eq_2, hsp] at h
  simp only [hA] at h
  obtain ⟨gl, gd, gi, kinds, hgl, hgd, hgi, hn, hps, hconv, htele, hsigs, hma, htm⟩ := S.glob hA
  rw [hgi] at hcov hargs
  simp only [Option.getD_some] at hcov hargs
  have hcov' := covered_spec hcov
  have hbody : gl.body = lamsWith (telescope gl.body).1 (telescope gl.body).2 :=
    (lamsWith_telescope gl.body).symm
  generalize (telescope gl.body).1 = ps at hn hconv htele hma hbody
  generalize (telescope gl.body).2 = body at hconv htm hbody
  have hkl : kinds.length = ps.length := hma.1.symm
  obtain ⟨e3, he3, h⟩ := Lam.ModesOk.bind_ok h
  cases h
  have hps0 : ps = [] := List.length_eq_zero_iff.1 hn.symm
  subst hps0
  have hk0 : kinds = [] := List.length_eq_zero_iff.1 hkl
  subst hk0
  have hgd0 : gd.ps = [] := List.length_eq_zero_iff.1 hps
  have hglob : ∀ k, evalBind S.Q k ρ' (.glob g) = later k fun k => eval S.Q k [] [] gd.body :=
    fun k => by rw [evalBind_glob, hgd]; simp [Result.ofOption, globVal, hgd0]
  have hcaf : SimUpTo S.V n (fun k => later k fun k => Lam.eval S.L k [] gl.body)
      (fun k => evalBind S.Q k ρ' (.glob g)) :=
    (SimUpTo.later fun m' hm' => hb m' (by omega) hconv rfl .nil
      (by simpa [lamsWith, ← hbody] using htm)).congr
      (fun k => by rw [hbody]; rfl) hglob
  refine (SimUpTo.bind (evalBind_mono S.Q ρ' _) (fun w => eval_mono S.Q (w :: ρ') J' e3) hcaf
    fun x w hxw => ?_).congr (fun k => by rw [lam_eval_glob S.L hgl])
      (fun k => eval_bind S.Q k ρ' J' _ _ e3)
  refine ih.groups he3 (henv.cons' w) (by simp [hd]) hdj
    (hk.suffix (List.suffix_cons w ρ') (List.suffix_refl _) hdj hdj)
    (by rw [← hd]; exact Opd.val_lvl_top ρ' w) (.inl ⟨hxw, fun p _ => ?_⟩) hargs
    (fun p hp => by have := hcov' p hp; omega)
  rw [htele]; simp

theorem spine_step (ih : S.ConvAt n fuel) (hb : ∀ m < n, BodySim S.L S.Q S.A S.G m)
    {cx : Cx} {f a : Lam.Term} {m : Mode} {k : Kont} {e : Exp} {ρ : Lam.Env} {ρ' : List Val}
    {J' : List JClo} {ks : List Kind} {SK : Lam.Val → Nat → Result Lam.Val}
    (h : spine S.A (fuel + 1) cx (.app f a m) k = .ok e) (henv : EnvR S.A S.G ks cx.vars ρ ρ')
    (hd : ρ'.length = cx.d) (hdj : J'.length = cx.dj) (hk : S.KontR n cx.dj k SK ρ' J')
    (ht : TermOk S.G ks (.app f a m)) :
    SimUpTo S.V n (fun k => (Lam.eval S.L k ρ (.app f a m)).bind (SK · k))
      (fun k => eval S.Q k ρ' J' e) := by
  have hsrc : ∀ k, (Lam.eval S.L k ρ (.app f a m)).bind (SK · k) =
      (Lam.eval S.L k ρ (Lam.Term.app f a m).spine.1).bind fun fv =>
        (applyArgs S.L k ρ fv (Lam.Term.app f a m).spine.2).bind (SK · k) := fun k => by
    conv => lhs; rw [← spine_apps (.app f a m)]
    rw [Lam.eval_apps, Result.bind_assoc]
  refine SimUpTo.congr ?_ hsrc (fun _ => rfl)
  cases ht with
  | appGlob hsp hcov hargs =>
    rw [hsp]; exact spine_glob ih hb henv hd hdj hk hsp hcov hargs h
  | appName hsp hi hcov hargs =>
    rw [hsp]; exact spine_name ih hb henv hd hdj hk hsp hi (covered_spec hcov) hargs h
  | appStrict hsp hi hargs =>
    rw [hsp]; exact spine_strict ih henv hd hdj hk hsp hi hargs h
  | appOther hsp hng hnv hth hargs =>
    rw [hsp]; exact spine_other ih henv hd hdj hk hsp hng hnv hth hargs h

end Setting

end Compilatrix.Anf.Convert.Proof
