import IxCC.Anf.Proof.Convert.Spine

/-! # ANF conversion: terms

`conv` at `fuel + 1`, one case per Lam construct (P1, M2.3): variables
(a value passed on, or a thunk forced), globals (a CAF's value one clock
down; a function global's closure behind a `tick` for Lam's δ charge), λs
(an `fn` closure), application spines, `let`, constructors and primitives
over converted argument lists, `case`, projections, literals, □, `tick`
and `trap`. -/

set_option autoImplicit false

namespace IxCC.Anf.Convert.Proof

open IxCC.Sem (Result ClockMono SimUpTo later later_succ later_zero)
open IxCC.Lam (Kind Mode argSlot applyArgs)
open IxCC.Lam.ModesOk (TermOk NameArgOk ArgsOk GInfo hasName expected covered KindsSpec sigsOf)
open IxCC.Ixon

namespace Setting

variable {S : Setting} {n fuel : Nat}

theorem hasName_false_strict {ms : List Mode} (h : hasName ms = false) : ∀ m ∈ ms, m = .strict := by
  intro m hm
  unfold hasName at h
  rw [List.any_eq_false] at h
  have := h m hm
  cases m with
  | strict => rfl
  | name => simp at this

/-- A function global used as a value: its closure, plain. -/
theorem glob_value {g : Lam.GlobalId} {nn : Nat} (hA : S.A.get? g = some (nn + 1))
    (hnm : hasName (((S.G.get? g).map (·.tele)).getD []) = false) :
    ∃ body ps', (∀ k ρ, Lam.eval S.L k ρ (.glob g) = later k fun _ => .ok (.clos [] (lamsWith ps' body))) ∧
      ∃ w, (∀ k ρ', evalBind S.Q k ρ' (.glob g) = .ok w) ∧ S.V (.clos [] (lamsWith ps' body)) w := by
  obtain ⟨gl, gd, gi, kinds, hgl, hgd, hgi, hn, hps, hconv, htele, hsigs, hma, htm⟩ := S.glob hA
  rw [hgi] at hnm
  simp only [Option.map_some, Option.getD_some] at hnm
  have hbody : gl.body = lamsWith (telescope gl.body).1 (telescope gl.body).2 :=
    (lamsWith_telescope gl.body).symm
  have hnl := notLam_telescope gl.body
  generalize (telescope gl.body).1 = ps at hn hconv htele hma hbody
  generalize (telescope gl.body).2 = body at hconv htm hbody hnl
  obtain ⟨p, ps', rfl⟩ : ∃ p ps', ps = p :: ps' := by
    cases ps with
    | nil => simp at hn
    | cons p ps' => exact ⟨p, ps', rfl⟩
  have hnn : nn = ps'.length := by simp at hn; omega
  subst hnn
  refine ⟨body, ps', fun k ρ => lam_eval_glob_fun S.L hgl hbody k ρ, .clos [] (ps'.length + 1) gd.body [],
    fun k ρ' => ?_, ?_⟩
  · rw [evalBind_glob, hgd]
    simp only [Result.ofOption, Result.bind_ok, globVal]
    split
    · next hg => rw [hg] at hps; simp at hps
    · rw [hps]
  · have hconv' : conv S.A (fuelFor gl.body)
        { vars := pushParams [] ([] : List Val).length ((p :: ps').map (·.1 == .name)),
          d := ([] : List Val).length + (p :: ps').length, dj := 0 } body .ret = .ok gd.body := by
      rw [modesAgree_thunks hma]; simpa using hconv
    refine .clo (tk := kinds) (j := 0) (.mk (ss := []) (got := []) hnl hma (by simp) .nil .nil hconv'
      (by simpa using htm) rfl (by simp) (by simp)) fun q hq => ?_
    -- a global used as a value has no `name` binder
    rw [htele] at hnm
    have hstrict := hasName_false_strict hnm
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 (by simpa using hq)
    have hil : i < (p :: ps').length := by
      rw [hma.1]; exact (List.getElem?_eq_some_iff.1 hi).1
    have := hma.2 i (p :: ps')[i] q (List.getElem?_eq_getElem hil) hi
    rw [hstrict _ (List.mem_map.2 ⟨_, List.getElem_mem hil, rfl⟩)] at this
    cases q with
    | strict => rfl
    | name s => simp [Kind.isName] at this

theorem conv_step (ih : S.ConvAt n fuel) (hb : ∀ m < n, BodySim S.L S.Q S.A S.G m)
    {cx : Cx} {t : Lam.Term} {k : Kont} {e : Exp} {ρ : Lam.Env} {ρ' : List Val} {J' : List JClo}
    {ks : List Kind} {SK : Lam.Val → Nat → Result Lam.Val}
    (h : conv S.A (fuel + 1) cx t k = .ok e) (henv : EnvR S.A S.G ks cx.vars ρ ρ')
    (hd : ρ'.length = cx.d) (hdj : J'.length = cx.dj) (hk : S.KontR n cx.dj k SK ρ' J')
    (ht : TermOk S.G ks t) :
    SimUpTo S.V n (fun k => (Lam.eval S.L k ρ t).bind (SK · k)) (fun k => eval S.Q k ρ' J' e) := by
  cases t with
  | var i =>
    rw [conv] at h
    cases ht with
    | varStrict hi =>
      obtain ⟨vi, hvi⟩ := henv.get_kind hi
      obtain ⟨q, s, w, hq, hs, hw, hsr, hth⟩ := henv.get hvi
      rw [hi] at hq; cases hq
      rw [hvi] at h
      simp only [hth, Kind.isName, Bool.false_eq_true, if_false] at h
      cases hsr with
      | val hv =>
      exact (pass_sim h hd hdj hk hw hv).congr
        (fun k => by rw [Lam.eval_var_of S.L k ρ hs, Lam.force_val, Result.bind_ok]) (fun _ => rfl)
    | varName hi hns =>
      obtain ⟨vi, hvi⟩ := henv.get_kind hi
      obtain ⟨q, s, w, hq, hs, hw, hsr, hth⟩ := henv.get hvi
      rw [hi] at hq; cases hq
      rw [hvi] at h
      simp only [hth, Kind.isName, if_true] at h
      cases hsr with
      | name hthk =>
      rename_i ρs ts
      have happ : ∀ k, evalBind S.Q k ρ' (.app (vi.opd.atom cx.d) [.box]) = applyN S.Q k w [.box] :=
        fun k => by rw [evalBind_app, ← hd, Opd.val_atom hw]; rfl
      exact (emit_sim h hd hdj hk ((force_sim hb hns hthk).congr (fun _ => rfl) happ)).congr
        (fun k => by rw [Lam.eval_var_of S.L k ρ hs]) (fun _ => rfl)
  | glob g =>
    rw [conv] at h
    cases ht with
    | glob hnm =>
    cases hA : S.A.get? g with
    | none => rw [hA] at h; cases h
    | some nA =>
    rw [hA] at h
    cases nA with
    | zero =>
      -- a CAF: its value one clock down
      simp only at h
      obtain ⟨gl, gd, gi, kinds, hgl, hgd, hgi, hn, hps, hconv, htele, hsigs, hma, htm⟩ := S.glob hA
      have hbody : gl.body = lamsWith (telescope gl.body).1 (telescope gl.body).2 :=
        (lamsWith_telescope gl.body).symm
      generalize (telescope gl.body).1 = ps at hn hconv htele hma hbody
      generalize (telescope gl.body).2 = body at hconv htm hbody
      have hps0 : ps = [] := List.length_eq_zero_iff.1 hn.symm
      subst hps0
      have hk0 : kinds = [] := List.length_eq_zero_iff.1 hma.1.symm
      subst hk0
      have hgd0 : gd.ps = [] := List.length_eq_zero_iff.1 hps
      have hglob : ∀ k, evalBind S.Q k ρ' (.glob g) = later k fun k => eval S.Q k [] [] gd.body :=
        fun k => by rw [evalBind_glob, hgd]; simp [Result.ofOption, globVal, hgd0]
      have hcaf : SimUpTo S.V n (fun k => Lam.eval S.L k ρ (.glob g))
          (fun k => evalBind S.Q k ρ' (.glob g)) :=
        (SimUpTo.later fun m' hm' => hb m' (by omega) hconv rfl .nil
          (by simpa [lamsWith, ← hbody] using htm)).congr
          (fun k => by rw [lam_eval_glob S.L hgl, hbody]; rfl) hglob
      exact emit_sim h hd hdj hk hcaf
    | succ nn =>
      -- a function global: its closure, behind a tick for Lam's δ charge
      obtain ⟨e0, he0, h⟩ := Lam.ModesOk.bind_ok h
      cases h
      obtain ⟨body, ps', hL, w, hQ, hv⟩ := glob_value hA hnm
      have hT := emit_sim he0 hd hdj hk (c := fun _ => .ok (.clos [] (lamsWith ps' body)))
        ((SimUpTo.ok hv).congr (fun _ => rfl) (fun k => hQ k ρ'))
      exact (SimUpTo.tickConst (eval_mono S.Q ρ' J' e0) hT fun k _ => rfl).congr
        (fun k => by rw [hL]) (fun k => eval_tick S.Q k ρ' J' e0)
  | lam mo c b =>
    rw [conv] at h
    rcases htel : telescope (.lam mo c b) with ⟨ps, body⟩
    simp only [htel] at h
    obtain ⟨b', hb', h⟩ := Lam.ModesOk.bind_ok h
    have hlams : Lam.Term.lam mo c b = lamsWith ps body := by
      rw [← lamsWith_telescope (.lam mo c b), htel]
    have hnl : NotLam body := by
      have := notLam_telescope (.lam mo c b); rw [htel] at this; exact this
    rw [hlams] at ht
    obtain ⟨hstrict, htm⟩ := termOk_lams (S := S) ps ht
    obtain ⟨p, ps', rfl⟩ : ∃ p ps', ps = p :: ps' := by
      cases ps with
      | nil => simp only [lamsWith] at hlams; rw [← hlams] at hnl; exact absurd hnl id
      | cons p ps' => exact ⟨p, ps', rfl⟩
    have hb0 : b = lamsWith ps' body := by
      obtain ⟨pm, pc⟩ := p
      simp only [lamsWith, Lam.Term.lam.injEq] at hlams
      exact hlams.2.2
    have hclo : CloR S.A S.G (List.replicate (p :: ps').length .strict) 0 (.clos ρ b)
        (.clos ρ' (p :: ps').length b' []) :=
      .mk (ss := []) (got := []) hnl (modesAgree_strict hstrict) (by simp) henv .nil
        (by rw [hd]; exact hb') (by simpa using htm) rfl (by simp [hb0]) rfl
    have hv : S.V (.clos ρ b) (.clos ρ' (p :: ps').length b' []) :=
      .clo hclo fun q hq => by simpa using hq
    exact (emit_sim h hd hdj hk ((SimUpTo.ok hv).congr (fun _ => rfl)
      (fun k => by rw [evalBind_fn S.Q k ρ' _ b' (by simp)]; simp))).congr
      (fun k => by rw [Lam.eval_lam]) (fun _ => rfl)
  | app f a mo =>
    rw [conv] at h
    exact ih.spine h henv hd hdj hk ht
  | letE c v b =>
    rw [conv] at h
    cases ht with
    | letE hv hbd =>
    refine (ih.conv (SK := fun x k => (Lam.eval S.L k (.val x :: ρ) b).bind (SK · k)) h henv hd hdj ?_
      hv).congr (fun k => by rw [Lam.eval_letE, Result.bind_assoc]) (fun _ => rfl)
    intro d' dj' o e' ρ'' J'' hf hd' hρ hdj' hJ x ⟨w, hw, hxw⟩
    exact ih.conv hf (.cons rfl hw (.val hxw) (henv.suffix hρ)) hd' hdj' (hk.suffix hρ hJ hdj hdj') hbd
  | con c fs =>
    rw [conv] at h
    cases ht with
    | con hfs =>
    refine (ih.convList (SKL := fun vs k => SK (.con c vs) k) h henv hd hdj ?_ hfs).congr
      (fun k => by rw [Lam.eval_con, Result.bind_assoc]; rfl) (fun _ => rfl)
    intro d' dj' os e' ρ'' J'' hf hd' hρ hdj' hJ xs ⟨ws, hws, hxs⟩
    have hcon : ∀ k, evalBind S.Q k ρ'' (.con c (os.map (·.atom d'))) = .ok (.con c ws) := fun k => by
      rw [evalBind_con, ← hd', opds_eval hws]; rfl
    exact (emit_sim hf hd' hdj' (hk.suffix hρ hJ hdj hdj') (c := fun _ => .ok (.con c xs))
      ((SimUpTo.ok (.con hxs)).congr (fun _ => rfl) hcon)).congr (fun _ => rfl) (fun _ => rfl)
  | case s alts dflt =>
    rw [conv] at h
    cases ht with
    | case hs halts hdflt =>
    refine (ih.conv (SK := fun v k => (S.caseSrc k ρ v alts dflt).bind (SK · k)) h henv hd hdj ?_
      hs).congr (fun k => by rw [Lam.eval_case, Result.bind_assoc]; rfl) (fun _ => rfl)
    intro d' dj' o e' ρ'' J'' hf hd' hρ hdj' hJ v ⟨w, hw, hvw⟩
    exact ih.caseOn hf (henv.suffix hρ) hd' hdj' (hk.suffix hρ hJ hdj hdj') hw hvw halts hdflt
  | proj c i s =>
    rw [conv] at h
    cases ht with
    | proj hs =>
    refine (ih.conv (SK := fun v k => (projL c i v).bind (SK · k)) h henv hd hdj ?_ hs).congr
      (fun k => by
        rw [Lam.eval_proj, Result.bind_assoc]
        exact Result.bind_congr _ fun v => by cases v <;> rfl) (fun _ => rfl)
    intro d' dj' o e' ρ'' J'' hf hd' hρ hdj' hJ v ⟨w, hw, hvw⟩
    have hproj : ∀ k, evalBind S.Q k ρ'' (.proj c i (o.atom d')) = projVal c i w := fun k => by
      rw [evalBind_proj, ← hd', Opd.val_atom hw]; rfl
    exact emit_sim hf hd' hdj' (hk.suffix hρ hJ hdj hdj')
      ((proj_sim c i hvw).congr (fun _ => rfl) hproj)
  | lit l =>
    rw [conv] at h
    exact (pass_sim h hd hdj hk (w := .lit l) rfl .lit).congr
      (fun k => by rw [Lam.eval_lit, Result.bind_ok]) (fun _ => rfl)
  | prim p args =>
    rw [conv] at h
    cases ht with
    | prim hargs =>
    refine (ih.convList (SKL := fun vs k => (Lam.primResult S.L.known p vs).bind (SK · k)) h henv hd
      hdj ?_ hargs).congr (fun k => by rw [Lam.eval_prim, Result.bind_assoc]) (fun _ => rfl)
    intro d' dj' os e' ρ'' J'' hf hd' hρ hdj' hJ xs ⟨ws, hws, hxs⟩
    have hprim : ∀ k, evalBind S.Q k ρ'' (.prim p (os.map (·.atom d'))) =
        primResult S.L.known p ws := fun k => by
      rw [evalBind_prim, ← hd', opds_eval hws, S.known]; rfl
    exact emit_sim hf hd' hdj' (hk.suffix hρ hJ hdj hdj')
      ((prim_sim p hxs).congr (fun _ => rfl) hprim)
  | tick b =>
    rw [conv] at h
    obtain ⟨e1, he1, h⟩ := Lam.ModesOk.bind_ok h
    cases h
    cases ht with
    | tick hb' =>
    exact (SimUpTo.tick (Lam.eval_mono S.L ρ b) (eval_mono S.Q ρ' J' e1)
      (ih.conv he1 henv hd hdj hk hb')).congr
      (fun k => by rw [Lam.eval_tick]; cases k <;> rfl) (fun k => eval_tick S.Q k ρ' J' e1)
  | box =>
    rw [conv] at h
    exact (pass_sim h hd hdj hk (w := .box) rfl .box).congr
      (fun k => by rw [Lam.eval_box', Result.bind_ok]) (fun _ => rfl)
  | trap =>
    rw [conv] at h
    cases h
    exact (SimUpTo.trap).congr (fun k => by rw [Lam.eval_trap']; rfl) (fun k => eval_trap' S.Q k ρ' J')

end Setting

end IxCC.Anf.Convert.Proof
