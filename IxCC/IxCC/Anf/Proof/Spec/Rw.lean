import IxCC.Anf.Proof.Spec.Sim

/-! # P4: rewritten code simulates its source

A rewritten call site calls the specialisation the site built, on the
holes' values: an activation of that site, so the call simulates the
callee's (`site_sim`, from `spec_sim`). Every other binding is the source's
(the fundamental lemma's compatibility) or a local function of rewritten
code (a closure of P4's other code, `RwClo`); the rest is the fundamental
lemma's structure over the rewrite relation, with definitions that keep
describing the source environment (`rw_step`, `rw_fund`, `xc_enter`, M2.3). -/

set_option autoImplicit false

namespace IxCC.Anf.Specialize.Proof

open Walk (Ent Cfg)
open WalkProof (WV WVs VOk)
open IxCC.Anf.Rel (Pw)
open IxCC.Sem (Result SimUpTo)

variable {P Q : Program}

/-! ## Call sites -/

theorem buildSpec_inv {src : Program} {defs : Src.NatMap Def} {t : Trees} {roots : List (Nat × Opd)}
    {g : GlobalId} {gd : GDef} {key : Key.GKey} {s : GlobalId} {spec : GDef}
    (h : buildSpec src defs t roots g gd key s = .ok spec) :
    ∃ pro m body s', prologue src defs (t.levelHoles.map fun (l, h) => (l, .lvl h)) t.holes.length
        (sortNats t.needed) = .ok (pro, m) ∧
      (Walk.walk { prog := src, redirect := some (specRedirect defs roots m t g gd.ps.length s) } Walk.fuel
        { σ := (List.range gd.ps.length).reverse.map fun i => Ent.opd (specParam defs roots m t i) }
        { d := t.holes.length + pro.length, dj := 0, facts := .leaf } gd.body .ret).run {} = .ok (body, s') ∧
      spec.ps.length = t.holes.length ∧ spec.body = binds pro body := by
  rw [buildSpec.eq_1] at h
  obtain ⟨⟨pro, m⟩, hpro, h⟩ := except_bind_ok h
  dsimp only at h
  obtain ⟨⟨body, s'⟩, hw, h⟩ := except_bind_ok h
  dsimp only at h
  cases h
  exact ⟨pro, m, body, s', hpro, hw, by simp, rfl⟩

theorem evalAtoms_mapM {ρ : List Val} : ∀ (as : List Atom), evalAtoms ρ as = as.mapM (·.eval ρ)
  | [] => rfl
  | a :: as => by
    rw [evalAtoms_cons, List.mapM_cons, evalAtoms_mapM as]
    cases a.eval ρ <;> cases as.mapM (·.eval ρ) <;> rfl

theorem siteArgs_get (t : Trees) (d : Nat) (as : List Atom) (k : Nat) :
    (siteArgs t d as)[k]? = (t.holes[k]?).map fun h => match h with
      | .param i => as.getD i .box
      | .level l => Opd.atom d (.lvl l)
      | .atom o => o.atom d := by
  simp only [siteArgs, List.getElem?_map]
  cases t.holes[k]? with
  | none => rfl
  | some h => cases h <;> rfl

/-- **A rewritten call site** simulates the call it replaces. -/
theorem site_sim {n : Nat} (hspec : ∀ D : Site, D.Ok P Q → SpecSim P Q n D) {defs : Src.NatMap Def}
    {ρ ρ' : List Val} {g s : GlobalId} {as args : List Atom} (hsite : SiteOk P Q defs ρ.length g as s args)
    (hD : DefsOk P defs ρ) (hρ : Pw (R4 P Q) ρ ρ') :
    SimUpTo (R4 P Q) n (fun k => evalBind P k ρ (.call g as)) (fun k => evalBind Q k ρ' (.call s args)) := by
  obtain ⟨inv, fkey, gd, mask, t, keys, roots, spec, hg, hfix, hst, hbuild, ⟨gdS, hQs, hps, hbody⟩, rfl⟩ := hsite
  obtain ⟨pro, m, body, s', hpro, hwalk, hspl, hspb⟩ := buildSpec_inv hbuild
  cases hvs : evalAtoms ρ as with
  | none =>
    refine (SimUpTo.stuck _).congr (fun k => ?_) (fun _ => rfl)
    rw [evalBind_call, hg, hvs]; rfl
  | some vs =>
  by_cases hn0 : vs.length ≠ gd.ps.length
  · refine (SimUpTo.stuck _).congr (fun k => ?_) (fun _ => rfl)
    rw [evalBind_call, hg, hvs]; simp [Result.ofOption, callVal, hn0]
  have hn : vs.length = gd.ps.length := by omega
  have hasl : as.length = gd.ps.length := by rw [← evalAtoms_length ρ hvs, hn]
  have hml : mask.length = gd.ps.length := by
    unfold fixedOk at hfix; simp only [Bool.and_eq_true, beq_iff_eq] at hfix; exact hfix.1
  obtain ⟨hT, hr1, hr2, hpar⟩ := siteTrees_ok hD fkey inv hvs hst
  have hρl : ρ'.length = ρ.length := hρ.length
  let D : Site := ⟨defs, ρ, t, roots, g, gd, s, pro, m, body⟩
  have hDok : D.Ok P Q :=
    { hg := hg
      hs := ⟨gdS, hQs, by rw [hps, hspl]; rfl, by rw [hbody, hspb]⟩
      defs := hD
      trees := by have := hT; rw [hasl] at this; exact this
      roots := fun i o hl => by
        obtain ⟨hcov, hir, a, ha, -, -⟩ := hr1 i o hl
        exact ⟨by have := (List.getElem?_eq_some_iff.1 ha).1; show i < gd.ps.length; omega, hcov, hir⟩
      params := fun i hi hl => by
        have hi' : i < gd.ps.length := hi
        obtain ⟨a, ha⟩ : ∃ a, as[i]? = some a := ⟨_, List.getElem?_eq_getElem (by omega)⟩
        obtain ⟨b, hb⟩ : ∃ b, mask[i]? = some b := ⟨_, List.getElem?_eq_getElem (by omega)⟩
        cases b with
        | true => rw [hr2 i a ha hb] at hl; cases hl
        | false => exact hpar i a ha hb
      pro := hpro
      walk := ⟨Walk.fuel, {}, s', hwalk⟩ }
  -- the specialisation's arguments evaluate
  have harg : ∀ x ∈ siteArgs t ρ.length as, ∃ w, x.eval ρ' = some w := by
    intro x hx
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hx
    rw [siteArgs_get] at hk
    cases hh : t.holes[k]? with
    | none => rw [hh] at hk; cases hk
    | some h =>
      rw [hh] at hk
      simp only [Option.map_some, Option.some.injEq] at hk
      subst hk
      cases h with
      | param i =>
        have hi := hT.param k i hh
        obtain ⟨a, ha⟩ : ∃ a, as[i]? = some a := ⟨_, List.getElem?_eq_getElem hi⟩
        obtain ⟨v, hv, -⟩ := evalAtoms_get hvs ha
        rcases Rel.atom_eval_rel WalkProof.structural.toBase hρ a with ⟨h1, -⟩ | ⟨v', w, -, hw, -⟩
        · rw [hv] at h1; cases h1
        · exact ⟨w, by simp [List.getD_eq_getElem?_getD, ha, hw]⟩
      | level l =>
        have hl := hT.lvl k l hh
        rcases Rel.atom_eval_rel WalkProof.structural.toBase hρ (.var (ρ.length - 1 - l)) with
          ⟨h1, -⟩ | ⟨v', w, -, hw, -⟩
        · simp only [Atom.eval] at h1
          rw [List.getElem?_eq_none_iff] at h1; omega
        · exact ⟨w, hw⟩
      | atom o =>
        have ho := hT.atom k o hh
        cases o with
        | lvl l =>
          rcases Rel.atom_eval_rel WalkProof.structural.toBase hρ (.var (ρ.length - 1 - l)) with
            ⟨h1, -⟩ | ⟨v', w, -, hw, -⟩
          · simp only [Atom.eval] at h1
            have : l < ρ.length := ho
            rw [List.getElem?_eq_none_iff] at h1; omega
          · exact ⟨w, hw⟩
        | lit l => exact ⟨_, rfl⟩
        | box => exact ⟨_, rfl⟩
  obtain ⟨Hv, hHv⟩ := mapM_exists harg
  have hHvl : Hv.length = t.holes.length := by
    rw [WalkProof.mapM_length hHv]; simp [siteArgs]
  have hget : ∀ k, Hv[k]? = ((siteArgs t ρ.length as)[k]?).bind (fun (a : Atom) => a.eval ρ') :=
    mapM_getElem? hHv
  refine (hspec D hDok vs Hv ⟨hn, hHvl, fun i o hl => ?_⟩ (fun k l hk => ?_) (fun k i hk => ?_)).congr
    (fun k => ?_) (fun k => ?_)
  · obtain ⟨-, -, a, ha, -, rfl⟩ := hr1 i o hl
    obtain ⟨v, hv, hvi⟩ := evalAtoms_get hvs ha
    rw [hvi]; exact atom_opd_val hv
  · have hl := hT.lvl k l hk
    rcases Rel.atom_eval_rel WalkProof.structural.toBase hρ (.var (ρ.length - 1 - l)) with
      ⟨h1, -⟩ | ⟨v, w, hv, hw, hvw⟩
    · simp only [Atom.eval] at h1
      rw [List.getElem?_eq_none_iff] at h1; omega
    · refine ⟨v, w, ?_, ?_, hvw⟩
      · simp only [Atom.eval] at hv
        rw [lvl_val hl]; exact hv
      · rw [hget, siteArgs_get, hk]; simp [Opd.atom, hw]
  · have hi := hT.param k i hk
    obtain ⟨a, ha⟩ : ∃ a, as[i]? = some a := ⟨_, List.getElem?_eq_getElem hi⟩
    obtain ⟨v, hv, hvi⟩ := evalAtoms_get hvs ha
    rcases Rel.atom_eval_rel WalkProof.structural.toBase hρ a with ⟨h1, -⟩ | ⟨v', w, hv', hw, hvw⟩
    · rw [hv] at h1; cases h1
    · rw [hv] at hv'; cases hv'
      refine ⟨v, w, hvi, ?_, hvw⟩
      rw [hget, siteArgs_get, hk]; simp [List.getD_eq_getElem?_getD, ha, hw]
  · rw [evalBind_call, hg, hvs]; rfl
  · rw [evalBind_call, hQs, evalAtoms_mapM, hHv]; rfl

/-! ## Rewritten code -/

/-- Rewritten code simulates its source at bound `n`. -/
def RwFund (P Q : Program) (n : Nat) : Prop :=
  ∀ ⦃defs : Src.NatMap Def⦄ ⦃ρ ρ' : List Val⦄ ⦃J J' : List JClo⦄ ⦃e e' : Exp⦄,
    RwE P Q defs ρ.length e e' → DefsOk P defs ρ → Pw (R4 P Q) ρ ρ' → JRw P Q J J' →
    SimUpTo (R4 P Q) n (fun k => eval P k ρ J e) (fun k => eval Q k ρ' J' e')

theorem JRw.get : ∀ {J J' : List JClo}, JRw P Q J J' → ∀ (j : Nat),
    (J[j]? = none ∧ J'[j]? = none) ∨ ∃ ρj ρj' Jj Jj' ar b b' r, J[j]? = some (.mk ρj Jj ar b r) ∧
      J'[j]? = some (.mk ρj' Jj' ar b' r) ∧ WVs Q (V P Q) (RwClo P Q) ρj ρj' ∧ JRw P Q Jj Jj' ∧
      RwClo P Q ar ρj b b'
  | _, _, .nil, _ => .inl ⟨rfl, rfl⟩
  | _, _, .cons hρ hJj hc _, 0 => .inr ⟨_, _, _, _, _, _, _, _, rfl, rfl, hρ, hJj, hc⟩
  | _, _, .cons _ _ _ h, j + 1 => by simpa using h.get j

section

variable {n : Nat} (hK : Q.known = P.known) (hlowF : ∀ m < n, Rel.FundAt P Q (R4 P Q) m)
  (hlow : ∀ m < n, RwFund P Q m) (happ : Rel.AppSim P Q (R4 P Q) n) (hcall : Rel.CallSim P Q (R4 P Q) n)
  (hglob : Rel.GlobSim P Q (R4 P Q) n) (hspec : ∀ D : Site, D.Ok P Q → SpecSim P Q n D)
include hK hlowF hlow happ hcall hglob hspec

mutual

theorem rw_exp : ∀ {defs : Src.NatMap Def} {d : Nat} {e e' : Exp}, RwE P Q defs d e e' →
    ∀ {ρ ρ' : List Val} {J J' : List JClo}, d = ρ.length → DefsOk P defs ρ → Pw (R4 P Q) ρ ρ' →
    JRw P Q J J' → SimUpTo (R4 P Q) n (fun k => eval P k ρ J e) (fun k => eval Q k ρ' J' e')
  | _, _, _, _, .bind hb hdf hbody, ρ, ρ', J, J', hd, hD, hρ, hJ => by
    subst hd
    refine (SimUpTo.bind' (evalBind_mono Q ρ' _) (fun w => eval_mono Q (w :: ρ') J' _)
      (rw_bind hb rfl hD hρ) fun v w hvw hk => by
        obtain ⟨k, -, hv⟩ := hk
        exact rw_exp hbody (by simp) (hD.insert (hdf ρ k v hD rfl hv)) (.cons hvw hρ) hJ).congr
      (fun k => eval_bind P k ρ J _ _ _) (fun k => eval_bind Q k ρ' J' _ _ _)
  | _, _, _, _, .join hjb hbody, ρ, ρ', J, J', hd, hD, hρ, hJ => by
    subst hd
    exact Rel.compat_join (rw_exp hbody rfl hD hρ
      (.cons (WalkProof.of_pw hρ) hJ ⟨_, hjb, fun _ _ => hD.blank _ _⟩ hJ))
  | _, _, _, _, .case (x := x) halts hdflt, ρ, ρ', J, J', hd, hD, hρ, hJ => by
    refine SimUpTo.congr ?_ (fun k => eval_case P k ρ J x _ _) (fun k => eval_case Q k ρ' J' x _ _)
    rcases Rel.atom_eval_rel WalkProof.structural.toBase hρ x with ⟨h1, h2⟩ | ⟨v, w, h1, h2, hvw⟩
    · rw [h1]; exact SimUpTo.stuck _
    · rw [h1, h2, hK]
      simp only [Result.ofOption, Result.bind_ok]
      rcases Rel.asCtor_rel WalkProof.structural.toBase P.known hvw with h3 | ⟨c, fs, fs', h3, h4, hfs⟩
      · rw [h3]; exact SimUpTo.stuck _
      · rw [h3, h4]
        exact rw_alts halts hd hD hρ hJ c hfs (rw_opt hdflt hd hD hρ hJ c hfs)
  | _, _, _, _, .tick hE, ρ, ρ', J, J', hd, hD, hρ, hJ => by
    subst hd
    exact Rel.compat_tick fun m hm => hlow m (by omega) hE hD hρ hJ
  | _, _, _, _, .jump (j := j) (as := as), ρ, ρ', J, J', hd, hD, hρ, hJ => by
    refine SimUpTo.congr ?_ (fun k => eval_jump P k ρ J j as) (fun k => eval_jump Q k ρ' J' j as)
    rcases hJ.get j with ⟨h1, h2⟩ | ⟨ρj, ρj', Jj, Jj', ar, b, b', r, h1, h2, hρj, hJj, hc⟩
    · rw [h1]; exact SimUpTo.stuck _
    · rw [h1, h2]
      simp only [Result.ofOption, Result.bind_ok]
      rcases Rel.atoms_eval_rel WalkProof.structural.toBase hρ as with ⟨h3, h4⟩ | ⟨vs, ws, h3, h4, hvs⟩
      · rw [h3]; exact SimUpTo.stuck _
      · rw [h3, h4]
        simp only [Result.bind_ok]
        refine Rel.compat_jumpTo hvs (fun _ _ _ _ _ _ _ _ _ e1 e2 => ?_) (fun _ _ _ _ _ _ _ _ _ _ e1 e2 => ?_)
        · cases e1; cases e2
          refine ⟨rfl, fun i hi hl => ?_⟩
          obtain ⟨defs', hE, hDj⟩ := hc
          have hE' : RwE P Q defs' (vs.reverse ++ ρj).length b b' := by
            rw [show (vs.reverse ++ ρj).length = ρj.length + ar by simp [hl]; omega]; exact hE
          refine hlow i (by omega) hE' (hDj vs hl) (hvs.reverse.append (WalkProof.pw_of hρj)) ?_
          cases r
          · exact hJj
          · exact .cons hρj hJj ⟨defs', hE, hDj⟩ hJj
        · cases e1; cases e2; rfl
  | _, _, _, _, .ret (a := a), ρ, ρ', J, J', _, _, hρ, _ => Rel.compat_ret WalkProof.structural.toBase hρ a
  | _, _, _, _, .trap, _, _, _, _, _, _, _, _ => Rel.compat_trap

theorem rw_bind : ∀ {defs : Src.NatMap Def} {d : Nat} {b b' : Bind}, RwB P Q defs d b b' →
    ∀ {ρ ρ' : List Val}, d = ρ.length → DefsOk P defs ρ → Pw (R4 P Q) ρ ρ' →
    SimUpTo (R4 P Q) n (fun k => evalBind P k ρ b) (fun k => evalBind Q k ρ' b')
  | _, _, _, _, .same (b := b), ρ, ρ', _, _, hρ =>
    Rel.fund_bind WalkProof.structural hK hlowF happ hcall hglob hρ b
  | _, _, _, _, .fn (ps := ps) (fb := fb) (fb' := fb') hE, ρ, ρ', hd, hD, hρ => by
    subst hd
    cases ps with
    | nil => exact (SimUpTo.stuck _).congr (fun k => evalBind_fn_nil P k ρ fb) (fun _ => rfl)
    | cons p ps =>
      exact (SimUpTo.ok (.xc (WalkProof.of_pw hρ) .nil ⟨_, hE, fun _ _ => hD.blank _ _⟩)).congr
        (fun k => evalBind_fn P k ρ _ fb (List.cons_ne_nil _ _))
        (fun k => evalBind_fn Q k ρ' _ fb' (List.cons_ne_nil _ _))
  | _, _, _, _, .call hs, ρ, ρ', hd, hD, hρ => by
    subst hd
    exact site_sim hspec hs hD hρ

theorem rw_alts : ∀ {defs : Src.NatMap Def} {d : Nat} {alts alts' : List Alt}, RwAlts P Q defs d alts alts' →
    ∀ {ρ ρ' : List Val} {J J' : List JClo}, d = ρ.length → DefsOk P defs ρ → Pw (R4 P Q) ρ ρ' →
    JRw P Q J J' → ∀ (c : Key.CtorKey) {fs fs' : List Val}, Pw (R4 P Q) fs fs' →
    ∀ {dflt dflt' : Option Exp},
    SimUpTo (R4 P Q) n (fun k => evalAlts P k ρ J c fs [] dflt) (fun k => evalAlts Q k ρ' J' c fs' [] dflt') →
    SimUpTo (R4 P Q) n (fun k => evalAlts P k ρ J c fs alts dflt) (fun k => evalAlts Q k ρ' J' c fs' alts' dflt')
  | _, _, _, _, .nil, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hdf => hdf
  | defs, _, _, _, .cons (key := key) (n := m) (b := b) (b' := b') hb hrest, ρ, ρ', J, J', hd, hD, hρ, hJ, c, fs, fs', hfs, dflt,
      dflt', hdf => by
    refine SimUpTo.congr ?_ (fun k => evalAlts_cons P k ρ J c fs key m _ _ dflt)
      (fun k => evalAlts_cons Q k ρ' J' c fs' key m _ _ dflt')
    have hl := hfs.length
    by_cases hsel : key = c ∧ m = fs.length
    · have hsel' : key = c ∧ m = fs'.length := ⟨hsel.1, by rw [hl]; exact hsel.2⟩
      subst hd
      have hE : RwE P Q (blankDefs defs ρ.length m) (fs.reverse ++ ρ).length b b' := by
        rw [show (fs.reverse ++ ρ).length = ρ.length + m by simp [hsel.2]; omega]; exact hb
      exact (rw_exp hE rfl (hD.blank _ _) (hfs.reverse.append hρ) hJ).congr (fun _ => if_pos hsel)
        (fun _ => if_pos hsel')
    · have hsel' : ¬ (key = c ∧ m = fs'.length) := by rw [hl]; exact hsel
      exact (rw_alts hrest hd hD hρ hJ c hfs hdf).congr (fun _ => if_neg hsel) (fun _ => if_neg hsel')

theorem rw_opt : ∀ {defs : Src.NatMap Def} {d : Nat} {dflt dflt' : Option Exp}, RwOpt P Q defs d dflt dflt' →
    ∀ {ρ ρ' : List Val} {J J' : List JClo}, d = ρ.length → DefsOk P defs ρ → Pw (R4 P Q) ρ ρ' →
    JRw P Q J J' → ∀ (c : Key.CtorKey) {fs fs' : List Val}, Pw (R4 P Q) fs fs' →
    SimUpTo (R4 P Q) n (fun k => evalAlts P k ρ J c fs [] dflt) (fun k => evalAlts Q k ρ' J' c fs' [] dflt')
  | _, _, _, _, .none, ρ, ρ', J, J', _, _, _, _, c, fs, fs', _ =>
    (SimUpTo.stuck _).congr (fun k => by rw [evalAlts_nil]) (fun k => by rw [evalAlts_nil])
  | _, _, _, _, .some hE, ρ, ρ', J, J', hd, hD, hρ, hJ, c, fs, fs', _ =>
    (rw_exp hE hd hD hρ hJ).congr (fun k => by rw [evalAlts_nil]) (fun k => by rw [evalAlts_nil])

end

/-- Rewritten code simulates at bound `n`, from the interface at `n`, the
fundamental lemma and the rewritten code's simulation below `n`. -/
theorem rw_step : RwFund P Q n := fun _ _ _ _ _ _ _ hE hD hρ hJ =>
  rw_exp hK hlowF hlow happ hcall hglob hspec hE rfl hD hρ hJ

end

theorem AppSim.mono {n m : Nat} (h : Rel.AppSim P Q (R4 P Q) n) (hm : m ≤ n) : Rel.AppSim P Q (R4 P Q) m :=
  fun _ _ _ _ hfg hvs => (h hfg hvs).mono_n hm

theorem CallSim.mono {n m : Nat} (h : Rel.CallSim P Q (R4 P Q) n) (hm : m ≤ n) : Rel.CallSim P Q (R4 P Q) m :=
  fun g _ _ hvs => (h g hvs).mono_n hm

theorem GlobSim.mono {n m : Nat} (h : Rel.GlobSim P Q (R4 P Q) n) (hm : m ≤ n) : Rel.GlobSim P Q (R4 P Q) m :=
  fun g => (h g).mono_n hm

/-- Rewritten code simulates at every bound up to `n`. -/
theorem rw_fund (hK : Q.known = P.known) {n : Nat} (hF : ∀ m < n, Rel.FundAt P Q (R4 P Q) m)
    (happ : Rel.AppSim P Q (R4 P Q) n) (hcall : Rel.CallSim P Q (R4 P Q) n) (hglob : Rel.GlobSim P Q (R4 P Q) n)
    (hspec : ∀ m ≤ n, ∀ D : Site, D.Ok P Q → SpecSim P Q m D) : ∀ m ≤ n, RwFund P Q m := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
  intro hm
  exact rw_step hK (fun i hi => hF i (by omega)) (fun i hi => ih i hi (by omega)) (AppSim.mono happ hm)
    (CallSim.mono hcall hm) (GlobSim.mono hglob hm) (hspec m hm)

/-- Entering a closure of rewritten code simulates. -/
theorem xc_enter {i : Nat} (h : RwFund P Q i) : WalkProof.XcEnter P Q (V P Q) (RwClo P Q) i := by
  intro nn ρ ρ' b b' args args' hρ hc hargs hl
  obtain ⟨defs, hE, hD⟩ := hc
  have hE' : RwE P Q defs (args.reverse ++ ρ).length b b' := by
    rw [show (args.reverse ++ ρ).length = ρ.length + nn by simp [hl]; omega]; exact hE
  exact h hE' (hD args hl) ((WalkProof.pw_of hargs).reverse.append (WalkProof.pw_of hρ)) .nil

end IxCC.Anf.Specialize.Proof
