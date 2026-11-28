import IxCC.Anf.Proof.Spec.Frame

/-! # P4: a specialisation simulates its callee

`spec_sim`: calling a site's specialisation on an activation (the callee's
arguments, masked ones the roots' values at the site; the specialisation's
arguments, level holes related to the caller's levels and unmasked
parameters' holes to the callee's arguments) simulates calling the callee,
one clock down: the prologue rebuilds a frame related to the site
(`prologue_frame`), so the callee's parameters' walk entries hold, and the
walk of the callee's body simulates it (the walk's simulation below the
bound). `red_sim`: a redirected recursive call inside the specialisation's
body passes its masked parameters unchanged (`Walk.fixedAt`), so it calls
the specialisation on another activation of the same site. -/

set_option autoImplicit false

namespace IxCC.Anf.Specialize.Proof

open Walk (Ent Cfg)
open WalkProof (WV WVs VOk WEnv WEnt WalkAt KontW)
open IxCC.Sem (Result SimUpTo)

variable {P Q : Program}

/-- A site's specialisation simulates its callee at bound `n`, for every
activation whose level holes and unmasked parameters' holes are related. -/
def SpecSim (P Q : Program) (n : Nat) (D : Site) : Prop :=
  ∀ vs Hv, D.Act vs Hv →
    (∀ (k l : Nat), D.t.holes[k]? = some (.level l) →
      ∃ v w, (Opd.lvl l).val D.ρs = some v ∧ Hv[k]? = some w ∧ R4 P Q v w) →
    (∀ (k i : Nat), D.t.holes[k]? = some (.param i) → ∃ v w, vs[i]? = some v ∧ Hv[k]? = some w ∧ R4 P Q v w) →
    SimUpTo (R4 P Q) n (fun k => (Result.ofOption (P.global? D.g)).bind (callVal P k · vs))
      (fun k => (Result.ofOption (Q.global? D.s)).bind (callVal Q k · Hv))

/-! ## Lists -/

theorem mapM_exists {α β : Type} {f : α → Option β} : ∀ {xs : List α}, (∀ x ∈ xs, ∃ y, f x = some y) →
    ∃ ys, xs.mapM f = some ys
  | [], _ => ⟨[], rfl⟩
  | x :: xs, h => by
    obtain ⟨y, hy⟩ := h x List.mem_cons_self
    obtain ⟨ys, hys⟩ := mapM_exists fun x' hx' => h x' (List.mem_cons_of_mem _ hx')
    exact ⟨y :: ys, by simp [List.mapM_cons, hy, hys]⟩

theorem mapM_getElem? {α β : Type} {f : α → Option β} {xs : List α} {ys : List β} (h : xs.mapM f = some ys)
    (i : Nat) : ys[i]? = xs[i]?.bind f := by
  by_cases hi : i < xs.length
  · rw [← WalkProof.mapM_get h i hi, List.getElem?_eq_getElem hi]; rfl
  · rw [List.getElem?_eq_none (by rw [WalkProof.mapM_length h]; omega), List.getElem?_eq_none (by omega)]; rfl

theorem lvl_rev {vs : List Val} {k : Nat} (hk : k < vs.length) : (Opd.lvl k).val vs.reverse = vs[k]? := by
  rw [lvl_val (by simp; omega), List.getElem?_reverse (by simp; omega)]
  congr 1; simp; omega

theorem lvl_rev_suffix {vs ρ : List Val} (hs : vs.reverse <:+ ρ) {k : Nat} (hk : k < vs.length) :
    (Opd.lvl k).val ρ = vs[k]? := by
  have h := lvl_rev hk
  rw [List.getElem?_eq_getElem hk] at h ⊢
  exact Opd.val_suffix hs h

/-- The first hole of an unmasked parameter. -/
theorem holeIdx_spec {t : Trees} {i : Nat} (h : ∃ k : Nat, t.holes[k]? = some (HoleSrc.param i)) :
    ∃ k, holeIdx t i = some k ∧ t.holes[k]? = some (HoleSrc.param i) := by
  obtain ⟨k, hk⟩ := h
  unfold holeIdx
  have hmem : (HoleSrc.param i, k) ∈ t.holes.zipIdx := List.mem_zipIdx_iff_getElem?.2 hk
  cases hf : t.holes.zipIdx.find? (fun (s, _) => match s with
      | .param j => j == i
      | _ => false) with
  | none =>
    rw [List.find?_eq_none] at hf
    exact absurd (by simp) (hf _ hmem)
  | some p =>
    obtain ⟨s, k'⟩ := p
    have hp := List.find?_some hf
    have hm := List.mem_of_find?_eq_some hf
    rw [List.mem_zipIdx_iff_getElem?] at hm
    refine ⟨k', rfl, ?_⟩
    cases s with
    | param j => simp only [beq_iff_eq] at hp; subst hp; exact hm
    | level _ => simp at hp
    | atom _ => simp at hp

/-- The callee's parameters in the specialisation. -/
theorem σ_get (D : Site) {i : Nat} (hi : i < D.n) :
    D.σ[i]? = some (Ent.opd (specParam D.defs D.roots D.m D.t (D.n - 1 - i))) := by
  unfold Site.σ
  rw [List.getElem?_map, List.getElem?_reverse (by simp; omega), List.getElem?_range (by simp; omega)]
  simp

theorem σ_length (D : Site) : D.σ.length = D.n := by simp [Site.σ]

/-! ## The specialisation's simulation -/

/-- Pairs of the caller's levels' values and the level holes' values. -/
def lvlPairs (D : Site) (Hv : List Val) : List (Val × Val) :=
  (List.range D.H).filterMap fun (k : Nat) => match (D.t.holes[k]? : Option HoleSrc) with
    | some (HoleSrc.level l) => ((Opd.lvl l).val D.ρs).bind fun v => (Hv[k]?).map (v, ·)
    | _ => none

theorem lvlPairs_lvls (D : Site) {Hv : List Val}
    (hlv : ∀ (k l : Nat), D.t.holes[k]? = some (.level l) →
      ∃ v w, (Opd.lvl l).val D.ρs = some v ∧ Hv[k]? = some w ∧ R4 P Q v w) :
    D.Lvls Hv (lvlPairs D Hv) ∧ ∀ p ∈ lvlPairs D Hv, R4 P Q p.1 p.2 := by
  refine ⟨fun k l hk => ?_, fun p hp => ?_⟩
  · obtain ⟨v, w, hv, hw, -⟩ := hlv k l hk
    refine ⟨v, w, hv, hw, List.mem_filterMap.2 ⟨k, List.mem_range.2 (List.getElem?_eq_some_iff.1 hk).1, ?_⟩⟩
    simp [hk, hv, hw]
  · obtain ⟨k, -, hk⟩ := List.mem_filterMap.1 hp
    split at hk
    · next l hkl =>
      obtain ⟨v, w, hv, hw, hvw⟩ := hlv k l hkl
      rw [hv, hw] at hk
      simp only [Option.bind_some, Option.map_some, Option.some.injEq] at hk
      subst hk
      exact hvw
    · cases hk

/-- **A specialisation simulates its callee**, given the walk's simulation
below the bound. -/
theorem spec_sim (hglob : GlobRel P Q) {n : Nat}
    (hW : ∀ m < n, ∀ fuel, WalkAt P Q (V P Q) (RwClo P Q) m fuel) {D : Site} (hD : D.Ok P Q) :
    SpecSim P Q n D := by
  intro vs Hv hact hlv hpar
  obtain ⟨gdS, hQs, hHps, hbody⟩ := hD.hs
  obtain ⟨hvl, hHl, hroots⟩ := hact
  rw [hD.hg, hQs]
  simp only [Result.ofOption, Result.bind_ok]
  have hvl' : vs.length = D.gd.ps.length := hvl
  have hHl' : Hv.length = gdS.ps.length := by rw [hHl, hHps]
  simp only [callVal, hvl', hHl', if_true]
  refine SimUpTo.later fun i hi => ?_
  -- the prologue's frame
  have hF0 : FrameOk P Q D.ρs Hv.reverse D.m0 := by
    intro l o hl
    obtain ⟨⟨l', h⟩, hmem, he⟩ := List.mem_map.1 (lookup_mem hl)
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨v, w, hv, hw, hvw⟩ := hlv h l' (hD.trees.lh l' h hmem)
    have hh : h < Hv.length := (List.getElem?_eq_some_iff.1 hw).1
    exact ⟨v, w, hv, by rw [lvl_rev hh, hw], hvw⟩
  have hm0 : MLvl D.m0 := fun p hp => by
    obtain ⟨⟨l, h⟩, -, rfl⟩ := List.mem_map.1 hp
    exact ⟨h, rfl⟩
  have hlh0 : ∀ l h, (l, h) ∈ D.t.levelHoles → (D.m0.lookup l).isSome := fun l h hm =>
    lookup_isSome_of_mem (List.mem_map.2 ⟨(l, h), hm, rfl⟩)
  have hpro : prologue P D.defs D.m0 Hv.reverse.length (sortNats D.t.needed) = .ok (D.pro, D.m) := by
    rw [List.length_reverse, hHl]; exact hD.pro
  obtain ⟨Fv, hFl, heval, hF, -, hlh, hneed⟩ := prologue_frame hglob hD.defs hD.trees _ _ _ _ _ hpro
    (sorted_sortNats _) (fun l h => mem_sortNats.1 h) hF0 hm0 hlh0
    (fun l hl hn => absurd (mem_sortNats.2 hl) hn)
  -- the callee's parameters
  have havail : ∀ o, Covered D.defs D.t o → Avail D.defs D.m o := fun o hc => by
    cases o with
    | lvl l =>
      rcases hc with ⟨h, hm⟩ | hn | hlit
      · exact .inl (hlh l h hm)
      · exact .inl (hneed l hn)
      · exact .inr hlit
    | lit _ => trivial
    | box => trivial
  have henv : WEnv Q (V P Q) (RwClo P Q) (D.cfg P) (List.replicate D.n true) D.σ vs.reverse (Fv ++ Hv.reverse) := by
    have h := WalkProof.WEnv.pushIdx (Q := Q) (Valid := V P Q) (Xc := RwClo P Q) (C := D.cfg P)
      (ρ' := Fv ++ Hv.reverse) (σP := D.σ) (V := vs.reverse) (by simp [σ_length, hvl])
      (fun j hj => ?_) WEnv.nil
    · simpa [σ_length] using h
    · rw [σ_length] at hj
      have hσ := σ_get D hj
      rw [List.getElem?_eq_getElem (by rw [σ_length]; exact hj)] at hσ
      have hvj : vs.reverse[j]? = vs[D.n - 1 - j]? := by
        rw [List.getElem?_reverse (by omega), hvl]
      cases hlk : D.roots.lookup (D.n - 1 - j) with
      | some o =>
        have hsp : specParam D.defs D.roots D.m D.t (D.n - 1 - j) = mapOpd D.defs D.m o := by
          simp [specParam, specFixed, hlk]
        obtain ⟨-, hcov, -⟩ := hD.roots _ o hlk
        have hov := hroots _ o hlk
        obtain ⟨v, hv⟩ : ∃ v, vs[D.n - 1 - j]? = some v := ⟨_, List.getElem?_eq_getElem (by omega)⟩
        rw [hv] at hov
        obtain ⟨w, hw, hvw⟩ := mapOpd_rel hD.defs hF (havail o hcov) hov
        exact ⟨_, w, by rw [Option.some.inj hσ, hsp], hw, v, by rw [hvj, hv], hvw⟩
      | none =>
        obtain ⟨k, hk, hkp⟩ := holeIdx_spec (hD.params _ (by omega) hlk)
        have hsp : specParam D.defs D.roots D.m D.t (D.n - 1 - j) = .lvl k := by
          simp [specParam, specFixed, hlk, hk]
        obtain ⟨v, w, hv, hw, hvw⟩ := hpar k _ hkp
        have hkH : k < Hv.length := (List.getElem?_eq_some_iff.1 hw).1
        refine ⟨_, w, by rw [Option.some.inj hσ, hsp], ?_, v, by rw [hvj, hv], hvw⟩

        exact Opd.val_append Fv (by rw [lvl_rev hkH]; exact hw)
  obtain ⟨hlvls, hpairs⟩ := lvlPairs_lvls D hlv
  have hV : VOk Q (V P Q) (RwClo P Q) (D.cfg P) vs.reverse (Fv ++ Hv.reverse) :=
    .mk (.inr ⟨D, vs, Hv, hD, rfl, ⟨hvl, hHl, hroots⟩, hlvls, List.suffix_refl _, List.suffix_append _ _⟩)
      hpairs
  obtain ⟨fuel, s, s', hwalk⟩ := hD.walk
  have hk : KontW Q (V P Q) (RwClo P Q) i .ret (fun v _ => .ok v) (Fv ++ Hv.reverse) [] :=
    ⟨_, rfl, fun x w hxw => SimUpTo.ok hxw⟩
  refine ((hW i (by omega) fuel).walk hwalk vs.reverse [] (Fv ++ Hv.reverse) [] _ [] _ hV henv .nil
    (by simp [hFl, hHl]; omega) rfl (WalkProof.factsOk_leaf _)
    ⟨fun j hj => by simp [List.getElem?_replicate] at hj, fun j hj => by simp at hj⟩ hk).congr
    (fun k => (Sem.Result.bind_pure _).symm) (fun k => ?_)
  rw [hbody, heval]

/-! ## Redirected calls -/

theorem fixedAt_spec {r : Walk.Redirect} {d : Nat} {as : List Atom} (h : Walk.fixedAt r d as = true) :
    as.length = r.fixedArgs.length ∧ ∀ (i : Nat) (a : Atom) (f : Opd), as[i]? = some a →
      r.fixedArgs[i]? = some (some f) → a = .var (d - 1 - i) ∨ (f = .box ∧ a = .box) := by
  unfold Walk.fixedAt at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨hl, hall⟩ := h
  refine ⟨hl, fun i a f ha hf => ?_⟩
  have hmem : ((a, i), some f) ∈ as.zipIdx.zip r.fixedArgs := by
    refine List.mem_iff_getElem?.2 ⟨i, ?_⟩
    rw [List.getElem?_zip_eq_some, List.getElem?_zipIdx, ha]
    exact ⟨by simp, hf⟩
  have := hall _ hmem
  simp only [Option.isNone_some, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    Option.some.injEq] at this
  rcases this with h1 | ⟨h1, h2⟩
  · exact .inl (Atom.beq_eq h1)
  · exact .inr ⟨h1, Atom.beq_eq h2⟩

theorem redirectArgs_spec {r : Walk.Redirect} {os os' : List Opd} (h : Walk.redirectArgs r os = some os') :
    r.holes.mapM (fun h => match h with
      | .param i => os[i]?
      | .fixed o => some o) = some os' := by
  unfold Walk.redirectArgs at h
  split at h
  · exact h
  · cases h

theorem site_holes (D : Site) (k : Nat) :
    D.r.holes[k]? = (D.t.holes[k]?).map fun h => match h with
      | .param i => Walk.Hole.param i
      | _ => .fixed (.lvl k) := by
  simp only [Site.r, specRedirect, List.getElem?_map, List.getElem?_zipIdx, Option.map_map]
  cases D.t.holes[k]? with
  | none => rfl
  | some h => cases h <;> simp

theorem site_fixedArgs (D : Site) {i : Nat} (hi : i < D.n) {o : Opd} (hl : D.roots.lookup i = some o) :
    D.r.fixedArgs[i]? = some (some (mapOpd D.defs D.m o)) := by
  simp [Site.r, specRedirect, List.getElem?_map, List.getElem?_range hi, specFixed, hl]

/-- **A redirected call** calls the specialisation on another activation of
the same site: its masked arguments are the activation's own (`fixedAt`),
its level holes are passed on. -/
theorem red_sim {n : Nat} (hspec : ∀ D : Site, D.Ok P Q → SpecSim P Q n D) {C : Cfg} {ρ ρ' : List Val}
    {r : Walk.Redirect} (hV : VOk Q (V P Q) (RwClo P Q) C ρ ρ') (hr : C.redirect = some r) :
    WalkProof.RedSim (P := P) (Q := Q) (Valid := V P Q) (Xc := RwClo P Q) n r ρ ρ' := by
  cases hV with
  | mk hv hprs =>
  rcases hv with rfl | ⟨D, vs, Hv, hD, rfl, ⟨hvl, hHl, hroots⟩, hlv, hsρ, hsρ'⟩
  · cases hr
  · simp only [Site.cfg, Option.some.injEq] at hr
    subst hr
    intro as os os' vc ws hfix hred hvc hws hvws
    obtain ⟨hasl, hasv⟩ := fixedAt_spec hfix
    have hfl : D.r.fixedArgs.length = D.n := by simp [Site.r, specRedirect]
    have hos' := redirectArgs_spec hred
    have hvcl : vc.length = D.n := by rw [evalAtoms_length ρ hvc, hasl, hfl]
    have hwsl : ws.length = os.length := WalkProof.mapM_length hws
    -- an element of the new specialisation arguments
    have helt : ∀ k o, os'[k]? = some o →
        (∃ i, D.t.holes[k]? = some (.param i) ∧ os[i]? = some o) ∨
        ((∀ i, D.t.holes[k]? ≠ some (.param i)) ∧ o = .lvl k ∧ k < D.H) := by
      intro k o hk
      rw [mapM_getElem? hos' k, site_holes] at hk
      cases hh : D.t.holes[k]? with
      | none => rw [hh] at hk; cases hk
      | some h =>
        rw [hh] at hk
        have hkH : k < D.H := (List.getElem?_eq_some_iff.1 hh).1
        cases h with
        | param i => exact .inl ⟨i, rfl, by simpa using hk⟩
        | level l =>
          simp only [Option.map_some, Option.bind_some, Option.some.injEq] at hk
          exact .inr ⟨(fun i e => by cases e), hk.symm, hkH⟩
        | atom o' =>
          simp only [Option.map_some, Option.bind_some, Option.some.injEq] at hk
          exact .inr ⟨(fun i e => by cases e), hk.symm, hkH⟩
    obtain ⟨ws', hws'⟩ : ∃ ws', os'.mapM (·.val ρ') = some ws' := by
      refine mapM_exists fun o ho => ?_
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 ho
      rcases helt k o hk with ⟨i, -, hi⟩ | ⟨-, rfl, hkH⟩
      · have := mapM_getElem? hws i
        rw [hi] at this
        cases hw : ws[i]? with
        | none =>
          have hil : i < os.length := (List.getElem?_eq_some_iff.1 hi).1
          rw [List.getElem?_eq_none_iff] at hw; omega
        | some w => rw [hw] at this; exact ⟨w, this.symm⟩
      · have hk' : k < Hv.length := by rw [hHl]; exact hkH
        exact ⟨_, (lvl_rev_suffix hsρ' hk').trans (List.getElem?_eq_getElem hk')⟩
    have hws'l : ws'.length = D.H := by
      rw [WalkProof.mapM_length hws', WalkProof.mapM_length hos']; simp [Site.r, specRedirect, Site.H]
    refine ⟨ws', hws', hspec D hD vc ws' ⟨hvcl, hws'l, fun i o hl => ?_⟩ (fun k l hk => ?_) (fun k i hk => ?_)⟩
    · -- a masked argument is the activation's
      obtain ⟨hi, -, -⟩ := hD.roots i o hl
      obtain ⟨a, ha⟩ : ∃ a, as[i]? = some a := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      rcases hasv i a _ ha (site_fixedArgs D hi hl) with rfl | ⟨hbox, rfl⟩
      · obtain ⟨v, hv, hvi⟩ := evalAtoms_get hvc ha
        rw [hroots i o hl, hvi]
        have hiρ : i < ρ.length := by
          have := hsρ.length_le; simp at this; omega
        have := lvl_rev_suffix hsρ (show i < vs.length by omega)
        rw [lvl_val hiρ] at this
        simp only [Atom.eval] at hv
        rw [← this, hv]
      · have ho : o = .box := site_mapOpd_eq_box hD hl hbox
        subst ho
        obtain ⟨v, hv, hvi⟩ := evalAtoms_get hvc ha
        simp only [Atom.eval, Option.some.injEq] at hv
        subst hv
        rw [hvi]; rfl
    · -- a level hole is passed on
      obtain ⟨v, w, hv, hw, hm⟩ := hlv k l hk
      refine ⟨v, w, hv, ?_, hprs _ hm⟩
      have hkH : k < D.H := (List.getElem?_eq_some_iff.1 hk).1
      obtain ⟨o, ho⟩ : ∃ o, os'[k]? = some o := ⟨_, List.getElem?_eq_getElem (by
        rw [WalkProof.mapM_length hos']; simp [Site.r, specRedirect]; exact hkH)⟩
      rcases helt k o ho with ⟨i, hki, -⟩ | ⟨-, rfl, -⟩
      · rw [hk] at hki; cases hki
      · rw [mapM_getElem? hws' k, ho]
        have hk' : k < Hv.length := by rw [hHl]; exact hkH
        simp only [Option.bind_some]
        rw [lvl_rev_suffix hsρ' hk', hw]
    · -- an unmasked parameter's hole gets the call's argument
      have hkH : k < D.H := (List.getElem?_eq_some_iff.1 hk).1
      obtain ⟨o, ho⟩ : ∃ o, os'[k]? = some o := ⟨_, List.getElem?_eq_getElem (by
        rw [WalkProof.mapM_length hos']; simp [Site.r, specRedirect]; exact hkH)⟩
      rcases helt k o ho with ⟨i', hki, hoi⟩ | ⟨hne, -, -⟩
      · rw [hk] at hki; cases hki
        have hil : i < os.length := (List.getElem?_eq_some_iff.1 hoi).1
        rcases hvws.get i with ⟨h1, h2⟩ | ⟨v, w, hv, hw, hvw⟩
        · rw [List.getElem?_eq_none_iff] at h2; omega
        · refine ⟨v, w, hv, ?_, hvw⟩
          rw [mapM_getElem? hws' k, ho]
          have := mapM_getElem? hws i
          rw [hoi, hw] at this
          exact this.symm
      · exact absurd hk (hne i)

end IxCC.Anf.Specialize.Proof
