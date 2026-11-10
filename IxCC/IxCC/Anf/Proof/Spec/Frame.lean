import IxCC.Anf.Proof.Spec.Rel

/-! # P4: the specialisation's frame

A specialisation's body starts with a prologue that rebuilds the caller's
definitions the value trees need (`prologue`): constructors of mapped
operands, function globals' closures, and local functions walked over the
caller's captured operands. From an activation whose level holes are
related to the caller's levels at the site, the prologue's values are
related to the caller's values of the levels they rebuild (`FrameOk`), so
every operand the trees cover is reproduced (`prologue_frame`). -/

set_option autoImplicit false

namespace IxCC.Anf.Specialize.Proof

open Walk (Ent Cfg)
open WalkProof (WV WVs VOk WEnv WEnt)
open IxCC.Sem (Result)

theorem except_bind_ok {α β : Type} {x : Except String α} {f : α → Except String β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

variable {P Q : Program}

/-- The output's function globals' closures against the input's. -/
def GlobRel (P Q : Program) : Prop :=
  ∀ g gd, P.global? g = some gd → gd.ps ≠ [] → ∃ gdQ, Q.global? g = some gdQ ∧ gdQ.ps = gd.ps ∧
    R4 P Q (.clos [] gd.ps.length gd.body []) (.clos [] gd.ps.length gdQ.body [])

/-- The prologue's level map against the caller's environment at the site:
each mapped level's value is related to its operand's value. -/
def FrameOk (P Q : Program) (ρs ρt : List Val) (m : List (Nat × Opd)) : Prop :=
  ∀ l o, m.lookup l = some o → ∃ v w, (Opd.lvl l).val ρs = some v ∧ o.val ρt = some w ∧ R4 P Q v w

/-- Every mapped operand is a level. -/
def MLvl (m : List (Nat × Opd)) : Prop := ∀ p ∈ m, ∃ x, p.2 = .lvl x

/-- An operand the level map reproduces. -/
def Avail (defs : Src.NatMap Def) (m : List (Nat × Opd)) : Opd → Prop
  | .lvl l => (m.lookup l).isSome ∨ ∃ n, defs.get? l = some (.lit n)
  | _ => True

variable {defs : Src.NatMap Def} {ρs : List Val}

theorem FrameOk.append {ρt : List Val} {m : List (Nat × Opd)} (h : FrameOk P Q ρs ρt m) (ext : List Val) :
    FrameOk P Q ρs (ext ++ ρt) m := fun l o hl => by
  obtain ⟨v, w, hv, hw, hvw⟩ := h l o hl
  exact ⟨v, w, hv, Opd.val_append ext hw, hvw⟩

theorem mapOpd_lvl (m : List (Nat × Opd)) (l : Nat) :
    mapOpd defs m (.lvl l) = match m.lookup l, defs.get? l with
      | some o, _ => o
      | none, some (.lit n) => .lit (.nat n)
      | none, _ => .box := rfl

/-- A reproduced operand's value in the specialisation is related to its
value at the site. -/
theorem mapOpd_rel (hD : DefsOk P defs ρs) {ρt : List Val} {m : List (Nat × Opd)} (hF : FrameOk P Q ρs ρt m)
    {o : Opd} (ha : Avail defs m o) {v : Val} (hv : o.val ρs = some v) :
    ∃ w, (mapOpd defs m o).val ρt = some w ∧ R4 P Q v w := by
  cases o with
  | lvl l =>
    rw [mapOpd_lvl]
    cases hl : m.lookup l with
    | some o =>
      obtain ⟨v', w, hv', hw, hvw⟩ := hF l o hl
      rw [hv] at hv'; cases hv'
      exact ⟨w, hw, hvw⟩
    | none =>
      rcases ha with ha | ⟨n, hn⟩
      · rw [hl] at ha; cases ha
      · have := hD l _ hn
        simp only [DefOk] at this
        rw [hv] at this; cases this
        simp only [hn]
        exact ⟨_, rfl, .lit⟩
  | lit l => simp only [Opd.val, Option.some.injEq] at hv; subst hv; exact ⟨_, rfl, .lit⟩
  | box => simp only [Opd.val, Option.some.injEq] at hv; subst hv; exact ⟨_, rfl, .box⟩

theorem mapOpd_ne_box {m : List (Nat × Opd)} (hm : MLvl m) {l : Nat} (ha : Avail defs m (.lvl l)) :
    mapOpd defs m (.lvl l) ≠ .box := by
  rw [mapOpd_lvl]
  cases hl : m.lookup l with
  | some o =>
    obtain ⟨x, hx⟩ := hm (l, o) (lookup_mem hl)
    simp only at hx ⊢
    rw [hx]; exact fun h => nomatch h
  | none =>
    rcases ha with ha | ⟨n, hn⟩
    · rw [hl] at ha; cases ha
    · simp only [hn]; exact fun h => nomatch h

theorem avail_of_ne_box {m : List (Nat × Opd)} {l : Nat} (h : mapOpd defs m (.lvl l) ≠ .box) :
    Avail defs m (.lvl l) := by
  rw [mapOpd_lvl] at h
  cases hl : m.lookup l with
  | some o => exact .inl (by simp [hl])
  | none =>
    rw [hl] at h
    cases hd : defs.get? l with
    | none => rw [hd] at h; exact absurd rfl h
    | some df =>
      rw [hd] at h
      cases df with
      | lit n => exact .inr ⟨n, hd⟩
      | _ => exact absurd rfl h

/-! ## A walk environment entry by entry -/

theorem wenv_ofIdx {Valid : Cfg → List Val → List Val → List (Val × Val) → Prop}
    {Xc : Nat → List Val → Exp → Exp → Prop} {C : Cfg} {ρ' : List Val} :
    ∀ (σ : List Ent) (live : List Bool) (ρ : List Val), σ.length = ρ.length → live.length = ρ.length →
    (∀ (j : Nat) (e : Ent) (v : Val), σ[j]? = some e → ρ[j]? = some v → live[j]? = some true →
      WEnt Q Valid Xc C e v ρ') →
    (∀ j : Nat, live[j]? = some false → σ[j]? = some (Ent.opd Opd.box)) →
    WEnv Q Valid Xc C live σ ρ ρ'
  | [], [], [], _, _, _, _ => .nil
  | e :: σ, b :: live, v :: ρ, h1, h2, hl, hd => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h1 h2
    have hrest := wenv_ofIdx σ live ρ h1 h2 (fun j e v he hv hb => hl (j + 1) e v he hv hb)
      (fun j hb => hd (j + 1) hb)
    cases b with
    | true => exact .live (hl 0 e v rfl rfl rfl) hrest
    | false =>
      have := hd 0 rfl
      simp only [List.getElem?_cons_zero, Option.some.injEq] at this
      subst this
      exact .dead hrest
  | [], _ :: _, _, h1, h2, _, _ => by simp at h1 h2; omega
  | [], [], _ :: _, h1, _, _, _ => by simp at h1
  | _ :: _, [], _, h1, h2, _, _ => by simp at h1 h2; omega
  | _ :: _, _ :: _, [], h1, _, _, _ => by simp at h1

/-! ## Rebuilt local functions -/

theorem drop_get {ρ : List Val} {df j : Nat} (hdf : df ≤ ρ.length) (hj : j < df) :
    (ρ.drop (ρ.length - df))[j]? = (Opd.lvl (df - 1 - j)).val ρ := by
  rw [List.getElem?_drop, lvl_val (by omega)]
  congr 1; omega

/-- A local function the prologue rebuilds: its walk over the captured
operands is a walked closure related to the caller's closure. -/
theorem rebuilt_fn (hD : DefsOk P defs ρs) {ρt : List Val} {m : List (Nat × Opd)} (hF : FrameOk P Q ρs ρt m)
    (hm : MLvl m) {l df : Nat} {ps : List Ixon.V3.BinderContract} {b b' : Exp} {idx : Nat}
    (hdl : defs.get? l = some (.fn df ps b idx))
    (hav : ∀ j ∈ b.free ps.length, j < df → Avail defs m (.lvl (df - 1 - j))) {s' : Walk.Fires}
    (hw : (Walk.walk { prog := P } Walk.fuel
      { σ := Walk.entsOf (paramOpds ρt.length ps.length) ++
          (List.range df).map fun j => Ent.opd (mapOpd defs m (.lvl (df - 1 - j))) }
      { d := ρt.length + ps.length, dj := 0, facts := .leaf } b .ret).run {} = .ok (b', s')) :
    ∃ v, (Opd.lvl l).val ρs = some v ∧ ps ≠ [] ∧ R4 P Q v (.clos ρt ps.length b' []) := by
  obtain ⟨hle, hps, hl⟩ := hD l _ hdl
  have hlt := lvl_lt hl
  have hdf : df ≤ ρs.length := by omega
  refine ⟨_, hl, hps, ?_⟩
  let live : List Bool := (List.range df).map fun j => !(mapOpd defs m (.lvl (df - 1 - j)) == .box)
  have hlen : (ρs.drop (ρs.length - df)).length = df := by simp; omega
  have henv : WEnv Q (V P Q) (RwClo P Q) { prog := P } live
      ((List.range df).map fun j => Ent.opd (mapOpd defs m (.lvl (df - 1 - j)))) (ρs.drop (ρs.length - df)) ρt := by
    refine wenv_ofIdx _ _ _ (by simp [hlen]) (by simp [live, hlen]) (fun j e v he hv hb => ?_) (fun j hb => ?_)
    · have hj : j < df := by
        have := (List.getElem?_eq_some_iff.1 he).1; simpa using this
      simp only [List.getElem?_map, List.getElem?_range hj, Option.map_some, Option.some.injEq] at he
      subst he
      simp only [live, List.getElem?_map, List.getElem?_range hj, Option.map_some, Option.some.injEq,
        Bool.not_eq_true', beq_eq_false_iff_ne] at hb
      rw [drop_get hdf hj] at hv
      obtain ⟨w, hw', hvw⟩ := mapOpd_rel hD hF (avail_of_ne_box hb) hv
      exact .opd hw' hvw
    · have hj : j < df := by
        have := (List.getElem?_eq_some_iff.1 hb).1; simpa [live] using this
      simp only [live, List.getElem?_map, List.getElem?_range hj, Option.map_some, Option.some.injEq,
        Bool.not_eq_false', beq_iff_eq] at hb
      simp [List.getElem?_range hj, hb]
  have hnd : WalkProof.NoDead (List.replicate ps.length true ++ live) [] b := by
    refine ⟨fun i hi => ?_, fun j hj => by simp at hj⟩
    by_cases hin : i < ps.length
    · rw [WalkProof.getElem?_replicate_lt true live hin] at hi; cases hi
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + ps.length := ⟨i - ps.length, by omega⟩
      rw [WalkProof.getElem?_replicate_append] at hi
      have hj : j < df := by
        have := (List.getElem?_eq_some_iff.1 hi).1; simpa [live] using this
      simp only [live, List.getElem?_map, List.getElem?_range hj, Option.map_some, Option.some.injEq,
        Bool.not_eq_false', beq_iff_eq] at hi
      by_cases hocc : Exp.occ (j + ps.length) b = 0
      · exact hocc
      · exfalso
        have hfree := occ_free b ps.length j (by rw [Nat.add_comm]; exact hocc)
        exact mapOpd_ne_box hm (hav j hfree hj) hi
  exact .walkc (C := { prog := P }) (σP := Walk.entsOf (paramOpds ρt.length ps.length))
    (got := []) (got' := []) (oOf := fun _ => .box) (wOf := fun _ => .box) (m := ps.length)
    (.mk (prs := []) (.inl rfl) fun _ h => nomatch h) hw henv (WalkProof.factsOk_leaf _) hnd
    (by simp [Walk.entsOf, WalkProof.paramOpds_length]) (Nat.le_refl _) (by simp)
    (by simpa using List.length_pos_iff.2 hps) (by simp) (fun p hp => by omega) (fun p v hp => by omega)
    (fun p _ hp2 => by
      simp only [Walk.entsOf, List.getElem?_map, WalkProof.paramOpds_get _ _ hp2, Option.map_some]
      simp)
    (fun _ _ _ _ _ hv => by simp at hv)

/-! ## The prologue -/

/-- The binding the prologue emits for a level. -/
def PBind (P : Program) (defs : Src.NatMap Def) (m : List (Nat × Opd)) (t l : Nat) (b : Bind) : Prop :=
  (∃ c fs, defs.get? l = some (.con c fs) ∧ b = .con c (fs.map fun o => (mapOpd defs m o).atom t)) ∨
  (∃ g, defs.get? l = some (.glob g) ∧ b = .glob g) ∨
  (∃ df ps body idx body' s', defs.get? l = some (.fn df ps body idx) ∧
    (Walk.walk { prog := P } Walk.fuel
      { σ := Walk.entsOf (paramOpds t ps.length) ++
          (List.range df).map fun j => Ent.opd (mapOpd defs m (.lvl (df - 1 - j))) }
      { d := t + ps.length, dj := 0, facts := .leaf } body .ret).run {} = .ok (body', s') ∧
    b = .fn ps body')

theorem prologue_cons_inv {m : List (Nat × Opd)} {t l : Nat} {ls : List Nat} {pro : List Bind}
    {m' : List (Nat × Opd)} (h : prologue P defs m t (l :: ls) = .ok (pro, m')) :
    ∃ b bs, pro = b :: bs ∧ PBind P defs m t l b ∧
      prologue P defs ((l, .lvl t) :: m) (t + 1) ls = .ok (bs, m') := by
  rw [prologue.eq_2] at h
  have rest : ∀ b, PBind P defs m t l b →
      ((fun b => do
          let __x ← prologue P defs ((l, Opd.lvl t) :: m) (t + 1) ls
          match __x with
            | (bs, m) => pure (b :: bs, m)) b : Except String (List Bind × List (Nat × Opd))) = .ok (pro, m') →
      ∃ b bs, pro = b :: bs ∧ PBind P defs m t l b ∧
        prologue P defs ((l, .lvl t) :: m) (t + 1) ls = .ok (bs, m') := by
    intro b hb h
    obtain ⟨⟨bs, m2⟩, hrest, h⟩ := except_bind_ok h
    cases h
    exact ⟨b, bs, rfl, hb, hrest⟩
  split at h
  · next c fs hdl =>
    obtain ⟨b, hb, h⟩ := except_bind_ok h
    cases hb
    exact rest _ (.inl ⟨c, fs, hdl, rfl⟩) h
  · next g hdl =>
    obtain ⟨b, hb, h⟩ := except_bind_ok h
    cases hb
    exact rest _ (.inr (.inl ⟨g, hdl, rfl⟩)) h
  · next df ps body idx hdl =>
    obtain ⟨⟨body', s'⟩, hw, h⟩ := except_bind_ok h
    obtain ⟨b, hb, h⟩ := except_bind_ok h
    cases hb
    exact rest _ (.inr (.inr ⟨df, ps, body, idx, body', s', hdl, hw, rfl⟩)) h
  · obtain ⟨b, hb, h⟩ := except_bind_ok h
    cases hb

theorem mapOpds_rel (hD : DefsOk P defs ρs) {ρt : List Val} {m : List (Nat × Opd)} (hF : FrameOk P Q ρs ρt m) :
    ∀ {fs : List Opd} {vs : List Val}, (∀ o ∈ fs, Avail defs m o) → fs.mapM (·.val ρs) = some vs →
      ∃ ws, (fs.map (mapOpd defs m)).mapM (·.val ρt) = some ws ∧ WVs Q (V P Q) (RwClo P Q) vs ws
  | [], vs, _, h => by simp at h; subst h; exact ⟨[], rfl, .nil⟩
  | o :: fs, vs, ha, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨v, hv, vs', hvs, rfl⟩ := h
    obtain ⟨w, hw, hvw⟩ := mapOpd_rel hD hF (ha o List.mem_cons_self) hv
    obtain ⟨ws, hws, hvws⟩ := mapOpds_rel hD hF (fun o' h => ha o' (List.mem_cons_of_mem _ h)) hvs
    exact ⟨w :: ws, by simp [List.mapM_cons, hw, hws], .cons hvw hvws⟩

/-- The value of the prologue's binding for a level, against the caller's
value of the level. -/
theorem pbind_val (hglob : GlobRel P Q) (hD : DefsOk P defs ρs) {ρt : List Val} {m : List (Nat × Opd)}
    (hF : FrameOk P Q ρs ρt m) (hm : MLvl m) {t : Trees} {l : Nat} (hneed : NeedOk defs t l)
    (hav : ∀ o, Covered defs t o → (∀ j, o = .lvl j → j < l) → Avail defs m o) {b : Bind}
    (hb : PBind P defs m ρt.length l b) :
    ∃ w v, (∀ k, evalBind Q k ρt b = .ok w) ∧ (Opd.lvl l).val ρs = some v ∧ R4 P Q v w := by
  rcases hb with ⟨c, fs, hdl, rfl⟩ | ⟨g, hdl, rfl⟩ | ⟨df, ps, body, idx, body', s', hdl, hw, rfl⟩
  · obtain ⟨hflt, vs, hvs, hlv⟩ := hD l _ hdl
    unfold NeedOk at hneed; rw [hdl] at hneed
    obtain ⟨ws, hws, hvws⟩ := mapOpds_rel hD hF (fun o ho => hav o (hneed o ho) fun j e => by
      subst e; exact hflt j ho) hvs
    refine ⟨.con c ws, _, fun k => ?_, hlv, .con hvws⟩
    rw [evalBind_con]
    have : fs.map (fun o => (mapOpd defs m o).atom ρt.length) =
        (fs.map (mapOpd defs m)).map (·.atom ρt.length) := by simp
    rw [this, WalkProof.opds_eval hws]; rfl
  · obtain ⟨gd, hg, hps, hlv⟩ := hD l _ hdl
    obtain ⟨gdQ, hQ, hpsQ, hrel⟩ := hglob g gd hg hps
    refine ⟨_, _, fun k => ?_, hlv, hrel⟩
    rw [evalBind_glob, hQ]
    simp only [Result.ofOption, Result.bind_ok]
    unfold globVal
    rw [hpsQ]
    cases hp : gd.ps with
    | nil => exact absurd hp hps
    | cons _ _ => rfl
  · obtain ⟨hle, -, -⟩ := hD l _ hdl
    unfold NeedOk at hneed; rw [hdl] at hneed
    obtain ⟨v, hv, hps, hrel⟩ := rebuilt_fn hD hF hm hdl (fun j hj hjd => hav _ (hneed j hj hjd) fun j' e => by
      cases e; omega) hw
    exact ⟨_, v, fun k => evalBind_fn Q k ρt ps body' hps, hv, hrel⟩

theorem lookup_cons {β : Type} (l l' : Nat) (o : β) (m : List (Nat × β)) :
    ((l, o) :: m).lookup l' = if l' = l then some o else m.lookup l' := by
  simp only [List.lookup]
  by_cases h : l' = l
  · subst h; simp
  · have : (l' == l) = false := by simp [h]
    rw [this, if_neg h]

theorem prologue_m : ∀ {ls : List Nat} {m m' : List (Nat × Opd)} {t : Nat} {pro : List Bind},
    prologue P defs m t ls = .ok (pro, m') → MLvl m →
    MLvl m' ∧ ∀ j, (m.lookup j).isSome ∨ j ∈ ls → (m'.lookup j).isSome
  | [], _, _, _, _, h, hm => by
    rw [prologue.eq_1] at h; cases h
    exact ⟨hm, fun j hj => hj.elim id (by simp)⟩
  | l :: ls, m, _, t, _, h, hm => by
    obtain ⟨b, bs, rfl, -, hrest⟩ := prologue_cons_inv h
    obtain ⟨hm', hms⟩ := prologue_m hrest (fun p hp => by
      rcases List.mem_cons.1 hp with rfl | hp
      · exact ⟨_, rfl⟩
      · exact hm p hp)
    refine ⟨hm', fun j hj => hms j ?_⟩
    rw [lookup_cons]
    by_cases he : j = l
    · rw [if_pos he]; exact .inl rfl
    · rw [if_neg he]
      rcases hj with hj | hj
      · exact .inl hj
      · rcases List.mem_cons.1 hj with hj | hj
        · exact absurd hj he
        · exact .inr hj

theorem site_mapOpd_eq_box {D : Site} (hD : D.Ok P Q) {i : Nat} {o : Opd}
    (hl : D.roots.lookup i = some o) (hbox : mapOpd D.defs D.m o = .box) : o = .box := by
  obtain ⟨-, hcov, -⟩ := hD.roots i o hl
  have hm0 : MLvl D.m0 := fun p hp => by
    obtain ⟨⟨l, h⟩, -, rfl⟩ := List.mem_map.1 hp; exact ⟨h, rfl⟩
  obtain ⟨hm, hms⟩ := prologue_m hD.pro hm0
  cases o with
  | box => rfl
  | lit _ => cases hbox
  | lvl l =>
    have ha : Avail D.defs D.m (.lvl l) := by
      rcases hcov with ⟨h, hmem⟩ | hn | hlit
      · exact .inl (hms l (.inl (lookup_isSome_of_mem (List.mem_map.2 ⟨(l, h), hmem, rfl⟩))))
      · exact .inl (hms l (.inr (mem_sortNats.2 hn)))
      · exact .inr hlit
    exact absurd hbox (mapOpd_ne_box hm ha)

/-- **The prologue's frame**: from a level map related to the caller's
levels at the site, the prologue evaluates to values related to the levels
it rebuilds, and maps every level hole and every needed level. -/
theorem prologue_frame (hglob : GlobRel P Q) (hD : DefsOk P defs ρs) {t : Trees} {np : Nat}
    (hT : TreesOk defs ρs.length np [] t) :
    ∀ (ls : List Nat) (m : List (Nat × Opd)) (ρt : List Val) (pro : List Bind) (m' : List (Nat × Opd)),
    prologue P defs m ρt.length ls = .ok (pro, m') →
    ls.Pairwise (· ≤ ·) → (∀ l ∈ ls, l ∈ t.needed) →
    FrameOk P Q ρs ρt m → MLvl m →
    (∀ l h, (l, h) ∈ t.levelHoles → (m.lookup l).isSome) →
    (∀ l ∈ t.needed, l ∉ ls → (m.lookup l).isSome) →
    ∃ Fv : List Val, Fv.length = pro.length ∧
      (∀ k J e, eval Q k ρt J (binds pro e) = eval Q k (Fv ++ ρt) J e) ∧
      FrameOk P Q ρs (Fv ++ ρt) m' ∧ MLvl m' ∧
      (∀ l h, (l, h) ∈ t.levelHoles → (m'.lookup l).isSome) ∧ (∀ l ∈ t.needed, (m'.lookup l).isSome)
  | [], m, ρt, pro, m', h, _, _, hF, hm, hlh, hn => by
    rw [prologue.eq_1] at h
    cases h
    exact ⟨[], rfl, fun k J e => rfl, by simpa using hF, hm, hlh, fun l hl => hn l hl (by simp)⟩
  | l :: ls, m, ρt, pro, m', h, hsort, hls, hF, hm, hlh, hn => by
    obtain ⟨b, bs, rfl, hb, hrest⟩ := prologue_cons_inv h
    have hl := hls l List.mem_cons_self
    have hneed := hT.need l hl List.not_mem_nil
    have hsort' := List.pairwise_cons.1 hsort
    have hdone : ∀ j ∈ t.needed, j < l → (m.lookup j).isSome := fun j hj hjl =>
      hn j hj fun hm' => by
        rcases List.mem_cons.1 hm' with rfl | hm'
        · omega
        · have := hsort'.1 j hm'; omega
    have hav : ∀ o, Covered defs t o → (∀ j, o = .lvl j → j < l) → Avail defs m o := by
      intro o hc hlt
      cases o with
      | lvl j =>
        rcases hc with ⟨h, hmem⟩ | hj | hlit
        · exact .inl (hlh j h hmem)
        · exact .inl (hdone j hj (hlt j rfl))
        · exact .inr hlit
      | lit _ => trivial
      | box => trivial
    obtain ⟨w, v, hbw, hv, hvw⟩ := pbind_val hglob hD hF hm hneed hav hb
    have hF2 : FrameOk P Q ρs (w :: ρt) ((l, .lvl ρt.length) :: m) := by
      intro l' o hl'
      rw [lookup_cons] at hl'
      split at hl'
      · next he =>
        subst he; cases hl'
        exact ⟨v, w, hv, Opd.val_lvl_top ρt w, hvw⟩
      · obtain ⟨v', w', hv', hw', hvw'⟩ := hF l' o hl'
        exact ⟨v', w', hv', Opd.val_append [w] hw', hvw'⟩
    have hm2 : MLvl ((l, .lvl ρt.length) :: m) := fun p hp => by
      rcases List.mem_cons.1 hp with rfl | hp
      · exact ⟨_, rfl⟩
      · exact hm p hp
    have hsome : ∀ j, (m.lookup j).isSome → (((l, Opd.lvl ρt.length) :: m).lookup j).isSome := fun j hj => by
      rw [lookup_cons]; split
      · rfl
      · exact hj
    obtain ⟨Fv, hlen, heval, hF', hm', hlh', hn'⟩ := prologue_frame hglob hD hT ls _ (w :: ρt) bs m' hrest hsort'.2
      (fun l' h => hls l' (List.mem_cons_of_mem _ h)) hF2 hm2 (fun l' h hm => hsome l' (hlh l' h hm))
      (fun j hj hjn => by
        by_cases he : j = l
        · rw [lookup_cons, if_pos he]; rfl
        · exact hsome j (hn j hj fun hm => by
            rcases List.mem_cons.1 hm with e | hm
            · exact he e
            · exact hjn hm))
    refine ⟨Fv ++ [w], by simp [hlen], fun k J e => ?_, by simpa using hF', hm', hlh', hn'⟩
    rw [binds.eq_2, eval_bind, hbw]
    simp only [Result.bind_ok]
    rw [heval]; simp

end IxCC.Anf.Specialize.Proof
