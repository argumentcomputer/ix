module

public import IxC.Kernel.Verify.Rename.Ind2

@[expose] public section

/-!
# Renaming and the native recursor's builders

The recursor type and rules the native route generates
(`structRecTyR`, `structRecRhsR` and their parts) at renamed inputs are the
renamed terms, and they are good on good inputs.
-/

set_option linter.unusedSimpArgs false

namespace Ix.Kernel

variable {md md' : Mode} {f : md.Id → md'.Id} {P : KeyScope md}

theorem nativeParts?_map (hf : InjOn f P) (nPd : Nat) {block : List (ConstantInfo md)}
    (hb : ∀ c ∈ block, c.Good P) :
    nativeParts? nPd (block.map (ConstantInfo.mapKeys f)) =
      (nativeParts? nPd block).map (NativeParts.mapKeys f) := by
  unfold nativeParts?
  rw [nativeShape?_map, Option.map_map, Option.map_map]
  cases nativeShape? nPd block with
  | none => rfl
  | some p =>
    simp only [Option.map_some, Function.comp_def, nativeRecPinOk_map hf p hb]
    rfl

/-! ## Binder lists -/

theorem Expr.BindersGood.mono_map {bs : List (Expr md × BinderMeta)} (h : Expr.BindersGood P bs)
    (g : BinderMeta → BinderMeta) : Expr.BindersGood P (bs.map fun b => (b.1, g b.2)) := by
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨b, hb, rfl⟩ := hx
  exact h b hb

theorem Expr.mkPisOf_mapKeys : ∀ (bs : List (Expr md × BinderMeta)) (b : Expr md),
    Expr.mkPisOf (Expr.mapBinders f bs) (b.mapKeys f) = (Expr.mkPisOf bs b).mapKeys f
  | [], _ => rfl
  | (t, m) :: bs, b => by
    simp only [Expr.mapBinders_cons, Expr.mkPisOf, Expr.mkPisOf_mapKeys bs b, Expr.mapKeys]

theorem Expr.mkLamsOf_mapKeys : ∀ (bs : List (Expr md × BinderMeta)) (b : Expr md),
    Expr.mkLamsOf (Expr.mapBinders f bs) (b.mapKeys f) = (Expr.mkLamsOf bs b).mapKeys f
  | [], _ => rfl
  | (t, m) :: bs, b => by
    simp only [Expr.mapBinders_cons, Expr.mkLamsOf, Expr.mkLamsOf_mapKeys bs b, Expr.mapKeys]

theorem Expr.mkPisOf_good : ∀ {bs : List (Expr md × BinderMeta)} {b : Expr md},
    Expr.BindersGood P bs → b.Good P → (Expr.mkPisOf bs b).Good P
  | [], _, _, hb => hb
  | (t, m) :: bs, b, hbs, hb => by
    simp only [Expr.mkPisOf, Expr.Good]
    exact ⟨hbs (t, m) (List.mem_cons_self ..),
      Expr.mkPisOf_good (fun x hx => hbs x (List.mem_cons_of_mem _ hx)) hb⟩

theorem Expr.mkLamsOf_good : ∀ {bs : List (Expr md × BinderMeta)} {b : Expr md},
    Expr.BindersGood P bs → b.Good P → (Expr.mkLamsOf bs b).Good P
  | [], _, _, hb => hb
  | (t, m) :: bs, b, hbs, hb => by
    simp only [Expr.mkLamsOf, Expr.Good]
    exact ⟨hbs (t, m) (List.mem_cons_self ..),
      Expr.mkLamsOf_good (fun x hx => hbs x (List.mem_cons_of_mem _ hx)) hb⟩

@[simp] theorem Expr.mapBinders_length (bs : List (Expr md × BinderMeta)) :
    (Expr.mapBinders f bs).length = bs.length := by
  simp [Expr.mapBinders]

theorem Expr.mapBinders_getD (bs : List (Expr md × BinderMeta)) (i : Nat) :
    (Expr.mapBinders f bs).getD i default =
      ((bs.getD i default).1.mapKeys f, (bs.getD i default).2) := by
  simp only [Expr.mapBinders, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases bs[i]? <;> rfl

theorem Expr.BindersGood.getD {bs : List (Expr md × BinderMeta)} (h : Expr.BindersGood P bs)
    (i : Nat) : (bs.getD i default).1.Good P := by
  simp only [List.getD_eq_getElem?_getD]
  cases hb : bs[i]? with
  | none => exact (show Expr.Good P (default : Expr md) from trivial)
  | some b => exact h b (List.mem_of_getElem? hb)

/-! ## The field telescopes -/

theorem structIdxAt_map (nF o i l m : Nat) (e : Expr md) :
    structIdxAt nF o i l m (e.mapKeys f) = (structIdxAt nF o i l m e).mapKeys f := by
  simp [structIdxAt]

theorem structIdxAt_good {e : Expr md} (he : e.Good P) (nF o i l m : Nat) :
    (structIdxAt nF o i l m e).Good P :=
  (he.liftLooseBVars _ _).liftLooseBVars _ _

theorem structTeleAt_map (nF o i l : Nat) (pw : PropWhen) (tele : List (Expr md × BinderMeta)) :
    structTeleAt nF o i l pw (Expr.mapBinders f tele) =
      Expr.mapBinders f (structTeleAt nF o i l pw tele) := by
  simp only [structTeleAt, Expr.mapBinders_length, Expr.mapBinders, List.map_map, List.length_map,
    Function.comp_def]
  apply List.map_congr_left
  intro k _
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases tele[k]? with
  | none => simp only [Option.map_none, Option.getD_none]; rw [← structIdxAt_map]; rfl
  | some b => simp only [Option.map_some, Option.getD_some, structIdxAt_map]

theorem structTeleAt_good {tele : List (Expr md × BinderMeta)} (h : Expr.BindersGood P tele)
    (nF o i l : Nat) (pw : PropWhen) : Expr.BindersGood P (structTeleAt nF o i l pw tele) := by
  intro x hx
  simp only [structTeleAt, List.mem_map] at hx
  obtain ⟨k, _, rfl⟩ := hx
  exact structIdxAt_good (h.getD k) _ _ _ _ _

@[simp] theorem structTeleVars_map (m : Nat) :
    (structTeleVars m : List (Expr md)).map (Expr.mapKeys f) = structTeleVars m :=
  map_mapKeys_bvars _ _

theorem structTeleVars_good (m : Nat) : Expr.GoodList P (structTeleVars m : List (Expr md)) :=
  goodList_bvars _ _

@[simp] theorem structRecPrefixAt_map (nP n nF e : Nat) :
    (structRecPrefixAt nP n nF e : List (Expr md)).map (Expr.mapKeys f) =
      structRecPrefixAt nP n nF e := by
  simp [structRecPrefixAt, List.map_append, map_mapKeys_bvars, Expr.mapKeys, Function.comp_def]

theorem structRecPrefixAt_good (nP n nF e : Nat) :
    Expr.GoodList P (structRecPrefixAt nP n nF e : List (Expr md)) := by
  intro x hx
  simp only [structRecPrefixAt, structPsAt, List.mem_append, List.mem_map, List.mem_singleton]
    at hx
  rcases hx with (⟨_, _, rfl⟩ | rfl) | ⟨_, _, rfl⟩ <;> trivial

theorem structFieldTeleOf_map (cty : Expr md) (nP nF i : Nat) :
    structFieldTeleOf (cty.mapKeys f) nP nF i = Expr.mapBinders f (structFieldTeleOf cty nP nF i) := by
  unfold structFieldTeleOf
  rw [Expr.stripPis_mapKeys]
  cases Expr.stripPis (nP + nF) cty with
  | none => rfl
  | some r =>
    simp only [Option.map_some, Expr.mapTele, Expr.mapBinders_getD, Expr.piBinders_mapKeys]

theorem structFieldTeleOf_good {cty : Expr md} (hc : cty.Good P) (nP nF i : Nat) :
    Expr.BindersGood P (structFieldTeleOf cty nP nF i) := by
  unfold structFieldTeleOf
  cases h : Expr.stripPis (nP + nF) cty with
  | none => exact fun _ h => nomatch h
  | some r =>
    obtain ⟨hbs, _⟩ := Expr.stripPis_good hc h
    exact (Expr.piBinders_good (hbs.getD (nP + i))).1

theorem structFieldIdxOf_map (cty : Expr md) (nP nF i : Nat) :
    structFieldIdxOf (cty.mapKeys f) nP nF i = (structFieldIdxOf cty nP nF i).map (Expr.mapKeys f) := by
  unfold structFieldIdxOf
  rw [Expr.stripPis_mapKeys]
  cases Expr.stripPis (nP + nF) cty with
  | none => rfl
  | some r =>
    simp only [Option.map_some, Expr.mapTele, Expr.mapBinders_getD, Expr.piBinders_mapKeys,
      Expr.getAppArgs_mapKeys, List.map_drop]

theorem structFieldIdxOf_good {cty : Expr md} (hc : cty.Good P) (nP nF i : Nat) :
    Expr.GoodList P (structFieldIdxOf cty nP nF i) := by
  unfold structFieldIdxOf
  cases h : Expr.stripPis (nP + nF) cty with
  | none => exact fun _ h => nomatch h
  | some r =>
    obtain ⟨hbs, _⟩ := Expr.stripPis_good hc h
    intro x hx
    exact (Expr.piBinders_good (hbs.getD (nP + i))).2.getAppArgs x (List.mem_of_mem_drop hx)

/-! ## The minor premises and the rules -/

theorem structIhApp_map (recC : Key md) (rlvls : List Level) (pw : PropWhen) (nP n nF i : Nat)
    (tele : List (Expr md × BinderMeta)) (idx : List (Expr md)) :
    structIhApp (recC.map f) rlvls pw nP n nF i (Expr.mapBinders f tele) (idx.map (Expr.mapKeys f)) =
      (structIhApp recC rlvls pw nP n nF i tele idx).mapKeys f := by
  simp only [structIhApp, Expr.mapBinders_length, structTeleAt_map, ← Expr.mkLamsOf_mapKeys,
    Expr.mapKeys_mkAppN, List.map_append, structRecPrefixAt_map, List.map_map,
    Function.comp_def, structIdxAt_map, List.map_cons, List.map_nil, structTeleVars_map]
  rfl

theorem structIhApp_good {recC : Key md} (hr : recC.Good P) {tele : List (Expr md × BinderMeta)}
    (ht : Expr.BindersGood P tele) {idx : List (Expr md)} (hi : Expr.GoodList P idx)
    (rlvls : List Level) (pw : PropWhen) (nP n nF i : Nat) :
    (structIhApp recC rlvls pw nP n nF i tele idx).Good P := by
  refine Expr.mkLamsOf_good (structTeleAt_good ht _ _ _ _ _) (Expr.Good.mkAppN hr ?_)
  intro x hx
  simp only [List.mem_append, List.mem_map, List.mem_singleton] at hx
  rcases hx with (hx | ⟨y, hy, rfl⟩) | rfl
  · exact structRecPrefixAt_good _ _ _ _ x hx
  · exact structIdxAt_good (hi y hy) _ _ _ _ _
  · exact Expr.Good.mkAppN trivial (structTeleVars_good _)

theorem structRuleBodyR_map (recC : Key md) (rlvls : List Level) (pw : PropWhen)
    (nP n nF j : Nat) (recIdx : List Nat) (teleOf : Nat → List (Expr md × BinderMeta))
    (idxOf : Nat → List (Expr md)) :
    structRuleBodyR (recC.map f) rlvls pw nP n nF j recIdx (fun i => Expr.mapBinders f (teleOf i))
        (fun i => (idxOf i).map (Expr.mapKeys f)) =
      (structRuleBodyR recC rlvls pw nP n nF j recIdx teleOf idxOf).mapKeys f := by
  simp only [structRuleBodyR, Expr.mapKeys_mkAppN, List.map_append, List.map_map,
    Function.comp_def, structIhApp_map, map_mapKeys_bvars, Expr.mapKeys]

theorem structRuleBodyR_good {recC : Key md} (hr : recC.Good P)
    {teleOf : Nat → List (Expr md × BinderMeta)} (ht : ∀ i, Expr.BindersGood P (teleOf i))
    {idxOf : Nat → List (Expr md)} (hi : ∀ i, Expr.GoodList P (idxOf i)) (rlvls : List Level)
    (pw : PropWhen) (nP n nF j : Nat) (recIdx : List Nat) :
    (structRuleBodyR recC rlvls pw nP n nF j recIdx teleOf idxOf).Good P := by
  refine Expr.Good.mkAppN trivial ?_
  intro x hx
  simp only [List.mem_append, List.mem_map] at hx
  rcases hx with ⟨_, _, rfl⟩ | ⟨i, _, rfl⟩
  · trivial
  · exact structIhApp_good hr (ht i) (hi i) _ _ _ _ _ _

theorem structIhPis_map (nF o : Nat) (pw : PropWhen) (teleOf : Nat → List (Expr md × BinderMeta))
    (idxOf : Nat → List (Expr md)) :
    ∀ (is : List Nat) (l : Nat) (body : Expr md),
      structIhPis nF o pw (fun i => Expr.mapBinders f (teleOf i))
          (fun i => (idxOf i).map (Expr.mapKeys f)) is l (body.mapKeys f) =
        (structIhPis nF o pw teleOf idxOf is l body).mapKeys f
  | [], _, _ => rfl
  | i :: is, l, body => by
    simp only [structIhPis, Expr.mapBinders_length, structTeleAt_map, structIhPis_map nF o pw
      teleOf idxOf is (l + 1) body, Expr.mapKeys]
    congr 1
    rw [← Expr.mkPisOf_mapKeys]
    simp only [Expr.mapKeys_mkAppN, List.map_append, List.map_map, Function.comp_def,
      structIdxAt_map, List.map_cons, List.map_nil, structTeleVars_map, Expr.mapKeys]

theorem structIhPis_good {teleOf : Nat → List (Expr md × BinderMeta)}
    (ht : ∀ i, Expr.BindersGood P (teleOf i)) {idxOf : Nat → List (Expr md)}
    (hi : ∀ i, Expr.GoodList P (idxOf i)) (nF o : Nat) (pw : PropWhen) :
    ∀ (is : List Nat) (l : Nat) {body : Expr md}, body.Good P →
      (structIhPis nF o pw teleOf idxOf is l body).Good P
  | [], _, _, hb => hb
  | i :: is, l, body, hb => by
    simp only [structIhPis, Expr.Good]
    refine ⟨Expr.mkPisOf_good (structTeleAt_good (ht i) _ _ _ _ _) (Expr.Good.mkAppN trivial ?_),
      structIhPis_good ht hi nF o pw is (l + 1) hb⟩
    intro x hx
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hx
    rcases hx with ⟨y, hy, rfl⟩ | rfl
    · exact structIdxAt_good (hi i y hy) _ _ _ _ _
    · exact Expr.Good.mkAppN trivial (structTeleVars_good _)

theorem structFieldTeleOf_map' (cty : Expr md) (nP nF : Nat) :
    structFieldTeleOf (cty.mapKeys f) nP nF = fun i => Expr.mapBinders f (structFieldTeleOf cty nP nF i) :=
  funext (structFieldTeleOf_map cty nP nF)

theorem structFieldIdxOf_map' (cty : Expr md) (nP nF : Nat) :
    structFieldIdxOf (cty.mapKeys f) nP nF = fun i => (structFieldIdxOf cty nP nF i).map (Expr.mapKeys f) :=
  funext (structFieldIdxOf_map cty nP nF)

theorem structMinorTyR_map (C : Key md) (lps : List LevelParam) (nP nF o : Nat) (pw : PropWhen)
    (cty : Expr md) (recIdx : List Nat) :
    structMinorTyR (C.map f) lps nP nF o pw (cty.mapKeys f) recIdx =
      (structMinorTyR C lps nP nF o pw cty recIdx).map (Expr.mapKeys f) := by
  unfold structMinorTyR
  rw [Expr.stripPis_mapKeys]
  cases Expr.stripPis nP cty with
  | none => rfl
  | some q =>
    obtain ⟨qbs, qb⟩ := q
    simp only [Option.map_some, Option.bind_some, Expr.mapTele]
    rw [Expr.stripPis_mapKeys]
    cases Expr.stripPis nF qb with
    | none => rfl
    | some r =>
      obtain ⟨rbs, rb⟩ := r
      simp only [Option.map_some, Option.bind_some, Expr.mapTele]
      rw [structFieldTeleOf_map', structFieldIdxOf_map', ← Expr.mapKeys_liftLooseBVars,
        Expr.getAppArgs_mapKeys, ← List.map_drop, List.map_map]
      have h1 : List.map (Expr.liftLooseBVars o nF ∘ Expr.mapKeys f) (List.drop nP rb.getAppArgs) =
          (List.map (Expr.liftLooseBVars o nF) (List.drop nP rb.getAppArgs)).map (Expr.mapKeys f) := by
        simp [List.map_map, Function.comp_def]
      rw [h1, structCtorSpineAt_map]
      have h2 : ((List.map (Expr.liftLooseBVars o nF) (List.drop nP rb.getAppArgs)).map
            (Expr.mapKeys f) ++ [(structCtorSpineAt C lps o nP nF).mapKeys f]) =
          (List.map (Expr.liftLooseBVars o nF) (List.drop nP rb.getAppArgs) ++
            [structCtorSpineAt C lps o nP nF]).map (Expr.mapKeys f) := by
        simp
      rw [h2, show (Expr.bvar (nF + o - 1) : Expr md') = (Expr.bvar (nF + o - 1) : Expr md).mapKeys f
        from rfl, ← Expr.mapKeys_mkAppN, ← Expr.mapKeys_liftLooseBVars, structIhPis_map,
        replacePisPw_mapKeys]

theorem structMinorTyR_good {C : Key md} (hC : C.Good P) {cty : Expr md} (hc : cty.Good P)
    {lps : List LevelParam} {nP nF o : Nat} {pw : PropWhen} {recIdx : List Nat} {r : Expr md}
    (h : structMinorTyR C lps nP nF o pw cty recIdx = some r) : r.Good P := by
  unfold structMinorTyR at h
  cases h₁ : Expr.stripPis nP cty with
  | none => rw [h₁] at h; exact nomatch h
  | some q =>
    rw [h₁] at h
    obtain ⟨_, hq⟩ := Expr.stripPis_good hc h₁
    simp only [Option.bind_some] at h
    cases h₂ : Expr.stripPis nF q.2 with
    | none => rw [h₂] at h; exact nomatch h
    | some s =>
      rw [h₂] at h
      obtain ⟨_, hs⟩ := Expr.stripPis_good hq h₂
      simp only [Option.bind_some] at h
      refine replacePisPw_good _ (hq.liftLooseBVars _ _) ?_ h
      refine structIhPis_good (structFieldTeleOf_good hc nP nF) (structFieldIdxOf_good hc nP nF)
        _ _ _ _ _ (Expr.Good.liftLooseBVars (Expr.Good.mkAppN (g := Expr.bvar (nF + o - 1)) trivial ?_) _ _)
      intro x hx
      simp only [List.mem_append, List.mem_map, List.mem_singleton] at hx
      rcases hx with ⟨y, hy, rfl⟩ | rfl
      · exact (hs.getAppArgs y (List.mem_of_mem_drop hy)).liftLooseBVars _ _
      · exact structCtorSpineAt_good hC _ _ _ _

/-- Rename a constructor's recursor data (name, field count, type, recursive fields). -/
def ctors4Map (f : md.Id → md'.Id) (cs : List (Key md × Nat × Expr md × List Nat)) :
    List (Key md' × Nat × Expr md' × List Nat) :=
  cs.map fun c => (c.1.map f, c.2.1, c.2.2.1.mapKeys f, c.2.2.2)

def ctors4Good (P : KeyScope md) (cs : List (Key md × Nat × Expr md × List Nat)) : Prop :=
  ∀ c ∈ cs, c.1.Good P ∧ c.2.2.1.Good P

theorem structMinorsPisR_map (lps : List LevelParam) (nP : Nat) (pw : PropWhen) :
    ∀ (cs : List (Key md × Nat × Expr md × List Nat)) (o : Nat) (body : Expr md),
      structMinorsPisR lps nP pw (ctors4Map f cs) o (body.mapKeys f) =
        (structMinorsPisR lps nP pw cs o body).map (Expr.mapKeys f)
  | [], _, _ => rfl
  | (C, nF, cty, recIdx) :: cs, o, body => by
    simp only [ctors4Map, List.map_cons, structMinorsPisR]
    rw [structMinorTyR_map]
    cases structMinorTyR C lps nP nF o pw cty recIdx with
    | none => rfl
    | some mty =>
      simp only [Option.map_some, Option.bind_some]
      have := structMinorsPisR_map lps nP pw cs (o + 1) body
      simp only [ctors4Map] at this
      rw [this]
      cases structMinorsPisR lps nP pw cs (o + 1) body <;> rfl

theorem structMinorsLamsR_map (lps : List LevelParam) (nP : Nat) (pw : PropWhen) :
    ∀ (cs : List (Key md × Nat × Expr md × List Nat)) (o : Nat) (body : Expr md),
      structMinorsLamsR lps nP pw (ctors4Map f cs) o (body.mapKeys f) =
        (structMinorsLamsR lps nP pw cs o body).map (Expr.mapKeys f)
  | [], _, _ => rfl
  | (C, nF, cty, recIdx) :: cs, o, body => by
    simp only [ctors4Map, List.map_cons, structMinorsLamsR]
    rw [structMinorTyR_map]
    cases structMinorTyR C lps nP nF o pw cty recIdx with
    | none => rfl
    | some mty =>
      simp only [Option.map_some, Option.bind_some]
      have := structMinorsLamsR_map lps nP pw cs (o + 1) body
      simp only [ctors4Map] at this
      rw [this]
      cases structMinorsLamsR lps nP pw cs (o + 1) body <;> rfl

theorem structMinorsPisR_good {lps : List LevelParam} {nP : Nat} {pw : PropWhen} :
    ∀ {cs : List (Key md × Nat × Expr md × List Nat)} {o : Nat} {body r : Expr md},
      ctors4Good P cs → body.Good P → structMinorsPisR lps nP pw cs o body = some r → r.Good P
  | [], _, _, _, _, hb, h => by simp only [structMinorsPisR, Option.some.injEq] at h; exact h ▸ hb
  | (C, nF, cty, recIdx) :: cs, o, body, r, hcs, hb, h => by
    simp only [structMinorsPisR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨mty, hm, rest, hr, rfl⟩ := h
    have hc := hcs _ (List.mem_cons_self ..)
    exact ⟨structMinorTyR_good hc.1 hc.2 hm,
      structMinorsPisR_good (fun x hx => hcs x (List.mem_cons_of_mem _ hx)) hb hr⟩

theorem structMinorsLamsR_good {lps : List LevelParam} {nP : Nat} {pw : PropWhen} :
    ∀ {cs : List (Key md × Nat × Expr md × List Nat)} {o : Nat} {body r : Expr md},
      ctors4Good P cs → body.Good P → structMinorsLamsR lps nP pw cs o body = some r → r.Good P
  | [], _, _, _, _, hb, h => by simp only [structMinorsLamsR, Option.some.injEq] at h; exact h ▸ hb
  | (C, nF, cty, recIdx) :: cs, o, body, r, hcs, hb, h => by
    simp only [structMinorsLamsR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨mty, hm, rest, hr, rfl⟩ := h
    have hc := hcs _ (List.mem_cons_self ..)
    exact ⟨structMinorTyR_good hc.1 hc.2 hm,
      structMinorsLamsR_good (fun x hx => hcs x (List.mem_cons_of_mem _ hx)) hb hr⟩

@[simp] theorem ctors4Map_length (cs : List (Key md × Nat × Expr md × List Nat)) :
    (ctors4Map f cs).length = cs.length := by
  simp [ctors4Map]

theorem structRecTyR_map (T : Key md) (lps : List LevelParam) (elim : LevelParam) (large : Bool)
    (nP nIdx : Nat) (tty : Expr md) (ctors : List (Key md × Nat × Expr md × List Nat)) :
    structRecTyR (T.map f) lps elim large nP nIdx (tty.mapKeys f) (ctors4Map f ctors) =
      (structRecTyR T lps elim large nP nIdx tty ctors).map (Expr.mapKeys f) := by
  unfold structRecTyR
  simp only [ctors4Map_length]
  rw [Expr.stripPis_mapKeys]
  cases Expr.stripPis nP tty with
  | none => rfl
  | some q =>
    obtain ⟨qbs, qb⟩ := q
    simp only [Option.map_some, Option.bind_some, Expr.mapTele]
    rw [structMotiveTyI_map]
    cases structMotiveTyI T lps nP nIdx (structElimLevel elim large) qb with
    | none => rfl
    | some mt =>
      simp only [Option.map_some, Option.bind_some]
      have hmaj : (Expr.forallE (structFamI (T.map f) lps nP nIdx (ctors.length + 1) 0)
            (Expr.mkAppN (Expr.bvar (nIdx + ctors.length + 1)) (structPsAt 1 nIdx ++ [Expr.bvar 0]))
            { pw := (structElimLevel elim large).zeronessOf } : Expr md') =
          (Expr.forallE (structFamI T lps nP nIdx (ctors.length + 1) 0)
            (Expr.mkAppN (Expr.bvar (nIdx + ctors.length + 1)) (structPsAt 1 nIdx ++ [Expr.bvar 0]))
            { pw := (structElimLevel elim large).zeronessOf } : Expr md).mapKeys f := by
        simp [Expr.mapKeys, structFamI_map, Expr.mapKeys_mkAppN, List.map_append]
      rw [hmaj, ← Expr.mapKeys_liftLooseBVars, replacePisPw_mapKeys]
      cases Expr.replacePisPw (structElimLevel elim large).zeronessOf nIdx
        (qb.liftLooseBVars (ctors.length + 1) 0) _ with
      | none => rfl
      | some major =>
        simp only [Option.map_some, Option.bind_some]
        rw [structMinorsPisR_map]
        cases structMinorsPisR lps nP (structElimLevel elim large).zeronessOf ctors 1 major with
        | none => rfl
        | some minors =>
          simp only [Option.map_some, Option.bind_some]
          rw [show (Expr.forallE (mt.mapKeys f) (minors.mapKeys f)
              { pw := (structElimLevel elim large).zeronessOf } : Expr md') =
              (Expr.forallE mt minors { pw := (structElimLevel elim large).zeronessOf }).mapKeys f
            from rfl, replacePisPw_mapKeys]

theorem structRecTyR_good {T : Key md} (hT : T.Good P) {lps : List LevelParam} {elim : LevelParam}
    {large : Bool} {nP nIdx : Nat} {tty : Expr md} (ht : tty.Good P)
    {ctors : List (Key md × Nat × Expr md × List Nat)} (hcs : ctors4Good P ctors) {r : Expr md}
    (h : structRecTyR T lps elim large nP nIdx tty ctors = some r) : r.Good P := by
  unfold structRecTyR at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨q, hq, mt, hmt, major, hmaj, minors, hmin, hr⟩ := h
  obtain ⟨_, hq2⟩ := Expr.stripPis_good ht hq
  have hmtg := structMotiveTyI_good hT hq2 hmt
  have hmajg : major.Good P := by
    refine replacePisPw_good _ (hq2.liftLooseBVars _ _) ?_ hmaj
    simp only [Expr.Good]
    refine ⟨structFamI_good hT _ _ _ _ _, Expr.Good.mkAppN trivial ?_⟩
    intro x hx
    simp only [structPsAt, List.mem_append, List.mem_map, List.mem_singleton] at hx
    rcases hx with ⟨_, _, rfl⟩ | rfl <;> trivial
  have hming := structMinorsPisR_good hcs hmajg hmin
  exact replacePisPw_good _ ht (show Expr.Good P (Expr.forallE _ _ _) from ⟨hmtg, hming⟩) hr

theorem structRecRhsR_map (T : Key md) (lps : List LevelParam) (elim : LevelParam) (large : Bool)
    (nP nIdx : Nat) (tty : Expr md) (ctors : List (Key md × Nat × Expr md × List Nat))
    (recC : Key md) (rlvls : List Level) (j : Nat) :
    structRecRhsR (T.map f) lps elim large nP nIdx (tty.mapKeys f) (ctors4Map f ctors) (recC.map f)
        rlvls j =
      (structRecRhsR T lps elim large nP nIdx tty ctors recC rlvls j).map (Expr.mapKeys f) := by
  unfold structRecRhsR
  simp only [ctors4Map_length]
  rw [show (ctors4Map f ctors)[j]? = (ctors[j]?).map
      (fun c => (c.1.map f, c.2.1, c.2.2.1.mapKeys f, c.2.2.2)) from List.getElem?_map ..]
  cases ctors[j]? with
  | none => rfl
  | some c =>
    obtain ⟨C, nF, cty, recIdx⟩ := c
    simp only [Option.map_some]
    rw [Expr.stripPis_mapKeys]
    cases Expr.stripPis nP tty with
    | none => rfl
    | some tq =>
      obtain ⟨tbs, tb⟩ := tq
      simp only [Option.map_some, Option.bind_some, Expr.mapTele]
      rw [structMotiveTyI_map]
      cases structMotiveTyI T lps nP nIdx (structElimLevel elim large) tb with
      | none => rfl
      | some mt =>
        simp only [Option.map_some, Option.bind_some]
        rw [Expr.stripPis_mapKeys]
        cases Expr.stripPis nP cty with
        | none => rfl
        | some q =>
          obtain ⟨qbs, qb⟩ := q
          simp only [Option.map_some, Option.bind_some, Expr.mapTele]
          rw [structFieldTeleOf_map', structFieldIdxOf_map', structRuleBodyR_map,
            ← Expr.mapKeys_liftLooseBVars, pisToLamsPw_mapKeys]
          cases Expr.pisToLamsPw (structElimLevel elim large).zeronessOf nF
            (qb.liftLooseBVars (ctors.length + 1) 0) _ with
          | none => rfl
          | some inner =>
            simp only [Option.map_some, Option.bind_some]
            rw [structMinorsLamsR_map]
            cases structMinorsLamsR lps nP (structElimLevel elim large).zeronessOf ctors 1 inner with
            | none => rfl
            | some minors =>
              simp only [Option.map_some, Option.bind_some]
              rw [show (Expr.lam (mt.mapKeys f) (minors.mapKeys f)
                  { pw := (structElimLevel elim large).zeronessOf } : Expr md') =
                  (Expr.lam mt minors { pw := (structElimLevel elim large).zeronessOf }).mapKeys f
                from rfl, pisToLamsPw_mapKeys]

theorem structRecRhsR_good {T : Key md} (hT : T.Good P) {lps : List LevelParam}
    {elim : LevelParam} {large : Bool} {nP nIdx : Nat} {tty : Expr md} (ht : tty.Good P)
    {ctors : List (Key md × Nat × Expr md × List Nat)} (hcs : ctors4Good P ctors)
    {recC : Key md} (hr : recC.Good P) {rlvls : List Level} {j : Nat} {r : Expr md}
    (h : structRecRhsR T lps elim large nP nIdx tty ctors recC rlvls j = some r) : r.Good P := by
  unfold structRecRhsR at h
  cases hj : ctors[j]? with
  | none => rw [hj] at h; exact nomatch h
  | some c =>
    rw [hj] at h
    obtain ⟨C, nF, cty, recIdx⟩ := c
    have hc := hcs _ (List.mem_of_getElem? hj)
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨tq, htq, mt, hmt, q, hq, inner, hin, minors, hmin, hr'⟩ := h
    obtain ⟨_, htq2⟩ := Expr.stripPis_good ht htq
    obtain ⟨_, hq2⟩ := Expr.stripPis_good hc.2 hq
    have hmtg := structMotiveTyI_good hT htq2 hmt
    have hing : inner.Good P :=
      pisToLamsPw_good _ (hq2.liftLooseBVars _ _)
        (structRuleBodyR_good hr (structFieldTeleOf_good hc.2 nP nF)
          (structFieldIdxOf_good hc.2 nP nF) _ _ _ _ _ _ _) hin
    have hming := structMinorsLamsR_good hcs hing hmin
    exact pisToLamsPw_good _ ht (show Expr.Good P (Expr.lam _ _ _) from ⟨hmtg, hming⟩) hr'

theorem nativeCtors4_map (ctorsA : List (ConstantVal md × Nat)) (kinds : List (List RecFieldKind)) :
    nativeCtors4 (ctorsA.map fun c => (c.1.mapKeys f, c.2)) kinds =
      ctors4Map f (nativeCtors4 ctorsA kinds) := by
  unfold nativeCtors4 ctors4Map
  rw [List.zipWith_map_left, List.map_zipWith]
  rfl

theorem nativeCtors4_good {ctorsA : List (ConstantVal md × Nat)} (h : ∀ c ∈ ctorsA, c.1.Good P)
    (kinds : List (List RecFieldKind)) : ctors4Good P (nativeCtors4 ctorsA kinds) := by
  unfold nativeCtors4
  induction ctorsA generalizing kinds with
  | nil => intro c hc; simp at hc
  | cons a as ih =>
    cases kinds with
    | nil => intro c hc; simp at hc
    | cons k ks =>
      intro c hc
      simp only [List.zipWith_cons_cons, List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact ⟨(h a (List.mem_cons_self ..)).1, (h a (List.mem_cons_self ..)).2⟩
      · exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) ks c hc

end Ix.Kernel
