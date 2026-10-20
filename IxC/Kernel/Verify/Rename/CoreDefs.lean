module

public import IxC.Kernel.Verify.Rename.Env

@[expose] public section

/-!
# Renaming and the core's fuel-free helpers

Each helper of `IxC/Kernel/CoreDefs.lean`, at renamed arguments and a related
environment, answers as at the originals, renamed where the answer is a
term: the delta step and its readers, the literal guards and shapes, the
certified `Nat` operations' data and guards, the structure-η fabrications
and the install-time rule bits.
-/

set_option linter.unusedSimpArgs false

set_option linter.unusedSectionVars false

namespace Ix.Kernel

variable {md md' : Mode} {f : md.Id → md'.Id} {P : md.Id → Prop}
variable {L : Env md → Env md' → Prop} [LinkPush P f L]

/-! ## Pinned shapes of a stored constant -/

theorem natIndOk_map (o : Option (ConstantInfo md)) :
    natIndOk (o.map (ConstantInfo.mapKeys f)) = natIndOk o := by
  rcases o with _ | ⟨_ | _ | _ | ⟨cv, caps⟩ | _ | _ | _⟩ <;> try rfl
  simp only [Option.map_some, ConstantInfo.mapKeys, natIndOk, ConstantVal.mapKeys_levelParams,
    ConstantVal.mapKeys_type]
  congr 1
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  exact Expr.mapKeys_eq_sort_iff

theorem natZeroOk_map (o : Option (ConstantInfo md)) :
    natZeroOk (o.map (ConstantInfo.mapKeys f)) = natZeroOk o := by
  rcases o with _ | ⟨_ | _ | _ | _ | ⟨cv, nP, nF⟩ | _ | _⟩ <;> try rfl
  simp only [Option.map_some, ConstantInfo.mapKeys, natZeroOk, ConstantVal.mapKeys_levelParams,
    ConstantVal.mapKeys_type]
  congr 1
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  simp

theorem natSuccOk_map (o : Option (ConstantInfo md)) :
    natSuccOk (o.map (ConstantInfo.mapKeys f)) = natSuccOk o := by
  rcases o with _ | ⟨_ | _ | _ | _ | ⟨⟨n, lps, t⟩, nP, nF⟩ | _ | _⟩ <;> try rfl
  simp only [Option.map_some, ConstantInfo.mapKeys, natSuccOk, ConstantVal.mapKeys,
    ConstantVal.mapKeys_levelParams, ConstantVal.mapKeys_type]
  rcases t with _ | _ | _ | _ | _ | _ |
    ⟨_ | _ | _ | ⟨c1, _ | _⟩ | _ | _ | _ | _ | _ | _,
     _ | _ | _ | ⟨c2, _ | _⟩ | _ | _ | _ | _ | _ | _, mb⟩ | _ | _ | _ <;>
    simp

theorem listConsTyOk_map (o : Option (ConstantInfo md)) :
    listConsTyOk (o.map (ConstantInfo.mapKeys f)) = listConsTyOk o := by
  rcases o with _ | c
  · rfl
  simp only [Option.map_some, listConsTyOk, ConstantInfo.mapKeys_toConstantVal,
    ConstantVal.mapKeys_levelParams, ConstantVal.mapKeys_type]
  split
  · symm; shape_match
  · rfl

theorem listTyOk_map (o : Option (ConstantInfo md)) :
    listTyOk (o.map (ConstantInfo.mapKeys f)) = listTyOk o := by
  rcases o with _ | c
  · rfl
  simp only [Option.map_some, listTyOk, ConstantInfo.mapKeys_toConstantVal,
    ConstantVal.mapKeys_levelParams, ConstantVal.mapKeys_type]
  split
  · symm; shape_match
  · rfl

theorem listNilTyOk_map (o : Option (ConstantInfo md)) :
    listNilTyOk (o.map (ConstantInfo.mapKeys f)) = listNilTyOk o := by
  rcases o with _ | c
  · rfl
  simp only [Option.map_some, listNilTyOk, ConstantInfo.mapKeys_toConstantVal,
    ConstantVal.mapKeys_levelParams, ConstantVal.mapKeys_type]
  split
  · symm; shape_match
  · rfl

theorem stringTyOk_map (o : Option (ConstantInfo md)) :
    stringTyOk (o.map (ConstantInfo.mapKeys f)) = stringTyOk o := by
  rcases o with _ | c
  · rfl
  simp only [Option.map_some, stringTyOk, ConstantInfo.mapKeys_toConstantVal,
    ConstantVal.mapKeys_levelParams, ConstantVal.mapKeys_type]
  congr 1
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  exact Expr.mapKeys_eq_sort_iff

theorem charTyOk_map (o : Option (ConstantInfo md)) :
    charTyOk (o.map (ConstantInfo.mapKeys f)) = charTyOk o := by
  rcases o with _ | c
  · rfl
  simp only [Option.map_some, charTyOk, ConstantInfo.mapKeys_toConstantVal,
    ConstantVal.mapKeys_levelParams, ConstantVal.mapKeys_type]
  congr 1
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  exact Expr.mapKeys_eq_sort_iff

theorem charOfNatTyOk_map (o : Option (ConstantInfo md)) :
    charOfNatTyOk (o.map (ConstantInfo.mapKeys f)) = charOfNatTyOk o := by
  rcases o with _ | c
  · rfl
  simp only [Option.map_some, charOfNatTyOk, ConstantInfo.mapKeys_toConstantVal,
    ConstantVal.mapKeys_levelParams, ConstantVal.mapKeys_type]
  congr 1
  symm; shape_match

theorem stringOfListTyOk_map (o : Option (ConstantInfo md)) :
    stringOfListTyOk (o.map (ConstantInfo.mapKeys f)) = stringOfListTyOk o := by
  rcases o with _ | c
  · rfl
  simp only [Option.map_some, stringOfListTyOk, ConstantInfo.mapKeys_toConstantVal,
    ConstantVal.mapKeys_levelParams, ConstantVal.mapKeys_type]
  congr 1
  symm; shape_match

/-! ## Environment readers -/

variable {env : Env md} {env' : Env md'}

theorem natLitSupported_ren (hE : EnvRelG P f L env env') :
    natLitSupported env' = natLitSupported env := by
  simp only [natLitSupported, hE.find_role, natIndOk_map, natZeroOk_map, natSuccOk_map]

theorem strLitSupported_ren (hE : EnvRelG P f L env env') :
    strLitSupported env' = strLitSupported env := by
  simp only [strLitSupported, natLitSupported_ren hE, hE.find_role, stringTyOk_map,
    stringOfListTyOk_map, listTyOk_map, listNilTyOk_map, listConsTyOk_map, charTyOk_map,
    charOfNatTyOk_map]

theorem isCtorApp_ren (hE : EnvRelG P f L env env') {e : Expr md} (he : e.Good P) :
    isCtorApp env' (e.mapKeys f) = isCtorApp env e := by
  unfold isCtorApp
  rw [← Expr.mapKeys_getAppFn]
  have hg := Expr.Good.getAppFn he
  generalize e.getAppFn = g at hg ⊢
  cases g with
  | const c us =>
    simp only [Expr.mapKeys]
    rw [hE.find c hg]
    cases env.find? c with
    | none => rfl
    | some ci => cases ci <;> rfl
  | _ => rfl

theorem unfoldDefinition_ren (hE : EnvRelG P f L env env') {e : Expr md} (he : e.Good P) :
    unfoldDefinition env' (e.mapKeys f) = (unfoldDefinition env e).map (Expr.mapKeys f) := by
  unfold unfoldDefinition
  rw [← Expr.mapKeys_getAppFn, Expr.getAppArgs_mapKeys]
  have hg := Expr.Good.getAppFn he
  generalize e.getAppFn = g at hg ⊢
  cases g with
  | const c us =>
    simp only [Expr.mapKeys]
    rw [hE.find c hg]
    cases env.find? c with
    | none => rfl
    | some ci =>
      cases ci with
      | defnInfo cv v h =>
        simp only [Option.map_some, ConstantInfo.mapKeys, ConstantVal.mapKeys_levelParams]
        by_cases hl : us.length = cv.levelParams.length <;> simp [hl]
      | _ => rfl
  | _ => rfl

theorem unfoldDefinition_good (hE : EnvRelG P f L env env') {e : Expr md} (he : e.Good P)
    {e' : Expr md} (h : unfoldDefinition env e = some e') : e'.Good P := by
  unfold unfoldDefinition at h
  have hg := Expr.Good.getAppFn he
  have ha := Expr.Good.getAppArgs he
  generalize e.getAppFn = g at hg h
  cases g with
  | const c us =>
    cases hc : env.find? c with
    | none => simp [hc] at h
    | some ci =>
      have hci := hE.good c ci hg hc
      cases ci with
      | defnInfo cv v hint =>
        simp only [hc] at h
        split at h
        · cases h
          exact Expr.Good.mkAppN (Expr.Good.instantiateLevelParams hci.2 _ _) ha
        · exact nomatch h
      | _ => simp [hc] at h
  | _ => exact nomatch h

theorem unfoldableHead_ren (hE : EnvRelG P f L env env') {e : Expr md} (he : e.Good P) :
    unfoldableHead env' (e.mapKeys f) = unfoldableHead env e := by
  unfold unfoldableHead
  rw [← Expr.mapKeys_getAppFn]
  have hg := Expr.Good.getAppFn he
  generalize e.getAppFn = g at hg ⊢
  cases g with
  | const c us =>
    simp only [Expr.mapKeys]
    rw [hE.find c hg]
    cases env.find? c with
    | none => rfl
    | some ci => cases ci <;> rfl
  | _ => rfl

theorem headHint_ren (hE : EnvRelG P f L env env') {e : Expr md} (he : e.Good P) :
    headHint env' (e.mapKeys f) = headHint env e := by
  unfold headHint
  rw [← Expr.mapKeys_getAppFn]
  have hg := Expr.Good.getAppFn he
  generalize e.getAppFn = g at hg ⊢
  cases g with
  | const c us =>
    simp only [Expr.mapKeys]
    rw [hE.find c hg]
    cases env.find? c with
    | none => rfl
    | some ci => cases ci <;> rfl
  | _ => rfl

theorem sameConstHeads_ren (hf : InjOn f P) {a b : Expr md} (ha : a.Good P) (hb : b.Good P) :
    sameConstHeads (a.mapKeys f) (b.mapKeys f) = sameConstHeads a b := by
  cases a <;> cases b <;> try rfl
  rename_i f₁ x₁ f₂ x₂
  simp only [Expr.mapKeys, sameConstHeads, ← Expr.mapKeys_getAppFn]
  have h₁ := Expr.Good.getAppFn ha.1
  have h₂ := Expr.Good.getAppFn hb.1
  generalize f₁.getAppFn = g₁ at h₁ ⊢
  generalize f₂.getAppFn = g₂ at h₂ ⊢
  cases g₁ <;> cases g₂ <;> try rfl
  exact Key.map_beq hf h₁ h₂

@[simp] theorem natLitToConstructor_mapKeys (n : Nat) :
    (natLitToConstructor n : Expr md).mapKeys f = natLitToConstructor n := by
  cases n <;> rfl

theorem constsResolve_ren (hE : EnvRelG P f L env env') {e : Expr md} (he : e.Good P) :
    (e.mapKeys f).constsResolve env' = e.constsResolve env := by
  induction e with
  | lit l =>
    cases l <;> simp only [Expr.mapKeys, Expr.constsResolve, hE.find_role] <;>
      simp only [Option.isSome_map]
  | const n us =>
    simp only [Expr.mapKeys, Expr.constsResolve]
    exact hE.find_isSome he
  | proj s i x ih =>
    simp only [Expr.mapKeys, Expr.constsResolve]
    rw [hE.find_isSome he.1, ih he.2]
  | _ => simp_all [Expr.constsResolve]

theorem litToCtorIfNat_ren (hE : EnvRelG P f L env env') (e : Expr md) :
    litToCtorIfNat env' (e.mapKeys f) = (litToCtorIfNat env e).mapKeys f := by
  rcases e with _ | _ | _ | _ | _ | _ | _ | _ | ⟨_ | _⟩ | _ <;>
    simp [litToCtorIfNat, natLitSupported_ren hE] <;> split <;> simp

@[simp] theorem rawNatLit?_mapKeys (e : Expr md) : rawNatLit? (e.mapKeys f) = rawNatLit? e := by
  rcases e with _ | _ | _ | ⟨c, _ | _⟩ | _ | _ | _ | _ | ⟨_ | _⟩ | _ <;> simp [rawNatLit?]

@[simp] theorem strLitToConstructor_mapKeys (s : String) :
    (strLitToConstructor s : Expr md).mapKeys f = strLitToConstructor s := by
  unfold strLitToConstructor
  simp only [Expr.mapKeys, Key.map_role]
  congr 1
  generalize s.toList = cs
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [List.foldr_cons, Expr.mapKeys, Key.map_role, ih]

@[simp] theorem isBoolTrue_mapKeys (e : Expr md) : (e.mapKeys f).isBoolTrue = e.isBoolTrue := by
  rcases e with _ | _ | _ | ⟨c, _ | _⟩ | _ | _ | _ | _ | _ | _ <;> simp [Expr.isBoolTrue]

@[simp] theorem quickPair_mapKeys (a b : Expr md) :
    (a.mapKeys f).quickPair (b.mapKeys f) = a.quickPair b := by
  cases a <;> cases b <;> rfl

/-! ## The certified `Nat` operations -/

/-- `all` over a list depends on the predicate only at the members. -/
theorem _root_.List.all_congr_mem {α : Type} {l : List α} {p q : α → Bool}
    (h : ∀ a ∈ l, p a = q a) : l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.all_cons]
    rw [h a (List.mem_cons_self), ih (fun b hb => h b (List.mem_cons_of_mem a hb))]

/-- A renamed term compares with a role-headed constant as the term does. -/
@[simp] theorem Expr.mapKeys_beq_const_role {e : Expr md} {r : Role} {us : List Level} :
    (e.mapKeys f == Expr.const (.role r) us) = (e == Expr.const (.role r) us) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  simp

@[simp] theorem natOpNames_contains_map (k : Key md) :
    (natOpNames (md := md')).contains (k.map f) = (natOpNames (md := md)).contains k := by
  simp [natOpNames]

@[simp] theorem natDivModNames_contains_map (k : Key md) :
    (natDivModNames (md := md')).contains (k.map f) = (natDivModNames (md := md)).contains k := by
  simp [natDivModNames]

@[simp] theorem natOpWfNames_contains_map (k : Key md) :
    (natOpWfNames (md := md')).contains (k.map f) = (natOpWfNames (md := md)).contains k := by
  simp [natOpWfNames]

@[simp] theorem natOpDeps_map (k : Key md) :
    natOpDeps (k.map f) = (natOpDeps k).map (Key.map f) := by
  simp only [natOpDeps, Key.map_eq_role_iff, apply_ite (List.map (Key.map f)), List.map_cons,
    List.map_nil, Key.map_role]

/-- The dependencies of an operation are role keys, so good. -/
theorem natOpDeps_good (k : Key md) : ∀ n ∈ natOpDeps k, n.Good P := by
  intro n hn
  rcases k with i | r | ⟨b, d⟩
  · simp [natOpDeps] at hn
  · cases r <;> simp [natOpDeps] at hn <;> (repeat' (rcases hn with rfl | hn)) <;> trivial
  · simp [natOpDeps] at hn

@[simp] theorem natOpEquations_map (d : Nat) (k : Key md) :
    natOpEquations d (k.map f) =
      (natOpEquations d k).map fun p => (p.1.mapKeys f, p.2.mapKeys f) := by
  simp only [natOpEquations, Key.map_eq_role_iff, apply_ite (List.map _), List.map_cons,
    List.map_nil, Expr.mapKeys, Key.map_role]

@[simp] theorem natOpResult_map (k : Key md) (a b : Nat) :
    natOpResult (k.map f) a b = (natOpResult k a b).map (Expr.mapKeys f) := by
  simp only [natOpResult, Key.map_eq_role_iff, apply_ite (Option.map (Expr.mapKeys f)),
    Option.map_some, Option.map_none, Expr.mapKeys, apply_ite (Key.map f), Key.map_role]

theorem natOpGuard_ren (hE : EnvRelG P f L env env') (k : Key md) :
    natOpGuard env' (k.map f) = natOpGuard env k := by
  unfold natOpGuard
  rw [natLitSupported_ren hE, natOpDeps_map, List.all_map]
  congr 1
  · congr 1
    apply List.all_congr_mem
    intro n hn
    simp only [Function.comp_apply]
    rw [hE.find n (natOpDeps_good k n hn)]
    cases env.find? n with
    | none => rfl
    | some ci => cases ci <;> rfl
  · simp only [Key.map_eq_role_iff, natDivModNames_contains_map, hE.find_role]
    split
    · cases env.find? boolTrueName <;> cases env.find? boolFalseName <;> simp
    · rfl

@[simp] theorem natOpStored_ren (hE : EnvRelG P f L env env') {k : Key md} (hk : k.Good P) :
    natOpStored env' (k.map f) = natOpStored env k := by
  unfold natOpStored
  rw [hE.find k hk]
  cases env.find? k with
  | none => rfl
  | some ci => cases ci <;> rfl

theorem natOpCod_ren (hE : EnvRelG P f L env env') (k : Key md) (e : Expr md) :
    natOpCod env' (k.map f) (e.mapKeys f) = natOpCod env k e := by
  unfold natOpCod
  simp only [Key.map_eq_role_iff, hE.find_role, Expr.mapKeys_beq_const_role]
  split
  · congr 1
    cases env.find? boolName with
    | none => rfl
    | some ci =>
      simp only [Option.map_some, ConstantInfo.mapKeys_toConstantVal,
        ConstantVal.mapKeys_levelParams, ConstantVal.mapKeys_type]
      congr 1
      rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
      exact Expr.mapKeys_eq_sort_iff
  · rfl

theorem natOpTyPinned_ren (hE : EnvRelG P f L env env') (k : Key md) (ty : Expr md) :
    natOpTyPinned env' (k.map f) (ty.mapKeys f) = natOpTyPinned env k ty := by
  unfold natOpTyPinned
  simp only [Key.map_eq_role_iff]
  split
  · rcases ty with _ | _ | _ | _ | _ | _ | ⟨dom, body, mb⟩ | _ | _ | _ <;> try rfl
    simp only [Expr.mapKeys, Expr.mapKeys_beq_const_role, natOpCod_ren hE]
  · rcases ty with _ | _ | _ | _ | _ | _ |
      ⟨dom, _ | _ | _ | _ | _ | _ | ⟨dom2, body, mb2⟩ | _ | _ | _, mb⟩ | _ | _ | _ <;> try rfl
    simp only [Expr.mapKeys, Expr.mapKeys_beq_const_role, natOpCod_ren hE]

theorem natOpStoredOk_ren (hE : EnvRelG P f L env env') {k : Key md} (hk : k.Good P) :
    natOpStoredOk env' (k.map f) = natOpStoredOk env k := by
  unfold natOpStoredOk
  rw [hE.find k hk]
  cases env.find? k with
  | none => rfl
  | some ci =>
    cases ci with
    | defnInfo cv v h =>
      simp only [Option.map_some, ConstantInfo.mapKeys, ConstantVal.mapKeys_levelParams,
        ConstantVal.mapKeys_type, natOpTyPinned_ren hE]
    | _ => rfl

/-! ## Substituting a constant -/

theorem substConst0_ren (hf : InjOn f P) {n : Key md} (hn : n.Good P) (r : Expr md) {e : Expr md}
    (he : e.Good P) :
    Expr.substConst0 (n.map f) (r.mapKeys f) (e.mapKeys f) =
      (Expr.substConst0 n r e).mapKeys f := by
  induction e with
  | const c us =>
    simp only [Expr.mapKeys, Expr.substConst0, Key.map_eq_map_iff hf he hn]
    by_cases hc : c = n ∧ us = [] <;> simp [hc]
  | app a b iha ihb =>
    simp only [Expr.mapKeys, Expr.substConst0, iha he.1, ihb he.2]
  | _ => rfl

theorem substConst0_good {n : Key md} {r : Expr md} (hr : r.Good P) {e : Expr md}
    (he : e.Good P) : (Expr.substConst0 n r e).Good P := by
  induction e with
  | const c us => simp only [Expr.substConst0]; split <;> assumption
  | app a b iha ihb => exact ⟨iha he.1, ihb he.2⟩
  | _ => exact he

theorem substConstAll_ren (hf : InjOn f P) {n : Key md} (hn : n.Good P) (r : Expr md)
    {e : Expr md} (he : e.Good P) :
    Expr.substConstAll (n.map f) (r.mapKeys f) (e.mapKeys f) =
      (Expr.substConstAll n r e).mapKeys f := by
  induction e with
  | const c us =>
    simp only [Expr.mapKeys, Expr.substConstAll, Key.map_eq_map_iff hf he hn]
    by_cases hc : c = n ∧ us = [] <;> simp [hc]
  | app a b iha ihb => simp only [Expr.mapKeys, Expr.substConstAll, iha he.1, ihb he.2]
  | lam t b m iht ihb => simp only [Expr.mapKeys, Expr.substConstAll, iht he.1, ihb he.2]
  | forallE t b m iht ihb => simp only [Expr.mapKeys, Expr.substConstAll, iht he.1, ihb he.2]
  | letE t v b l iht ihv ihb =>
    simp only [Expr.mapKeys, Expr.substConstAll, iht he.1, ihv he.2.1, ihb he.2.2]
  | proj s i x ih => simp only [Expr.mapKeys, Expr.substConstAll, ih he.2]
  | _ => rfl

theorem substConstAll_good {n : Key md} {r : Expr md} (hr : r.Good P) {e : Expr md}
    (he : e.Good P) : (Expr.substConstAll n r e).Good P := by
  induction e with
  | const c us => simp only [Expr.substConstAll]; split <;> assumption
  | app a b iha ihb => exact ⟨iha he.1, ihb he.2⟩
  | lam t b m iht ihb => exact ⟨iht he.1, ihb he.2⟩
  | forallE t b m iht ihb => exact ⟨iht he.1, ihb he.2⟩
  | letE t v b l iht ihv ihb => exact ⟨iht he.1, ihv he.2.1, ihb he.2.2⟩
  | proj s i x ih => exact ⟨he.1, ih he.2⟩
  | _ => exact he

/-! ## Telescopes, projections, η -/

@[simp] theorem piResidual_mapKeys (e : Expr md) (as : List (Expr md)) :
    piResidual (e.mapKeys f) (as.map (Expr.mapKeys f)) = (piResidual e as).map (Expr.mapKeys f) := by
  induction as generalizing e with
  | nil => rfl
  | cons a as ih =>
    cases e with
    | forallE t b m =>
      simp only [Expr.mapKeys, List.map_cons, piResidual]
      rw [← Expr.mapKeys_instantiate1, ih]
    | _ => rfl

theorem piResidual_good {e : Expr md} {as : List (Expr md)} (he : e.Good P)
    (has : Expr.GoodList P as) {r : Expr md} (h : piResidual e as = some r) : r.Good P := by
  induction as generalizing e with
  | nil => cases h; exact he
  | cons a as ih =>
    simp only [Expr.goodList_cons] at has
    cases e with
    | forallE t b m => exact ih (Expr.Good.instantiate1 he.2 has.1 0) has.2 h
    | _ => exact nomatch h

theorem towerSlotsAll_ren (hE : EnvRelG P f L env env') {T : Key md} (hT : T.Good P) (nF : Nat) :
    towerSlotsAll env' (T.map f) nF = towerSlotsAll env T nF := by
  unfold towerSlotsAll
  congr 1
  funext j
  rw [hE.findProj? hT j]
  cases env.findProj? T j <;> rfl

theorem recSlotsAll_ren (hE : EnvRelG P f L env env') {T : Key md} (hT : T.Good P) (nF : Nat) :
    recSlotsAll env' (T.map f) nF = recSlotsAll env T nF := by
  unfold recSlotsAll
  congr 1
  funext j
  have h := hE.find (projFnName T j) hT
  simp only [projFnName, auxKey, Key.map_aux] at h ⊢
  rw [h]
  cases env.find? (.aux T (.projFn j)) with
  | none => rfl
  | some ci => cases ci <;> rfl

theorem etaProjs_ren (hE : EnvRelG P f L env env') {T : Key md} (hT : T.Good P) (us : List Level)
    (targs : List (Expr md)) (b : Expr md) (nF : Nat) :
    etaProjs env' (T.map f) us (targs.map (Expr.mapKeys f)) (b.mapKeys f) nF =
      (etaProjs env T us targs b nF).map (Expr.mapKeys f) := by
  unfold etaProjs
  rw [towerSlotsAll_ren hE hT]
  split <;> simp [List.map_map, Function.comp_def, projFnName, auxKey]

theorem etaProjs_good {T : Key md} (hT : T.Good P) {us : List Level} {targs : List (Expr md)}
    (ht : Expr.GoodList P targs) {b : Expr md} (hb : b.Good P) (nF : Nat) :
    Expr.GoodList P (etaProjs env T us targs b nF) := by
  unfold etaProjs
  split
  · intro x hx; simp only [List.mem_map] at hx; obtain ⟨_, _, rfl⟩ := hx; exact ⟨hT, hb⟩
  · intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨_, _, rfl⟩ := hx
    exact Expr.Good.mkAppN hT (by simp [Expr.goodList_append, ht, hb])

theorem etaCtorShape_ren (hE : EnvRelG P f L env env') {a : Expr md} (ha : a.Good P) :
    etaCtorShape env' (a.mapKeys f) = etaCtorShape env a := by
  unfold etaCtorShape
  rw [← Expr.mapKeys_getAppFn, Expr.getAppArgs_mapKeys, List.length_map]
  have hg := Expr.Good.getAppFn ha
  generalize a.getAppFn = g at hg ⊢
  cases g with
  | const c us =>
    simp only [Expr.mapKeys]
    rw [hE.find c hg]
    cases env.find? c with
    | none => rfl
    | some ci => cases ci <;> rfl
  | _ => rfl

@[simp] theorem etaFabArgs_mapKeys (T : Key md) (ust : List Level) (targs : List (Expr md))
    (major : Expr md) (nF : Nat) :
    etaFabArgs (T.map f) ust (targs.map (Expr.mapKeys f)) (major.mapKeys f) nF =
      (etaFabArgs T ust targs major nF).map (Expr.mapKeys f) := by
  simp [etaFabArgs, List.map_map, Function.comp_def, projFnName, auxKey]

theorem etaFabArgsE_ren (hE : EnvRelG P f L env env') {T : Key md} (hT : T.Good P)
    (ust : List Level) (targs : List (Expr md)) (major : Expr md) (nF : Nat) :
    etaFabArgsE env' (T.map f) ust (targs.map (Expr.mapKeys f)) (major.mapKeys f) nF =
      (etaFabArgsE env T ust targs major nF).map (Expr.mapKeys f) := by
  simp [etaFabArgsE, etaProjs_ren hE hT]

@[simp] theorem ProjEntry.fireOk_mapKeys (e : ProjEntry md) (us : List Level) :
    (e.mapKeys f).fireOk us = e.fireOk us := rfl

theorem andRescueSlots_ren (hE : EnvRelG P f L env env') {ctor : Key md} (hc : ctor.Good P)
    (nP : Nat) (ust : List Level) :
    andRescueSlots env' (ctor.map f) nP ust = andRescueSlots env ctor nP ust := by
  unfold andRescueSlots andRescueSlotsOf
  congr 1
  funext j
  have h := hE.findProj? (T := andName) trivial j
  simp only [Key.map_role] at h
  rw [h]
  cases he : env.findProj? andName j with
  | none => rfl
  | some e =>
    have hg := hE.findProj?_good (T := andName) trivial he
    simp only [Option.map_some, ProjEntry.mapKeys]
    rw [Key.map_beq hE.inj hg.2.1 hc]
    rfl

theorem recRuleKOf_ren (hE : EnvRelG P f L env env') {ctor : Key md} (hc : ctor.Good P) :
    recRuleKOf env'.find? (ctor.map f) = recRuleKOf env.find? ctor := by
  unfold recRuleKOf
  rw [hE.find ctor hc]
  cases hci : env.find? ctor with
  | none => rfl
  | some ci =>
    have hg := hE.good ctor ci hc hci
    cases ci with
    | ctorInfo cvj nP nF =>
      simp only [Option.map_some, ConstantInfo.mapKeys, ConstantVal.mapKeys_type,
        ← Expr.mapKeys_piResult, ← Expr.mapKeys_getAppFn]
      have hh := Expr.Good.getAppFn (Expr.Good.piResult hg.2)
      generalize cvj.type.piResult.getAppFn = g at hh ⊢
      cases g with
      | const T us =>
        simp only [Expr.mapKeys]
        rw [hE.find T hh]
        cases env.find? T with
        | none => rfl
        | some ci => cases ci <;> rfl
      | _ => rfl
    | _ => rfl

theorem recRuleEtaOf_ren (hE : EnvRelG P f L env env') {recName ctor : Key md}
    (hc : ctor.Good P) :
    recRuleEtaOf env'.find? (recName.map f) (ctor.map f) = recRuleEtaOf env.find? recName ctor := by
  unfold recRuleEtaOf
  rw [hE.find ctor hc]
  cases hci : env.find? ctor with
  | none => rfl
  | some ci =>
    have hg := hE.good ctor ci hc hci
    cases ci with
    | ctorInfo cvj nP nF =>
      simp only [Option.map_some, ConstantInfo.mapKeys, ConstantVal.mapKeys_type,
        ConstantVal.mapKeys_levelParams, ← Expr.mapKeys_piResult, ← Expr.mapKeys_getAppFn]
      have hh := Expr.Good.getAppFn (Expr.Good.piResult hg.2)
      generalize cvj.type.piResult.getAppFn = g at hh ⊢
      cases g with
      | const T us =>
        simp only [Expr.mapKeys]
        rw [hE.find T hh]
        cases hT : env.find? T with
        | none => rfl
        | some cT =>
          have hgT := hE.good T cT hh hT
          cases cT with
          | indInfo cvT caps =>
            simp only [Option.map_some, ConstantInfo.mapKeys, IndCaps.mapKeys,
              ConstantVal.mapKeys_levelParams, Key.map_isProjFnShape]
            congr 2
            have hcaps := hgT.2
            cases hec : caps.etaCtor with
            | none => rfl
            | some k =>
              have hk : k.Good P := hcaps k hec
              have hb : (some (Key.map f k) == some (Key.map f ctor)) = (some k == some ctor) := by
                rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, Option.some.injEq, Option.some.injEq]
                exact Key.map_eq_map_iff hE.inj hk hc
              simp only [Option.map_some, hb]
          | _ => rfl
      | _ => rfl
    | _ => rfl

theorem recRuleBits_ren (hE : EnvRelG P f L env env') {recName : Key md} {rl : RecRule md}
    (hrl : rl.Good P) :
    recRuleBits env'.find? (recName.map f) (rl.mapKeys f) =
      (recRuleBits env.find? recName rl).mapKeys f := by
  simp only [recRuleBits, RecRule.mapKeys]
  rw [recRuleKOf_ren hE hrl.1, recRuleEtaOf_ren hE hrl.1]

@[simp] theorem recRuleK_map (rules : List (RecRule md)) :
    recRuleK (rules.map (RecRule.mapKeys f)) = recRuleK rules := by
  rcases rules with _ | ⟨r, _ | _⟩ <;> rfl

@[simp] theorem recFireComparands_mapKeys (rl : RecRule md) (lps : List LevelParam)
    (us : List Level) (cvjLps : List LevelParam) (args : List (Expr md)) (rP : Nat) :
    recFireComparands (rl.mapKeys f) lps us cvjLps (args.map (Expr.mapKeys f)) rP =
      ((recFireComparands rl lps us cvjLps args rP).1,
       (recFireComparands rl lps us cvjLps args rP).2.map (Expr.mapKeys f)) := by
  unfold recFireComparands
  cases h : rl.fire with
  | nested lvls pins =>
    simp only [RecRule.mapKeys, h, RecRuleFire.mapKeys, List.map_map, Function.comp_def,
      ← List.map_take, Expr.mapKeys_instSpine, Expr.mapKeys_instantiateLevelParams]
  | inert => simp [RecRule.mapKeys, h, ← List.map_take]
  | plain => simp [RecRule.mapKeys, h, ← List.map_take]

@[simp] theorem ProjEntry.typeAt_mapKeys (e : ProjEntry md) (us : List Level)
    (targs : List (Expr md)) (pe : Expr md) :
    (e.mapKeys f).typeAt us (targs.map (Expr.mapKeys f)) (pe.mapKeys f) =
      (e.typeAt us targs pe).mapKeys f := by
  simp [ProjEntry.typeAt, ProjEntry.mapKeys, List.map_reverse]

end Ix.Kernel
