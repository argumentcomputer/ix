import Ix.Cert.StrongValueLaws
import Ix.Cert.UnchangedStepLaws

/-! # The value-level Source laws of a renamed environment

`Obligation.UnchangedRules`: a strong model of an environment that installs the
constants of a renaming of `envQ` gives `envQ`'s value-level recursor rules and
capability laws at the pulled-back values.

The strong model satisfies the laws of its own environment
(`StrongValueLaws.recRuleLaws`, `StrongValueLaws.capabilityLaws`). That
environment holds every constant of `envQ`, renamed, and answers the lookups
alike. Each law of `envQ` is therefore the law of the renamed constant there.
* Its premises move to the compiled environment: a good term denotes there,
  renamed, what it denotes in `envQ` at the pulled-back values (`Denotes.push`),
  and so do the fits (`Fits.push`).
* Its conclusion is the same equation, since the pulled-back value of a key is
  its renamed key's value. -/

namespace Ix.Cert.UnchangedValueLaws

open Ix.Kernel Ix.Kernel.SetTheory

universe w

variable {V : Type w} [SetTheory V]
variable {P : Mode.Id .source → Prop} {f : Mode.Id .source → Mode.Id .anon}
variable {envQ : Env .source} {envR envA : Env .anon}

/-! ## Denotations and fits, pushed along the renaming -/

/-- **A good term denotes in the compiled environment, renamed, what it denotes in
`envQ` at the pulled-back values.** -/
theorem Denotes.push (rel : EnvRel P f envQ envR) (same : SameEnv envA envR)
    {cval : Key .anon → (LevelParam → Nat) → V} {φ : LevelParam → Nat} {ρ : BVarIdx → V}
    {e : Ix.Kernel.Expr .source} {v : V}
    (h : Denotes (pullCval f cval) envQ φ ρ e v) :
    e.Good (KeyScope.ofId P) → Denotes cval envA φ ρ (e.mapKeys f) v := by
  induction h with
  | bvar => intro _; exact .bvar
  | sort => intro _; exact .sort
  | @const ρ n us ci hf hlen =>
    intro _
    have hf' : envA.find? (n.map f) = some (ci.mapKeys f) := by
      rw [same.find]
      exact rel.find_some hf
    have hlps : (ci.mapKeys f).toConstantVal.levelParams = ci.toConstantVal.levelParams := by
      simp [ConstantInfo.mapKeys_toConstantVal]
    have hd := Denotes.const (cval := cval) (φ := φ) (ρ := ρ) (us := us) hf'
      (by rw [hlps]; exact hlen)
    rw [hlps] at hd
    exact hd
  | app _ _ ihf iha => intro hg; exact .app (ihf hg.1) (iha hg.2)
  | lam _ _ hP ihA ihF => intro hg; exact .lam (ihA hg.1) (fun x hx => ihF x hx hg.2) hP
  | pi _ _ hP ihA ihB => intro hg; exact .pi (ihA hg.1) (fun x hx => ihB x hx hg.2) hP
  | proj_table ht _ ih =>
    intro hg
    exact .proj_table (by rw [findProj_sameFind same.find, rel.findProj? hg.1, ht]; rfl) (ih hg.2)
  | proj_fst ht _ ih =>
    intro hg
    exact .proj_fst (by rw [findProj_sameFind same.find, rel.findProj? hg.1, ht]; rfl) (ih hg.2)
  | proj_snd ht _ ih =>
    intro hg
    exact .proj_snd (by rw [findProj_sameFind same.find, rel.findProj? hg.1, ht]; rfl) (ih hg.2)
  | @natLit ρ n X _ ih =>
    intro _
    have h := ih (natLitToConstructor_good (KeyScope.ofId_pre P) n)
    rw [natLitToConstructor_mapKeys] at h
    exact .natLit h
  | @strLit ρ s X _ ih =>
    intro _
    have h := ih (strLitToConstructor_good (KeyScope.ofId_pre P) (KeyScope.ofId_str P) s)
    rw [strLitToConstructor_mapKeys] at h
    exact .strLit h

/-- **A fit of a good telescope holds in the compiled environment, renamed**, and
its residual is good. -/
theorem Fits.push (rel : EnvRel P f envQ envR) (same : SameEnv envA envR)
    {cval : Key .anon → (LevelParam → Nat) → V} {φ : LevelParam → Nat} :
    ∀ {ρ ρ' : BVarIdx → V} {T R : Ix.Kernel.Expr .source} {vs : List V},
      Fits (pullCval f cval) envQ φ ρ T vs ρ' R → T.Good (KeyScope.ofId P) →
      Fits cval envA φ ρ (T.mapKeys f) vs ρ' (R.mapKeys f) ∧ R.Good (KeyScope.ofId P) := by
  intro ρ ρ' T R vs h
  induction h with
  | nil => intro hg; exact ⟨.nil, hg⟩
  | cons hA hx _ ih =>
    intro hg
    obtain ⟨h1, h2⟩ := ih hg.2
    exact ⟨.cons (Denotes.push rel same hA hg.1) hx h1, h2⟩

/-! ## Helpers -/

theorem getD_map_default {α β : Type _} {g : α → β} {d : α} {d' : β} (h : g d = d')
    (l : List α) (i : Nat) : (l.map g).getD i d' = g (l.getD i d) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> simp [h]

theorem getD_good {l : List (Ix.Kernel.Expr .source)} (hl : Expr.GoodList (KeyScope.ofId P) l)
    (i : Nat) : (l.getD i (.bvar 0)).Good (KeyScope.ofId P) := by
  simp only [List.getD_eq_getElem?_getD]
  cases hi : l[i]? with
  | none => trivial
  | some x => exact hl x (List.mem_of_getElem? hi)

theorem towerSlotsAll_sameFind {md : Mode} {e e' : Env md} (hf : ∀ k, e.find? k = e'.find? k)
    (T : Key md) (nF : Nat) : towerSlotsAll e T nF = towerSlotsAll e' T nF := by
  unfold towerSlotsAll
  simp only [findProj_sameFind hf]

theorem recSlotsAll_sameFind {md : Mode} {e e' : Env md} (hf : ∀ k, e.find? k = e'.find? k)
    (T : Key md) (nF : Nat) : recSlotsAll e T nF = recSlotsAll e' T nF := by
  unfold recSlotsAll
  simp only [hf]

theorem fire_plain_of_map {rl : RecRule .source} (h : (rl.mapKeys f).fire = .plain) :
    rl.fire = .plain := by
  cases hr : rl.fire <;> simp_all [RecRule.mapKeys, RecRuleFire.mapKeys]

theorem fire_nested_of_map {rl : RecRule .source} {lvls : List Ix.Kernel.Level}
    {pins' : List (Ix.Kernel.Expr .anon)} (h : (rl.mapKeys f).fire = .nested lvls pins') :
    ∃ pins, rl.fire = .nested lvls pins ∧ pins' = pins.map (Expr.mapKeys f) := by
  cases hr : rl.fire with
  | nested l ps =>
    simp only [RecRule.mapKeys, hr, RecRuleFire.mapKeys, RecRuleFire.nested.injEq] at h
    exact ⟨ps, by rw [h.1], h.2.symm⟩
  | _ => simp [RecRule.mapKeys, hr, RecRuleFire.mapKeys] at h

/-- A key with a projection table in a good environment is good. -/
theorem findProj_key_good (rel : EnvRel P f envQ envR) {sn : Key .source} {i : Nat}
    {entry : ProjEntry .source} (h : envQ.findProj? sn i = some entry) :
    sn.Good (KeyScope.ofId P) := by
  unfold Env.findProj? at h
  split at h
  · rename_i tbl htbl
    have hg := UnchangedStepLaws.EnvRel.found rel _ _ htbl
    simpa [projTableName, auxKey] using hg
  · exact nomatch h

/-! ## The laws, pulled back -/

variable (rel : EnvRel P f envQ envR) (same : SameEnv envA envR)
  (M : Cached.StrongModel V envA)

include rel same

/-- **The recursor rules of `envQ` at the pulled-back values.** -/
theorem recRuleLaw_pull {c : Key .source} {cv : Ix.Kernel.ConstantVal .source} {mI rP : Nat}
    {rules : List (RecRule .source)} (hfind : envQ.find? c = some (.recInfo cv mI rP rules))
    {rl : RecRule .source} (hrl : rl ∈ rules) (hfire : rl.fire ≠ .inert) :
    RecRuleLaw (pullCval f M.model.cval) envQ c cv mI rP rl := by
  have hfindA : envA.find? (c.map f) =
      some (.recInfo (cv.mapKeys f) mI rP (rules.map (RecRule.mapKeys f))) := by
    rw [same.find]
    exact rel.find_some hfind
  have hgc := rel.all _ (Semantics.Env.find?_mem hfind)
  have hrlG : rl.Good (KeyScope.ofId P) := hgc.2 rl hrl
  have lawA := StrongValueLaws.recRuleLaw M hfindA (List.mem_map_of_mem hrl)
    (by simpa using hfire)
  intro φ us hus cvj cnP cnF hctor usj husj hlv ρ ρx ρy Rx Ry xs ys hxl hyl hfy hfx hpar hnest
    hidxl hidx R hR
  have hctorA : envA.find? (rl.mapKeys f).ctor = some (.ctorInfo (cvj.mapKeys f) cnP cnF) := by
    rw [same.find]
    exact rel.find_some hctor
  have hgj := rel.all _ (Semantics.Env.find?_mem hctor)
  obtain ⟨hfyA, hgRy⟩ := Fits.push rel same hfy (Expr.Good.instantiateLevelParams hgj.2 _ _)
  obtain ⟨hfxA, -⟩ := Fits.push rel same hfx (Expr.Good.instantiateLevelParams hgc.1.2 _ _)
  have hcmp := congrArg Prod.fst
    (recFireComparands_mapKeys (f := f) rl cv.levelParams us cvj.levelParams [] rP)
  simp only [List.map_nil] at hcmp
  refine lawA φ us hus (cvj.mapKeys f) cnP cnF hctorA usj husj
    (by
      show Ix.Kernel.Level.substFn φ cvj.levelParams usj = Ix.Kernel.Level.substFn φ cvj.levelParams
        (recFireComparands (rl.mapKeys f) cv.levelParams us cvj.levelParams [] rP).1
      rw [hcmp]; exact hlv)
    ρ ρx ρy (Rx.mapKeys f) (Ry.mapKeys f) xs ys hxl hyl
    (by simpa only [ConstantVal.mapKeys_type, ConstantVal.mapKeys_levelParams,
      Expr.mapKeys_instantiateLevelParams] using hfyA)
    (by
      have h := hfxA
      simp only [
        Expr.mapKeys_instantiateLevelParams] at h
      exact h)
    (fun hb hp i hi him => hpar hb (fire_plain_of_map hp) i hi him) ?_ ?_ ?_ R ?_
  · intro lvls pins' hn i hi
    obtain ⟨pins, hn0, rfl⟩ := fire_nested_of_map hn
    have hpinsG : Expr.GoodList (KeyScope.ofId P) pins := by
      have := hrlG.2.1
      rw [hn0] at this
      exact this
    have h := Denotes.push rel same (hnest lvls pins hn0 i hi)
      (Expr.Good.instantiateLevelParams (getD_good hpinsG i) _ _)
    rw [getD_map_default (g := Expr.mapKeys f) (d := (default : Ix.Kernel.Expr .source))
      (d' := (default : Ix.Kernel.Expr .anon)) rfl,
      ConstantVal.mapKeys_levelParams, ← Expr.mapKeys_instantiateLevelParams]
    exact h
  · rw [Expr.getAppArgs_mapKeys, List.length_map]
    exact hidxl
  · intro i hi
    have h := Denotes.push rel same (hidx i hi) (getD_good (Expr.Good.getAppArgs hgRy) _)
    rw [Expr.getAppArgs_mapKeys, getD_map_default (g := Expr.mapKeys f)
      (d := (Ix.Kernel.Expr.bvar 0 : Ix.Kernel.Expr .source)) (d' := Ix.Kernel.Expr.bvar 0) rfl]
    exact h
  · have h := Denotes.push rel same hR (Expr.Good.instantiateLevelParams hrlG.2.2 _ _)
    rw [Expr.mapKeys_instantiateLevelParams] at h
    exact h

/-- The η-expansion's field values agree across the renaming. -/
theorem etaFieldVals_pull {T : Key .source} (hTg : T.Good (KeyScope.ofId P)) (ψ : LevelParam → Nat)
    (ts : List V) (x : V) (nF : Nat) :
    etaFieldVals M.model.cval envA (T.map f) ψ ts x nF =
      etaFieldVals (pullCval f M.model.cval) envQ T ψ ts x nF := by
  unfold etaFieldVals
  rw [towerSlotsAll_sameFind same.find, towerSlotsAll_ren rel.toG hTg,
    findProj_sameFind same.find, rel.findProj? hTg, Option.map_map]
  rfl

/-- **Structure η of `envQ` at the pulled-back values.** -/
theorem etaLaw_pull {T : Key .source} {cvT : Ix.Kernel.ConstantVal .source}
    {caps : Ix.Kernel.IndCaps .source} (hT : envQ.find? T = some (.indInfo cvT caps))
    (heta : caps.eta = true) (hres : reservedBasisNames.contains T = false)
    (hslots : (towerSlotsAll envQ T caps.etaFields || recSlotsAll envQ T caps.etaFields) = true) :
    EtaLaw (pullCval f M.model.cval) envQ T cvT caps := by
  have hTA : envA.find? (T.map f) = some (.indInfo (cvT.mapKeys f) (caps.mapKeys f)) := by
    rw [same.find]
    exact rel.find_some hT
  have hTg : T.Good (KeyScope.ofId P) := UnchangedStepLaws.EnvRel.found rel T _ hT
  have hgT := rel.all _ (Semantics.Env.find?_mem hT)
  have lawA := StrongValueLaws.etaLaw M hTA heta
    (by rw [reservedBasisNames_contains_map]; exact hres)
    (by
      show (towerSlotsAll envA (T.map f) caps.etaFields ||
        recSlotsAll envA (T.map f) caps.etaFields) = true
      rw [towerSlotsAll_sameFind same.find, towerSlotsAll_ren rel.toG hTg,
        recSlotsAll_sameFind same.find, recSlotsAll_ren rel.toG hTg]
      exact hslots)
  intro C hC hCres hCstored φ us hus ρ ρ' R ts x htl hfit hx
  obtain ⟨cvC, nP, nF, hCf⟩ := hCstored
  obtain ⟨hfitA, -⟩ := Fits.push rel same hfit (Expr.Good.instantiateLevelParams hgT.1.2 _ _)
  have h := lawA (C.map f) (by show caps.etaCtor.map (Key.map f) = _; rw [hC]; rfl)
    (by rw [reservedBasisNames_contains_map]; exact hCres)
    ⟨cvC.mapKeys f, nP, nF, by rw [same.find]; exact rel.find_some hCf⟩ φ us hus ρ ρ'
    (R.mapKeys f) ts x htl
    (by simpa only [ConstantVal.mapKeys_type, ConstantVal.mapKeys_levelParams,
      Expr.mapKeys_instantiateLevelParams] using hfitA) hx
  refine h.trans ?_
  rw [show (caps.mapKeys f).etaFields = caps.etaFields from rfl,
    ConstantVal.mapKeys_levelParams, etaFieldVals_pull rel same M hTg]
  rfl

/-- **Unit-likeness of `envQ` at the pulled-back values.** -/
theorem unitLaw_pull {T : Key .source} {cvT : Ix.Kernel.ConstantVal .source}
    {caps : Ix.Kernel.IndCaps .source} (hT : envQ.find? T = some (.indInfo cvT caps))
    (hunit : caps.unitlike = true) (hres : reservedBasisNames.contains T = false) :
    UnitLaw (pullCval f M.model.cval) envQ T cvT caps := by
  have hTA : envA.find? (T.map f) = some (.indInfo (cvT.mapKeys f) (caps.mapKeys f)) := by
    rw [same.find]
    exact rel.find_some hT
  have hgT := rel.all _ (Semantics.Env.find?_mem hT)
  have lawA := StrongValueLaws.unitLaw M hTA hunit
    (by rw [reservedBasisNames_contains_map]; exact hres)
  intro φ us hus ρ ρ' R ts x y htl hfit hx hy
  obtain ⟨hfitA, -⟩ := Fits.push rel same hfit (Expr.Good.instantiateLevelParams hgT.1.2 _ _)
  exact lawA φ us hus ρ ρ' (R.mapKeys f) ts x y htl
    (by simpa only [ConstantVal.mapKeys_type, ConstantVal.mapKeys_levelParams,
      Expr.mapKeys_instantiateLevelParams] using hfitA) hx hy

/-- **The projection law of `envQ` at the pulled-back values.** -/
theorem projLaw_pull {sn : Key .source} {i : Nat} {entry : ProjEntry .source}
    (hent : envQ.findProj? sn i = some entry) :
    ProjLaw (pullCval f M.model.cval) envQ entry i := by
  have hsn := findProj_key_good rel hent
  have hentA : envA.findProj? (sn.map f) i = some (entry.mapKeys f) := by
    rw [findProj_sameFind same.find, rel.findProj? hsn, hent]
    rfl
  have lawA := StrongValueLaws.projLaw M hentA
  intro φ us hus hfire cvC nP nF hctor ρ ρ' R ys hyl hfit
  have hgC := rel.all _ (Semantics.Env.find?_mem hctor)
  obtain ⟨hfitA, -⟩ := Fits.push rel same hfit (Expr.Good.instantiateLevelParams hgC.2 _ _)
  exact lawA φ us hus (by rw [ProjEntry.fireOk_mapKeys]; exact hfire) (cvC.mapKeys f) nP nF
    (by rw [same.find]; exact rel.find_some hctor) ρ ρ' (R.mapKeys f) ys hyl
    (by simpa only [ConstantVal.mapKeys_type, ConstantVal.mapKeys_levelParams,
      Expr.mapKeys_instantiateLevelParams] using hfitA)

end Ix.Cert.UnchangedValueLaws

namespace Ix.Cert

open Ix.Cert.UnchangedValueLaws

universe w

/-- **The value-level Source laws of a renamed environment**
(`Obligation.UnchangedRules`). -/
theorem unchangedRules : Obligation.UnchangedRules.{w} := by
  intro V _ P f envQ envR envA M rel same
  exact ⟨fun _ _ _ _ _ hfind _ hrl hfire => recRuleLaw_pull rel same M hfind hrl hfire,
    fun _ _ _ hT heta hres hslots => etaLaw_pull rel same M hT heta hres hslots,
    fun _ _ _ hT hunit hres => unitLaw_pull rel same M hT hunit hres,
    fun _ _ _ hent => projLaw_pull rel same M hent⟩

/-- info: 'Ix.Cert.unchangedRules' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms unchangedRules

end Ix.Cert
