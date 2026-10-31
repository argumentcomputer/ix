module

public import IxC.Kernel.Verify.Rename.Decl4
public import IxC.Kernel.Inductives.SumParts
public import IxC.Kernel.Verify.Inductives.StructBody

@[expose] public section

/-!
# Renaming and the inductive recognisers' term builders (structures)

The terms the structure route builds and compares (`IxC/Kernel/Inductives/
StructParts.lean`) at renamed keys are the renamed terms; the syntactic
queries answer alike; the structure recogniser (`structPartsCore?`) finds the
renamed parts of a renamed block.
-/

set_option linter.unusedSimpArgs false

namespace Ix.Kernel

variable {md md' : Mode} {f : md.Id → md'.Id} {P : KeyScope md}

/-! ## Terms naming no key -/

theorem map_mapKeys_bvars {α : Type} (g : α → Nat) (l : List α) :
    (l.map fun x => (Expr.bvar (g x) : Expr md)).map (Expr.mapKeys f) =
      l.map fun x => (Expr.bvar (g x) : Expr md') := by
  simp [List.map_map, Function.comp_def, Expr.mapKeys]

theorem goodList_bvars {α : Type} (g : α → Nat) (l : List α) :
    Expr.GoodList P (l.map fun x => (Expr.bvar (g x) : Expr md)) := by
  intro e he
  simp only [List.mem_map] at he
  obtain ⟨_, _, rfl⟩ := he
  trivial

@[simp] theorem structPsAt_map (o nP : Nat) :
    (structPsAt o nP : List (Expr md)).map (Expr.mapKeys f) = structPsAt o nP :=
  map_mapKeys_bvars _ _

theorem structPsAt_good (o nP : Nat) : Expr.GoodList P (structPsAt o nP : List (Expr md)) :=
  goodList_bvars _ _

@[simp] theorem structRuleBody_mapKeys (nF : Nat) :
    (structRuleBody nF : Expr md).mapKeys f = structRuleBody nF := by
  simp [structRuleBody, Expr.mapKeys_mkAppN, map_mapKeys_bvars, Expr.mapKeys, Function.comp_def]

@[simp] theorem structProjPs_map (nP : Nat) :
    (structProjPs nP : List (Expr md)).map (Expr.mapKeys f) = structProjPs nP :=
  map_mapKeys_bvars _ _

/-! ## The builders -/

theorem structFam_map (T : Key md) (lps : List LevelParam) (nP o : Nat) :
    structFam (T.map f) lps nP o = (structFam T lps nP o).mapKeys f := by
  simp [structFam, Expr.mapKeys_mkAppN, map_mapKeys_bvars, Expr.mapKeys, Function.comp_def]

theorem structFam_good {T : Key md} (hT : T.Good P) (lps : List LevelParam) (nP o : Nat) :
    (structFam T lps nP o).Good P :=
  Expr.Good.mkAppN hT (goodList_bvars _ _)

theorem structCtorSpine_map (C : Key md) (lps : List LevelParam) (nP nF : Nat) :
    structCtorSpine (C.map f) lps nP nF = (structCtorSpine C lps nP nF).mapKeys f := by
  simp [structCtorSpine, Expr.mapKeys_mkAppN, map_mapKeys_bvars, Expr.mapKeys, List.map_append, Function.comp_def]

theorem structCtorSpine_good {C : Key md} (hC : C.Good P) (lps : List LevelParam) (nP nF : Nat) :
    (structCtorSpine C lps nP nF).Good P := by
  refine Expr.Good.mkAppN hC ?_
  intro e he
  simp only [List.mem_append, List.mem_map] at he
  rcases he with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> trivial

theorem structCtorSpineAt_map (C : Key md) (lps : List LevelParam) (o nP nF : Nat) :
    structCtorSpineAt (C.map f) lps o nP nF = (structCtorSpineAt C lps o nP nF).mapKeys f := by
  simp [structCtorSpineAt, Expr.mapKeys_mkAppN, map_mapKeys_bvars, Expr.mapKeys, List.map_append, Function.comp_def]

theorem structCtorSpineAt_good {C : Key md} (hC : C.Good P) (lps : List LevelParam)
    (o nP nF : Nat) : (structCtorSpineAt C lps o nP nF).Good P := by
  refine Expr.Good.mkAppN hC ?_
  intro e he
  simp only [structPsAt, List.mem_append, List.mem_map] at he
  rcases he with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> trivial

theorem structFamI_map (T : Key md) (lps : List LevelParam) (nP nIdx e o : Nat) :
    structFamI (T.map f) lps nP nIdx e o = (structFamI T lps nP nIdx e o).mapKeys f := by
  simp [structFamI, Expr.mapKeys_mkAppN, Expr.mapKeys, List.map_append]

theorem structFamI_good {T : Key md} (hT : T.Good P) (lps : List LevelParam) (nP nIdx e o : Nat) :
    (structFamI T lps nP nIdx e o).Good P := by
  refine Expr.Good.mkAppN hT ?_
  intro x hx
  simp only [structPsAt, List.mem_append, List.mem_map] at hx
  rcases hx with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> trivial

theorem replacePisPw_mapKeys (pw : PropWhen) :
    ∀ (k : Nat) (e b : Expr md),
      Expr.replacePisPw pw k (e.mapKeys f) (b.mapKeys f) =
        (Expr.replacePisPw pw k e b).map (Expr.mapKeys f)
  | 0, _, _ => rfl
  | k + 1, .forallE ty rest m, b => by
    simp only [Expr.mapKeys, Expr.replacePisPw, replacePisPw_mapKeys pw k rest b, Option.map_map]
    cases Expr.replacePisPw pw k rest b <;> rfl
  | _ + 1, .bvar _, _ | _ + 1, .fvar _ _, _ | _ + 1, .sort _, _ | _ + 1, .const _ _, _
  | _ + 1, .app _ _, _ | _ + 1, .lam _ _ _, _ | _ + 1, .letE _ _ _ _, _ | _ + 1, .lit _, _
  | _ + 1, .proj _ _ _, _ => rfl

theorem replacePisPw_good (pw : PropWhen) :
    ∀ {k : Nat} {e b r : Expr md}, e.Good P → b.Good P → Expr.replacePisPw pw k e b = some r →
      r.Good P
  | 0, _, _, _, _, hb, h => by simp only [Expr.replacePisPw, Option.some.injEq] at h; exact h ▸ hb
  | k + 1, .forallE ty rest m, b, r, he, hb, h => by
    simp only [Expr.replacePisPw, Option.map_eq_some_iff] at h
    obtain ⟨r₀, h₀, rfl⟩ := h
    exact ⟨he.1, replacePisPw_good pw he.2 hb h₀⟩
  | _ + 1, .bvar _, _, _, _, _, h | _ + 1, .fvar _ _, _, _, _, _, h
  | _ + 1, .sort _, _, _, _, _, h | _ + 1, .const _ _, _, _, _, _, h
  | _ + 1, .app _ _, _, _, _, _, h | _ + 1, .lam _ _ _, _, _, _, _, h
  | _ + 1, .letE _ _ _ _, _, _, _, _, h | _ + 1, .lit _, _, _, _, _, h
  | _ + 1, .proj _ _ _, _, _, _, _, h => nomatch h

theorem pisToLamsPw_mapKeys (pw : PropWhen) :
    ∀ (k : Nat) (e b : Expr md),
      Expr.pisToLamsPw pw k (e.mapKeys f) (b.mapKeys f) =
        (Expr.pisToLamsPw pw k e b).map (Expr.mapKeys f)
  | 0, _, _ => rfl
  | k + 1, .forallE ty rest m, b => by
    simp only [Expr.mapKeys, Expr.pisToLamsPw, pisToLamsPw_mapKeys pw k rest b, Option.map_map]
    cases Expr.pisToLamsPw pw k rest b <;> rfl
  | _ + 1, .bvar _, _ | _ + 1, .fvar _ _, _ | _ + 1, .sort _, _ | _ + 1, .const _ _, _
  | _ + 1, .app _ _, _ | _ + 1, .lam _ _ _, _ | _ + 1, .letE _ _ _ _, _ | _ + 1, .lit _, _
  | _ + 1, .proj _ _ _, _ => rfl

theorem pisToLamsPw_good (pw : PropWhen) :
    ∀ {k : Nat} {e b r : Expr md}, e.Good P → b.Good P → Expr.pisToLamsPw pw k e b = some r →
      r.Good P
  | 0, _, _, _, _, hb, h => by simp only [Expr.pisToLamsPw, Option.some.injEq] at h; exact h ▸ hb
  | k + 1, .forallE ty rest m, b, r, he, hb, h => by
    simp only [Expr.pisToLamsPw, Option.map_eq_some_iff] at h
    obtain ⟨r₀, h₀, rfl⟩ := h
    exact ⟨he.1, pisToLamsPw_good pw he.2 hb h₀⟩
  | _ + 1, .bvar _, _, _, _, _, h | _ + 1, .fvar _ _, _, _, _, _, h
  | _ + 1, .sort _, _, _, _, _, h | _ + 1, .const _ _, _, _, _, _, h
  | _ + 1, .app _ _, _, _, _, _, h | _ + 1, .lam _ _ _, _, _, _, _, h
  | _ + 1, .letE _ _ _ _, _, _, _, _, h | _ + 1, .lit _, _, _, _, _, h
  | _ + 1, .proj _ _ _, _, _, _, _, h => nomatch h

theorem structMotiveTyI_map (T : Key md) (lps : List LevelParam) (nP nIdx : Nat) (ℓ : Level)
    (itele : Expr md) :
    structMotiveTyI (T.map f) lps nP nIdx ℓ (itele.mapKeys f) =
      (structMotiveTyI T lps nP nIdx ℓ itele).map (Expr.mapKeys f) := by
  unfold structMotiveTyI
  rw [← replacePisPw_mapKeys]
  simp only [Expr.mapKeys, structFamI_map]

theorem structMotiveTyI_good {T : Key md} (hT : T.Good P) {lps : List LevelParam}
    {nP nIdx : Nat} {ℓ : Level} {itele r : Expr md} (hi : itele.Good P)
    (h : structMotiveTyI T lps nP nIdx ℓ itele = some r) : r.Good P :=
  replacePisPw_good _ hi (by simp only [Expr.Good]; exact ⟨structFamI_good hT _ _ _ _ _, trivial⟩) h

/-! ## Syntactic queries -/

theorem Expr.mentionsConst_map (hf : InjOn f P) {T : Key md} (hT : T.Good P) :
    ∀ {e : Expr md}, e.Good P → (e.mapKeys f).mentionsConst (T.map f) = e.mentionsConst T := by
  intro e he
  induction e with
  | const n us => simp only [Expr.mapKeys, Expr.mentionsConst, Key.map_beq hf he hT]
  | proj s i x ih =>
    simp only [Expr.Good] at he
    simp only [Expr.mapKeys, Expr.mentionsConst, Key.map_beq hf he.1 hT, ih he.2]
  | _ => simp_all [Expr.mapKeys, Expr.mentionsConst, Expr.Good]

theorem Expr.hasLooseBVar_mapKeys :
    ∀ (i : Nat) (e : Expr md), (e.mapKeys f).hasLooseBVar i = e.hasLooseBVar i := by
  intro i e
  induction e generalizing i <;> simp_all [Expr.mapKeys, Expr.hasLooseBVar]

theorem Expr.bvarB_mapKeys (e : Expr md) : (e.mapKeys f).bvarB = e.bvarB := by
  rw [Expr.bvarB_eq, Expr.bvarB_eq, Expr.bvarBound_mapKeys]

theorem Expr.hasLooseBVarB_mapKeys (i : Nat) (e : Expr md) :
    (e.mapKeys f).hasLooseBVarB i = e.hasLooseBVarB i := by
  rw [Expr.hasLooseBVarB_eq, Expr.hasLooseBVarB_eq, Expr.hasLooseBVar_mapKeys]

theorem structUsedLater_map (cty : Expr md) (nP j : Nat) :
    structUsedLater (cty.mapKeys f) nP j = structUsedLater cty nP j := by
  unfold structUsedLater
  rw [Expr.stripPis_mapKeys]
  cases Expr.stripPis (nP + j + 1) cty with
  | none => rfl
  | some p => exact Expr.hasLooseBVarB_mapKeys 0 p.2

theorem structProjGuards_map (cty : Expr md) (nP nF : Nat) (sorts : List Level) :
    structProjGuards (cty.mapKeys f) nP nF sorts = structProjGuards cty nP nF sorts := by
  simp only [structProjGuards, structUsedLater_map]

theorem structCtorResidOk_map (hf : InjOn f P) {T : Key md} (hT : T.Good P)
    (lps : List LevelParam) (nP o nIdx : Nat) {cbody : Expr md} (hc : cbody.Good P) :
    structCtorResidOk (T.map f) lps nP o nIdx (cbody.mapKeys f) =
      structCtorResidOk T lps nP o nIdx cbody := by
  unfold structCtorResidOk
  rw [← Expr.mapKeys_getAppFn, Expr.getAppArgs_mapKeys, List.length_map, ← List.map_take]
  have h1 : (Expr.const (T.map f) (lps.map Level.param) : Expr md') =
      (Expr.const T (lps.map Level.param) : Expr md).mapKeys f := rfl
  rw [h1, Expr.mapKeys_beq hf hc.getAppFn (show Expr.Good P (Expr.const T _) from hT),
    ← structPsAt_map (f := f) o nP]
  congr 1
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  exact ⟨fun h => Expr.mapKeys_list_inj hf
    (fun x hx => hc.getAppArgs x (List.mem_of_mem_take hx)) (structPsAt_good o nP) h,
    fun h => h ▸ rfl⟩

end Ix.Kernel
