module

public import IxC.Kernel.Verify.Rename.Decl4

@[expose] public section

/-!
# The `.indDecl` shape guard, renamed (step 7.3, chunk (iii))

`indShapeOk` at the renamed environment and block is `indShapeOk` at the
original ones: its lookups answer alike on good keys (`EnvRel`), its name lists
are the renamed lists, and renaming is injective on good keys, so `contains`
and `Nodup` answer alike too. So `checkIndShape` throws on the renamed run
exactly when it throws on the original, and passes otherwise (`checkIndShape_sim`).
-/

set_option linter.unusedSimpArgs false

namespace Ix.Kernel

variable {md md' : Mode} {f : md.Id → md'.Id} {P : md.Id → Prop}

/-- **`constsResolveBy`, renamed**: over lookups that answer alike on good keys. -/
theorem constsResolveBy_ren {has : Key md → Bool} {has' : Key md' → Bool}
    (hhas : ∀ k : Key md, k.Good P → has' (k.map f) = has k) :
    ∀ {e : Expr md}, e.Good P → (e.mapKeys f).constsResolveBy has' = e.constsResolveBy has := by
  have hr : ∀ r : Role, has' (roleKey r) = has (roleKey r) := fun r => hhas (roleKey r) trivial
  intro e he
  induction e with
  | lit l =>
    cases l <;> simp only [Expr.mapKeys, Expr.constsResolveBy, natName, natZeroName, natSuccName,
      stringName, stringOfListName, listName, listNilName, listConsName, charName, charOfNatName, hr]
  | const n us =>
    simp only [Expr.mapKeys, Expr.constsResolveBy]
    exact hhas n he
  | proj s i x ih =>
    simp only [Expr.mapKeys, Expr.constsResolveBy]
    rw [hhas s he.1, ih he.2]
  | _ => simp_all [Expr.constsResolveBy]

/-- The block's type formers' names, renamed. -/
theorem indFormerNames_map : ∀ block : List (ConstantInfo md),
    indFormerNames (block.map (ConstantInfo.mapKeys f)) = (indFormerNames block).map (Key.map f)
  | [] => rfl
  | c :: cs => by
    have ih := indFormerNames_map cs
    cases c <;> simp_all [indFormerNames]

/-- The block's constructors' names, renamed. -/
theorem indCtorNames_map : ∀ block : List (ConstantInfo md),
    indCtorNames (block.map (ConstantInfo.mapKeys f)) = (indCtorNames block).map (Key.map f)
  | [] => rfl
  | c :: cs => by
    have ih := indCtorNames_map cs
    cases c <;> simp_all [indCtorNames]

theorem indFormerNames_good : ∀ {block : List (ConstantInfo md)}, (∀ c ∈ block, c.Good P) →
    ∀ k ∈ indFormerNames block, k.Good P
  | [], _ => by simp [indFormerNames]
  | c :: cs, h => by
    have ih := indFormerNames_good (block := cs)
      (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))
    have hc := h c List.mem_cons_self
    intro k hk
    cases c <;> simp only [indFormerNames, List.filterMap_cons] at hk
    all_goals first
      | exact ih k hk
      | (rcases List.mem_cons.mp hk with rfl | hk
         · exact hc.1.1
         · exact ih k hk)

theorem indCtorNames_good : ∀ {block : List (ConstantInfo md)}, (∀ c ∈ block, c.Good P) →
    ∀ k ∈ indCtorNames block, k.Good P
  | [], _ => by simp [indCtorNames]
  | c :: cs, h => by
    have ih := indCtorNames_good (block := cs)
      (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))
    have hc := h c List.mem_cons_self
    intro k hk
    cases c <;> simp only [indCtorNames, List.filterMap_cons] at hk
    all_goals first
      | exact ih k hk
      | (rcases List.mem_cons.mp hk with rfl | hk
         · exact hc.1
         · exact ih k hk)

/-- `contains` of a renamed list of good keys, at a renamed good key. -/
theorem contains_map_ren (hf : InjOn f P) {l : List (Key md)} (hl : ∀ k ∈ l, k.Good P)
    {k : Key md} (hk : k.Good P) : (l.map (Key.map f)).contains (k.map f) = l.contains k := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [List.map_cons, List.contains_cons]
    rw [Key.map_beq hf hk (hl a List.mem_cons_self),
      ih (fun k' hk' => hl k' (List.mem_cons_of_mem _ hk'))]

/-- `Nodup` of a renamed list of good keys. -/
theorem nodup_map_ren (hf : InjOn f P) {l : List (Key md)} (hl : ∀ k ∈ l, k.Good P) :
    (l.map (Key.map f)).Nodup ↔ l.Nodup := by
  induction l with
  | nil => simp
  | cons a as ih =>
    have has : ∀ k ∈ as, k.Good P := fun k hk => hl k (List.mem_cons_of_mem _ hk)
    have ha : a.Good P := hl a List.mem_cons_self
    simp only [List.map_cons, List.nodup_cons, ih has, List.mem_map]
    constructor
    · rintro ⟨hn, hd⟩
      exact ⟨fun hm => hn ⟨a, hm, rfl⟩, hd⟩
    · rintro ⟨hn, hd⟩
      refine ⟨?_, hd⟩
      rintro ⟨b, hb, he⟩
      exact hn (Key.map_inj hf (has b hb) ha he ▸ hb)

/-- `List.all` at functions that agree on the list's members. -/
theorem List.all_congr_mem' {α : Type} {l : List α} {p q : α → Bool} (h : ∀ a ∈ l, p a = q a) :
    l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [List.all_cons, h a List.mem_cons_self,
      ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]

/-- **The shape guard, renamed**: it answers alike on a good block over
related environments. -/
theorem indShapeOk_ren {env : Env md} {env' : Env md'} (hE : EnvRel P f env env')
    {block : List (ConstantInfo md)} (hb : ∀ c ∈ block, c.Good P) :
    indShapeOk env'.find? (block.map (ConstantInfo.mapKeys f)) = indShapeOk env.find? block := by
  have hf := hE.inj
  have hfg := indFormerNames_good hb
  have hcg := indCtorNames_good hb
  have hhas : ∀ k : Key md, k.Good P →
      indShapeHas env'.find? (block.map (ConstantInfo.mapKeys f)) (k.map f) =
        indShapeHas env.find? block k := by
    intro k hk
    simp only [indShapeHas, indFormerNames_map, hE.find_isSome hk, contains_map_ren hf hfg hk]
  simp only [indShapeOk, List.all_map, indCtorNames_map, nodup_map_ren hf hcg]
  congr 1
  · congr 1
    · apply List.all_congr_mem'
      intro c hc
      cases c with
      | indInfo cv caps =>
        simp only [Function.comp, ConstantInfo.mapKeys, ConstantVal.mapKeys_type]
        exact constsResolveBy_ren hhas (hb _ hc).1.2
      | ctorInfo cv nP nF =>
        simp only [Function.comp, ConstantInfo.mapKeys, ConstantVal.mapKeys_type]
        exact constsResolveBy_ren hhas (hb _ hc).2
      | _ => rfl
    · apply List.all_congr_mem'
      intro c hc
      simp only [Function.comp]
      have hcG := hcg c hc
      have hn : (env'.find? (c.map f)).isNone = (env.find? c).isNone := by
        rw [← Option.not_isSome, ← Option.not_isSome, hE.find_isSome hcG]
      rw [hn, indFormerNames_map, contains_map_ren hf hfg hcG]

/-- **`checkIndShape`, renamed**: a pass on a good block is a pass on the
renamed block over related environments. -/
theorem checkIndShape_sim {env : Env md} {env' : Env md'} (hE : EnvRel P f env env')
    {block : List (ConstantInfo md)} (hb : ∀ c ∈ block, c.Good P) :
    SimE (fun _ => True) id (checkIndShape (m := CheckM md) env.find? block)
      (checkIndShape (m := CheckM md') env'.find? (block.map (ConstantInfo.mapKeys f))) := by
  unfold SimE
  intro u h
  unfold checkIndShape at h ⊢
  rw [indShapeOk_ren hE hb]
  split
  · exact ⟨trivial, rfl⟩
  · split at h
    · contradiction
    · exact nomatch h

end Ix.Kernel
