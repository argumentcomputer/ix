module

public import IxC.Kernel.Model.LevelRenKit

@[expose] public section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-!
# Transport of the rules along a renaming of level parameters

A derivation of the rules tier moves along a **renaming of level parameters**
`instantiateLevelParams ks ws` whose replacements are parameters (`Level.IsRen ws`): the
environment and the depth stay, every term of the judgement is renamed, and a stored constant
used at levels `us` is used at the renamed levels.

**What it needs** (`LvRen`): the stored terms mention only their constant's level parameters
(`LvStore`: `EnvWF` and `ThmLevels`), and they apply every stored constant at its own number of
level parameters (`StoreAr`). The terms of the judgement are arity-correct too
(`Expr.arOk`): a full-grade inference establishes it of its subject from its own derivation,
given its annotations; reduction and inference keep it. Without arity the statement is false:
`DefEq.unitLikeTy`, `DefEq.structEtaTy` and `Red.iota` at a nested rule instantiate a stored type
at a level list no premise measures, and at a short list the stored parameters left over are not
renamed while the rest of the judgement is.

**Why a renaming**: three side conditions read a stored datum instantiated at the use's levels
as "zero at every valuation" or "never zero" (`FireSem`, `isProofFast`, `capsNeverZero`); a
renaming keeps the value of a level at the constant valuations that decide them. Every other
level side condition is an equation between values at every valuation, or the zero-ness datum
of a level, and moves under any instantiation.
-/

namespace Ix.Kernel.Rules

open Ix.Kernel.LevelRen

/-- **The transport's hypotheses.** -/
structure LvRen (env : Env md) (ks : List LevelParam) (ws : List Level) : Prop where
  ren : Level.IsRen ws
  lv : LvStore env
  ar : StoreAr env

/-! ## The basis constants the rules fabricate have their arity -/

section Guards

variable {env : Env md}

theorem lps_of_guard {p : Option (ConstantInfo md) → Bool} {n : Key md} {k : Nat}
    (hp : ∀ ci, p (some ci) = true → ci.toConstantVal.levelParams.length = k)
    (h : p (env.find? n) = true) :
    ∀ ci, env.find? n = some ci → ci.toConstantVal.levelParams.length = k :=
  fun ci hf => hp ci (by rw [← hf]; exact h)

theorem arOk_const_of_guard {p : Option (ConstantInfo md) → Bool} {n : Key md} {us : List Level}
    (hp : ∀ ci, p (some ci) = true → ci.toConstantVal.levelParams.length = us.length)
    (h : p (env.find? n) = true) : Expr.arOk env (.const n us) = true :=
  arOk_const_of (fun ci hf => (lps_of_guard hp h ci hf).symm)

theorem natIndOk_len : ∀ ci : ConstantInfo md, natIndOk (some ci) = true →
    ci.toConstantVal.levelParams.length = ([] : List Level).length := by
  intro ci h
  cases ci with
  | indInfo cv caps =>
    simp only [natIndOk, Bool.and_eq_true, List.isEmpty_iff] at h
    show cv.levelParams.length = 0
    simp [h.1]
  | _ => simp [natIndOk] at h

theorem natZeroOk_len : ∀ ci : ConstantInfo md, natZeroOk (some ci) = true →
    ci.toConstantVal.levelParams.length = ([] : List Level).length := by
  intro ci h
  cases ci with
  | ctorInfo cv nP nF =>
    simp only [natZeroOk, Bool.and_eq_true, List.isEmpty_iff] at h
    show cv.levelParams.length = 0
    simp [h.1]
  | _ => simp [natZeroOk] at h

theorem natSuccOk_len : ∀ ci : ConstantInfo md, natSuccOk (some ci) = true →
    ci.toConstantVal.levelParams.length = ([] : List Level).length := by
  intro ci h
  cases ci with
  | ctorInfo cv nP nF =>
    simp only [natSuccOk, Bool.and_eq_true, List.isEmpty_iff] at h
    show cv.levelParams.length = 0
    simp [h.1]
  | _ => simp [natSuccOk] at h

theorem anyEmpty_len {p : Option (ConstantInfo md) → Bool}
    (hp : ∀ ci, p (some ci) = true → ci.toConstantVal.levelParams.isEmpty = true) :
    ∀ ci, p (some ci) = true → ci.toConstantVal.levelParams.length = ([] : List Level).length := by
  intro ci h
  have := hp ci h
  rw [List.isEmpty_iff] at this
  simp [this]

theorem stringTyOk_empty : ∀ ci : ConstantInfo md, stringTyOk (some ci) = true →
    ci.toConstantVal.levelParams.isEmpty = true := by
  intro ci h
  simp only [stringTyOk, Bool.and_eq_true] at h
  exact h.1

theorem charTyOk_empty : ∀ ci : ConstantInfo md, charTyOk (some ci) = true →
    ci.toConstantVal.levelParams.isEmpty = true := by
  intro ci h
  simp only [charTyOk, Bool.and_eq_true] at h
  exact h.1

theorem charOfNatTyOk_empty : ∀ ci : ConstantInfo md, charOfNatTyOk (some ci) = true →
    ci.toConstantVal.levelParams.isEmpty = true := by
  intro ci h
  simp only [charOfNatTyOk, Bool.and_eq_true] at h
  exact h.1

theorem stringOfListTyOk_empty : ∀ ci : ConstantInfo md, stringOfListTyOk (some ci) = true →
    ci.toConstantVal.levelParams.isEmpty = true := by
  intro ci h
  simp only [stringOfListTyOk, Bool.and_eq_true] at h
  exact h.1

theorem listNilTyOk_len : ∀ ci : ConstantInfo md, listNilTyOk (some ci) = true →
    ci.toConstantVal.levelParams.length = ([Level.zero] : List Level).length := by
  intro ci h
  simp only [listNilTyOk] at h
  split at h
  · rename_i p hp
    simp [hp]
  · exact nomatch h

theorem listConsTyOk_len : ∀ ci : ConstantInfo md, listConsTyOk (some ci) = true →
    ci.toConstantVal.levelParams.length = ([Level.zero] : List Level).length := by
  intro ci h
  simp only [listConsTyOk] at h
  split at h
  · rename_i p hp
    simp [hp]
  · exact nomatch h

theorem natAddTyOk_len : ∀ ci : ConstantInfo md, natAddTyOk (some ci) = true →
    ci.toConstantVal.levelParams.length = ([] : List Level).length := by
  intro ci h
  obtain ⟨n, v, hint, mb₁, mb₂, he, -⟩ := natAddTyOk_inv h
  obtain rfl := Option.some.inj he
  rfl

theorem natLit_arOk (hs : natLitSupported env = true) :
    Expr.arOk env (.const natName []) = true ∧ Expr.arOk env (.const natZeroName []) = true ∧
      Expr.arOk env (.const natSuccName []) = true := by
  simp only [natLitSupported, Bool.and_eq_true] at hs
  obtain ⟨⟨h1, h2⟩, h3⟩ := hs
  exact ⟨arOk_const_of_guard natIndOk_len h1, arOk_const_of_guard natZeroOk_len h2,
    arOk_const_of_guard natSuccOk_len h3⟩

theorem arOk_natLitToConstructor (hs : natLitSupported env = true) (n : Nat) :
    Expr.arOk env (natLitToConstructor n : Expr md) = true := by
  obtain ⟨-, hz, hsu⟩ := natLit_arOk hs
  cases n with
  | zero => exact hz
  | succ k => exact arOk_app.mpr ⟨hsu, rfl⟩

theorem strLit_arOk (hs : strLitSupported env = true) :
    Expr.arOk env (.const stringName []) = true ∧
      ∀ s : String, Expr.arOk env (strLitToConstructor s : Expr md) = true := by
  simp only [strLitSupported, Bool.and_eq_true] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨_, h1⟩, h2⟩, _⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hs
  have hstr : Expr.arOk env (.const stringName []) = true :=
    arOk_const_of_guard (anyEmpty_len stringTyOk_empty) h1
  have hofl : Expr.arOk env (.const stringOfListName []) = true :=
    arOk_const_of_guard (anyEmpty_len stringOfListTyOk_empty) h2
  have hnil : Expr.arOk env (.const listNilName [Level.zero]) = true :=
    arOk_const_of_guard listNilTyOk_len h4
  have hcons : Expr.arOk env (.const listConsName [Level.zero]) = true :=
    arOk_const_of_guard listConsTyOk_len h5
  have hchar : Expr.arOk env (.const charName []) = true :=
    arOk_const_of_guard (anyEmpty_len charTyOk_empty) h6
  have hofn : Expr.arOk env (.const charOfNatName []) = true :=
    arOk_const_of_guard (anyEmpty_len charOfNatTyOk_empty) h7
  refine ⟨hstr, fun s => ?_⟩
  unfold strLitToConstructor
  refine arOk_app.mpr ⟨hofl, ?_⟩
  generalize s.toList = l
  induction l with
  | nil => exact arOk_app.mpr ⟨hnil, hchar⟩
  | cons c cs ih =>
    simp only [List.foldr]
    exact arOk_app.mpr ⟨arOk_app.mpr ⟨arOk_app.mpr ⟨hcons, hchar⟩, arOk_app.mpr ⟨hofn, rfl⟩⟩, ih⟩

theorem natAdd_arOk (ht : natAddTyOk (env.find? natAddName) = true) :
    Expr.arOk env (.const natAddName []) = true :=
  arOk_const_of_guard natAddTyOk_len ht

theorem arOk_natAddLit (ht : natAddTyOk (env.find? natAddName) = true) {b : Expr md}
    (hb : Expr.arOk env b = true) (k : Nat) : Expr.arOk env (natAddLit b k) = true := by
  unfold natAddLit
  split
  · exact hb
  · exact arOk_app.mpr ⟨arOk_app.mpr ⟨natAdd_arOk ht, hb⟩, rfl⟩

theorem arOk_natOpResult (hA : StoreAr env) {c : Key md} {a b : Nat} {r : Expr md}
    (hst : natOpStored env c = true) (h : natOpResult c a b = some r) :
    Expr.arOk env r = true := by
  have hlit : ∀ n : Nat, Expr.arOk env (.lit (.natVal n) : Expr md) = true := fun _ => rfl
  have hall : (natOpResult c a b).all (Expr.arOk env) = true := by
    unfold natOpResult
    by_cases hcb : c = natBeqName ∨ c = natBleName
    · have hT : Expr.arOk env (.const boolTrueName []) = true :=
        arOk_const_nil (fun ci hf => hA.bool hst hcb (.inl rfl) hf)
      have hF : Expr.arOk env (.const boolFalseName []) = true :=
        arOk_const_nil (fun ci hf => hA.bool hst hcb (.inr rfl) hf)
      simp [apply_ite (Option.all (Expr.arOk env)), hlit,
        apply_ite (fun n : Key md => Expr.arOk env (.const n [])), hT, hF]
    · have h1 : ¬ c = natBeqName := fun e => hcb (.inl e)
      have h2 : ¬ c = natBleName := fun e => hcb (.inr e)
      simp [apply_ite (Option.all (Expr.arOk env)), hlit, h1, h2]
  rw [h] at hall
  simpa using hall

end Guards

/-! ## Stored data under the renaming -/

section Store

variable {env : Env md} {ks : List LevelParam} {ws : List Level}

theorem LvRen.unfold (h : LvRen env ks ws) {e e' : Expr md}
    (hu : unfoldDefinition env e = some e') (he : Expr.arOk env e = true) :
    unfoldDefinition env (e.instantiateLevelParams ks ws) =
      some (e'.instantiateLevelParams ks ws) ∧ Expr.arOk env e' = true := by
  unfold unfoldDefinition at hu ⊢
  split at hu
  · rename_i n us hfn
    cases hf : env.find? n with
    | none => rw [hf] at hu; exact nomatch hu
    | some c =>
      rw [hf] at hu
      cases c with
      | defnInfo cv value hint =>
        dsimp only at hu
        split at hu
        · next hlen =>
          obtain rfl := Option.some.inj hu
          refine ⟨?_, arOk_mkAppN _ (by rw [arOk_inst]; exact h.ar.defn hf)
            (arOk_getAppArgs he)⟩
          rw [inst_getAppFn_const ks ws hfn]
          dsimp only
          rw [hf]
          dsimp only
          have hlen' : (us.map (Level.subst ks ws)).length = cv.levelParams.length := by
            rw [List.length_map]; exact hlen
          rw [if_pos hlen', instantiateLevelParams_mkAppN,
            inst_comp hlen (h.lv.defn hf), Expr.getAppArgs_instantiateLevelParams]
        · exact nomatch hu
      | _ => exact nomatch hu
  · exact nomatch hu

theorem LvRen.typeAt (h : LvRen env ks ws) {sn : Key md} {i : Nat} {entry : ProjEntry md}
    (hent : env.findProj? sn i = some entry) {us : List Level}
    (hus : us.length = entry.levelParams.length) (targs : List (Expr md)) (pe : Expr md) :
    (entry.typeAt us targs pe).instantiateLevelParams ks ws =
      entry.typeAt (us.map (Level.subst ks ws)) (targs.map (·.instantiateLevelParams ks ws))
        (pe.instantiateLevelParams ks ws) := by
  unfold ProjEntry.typeAt
  rw [inst_instantiateList ks ws _ _ (Nat.le_refl _), inst_comp hus (h.lv.proj hent)]
  simp [List.map_reverse]

theorem LvRen.arOk_typeAt (h : LvRen env ks ws) {sn : Key md} {i : Nat} {entry : ProjEntry md}
    (hent : env.findProj? sn i = some entry) (us : List Level) {targs : List (Expr md)}
    {pe : Expr md} (ht : ∀ a ∈ targs, Expr.arOk env a = true) (hpe : Expr.arOk env pe = true) :
    Expr.arOk env (entry.typeAt us targs pe) = true := by
  unfold ProjEntry.typeAt
  refine arOk_instantiateList _ _ (Nat.le_refl _) (fun x hx => ?_) _ _
    (by rw [arOk_inst]; exact h.ar.proj hent)
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hpe
  · exact ht x (List.mem_reverse.mp hx)

theorem LvRen.comparands_fst (h : LvRen env ks ws) {k : Key md} {cv : ConstantVal md}
    {mI rP' : Nat} {rules : List (RecRule md)} (hf : env.find? k = some (.recInfo cv mI rP' rules))
    {rl : RecRule md} (hrl : rl ∈ rules) (hfire : rl.fire ≠ .inert) {cvj : ConstantVal md}
    {nP nF : Nat} (hc : env.find? rl.ctor = some (.ctorInfo cvj nP nF)) {us : List Level}
    (hus : us.length = cv.levelParams.length) (args args' : List (Expr md)) (rP : Nat) :
    (recFireComparands rl cv.levelParams (us.map (Level.subst ks ws)) cvj.levelParams args'
      rP).1 =
      (recFireComparands rl cv.levelParams us cvj.levelParams args rP).1.map
        (Level.subst ks ws) := by
  unfold recFireComparands
  cases hfr : rl.fire with
  | inert => exact absurd hfr hfire
  | plain =>
    dsimp only
    rw [List.map_map]
    apply List.map_congr_left
    intro p hp
    exact (subst_comp_param hus (h.lv.plain hf rl hrl hfr hc p hp)).symm
  | nested lvls pins =>
    dsimp only
    rw [List.map_map]
    apply List.map_congr_left
    intro l hl
    exact (Level.subst_subst hus (((h.lv.rhs hf rl hrl).2 lvls pins hfr).1 l hl)).symm

theorem LvRen.comparands_snd (h : LvRen env ks ws) {k : Key md} {cv : ConstantVal md}
    {mI rP' : Nat} {rules : List (RecRule md)} (hf : env.find? k = some (.recInfo cv mI rP' rules))
    {rl : RecRule md} (hrl : rl ∈ rules) {us : List Level}
    (hus : us.length = cv.levelParams.length) (cvjLps : List LevelParam)
    (args : List (Expr md)) (rP : Nat) :
    (recFireComparands rl cv.levelParams (us.map (Level.subst ks ws)) cvjLps
      (args.map (·.instantiateLevelParams ks ws)) rP).2 =
      (recFireComparands rl cv.levelParams us cvjLps args rP).2.map
        (·.instantiateLevelParams ks ws) := by
  unfold recFireComparands
  cases hfr : rl.fire with
  | nested lvls pins =>
    dsimp only
    rw [List.map_map]
    apply List.map_congr_left
    intro p hp
    simp only [Function.comp]
    rw [inst_instSpine, List.map_take,
      inst_comp hus (((h.lv.rhs hf rl hrl).2 lvls pins hfr).2 p hp)]
  | _ => dsimp only; rw [List.map_take]

theorem LvRen.arOk_comparands_snd (h : LvRen env ks ws) {k : Key md} {cv : ConstantVal md}
    {mI rP' : Nat} {rules : List (RecRule md)} (hf : env.find? k = some (.recInfo cv mI rP' rules))
    {rl : RecRule md} (hrl : rl ∈ rules) (us : List Level) (cvjLps : List LevelParam)
    {args : List (Expr md)} (hargs : ∀ a ∈ args, Expr.arOk env a = true) (rP : Nat) :
    ∀ x ∈ (recFireComparands rl cv.levelParams us cvjLps args rP).2, Expr.arOk env x = true := by
  unfold recFireComparands
  cases hfr : rl.fire with
  | nested lvls pins =>
    dsimp only
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    exact arOk_instSpine _ _ (fun y hy => hargs y (List.mem_of_mem_take hy))
      (by rw [arOk_inst]; exact (h.ar.rhs hf rl hrl).2 lvls pins hfr p hp)
  | _ =>
    dsimp only
    intro x hx
    exact hargs x (List.mem_of_mem_take hx)

end Store

/-! ## Leaves, and the arity of the terms a rule builds -/

section Arity

variable {env : Env md}

theorem leaves_app {f a : Expr md} (h : ∀ l ∈ (Expr.app f a).fvarLeaves, Expr.arOk env l.2 = true) :
    (∀ l ∈ f.fvarLeaves, Expr.arOk env l.2 = true) ∧
      (∀ l ∈ a.fvarLeaves, Expr.arOk env l.2 = true) := by
  simp only [Expr.fvarLeaves, List.mem_append] at h
  exact ⟨fun l hl => h l (.inl hl), fun l hl => h l (.inr hl)⟩

theorem leaves_forallE {ty b : Expr md} {m : BinderMeta}
    (h : ∀ l ∈ (Expr.forallE ty b m).fvarLeaves, Expr.arOk env l.2 = true) :
    (∀ l ∈ ty.fvarLeaves, Expr.arOk env l.2 = true) ∧
      (∀ l ∈ b.fvarLeaves, Expr.arOk env l.2 = true) := by
  simp only [Expr.fvarLeaves, List.mem_append] at h
  exact ⟨fun l hl => h l (.inl hl), fun l hl => h l (.inr hl)⟩

theorem leaves_lam {ty b : Expr md} {m : BinderMeta}
    (h : ∀ l ∈ (Expr.lam ty b m).fvarLeaves, Expr.arOk env l.2 = true) :
    (∀ l ∈ ty.fvarLeaves, Expr.arOk env l.2 = true) ∧
      (∀ l ∈ b.fvarLeaves, Expr.arOk env l.2 = true) := by
  simp only [Expr.fvarLeaves, List.mem_append] at h
  exact ⟨fun l hl => h l (.inl hl), fun l hl => h l (.inr hl)⟩

theorem leaves_proj {s : Key md} {i : Nat} {e : Expr md}
    (h : ∀ l ∈ (Expr.proj s i e).fvarLeaves, Expr.arOk env l.2 = true) :
    ∀ l ∈ e.fvarLeaves, Expr.arOk env l.2 = true := by
  simp only [Expr.fvarLeaves] at h
  exact h

theorem fvarLeaves_nil_of_hasFvar : ∀ {e : Expr md}, e.hasFvar = false → e.fvarLeaves = [] := by
  intro e
  induction e <;> intro h <;> simp_all [Expr.hasFvar, Expr.fvarLeaves]

/-- The leaves of a binder's body opened at a variable of its domain. -/
theorem leaves_open {ty b : Expr md} (d : Nat) (hty : Expr.arOk env ty = true)
    (hlt : ∀ l ∈ ty.fvarLeaves, Expr.arOk env l.2 = true)
    (hlb : ∀ l ∈ b.fvarLeaves, Expr.arOk env l.2 = true) :
    ∀ l ∈ (b.instantiate1 (.fvar d ty)).fvarLeaves, Expr.arOk env l.2 = true := by
  intro l hl
  rcases fvarLeaves_instantiate1 b 0 l hl with h | h
  · exact hlb l h
  · simp only [Expr.fvarLeaves, List.mem_cons] at h
    rcases h with rfl | h
    · exact hty
    · exact hlt l h

theorem arOk_bind {ty b : Expr md} {m : BinderMeta} :
    Expr.arOk env (.forallE ty b m) = true ↔ Expr.arOk env ty = true ∧ Expr.arOk env b = true := by
  simp [Expr.arOk]

theorem arOk_lam {ty b : Expr md} {m : BinderMeta} :
    Expr.arOk env (.lam ty b m) = true ↔ Expr.arOk env ty = true ∧ Expr.arOk env b = true := by
  simp [Expr.arOk]

theorem arOk_take {l : List (Expr md)} (h : ∀ a ∈ l, Expr.arOk env a = true) (n : Nat) :
    ∀ a ∈ l.take n, Expr.arOk env a = true := fun a ha => h a (List.mem_of_mem_take ha)

theorem arOk_drop {l : List (Expr md)} (h : ∀ a ∈ l, Expr.arOk env a = true) (n : Nat) :
    ∀ a ∈ l.drop n, Expr.arOk env a = true := fun a ha => h a (List.mem_of_mem_drop ha)

theorem arOk_append {l l' : List (Expr md)} (h : ∀ a ∈ l, Expr.arOk env a = true)
    (h' : ∀ a ∈ l', Expr.arOk env a = true) : ∀ a ∈ l ++ l', Expr.arOk env a = true := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · exact h a ha
  · exact h' a ha

theorem arOk_head_len {e : Expr md} {c : Key md} {us : List Level} {ci : ConstantInfo md}
    (he : Expr.arOk env e = true) (hh : e.getAppFn = .const c us) (hf : env.find? c = some ci) :
    us.length = ci.toConstantVal.levelParams.length := by
  have := arOk_getAppFn he
  rw [hh] at this
  exact arOk_const this hf

/-- The fabricated projections are arity-correct, given the projection functions' records. -/
theorem arOk_etaProjs {T : Key md} {us : List Level} {targs : List (Expr md)} {b : Expr md}
    {nF : Nat}
    (hpf : towerSlotsAll env T nF = false → ∀ j ∈ List.range nF,
      ∃ (cvp : ConstantVal md) (mI rP : Nat) (rules : List (RecRule md)),
        env.find? (projFnName T j) = some (.recInfo cvp mI rP rules) ∧
          cvp.levelParams.length = us.length)
    (ht : ∀ a ∈ targs, Expr.arOk env a = true) (hb : Expr.arOk env b = true) :
    ∀ x ∈ etaProjs env T us targs b nF, Expr.arOk env x = true := by
  unfold etaProjs
  by_cases hts : towerSlotsAll env T nF = true
  · simp only [hts, if_true]
    intro x hx
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
    exact hb
  · simp only [hts, Bool.false_eq_true, if_false]
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    obtain ⟨cvp, mI, rP, rules, hf, hl⟩ := hpf (by simpa using hts) j hj
    refine arOk_mkAppN _ (arOk_const_of (fun ci hci => ?_)) (arOk_append ht ?_)
    · rw [hf] at hci
      obtain rfl := Option.some.inj hci
      exact hl.symm
    · intro y hy
      rw [List.mem_singleton] at hy
      subst hy
      exact hb

end Arity

/-! ## The transport -/

section Transport

set_option hygiene false in
local notation "⌜" e "⌝" => Expr.instantiateLevelParams ks ws e

set_option hygiene false in
local notation:50 "AR " e:max => Expr.arOk env e = true

set_option hygiene false in
local notation "LV" => (∀ l ∈ e.fvarLeaves, Expr.arOk env l.2 = true)

mutual

/-- **A reduction, renamed.** -/
theorem red_lr {env : Env md} {ks : List LevelParam} {ws : List Level} (h : LvRen env ks ws) :
    ∀ {d : Nat} {e e' : Expr md}, Red env d e e' → AR e → AR e' ∧ Red env d ⌜e⌝ ⌜e'⌝
  | _, _, _, .refl, he => ⟨he, .refl⟩
  | _, _, _, .trans h₁ h₂, he => by
    have r₁ := red_lr h h₁ he
    have r₂ := red_lr h h₂ r₁.1
    exact ⟨r₂.1, .trans r₁.2 r₂.2⟩
  | _, _, _, .appFn hf, he => by
    obtain ⟨hf', ha⟩ := arOk_app.mp he
    have r := red_lr h hf hf'
    exact ⟨arOk_app.mpr ⟨r.1, ha⟩, .appFn r.2⟩
  | _, _, _, .projArg hr, he => by
    have r := red_lr h hr he
    exact ⟨r.1, .projArg r.2⟩
  | _, _, _, .appArg hr, he => by
    obtain ⟨hf, ha⟩ := arOk_app.mp he
    have r := red_lr h hr ha
    exact ⟨arOk_app.mpr ⟨hf, r.1⟩, .appArg r.2⟩
  | _, _, _, .betaGate (ty := ty) (body := body) (a := a) hnev, he => by
    obtain ⟨hl, ha⟩ := arOk_app.mp he
    obtain ⟨-, hb⟩ := arOk_lam.mp hl
    refine ⟨arOk_instantiate1 ha body 0 hb, ?_⟩
    rw [inst_instantiate1]
    exact .betaGate (isNever_substPW hnev)
  | _, _, _, .beta (ty := ty) (body := body) (a := a) hta hd', he => by
    obtain ⟨hl, ha⟩ := arOk_app.mp he
    obtain ⟨hty, hb⟩ := arOk_lam.mp hl
    have i₁ := infer_lr h hta (arOk_fvarLeaves ha) (fun _ => ha)
    refine ⟨arOk_instantiate1 ha body 0 hb, ?_⟩
    rw [inst_instantiate1]
    exact .beta i₁.2.2 (defEq_lr h hd' i₁.2.1 hty)
  | _, _, _, .delta hu, he => by
    obtain ⟨hu', ha⟩ := h.unfold hu he
    exact ⟨ha, .delta hu'⟩
  | _, _, _, .deltaThm (us := us) (cv := cv) (value := value) hf hlen hvf hvb hinf hde hinfT
      hred hz, _ => by
    refine ⟨by rw [arOk_inst]; exact h.ar.thm hf, ?_⟩
    rw [inst_comp hlen (h.lv.thm hf)]
    exact .deltaThm hf (by rw [List.length_map]; exact hlen) hvf hvb hinf hde hinfT hred hz
  | _, _, _, .eqProof (a := a) (b := b) (p := p) hhead hfE hp hwp hbp hlp ha hda hb hdb hTT hred
      hv, he => by
    have hla := arOk_fvarLeaves he
    have ip := infer_lr h hp (fun l hl => hla l (hlp l hl)) (fun hg => nomatch hg)
    obtain ⟨hEqT, hb'⟩ := arOk_app.mp ip.2.1
    obtain ⟨hEqT', -⟩ := arOk_app.mp hEqT
    obtain ⟨-, hT⟩ := arOk_app.mp hEqT'
    have ia := infer_lr h ha hla (fun hg => nomatch hg)
    have ib := infer_lr h hb (arOk_fvarLeaves hb') (fun hg => nomatch hg)
    have iT := infer_lr h hTT (arOk_fvarLeaves hT) (fun hg => nomatch hg)
    refine ⟨hb', .eqProof (inst_getAppFn_const ks ws hhead) hfE ip.2.2
      (by rw [wscopedB_inst]; exact hwp)
      (by rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact hbp)
      (fvarLeaves_sub_inst ks ws hlp) ia.2.2 (defEq_lr h hda ia.2.1 hT) ib.2.2
      (defEq_lr h hdb ib.2.1 hT) iT.2.2 (red_lr h hred iT.2.1).2 ?_⟩
    intro φ
    rw [Level.eval_subst, Level.eval_subst]
    exact hv _
  | _, _, _, .natLit (n := n) hs, _ => by
    refine ⟨arOk_natLitToConstructor hs n, ?_⟩
    rw [natLitToConstructor_inst]
    exact .natLit hs
  | _, _, _, .natZeroLit hs, _ => ⟨rfl, .natZeroLit hs⟩
  | _, _, _, .strLit (s := s) hs, _ => by
    refine ⟨(strLit_arOk hs).2 s, ?_⟩
    rw [strLitToConstructor_inst]
    exact .strLit hs
  | _, _, _, .natSucc hsup hw hn, he => by
    obtain ⟨-, ha⟩ := arOk_app.mp he
    have r := red_lr h hw ha
    exact ⟨rfl, .natSucc hsup r.2 (by rw [rawNatLit?_inst]; exact hn)⟩
  | _, _, _, .natOp hc hst hwa hn₁ hwb hn₂ hr, he => by
    obtain ⟨hfa, hb⟩ := arOk_app.mp he
    obtain ⟨-, ha⟩ := arOk_app.mp hfa
    have ra := red_lr h hwa ha
    have rb := red_lr h hwb hb
    refine ⟨arOk_natOpResult h.ar hst hr, ?_⟩
    rw [natOpResult_inst ks ws hr]
    exact .natOp hc hst ra.2 (by rw [rawNatLit?_inst]; exact hn₁) rb.2
      (by rw [rawNatLit?_inst]; exact hn₂) hr
  | _, _, _, .natAddSucc (us := us) (b := b) (k := k) hs ht, he => by
    obtain ⟨hfa, -⟩ := arOk_app.mp he
    obtain ⟨-, hb⟩ := arOk_app.mp hfa
    refine ⟨arOk_app.mpr ⟨(natLit_arOk hs).2.2, arOk_natAddLit ht hb k⟩, ?_⟩
    show Red _ _ (.app (.app (.const natAddName (us.map (Level.subst ks ws))) ⌜b⌝)
      (.lit (.natVal (k + 1)))) (.app (.const natSuccName []) ⌜natAddLit b k⌝)
    rw [natAddLit_inst]
    exact .natAddSucc hs ht
  | _, _, _, .natAddZero hs ht hw hn, he => by
    obtain ⟨hfa, ha⟩ := arOk_app.mp he
    obtain ⟨-, hb⟩ := arOk_app.mp hfa
    have r := red_lr h hw ha
    exact ⟨hb, .natAddZero hs ht r.2 (by rw [rawNatLit?_inst]; exact hn)⟩
  | _, _, _, .proj (e := e) (us := us) (cvC := cvC) hent hhead hi hlen hus hfire hctor hcerts,
      he₀ => by
    have he : AR e := he₀
    have hargs := arOk_getAppArgs he
    have hlenC : us.length = cvC.levelParams.length := arOk_head_len he hhead hctor
    have hlvC : cvC.type.allLevelParamsDefined cvC.levelParams = true := h.lv.type hctor
    have hT : AR (cvC.type.instantiateLevelParams cvC.levelParams us) := by
      rw [arOk_inst]; exact h.ar.type hctor
    have hc := certs_lr h hcerts hT hargs
    rw [inst_comp hlenC hlvC, ← Expr.getAppArgs_instantiateLevelParams] at hc
    refine ⟨arOk_getD hargs _, ?_⟩
    rw [← getD_map_inst, ← Expr.getAppArgs_instantiateLevelParams]
    exact .proj hent (inst_getAppFn_const ks ws hhead) hi
      (by rw [Expr.getAppArgs_instantiateLevelParams, List.length_map]; exact hlen)
      (by rw [List.length_map]; exact hus) (fireSem_ren h.ren ks hfire) hctor hc
  | _, _, _, .iota (e := e) (us := us) (cv := cv) (rP := rP) (rules := rules)
      (major := major) (cj := cj) (usj := usj) (cvj := cvj) (cnP := cnP) (cnF := cnF) (rl := rl)
      hhead hrec hlen hus hmajor hmhead hctor hrule hmlen hfire hlv hparams hcertR hcertC hres
      hidx, he => by
    have hrl : rl ∈ rules := List.mem_of_find?_eq_some hrule
    have hargs := arOk_getAppArgs he
    have rmaj := red_lr h hmajor (arOk_getD hargs _)
    have hmargs := arOk_getAppArgs rmaj.1
    have husj : usj.length = cvj.levelParams.length := arOk_head_len rmaj.1 hmhead hctor
    have hlvj : cvj.type.allLevelParamsDefined cvj.levelParams = true := h.lv.type hctor
    have hlvR : cv.type.allLevelParamsDefined cv.levelParams = true := h.lv.type hrec
    refine ⟨arOk_mkAppN _ (by rw [arOk_inst]; exact (h.ar.rhs hrec rl hrl).1)
      (arOk_append (arOk_take hargs _) (arOk_drop hmargs _)), ?_⟩
    have hgoal : (Expr.mkAppN (rl.rhs.instantiateLevelParams cv.levelParams us)
        (e.getAppArgs.take rP ++ major.getAppArgs.drop rl.ctorParams)).instantiateLevelParams
          ks ws =
        Expr.mkAppN (rl.rhs.instantiateLevelParams cv.levelParams (us.map (Level.subst ks ws)))
          ((⌜e⌝).getAppArgs.take rP ++ (⌜major⌝).getAppArgs.drop rl.ctorParams) := by
      rw [instantiateLevelParams_mkAppN, inst_comp hus (h.lv.rhs hrec rl hrl).1,
        Expr.getAppArgs_instantiateLevelParams, Expr.getAppArgs_instantiateLevelParams,
        List.map_append, List.map_take, List.map_drop]
    rw [hgoal]
    have hmaj := rmaj.2
    rw [← getD_map_inst, ← Expr.getAppArgs_instantiateLevelParams] at hmaj
    have hTR : AR (cv.type.instantiateLevelParams cv.levelParams us) := by
      rw [arOk_inst]; exact h.ar.type hrec
    have hcR := certs_lr h hcertR hTR
      (arOk_append (arOk_take hargs _) (fun x hx => by
        rw [List.mem_singleton] at hx; subst hx; exact rmaj.1))
    rw [inst_comp hus hlvR, List.map_append, List.map_take,
      ← Expr.getAppArgs_instantiateLevelParams] at hcR
    have hTC : AR (cvj.type.instantiateLevelParams cvj.levelParams usj) := by
      rw [arOk_inst]; exact h.ar.type hctor
    have hcC := certs_lr h hcertC hTC hmargs
    rw [inst_comp husj hlvj, ← Expr.getAppArgs_instantiateLevelParams] at hcC
    exact .iota (inst_getAppFn_const ks ws hhead) hrec
      (by rw [Expr.getAppArgs_instantiateLevelParams, List.length_map]; exact hlen)
      (by rw [List.length_map]; exact hus) hmaj
      (inst_getAppFn_const ks ws hmhead) hctor hrule
      (by rw [Expr.getAppArgs_instantiateLevelParams, List.length_map]; exact hmlen) hfire
      (by
        intro φ
        have hrc : rl.ctor = cj := by simpa using List.find?_some hrule
        have hctor' : env.find? rl.ctor = some (.ctorInfo cvj cnP cnF) := by
          rw [hrc]; exact hctor
        rw [h.comparands_fst hrec hrl hfire hctor' hus e.getAppArgs]
        exact Level.evalEqList_subst ks ws φ (hlv _))
      (fun hc => by
        have hd := defEqList_lr h (hparams hc) (arOk_take hmargs _)
          (h.arOk_comparands_snd hrec hrl us cvj.levelParams hargs rP)
        rw [List.map_take, ← Expr.getAppArgs_instantiateLevelParams,
          ← h.comparands_snd hrec hrl hus, ← Expr.getAppArgs_instantiateLevelParams] at hd
        exact hd)
      hcR hcC
      (fun hne => by
        have hp := piResidual_inst ks ws _ _ _ (hres hne)
        rw [inst_comp husj hlvj, ← Expr.getAppArgs_instantiateLevelParams] at hp
        exact hp)
      (fun hne => by
        have hrs := arOk_piResidual _ (hres hne) hTC hmargs
        have hd := defEqList_lr h (hidx hne) (arOk_drop (arOk_getAppArgs hrs) _)
          (arOk_drop (arOk_take hargs _) _)
        rw [List.map_drop, List.map_drop, List.map_take, ← Expr.getAppArgs_instantiateLevelParams,
          ← Expr.getAppArgs_instantiateLevelParams] at hd
        exact hd)
  | _, _, _, .rescueK (major := major) (tmaj := tmaj) (fab := fab) (cvj := cvj) (rl := rl)
      (ust := ust)
      hrec hk hctor hres hind htm htmaj hthead hlv hnP hfab hws hb hlv' hcerts htf hdt hpi,
      he => by
    have itm := infer_lr h htm (arOk_fvarLeaves he) (fun _ => he)
    have rtm := red_lr h htmaj itm.2.1
    have htargs := arOk_getAppArgs rtm.1
    have hfab' : AR fab := by
      rw [hfab]
      exact arOk_mkAppN _ (arOk_const_of (fun ci hci => by
        rw [hctor] at hci; obtain rfl := Option.some.inj hci; exact hlv.symm))
        (arOk_take htargs _)
    have itf := infer_lr h htf (arOk_fvarLeaves hfab') (fun _ => hfab')
    have hT : AR (cvj.type.instantiateLevelParams cvj.levelParams ust) := by
      rw [arOk_inst]; exact h.ar.type hctor
    have hcs := certs_lr h hcerts hT (arOk_take htargs _)
    rw [inst_comp hlv.symm (show cvj.type.allLevelParamsDefined cvj.levelParams = true from h.lv.type hctor), List.map_take,
      ← Expr.getAppArgs_instantiateLevelParams] at hcs
    refine ⟨hfab', .rescueK hrec hk hctor hres hind itm.2.2 rtm.2
      (inst_getAppFn_const ks ws hthead) (by rw [List.length_map]; exact hlv)
      (by rw [Expr.getAppArgs_instantiateLevelParams, List.length_map]; exact hnP)
      (by rw [hfab, instantiateLevelParams_mkAppN, Expr.getAppArgs_instantiateLevelParams,
            List.map_take]; rfl)
      (by rw [wscopedB_inst]; exact hws)
      (by rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact hb)
      (fvarLeaves_all_inst ks ws hlv') hcs itf.2.2 (defEq_lr h hdt rtm.1 itf.2.1)
      (defEq_lr h hpi hfab' he)⟩
  | d, _, _, .rescueEta (major := major) (tmaj := tmaj) (fab := fab) (cvj := cvj) (rl := rl)
      (T := T) (ust := ust) (cvT := cvT) (caps := caps) hrec heta hctor hres hind htm htmaj
      hthead hlen hlv hnz hfab hws hb hlv' hcerts hproj hpi, he => by
    have itm := infer_lr h htm (arOk_fvarLeaves he) (fun _ => he)
    have rtm := red_lr h htmaj itm.2.1
    have htargs := arOk_getAppArgs rtm.1
    have hlps := h.lv.eta hrec heta hctor hres hind
    have hpc : towerSlotsAll env T caps.etaFields = false →
        (∀ j ∈ List.range caps.etaFields,
          ∃ (cvp : ConstantVal md) (mI rP : Nat) (rules : List (RecRule md)),
            env.find? (projFnName T j) = some (.recInfo cvp mI rP rules) ∧
              cvp.levelParams = cvT.levelParams) ∧
          EtaProjCerts env d T (ust.map (Level.subst ks ws))
            (tmaj.getAppArgs.map (·.instantiateLevelParams ks ws)) ⌜major⌝ cvT.levelParams
            (List.range caps.etaFields) :=
      fun hno => etaProjCerts_lr h (hproj hno) hlv htargs he
    have hfa : ∀ x ∈ etaFabArgsE env T ust tmaj.getAppArgs major caps.etaFields, AR x := by
      unfold etaFabArgsE
      refine arOk_append htargs (arOk_etaProjs (fun hno j hj => ?_) htargs he)
      obtain ⟨cvp, mI, rP, rules, hf, hl⟩ := (hpc hno).1 j hj
      exact ⟨cvp, mI, rP, rules, hf, by rw [hl, hlv]⟩
    have hlj : ust.length = cvj.levelParams.length := by rw [hlps]; exact hlv
    have hfab' : AR fab := by
      rw [hfab]
      exact arOk_mkAppN _ (arOk_const_of (fun ci hci => by
        rw [hctor] at hci; obtain rfl := Option.some.inj hci; exact hlj))
        hfa
    have hargs := etaFabArgsE_inst ks ws env T ust tmaj.getAppArgs major caps.etaFields
    rw [← Expr.getAppArgs_instantiateLevelParams] at hargs
    have hT : AR (cvj.type.instantiateLevelParams cvj.levelParams ust) := by
      rw [arOk_inst]; exact h.ar.type hctor
    have hcs := certs_lr h hcerts hT hfa
    rw [inst_comp hlj (show cvj.type.allLevelParamsDefined cvj.levelParams = true from h.lv.type hctor), hargs] at hcs
    refine ⟨hfab', .rescueEta hrec heta hctor hres hind itm.2.2 rtm.2
      (inst_getAppFn_const ks ws hthead)
      (by rw [Expr.getAppArgs_instantiateLevelParams, List.length_map]; exact hlen)
      (by rw [List.length_map]; exact hlv) (capsNeverZero_ren h.ren ks hnz)
      (by rw [hfab, instantiateLevelParams_mkAppN, hargs]; rfl)
      (by rw [wscopedB_inst]; exact hws)
      (by rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact hb)
      (fvarLeaves_all_inst ks ws hlv') hcs
      (fun hno => by
        have hp := (hpc hno).2
        rw [← Expr.getAppArgs_instantiateLevelParams] at hp
        exact hp)
      (defEq_lr h hpi hfab' he)⟩
  | _, _, _, .rescueAnd (major := major) (tmaj := tmaj) (fab := fab) (cvj := cvj) (rl := rl)
      (ust := ust)
      hrec hctor hres hind htm htmaj hthead hlen hlv hslots hfab hws hb hlv' hcerts htf hdt hpi,
      he => by
    have itm := infer_lr h htm (arOk_fvarLeaves he) (fun _ => he)
    have rtm := red_lr h htmaj itm.2.1
    have htargs := arOk_getAppArgs rtm.1
    have hfa : ∀ x ∈ tmaj.getAppArgs ++ [Expr.proj andName 0 major, Expr.proj andName 1 major],
        AR x := by
      refine arOk_append htargs (fun x hx => ?_)
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl <;> exact he
    have hfab' : AR fab := by
      rw [hfab]
      exact arOk_mkAppN _ (arOk_const_of (fun ci hci => by
        rw [hctor] at hci; obtain rfl := Option.some.inj hci; exact hlv.symm)) hfa
    have itf := infer_lr h htf (arOk_fvarLeaves hfab') (fun _ => hfab')
    have hargs :
        (tmaj.getAppArgs ++ [Expr.proj andName 0 major, Expr.proj andName 1 major]).map
          (·.instantiateLevelParams ks ws) =
        (⌜tmaj⌝).getAppArgs ++ [Expr.proj andName 0 ⌜major⌝, Expr.proj andName 1 ⌜major⌝] := by
      rw [List.map_append, Expr.getAppArgs_instantiateLevelParams]
      rfl
    have hT : AR (cvj.type.instantiateLevelParams cvj.levelParams ust) := by
      rw [arOk_inst]; exact h.ar.type hctor
    have hcs := certs_lr h hcerts hT hfa
    rw [inst_comp hlv.symm (show cvj.type.allLevelParamsDefined cvj.levelParams = true from h.lv.type hctor), hargs] at hcs
    refine ⟨hfab', .rescueAnd hrec hctor hres hind itm.2.2 rtm.2
      (inst_getAppFn_const ks ws hthead)
      (by rw [Expr.getAppArgs_instantiateLevelParams, List.length_map]; exact hlen)
      (by rw [List.length_map]; exact hlv)
      (fun j hj => by
        obtain ⟨e, hfe, hct, hnP, hnF, hfire⟩ := hslots j hj
        exact ⟨e, hfe, hct, hnP, hnF, fireSem_ren h.ren ks hfire⟩)
      (by rw [hfab, instantiateLevelParams_mkAppN, hargs]; rfl)
      (by rw [wscopedB_inst]; exact hws)
      (by rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact hb)
      (fvarLeaves_all_inst ks ws hlv') hcs itf.2.2 (defEq_lr h hdt rtm.1 itf.2.1)
      (defEq_lr h hpi hfab' he)⟩

/-- **A conversion, renamed.** -/
theorem defEq_lr {env : Env md} {ks : List LevelParam} {ws : List Level} (h : LvRen env ks ws) :
    ∀ {d : Nat} {a b : Expr md}, DefEq env d a b → AR a → AR b → DefEq env d ⌜a⌝ ⌜b⌝
  | _, _, _, .refl, _, _ => .refl
  | _, _, _, .symm hd, ha, hb => .symm (defEq_lr h hd hb ha)
  | _, _, _, .redL hr hd, ha, hb => by
    have r := red_lr h hr ha
    exact .redL r.2 (defEq_lr h hd r.1 hb)
  | _, _, _, .sort hu, _, _ => .sort (fun φ => by
      rw [Level.eval_subst, Level.eval_subst]; exact hu _)
  | _, _, _, .fvar, _, _ => .fvar
  | _, _, _, .const hus, _, _ => .const (fun φ => Level.evalEqList_subst ks ws φ (hus _))
  | _, _, _, .natZero, _, _ => .natZero
  | _, _, _, .natSucc hd, ha, hb =>
    .natSucc (defEq_lr h hd ha (arOk_app.mp hb).2)
  | _, _, _, .natOffset (a := a) (b := b) (ba := ba) (bb := bb) (k := k) hs ht hoa hob hd, ha,
      hb => by
    have hba := arOk_natOffsetOf_base hoa ha
    have hbb := arOk_natOffsetOf_base hob hb
    exact .natOffset (ba := ⌜ba⌝) (bb := ⌜bb⌝) (k := k) hs
      (fun h' => ht (by rwa [natOffsetAdd_inst, natOffsetAdd_inst] at h'))
      (by rw [natOffsetOf_inst, hoa]; rfl) (by rw [natOffsetOf_inst, hob]; rfl)
      (defEq_lr h hd hba hbb)
  | d, _, _, .forallE (ty₁ := ty₁) (body₁ := body₁) (ty₂ := ty₂) (body₂ := body₂) hty hbody hpw,
      ha, hb => by
    obtain ⟨hty₁, hb₁⟩ := arOk_bind.mp ha
    obtain ⟨hty₂, hb₂⟩ := arOk_bind.mp hb
    have h2 := defEq_lr h hbody (arOk_instantiate1 (v := .fvar d ty₂) hty₂ body₁ 0 hb₁)
      (arOk_instantiate1 (v := .fvar d ty₂) hty₂ body₂ 0 hb₂)
    rw [inst_instantiate1, inst_instantiate1] at h2
    exact .forallE (defEq_lr h hty hty₁ hty₂) h2 (congrArg (Level.substPW ks ws) hpw)
  | d, _, _, .lam (ty₁ := ty₁) (body₁ := body₁) (ty₂ := ty₂) (body₂ := body₂) hty hbody hpw,
      ha, hb => by
    obtain ⟨hty₁, hb₁⟩ := arOk_lam.mp ha
    obtain ⟨hty₂, hb₂⟩ := arOk_lam.mp hb
    have h2 := defEq_lr h hbody (arOk_instantiate1 (v := .fvar d ty₂) hty₂ body₁ 0 hb₁)
      (arOk_instantiate1 (v := .fvar d ty₂) hty₂ body₂ 0 hb₂)
    rw [inst_instantiate1, inst_instantiate1] at h2
    exact .lam (defEq_lr h hty hty₁ hty₂) h2 (congrArg (Level.substPW ks ws) hpw)
  | _, _, _, .app hf ha', ha, hb =>
    .app (defEq_lr h hf (arOk_app.mp ha).1 (arOk_app.mp hb).1)
      (defEq_lr h ha' (arOk_app.mp ha).2 (arOk_app.mp hb).2)
  | _, _, _, .proj hd, ha, hb => .proj (defEq_lr h hd ha hb)
  | d, _, _, .eta (b := b) (ty₁ := ty₁) (body₁ := body₁) htb hwtb hty hbody hpw, ha, hb => by
    obtain ⟨hty₁, hb₁⟩ := arOk_lam.mp ha
    have itb := infer_lr h htb (arOk_fvarLeaves hb) (fun _ => hb)
    have rtb := red_lr h hwtb itb.2.1
    obtain ⟨hty₂, -⟩ := arOk_bind.mp rtb.1
    have h2 := defEq_lr h hbody (arOk_instantiate1 (v := .fvar d ty₁) hty₁ body₁ 0 hb₁)
      (arOk_app.mpr ⟨hb, hty₁⟩)
    rw [inst_instantiate1] at h2
    exact .eta itb.2.2 rtb.2 (defEq_lr h hty hty₂ hty₁) h2 (congrArg (Level.substPW ks ws) hpw)
  | _, _, _, .proofFast h₁ h₂, _, _ =>
    .proofFast (by rw [isProofFast_inst h.ren]; exact h₁) (by rw [isProofFast_inst h.ren]; exact h₂)
  | _, _, _, .proofIrrel hta htta hu hu0 htb httb hv hv0, ha, hb => by
    have ita := infer_lr h hta (arOk_fvarLeaves ha) (fun _ => ha)
    have itta := infer_lr h htta (arOk_fvarLeaves ita.2.1) (fun _ => ita.2.1)
    have itb := infer_lr h htb (arOk_fvarLeaves hb) (fun _ => hb)
    have ittb := infer_lr h httb (arOk_fvarLeaves itb.2.1) (fun _ => itb.2.1)
    exact .proofIrrel ita.2.2 itta.2.2 (red_lr h hu itta.2.1).2
      (fun φ => by rw [Level.eval_subst]; exact hu0 _) itb.2.2 ittb.2.2 (red_lr h hv ittb.2.1).2
      (fun φ => by rw [Level.eval_subst]; exact hv0 _)
  | _, _, _, .unitLike hta hwta hua htb hwtb hub, ha, hb => by
    have ita := infer_lr h hta (arOk_fvarLeaves ha) (fun _ => ha)
    have itb := infer_lr h htb (arOk_fvarLeaves hb) (fun _ => hb)
    exact .unitLike ita.2.2 (red_lr h hwta ita.2.1).2 (by rw [isUnitLikeTy_inst]; exact hua)
      itb.2.2 (red_lr h hwtb itb.2.1).2 (by rw [isUnitLikeTy_inst]; exact hub)
  | d, _, _, .structEta (a := a) (b := b) (wtb := wtb) (cvT := cvT) (caps := caps) (T := T)
      (us' := us') htb hwtb hhead hctor hlen hthead hind heta hetaCtor hresT hresc htlen hlv
      hlps hslots hus hcerts hproj hparams hfields, ha, hb => by
    have itb := infer_lr h htb (arOk_fvarLeaves hb) (fun _ => hb)
    have rtb := red_lr h hwtb itb.2.1
    have hwargs := arOk_getAppArgs rtb.1
    have haargs := arOk_getAppArgs ha
    have hpc : towerSlotsAll env T caps.etaFields = false →
        (∀ j ∈ List.range caps.etaFields,
          ∃ (cvp : ConstantVal md) (mI rP : Nat) (rules : List (RecRule md)),
            env.find? (projFnName T j) = some (.recInfo cvp mI rP rules) ∧
              cvp.levelParams = cvT.levelParams) ∧
          EtaProjCerts env d T (us'.map (Level.subst ks ws))
            (wtb.getAppArgs.map (·.instantiateLevelParams ks ws)) ⌜b⌝ cvT.levelParams
            (List.range caps.etaFields) :=
      fun hno => etaProjCerts_lr h (hproj hno) hlv hwargs hb
    have hep := arOk_etaProjs (us := us') (fun hno j hj => by
      obtain ⟨cvp, mI, rP, rules, hf, hl⟩ := (hpc hno).1 j hj
      exact ⟨cvp, mI, rP, rules, hf, by rw [hl, hlv]⟩) hwargs hb
    have hT : AR (cvT.type.instantiateLevelParams cvT.levelParams us') := by
      rw [arOk_inst]; exact h.ar.type hind
    have hcs := certs_lr h hcerts hT hwargs
    rw [inst_comp hlv (show cvT.type.allLevelParamsDefined cvT.levelParams = true from h.lv.type hind), ← Expr.getAppArgs_instantiateLevelParams] at hcs
    have hp := defEqList_lr h hparams (arOk_take haargs _) hwargs
    rw [List.map_take, ← Expr.getAppArgs_instantiateLevelParams,
      ← Expr.getAppArgs_instantiateLevelParams] at hp
    have hf := defEqList_lr h hfields (arOk_drop haargs _) hep
    rw [List.map_drop, ← Expr.getAppArgs_instantiateLevelParams, etaProjs_inst,
      ← Expr.getAppArgs_instantiateLevelParams] at hf
    exact .structEta itb.2.2 rtb.2 (inst_getAppFn_const ks ws hhead) hctor
      (by rw [Expr.getAppArgs_instantiateLevelParams, List.length_map]; exact hlen)
      (inst_getAppFn_const ks ws hthead) hind heta hetaCtor hresT hresc
      (by rw [Expr.getAppArgs_instantiateLevelParams, List.length_map]; exact htlen)
      (by rw [List.length_map]; exact hlv) hlps hslots
      (fun φ => Level.evalEqList_subst ks ws φ (hus _)) hcs
      (fun hno => by
        have hp' := (hpc hno).2
        rw [← Expr.getAppArgs_instantiateLevelParams] at hp'
        exact hp') hp hf
  | _, _, _, .structUnit (cvT := cvT) (us' := us') hta hwta hthead hind hunit hresT htlen hlv
      htb hwtb hd' hcerts, ha, hb => by
    have ita := infer_lr h hta (arOk_fvarLeaves ha) (fun _ => ha)
    have rta := red_lr h hwta ita.2.1
    have itb := infer_lr h htb (arOk_fvarLeaves hb) (fun _ => hb)
    have rtb := red_lr h hwtb itb.2.1
    have hT : AR (cvT.type.instantiateLevelParams cvT.levelParams us') := by
      rw [arOk_inst]; exact h.ar.type hind
    have hcs := certs_lr h hcerts hT (arOk_getAppArgs rta.1)
    rw [inst_comp hlv (show cvT.type.allLevelParamsDefined cvT.levelParams = true from h.lv.type hind), ← Expr.getAppArgs_instantiateLevelParams] at hcs
    exact .structUnit ita.2.2 rta.2 (inst_getAppFn_const ks ws hthead) hind hunit hresT
      (by rw [Expr.getAppArgs_instantiateLevelParams, List.length_map]; exact htlen)
      (by rw [List.length_map]; exact hlv) itb.2.2 rtb.2 (defEq_lr h hd' rta.1 rtb.1) hcs
  | _, _, _, .proofIrrelTy hta htta hu hu0 htb hd', ha, hb => by
    have ita := infer_lr h hta (arOk_fvarLeaves ha) (fun _ => ha)
    have itta := infer_lr h htta (arOk_fvarLeaves ita.2.1) (fun _ => ita.2.1)
    have itb := infer_lr h htb (arOk_fvarLeaves hb) (fun _ => hb)
    exact .proofIrrelTy ita.2.2 itta.2.2 (red_lr h hu itta.2.1).2
      (fun φ => by rw [Level.eval_subst]; exact hu0 _) itb.2.2 (defEq_lr h hd' ita.2.1 itb.2.1)
  | _, _, _, .unitLikeTy (cvT := cvT) (us := us) hta hwta hthead hind hunit htlen hcerts hkind htb
      hd', ha, hb => by
    have ita := infer_lr h hta (arOk_fvarLeaves ha) (fun _ => ha)
    have rta := red_lr h hwta ita.2.1
    have itb := infer_lr h htb (arOk_fvarLeaves hb) (fun _ => hb)
    have hlenT : us.length = cvT.levelParams.length := arOk_head_len rta.1 hthead hind
    have hT : AR (cvT.type.instantiateLevelParams cvT.levelParams us) := by
      rw [arOk_inst]; exact h.ar.type hind
    have hcs := certs_lr h hcerts hT (arOk_getAppArgs rta.1)
    rw [inst_comp hlenT (show cvT.type.allLevelParamsDefined cvT.levelParams = true from h.lv.type hind), ← Expr.getAppArgs_instantiateLevelParams] at hcs
    exact .unitLikeTy ita.2.2 rta.2 (inst_getAppFn_const ks ws hthead) hind hunit
      (by rw [Expr.getAppArgs_instantiateLevelParams, List.length_map]; exact htlen) hcs
      (hkind.imp id (fun hk => by rw [isUnitLikeTy_inst]; exact hk)) itb.2.2
      (defEq_lr h hd' ita.2.1 itb.2.1)
  | _, _, _, .structEtaTy (a := a) (b := b) (cvT := cvT) (T := T) (us := us) (cnP := cnP)
      (cnF := cnF) hhead hctor hlen hind heta hetaCtor hpos htow hta hwta hcerts htb hd' hfields,
      hb, ha => by
    have ita := infer_lr h hta (arOk_fvarLeaves ha) (fun _ => ha)
    have rta := red_lr h hwta ita.2.1
    have itb := infer_lr h htb (arOk_fvarLeaves hb) (fun _ => hb)
    have haargs := arOk_getAppArgs ha
    have hlenT : us.length = cvT.levelParams.length := by
      have := (arOk_mkAppN_inv _ rta.1).1
      exact arOk_const this hind
    have hr := rta.2
    rw [instantiateLevelParams_mkAppN, List.map_take,
      ← Expr.getAppArgs_instantiateLevelParams] at hr
    have hT : AR (cvT.type.instantiateLevelParams cvT.levelParams us) := by
      rw [arOk_inst]; exact h.ar.type hind
    have hcs := certs_lr h hcerts hT (arOk_take haargs _)
    rw [inst_comp hlenT (show cvT.type.allLevelParamsDefined cvT.levelParams = true from h.lv.type hind), List.map_take,
      ← Expr.getAppArgs_instantiateLevelParams] at hcs
    have hpl : ∀ x ∈ (List.range cnF).map (fun i => Expr.proj T i b), AR x := by
      intro x hx
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
      exact hb
    have hf := defEqList_lr h hfields hpl (arOk_drop haargs _)
    rw [List.map_map, List.map_drop, ← Expr.getAppArgs_instantiateLevelParams] at hf
    exact .structEtaTy (inst_getAppFn_const ks ws hhead) hctor
      (by rw [Expr.getAppArgs_instantiateLevelParams, List.length_map]; exact hlen) hind heta
      hetaCtor hpos htow ita.2.2 hr hcs itb.2.2 (defEq_lr h hd' itb.2.1 ita.2.1) hf

/-- **An inference, renamed.** At the full grade the subject's arity comes from the derivation,
given its annotations'. -/
theorem infer_lr {env : Env md} {ks : List LevelParam} {ws : List Level} (h : LvRen env ks ws) :
    ∀ {g : Grade} {d : Nat} {e t : Expr md}, Infer env g d e t → LV → (g = .io → AR e) →
      AR e ∧ AR t ∧ Infer env g d ⌜e⌝ ⌜t⌝
  | _, _, _, _, .sort, _, _ => ⟨rfl, rfl, .sort⟩
  | _, _, _, _, .fvar (idx := idx) (ty := ty) hi, hl, _ => by
    have hty : AR ty := hl (idx, ty) (by simp [Expr.fvarLeaves])
    exact ⟨hty, hty, .fvar hi⟩
  | _, _, _, _, .const (us := us) (ci := ci) hf htower hus, _, _ => by
    refine ⟨arOk_const_of (fun ci' hf' => by rw [hf] at hf'; cases hf'; exact hus),
      by rw [arOk_inst]; exact h.ar.type hf, ?_⟩
    rw [inst_comp hus (h.lv.type hf)]
    exact .const hf htower (by rw [List.length_map]; exact hus)
  | _, _, _, _, .natLit hs, _, _ => ⟨rfl, (natLit_arOk hs).1, .natLit hs⟩
  | _, _, _, _, .strLit hs, _, _ => ⟨rfl, (strLit_arOk hs).1, .strLit hs⟩
  | _, d, _, _, .forallE (ty := ty) (body := body) hs hu hbs hv hz, hl, hio => by
    have hl' := leaves_forallE hl
    have is := infer_lr h hs hl'.1 (fun hg => (arOk_bind.mp (hio hg)).1)
    have hbo := leaves_open d is.1 hl'.1 hl'.2
    have ibs := infer_lr h hbs hbo
      (fun hg => arOk_instantiate1 (v := .fvar d ty) is.1 body 0 (arOk_bind.mp (hio hg)).2)
    have hbody : AR body := arOk_of_instantiate1 body 0 ibs.1
    have rv := red_lr h hv ibs.2.1
    rw [inst_instantiate1] at ibs
    exact ⟨arOk_bind.mpr ⟨is.1, hbody⟩, rfl, .forallE is.2.2 (red_lr h hu is.2.1).2 ibs.2.2 rv.2
      (by rw [Level.zeronessOf_subst, hz])⟩
  | g, d, _, _, .lam (ty := ty) (body := body) (bt := bt) (mb := mb) hs hu hbt hchain hbtt hv
      hz, hl, hio => by
    have hl' := leaves_lam hl
    have hty : AR ty := by
      by_cases hgf : g = .full
      · exact (infer_lr h (hs hgf) hl'.1 (fun hg => nomatch hg)).1
      · have hgi : g = .io := by
          cases g with
          | full => exact absurd rfl hgf
          | io => rfl
        exact (arOk_lam.mp (hio hgi)).1
    have hbo := leaves_open d hty hl'.1 hl'.2
    have ibt := infer_lr h hbt hbo
      (fun hg => arOk_instantiate1 (v := .fvar d ty) hty body 0 (arOk_lam.mp (hio hg)).2)
    have hbody : AR body := arOk_of_instantiate1 body 0 ibt.1
    have hbt := ibt.2.1
    rw [inst_instantiate1] at ibt
    have habs : (Expr.forallE ty (bt.abstract1 d) mb).instantiateLevelParams ks ws =
        .forallE ⌜ty⌝ ((⌜bt⌝).abstract1 d) { mb with pw := Level.substPW ks ws mb.pw } := by
      show Expr.forallE ⌜ty⌝ ((bt.abstract1 d 0).instantiateLevelParams ks ws) _ = _
      rw [inst_abstract1]
    have hnone : (⌜body⌝).lamPw = none → body.lamPw = none := by
      intro hn
      rw [lamPw_inst] at hn
      rcases hb : body.lamPw with _ | p
      · rfl
      · rw [hb] at hn; exact nomatch hn
    refine ⟨arOk_lam.mpr ⟨hty, hbody⟩, arOk_bind.mpr ⟨hty, arOk_abstract1 d bt 0 hbt⟩, ?_⟩
    rw [habs]
    exact .lam (fun hg => (infer_lr h (hs hg) hl'.1 (fun hg' => nomatch hg')).2.2)
      (fun hg => (red_lr h (hu hg) (infer_lr h (hs hg) hl'.1
        (fun hg' => nomatch hg')).2.1).2)
      ibt.2.2
      (fun pwI hp => by
        rw [lamPw_inst] at hp
        rcases hb : body.lamPw with _ | p
        · rw [hb] at hp; exact nomatch hp
        · rw [hb] at hp
          obtain rfl := Option.some.inj hp
          exact congrArg (Level.substPW ks ws) (hchain p hb))
      (fun hn => by
        have i₂ := infer_lr h (hbtt (hnone hn)) (arOk_fvarLeaves hbt) (fun _ => hbt)
        exact i₂.2.2)
      (fun hn => by
        have i₂ := infer_lr h (hbtt (hnone hn)) (arOk_fvarLeaves hbt) (fun _ => hbt)
        exact (red_lr h (hv (hnone hn)) i₂.2.1).2)
      (fun hn => by rw [Level.zeronessOf_subst, hz (hnone hn)])
  | _, _, _, _, .app (f := f) (a := a) (body := body) htf hw hta hd', hl, hio => by
    have hl' := leaves_app hl
    have itf := infer_lr h htf hl'.1 (fun hg => (arOk_app.mp (hio hg)).1)
    have rr := red_lr h hw itf.2.1
    obtain ⟨hty, hbody⟩ := arOk_bind.mp rr.1
    have ita := infer_lr h hta hl'.2 (fun hg => (arOk_app.mp (hio hg)).2)
    refine ⟨arOk_app.mpr ⟨itf.1, ita.1⟩, arOk_instantiate1 ita.1 body 0 hbody, ?_⟩
    rw [inst_instantiate1]
    exact .app itf.2.2 rr.2 ita.2.2 (defEq_lr h hd' ita.2.1 hty)
  | _, _, _, _, .appSkip (f := f) (a := a) (body := body) htf hw hnev, hl, hio => by
    have he := hio rfl
    have hl' := leaves_app hl
    have itf := infer_lr h htf hl'.1 (fun _ => (arOk_app.mp he).1)
    have rr := red_lr h hw itf.2.1
    obtain ⟨-, hbody⟩ := arOk_bind.mp rr.1
    refine ⟨he, arOk_instantiate1 (arOk_app.mp he).2 body 0 hbody, ?_⟩
    rw [inst_instantiate1]
    exact .appSkip itf.2.2 rr.2 (isNever_substPW hnev)
  | _, _, _, _, .proj (pe := pe) (te := te) (us := us) (entry := entry) htpe hte hhead hent hlen
      hus hprop, hl, hio => by
    have ipe := infer_lr h htpe (leaves_proj hl) hio
    have rte := red_lr h hte ipe.2.1
    refine ⟨ipe.1, h.arOk_typeAt hent us (arOk_getAppArgs rte.1) ipe.1, ?_⟩
    rw [h.typeAt hent hus, ← Expr.getAppArgs_instantiateLevelParams]
    exact .proj ipe.2.2 rte.2 (inst_getAppFn_const ks ws hhead) hent
      (by rw [Expr.getAppArgs_instantiateLevelParams, List.length_map]; exact hlen)
      (by rw [List.length_map]; exact hus) (fireSem_ren h.ren ks hprop)

/-- **A telescope certificate, renamed.** -/
theorem certs_lr {env : Env md} {ks : List LevelParam} {ws : List Level} (h : LvRen env ks ws) :
    ∀ {d : Nat} {lic : Bool} {T : Expr md} {args : List (Expr md)},
      Certs env d lic T args → AR T → (∀ a ∈ args, AR a) →
        Certs env d lic ⌜T⌝ (args.map (·.instantiateLevelParams ks ws))
  | _, _, _, _, .nil, _, _ => .nil
  | _, _, _, _, .skip (body := body) (arg := arg) hlic hnev hrest, hT, ha => by
    have harg : AR arg := ha arg (by simp)
    have hr := certs_lr h hrest (arOk_instantiate1 harg body 0 (arOk_bind.mp hT).2)
      (fun x hx => ha x (List.mem_cons_of_mem _ hx))
    rw [inst_instantiate1] at hr
    exact .skip hlic (isNever_substPW hnev) hr
  | _, _, _, _, .cert (body := body) (arg := arg) hta hd' hrest, hT, ha => by
    have harg : AR arg := ha arg (by simp)
    have ita := infer_lr h hta (arOk_fvarLeaves harg) (fun _ => harg)
    have hr := certs_lr h hrest (arOk_instantiate1 harg body 0 (arOk_bind.mp hT).2)
      (fun x hx => ha x (List.mem_cons_of_mem _ hx))
    rw [inst_instantiate1] at hr
    exact .cert ita.2.2 (defEq_lr h hd' ita.2.1 (arOk_bind.mp hT).1) hr

/-- **A pairwise conversion, renamed.** -/
theorem defEqList_lr {env : Env md} {ks : List LevelParam} {ws : List Level}
    (h : LvRen env ks ws) :
    ∀ {d : Nat} {as bs : List (Expr md)}, DefEqList env d as bs →
      (∀ a ∈ as, AR a) → (∀ b ∈ bs, AR b) →
      DefEqList env d (as.map (·.instantiateLevelParams ks ws))
        (bs.map (·.instantiateLevelParams ks ws))
  | _, _, _, .nil, _, _ => .nil
  | _, _, _, .cons hd hs, ha, hb =>
    .cons (defEq_lr h hd (ha _ (by simp)) (hb _ (by simp)))
      (defEqList_lr h hs (fun x hx => ha x (List.mem_cons_of_mem _ hx))
        (fun x hx => hb x (List.mem_cons_of_mem _ hx)))

/-- **The per-field certificates of a projection-function family, renamed**, with the records
they read. -/
theorem etaProjCerts_lr {env : Env md} {ks : List LevelParam} {ws : List Level}
    (h : LvRen env ks ws) :
    ∀ {d : Nat} {T : Key md} {us' : List Level} {targs : List (Expr md)} {b : Expr md}
      {lpsT : List LevelParam} {idxs : List Nat},
      EtaProjCerts env d T us' targs b lpsT idxs → us'.length = lpsT.length →
      (∀ a ∈ targs, AR a) → AR b →
      (∀ j ∈ idxs, ∃ (cvp : ConstantVal md) (mI rP : Nat) (rules : List (RecRule md)),
          env.find? (projFnName T j) = some (.recInfo cvp mI rP rules) ∧
            cvp.levelParams = lpsT) ∧
        EtaProjCerts env d T (us'.map (Level.subst ks ws))
          (targs.map (·.instantiateLevelParams ks ws)) ⌜b⌝ lpsT idxs
  | _, _, _, _, _, _, _, .nil, _, _, _ => ⟨(fun _ hj => nomatch hj), .nil⟩
  | _, _, us', targs, b, _, _, .cons (i := i) (cvp := cvp) hf hlps hstrip hcerts hrest, hlen,
      ht, hb => by
    have hT : AR (cvp.type.instantiateLevelParams cvp.levelParams us') := by
      rw [arOk_inst]; exact h.ar.type hf
    have hc := certs_lr h hcerts hT (arOk_append ht (fun x hx => by
      rw [List.mem_singleton] at hx; subst hx; exact hb))
    have hl' : us'.length = cvp.levelParams.length := by rw [hlen, hlps]
    rw [inst_comp hl' (show cvp.type.allLevelParamsDefined cvp.levelParams = true from h.lv.type hf), List.map_append] at hc
    have ir := etaProjCerts_lr h hrest hlen ht hb
    refine ⟨fun j hj => ?_, .cons hf hlps (by rw [List.length_map]; exact hstrip) hc ir.2⟩
    rcases List.mem_cons.mp hj with rfl | hj
    · exact ⟨cvp, _, _, _, hf, hlps⟩
    · exact ir.1 j hj

end

end Transport

/-! ## Corollaries -/

theorem Infer.lvRen {env : Env md} {ks : List LevelParam} {ws : List Level} (h : LvRen env ks ws)
    {g : Grade} {d : Nat} {e t : Expr md} (hi : Infer env g d e t)
    (hl : ∀ l ∈ e.fvarLeaves, Expr.arOk env l.2 = true)
    (hio : g = .io → Expr.arOk env e = true) :
    Infer env g d (e.instantiateLevelParams ks ws) (t.instantiateLevelParams ks ws) :=
  (infer_lr h hi hl hio).2.2

/-- **A closed term's full-grade inference, renamed**: no arity hypothesis. -/
theorem Infer.lvRen_closed {env : Env md} {ks : List LevelParam} {ws : List Level}
    (h : LvRen env ks ws) {d : Nat} {e t : Expr md} (hi : Infer env .full d e t)
    (hfv : e.hasFvar = false) :
    Expr.arOk env t = true ∧
      Infer env .full d (e.instantiateLevelParams ks ws) (t.instantiateLevelParams ks ws) := by
  have hl : ∀ l ∈ e.fvarLeaves, Expr.arOk env l.2 = true := by
    intro l hl
    rw [fvarLeaves_nil_of_hasFvar hfv] at hl
    exact nomatch hl
  have r := infer_lr h hi hl (fun hg => nomatch hg)
  exact ⟨r.2.1, r.2.2⟩

theorem DefEq.lvRen {env : Env md} {ks : List LevelParam} {ws : List Level} (h : LvRen env ks ws)
    {d : Nat} {a b : Expr md} (hd : DefEq env d a b) (ha : Expr.arOk env a = true)
    (hb : Expr.arOk env b = true) :
    DefEq env d (a.instantiateLevelParams ks ws) (b.instantiateLevelParams ks ws) :=
  defEq_lr h hd ha hb

theorem Red.lvRen {env : Env md} {ks : List LevelParam} {ws : List Level} (h : LvRen env ks ws)
    {d : Nat} {e e' : Expr md} (hr : Red env d e e') (he : Expr.arOk env e = true) :
    Expr.arOk env e' = true ∧
      Red env d (e.instantiateLevelParams ks ws) (e'.instantiateLevelParams ks ws) :=
  red_lr h hr he

end Ix.Kernel.Rules
