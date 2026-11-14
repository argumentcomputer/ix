module

public import IxC.Kernel.Model.Open.Denotes
import IxC.Kernel.Verify.PropWhen
public import IxC.Kernel.Verify.StrLitExpr

@[expose] public section

/-!
# Level instantiation, at open terms

A use `c.{us}` of a stored constant reads its type and value at the level arguments:
the kernel instantiates the constant's level parameters (`Expr.instantiateLevelParams`,
which also substitutes into the binders' proposition data). Over a model whose constants
read only their own level parameters (`CvalParams`, the field `Model.cval_params`):

* `DenotesO.congr_levels`: a denotation reads the level assignment only at the levels the
  term mentions;
* `DenotesO.instantiateLevelParams`: the instantiated term denotes, at `φ`, what the term
  denotes at the assignment the instantiation induces (`Level.substFn φ ks us`).
-/

namespace Ix.Kernel

open SetTheory Ix.Kernel.SetModel

universe w

variable {V : Type w} [SetTheory V] {cval : Key md → (LevelParam → Nat) → V} {env : Env md}
  {σ : Nat → V}

/-- A constant's set reads the level assignment only at its own level parameters
(`Model.cval_params`). -/
def CvalParams (cval : Key md → (LevelParam → Nat) → V) (env : Env md) : Prop :=
  ∀ (n : Key md) (ci : ConstantInfo md), env.find? n = some ci →
    ∀ φ₁ φ₂ : LevelParam → Nat, (∀ p ∈ ci.toConstantVal.levelParams, φ₁ p = φ₂ p) →
      cval n φ₁ = cval n φ₂

theorem substFn_congr {ps : List LevelParam} {φ₁ φ₂ : LevelParam → Nat}
    (hag : ∀ p ∈ ps, φ₁ p = φ₂ p) :
    ∀ (lps : List LevelParam) (us : List Level), lps.length = us.length →
      (∀ u ∈ us, u.allParamsDefined ps = true) →
      ∀ p ∈ lps, Level.substFn φ₁ lps us p = Level.substFn φ₂ lps us p
  | [], _, _, _, p, hp => absurd hp (by simp)
  | _ :: _, [], hl, _, _, _ => absurd hl (by simp)
  | k :: lps, u :: us, hl, hus, p, hp => by
    simp only [Level.substFn]
    by_cases hk : k = p
    · rw [if_pos hk, if_pos hk]
      exact Level.eval_ext (hus u (by simp)) hag
    · rw [if_neg hk, if_neg hk]
      exact substFn_congr hag lps us (by simpa using hl) (fun v hv => hus v (by simp [hv]))
        p (by rcases List.mem_cons.mp hp with h | h
              · exact absurd h.symm hk
              · exact h)

theorem substFn_map_subst (φ : LevelParam → Nat) (ks : List LevelParam) (vs : List Level) :
    ∀ (lps : List LevelParam) (us : List Level), lps.length = us.length →
      ∀ p ∈ lps, Level.substFn φ lps (us.map (Level.subst ks vs)) p =
        Level.substFn (Level.substFn φ ks vs) lps us p
  | [], _, _, p, hp => absurd hp (by simp)
  | _ :: _, [], hl, _, _ => absurd hl (by simp)
  | k :: lps, u :: us, hl, p, hp => by
    simp only [List.map_cons, Level.substFn]
    by_cases hk : k = p
    · rw [if_pos hk, if_pos hk]
      exact Level.eval_subst φ ks vs u
    · rw [if_neg hk, if_neg hk]
      exact substFn_map_subst φ ks vs lps us (by simpa using hl) p
        (by rcases List.mem_cons.mp hp with h | h
            · exact absurd h.symm hk
            · exact h)

theorem strLitList_allLevelParamsDefined (ps : List LevelParam) :
    ∀ cs : List Char, ((strLitList (md := md)) cs).allLevelParamsDefined ps = true
  | [] => rfl
  | c :: cs => by
    (simp only [strLitList, Expr.allLevelParamsDefined, strLitList_allLevelParamsDefined ps cs])
      <;> rfl

theorem strLitToConstructor_allLevelParamsDefined (ps : List LevelParam) (s : String) :
    ((strLitToConstructor (md := md)) s).allLevelParamsDefined ps = true := by
  rw [strLitToConstructor_eq]
  (simp only [Expr.allLevelParamsDefined, strLitList_allLevelParamsDefined ps s.toList])
    <;> rfl

theorem natLitToConstructor_allLevelParamsDefined (ps : List LevelParam) (n : Nat) :
    ((natLitToConstructor (md := md)) n).allLevelParamsDefined ps = true := by
  cases n <;> rfl

/-- **A denotation reads the level assignment only at the levels the term mentions.** -/
theorem DenotesO.congr_levels (hcp : CvalParams cval env) {ps : List LevelParam}
    {φ₁ φ₂ : LevelParam → Nat} (hag : ∀ p ∈ ps, φ₁ p = φ₂ p) {ρ : BVarIdx → V}
    {e : Expr md} {v : V} (h : DenotesO cval env φ₁ σ ρ e v) :
    e.allLevelParamsDefined ps = true → DenotesO cval env φ₂ σ ρ e v := by
  induction h with
  | bvar => exact fun _ => .bvar
  | fvar => exact fun _ => .fvar
  | @sort ρ u =>
    intro hd
    rw [Level.eval_ext (by simpa [Expr.allLevelParamsDefined] using hd) hag]
    exact .sort
  | @const ρ n us ci hf hlen =>
    intro hd
    simp only [Expr.allLevelParamsDefined, List.all_eq_true] at hd
    rw [hcp n ci hf _ _ (substFn_congr hag _ us hlen.symm hd)]
    exact .const hf hlen
  | app _ _ ihf iha =>
    intro hd
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hd
    exact .app (ihf hd.1) (iha hd.2)
  | @lam ρ ty body m A F _ _ hP ihA ihF =>
    intro hd
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hd
    have hr : regime φ₁ m.pw = regime φ₂ m.pw := by
      simp only [regime, PropWhen.holds_ext hd.2 hag]
    rw [hr]
    exact .lam (ihA hd.1.1) (fun x hx => ihF x hx hd.1.2) (by rw [← hr]; exact hP)
  | @pi ρ ty body m A B _ _ hP ihA ihB =>
    intro hd
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hd
    have hr : regime φ₁ m.pw = regime φ₂ m.pw := by
      simp only [regime, PropWhen.holds_ext hd.2 hag]
    rw [hr]
    exact .pi (ihA hd.1.1) (fun x hx => ihB x hx hd.1.2) (by rw [← hr]; exact hP)
  | proj_table ht _ ih => exact fun hd => .proj_table ht (ih hd)
  | proj_fst ht _ ih => exact fun hd => .proj_fst ht (ih hd)
  | proj_snd ht _ ih => exact fun hd => .proj_snd ht (ih hd)
  | natLit _ ih => exact fun _ => .natLit (ih (natLitToConstructor_allLevelParamsDefined ps _))
  | strLit _ ih => exact fun _ => .strLit (ih (strLitToConstructor_allLevelParamsDefined ps _))

/-- **Level instantiation**: the term with its level parameters `ks` instantiated at `us`
denotes, at `φ`, what the term denotes at `Level.substFn φ ks us`. -/
theorem DenotesO.instantiateLevelParams (hcp : CvalParams cval env) {φ : LevelParam → Nat}
    (ks : List LevelParam) (us : List Level) :
    ∀ (e : Expr md) (ρ : BVarIdx → V) (v : V),
      DenotesO cval env φ σ ρ (e.instantiateLevelParams ks us) v ↔
        DenotesO cval env (Level.substFn φ ks us) σ ρ e v := by
  intro e
  induction e with
  | bvar i =>
    intro ρ v
    simp only [Expr.instantiateLevelParams]
    constructor
    · intro h; cases h; exact .bvar
    · intro h; cases h; exact .bvar
  | fvar i ty _ =>
    intro ρ v
    simp only [Expr.instantiateLevelParams]
    constructor
    · intro h; cases h; exact .fvar
    · intro h; cases h; exact .fvar
  | sort u =>
    intro ρ v
    simp only [Expr.instantiateLevelParams]
    constructor
    · intro h; cases h; rw [Level.eval_subst]; exact .sort
    · intro h; cases h; rw [← Level.eval_subst]; exact .sort
  | const n vs =>
    intro ρ v
    simp only [Expr.instantiateLevelParams]
    constructor
    · intro h
      cases h with
      | @const _ _ _ ci hf hlen =>
        have hlen' : vs.length = ci.toConstantVal.levelParams.length := by simpa using hlen
        rw [hcp n ci hf _ _ (substFn_map_subst φ ks us _ vs hlen'.symm)]
        exact .const hf hlen'
    · intro h
      cases h with
      | @const _ _ _ ci hf hlen =>
        rw [← hcp n ci hf _ _ (substFn_map_subst φ ks us _ vs hlen.symm)]
        exact .const hf (by simpa using hlen)
  | app f a ihf iha =>
    intro ρ v
    simp only [Expr.instantiateLevelParams]
    constructor
    · intro h
      cases h with
      | app hf ha => exact .app ((ihf ρ _).1 hf) ((iha ρ _).1 ha)
    · intro h
      cases h with
      | app hf ha => exact .app ((ihf ρ _).2 hf) ((iha ρ _).2 ha)
  | lam ty body m ihty ihb =>
    intro ρ v
    simp only [Expr.instantiateLevelParams]
    have hr : regime φ (Level.substPW ks us m.pw) = regime (Level.substFn φ ks us) m.pw := by
      simp only [regime, Level.holds_substPW]
    constructor
    · intro h
      cases h with
      | lam hA hF hP =>
        rw [hr]
        exact .lam ((ihty ρ _).1 hA) (fun x hx => (ihb _ _).1 (hF x hx))
          (by rw [← hr]; exact hP)
    · intro h
      cases h with
      | lam hA hF hP =>
        rw [← hr]
        exact .lam ((ihty ρ _).2 hA) (fun x hx => (ihb _ _).2 (hF x hx))
          (by rw [hr]; exact hP)
  | forallE ty body m ihty ihb =>
    intro ρ v
    simp only [Expr.instantiateLevelParams]
    have hr : regime φ (Level.substPW ks us m.pw) = regime (Level.substFn φ ks us) m.pw := by
      simp only [regime, Level.holds_substPW]
    constructor
    · intro h
      cases h with
      | pi hA hB hP =>
        rw [hr]
        exact .pi ((ihty ρ _).1 hA) (fun x hx => (ihb _ _).1 (hB x hx))
          (by rw [← hr]; exact hP)
    · intro h
      cases h with
      | pi hA hB hP =>
        rw [← hr]
        exact .pi ((ihty ρ _).2 hA) (fun x hx => (ihb _ _).2 (hB x hx))
          (by rw [hr]; exact hP)
  | letE ty val body lm _ _ _ =>
    intro ρ v
    simp only [Expr.instantiateLevelParams]
    constructor
    · intro h; cases h
    · intro h; cases h
  | lit l =>
    intro ρ v
    simp only [Expr.instantiateLevelParams]
    exact ⟨fun h => h.congr_levels hcp (ps := []) (fun _ h => absurd h (by simp)) rfl,
      fun h => h.congr_levels hcp (ps := []) (fun _ h => absurd h (by simp)) rfl⟩
  | proj s i e ih =>
    intro ρ v
    simp only [Expr.instantiateLevelParams]
    constructor
    · intro h
      cases h with
      | proj_table ht he => exact .proj_table ht ((ih ρ _).1 he)
      | proj_fst ht he => exact .proj_fst ht ((ih ρ _).1 he)
      | proj_snd ht he => exact .proj_snd ht ((ih ρ _).1 he)
    · intro h
      cases h with
      | proj_table ht he => exact .proj_table ht ((ih ρ _).2 he)
      | proj_fst ht he => exact .proj_fst ht ((ih ρ _).2 he)
      | proj_snd ht he => exact .proj_snd ht ((ih ρ _).2 he)

end Ix.Kernel
