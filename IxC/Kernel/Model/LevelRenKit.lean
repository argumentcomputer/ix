module

public import IxC.Kernel.Rules.Rel
public import IxC.Kernel.Rules.TransportKit
public import IxC.Kernel.Rules.NatOffset
public import IxC.Kernel.Verify.InstLevels
public import IxC.Kernel.Verify.PropWhen
public import IxC.Kernel.Verify.Level
public import IxC.Kernel.Verify.EnvWF
public import IxC.Kernel.Model.Open.StoredFacts

@[expose] public section

/-!
# Renaming level parameters: the kit

What the transport of the rules along a renaming of level parameters
(`Model/LevelRen.lean`) reads. The renaming is a level instantiation
`instantiateLevelParams ks ws` whose replacements are parameters (`Level.IsRen ws`).

* **Commutation.** Every helper the rules name commutes with any level instantiation: binder
  opening and closing, spines, the bulk instantiations, `piResidual`, the literal readings and
  shapes, the `Nat` offsets, the fabricated projections.
* **Semantic guards.** The rules' level side conditions are statements about every valuation.
  Those that are equalities move under any instantiation (`Level.eval_subst`). Three are
  "zero at every valuation" or "never zero" of a stored datum instantiated at the use's levels
  (`FireSem`, `isProofFast`, `capsNeverZero`): each is decided by a constant valuation (all ones,
  all zeros), and a renaming does not change a level's value there.
* **Arity.** `Expr.arOk env e`: every constant of `e` that `env` stores is applied at its own
  number of level parameters, annotations included. Three rules instantiate a stored type at a
  level list no premise measures (`DefEq.unitLikeTy`, `DefEq.structEtaTy`, `Red.iota` at a
  nested rule); at a short list the parameters left over stay, and no renaming that moves them
  commutes. Arity of the terms involved excludes that.
* **The store.** `LvStore`: stored terms mention only their constant's level parameters
  (`EnvWF`, and `ThmLevels` for a theorem's value, which `EnvWF` does not record). `StoreAr`:
  stored terms are `arOk`.
-/

namespace Ix.Kernel

/-! ## Renamings of levels -/

namespace Level

/-- **A renaming**: every replacement is a parameter. -/
def IsRen (ws : List Level) : Prop := ∀ w ∈ ws, ∃ q, w = Level.param q

theorem IsRen.tail {w : Level} {ws : List Level} (h : IsRen (w :: ws)) : IsRen ws :=
  fun v hv => h v (List.mem_cons_of_mem _ hv)

theorem IsRen.map_param (qs : List LevelParam) : IsRen (qs.map Level.param) := by
  intro w hw
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hw
  exact ⟨q, rfl⟩

/-- At a constant valuation a renaming's valuation is the same constant. -/
theorem substFn_const_of_ren (c : Nat) :
    ∀ (ks : List LevelParam) (ws : List Level), IsRen ws → ∀ n,
      substFn (fun _ => c) ks ws n = c
  | [], ws, _, n => by cases ws <;> rfl
  | _ :: _, [], _, n => rfl
  | k :: ks, w :: ws, h, n => by
    obtain ⟨q, rfl⟩ := h w (by simp)
    show (if k = n then eval (fun _ => c) (.param q) else substFn (fun _ => c) ks ws n) = c
    split
    · rfl
    · exact substFn_const_of_ren c ks ws h.tail n

/-- **A renaming keeps a level's value at a constant valuation.** -/
theorem eval_const_subst_of_ren {ws : List Level} (h : IsRen ws) (c : Nat)
    (ks : List LevelParam) (l : Level) :
    eval (fun _ => c) (subst ks ws l) = eval (fun _ => c) l := by
  rw [eval_subst]
  have : substFn (fun _ => c) ks ws = fun _ => c := funext (substFn_const_of_ren c ks ws h)
  rw [this]

/-- A stored instantiation renamed: its constant valuation is unchanged. -/
theorem substFn_const_map_ren {ws : List Level} (h : IsRen ws) (c : Nat) (ks : List LevelParam) :
    ∀ (lps : List LevelParam) (us : List Level) (n : LevelParam),
      substFn (fun _ => c) lps (us.map (subst ks ws)) n = substFn (fun _ => c) lps us n
  | [], us, n => by cases us <;> rfl
  | _ :: _, [], n => rfl
  | p :: lps, u :: us, n => by
    show (if p = n then eval (fun _ => c) (subst ks ws u)
        else substFn (fun _ => c) lps (us.map (subst ks ws)) n) =
      (if p = n then eval (fun _ => c) u else substFn (fun _ => c) lps us n)
    rw [eval_const_subst_of_ren h c ks u, substFn_const_map_ren h c ks lps us n]

theorem substFn_const_map_ren_fun {ws : List Level} (h : IsRen ws) (c : Nat)
    (ks lps : List LevelParam) (us : List Level) :
    substFn (fun _ => c) lps (us.map (subst ks ws)) = substFn (fun _ => c) lps us :=
  funext (substFn_const_map_ren h c ks lps us)

/-- **Zero at every valuation is zero at the all-ones valuation.** -/
theorem eval_eq_zero_of_eval_one : ∀ (l : Level), eval (fun _ => 1) l = 0 →
    ∀ φ : LevelParam → Nat, eval φ l = 0
  | .zero, _, _ => rfl
  | .succ l, h, _ => by simp [eval] at h
  | .max a b, h, φ => by
    simp only [eval] at h ⊢
    have h1 := Nat.le_max_left (eval (fun _ => 1) a) (eval (fun _ => 1) b)
    have h2 := Nat.le_max_right (eval (fun _ => 1) a) (eval (fun _ => 1) b)
    have ha : eval (fun _ => 1) a = 0 := by omega
    have hb : eval (fun _ => 1) b = 0 := by omega
    rw [eval_eq_zero_of_eval_one a ha φ, eval_eq_zero_of_eval_one b hb φ]
    rfl
  | .imax a b, h, φ => by
    simp only [eval] at h ⊢
    by_cases hb : eval (fun _ => 1) b = 0
    · rw [if_pos (eval_eq_zero_of_eval_one b hb φ)]
    · rw [if_neg hb] at h
      have h2 := Nat.le_max_right (eval (fun _ => 1) a) (eval (fun _ => 1) b)
      omega
  | .param n, h, _ => by simp [eval] at h

/-- Pointwise evaluation equality moves under any instantiation. -/
theorem evalEqList_subst (ks : List LevelParam) (ws : List Level) :
    ∀ {us us' : List Level} (φ : LevelParam → Nat),
      EvalEqList (substFn φ ks ws) us us' →
        EvalEqList φ (us.map (subst ks ws)) (us'.map (subst ks ws))
  | [], [], _, _ => trivial
  | u :: us, u' :: us', φ, ⟨h1, h2⟩ => by
    refine ⟨?_, evalEqList_subst ks ws φ h2⟩
    rw [eval_subst, eval_subst]
    exact h1
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], _, h => h.elim

theorem evalEqList_length : ∀ {us us' : List Level} {φ : LevelParam → Nat},
    EvalEqList φ us us' → us.length = us'.length
  | [], [], _, _ => rfl
  | _ :: _, _ :: _, _, h => by rw [List.length_cons, List.length_cons, evalEqList_length h.2]
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], _, h => h.elim

end Level

/-! ## The datum under a renaming -/

namespace LevelRen

open Ix.Kernel.Rules

theorem isNever_eq_not_holds_zero (pw : PropWhen) :
    pw.isNever = !(pw.holds (fun _ => 0)) := by
  cases pw with
  | never => simp
  | ifAllZero ps => simp

theorem isProp_eq_holds_one (pw : PropWhen) : pw.isProp = pw.holds (fun _ => 1) := by
  cases pw with
  | never =>
    have hb : (PropWhen.never == PropWhen.ifAllZero []) = false := by
      simpa using (PropWhen.ifAllZero_ne_never []).symm
    simp [PropWhen.isProp, hb]
  | ifAllZero ps =>
    cases ps with
    | nil => simp [PropWhen.isProp]
    | cons p ps' =>
      have hne : PropWhen.ifAllZero (p :: ps') ≠ PropWhen.ifAllZero [] := by
        intro he
        have := congrArg (PropWhen.holds (fun _ => 1)) he
        simp at this
      have hb : (PropWhen.ifAllZero (p :: ps') == PropWhen.ifAllZero []) = false := by
        simpa using hne
      simp [PropWhen.isProp, hb]

/-- A renamed datum holds at a constant valuation exactly where the datum does. -/
theorem holds_const_substPW {ws : List Level} (h : Level.IsRen ws) (c : Nat)
    (ks : List LevelParam) (pw : PropWhen) :
    (Level.substPW ks ws pw).holds (fun _ => c) = pw.holds (fun _ => c) := by
  rw [Level.holds_substPW]
  have : Level.substFn (fun _ => c) ks ws = fun _ => c :=
    funext (Level.substFn_const_of_ren c ks ws h)
  rw [this]

theorem isNever_substPW_ren {ws : List Level} (h : Level.IsRen ws) (ks : List LevelParam)
    (pw : PropWhen) : (Level.substPW ks ws pw).isNever = pw.isNever := by
  rw [isNever_eq_not_holds_zero, isNever_eq_not_holds_zero, holds_const_substPW h 0]

/-- `never` stays `never` under any instantiation. -/
theorem isNever_substPW {ks : List LevelParam} {ws : List Level} {pw : PropWhen}
    (h : pw.isNever = true) : (Level.substPW ks ws pw).isNever = true := by
  obtain rfl := PropWhen.isNever_iff.mp h
  show (PropWhen.never.bindZ _).isNever = true
  rw [PropWhen.bindZ_never]
  exact PropWhen.isNever_never

/-- A stored datum instantiated at renamed levels holds at a constant valuation exactly where
it does at the levels. -/
theorem holds_const_substPW_map {ws : List Level} (h : Level.IsRen ws) (c : Nat)
    (ks lps : List LevelParam) (us : List Level) (pw : PropWhen) :
    (Level.substPW lps (us.map (Level.subst ks ws)) pw).holds (fun _ => c) =
      (Level.substPW lps us pw).holds (fun _ => c) := by
  rw [Level.holds_substPW, Level.holds_substPW, Level.substFn_const_map_ren_fun h c ks lps us]

/-! ## The three valuation-blind guards -/

/-- **The tower-fire guard moves under a renaming.** -/
theorem fireSem_ren {ws : List Level} (h : Level.IsRen ws) (ks : List LevelParam)
    {entry : ProjEntry md} {us : List Level} (hf : FireSem entry us) :
    FireSem entry (us.map (Level.subst ks ws)) := by
  intro hz φ
  have h1 := hf hz (fun _ => 1)
  refine Level.eval_eq_zero_of_eval_one _ ?_ φ
  rw [Level.eval_subst] at h1 ⊢
  rw [Level.substFn_const_map_ren_fun h 1 ks]
  exact h1

/-- **The structure rescue's never-zero test moves under a renaming.** -/
theorem capsNeverZero_ren {ws : List Level} (h : Level.IsRen ws) (ks : List LevelParam)
    {lps : List LevelParam} {us : List Level} {caps : IndCaps md}
    (hc : capsNeverZero lps us caps = true) :
    capsNeverZero lps (us.map (Level.subst ks ws)) caps = true := by
  unfold capsNeverZero at hc ⊢
  rw [isNever_eq_not_holds_zero] at hc ⊢
  rw [holds_const_substPW_map h 0 ks]
  exact hc

/-! ## Commutation with level instantiation -/

section Commute

variable (ks : List LevelParam) (ws : List Level)

theorem inst_instantiate1 (v : Expr md) :
    ∀ (e : Expr md) (k : Nat),
      (e.instantiate1 v k).instantiateLevelParams ks ws =
        (e.instantiateLevelParams ks ws).instantiate1 (v.instantiateLevelParams ks ws) k := by
  intro e
  induction e with
  | bvar i =>
    intro k
    by_cases h1 : i = k <;> by_cases h2 : i > k <;>
      simp [Expr.instantiate1, Expr.instantiateLevelParams, h1, h2]
  | fvar _ _ _ => intro k; rfl
  | sort _ => intro k; rfl
  | const _ _ => intro k; rfl
  | lit _ => intro k; rfl
  | app f a ihf iha => intro k; simp only [Expr.instantiate1, Expr.instantiateLevelParams, ihf, iha]
  | lam ty b m iht ihb =>
    intro k; simp only [Expr.instantiate1, Expr.instantiateLevelParams, iht, ihb]
  | forallE ty b m iht ihb =>
    intro k; simp only [Expr.instantiate1, Expr.instantiateLevelParams, iht, ihb]
  | letE ty v' b l iht ihv ihb =>
    intro k; simp only [Expr.instantiate1, Expr.instantiateLevelParams, iht, ihv, ihb]
  | proj s i e ih => intro k; simp only [Expr.instantiate1, Expr.instantiateLevelParams, ih]

theorem inst_abstract1 (D : Nat) :
    ∀ (e : Expr md) (k : Nat),
      (e.abstract1 D k).instantiateLevelParams ks ws =
        (e.instantiateLevelParams ks ws).abstract1 D k := by
  intro e
  induction e with
  | fvar i ty _ =>
    intro k
    by_cases h : i = D
    · subst h
      simp [Expr.abstract1, Expr.instantiateLevelParams]
    · simp [Expr.abstract1, Expr.instantiateLevelParams, h]
  | bvar _ => intro k; rfl
  | sort _ => intro k; rfl
  | const _ _ => intro k; rfl
  | lit _ => intro k; rfl
  | app f a ihf iha => intro k; simp only [Expr.abstract1, Expr.instantiateLevelParams, ihf, iha]
  | lam ty b m iht ihb =>
    intro k; simp only [Expr.abstract1, Expr.instantiateLevelParams, iht, ihb]
  | forallE ty b m iht ihb =>
    intro k; simp only [Expr.abstract1, Expr.instantiateLevelParams, iht, ihb]
  | letE ty v b l iht ihv ihb =>
    intro k; simp only [Expr.abstract1, Expr.instantiateLevelParams, iht, ihv, ihb]
  | proj s i e ih => intro k; simp only [Expr.abstract1, Expr.instantiateLevelParams, ih]

theorem inst_getAppFn_const {e : Expr md} {c : Key md} {us : List Level}
    (h : e.getAppFn = .const c us) :
    (e.instantiateLevelParams ks ws).getAppFn = .const c (us.map (Level.subst ks ws)) := by
  rw [Expr.getAppFn_instantiateLevelParams, h]
  rfl

theorem numArgs_inst : ∀ e : Expr md, (e.instantiateLevelParams ks ws).numArgs = e.numArgs := by
  intro e
  induction e with
  | app f a ihf _ =>
    show (f.instantiateLevelParams ks ws).numArgs + 1 = f.numArgs + 1
    rw [ihf]
  | _ => rfl

theorem lamPw_inst (e : Expr md) :
    (e.instantiateLevelParams ks ws).lamPw = e.lamPw.map (Level.substPW ks ws) := by
  cases e <;> rfl

theorem fvarLeaves_inst :
    ∀ e : Expr md, (e.instantiateLevelParams ks ws).fvarLeaves =
      e.fvarLeaves.map (fun l => (l.1, l.2.instantiateLevelParams ks ws)) := by
  intro e
  induction e <;> simp_all [Expr.instantiateLevelParams, Expr.fvarLeaves]

theorem fvarLeaves_sub_inst {a b : Expr md} (h : ∀ l ∈ a.fvarLeaves, l ∈ b.fvarLeaves) :
    ∀ l ∈ (a.instantiateLevelParams ks ws).fvarLeaves,
      l ∈ (b.instantiateLevelParams ks ws).fvarLeaves := by
  rw [fvarLeaves_inst, fvarLeaves_inst]
  intro l hl
  obtain ⟨l', hl', rfl⟩ := List.mem_map.mp hl
  exact List.mem_map.mpr ⟨l', h l' hl', rfl⟩

theorem fvarLeaves_all_inst {a b : Expr md}
    (h : a.fvarLeaves.all (fun l => b.fvarLeaves.contains l) = true) :
    (a.instantiateLevelParams ks ws).fvarLeaves.all
      (fun l => (b.instantiateLevelParams ks ws).fvarLeaves.contains l) = true := by
  rw [List.all_eq_true] at h ⊢
  intro l hl
  have hsub : ∀ l ∈ a.fvarLeaves, l ∈ b.fvarLeaves := fun l hl =>
    List.contains_iff_mem.mp (h l hl)
  exact List.contains_iff_mem.mpr (fvarLeaves_sub_inst ks ws hsub l hl)

theorem wscopedB_inst :
    ∀ (e : Expr md) (D : Nat), (e.instantiateLevelParams ks ws).wscopedB D = e.wscopedB D := by
  intro e
  induction e <;> intro D <;> simp_all [Expr.instantiateLevelParams, Expr.wscopedB]

theorem piResidual_inst :
    ∀ (args : List (Expr md)) (T r : Expr md), piResidual T args = some r →
      piResidual (T.instantiateLevelParams ks ws) (args.map (·.instantiateLevelParams ks ws)) =
        some (r.instantiateLevelParams ks ws) := by
  intro args
  induction args with
  | nil =>
    intro T r h
    simp only [piResidual, Option.some.injEq] at h
    subst h
    simp [piResidual]
  | cons a as ih =>
    intro T r h
    cases T with
    | forallE ty b m =>
      simp only [piResidual, Expr.instantiateLevelParams, List.map_cons] at h ⊢
      rw [← inst_instantiate1 ks ws a b 0]
      exact ih _ _ h
    | _ => simp [piResidual] at h

theorem inst_instSpine :
    ∀ (as : List (Expr md)) (t : Nat) (e : Expr md),
      (Expr.instSpine as t e).instantiateLevelParams ks ws =
        Expr.instSpine (as.map (·.instantiateLevelParams ks ws)) t
          (e.instantiateLevelParams ks ws) := by
  intro as
  induction as with
  | nil => intro t e; rfl
  | cons a as ih =>
    intro t e
    simp only [Expr.instSpine, List.map_cons]
    rw [ih, inst_instantiate1]

theorem inst_instantiateList :
    ∀ (n : Nat) (vs : List (Expr md)), vs.length ≤ n → ∀ (e : Expr md) (d : Nat),
      (e.instantiateList vs d).instantiateLevelParams ks ws =
        (e.instantiateLevelParams ks ws).instantiateList
          (vs.map (·.instantiateLevelParams ks ws)) d := by
  intro n
  induction n with
  | zero =>
    intro vs hvs
    obtain rfl : vs = [] := List.eq_nil_of_length_eq_zero (by omega)
    intro e
    induction e <;> intro d <;> simp_all [Expr.instantiateList, Expr.instantiateLevelParams]
  | succ n ihn =>
    intro vs hvs e
    induction e with
    | bvar j =>
      intro d
      by_cases h1 : j < d
      · simp [Expr.instantiateList, Expr.instantiateLevelParams, h1]
      · by_cases h2 : j - d < vs.length
        · have hlen : (vs.take (j - d)).length ≤ n := by
            rw [List.length_take]; omega
          have key := ihn (vs.take (j - d)) hlen vs[j - d] d
          simp [Expr.instantiateList, Expr.instantiateLevelParams, h1, h2, key]
        · simp [Expr.instantiateList, Expr.instantiateLevelParams, h1, h2]
    | fvar => intro d; simp [Expr.instantiateList, Expr.instantiateLevelParams]
    | sort => intro d; simp [Expr.instantiateList, Expr.instantiateLevelParams]
    | const => intro d; simp [Expr.instantiateList, Expr.instantiateLevelParams]
    | lit => intro d; simp [Expr.instantiateList, Expr.instantiateLevelParams]
    | app f a ihf iha =>
      intro d; simp only [Expr.instantiateList, Expr.instantiateLevelParams, ihf, iha]
    | lam ty b m iht ihb =>
      intro d; simp only [Expr.instantiateList, Expr.instantiateLevelParams, iht, ihb]
    | forallE ty b m iht ihb =>
      intro d; simp only [Expr.instantiateList, Expr.instantiateLevelParams, iht, ihb]
    | letE ty v b l iht ihv ihb =>
      intro d; simp only [Expr.instantiateList, Expr.instantiateLevelParams, iht, ihv, ihb]
    | proj s i e ih => intro d; simp only [Expr.instantiateList, Expr.instantiateLevelParams, ih]

theorem getD_map_inst :
    ∀ (l : List (Expr md)) (n : Nat),
      (l.map (·.instantiateLevelParams ks ws)).getD n (.bvar 0) =
        (l.getD n (.bvar 0)).instantiateLevelParams ks ws
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, n + 1 => getD_map_inst l n

theorem natLitToConstructor_inst (n : Nat) :
    (natLitToConstructor n : Expr md).instantiateLevelParams ks ws = natLitToConstructor n := by
  cases n <;> rfl

theorem strLitToConstructor_inst (s : String) :
    (strLitToConstructor s : Expr md).instantiateLevelParams ks ws = strLitToConstructor s := by
  unfold strLitToConstructor
  simp only [Expr.instantiateLevelParams]
  congr 1
  generalize s.toList = l
  induction l with
  | nil => first | rfl | simp [Expr.instantiateLevelParams, Level.subst]
  | cons c cs ih =>
    simp only [List.foldr, Expr.instantiateLevelParams, ih, List.map_cons, List.map_nil,
      Level.subst]

theorem natOpResult_map_inst (c : Key md) (a b : Nat) :
    (natOpResult c a b).map (·.instantiateLevelParams ks ws) = natOpResult c a b := by
  simp only [natOpResult, apply_ite (Option.map (·.instantiateLevelParams ks ws)),
    Option.map_some, Option.map_none, Expr.instantiateLevelParams, List.map_nil]

theorem natOpResult_inst {c : Key md} {a b : Nat} {r : Expr md}
    (h : natOpResult c a b = some r) : r.instantiateLevelParams ks ws = r := by
  have := natOpResult_map_inst ks ws c a b
  rw [h] at this
  exact Option.some.inj this

theorem rawNatLit?_inst (e : Expr md) :
    rawNatLit? (e.instantiateLevelParams ks ws) = rawNatLit? e := by
  cases e with
  | const c us => cases us <;> rfl
  | lit l => cases l <;> rfl
  | _ => rfl

theorem isUnitLikeTy_inst (env : Env md) (e : Expr md) :
    isUnitLikeTy env (e.instantiateLevelParams ks ws) = isUnitLikeTy env e := by
  cases e <;> rfl

theorem natAddLit_inst (b : Expr md) (k : Nat) :
    (Rules.natAddLit b k).instantiateLevelParams ks ws =
      Rules.natAddLit (b.instantiateLevelParams ks ws) k := by
  unfold Rules.natAddLit
  by_cases hk : k = 0
  · rw [if_pos hk, if_pos hk]
  · rw [if_neg hk, if_neg hk]
    rfl

theorem natOffsetOf_inst : ∀ e : Expr md,
    Rules.natOffsetOf (e.instantiateLevelParams ks ws) =
      (Rules.natOffsetOf e).map (fun p => (p.1.instantiateLevelParams ks ws, p.2)) := by
  refine Rules.natOffsetOf_rec (fun e ih => ?_)
  cases e with
  | lit l => cases l <;> rfl
  | app f x =>
    cases f with
    | const c us =>
      show Rules.natOffsetOf (.app (.const c (us.map (Level.subst ks ws)))
        (x.instantiateLevelParams ks ws)) = _
      rw [Rules.natOffsetOf_succ, Rules.natOffsetOf_succ]
      by_cases hc : c = natSuccName
      · subst hc
        rw [if_pos rfl, if_pos rfl, ih x (Or.inl ⟨us, rfl⟩)]
        cases Rules.natOffsetOf x with
        | none => rfl
        | some p => obtain ⟨b, k⟩ := p; rfl
      · rw [if_neg hc, if_neg hc]
        rfl
    | app g y =>
      cases g with
      | const c us =>
        cases x with
        | lit l =>
          cases l with
          | natVal m =>
            show Rules.natOffsetOf (.app (.app (.const c (us.map (Level.subst ks ws)))
              (y.instantiateLevelParams ks ws)) (.lit (.natVal m))) = _
            rw [Rules.natOffsetOf_add, Rules.natOffsetOf_add]
            by_cases hc : c = natAddName
            · subst hc
              rw [if_pos rfl, if_pos rfl, ih y (Or.inr ⟨us, m, rfl⟩)]
              cases Rules.natOffsetOf y with
              | none => rfl
              | some p => obtain ⟨b, k⟩ := p; rfl
            · rw [if_neg hc, if_neg hc]
              rfl
          | strVal _ => rfl
        | _ => rfl
      | _ => rfl
    | _ => rfl
  | _ => rfl

theorem natOffsetAdd_inst : ∀ e : Expr md,
    Rules.natOffsetAdd (e.instantiateLevelParams ks ws) = Rules.natOffsetAdd e := by
  refine Rules.natOffsetOf_rec (fun e ih => ?_)
  cases e with
  | app f x =>
    cases f with
    | const c us =>
      show Rules.natOffsetAdd (.app (.const c (us.map (Level.subst ks ws)))
        (x.instantiateLevelParams ks ws)) = _
      rw [Rules.natOffsetAdd_succ, Rules.natOffsetAdd_succ]
      by_cases hc : c = natSuccName
      · subst hc
        rw [if_pos rfl, if_pos rfl, ih x (Or.inl ⟨us, rfl⟩)]
      · rw [if_neg hc, if_neg hc]
    | app g y =>
      cases g with
      | const c us =>
        cases x with
        | lit l => cases l <;> rfl
        | _ => rfl
      | _ => rfl
    | _ => rfl
  | _ => rfl

theorem etaProjs_inst (env : Env md) (T : Key md) (us : List Level)
    (targs : List (Expr md)) (b : Expr md) (nF : Nat) :
    (etaProjs env T us targs b nF).map (·.instantiateLevelParams ks ws) =
      etaProjs env T (us.map (Level.subst ks ws)) (targs.map (·.instantiateLevelParams ks ws))
        (b.instantiateLevelParams ks ws) nF := by
  unfold etaProjs
  by_cases ht : towerSlotsAll env T nF = true
  · simp only [ht, if_true, List.map_map]
    rfl
  · simp only [ht, Bool.false_eq_true, if_false, List.map_map]
    congr 1
    funext j
    simp only [Function.comp, instantiateLevelParams_mkAppN, List.map_append, List.map_cons,
      List.map_nil]
    rfl

theorem etaFabArgsE_inst (env : Env md) (T : Key md) (us : List Level)
    (targs : List (Expr md)) (b : Expr md) (nF : Nat) :
    (etaFabArgsE env T us targs b nF).map (·.instantiateLevelParams ks ws) =
      etaFabArgsE env T (us.map (Level.subst ks ws)) (targs.map (·.instantiateLevelParams ks ws))
        (b.instantiateLevelParams ks ws) nF := by
  unfold etaFabArgsE
  rw [List.map_append, etaProjs_inst]

end Commute

/-! ## The prop-ness readers under a renaming

Each reader's answer, read at a constant valuation, is unchanged. At the all-ones valuation
that is `isProofFast`'s test (`isProp_eq_holds_one`). -/

section Readers

variable {ws : List Level} (hR : Level.IsRen ws) (ks : List LevelParam)
include hR

theorem peelNeverPis_inst :
    ∀ (n : Nat) (e : Expr md), (e.instantiateLevelParams ks ws).peelNeverPis n =
      (e.peelNeverPis n).map (·.instantiateLevelParams ks ws)
  | 0, _ => rfl
  | k + 1, e => by
    cases e with
    | forallE ty b m =>
      show (if (Level.substPW ks ws m.pw).isNever then
          (b.instantiateLevelParams ks ws).peelNeverPis k else none) = _
      rw [isNever_substPW_ren hR ks m.pw]
      by_cases hm : m.pw.isNever = true
      · simp [Expr.peelNeverPis, hm, peelNeverPis_inst k b]
      · simp [Expr.peelNeverPis, hm]
    | _ => rfl

theorem residualPW_inst (c : Nat) (o : Option (Expr md)) :
    (residualPW (o.map (·.instantiateLevelParams ks ws))).map (·.holds (fun _ => c)) =
      (residualPW o).map (·.holds (fun _ => c)) := by
  rcases o with _ | e
  · rfl
  · cases e with
    | sort u =>
      show some ((Level.zeronessOf (Level.subst ks ws u)).holds (fun _ => c)) =
        some ((Level.zeronessOf u).holds (fun _ => c))
      rw [Level.zeronessOf_subst, holds_const_substPW hR c ks]
    | _ => rfl

theorem headTypePW_inst (c : Nat) (f : Key md → Option (ConstantInfo md)) (e : Expr md)
    (n : Nat) :
    (headTypePW f (e.instantiateLevelParams ks ws) n).map (·.holds (fun _ => c)) =
      (headTypePW f e n).map (·.holds (fun _ => c)) := by
  cases e with
  | const I us =>
    show (match f I with
        | some ci =>
          if ci.isTowerEntry then none else
          if (us.map (Level.subst ks ws)).length = ci.toConstantVal.levelParams.length then
            (residualPW (ci.toConstantVal.type.peelNeverPis n)).map
              (Level.substPW ci.toConstantVal.levelParams (us.map (Level.subst ks ws)))
          else none
        | none => none).map (·.holds (fun _ => c)) =
      (match f I with
        | some ci =>
          if ci.isTowerEntry then none else
          if us.length = ci.toConstantVal.levelParams.length then
            (residualPW (ci.toConstantVal.type.peelNeverPis n)).map
              (Level.substPW ci.toConstantVal.levelParams us)
          else none
        | none => none).map (·.holds (fun _ => c))
    rcases f I with _ | ci
    · rfl
    · dsimp only
      rw [List.length_map]
      split
      · rfl
      · split
        · rw [Option.map_map, Option.map_map]
          congr 1
          funext pw
          exact holds_const_substPW_map hR c ks _ us pw
        · rfl
  | fvar i ty =>
    show (residualPW ((ty.instantiateLevelParams ks ws).peelNeverPis n)).map _ =
      (residualPW (ty.peelNeverPis n)).map _
    rw [peelNeverPis_inst hR ks n ty]
    exact residualPW_inst hR ks c _
  | _ => rfl

theorem typeSortPW_inst (c : Nat) (f : Key md → Option (ConstantInfo md)) (T : Expr md) :
    (typeSortPW f (T.instantiateLevelParams ks ws)).map (·.holds (fun _ => c)) =
      (typeSortPW f T).map (·.holds (fun _ => c)) := by
  by_cases h1 : ∃ ty b m, T = .forallE ty b m
  · obtain ⟨ty, b, m, rfl⟩ := h1
    show some ((Level.substPW ks ws m.pw).holds (fun _ => c)) = some (m.pw.holds (fun _ => c))
    rw [holds_const_substPW hR c ks]
  by_cases h2 : ∃ u, T = .sort u
  · obtain ⟨u, rfl⟩ := h2; rfl
  have h1' : ∀ ty b m, T ≠ .forallE ty b m := fun ty b m e => h1 ⟨ty, b, m, e⟩
  have h2' : ∀ u, T ≠ .sort u := fun u e => h2 ⟨u, e⟩
  have h1r : ∀ ty b m, T.instantiateLevelParams ks ws ≠ .forallE ty b m := by
    intro ty b m e
    cases T with
    | forallE ty' b' m' => exact h1' ty' b' m' rfl
    | _ => exact nomatch e
  have h2r : ∀ u, T.instantiateLevelParams ks ws ≠ .sort u := by
    intro u e
    cases T with
    | sort u' => exact h2' u' rfl
    | _ => exact nomatch e
  rw [typeSortPW_other h1r h2r, typeSortPW_other h1' h2', Expr.getAppFn_instantiateLevelParams,
    numArgs_inst ks ws]
  exact headTypePW_inst hR ks c f _ _

theorem headProofPW_inst (c : Nat) (f : Key md → Option (ConstantInfo md)) (e : Expr md) :
    (headProofPW f (e.instantiateLevelParams ks ws)).map (·.holds (fun _ => c)) =
      (headProofPW f e).map (·.holds (fun _ => c)) := by
  cases e with
  | const cn us =>
    show (match f cn with
        | some ci =>
          if ci.isTowerEntry then none else
          if (us.map (Level.subst ks ws)).length = ci.toConstantVal.levelParams.length then
            (typeSortPW f ci.toConstantVal.type).map
              (Level.substPW ci.toConstantVal.levelParams (us.map (Level.subst ks ws)))
          else none
        | none => none).map (·.holds (fun _ => c)) =
      (match f cn with
        | some ci =>
          if ci.isTowerEntry then none else
          if us.length = ci.toConstantVal.levelParams.length then
            (typeSortPW f ci.toConstantVal.type).map
              (Level.substPW ci.toConstantVal.levelParams us)
          else none
        | none => none).map (·.holds (fun _ => c))
    rcases f cn with _ | ci
    · rfl
    · dsimp only
      rw [List.length_map]
      split
      · rfl
      · split
        · rw [Option.map_map, Option.map_map]
          congr 1
          funext pw
          exact holds_const_substPW_map hR c ks _ us pw
        · rfl
  | fvar i ty => exact typeSortPW_inst hR ks c f ty
  | _ => rfl

theorem proofPW_inst (c : Nat) (f : Key md → Option (ConstantInfo md)) (a : Expr md) :
    (proofPW f (a.instantiateLevelParams ks ws)).map (·.holds (fun _ => c)) =
      (proofPW f a).map (·.holds (fun _ => c)) := by
  by_cases h : ∃ ty b m, a = .lam ty b m
  · obtain ⟨ty, b, m, rfl⟩ := h
    show some ((Level.substPW ks ws m.pw).holds (fun _ => c)) = some (m.pw.holds (fun _ => c))
    rw [holds_const_substPW hR c ks]
  have h' : ∀ ty b m, a ≠ .lam ty b m := fun ty b m e => h ⟨ty, b, m, e⟩
  have hr : ∀ ty b m, a.instantiateLevelParams ks ws ≠ .lam ty b m := by
    intro ty b m e
    cases a with
    | lam ty' b' m' => exact h' ty' b' m' rfl
    | _ => exact nomatch e
  rw [proofPW_other hr, proofPW_other h', Expr.getAppFn_instantiateLevelParams]
  exact headProofPW_inst hR ks c f _

/-- **`isProofFast` is blind to a renaming.** -/
theorem isProofFast_inst (f : Key md → Option (ConstantInfo md)) (a : Expr md) :
    isProofFast f (a.instantiateLevelParams ks ws) = isProofFast f a := by
  have key := proofPW_inst hR ks 1 f a
  unfold isProofFast
  revert key
  rcases proofPW f (a.instantiateLevelParams ks ws) with _ | pw' <;>
    rcases proofPW f a with _ | pw <;> intro key
  · rfl
  · exact nomatch key
  · exact nomatch key
  · rw [isProp_eq_holds_one, isProp_eq_holds_one]
    exact Option.some.inj key

end Readers

end LevelRen

/-! ## Arity -/

/-- **Every stored constant `e` names is applied at its own number of level parameters**,
annotations included. -/
def Expr.arOk (env : Env md) : Expr md → Bool
  | .bvar _ => true
  | .fvar _ ty => Expr.arOk env ty
  | .sort _ => true
  | .const c us =>
    match env.find? c with
    | some ci => us.length == ci.toConstantVal.levelParams.length
    | none => true
  | .app f a => Expr.arOk env f && Expr.arOk env a
  | .lam ty b _ => Expr.arOk env ty && Expr.arOk env b
  | .forallE ty b _ => Expr.arOk env ty && Expr.arOk env b
  | .letE ty v b _ => Expr.arOk env ty && Expr.arOk env v && Expr.arOk env b
  | .lit _ => true
  | .proj _ _ e => Expr.arOk env e

namespace LevelRen

section Arity

variable {env : Env md}

theorem arOk_const {c : Key md} {us : List Level}
    (h : Expr.arOk env (.const c us) = true) {ci : ConstantInfo md}
    (hf : env.find? c = some ci) : us.length = ci.toConstantVal.levelParams.length := by
  simp only [Expr.arOk, hf, beq_iff_eq] at h
  exact h

theorem arOk_const_of {c : Key md} {us : List Level}
    (h : ∀ ci, env.find? c = some ci → us.length = ci.toConstantVal.levelParams.length) :
    Expr.arOk env (.const c us) = true := by
  simp only [Expr.arOk]
  rcases hf : env.find? c with _ | ci
  · rfl
  · simp [h ci hf]

theorem arOk_const_nil {c : Key md}
    (h : ∀ ci, env.find? c = some ci → ci.toConstantVal.levelParams = []) :
    Expr.arOk env (.const c []) = true :=
  arOk_const_of (fun ci hf => by rw [h ci hf]; rfl)

theorem arOk_app {f a : Expr md} :
    Expr.arOk env (.app f a) = true ↔ Expr.arOk env f = true ∧ Expr.arOk env a = true := by
  simp [Expr.arOk]

theorem arOk_instantiate1 {v : Expr md} (hv : Expr.arOk env v = true) :
    ∀ (e : Expr md) (k : Nat), Expr.arOk env e = true →
      Expr.arOk env (e.instantiate1 v k) = true := by
  intro e
  induction e with
  | bvar i =>
    intro k _
    simp only [Expr.instantiate1]
    split
    · exact hv
    · split <;> rfl
  | fvar _ _ _ => intro k h; exact h
  | sort _ => intro k h; exact h
  | const _ _ => intro k h; exact h
  | lit _ => intro k h; exact h
  | app f a ihf iha =>
    intro k h
    simp only [Expr.instantiate1, Expr.arOk, Bool.and_eq_true] at h ⊢
    exact ⟨ihf k h.1, iha k h.2⟩
  | lam ty b m iht ihb =>
    intro k h
    simp only [Expr.instantiate1, Expr.arOk, Bool.and_eq_true] at h ⊢
    exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | forallE ty b m iht ihb =>
    intro k h
    simp only [Expr.instantiate1, Expr.arOk, Bool.and_eq_true] at h ⊢
    exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | letE ty v' b l iht ihv ihb =>
    intro k h
    simp only [Expr.instantiate1, Expr.arOk, Bool.and_eq_true] at h ⊢
    exact ⟨⟨iht k h.1.1, ihv k h.1.2⟩, ihb (k + 1) h.2⟩
  | proj s i e ih =>
    intro k h
    simp only [Expr.instantiate1, Expr.arOk] at h ⊢
    exact ih k h

theorem arOk_of_instantiate1 {v : Expr md} :
    ∀ (e : Expr md) (k : Nat), Expr.arOk env (e.instantiate1 v k) = true →
      Expr.arOk env e = true := by
  intro e
  induction e with
  | bvar i => intro _ _; rfl
  | fvar _ _ _ => intro k h; exact h
  | sort _ => intro k h; exact h
  | const _ _ => intro k h; exact h
  | lit _ => intro k h; exact h
  | app f a ihf iha =>
    intro k h
    simp only [Expr.instantiate1, Expr.arOk, Bool.and_eq_true] at h ⊢
    exact ⟨ihf k h.1, iha k h.2⟩
  | lam ty b m iht ihb =>
    intro k h
    simp only [Expr.instantiate1, Expr.arOk, Bool.and_eq_true] at h ⊢
    exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | forallE ty b m iht ihb =>
    intro k h
    simp only [Expr.instantiate1, Expr.arOk, Bool.and_eq_true] at h ⊢
    exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | letE ty v' b l iht ihv ihb =>
    intro k h
    simp only [Expr.instantiate1, Expr.arOk, Bool.and_eq_true] at h ⊢
    exact ⟨⟨iht k h.1.1, ihv k h.1.2⟩, ihb (k + 1) h.2⟩
  | proj s i e ih =>
    intro k h
    simp only [Expr.instantiate1, Expr.arOk] at h ⊢
    exact ih k h

theorem arOk_abstract1 (D : Nat) :
    ∀ (e : Expr md) (k : Nat), Expr.arOk env e = true →
      Expr.arOk env (e.abstract1 D k) = true := by
  intro e
  induction e with
  | fvar i ty _ =>
    intro k h
    simp only [Expr.abstract1]
    split
    · rfl
    · exact h
  | bvar _ => intro k h; exact h
  | sort _ => intro k h; exact h
  | const _ _ => intro k h; exact h
  | lit _ => intro k h; exact h
  | app f a ihf iha =>
    intro k h
    simp only [Expr.abstract1, Expr.arOk, Bool.and_eq_true] at h ⊢
    exact ⟨ihf k h.1, iha k h.2⟩
  | lam ty b m iht ihb =>
    intro k h
    simp only [Expr.abstract1, Expr.arOk, Bool.and_eq_true] at h ⊢
    exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | forallE ty b m iht ihb =>
    intro k h
    simp only [Expr.abstract1, Expr.arOk, Bool.and_eq_true] at h ⊢
    exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | letE ty v b l iht ihv ihb =>
    intro k h
    simp only [Expr.abstract1, Expr.arOk, Bool.and_eq_true] at h ⊢
    exact ⟨⟨iht k h.1.1, ihv k h.1.2⟩, ihb (k + 1) h.2⟩
  | proj s i e ih =>
    intro k h
    simp only [Expr.abstract1, Expr.arOk] at h ⊢
    exact ih k h

/-- **Arity does not see levels.** -/
theorem arOk_inst (ks : List LevelParam) (ws : List Level) :
    ∀ e : Expr md, Expr.arOk env (e.instantiateLevelParams ks ws) = Expr.arOk env e := by
  intro e
  induction e with
  | const c us =>
    simp only [Expr.instantiateLevelParams, Expr.arOk, List.length_map]
  | _ => simp_all [Expr.instantiateLevelParams, Expr.arOk]

theorem arOk_getAppArgs : ∀ {e : Expr md}, Expr.arOk env e = true →
    ∀ a ∈ e.getAppArgs, Expr.arOk env a = true := by
  intro e
  induction e with
  | app f x ihf _ =>
    intro h a ha
    simp only [Expr.arOk, Bool.and_eq_true] at h
    simp only [Expr.getAppArgs, List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | rfl
    · exact ihf h.1 a ha
    · exact h.2
  | _ => intro _ a ha; simp [Expr.getAppArgs] at ha

theorem arOk_getAppFn : ∀ {e : Expr md}, Expr.arOk env e = true →
    Expr.arOk env e.getAppFn = true := by
  intro e
  induction e with
  | app f x ihf _ =>
    intro h
    simp only [Expr.arOk, Bool.and_eq_true] at h
    exact ihf h.1
  | _ => intro h; exact h

theorem arOk_mkAppN : ∀ (as : List (Expr md)) {f : Expr md}, Expr.arOk env f = true →
    (∀ a ∈ as, Expr.arOk env a = true) → Expr.arOk env (Expr.mkAppN f as) = true
  | [], _, hf, _ => hf
  | a :: as, f, hf, has => by
    refine arOk_mkAppN as (f := .app f a) ?_ (fun x hx => has x (List.mem_cons_of_mem _ hx))
    simp only [Expr.arOk, Bool.and_eq_true]
    exact ⟨hf, has a (by simp)⟩

theorem arOk_mkAppN_inv : ∀ (as : List (Expr md)) {f : Expr md},
    Expr.arOk env (Expr.mkAppN f as) = true →
      Expr.arOk env f = true ∧ ∀ a ∈ as, Expr.arOk env a = true
  | [], _, h => ⟨h, fun _ ha => nomatch ha⟩
  | a :: as, f, h => by
    obtain ⟨h1, h2⟩ := arOk_mkAppN_inv as (f := .app f a) h
    simp only [Expr.arOk, Bool.and_eq_true] at h1
    refine ⟨h1.1, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h1.2
    · exact h2 x hx

theorem arOk_getD : ∀ {l : List (Expr md)}, (∀ a ∈ l, Expr.arOk env a = true) → ∀ n,
    Expr.arOk env (l.getD n (.bvar 0)) = true
  | [], _, _ => rfl
  | a :: _, h, 0 => h a (by simp)
  | _ :: l, h, n + 1 => arOk_getD (l := l) (fun x hx => h x (List.mem_cons_of_mem _ hx)) n

theorem arOk_instSpine : ∀ (as : List (Expr md)) (t : Nat) {e : Expr md},
    (∀ a ∈ as, Expr.arOk env a = true) → Expr.arOk env e = true →
      Expr.arOk env (Expr.instSpine as t e) = true
  | [], _, _, _, he => he
  | a :: as, t, e, has, he =>
    arOk_instSpine as (t - 1) (fun x hx => has x (List.mem_cons_of_mem _ hx))
      (arOk_instantiate1 (has a (by simp)) e t he)

theorem arOk_instantiateList :
    ∀ (n : Nat) (vs : List (Expr md)), vs.length ≤ n → (∀ v ∈ vs, Expr.arOk env v = true) →
      ∀ (e : Expr md) (d : Nat), Expr.arOk env e = true →
        Expr.arOk env (e.instantiateList vs d) = true := by
  intro n
  induction n with
  | zero =>
    intro vs hvs _
    obtain rfl : vs = [] := List.eq_nil_of_length_eq_zero (by omega)
    intro e
    induction e with
    | bvar j => intro d _; simp only [Expr.instantiateList]; split <;> simp_all [Expr.arOk]
    | _ => intro d h; simp_all [Expr.instantiateList, Expr.arOk]
  | succ n ihn =>
    intro vs hvs hv e
    induction e with
    | bvar j =>
      intro d _
      simp only [Expr.instantiateList]
      split
      · rfl
      · split
        · rename_i h2
          have hlen : (vs.take (j - d)).length ≤ n := by rw [List.length_take]; omega
          exact ihn (vs.take (j - d)) hlen
            (fun x hx => hv x (List.mem_of_mem_take hx)) _ d
            (hv _ (List.getElem_mem h2))
        · rfl
    | fvar _ _ _ => intro d h; simp only [Expr.instantiateList]; exact h
    | sort _ => intro d h; simp only [Expr.instantiateList]; exact h
    | const _ _ => intro d h; simp only [Expr.instantiateList]; exact h
    | lit _ => intro d h; simp only [Expr.instantiateList]; exact h
    | app f a ihf iha =>
      intro d h
      simp only [Expr.instantiateList, Expr.arOk, Bool.and_eq_true] at h ⊢
      exact ⟨ihf d h.1, iha d h.2⟩
    | lam ty b m iht ihb =>
      intro d h
      simp only [Expr.instantiateList, Expr.arOk, Bool.and_eq_true] at h ⊢
      exact ⟨iht d h.1, ihb (d + 1) h.2⟩
    | forallE ty b m iht ihb =>
      intro d h
      simp only [Expr.instantiateList, Expr.arOk, Bool.and_eq_true] at h ⊢
      exact ⟨iht d h.1, ihb (d + 1) h.2⟩
    | letE ty v b l iht ihv ihb =>
      intro d h
      simp only [Expr.instantiateList, Expr.arOk, Bool.and_eq_true] at h ⊢
      exact ⟨⟨iht d h.1.1, ihv d h.1.2⟩, ihb (d + 1) h.2⟩
    | proj s i e ih =>
      intro d h
      simp only [Expr.instantiateList, Expr.arOk] at h ⊢
      exact ih d h

theorem arOk_piResidual : ∀ (args : List (Expr md)) {T r : Expr md},
    piResidual T args = some r → Expr.arOk env T = true →
      (∀ a ∈ args, Expr.arOk env a = true) → Expr.arOk env r = true
  | [], T, r, h, hT, _ => by
    simp only [piResidual, Option.some.injEq] at h
    subst h
    exact hT
  | a :: as, T, r, h, hT, has => by
    cases T with
    | forallE ty b m =>
      simp only [piResidual] at h
      simp only [Expr.arOk, Bool.and_eq_true] at hT
      exact arOk_piResidual as h (arOk_instantiate1 (has a (by simp)) b 0 hT.2)
        (fun x hx => has x (List.mem_cons_of_mem _ hx))
    | _ => simp [piResidual] at h

/-- Every annotation of an arity-correct term is arity-correct. -/
theorem arOk_fvarLeaves : ∀ {e : Expr md}, Expr.arOk env e = true →
    ∀ l ∈ e.fvarLeaves, Expr.arOk env l.2 = true := by
  intro e
  induction e with
  | fvar i ty ih =>
    intro h l hl
    simp only [Expr.arOk] at h
    simp only [Expr.fvarLeaves, List.mem_cons] at hl
    rcases hl with rfl | hl
    · exact h
    · exact ih h l hl
  | app f a ihf iha =>
    intro h l hl
    simp only [Expr.arOk, Bool.and_eq_true] at h
    simp only [Expr.fvarLeaves, List.mem_append] at hl
    rcases hl with hl | hl
    · exact ihf h.1 l hl
    · exact iha h.2 l hl
  | lam ty b m iht ihb =>
    intro h l hl
    simp only [Expr.arOk, Bool.and_eq_true] at h
    simp only [Expr.fvarLeaves, List.mem_append] at hl
    rcases hl with hl | hl
    · exact iht h.1 l hl
    · exact ihb h.2 l hl
  | forallE ty b m iht ihb =>
    intro h l hl
    simp only [Expr.arOk, Bool.and_eq_true] at h
    simp only [Expr.fvarLeaves, List.mem_append] at hl
    rcases hl with hl | hl
    · exact iht h.1 l hl
    · exact ihb h.2 l hl
  | letE ty v b _ iht ihv ihb =>
    intro h l hl
    simp only [Expr.arOk, Bool.and_eq_true] at h
    simp only [Expr.fvarLeaves, List.mem_append] at hl
    rcases hl with (hl | hl) | hl
    · exact iht h.1.1 l hl
    · exact ihv h.1.2 l hl
    · exact ihb h.2 l hl
  | proj s i e ih =>
    intro h l hl
    simp only [Expr.arOk] at h
    simp only [Expr.fvarLeaves] at hl
    exact ih h l hl
  | _ => intro _ l hl; simp [Expr.fvarLeaves] at hl

/-- The leaves of an instantiation are the term's and the value's. -/
theorem fvarLeaves_instantiate1 {v : Expr md} :
    ∀ (e : Expr md) (k : Nat) (l : Nat × Expr md), l ∈ (e.instantiate1 v k).fvarLeaves →
      l ∈ e.fvarLeaves ∨ l ∈ v.fvarLeaves := by
  intro e
  induction e with
  | bvar i =>
    intro k l hl
    simp only [Expr.instantiate1] at hl
    split at hl
    · exact .inr hl
    · split at hl <;> simp [Expr.fvarLeaves] at hl
  | fvar _ _ _ => intro k l hl; exact .inl hl
  | sort _ => intro k l hl; exact .inl hl
  | const _ _ => intro k l hl; exact .inl hl
  | lit _ => intro k l hl; exact .inl hl
  | app f a ihf iha =>
    intro k l hl
    simp only [Expr.instantiate1, Expr.fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · rcases ihf k l hl with h | h
      · exact .inl (.inl h)
      · exact .inr h
    · rcases iha k l hl with h | h
      · exact .inl (.inr h)
      · exact .inr h
  | lam ty b m iht ihb =>
    intro k l hl
    simp only [Expr.instantiate1, Expr.fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · rcases iht k l hl with h | h
      · exact .inl (.inl h)
      · exact .inr h
    · rcases ihb (k + 1) l hl with h | h
      · exact .inl (.inr h)
      · exact .inr h
  | forallE ty b m iht ihb =>
    intro k l hl
    simp only [Expr.instantiate1, Expr.fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · rcases iht k l hl with h | h
      · exact .inl (.inl h)
      · exact .inr h
    · rcases ihb (k + 1) l hl with h | h
      · exact .inl (.inr h)
      · exact .inr h
  | letE ty v' b _ iht ihv ihb =>
    intro k l hl
    simp only [Expr.instantiate1, Expr.fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with (hl | hl) | hl
    · rcases iht k l hl with h | h
      · exact .inl (.inl (.inl h))
      · exact .inr h
    · rcases ihv k l hl with h | h
      · exact .inl (.inl (.inr h))
      · exact .inr h
    · rcases ihb (k + 1) l hl with h | h
      · exact .inl (.inr h)
      · exact .inr h
  | proj s i e ih =>
    intro k l hl
    simp only [Expr.instantiate1, Expr.fvarLeaves] at hl ⊢
    exact ih k l hl

theorem arOk_natOffsetOf_base : ∀ {a : Expr md} {b : Expr md} {k : Nat},
    Rules.natOffsetOf a = some (b, k) → Expr.arOk env a = true → Expr.arOk env b = true := by
  intro a
  refine Rules.natOffsetOf_rec (Q := fun a => ∀ {b : Expr md} {k : Nat},
    Rules.natOffsetOf a = some (b, k) → Expr.arOk env a = true → Expr.arOk env b = true)
    (fun e ih => ?_) a
  intro b k h ha
  rcases Rules.natOffsetOf_some h with ⟨rfl, rfl⟩ | ⟨us, x, rfl, hs⟩ | ⟨us, x, n, rfl, hs⟩
  · rfl
  · have hx' : Expr.arOk env x = true := (arOk_app.mp ha).2
    unfold Rules.natOffsetStep at hs
    split at hs
    · rename_i b' k' hx
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hs
      exact ih x (Or.inl ⟨us, rfl⟩) hx hx'
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hs
      exact hx'
  · have hx' : Expr.arOk env x = true := (arOk_app.mp (arOk_app.mp ha).1).2
    unfold Rules.natOffsetStep at hs
    split at hs
    · rename_i b' k' hx
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hs
      exact ih x (Or.inr ⟨us, n, rfl⟩) hx hx'
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hs
      exact hx'

end Arity

end LevelRen

/-! ## The store -/

/-- **A stored theorem's value mentions only the theorem's level parameters.** The theorem
step checks it (`ValueFrontRunJ`); `EnvWF` records it for every other stored term. -/
def ThmLevels (env : Env md) : Prop :=
  ∀ n cv v, env.find? n = some (.thmInfo cv v) → v.allLevelParamsDefined cv.levelParams = true

/-- **The stored terms mention only their constant's level parameters**, what the transport
reads of it: types, definition and theorem values, rule right-hand sides with their nested
levels and pins, projection bodies; a canonical rule's constructor parameters are among the
recursor's, and an η-rescue rule's constructor has its family's. -/
structure LvStore (env : Env md) : Prop where
  type : ∀ {k : Key md} {c : ConstantInfo md}, env.find? k = some c →
    c.toConstantVal.type.allLevelParamsDefined c.toConstantVal.levelParams = true
  defn : ∀ {k : Key md} {cv : ConstantVal md} {v : Expr md} {h : ReducibilityHint},
    env.find? k = some (.defnInfo cv v h) → v.allLevelParamsDefined cv.levelParams = true
  thm : ∀ {k : Key md} {cv : ConstantVal md} {v : Expr md},
    env.find? k = some (.thmInfo cv v) → v.allLevelParamsDefined cv.levelParams = true
  rhs : ∀ {k : Key md} {cv : ConstantVal md} {mI rP : Nat} {rules : List (RecRule md)},
    env.find? k = some (.recInfo cv mI rP rules) → ∀ rl ∈ rules,
      rl.rhs.allLevelParamsDefined cv.levelParams = true ∧
      ∀ lvls pins, rl.fire = .nested lvls pins →
        (∀ l ∈ lvls, l.allParamsDefined cv.levelParams = true) ∧
        ∀ p ∈ pins, p.allLevelParamsDefined cv.levelParams = true
  plain : ∀ {k : Key md} {cv : ConstantVal md} {mI rP : Nat} {rules : List (RecRule md)},
    env.find? k = some (.recInfo cv mI rP rules) → ∀ rl ∈ rules, rl.fire = .plain →
      ∀ {cvj : ConstantVal md} {nP nF : Nat}, env.find? rl.ctor = some (.ctorInfo cvj nP nF) →
        ∀ p ∈ cvj.levelParams, p ∈ cv.levelParams
  eta : ∀ {k : Key md} {cv : ConstantVal md} {mI rP : Nat} {rl : RecRule md},
    env.find? k = some (.recInfo cv mI rP [rl]) → rl.eta = true →
      ∀ {cvj : ConstantVal md} {nP nF : Nat} {T : Key md} {tus : List Level}
        {cvT : ConstantVal md} {caps : IndCaps md},
        env.find? rl.ctor = some (.ctorInfo cvj nP nF) →
        (cvj.type.piResult).getAppFn = .const T tus →
        env.find? T = some (.indInfo cvT caps) → cvj.levelParams = cvT.levelParams
  proj : ∀ {sn : Key md} {i : Nat} {entry : ProjEntry md},
    env.findProj? sn i = some entry →
      entry.body.allLevelParamsDefined entry.levelParams = true

/-- **The stored terms are arity-correct.** -/
structure StoreAr (env : Env md) : Prop where
  type : ∀ {k : Key md} {c : ConstantInfo md}, env.find? k = some c →
    Expr.arOk env c.toConstantVal.type = true
  defn : ∀ {k : Key md} {cv : ConstantVal md} {v : Expr md} {h : ReducibilityHint},
    env.find? k = some (.defnInfo cv v h) → Expr.arOk env v = true
  thm : ∀ {k : Key md} {cv : ConstantVal md} {v : Expr md},
    env.find? k = some (.thmInfo cv v) → Expr.arOk env v = true
  rhs : ∀ {k : Key md} {cv : ConstantVal md} {mI rP : Nat} {rules : List (RecRule md)},
    env.find? k = some (.recInfo cv mI rP rules) → ∀ rl ∈ rules,
      Expr.arOk env rl.rhs = true ∧
      ∀ lvls pins, rl.fire = .nested lvls pins → ∀ p ∈ pins, Expr.arOk env p = true
  proj : ∀ {sn : Key md} {i : Nat} {entry : ProjEntry md},
    env.findProj? sn i = some entry → Expr.arOk env entry.body = true
  /-- the `Bool` values a `Nat` comparison folds to take no level parameters -/
  bool : ∀ {n : Key md} {ci : ConstantInfo md}, (n = boolTrueName ∨ n = boolFalseName) →
    env.find? n = some ci → ci.toConstantVal.levelParams = []

namespace LvStore

private theorem find?_mem'' {env : Env md} {n : Key md} {ci : ConstantInfo md}
    (h : env.find? n = some ci) : ci ∈ env.consts := by
  unfold Env.find? at h
  exact List.mem_of_find?_eq_some h

theorem allLevelParamsDefined_getAppFn {ps : List LevelParam} :
    ∀ {e : Expr md}, e.allLevelParamsDefined ps = true →
      e.getAppFn.allLevelParamsDefined ps = true := by
  intro e
  induction e with
  | app f a ihf _ =>
    intro h
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    exact ihf h.1
  | _ => intro h; exact h

/-- **The store invariant and `ThmLevels` give `LvStore`.** -/
theorem of {env : Env md} (hS : Open.StoreInv env) (hT : ThmLevels env) : LvStore env where
  type := fun hf => (hS.wf _ (find?_mem'' hf)).2.1
  defn := fun hf => ((hS.wf _ (find?_mem'' hf)).2.2.2.2.1 _ _ _ rfl).2.1
  thm := fun hf => hT _ _ _ hf
  rhs := fun hf rl hrl => by
    have hr := (hS.wf _ (find?_mem'' hf)).2.2.2.2.2.1 _ _ _ _ rfl rl hrl
    exact ⟨hr.2.1, fun lvls pins hfire =>
      ⟨(hr.2.2.2.2 lvls pins hfire).2.1,
        fun p hp => ((hr.2.2.2.2 lvls pins hfire).2.2.1 p hp).2.1⟩⟩
  plain := fun {k cv mI rP rules} hf rl hrl hfire {cvj nP nF} hc p hp => by
    obtain ⟨pre, dom, body, bm, D, hs, hdom, -⟩ := hS.recPlain hf hrl hfire hc
    have hty : cv.type.allLevelParamsDefined cv.levelParams = true :=
      (hS.wf _ (find?_mem'' hf)).2.1
    have hb := Expr.allLevelParamsDefined_stripPis_body mI hs hty
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hb
    have hd := allLevelParamsDefined_getAppFn hb.1.1
    rw [hdom] at hd
    simp only [Expr.allLevelParamsDefined, List.all_eq_true] at hd
    have := hd (.param p) (List.mem_map.mpr ⟨p, hp, rfl⟩)
    simpa [Level.allParamsDefined] using this
  eta := fun {k cv mI rP rl} hf hE {cvj nP nF T tus cvT caps} hc hpi hT' => by
    obtain ⟨cvj', cnP', cnF', T', us', cvT', caps', hc', hpi', hT'', -, -, -, hlps⟩ :=
      hS.recEta hf (List.mem_singleton.mpr rfl) hE
    rw [hc] at hc'
    obtain ⟨rfl, rfl, rfl⟩ := ConstantInfo.ctorInfo.inj (Option.some.inj hc')
    rw [hpi] at hpi'
    obtain ⟨rfl, rfl⟩ := Expr.const.inj hpi'
    rw [hT'] at hT''
    obtain ⟨rfl, rfl⟩ := ConstantInfo.indInfo.inj (Option.some.inj hT'')
    exact hlps
  proj := fun {_ i _} hent => by
    obtain ⟨tbl, hf, hi, rfl⟩ := Env.findProj?_some hent
    obtain ⟨hsz, hb⟩ := (hS.wf _ (find?_mem'' hf)).2.2.2.2.2.2.1 tbl rfl
    have hi' : i < tbl.bodies.size := hsz ▸ hi
    have hget : tbl.bodies[i]? = some tbl.bodies[i] := by simp [hi']
    have hbody : (tbl.entry i).body = tbl.bodies[i] := by
      simp [ProjTable.entry, hi']
    rw [hbody]
    exact (hb i _ hget).2.1

end LvStore

/-! ## Composition with a stored instantiation -/

namespace LevelRen

/-- **Composition of level instantiations** on a term whose parameters the inner one covers. -/
theorem inst_comp {ks : List LevelParam} {ws : List Level}
    {ps : List LevelParam} {us : List Level} (hl : us.length = ps.length) :
    ∀ {e : Expr md}, e.allLevelParamsDefined ps = true →
      (e.instantiateLevelParams ps us).instantiateLevelParams ks ws =
        e.instantiateLevelParams ps (us.map (Level.subst ks ws)) := by
  intro e
  induction e with
  | bvar _ => intro _; rfl
  | fvar idx ty ih =>
    intro h
    simp only [Expr.allLevelParamsDefined] at h
    simp only [Expr.instantiateLevelParams, ih h]
  | sort u =>
    intro h
    simp only [Expr.allLevelParamsDefined] at h
    simp only [Expr.instantiateLevelParams, Level.subst_subst (ks := ks) (us := ws) hl h]
  | const n ls =>
    intro h
    simp only [Expr.allLevelParamsDefined, List.all_eq_true] at h
    simp only [Expr.instantiateLevelParams, List.map_map]
    congr 1
    exact List.map_congr_left fun u hu => Level.subst_subst (ks := ks) (us := ws) hl (h u hu)
  | app f a ihf iha =>
    intro h
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.instantiateLevelParams, ihf h.1, iha h.2]
  | lam ty body m iht ihb =>
    intro h
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.instantiateLevelParams, iht h.1.1, ihb h.1.2,
      Level.substPW_comp (ks := ks) (us := ws) hl h.2]
  | forallE ty body m iht ihb =>
    intro h
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.instantiateLevelParams, iht h.1.1, ihb h.1.2,
      Level.substPW_comp (ks := ks) (us := ws) hl h.2]
  | letE ty val body l iht ihv ihb =>
    intro h
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.instantiateLevelParams, iht h.1.1, ihv h.1.2, ihb h.2]
  | lit _ => intro _; rfl
  | proj s i e ih =>
    intro h
    simp only [Expr.allLevelParamsDefined] at h
    simp only [Expr.instantiateLevelParams, ih h]

/-- A level of the stored parameters, instantiated and then renamed. -/
theorem subst_comp_param {ks : List LevelParam} {ws : List Level}
    {ps : List LevelParam} {us : List Level} (hl : us.length = ps.length) {p : LevelParam}
    (hp : p ∈ ps) :
    Level.subst ks ws (Level.subst ps us (.param p)) =
      Level.subst ps (us.map (Level.subst ks ws)) (.param p) :=
  Level.subst_subst hl (by simpa [Level.allParamsDefined] using hp)

end LevelRen

end Ix.Kernel
