import IxVMRefinement.Iota.Kernel
import IxVMRefinement.Core.Certs
import IxC.Kernel.Verify.InstLevels
import IxC.Kernel.Verify.PropWhen
import IxC.Kernel.Verify.Shift
import IxC.Kernel.Verify.InstList

/-! # Kernel-side lemmas of the ι step: level instantiation, spines, the major premise's domain

* **Positional levels**: a stored term with its level parameters renamed to positions
  (`posOf`), instantiated at the positions, is the term instantiated at its parameters
  (`posOf_inst`), when its parameters are its constant's.
* **Spines**: instantiating bound variables, or level parameters, keeps a constant head and
  maps the arguments (`instList_constHead`); a bound variable instantiated by closed terms is
  the term at its position (`instList_bvar`).
* **The nested rule's pins**: a pin lifted over the index binders and instantiated by the
  spine before the major premise is the pin instantiated by the rule's prefix
  (`instList_lift_append`). -/

namespace IxVM.Refinement.Core

open Ix.Kernel (Level LevelParam)
open Ix.Kernel.Expr (instantiateList instantiateList_nil instantiateList_eq_self
  liftLooseBVars looseBVarsBounded)

set_option linter.unusedVariables false

/-! ## Levels -/

/-- The positional parameter list, at its positions, is any list of its length. -/
theorem subst_go_range' (us : List Level) :
    ∀ (n s i : Nat) (hl : us.length = n) (h1 : s ≤ i) (h2 : i < s + n),
      Level.subst.go (List.range' s n) us i =
        us[i - s]'(by have := Nat.sub_lt_left_of_lt_add h1 h2; omega)
  | 0, s, i, _, h1, h2 => by omega
  | n + 1, s, i, hl, h1, h2 => by
    cases us with
    | nil => simp at hl
    | cons u us =>
      rw [List.range'_succ]
      simp only [Level.subst.go]
      by_cases hs : s = i
      · subst hs
        simp
      · rw [ite_eq_right hs]
        have := subst_go_range' us n (s + 1) i (by simpa using hl) (by omega) (by omega)
        rw [this]
        have e : i - s = (i - (s + 1)) + 1 := by omega
        simp only [e, List.getElem_cons_succ]

theorem posLevels_subst (us : List Level) (ps : List LevelParam) (hl : us.length = ps.length) :
    (posLevels ps).map (Level.subst (List.range ps.length) us) = us := by
  apply List.ext_getElem
  · simp [posLevels, hl]
  · intro i h1 h2
    simp only [posLevels, List.getElem_map, List.getElem_range, Level.subst]
    rw [List.range_eq_range', subst_go_range' us ps.length 0 i hl (by omega)
      (by simp [posLevels] at h1; omega)]
    simp

/-- **Composition of level instantiations**, when the term's parameters are the inner ones. -/
theorem inst_inst {ps ks : List LevelParam} {vs us : List Level} (hl : vs.length = ps.length) :
    ∀ (e : KExpr), e.allLevelParamsDefined ps = true →
      (e.instantiateLevelParams ps vs).instantiateLevelParams ks us =
        e.instantiateLevelParams ps (vs.map (Level.subst ks us)) := by
  intro e
  induction e with
  | bvar i => intro _; rfl
  | fvar idx ty ih =>
    intro h
    simp only [Ix.Kernel.Expr.allLevelParamsDefined] at h
    simp only [Ix.Kernel.Expr.instantiateLevelParams, ih h]
  | sort u =>
    intro h
    simp only [Ix.Kernel.Expr.allLevelParamsDefined] at h
    simp only [Ix.Kernel.Expr.instantiateLevelParams, Level.subst_subst hl h]
  | const n ls =>
    intro h
    simp only [Ix.Kernel.Expr.allLevelParamsDefined, List.all_eq_true] at h
    simp only [Ix.Kernel.Expr.instantiateLevelParams, List.map_map]
    congr 1
    apply List.map_congr_left
    intro u hu
    exact Level.subst_subst hl (h u hu)
  | app f a ihf iha =>
    intro h
    simp only [Ix.Kernel.Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Ix.Kernel.Expr.instantiateLevelParams, ihf h.1, iha h.2]
  | lam ty b m iht ihb =>
    intro h
    simp only [Ix.Kernel.Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Ix.Kernel.Expr.instantiateLevelParams, iht h.1.1, ihb h.1.2,
      Level.substPW_comp hl h.2]
  | forallE ty b m iht ihb =>
    intro h
    simp only [Ix.Kernel.Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Ix.Kernel.Expr.instantiateLevelParams, iht h.1.1, ihb h.1.2,
      Level.substPW_comp hl h.2]
  | letE ty v b m iht ihv ihb =>
    intro h
    simp only [Ix.Kernel.Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Ix.Kernel.Expr.instantiateLevelParams, iht h.1.1, ihv h.1.2, ihb h.2]
  | lit l => intro _; rfl
  | proj s i e ih =>
    intro h
    simp only [Ix.Kernel.Expr.allLevelParamsDefined] at h
    simp only [Ix.Kernel.Expr.instantiateLevelParams, ih h]

/-- **Positional levels**: the loaded form of a stored term, instantiated at the positions, is
the stored term instantiated at its constant's parameters. -/
theorem posOf_inst {ps : List LevelParam} {us : List Level} (hl : us.length = ps.length)
    {e : KExpr} (h : e.allLevelParamsDefined ps = true) :
    (posOf ps e).instantiateLevelParams (List.range ps.length) us =
      e.instantiateLevelParams ps us := by
  unfold posOf
  rw [inst_inst (by simp [posLevels]) e h, posLevels_subst us ps hl]

/-! ## Spines under instantiation -/

theorem mkAppN_getApp : ∀ (e : KExpr),
    Ix.Kernel.Expr.mkAppN e.getAppFn e.getAppArgs = e := by
  intro e
  induction e with
  | app f a ihf _ =>
    simp only [Ix.Kernel.Expr.getAppFn, Ix.Kernel.Expr.getAppArgs]
    rw [← mkAppN_mkAppN, ihf]
    rfl
  | _ => rfl

theorem instList_mkAppN (vs : List KExpr) (d : Nat) :
    ∀ (as : List KExpr) (f : KExpr),
      (Ix.Kernel.Expr.mkAppN f as).instantiateList vs d =
        Ix.Kernel.Expr.mkAppN (f.instantiateList vs d) (as.map (·.instantiateList vs d))
  | [], _ => rfl
  | a :: as, f => by
    show (Ix.Kernel.Expr.mkAppN (.app f a) as).instantiateList vs d = _
    rw [instList_mkAppN vs d as (.app f a)]
    simp only [instantiateList, List.map_cons]
    rfl

/-- **A constant-headed spine, instantiated**: the head stays, the arguments are instantiated. -/
theorem instList_constHead {e : KExpr} {n : KKey} {ls : List KLevel}
    (he : e.getAppFn = .const n ls) (vs : List KExpr) (d : Nat) :
    (e.instantiateList vs d).getAppFn = .const n ls ∧
      (e.instantiateList vs d).getAppArgs = e.getAppArgs.map (·.instantiateList vs d) := by
  have h := instList_mkAppN vs d e.getAppArgs e.getAppFn
  rw [mkAppN_getApp, he] at h
  rw [h, getAppFn_mkAppN, getAppArgs_mkAppN]
  simp only [instantiateList]
  exact ⟨rfl, by simp [Ix.Kernel.Expr.getAppArgs]⟩

/-- A bound variable at or above the depth, instantiated. -/
theorem bvar_inst_ge {vs : List KExpr} {d j : Nat} (h : d ≤ j) :
    (Ix.Kernel.Expr.bvar j).instantiateList vs d =
      if h' : j - d < vs.length then vs[j - d].instantiateList (vs.take (j - d)) d
      else .bvar (j - vs.length) := by
  simp only [instantiateList]
  rw [ite_eq_right (show ¬ j < d by omega)]

/-- A bound variable instantiated by closed terms is the term at its position. -/
theorem instList_bvar {vs : List KExpr} (hc : ∀ v ∈ vs, v.looseBVarsBounded 0 = true)
    {j : Nat} (hj : j < vs.length) : (Ix.Kernel.Expr.bvar j).instantiateList vs 0 = vs[j] := by
  rw [bvar_inst_ge (Nat.zero_le j)]
  simp only [Nat.sub_zero, hj, ↓reduceDIte]
  exact instantiateList_eq_self (hc _ (List.getElem_mem hj))

/-- Instantiating level parameters keeps the domain of a binder. -/
theorem piDomAt_instLP (ks : List LevelParam) (us : List KLevel) :
    ∀ (n : Nat) (T D : KExpr), piDomAt n T = some D →
      piDomAt n (T.instantiateLevelParams ks us) = some (D.instantiateLevelParams ks us) := by
  intro n
  induction n with
  | zero =>
    intro T D hT
    cases T with
    | forallE ty body m =>
      simp only [piDomAt, Option.some.injEq] at hT
      subst hT
      simp [piDomAt, Ix.Kernel.Expr.instantiateLevelParams]
    | _ => simp [piDomAt] at hT
  | succ n ih =>
    intro T D hT
    cases T with
    | forallE ty body m =>
      simp only [piDomAt] at hT
      simp only [Ix.Kernel.Expr.instantiateLevelParams, piDomAt]
      exact ih body D hT
    | _ => simp [piDomAt] at hT

/-! ## Lifting -/

theorem instLP_lift (ks : List LevelParam) (us : List KLevel) (n : Nat) :
    ∀ (e : KExpr) (c : Nat),
      (e.liftLooseBVars n c).instantiateLevelParams ks us =
        (e.instantiateLevelParams ks us).liftLooseBVars n c := by
  intro e
  induction e with
  | bvar i =>
    intro c
    by_cases h : i ≥ c <;> simp [liftLooseBVars, Ix.Kernel.Expr.instantiateLevelParams, h]
  | fvar idx ty _ => intro c; rfl
  | sort u => intro c; rfl
  | const n ls => intro c; rfl
  | app f a ihf iha =>
    intro c
    simp only [liftLooseBVars, Ix.Kernel.Expr.instantiateLevelParams, ihf, iha]
  | lam ty b m iht ihb =>
    intro c
    simp only [liftLooseBVars, Ix.Kernel.Expr.instantiateLevelParams, iht, ihb]
  | forallE ty b m iht ihb =>
    intro c
    simp only [liftLooseBVars, Ix.Kernel.Expr.instantiateLevelParams, iht, ihb]
  | letE ty v b m iht ihv ihb =>
    intro c
    simp only [liftLooseBVars, Ix.Kernel.Expr.instantiateLevelParams, iht, ihv, ihb]
  | lit l => intro c; rfl
  | proj s i e ih =>
    intro c
    simp only [liftLooseBVars, Ix.Kernel.Expr.instantiateLevelParams, ih]

/-- **A term lifted over `xs.length` binders and instantiated by `xs ++ zs`** (closed terms) is
the term instantiated by `zs`. -/
theorem instList_lift_append {xs zs : List KExpr}
    (hc : ∀ v ∈ xs ++ zs, v.looseBVarsBounded 0 = true) :
    ∀ (e : KExpr) (d : Nat),
      (e.liftLooseBVars xs.length d).instantiateList (xs ++ zs) d = e.instantiateList zs d := by
  have hcl : ∀ (v : KExpr) (d : Nat), v ∈ xs ++ zs → ∀ ws : List KExpr,
      v.instantiateList ws d = v := fun v d hv ws =>
    instantiateList_eq_self (Ix.Kernel.Expr.looseBVarsBounded_mono (Nat.zero_le d) (hc v hv))
  intro e
  induction e with
  | bvar i =>
    intro d
    by_cases hid : d ≤ i
    · simp only [liftLooseBVars, show i ≥ d from hid, ↓reduceIte]
      rw [bvar_inst_ge (show d ≤ i + xs.length by omega), bvar_inst_ge hid]
      by_cases hin : i - d < zs.length
      · have h1 : i + xs.length - d < (xs ++ zs).length := by
          simp only [List.length_append]; omega
        simp only [h1, hin, ↓reduceDIte]
        rw [hcl _ d (List.getElem_mem _),
          hcl _ d (List.mem_append_right _ (List.getElem_mem _))]
        simp only [List.getElem_append_right (show xs.length ≤ i + xs.length - d by omega),
          show i + xs.length - d - xs.length = i - d by omega]
      · have h1 : ¬ (i + xs.length - d < xs.length + zs.length) := by omega
        simp only [List.length_append, h1, hin, ↓reduceDIte, Ix.Kernel.Expr.bvar.injEq]
        omega
    · simp only [liftLooseBVars, show ¬ (i ≥ d) by omega, ↓reduceIte, instantiateList,
        show i < d by omega]
  | fvar idx ty _ => intro d; simp only [liftLooseBVars, instantiateList]
  | sort u => intro d; simp only [liftLooseBVars, instantiateList]
  | const n ls => intro d; simp only [liftLooseBVars, instantiateList]
  | app f a ihf iha =>
    intro d
    simp only [liftLooseBVars, instantiateList, ihf, iha]
  | lam ty b m iht ihb =>
    intro d
    simp only [liftLooseBVars, instantiateList, iht, ihb]
  | forallE ty b m iht ihb =>
    intro d
    simp only [liftLooseBVars, instantiateList, iht, ihb]
  | letE ty v b m iht ihv ihb =>
    intro d
    simp only [liftLooseBVars, instantiateList, iht, ihv, ihb]
  | lit l => intro d; simp only [liftLooseBVars, instantiateList]
  | proj s i e ih =>
    intro d
    simp only [liftLooseBVars, instantiateList, ih]

/-! ## Lists and levels -/

theorem evalEqList_length {φ : LevelParam → Nat} :
    ∀ {us vs : List KLevel}, Level.EvalEqList φ us vs → us.length = vs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp [evalEqList_length h.2]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem LvEqList.length_eq {us vs : List KLevel} (h : LvEqList us vs) : us.length = vs.length :=
  evalEqList_length (h fun _ => 0)

/-- **The rule found by its constructor key**: in a rule list with distinct keys, the rule
holding a key. -/
theorem find_ctor_of_nodup {rls : List (Ix.Kernel.RecRule .anon)}
    (hnd : (rls.map (·.ctor)).Nodup) {rl : Ix.Kernel.RecRule .anon} (hrl : rl ∈ rls) :
    rls.find? (fun r' => r'.ctor == rl.ctor) = some rl := by
  induction rls with
  | nil => simp at hrl
  | cons r rs ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rcases List.mem_cons.mp hrl with rfl | hrl
    · simp
    · have hne : r.ctor ≠ rl.ctor := fun e => hnd.1 ⟨rl, hrl, e.symm⟩
      rw [List.find?_cons_of_neg (by simpa using hne)]
      exact ih hnd.2 hrl

end IxVM.Refinement.Core
