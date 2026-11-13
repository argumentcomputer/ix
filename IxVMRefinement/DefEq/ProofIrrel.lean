import IxVMRefinement.DefEq.Basic
import IxVMRefinement.Core.RomBound
import IxVMRefinement.Lib.Words
import IxVMRefinement.Levels.Spec
import IxVMRefinement.Subst.Spine
import IxC.Kernel.Verify.PropRead
import IxC.Kernel.Verify.InstLevels
import IxC.Kernel.Verify.PropWhen

/-! # Step lemma of `KernelDefEq::try_proof_irrel`

* `level_zero_at`: tests whether a stored level (directly, or instantiated at the use's levels by
  `level_inst_params`) equates with `Zero` (`levelEqual_eq_true_sound`).
* `peel_never_pis`: peels `k` syntactic `∀` binders whose binder levels pass `level_is_not_zero`
  (`Expr.peelNeverPis`, via `Level.isNeverZero_eq_isNever`).
* `residual_class` and `type_sort_class`: read the three-valued sort class (`0` not `Prop`, `1`
  always `Prop`, `2` unknown) of a type, either in place (`inst = 0`, for an opened variable's
  declared type) or instantiated at a constant's use levels (`inst = 1`, for a constant's stored
  positional type `posOf`).
* `proof_class`: reads the three-valued proof class of a term; answer `1` establishes
  `Ix.Kernel.isProofFast c.env.find? E = true`.
* `try_proof_irrel_slow` and `try_proof_irrel`: answer `1` on both fast classifications gives
  `DefEq.proofFast`; falling through to `try_proof_irrel_slow` infers both io-grade types, checks
  that the first is a proposition (`is_prop_type`), and equates the two types (`DefEq.proofIrrelTy`).
-/

namespace IxVM.Refinement.Core.DefEqAux

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Class answers and small field arithmetic -/

/-- A three-valued fast-classification answer: `0` (definitely no), `1` (definitely yes), or `2`
(unknown). -/
def IsClassVal (v : SourceValue F) : Prop :=
  v = .field 0 ∨ v = .field 1 ∨ v = .field 2

private theorem val_natCast_small {m : Nat} (hm : m < 9223372036854775808) :
    ZMod.val (m : F) = m :=
  ZMod.val_natCast_of_lt (Nat.lt_of_lt_of_le hm (by decide))

private theorem natCast_inj_small {a b : Nat} (ha : a < 9223372036854775808)
    (hb : b < 9223372036854775808) (h : (a : F) = (b : F)) : a = b := by
  have h1 := val_natCast_small ha
  have h2 := val_natCast_small hb
  rw [h] at h1
  omega

private theorem lt_of_lt_2_39 {m : Nat} (hm : m < 2 ^ 39) : m < 9223372036854775808 :=
  Nat.lt_of_lt_of_le hm (by decide)

private theorem sub_field_zero {a b : F}
    (op : evalBinOp .sub (.field a : SourceValue F) (.field b) = .ok (.field 0)) : a = b := by
  simp only [evalBinOp, Except.ok.injEq, Value.field.injEq] at op
  exact sub_eq_zero.mp op

theorem field_two_ne_one : (Value.field (2 : F) : SourceValue F) ≠ .field 1 := by
  intro h
  injection h with h
  have h' : ((2 : Nat) : F) = ((1 : Nat) : F) := by
    rw [Nat.cast_ofNat, Nat.cast_one]
    exact h
  have := natCast_inj_small (by omega) (by omega) h'
  omega

theorem isClassVal_ite (p : Prop) [Decidable p] :
    IsClassVal (.field (if p then 1 else 0)) := by
  by_cases hp : p <;> simp [IsClassVal, hp]

private theorem isClassVal_to_nat {v : SourceValue F} (hv : IsClassVal v) :
    ∃ n : Nat, n ≤ 2 ∧ v = .field (n : F) := by
  rcases hv with rfl | rfl | rfl
  · exact ⟨0, by omega, by rw [Nat.cast_zero]⟩
  · exact ⟨1, by omega, by rw [Nat.cast_one]⟩
  · exact ⟨2, by omega, by rw [Nat.cast_ofNat]⟩

/-- Two classification answers whose product is `1` are both `1`. -/
theorem mul_class_eq_one {x y : SourceValue F} (hx : IsClassVal x) (hy : IsClassVal y)
    (op : evalBinOp .mul x y = .ok (.field 1)) : x = .field 1 ∧ y = .field 1 := by
  obtain ⟨a, ha, rfl⟩ := isClassVal_to_nat hx
  obtain ⟨b, hb, rfl⟩ := isClassVal_to_nat hy
  simp only [evalBinOp, Except.ok.injEq, Value.field.injEq] at op
  have hm : ((a * b : Nat) : F) = ((1 : Nat) : F) := by
    rw [Nat.cast_mul, Nat.cast_one]
    exact op
  have hab_lt : a * b < 9223372036854775808 := by
    rcases (show a = 0 ∨ a = 1 ∨ a = 2 by omega) with rfl | rfl | rfl <;> omega
  have hab : a * b = 1 := natCast_inj_small hab_lt (by omega) hm
  have hab1 : a = 1 ∧ b = 1 := by
    rcases (show a = 0 ∨ a = 1 ∨ a = 2 by omega) with rfl | rfl | rfl <;> omega
  rw [hab1.1, hab1.2, Nat.cast_one]
  exact ⟨rfl, rfl⟩

/-! ## Heap and list helpers -/

private theorem repKLevel_store_zero (h : Heap F) :
    RepKLevel (h ++ [.construct IxVM.Refinement.KernelLevels.klevelEnum "Zero" []]) .zero
      (.ptr (.enum IxVM.Refinement.KernelLevels.klevelEnum) h.length) :=
  RepKLevel.zero (by simp)

theorem pi_tml_length {c : Ctx} {d : Nat} {Γ : Nat → KExpr} {As : List KExpr}
    {l r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::length<&KernelTypes::KExprNode>» [l] h r h' cs)
    (hl : c.tml d Γ h As l) : r = .field (As.length : F) ∧ h' = h :=
  Lib.Lists.length_spec (t := .ptr (.named "KernelTypes::KExprNode" [])) (R := TmE c.κ d Γ)
    (by rw [Obs.Names.«Lists::length<&KernelTypes::KExprNode>».symbol]; exact ev)
    (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact hl)

theorem pi_lvl_length {ls : List KLevel} {l r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::length<&KernelTypes::KLevelNode>» [l] h r h' cs)
    (hl : RepKLevelList h ls l) :
    r = .field (ls.length : F) ∧ h' = h := by
  have e : Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>» =
      IxVM.Refinement.KernelLevels.klevelListEnum := klevelListEnum_eq
  exact Lib.Lists.length_spec (t := .ptr (.named "KernelTypes::KLevelNode" [])) (R := RepKLevel)
    (by rw [Obs.Names.«Lists::length<&KernelTypes::KLevelNode>».symbol]; exact ev)
    (by rw [Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>».symbol, e]; exact hl)

/-- Every `CIRep`-represented constant is a non-table entry with bounded, positional-permuted
level parameters. -/
theorem ciRep_info {κ : _root_.Address → KKey} {h : Heap F} {v : SourceValue F}
    {ci : Ix.Kernel.ConstantInfo .anon} (r : CIRep κ h v ci) :
    ci.isTowerEntry = false ∧
      ci.toConstantVal.levelParams.length < 4294967296 ∧
      ci.toConstantVal.levelParams.Perm (List.range ci.toConstantVal.levelParams.length) := by
  cases r with
  | axio hv | opaq hv | defn hv _ | thm hv _ | induct hv _ _ | ctor hv _ _ _ _
  | recr hv _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨rfl, hv.2.1, hv.2.2.1⟩
  | quot hv hk =>
    refine ⟨?_, hv.2.1, hv.2.2.1⟩
    rcases hk with ⟨-, _, _, rfl⟩ | ⟨-, _, _, _, rfl⟩ | ⟨-, _, _, _, _, rfl⟩ |
      ⟨-, _, _, _, _, rfl⟩ <;> rfl

/-! ## `PropWhen`, positional levels, and spines -/

theorem isProp_iff {pw : Ix.Kernel.PropWhen} :
    pw.isProp = true ↔ pw = .ifAllZero [] :=
  beq_iff_eq

theorem isProp_always : (Ix.Kernel.PropWhen.ifAllZero []).isProp = true :=
  isProp_iff.mpr rfl

theorem zeronessOf_eq_always_of_eval_zero {u : KLevel}
    (h : ∀ φ, Ix.Kernel.Level.eval φ u = 0) :
    u.zeronessOf = .ifAllZero [] :=
  Ix.Kernel.PropWhen.eq_of_holds fun φ => by
    rw [Ix.Kernel.PropWhen.zeronessOf_sound, Ix.Kernel.PropWhen.holds_ifAllZero, h φ]
    rfl

private theorem substPW_never (ks : List Ix.Kernel.LevelParam) (vs : List KLevel) :
    Ix.Kernel.Level.substPW ks vs .never = .never :=
  Ix.Kernel.PropWhen.eq_of_holds fun φ => by
    rw [Ix.Kernel.Level.holds_substPW, Ix.Kernel.PropWhen.holds_never,
      Ix.Kernel.PropWhen.holds_never]

private theorem getElem?_subst_go_range_pi :
    ∀ (s : Nat) (us : List KLevel) (i : Nat), s ≤ i → i < s + us.length →
      us[i - s]? = some (Ix.Kernel.Level.subst.go (List.range' s us.length) us i)
  | s, [], i, h1, h2 => by
    have : ([] : List KLevel).length = 0 := rfl
    omega
  | s, u :: us, i, h1, h2 => by
    show _ = some (if s = i then u else
      Ix.Kernel.Level.subst.go (List.range' (s + 1) us.length) us i)
    have hl : (u :: us).length = us.length + 1 := rfl
    by_cases h : s = i
    · subst h
      rw [ite_eq_left rfl, Nat.sub_self, List.getElem?_cons_zero]
    · rw [ite_eq_right h, show i - s = i - (s + 1) + 1 by omega, List.getElem?_cons_succ]
      exact getElem?_subst_go_range_pi (s + 1) us i (by omega) (by omega)

private theorem getElem?_eq_subst_go_range_pi {us : List KLevel} {i : Nat} (hi : i < us.length) :
    us[i]? = some (Ix.Kernel.Level.subst.go (List.range us.length) us i) := by
  have := getElem?_subst_go_range_pi 0 us i (Nat.zero_le i) (by omega)
  rwa [Nat.sub_zero, ← List.range_eq_range'] at this

private theorem posLevels_map_subst_pi {ps : List Ix.Kernel.LevelParam} {us : List KLevel}
    (hlen : us.length = ps.length) :
    (posLevels ps).map (Ix.Kernel.Level.subst (List.range us.length) us) = us := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_map]
  by_cases hi : i < us.length
  · have h1 : (posLevels ps)[i]? = some (Ix.Kernel.Level.param i) := by
      rw [posLevels, List.getElem?_map, List.getElem?_range (by omega)]; rfl
    rw [h1, getElem?_eq_subst_go_range_pi hi]; rfl
  · have h1 : (posLevels ps)[i]? = none := by
      rw [List.getElem?_eq_none_iff, posLevels, List.length_map, List.length_range]
      omega
    have h2 : us[i]? = none := List.getElem?_eq_none_iff.mpr (by omega)
    rw [h1, h2]; rfl

private theorem subst_go_of_not_mem_pi :
    ∀ {ks : List Ix.Kernel.LevelParam} {vs : List KLevel} {p : Ix.Kernel.LevelParam}, p ∉ ks →
      Ix.Kernel.Level.subst.go ks vs p = .param p
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | k :: ks, v :: vs, p, h => by
    show (if k = p then v else Ix.Kernel.Level.subst.go ks vs p) = _
    rw [ite_eq_right (fun e => h (List.mem_cons.mpr (Or.inl e.symm)))]
    exact subst_go_of_not_mem_pi (fun hm => h (List.mem_cons.mpr (Or.inr hm)))

theorem subst_posLevels_perm_pi {ps : List Ix.Kernel.LevelParam} {us : List KLevel}
    (hperm : ps.Perm (List.range ps.length)) (hlen : us.length = ps.length) :
    ∀ l : KLevel, Ix.Kernel.Level.subst (List.range us.length) us
      (Ix.Kernel.Level.subst ps (posLevels ps) l) = Ix.Kernel.Level.subst ps us l := by
  intro l
  induction l with
  | zero => rfl
  | succ l ih => simp only [Ix.Kernel.Level.subst, ih]
  | max l r ihl ihr => simp only [Ix.Kernel.Level.subst, ihl, ihr]
  | imax l r ihl ihr => simp only [Ix.Kernel.Level.subst, ihl, ihr]
  | param p =>
    show Ix.Kernel.Level.subst (List.range us.length) us
        (Ix.Kernel.Level.subst.go ps (posLevels ps) p) = Ix.Kernel.Level.subst.go ps us p
    by_cases hp : p ∈ ps
    · have hl : (posLevels ps).length = ps.length := by
        rw [posLevels, List.length_map, List.length_range]
      have h := Ix.Kernel.Level.subst_go_map
        (Ix.Kernel.Level.subst (List.range us.length) us) ps (posLevels ps) p hp hl
      rw [posLevels_map_subst_pi hlen] at h
      exact h.symm
    · have hp' : p ∉ List.range us.length := by
        rw [hlen]
        exact fun hm => hp (hperm.mem_iff.mpr hm)
      rw [subst_go_of_not_mem_pi (vs := posLevels ps) hp, subst_go_of_not_mem_pi (vs := us) hp]
      exact subst_go_of_not_mem_pi hp'

theorem substPW_posLevels_perm_pi {ps : List Ix.Kernel.LevelParam} {us : List KLevel}
    (hperm : ps.Perm (List.range ps.length)) (hlen : us.length = ps.length)
    (pw : Ix.Kernel.PropWhen) :
    Ix.Kernel.Level.substPW (List.range us.length) us
      (Ix.Kernel.Level.substPW ps (posLevels ps) pw) = Ix.Kernel.Level.substPW ps us pw := by
  apply Ix.Kernel.PropWhen.eq_of_holds
  intro φ
  rw [Ix.Kernel.Level.holds_substPW, Ix.Kernel.Level.holds_substPW,
    Ix.Kernel.Level.holds_substPW]
  congr 1
  funext p
  rw [← Ix.Kernel.Level.eval_subst_go, ← Ix.Kernel.Level.eval_subst_go,
    ← Ix.Kernel.Level.eval_subst]
  exact congrArg (Ix.Kernel.Level.eval φ) (subst_posLevels_perm_pi hperm hlen (.param p))

/-- If `substPW ps' (cus.map (subst ps us)) pw` is `ifAllZero []`, every parameter in `pw` had to
be covered by `ps'` (an uncovered parameter evaluates to `1 ≠ 0` under `fun _ => 1`), so
`substPW_comp` applies without any store invariant. -/
theorem isProp_substPW_comp {ps ps' : List Ix.Kernel.LevelParam}
    {us cus : List KLevel} {pw : Ix.Kernel.PropWhen}
    (hl : cus.length = ps'.length)
    (h : (Ix.Kernel.Level.substPW ps' (cus.map (Ix.Kernel.Level.subst ps us)) pw).isProp = true) :
    (Ix.Kernel.Level.substPW ps us (Ix.Kernel.Level.substPW ps' cus pw)).isProp = true := by
  have heq : Ix.Kernel.Level.substPW ps' (cus.map (Ix.Kernel.Level.subst ps us)) pw =
      .ifAllZero [] := isProp_iff.mp h
  cases pw with
  | never =>
    rw [substPW_never] at heq
    exact absurd heq.symm (Ix.Kernel.PropWhen.ifAllZero_ne_never [])
  | ifAllZero pws =>
    have hdef : (Ix.Kernel.PropWhen.ifAllZero pws).paramsDefined ps' = true := by
      rw [Ix.Kernel.PropWhen.paramsDefined_ifAllZero, List.all_eq_true]
      intro n hn
      rw [List.contains_iff_mem]
      by_contra hnot
      have hh := congrArg (Ix.Kernel.PropWhen.holds (fun _ => 1)) heq
      rw [Ix.Kernel.Level.holds_substPW, Ix.Kernel.PropWhen.holds_ifAllZero,
        Ix.Kernel.PropWhen.holds_ifAllZero] at hh
      have hn0 := List.all_eq_true.mp hh n hn
      rw [← Ix.Kernel.Level.eval_subst_go, subst_go_of_not_mem_pi hnot] at hn0
      exact Bool.false_ne_true hn0
    rw [Ix.Kernel.Level.substPW_comp hl hdef]
    exact h

/-- Peeling `k` `.never`-annotated `∀` binders off `posOf ps T` to a sort comes from peeling `k`
`.never`-annotated `∀` binders off `T` itself. -/
theorem peelNeverPis_posOf_sort_inv {ps : List Ix.Kernel.LevelParam}
    (hperm : ps.Perm (List.range ps.length)) :
    ∀ (k : Nat) {T : KExpr} {u' : KLevel},
      (posOf ps T).peelNeverPis k = some (.sort u') →
      ∃ u, T.peelNeverPis k = some (.sort u) ∧
        u' = Ix.Kernel.Level.subst ps (posLevels ps) u
  | 0, T, u', h => by
    have heq := Ix.Kernel.Expr.peelNeverPis_zero_inv h
    cases T <;>
      simp only [posOf, Ix.Kernel.Expr.instantiateLevelParams, reduceCtorEq,
        Ix.Kernel.Expr.sort.injEq] at heq
    exact ⟨_, rfl, heq.symm⟩
  | k + 1, T, u', h => by
    obtain ⟨dom', body', m', heq, hnev', hb⟩ := Ix.Kernel.Expr.peelNeverPis_succ_inv h
    cases T <;>
      simp only [posOf, Ix.Kernel.Expr.instantiateLevelParams, reduceCtorEq,
        Ix.Kernel.Expr.forallE.injEq] at heq
    case forallE dom body m =>
      obtain ⟨rfl, rfl, rfl⟩ := heq
      have hpm : Ix.Kernel.Level.substPW ps (posLevels ps) m.pw = .never :=
        Ix.Kernel.PropWhen.isNever_iff.mp hnev'
      have hself := substPW_posLevels_perm_pi hperm (us := ps.map .param) (by simp) m.pw
      rw [hpm, substPW_never, Ix.Kernel.Level.substPW_self] at hself
      have hnev : m.pw.isNever = true := by
        rw [← hself]
        exact Ix.Kernel.PropWhen.isNever_never
      obtain ⟨u, hbu, hu'⟩ := peelNeverPis_posOf_sort_inv hperm k hb
      refine ⟨u, ?_, hu'⟩
      simp only [Ix.Kernel.Expr.peelNeverPis, hnev, ↓reduceIte]
      exact hbu

theorem mkAppN_fn_numArgs :
    ∀ (As : List KExpr) (E : KExpr),
      (Ix.Kernel.Expr.mkAppN E As).getAppFn = E.getAppFn ∧
        (Ix.Kernel.Expr.mkAppN E As).numArgs = E.numArgs + As.length
  | [], E => ⟨rfl, by simp [Ix.Kernel.Expr.mkAppN]⟩
  | a :: As, E => by
    obtain ⟨hfn, hnum⟩ := mkAppN_fn_numArgs As (.app E a)
    refine ⟨hfn, ?_⟩
    simp only [Ix.Kernel.Expr.mkAppN, Ix.Kernel.Expr.numArgs, List.length_cons] at hnum ⊢
    omega

private theorem numArgs_instantiateLevelParams (ks : List Ix.Kernel.LevelParam) (vs : List KLevel) :
    ∀ e : KExpr, (e.instantiateLevelParams ks vs).numArgs = e.numArgs := by
  intro e
  induction e <;> simp_all [Ix.Kernel.Expr.instantiateLevelParams, Ix.Kernel.Expr.numArgs]

theorem typeSortPW_of_getAppFn_const (find? : KKey → Option (Ix.Kernel.ConstantInfo .anon))
    {E : KExpr} {I : KKey} {us : List KLevel} (hfn : E.getAppFn = .const I us) :
    Ix.Kernel.typeSortPW find? E = Ix.Kernel.headTypePW find? (.const I us) E.numArgs := by
  cases E <;> simp only [Ix.Kernel.Expr.getAppFn, reduceCtorEq] at hfn <;>
    exact congrArg (fun x => Ix.Kernel.headTypePW find? x _) hfn

theorem typeSortPW_of_getAppFn_fvar (find? : KKey → Option (Ix.Kernel.ConstantInfo .anon))
    {E : KExpr} {idx : Nat} {ty : KExpr} (hfn : E.getAppFn = .fvar idx ty) :
    Ix.Kernel.typeSortPW find? E = Ix.Kernel.headTypePW find? (.fvar idx ty) E.numArgs := by
  cases E <;> simp only [Ix.Kernel.Expr.getAppFn, reduceCtorEq] at hfn <;>
    exact congrArg (fun x => Ix.Kernel.headTypePW find? x _) hfn

theorem proofPW_of_getAppFn_const (find? : KKey → Option (Ix.Kernel.ConstantInfo .anon))
    {E : KExpr} {I : KKey} {us : List KLevel} (hfn : E.getAppFn = .const I us) :
    Ix.Kernel.proofPW find? E = Ix.Kernel.headProofPW find? (.const I us) := by
  cases E <;> simp only [Ix.Kernel.Expr.getAppFn, reduceCtorEq] at hfn <;>
    exact congrArg (Ix.Kernel.headProofPW find?) hfn

theorem proofPW_of_getAppFn_fvar (find? : KKey → Option (Ix.Kernel.ConstantInfo .anon))
    {E : KExpr} {idx : Nat} {ty : KExpr} (hfn : E.getAppFn = .fvar idx ty) :
    Ix.Kernel.proofPW find? E = Ix.Kernel.headProofPW find? (.fvar idx ty) := by
  cases E <;> simp only [Ix.Kernel.Expr.getAppFn, reduceCtorEq] at hfn <;>
    exact congrArg (Ix.Kernel.headProofPW find?) hfn

theorem posOf_eq_mkAppN_const_inv {ps : List Ix.Kernel.LevelParam} {T : KExpr}
    {K : KKey} {cus' : List KLevel} {As' : List KExpr}
    (heq : posOf ps T = Ix.Kernel.Expr.mkAppN (.const K cus') As') :
    ∃ cus, T.getAppFn = .const K cus ∧
      cus' = cus.map (Ix.Kernel.Level.subst ps (posLevels ps)) ∧
      T.numArgs = As'.length := by
  obtain ⟨hfn, hnum⟩ := mkAppN_fn_numArgs As' (.const K cus')
  rw [← heq] at hfn hnum
  simp only [posOf, Ix.Kernel.Expr.getAppFn_instantiateLevelParams,
    numArgs_instantiateLevelParams, Ix.Kernel.Expr.getAppFn, Ix.Kernel.Expr.numArgs,
    Nat.zero_add] at hfn hnum
  cases hTf : T.getAppFn <;>
    simp only [hTf, Ix.Kernel.Expr.instantiateLevelParams, reduceCtorEq,
      Ix.Kernel.Expr.const.injEq] at hfn
  obtain ⟨rfl, rfl⟩ := hfn
  exact ⟨_, rfl, rfl, hnum⟩

end IxVM.Refinement.Core.DefEqAux

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList)
open Ix.Kernel.Rules (Red DefEq)
open IxVM.Refinement.Core.DefEqAux

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Internal helpers of `KernelDefEq` -/

private theorem level_zero_at_zero {x_l x_us : SourceValue F} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)} {u : KLevel}
    (ev : ObsFn W "KernelDefEq::level_zero_at" [x_l, .field 0, x_us] h r h' calls)
    (bd : IxVM.Consistency.Bounded calls) (hu : LvRep h u x_l) :
    IsClassVal r ∧ (r = .field 1 → ∀ φ, Ix.Kernel.Level.eval φ u = 0) := by
  rcases Obs.«KernelDefEq::level_zero_at».obs ev with
    ⟨cs18, m31, -, hm39, ev20, hc43⟩ | ⟨_, _, _, _, _, hne44, _⟩
  · subst hc43 hm39
    obtain ⟨l, hl, heq⟩ := hu
    obtain ⟨hr, -⟩ := IxVM.Refinement.Levels.levelEqual_step ev20 x_l _ rfl
      (bounded_sub (fun x hx => by simp [hx]) bd) l .zero (hl.mono (Heap.Extends.snoc _ _))
      (DefEqAux.repKLevel_store_zero h)
    refine ⟨hr ▸ isClassVal_ite _, fun hr1 φ => ?_⟩
    have ht : IxVM.Refinement.KernelLevels.levelEqual l .zero = true :=
      of_ite_field_ne_zero hr (hr1 ▸ field_one_ne_zero)
    exact (heq φ).trans (IxVM.Refinement.KernelLevels.levelEqual_eq_true_sound ht φ)
  · exact (hne44 rfl).elim

private theorem level_zero_at_inst {x_l x_us : SourceValue F} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)} {u : KLevel} {us : List KLevel}
    (ev : ObsFn W "KernelDefEq::level_zero_at" [x_l, .field 1, x_us] h r h' calls)
    (bd : IxVM.Consistency.Bounded calls) (hu : LvRep h u x_l) (hus : LvListRep h us x_us) :
    IsClassVal r ∧
      (r = .field 1 →
        ∀ φ, Ix.Kernel.Level.eval φ (Ix.Kernel.Level.subst (List.range us.length) us u) = 0) := by
  rcases Obs.«KernelDefEq::level_zero_at».obs ev with
    ⟨_, _, hv14, _⟩ | ⟨cs51, v54, m57, cs65, m85, -, ev67, hm93, ev53, hc97⟩
  · exact absurd hv14 field_one_ne_zero
  · subst hc97 hm93
    obtain ⟨l, hl, heq⟩ := hu
    obtain ⟨ls, hls, heqs⟩ := hus
    obtain ⟨-, hv54, -⟩ := IxVM.Refinement.Levels.levelInstParams_step ev67 x_l x_us rfl
      (bounded_sub (fun x hx => by simp [hx]) bd) l ls hl hls
    obtain ⟨hr, -⟩ := IxVM.Refinement.Levels.levelEqual_step ev53 v54 _ rfl
      (bounded_sub (fun x hx => by simp [hx]) bd) _ .zero (hv54.mono (Heap.Extends.snoc _ _))
      (DefEqAux.repKLevel_store_zero m57)
    refine ⟨hr ▸ isClassVal_ite _, fun hr1 φ => ?_⟩
    have ht : IxVM.Refinement.KernelLevels.levelEqual _ .zero = true :=
      of_ite_field_ne_zero hr (hr1 ▸ field_one_ne_zero)
    exact (SubstAux.lvEq_subst heq heqs φ).trans
      (IxVM.Refinement.KernelLevels.levelEqual_eq_true_sound ht φ)

private theorem peel_never_pis_aux {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} :
    ∀ (n : Nat) {x_e x_r : SourceValue F} {k : F} {h h' : Heap F} {calls : List (Call F)}
      {j : Nat} {E : KExpr},
      ZMod.val k = n →
      ObsFn W "KernelDefEq::peel_never_pis" [x_e, .field k] h (.tuple [.field 1, x_r]) h' calls →
      Tm κ d Γ h j E x_e →
      ∃ R, E.peelNeverPis n = some R ∧ Tm κ d Γ h' (j + n) R x_r
  | 0, x_e, x_r, k, h, h', calls, j, E, hvk, ev, hE => by
    have hk0 : k = 0 := (ZMod.val_eq_zero k).mp hvk
    subst hk0
    rcases Obs.«KernelDefEq::peel_never_pis».obs ev with
      ⟨-, he19, he33, -⟩ | ⟨_, _, _, _, _, _, _, hne35, _⟩ | ⟨_, _, _, _, _, _, hne35, _⟩ |
      ⟨_, hne35, _⟩
    · subst he33
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at he19
      obtain ⟨-, rfl⟩ := he19
      exact ⟨E, rfl, by simpa only [Nat.add_zero] using hE⟩
    · exact (hne35 rfl).elim
    · exact (hne35 rfl).elim
    · exact (hne35 rfl).elim
  | n + 1, x_e, x_r, k, h, h', calls, j, E, hvk, ev, hE => by
    have hk0 : k ≠ 0 := fun hk => by subst hk; simp at hvk
    rcases Obs.«KernelDefEq::peel_never_pis».obs ev with
      ⟨hv14, _⟩ |
      ⟨w58, x_b, x_bl, m75, cs86, cs104, v108, -, ld50, ev88, op129, ev106, -⟩ |
      ⟨_, _, _, _, _, _, -, _, _, _, he140, _⟩ |
      ⟨_, -, _, _, he164, _⟩
    · injection hv14 with hk
      exact (hk0 hk).elim
    · obtain rfl := Lib.sub_one_inv op129
      obtain ⟨T, B, ℓ, rfl, -, hB, hℓ⟩ := hE.forallE_of_load ld50
      obtain ⟨h1, rfl⟩ := IxVM.Refinement.Levels.levelIsNotZero_step ev88 x_bl rfl ℓ hℓ
      have hnz : ℓ.isNeverZero = true := of_ite_field_ne_zero h1 field_one_ne_zero
      have hnev : (bmeta ℓ).pw.isNever = true := by
        show ℓ.zeronessOf.isNever = true
        rwa [← Ix.Kernel.Level.isNeverZero_eq_isNever]
      have hvk' : ZMod.val (k - 1) = n := by
        have := Lib.val_sub_one hk0
        omega
      obtain ⟨R, hR, hTm⟩ := peel_never_pis_aux n hvk' ev106 hB
      refine ⟨R, ?_, by simpa only [Nat.add_assoc, Nat.add_comm 1 n] using hTm⟩
      simp only [Ix.Kernel.Expr.peelNeverPis, hnev, ↓reduceIte]
      exact hR
    · simp only [Value.tuple.injEq, List.cons.injEq] at he140
      exact absurd he140.1 field_one_ne_zero
    · simp only [Value.tuple.injEq, List.cons.injEq] at he164
      exact absurd he164.1 field_one_ne_zero

private theorem residual_class_zero {κ : _root_.Address → KKey} {d j : Nat} {Γ : Nat → KExpr}
    {x_ok x_r x_us : SourceValue F} {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    {n : Nat} {E : KExpr}
    (ev : ObsFn W "KernelDefEq::residual_class" [x_ok, x_r, .field 0, x_us] h r h' calls)
    (bd : IxVM.Consistency.Bounded calls)
    (hpeel : x_ok = .field 1 → ∃ R, E.peelNeverPis n = some R ∧ Tm κ d Γ h j R x_r) :
    IsClassVal r ∧
      (r = .field 1 → ∃ u, E.peelNeverPis n = some (.sort u) ∧
        ∀ φ, Ix.Kernel.Level.eval φ u = 0) := by
  rcases Obs.«KernelDefEq::residual_class».obs ev with
    ⟨x_u, cs42, hv14, ld26, ev44, hc69⟩ | ⟨_, _, _, _, he74, _⟩ | ⟨_, he81, _⟩
  · subst hc69
    obtain ⟨R, hRp, hR⟩ := hpeel hv14
    obtain ⟨u, rfl, hu⟩ := hR.sort_of_load ld26
    obtain ⟨hcl, hz⟩ := level_zero_at_zero ev44 (bounded_sub (fun x hx => by simp [hx]) bd) hu
    exact ⟨hcl, fun hr1 => ⟨u, hRp, hz hr1⟩⟩
  · subst he74
    exact ⟨.inr (.inr rfl), fun hr1 => absurd hr1 field_two_ne_one⟩
  · subst he81
    exact ⟨.inr (.inr rfl), fun hr1 => absurd hr1 field_two_ne_one⟩

private theorem residual_class_inst {κ : _root_.Address → KKey} {d j : Nat} {Γ : Nat → KExpr}
    {x_ok x_r x_us : SourceValue F} {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    {n : Nat} {E : KExpr} {us : List KLevel}
    (ev : ObsFn W "KernelDefEq::residual_class" [x_ok, x_r, .field 1, x_us] h r h' calls)
    (bd : IxVM.Consistency.Bounded calls) (hus : LvListRep h us x_us)
    (hpeel : x_ok = .field 1 → ∃ R, E.peelNeverPis n = some R ∧ Tm κ d Γ h j R x_r) :
    IsClassVal r ∧
      (r = .field 1 → ∃ u, E.peelNeverPis n = some (.sort u) ∧
        ∀ φ, Ix.Kernel.Level.eval φ (Ix.Kernel.Level.subst (List.range us.length) us u) = 0) := by
  rcases Obs.«KernelDefEq::residual_class».obs ev with
    ⟨x_u, cs42, hv14, ld26, ev44, hc69⟩ | ⟨_, _, _, _, he74, _⟩ | ⟨_, he81, _⟩
  · subst hc69
    obtain ⟨R, hRp, hR⟩ := hpeel hv14
    obtain ⟨u, rfl, hu⟩ := hR.sort_of_load ld26
    obtain ⟨hcl, hz⟩ := level_zero_at_inst ev44 (bounded_sub (fun x hx => by simp [hx]) bd) hu hus
    exact ⟨hcl, fun hr1 => ⟨u, hRp, hz hr1⟩⟩
  · subst he74
    exact ⟨.inr (.inr rfl), fun hr1 => absurd hr1 field_two_ne_one⟩
  · subst he81
    exact ⟨.inr (.inr rfl), fun hr1 => absurd hr1 field_two_ne_one⟩

private theorem type_sort_class_zero (c : Ctx) {x_t x_types x_us : SourceValue F}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    {d : Nat} {Γ : Nat → KExpr} {T : KExpr}
    (ev : ObsFn W "KernelDefEq::type_sort_class" [x_t, x_types, .field 0, x_us] h r h' calls)
    (ih : IH c calls) (good : Good c calls)
    (htypes : c.types Γ h d x_types) (hT : c.tm d Γ h T x_t) :
    IsClassVal r ∧
      (r = .field 1 → ∃ pw, Ix.Kernel.typeSortPW c.env.find? T = some pw ∧ pw.isProp = true) := by
  rcases Obs.«KernelDefEq::type_sort_class».obs ev with
    ⟨w20, w21, x_bl, cs40, ld12, ev42, hc67⟩ |
    ⟨w75, ld12, he81, he82, hc83⟩ |
    ⟨v1, m89, cs99, x_head, x_args, x_c, x_cus, v152, m153, p160, cs166, m178, x186, y187, m188,
      cs197, cs211, v271, m272, cs274, m281, cs291, v294, v295, m297, cs305, m317, cs325, x_ok,
      x_r, cs352, ld12, _, _, ev101, ld134, ev168, ld162, ev199, ev213, op193, sg279, ev307,
      ev327, ev293, ev354, hc386⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      he391, _, _⟩ |
    ⟨v1, m89, cs99, x_head, x_args, x_i, m421, cs431, v434, v435, m437, cs445, m465, cs473, x_ok,
      x_r, cs500, m528, ld12, _, _, ev101, ld134, hv419, ev447, ev475, ev433, hm536, ev502,
      hc540⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, hne541, _, _, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, he552, _, _⟩
  · -- `Forall`
    subst hc67
    obtain ⟨dom, body, ℓ, rfl, -, -, hℓ⟩ := hT.forallE_of_load ld12
    obtain ⟨hcl, hz⟩ := level_zero_at_zero ev42 (good.sub fun x hx => by simp [hx]).2
      ⟨ℓ, hℓ, LvEq.refl ℓ⟩
    refine ⟨hcl, fun hr1 => ⟨(bmeta ℓ).pw, rfl, ?_⟩⟩
    show ℓ.zeronessOf.isProp = true
    rw [zeronessOf_eq_always_of_eval_zero (hz hr1)]
    exact isProp_always
  · -- `Srt`
    subst he81
    exact ⟨.inl rfl, fun hr1 => absurd hr1.symm field_one_ne_zero⟩
  · -- `other_Const_n0`
    rcases sg279 with ⟨-, he241, he242, hc243⟩ | ⟨_, hne244, _, _⟩
    · subst hc243 hc386
      have e101 := ObsFn.heap_extends ev101
      have e168 := ObsFn.heap_extends ev168
      obtain ⟨hd, sp, H, As, htup, hH, hAs, rfl⟩ := ih.get (.subst .collect_spine) (by lt_calls)
        ev101 x_t rfl (good.sub fun x hx => by simp [hx]) d Γ 0 T hT
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup
      obtain ⟨rfl, rfl⟩ := htup
      obtain ⟨a, cus, rfl, ha, hcus⟩ := hH.const_of_load ld134
      obtain ⟨ci, hfind, vci, hvci, hrep⟩ := ih.get (.callees .get_ci) (by lt_calls) ev168 x_c a
        rfl (good.sub fun x hx => by simp [hx]) ha
      rw [ld162] at hvci
      injection hvci with hvci
      subst hvci
      obtain ⟨hnt, hlp_lt, hperm⟩ := ciRep_info hrep
      obtain ⟨ls, hls, hlveq⟩ := LvListRep.mono e168 hcus
      have hls_lt : ls.length < 2 ^ 39 := RomBound.bounded_length_lt good.2
        (c := ⟨Obs.Names.«Lists::length<&KernelTypes::KLevelNode>», [x_cus], m153⟩) (by simp)
        (by simp) hls
      obtain ⟨rfl, hm188⟩ := pi_lvl_length ev199 hls
      have hrep188 : CIRep c.κ m188 v152 ci := by rw [hm188]; exact hrep
      obtain ⟨rfl, hm178⟩ := ih.get (.infer .const_num_lvls) (by lt_calls) ev213 v152 ci rfl
        (good.sub fun x hx => by simp [hx]) hrep188
      have hcus_len : cus.length = ci.toConstantVal.levelParams.length :=
        (Ix.Kernel.Level.EvalEqList.length_eq (hlveq fun _ => 0)).trans
          (natCast_inj_small (DefEqAux.lt_of_lt_2_39 hls_lt) (by omega)
            (DefEqAux.sub_field_zero op193))
      have hrep272 : CIRep c.κ m272 v152 ci := by rw [he242, hm178, hm188]; exact hrep
      obtain ⟨hcty, hm297⟩ := ih.get (.infer .const_type_of) (by lt_calls) ev307 v152 ci rfl
        (good.sub fun x hx => by simp [hx]) hrep272
      have hAs297 : c.tml d Γ m297 As x_args := by
        rw [hm297, he242, hm178, hm188]
        exact tml_mono e168 hAs
      have hAs_lt : As.length < 2 ^ 39 := RomBound.bounded_length_lt good.2
        (c := ⟨Obs.Names.«Lists::length<&KernelTypes::KExprNode>», [x_args], m297⟩) (by simp)
        (by simp) hAs297
      obtain ⟨rfl, hm317⟩ := pi_tml_length ev327 hAs297
      have hval_As : ZMod.val (As.length : F) = As.length :=
        DefEqAux.val_natCast_small (DefEqAux.lt_of_lt_2_39 hAs_lt)
      have e293 := ObsFn.heap_extends ev293
      have e153_281 : Heap.Extends m153 m281 := by
        rw [← hm188, ← hm178, ← he242, ← hm297, ← hm317]
        exact e293
      have hcus281 : LvListRep m281 cus v271 := by
        rw [he241]
        exact ⟨ls, hls.mono e153_281, hlveq⟩
      have hcty317 : Tm c.κ d Γ m317 0
          (posOf ci.toConstantVal.levelParams ci.toConstantVal.type) v294 := by
        rw [hm317]
        exact hcty d Γ
      obtain ⟨hcl, hz⟩ := residual_class_inst ev354 (good.sub fun x hx => by simp [hx]).2 hcus281
        (fun hok => by subst hok; exact peel_never_pis_aux As.length hval_As ev293 hcty317)
      refine ⟨hcl, fun hr1 => ?_⟩
      obtain ⟨u', hpeel', hu0⟩ := hz hr1
      obtain ⟨u, hpeel, rfl⟩ := peelNeverPis_posOf_sort_inv hperm As.length hpeel'
      have hu0' : ∀ φ, Ix.Kernel.Level.eval φ
          (Ix.Kernel.Level.subst ci.toConstantVal.levelParams cus u) = 0 := by
        intro φ
        rw [← subst_posLevels_perm_pi hperm hcus_len u]
        exact hu0 φ
      obtain ⟨hfn, hnum⟩ := mkAppN_fn_numArgs As (.const (c.κ (ixAddr a)) cus)
      simp only [Ix.Kernel.Expr.getAppFn, Ix.Kernel.Expr.numArgs, Nat.zero_add] at hfn hnum
      refine ⟨Ix.Kernel.Level.substPW ci.toConstantVal.levelParams cus u.zeronessOf, ?_, ?_⟩
      · rw [typeSortPW_of_getAppFn_const c.env.find? hfn, hnum]
        simp [Ix.Kernel.headTypePW, hfind, hnt, hcus_len, hpeel, Ix.Kernel.residualPW]
      · rw [← Ix.Kernel.Level.zeronessOf_subst, zeronessOf_eq_always_of_eval_zero hu0']
        exact isProp_always
    · exact (hne244 rfl).elim
  · -- `other_Const_other`
    subst he391
    exact ⟨.inr (.inr rfl), fun hr1 => absurd hr1 field_two_ne_one⟩
  · -- `other_BVar_n0`
    subst hc540
    have e101 := ObsFn.heap_extends ev101
    have e447 := ObsFn.heap_extends ev447
    obtain ⟨hd, sp, H, As, htup, hH, hAs, rfl⟩ := ih.get (.subst .collect_spine) (by lt_calls)
      ev101 x_t rfl (good.sub fun x hx => by simp [hx]) d Γ 0 T hT
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup
    obtain ⟨rfl, rfl⟩ := htup
    obtain ⟨i, rfl, -, hbvar⟩ := hH.bvar_of_load ld134
    have hH_eq : H = .fvar (fvIdx d 0 (ZMod.val i)) (Γ (fvIdx d 0 (ZMod.val i))) := by
      rcases hbvar with ⟨hi, -⟩ | ⟨-, -, hEq⟩
      · omega
      · exact hEq
    subst hH_eq
    obtain ⟨-, hty_i⟩ := ih.get (.infer .types_lookup) (by lt_calls) ev447 x_types i rfl
      (good.sub fun x hx => by simp [hx]) d Γ (types_mono e101 htypes)
    have hAs437 : c.tml d Γ m437 As x_args := tml_mono e447 hAs
    have hAs_lt : As.length < 2 ^ 39 := RomBound.bounded_length_lt good.2
      (c := ⟨Obs.Names.«Lists::length<&KernelTypes::KExprNode>», [x_args], m437⟩) (by simp)
      (by simp) hAs437
    obtain ⟨rfl, hm465⟩ := pi_tml_length ev475 hAs437
    have hval_As : ZMod.val (As.length : F) = As.length :=
      DefEqAux.val_natCast_small (DefEqAux.lt_of_lt_2_39 hAs_lt)
    have hty465 : Tm c.κ d Γ m465 0 (Γ (fvIdx d 0 (ZMod.val i))) v434 := by
      rw [hm465]
      exact hty_i
    have e528 : Heap.Extends m421 m528 := by rw [hm536]; exact Heap.Extends.snoc _ _
    obtain ⟨hcl, hz⟩ := residual_class_zero ev502 (good.sub fun x hx => by simp [hx]).2
      (fun hok => by
        subst hok
        obtain ⟨R, hRp, hTm⟩ := peel_never_pis_aux As.length hval_As ev433 hty465
        exact ⟨R, hRp, Tm.mono e528 hTm⟩)
    refine ⟨hcl, fun hr1 => ?_⟩
    obtain ⟨u, hpeel, hu0⟩ := hz hr1
    obtain ⟨hfn, hnum⟩ := mkAppN_fn_numArgs As
      (.fvar (fvIdx d 0 (ZMod.val i)) (Γ (fvIdx d 0 (ZMod.val i))))
    simp only [Ix.Kernel.Expr.getAppFn, Ix.Kernel.Expr.numArgs, Nat.zero_add] at hfn hnum
    refine ⟨u.zeronessOf, ?_, ?_⟩
    · rw [typeSortPW_of_getAppFn_fvar c.env.find? hfn, hnum]
      simp [Ix.Kernel.headTypePW, hpeel, Ix.Kernel.residualPW]
    · rw [zeronessOf_eq_always_of_eval_zero hu0]
      exact isProp_always
  · -- `other_BVar_other`
    exact (hne541 rfl).elim
  · -- `other_other`
    subst he552
    exact ⟨.inr (.inr rfl), fun hr1 => absurd hr1 field_two_ne_one⟩

private theorem type_sort_class_inst (c : Ctx) {x_t x_types x_us : SourceValue F}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    {ps : List Ix.Kernel.LevelParam} {T : KExpr} {us : List KLevel}
    (ev : ObsFn W "KernelDefEq::type_sort_class" [x_t, x_types, .field 1, x_us] h r h' calls)
    (ih : IH c calls) (good : Good c calls)
    (hperm : ps.Perm (List.range ps.length)) (hlen : us.length = ps.length)
    (hT : c.tmc h (posOf ps T) x_t) (hus : LvListRep h us x_us) :
    IsClassVal r ∧
      (r = .field 1 →
        ∃ pw, Ix.Kernel.typeSortPW c.env.find? T = some pw ∧
          (Ix.Kernel.Level.substPW ps us pw).isProp = true) := by
  let Γ₀ : Nat → KExpr := fun _ => .sort .zero
  rcases Obs.«KernelDefEq::type_sort_class».obs ev with
    ⟨w20, w21, x_bl, cs40, ld12, ev42, hc67⟩ |
    ⟨w75, ld12, he81, he82, hc83⟩ |
    ⟨v1, m89, cs99, x_head, x_args, x_c, x_cus, v152, m153, p160, cs166, m178, x186, y187, m188,
      cs197, cs211, v271, m272, cs274, m281, cs291, v294, v295, m297, cs305, m317, cs325, x_ok,
      x_r, cs352, ld12, _, _, ev101, ld134, ev168, ld162, ev199, ev213, op193, sg279, ev307,
      ev327, ev293, ev354, hc386⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      he391, _, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv419, _, _, _, _, _,
      _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, he545, _, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, he552, _, _⟩
  · -- `Forall`
    subst hc67
    obtain ⟨dom', body', ℓ, heq, -, -, hℓ⟩ := (hT 0 Γ₀).forallE_of_load ld12
    cases T <;>
      simp only [posOf, Ix.Kernel.Expr.instantiateLevelParams, reduceCtorEq,
        Ix.Kernel.Expr.forallE.injEq] at heq
    case forallE dom body m =>
      obtain ⟨-, -, hm⟩ := heq
      have hpw : Ix.Kernel.Level.substPW ps (posLevels ps) m.pw = ℓ.zeronessOf :=
        congrArg Ix.Kernel.BinderMeta.pw hm
      obtain ⟨hcl, hz⟩ := level_zero_at_inst ev42 (good.sub fun x hx => by simp [hx]).2
        ⟨ℓ, hℓ, LvEq.refl ℓ⟩ hus
      refine ⟨hcl, fun hr1 => ⟨m.pw, rfl, ?_⟩⟩
      rw [← substPW_posLevels_perm_pi hperm hlen m.pw, hpw, ← Ix.Kernel.Level.zeronessOf_subst,
        zeronessOf_eq_always_of_eval_zero (hz hr1)]
      exact isProp_always
  · -- `Srt`
    subst he81
    exact ⟨.inl rfl, fun hr1 => absurd hr1.symm field_one_ne_zero⟩
  · -- `other_Const_n0`
    subst hc386
    rcases sg279 with ⟨hv239, _, _, _⟩ | ⟨cs251, -, ev253, hc270⟩
    · exact absurd hv239 field_one_ne_zero
    · subst hc270
      have e101 := ObsFn.heap_extends ev101
      have e168 := ObsFn.heap_extends ev168
      obtain ⟨hd, sp, H, As', htup, hH, hAs', heq_pos⟩ := ih.get (.subst .collect_spine)
        (by lt_calls) ev101 x_t rfl (good.sub fun x hx => by simp [hx]) 0 Γ₀ 0 (posOf ps T)
        (hT 0 Γ₀)
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup
      obtain ⟨rfl, rfl⟩ := htup
      obtain ⟨a, cus', rfl, ha, hcus'⟩ := hH.const_of_load ld134
      obtain ⟨cus, hT_fn, rfl, hT_num⟩ := posOf_eq_mkAppN_const_inv heq_pos
      obtain ⟨ci, hfind, vci, hvci, hrep⟩ := ih.get (.callees .get_ci) (by lt_calls) ev168 x_c a
        rfl (good.sub fun x hx => by simp [hx]) ha
      rw [ld162] at hvci
      injection hvci with hvci
      subst hvci
      obtain ⟨hnt, hlp_lt, hperm'⟩ := ciRep_info hrep
      obtain ⟨ls, hls, hlveq'⟩ := LvListRep.mono e168 hcus'
      have hls_lt : ls.length < 2 ^ 39 := RomBound.bounded_length_lt good.2
        (c := ⟨Obs.Names.«Lists::length<&KernelTypes::KLevelNode>», [x_cus], m153⟩) (by simp)
        (by simp) hls
      obtain ⟨rfl, hm188⟩ := pi_lvl_length ev199 hls
      have hrep188 : CIRep c.κ m188 v152 ci := by rw [hm188]; exact hrep
      obtain ⟨rfl, hm178⟩ := ih.get (.infer .const_num_lvls) (by lt_calls) ev213 v152 ci rfl
        (good.sub fun x hx => by simp [hx]) hrep188
      have hcus'_len :
          (cus.map (Ix.Kernel.Level.subst ps (posLevels ps))).length =
            ci.toConstantVal.levelParams.length :=
        (Ix.Kernel.Level.EvalEqList.length_eq (hlveq' fun _ => 0)).trans
          (natCast_inj_small (DefEqAux.lt_of_lt_2_39 hls_lt) (by omega)
            (DefEqAux.sub_field_zero op193))
      have hcus_len : cus.length = ci.toConstantVal.levelParams.length := by
        simpa only [List.length_map] using hcus'_len
      have hls178 : RepKLevelList m178 ls x_cus := by rw [hm178, hm188]; exact hls
      have e_h_178 : Heap.Extends h m178 := by rw [hm178, hm188]; exact e101.trans e168
      obtain ⟨lus, hlus178, hlvequ⟩ := LvListRep.mono e_h_178 hus
      obtain ⟨-, hv271, e253⟩ := IxVM.Refinement.Levels.levelListInst_step ev253 x_cus x_us rfl
        (good.sub fun x hx => by simp [hx]).2 ls lus hls178 hlus178
      have hv271_eq : LvEqList (cus.map (Ix.Kernel.Level.subst ps us))
          (IxVM.Refinement.KernelLevels.substLevelList ls lus) := by
        have hcomp := SubstAux.lvEqList_subst hlveq' hlvequ
        have hmap :
            (cus.map (Ix.Kernel.Level.subst ps (posLevels ps))).map
                (Ix.Kernel.Level.subst (List.range us.length) us) =
              cus.map (Ix.Kernel.Level.subst ps us) := by
          rw [List.map_map]
          exact List.map_congr_left fun l _ => subst_posLevels_perm_pi hperm hlen l
        rwa [hmap] at hcomp
      have hrep272 : CIRep c.κ m272 v152 ci :=
        (show CIRep c.κ m178 v152 ci by rw [hm178]; exact hrep188).mono e253
      obtain ⟨hcty, hm297⟩ := ih.get (.infer .const_type_of) (by lt_calls) ev307 v152 ci rfl
        (good.sub fun x hx => by simp [hx]) hrep272
      have e153_272 : Heap.Extends m153 m272 := by rw [← hm188, ← hm178]; exact e253
      have hAs'297 : c.tml 0 Γ₀ m297 As' x_args := by
        rw [hm297]
        exact tml_mono (e168.trans e153_272) hAs'
      have hAs'_lt : As'.length < 2 ^ 39 := RomBound.bounded_length_lt good.2
        (c := ⟨Obs.Names.«Lists::length<&KernelTypes::KExprNode>», [x_args], m297⟩) (by simp)
        (by simp) hAs'297
      obtain ⟨rfl, hm317⟩ := pi_tml_length ev327 hAs'297
      have hval_As' : ZMod.val (As'.length : F) = As'.length :=
        DefEqAux.val_natCast_small (DefEqAux.lt_of_lt_2_39 hAs'_lt)
      have e293 := ObsFn.heap_extends ev293
      have e272_281 : Heap.Extends m272 m281 := by rw [← hm297, ← hm317]; exact e293
      have hv271_281 : LvListRep m281 (cus.map (Ix.Kernel.Level.subst ps us)) v271 :=
        ⟨_, hv271.mono e272_281, hv271_eq⟩
      have hcty317 : Tm c.κ 0 Γ₀ m317 0
          (posOf ci.toConstantVal.levelParams ci.toConstantVal.type) v294 := by
        rw [hm317]
        exact hcty 0 Γ₀
      obtain ⟨hcl, hz⟩ := residual_class_inst ev354 (good.sub fun x hx => by simp [hx]).2
        hv271_281
        (fun hok => by subst hok; exact peel_never_pis_aux As'.length hval_As' ev293 hcty317)
      refine ⟨hcl, fun hr1 => ?_⟩
      obtain ⟨u', hpeel', hu0⟩ := hz hr1
      obtain ⟨u, hpeel, rfl⟩ := peelNeverPis_posOf_sort_inv hperm' As'.length hpeel'
      have hmap_len : (cus.map (Ix.Kernel.Level.subst ps us)).length =
          ci.toConstantVal.levelParams.length := by
        rw [List.length_map]
        exact hcus_len
      have hu0' : ∀ φ, Ix.Kernel.Level.eval φ
          (Ix.Kernel.Level.subst ci.toConstantVal.levelParams
            (cus.map (Ix.Kernel.Level.subst ps us)) u) = 0 := by
        intro φ
        rw [← subst_posLevels_perm_pi hperm' hmap_len u]
        exact hu0 φ
      have hpw_comp :
          (Ix.Kernel.Level.substPW ci.toConstantVal.levelParams
            (cus.map (Ix.Kernel.Level.subst ps us)) u.zeronessOf).isProp = true := by
        rw [← Ix.Kernel.Level.zeronessOf_subst, zeronessOf_eq_always_of_eval_zero hu0']
        exact isProp_always
      refine ⟨Ix.Kernel.Level.substPW ci.toConstantVal.levelParams cus u.zeronessOf, ?_,
        isProp_substPW_comp hcus_len hpw_comp⟩
      rw [typeSortPW_of_getAppFn_const c.env.find? hT_fn, hT_num]
      simp [Ix.Kernel.headTypePW, hfind, hnt, hcus_len, hpeel, Ix.Kernel.residualPW]
  · -- `other_Const_other`
    subst he391
    exact ⟨.inr (.inr rfl), fun hr1 => absurd hr1 field_two_ne_one⟩
  · -- `other_BVar_n0`
    exact absurd hv419 field_one_ne_zero
  · -- `other_BVar_other`
    subst he545
    exact ⟨.inr (.inr rfl), fun hr1 => absurd hr1 field_two_ne_one⟩
  · -- `other_other`
    subst he552
    exact ⟨.inr (.inr rfl), fun hr1 => absurd hr1 field_two_ne_one⟩

private theorem proof_class_spec (c : Ctx) {x_a x_types : SourceValue F}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    {d : Nat} {Γ : Nat → KExpr} {A : KExpr}
    (ev : ObsFn W "KernelDefEq::proof_class" [x_a, x_types] h r h' calls)
    (ih : IH c calls) (good : Good c calls)
    (htypes : c.types Γ h d x_types) (hA : c.tm d Γ h A x_a) :
    IsClassVal r ∧ (r = .field 1 → Ix.Kernel.isProofFast c.env.find? A = true) := by
  rcases Obs.«KernelDefEq::proof_class».obs ev with
    ⟨w20, w21, x_bl, cs40, m53, ld12, hm61, ev42, hc65⟩ |
    ⟨v1, m71, cs81, x_head, w95, x_c, x_us, v135, m136, p143, cs149, m161, x169, y170, m171,
      cs180, cs194, cs212, v215, m220, cs228, ld12, _, ev83, ld117, ev151, ld145, ev182, ev196,
      op176, ev230, ev214, hc259⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, he264, _,
      _⟩ |
    ⟨v1, m71, cs81, x_head, w95, x_i, cs282, v285, m290, cs298, m331, ld12, _, ev83, ld117, ev300,
      hm339, ev284, hc343⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, he357, _, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, he385, _, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, he401, _, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, he408, _, _⟩
  · -- `Lam`
    subst hc65 hm61
    obtain ⟨dom, body, ℓ, rfl, -, -, hℓ⟩ := hA.lam_of_load ld12
    obtain ⟨hr, -⟩ := IxVM.Refinement.Levels.levelEqual_step ev42 x_bl _ rfl
      (good.sub fun x hx => by simp [hx]).2 ℓ .zero (hℓ.mono (Heap.Extends.snoc _ _))
      (DefEqAux.repKLevel_store_zero h)
    refine ⟨hr ▸ isClassVal_ite _, fun hr1 => ?_⟩
    have ht : IxVM.Refinement.KernelLevels.levelEqual ℓ .zero = true :=
      of_ite_field_ne_zero hr (hr1 ▸ field_one_ne_zero)
    have hz := zeronessOf_eq_always_of_eval_zero
      (IxVM.Refinement.KernelLevels.levelEqual_eq_true_sound ht)
    simp only [Ix.Kernel.isProofFast, Ix.Kernel.proofPW, bmeta, hz]
    exact isProp_always
  · -- `other_Const_n0`
    subst hc259
    have e83 := ObsFn.heap_extends ev83
    have e151 := ObsFn.heap_extends ev151
    obtain ⟨hd, sp, H, As, htup, hH, -, rfl⟩ := ih.get (.subst .collect_spine) (by lt_calls) ev83
      x_a rfl (good.sub fun x hx => by simp [hx]) d Γ 0 A hA
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup
    obtain ⟨rfl, rfl⟩ := htup
    obtain ⟨a, us, rfl, ha, hus⟩ := hH.const_of_load ld117
    obtain ⟨ci, hfind, vci, hvci, hrep⟩ := ih.get (.callees .get_ci) (by lt_calls) ev151 x_c a rfl
      (good.sub fun x hx => by simp [hx]) ha
    rw [ld145] at hvci
    injection hvci with hvci
    subst hvci
    obtain ⟨hnt, hlp_lt, hperm⟩ := ciRep_info hrep
    obtain ⟨ls, hls, hlveq⟩ := LvListRep.mono e151 hus
    have hls_lt : ls.length < 2 ^ 39 := RomBound.bounded_length_lt good.2
      (c := ⟨Obs.Names.«Lists::length<&KernelTypes::KLevelNode>», [x_us], m136⟩) (by simp)
      (by simp) hls
    obtain ⟨rfl, hm171⟩ := pi_lvl_length ev182 hls
    have hrep171 : CIRep c.κ m171 v135 ci := by rw [hm171]; exact hrep
    obtain ⟨rfl, hm161⟩ := ih.get (.infer .const_num_lvls) (by lt_calls) ev196 v135 ci rfl
      (good.sub fun x hx => by simp [hx]) hrep171
    have hus_len : us.length = ci.toConstantVal.levelParams.length :=
      (Ix.Kernel.Level.EvalEqList.length_eq (hlveq fun _ => 0)).trans
        (natCast_inj_small (DefEqAux.lt_of_lt_2_39 hls_lt) (by omega)
          (DefEqAux.sub_field_zero op176))
    have hrep161 : CIRep c.κ m161 v135 ci := by rw [hm161]; exact hrep171
    obtain ⟨hcty, hm220⟩ := ih.get (.infer .const_type_of) (by lt_calls) ev230 v135 ci rfl
      (good.sub fun x hx => by simp [hx]) hrep161
    have hus220 : LvListRep m220 us x_us := by
      rw [hm220, hm161, hm171]
      exact ⟨ls, hls, hlveq⟩
    obtain ⟨hcl, hz⟩ := type_sort_class_inst c ev214 (ih.mono (by lt_calls))
      (good.sub fun x hx => by simp [hx]) hperm hus_len hcty hus220
    refine ⟨hcl, fun hr1 => ?_⟩
    obtain ⟨pw, hpw, hisp⟩ := hz hr1
    obtain ⟨hfn, -⟩ := mkAppN_fn_numArgs As (.const (c.κ (ixAddr a)) us)
    simp only [Ix.Kernel.Expr.getAppFn] at hfn
    simp only [Ix.Kernel.isProofFast, proofPW_of_getAppFn_const c.env.find? hfn,
      Ix.Kernel.headProofPW, hfind, hnt, Bool.false_eq_true, ↓reduceIte, hus_len, hpw,
      Option.map_some]
    exact hisp
  · -- `other_Const_other`
    subst he264
    exact ⟨.inr (.inr rfl), fun hr1 => absurd hr1 field_two_ne_one⟩
  · -- `other_BVar`
    subst hc343
    have e83 := ObsFn.heap_extends ev83
    have e300 := ObsFn.heap_extends ev300
    obtain ⟨hd, sp, H, As, htup, hH, -, rfl⟩ := ih.get (.subst .collect_spine) (by lt_calls) ev83
      x_a rfl (good.sub fun x hx => by simp [hx]) d Γ 0 A hA
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup
    obtain ⟨rfl, rfl⟩ := htup
    obtain ⟨i, rfl, -, hbvar⟩ := hH.bvar_of_load ld117
    have hH_eq : H = .fvar (fvIdx d 0 (ZMod.val i)) (Γ (fvIdx d 0 (ZMod.val i))) := by
      rcases hbvar with ⟨hi, -⟩ | ⟨-, -, hEq⟩
      · omega
      · exact hEq
    subst hH_eq
    obtain ⟨-, hty_i⟩ := ih.get (.infer .types_lookup) (by lt_calls) ev300 x_types i rfl
      (good.sub fun x hx => by simp [hx]) d Γ (types_mono e83 htypes)
    have e331 : Heap.Extends m290 m331 := by rw [hm339]; exact Heap.Extends.snoc _ _
    obtain ⟨hcl, hz⟩ := type_sort_class_zero c ev284 (ih.mono (by lt_calls))
      (good.sub fun x hx => by simp [hx]) (types_mono (e83.trans (e300.trans e331)) htypes)
      (Tm.mono e331 hty_i)
    refine ⟨hcl, fun hr1 => ?_⟩
    obtain ⟨pw, hpw, hisp⟩ := hz hr1
    obtain ⟨hfn, -⟩ := mkAppN_fn_numArgs As
      (.fvar (fvIdx d 0 (ZMod.val i)) (Γ (fvIdx d 0 (ZMod.val i))))
    simp only [Ix.Kernel.Expr.getAppFn] at hfn
    simp only [Ix.Kernel.isProofFast, proofPW_of_getAppFn_fvar c.env.find? hfn,
      Ix.Kernel.headProofPW, hpw]
    exact hisp
  · -- `other_Srt`
    subst he357
    exact ⟨.inl rfl, fun hr1 => absurd hr1.symm field_one_ne_zero⟩
  · -- `other_Forall`
    subst he385
    exact ⟨.inl rfl, fun hr1 => absurd hr1.symm field_one_ne_zero⟩
  · -- `other_Lit`
    subst he401
    exact ⟨.inl rfl, fun hr1 => absurd hr1.symm field_one_ne_zero⟩
  · -- `other_other`
    subst he408
    exact ⟨.inr (.inr rfl), fun hr1 => absurd hr1 field_two_ne_one⟩

private theorem try_proof_irrel_slow_spec (c : Ctx) {rc a b types : SourceValue F}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    {d : Nat} {Γ : Nat → KExpr} {A B : KExpr}
    (ev : ObsFn W "KernelDefEq::try_proof_irrel_slow" [rc, a, b, types] h r h' calls)
    (ih : IH c calls) (good : Good c calls) (hrc : c.rc h rc)
    (htypes : c.types Γ h d types) (hA : c.tm d Γ h A a) (hB : c.tm d Γ h B b)
    (hr : r ≠ .field 0) :
    DefEq c.env d A B := by
  rcases Obs.«KernelDefEq::try_proof_irrel_slow».obs ev with
    ⟨_, _, _, _, _, _, _, he82, _, _⟩ |
    ⟨v1, m2, cs12, v39, m40, cs51, v89, m90, cs100, cs130, ev14, ev53, hne85, ev102, ev132,
      hc165⟩
  · exact absurd he82 hr
  · subst hc165
    obtain ⟨TA, hTA, hinfA⟩ := ih.get (.infer .k_infer_only) (by lt_calls) ev14 rc a types rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ htypes A hA
    have e1 := ObsFn.heap_extends ev14
    obtain ⟨S, u, hinfTA, hredTA, hu0⟩ := ih.get (.defEq .is_prop_type) (by lt_calls) ev53 rc v1
      types rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono e1 hrc) d Γ (types_mono e1 htypes)
      TA hTA hne85
    have e2 := ObsFn.heap_extends ev53
    have E40 := e1.trans e2
    obtain ⟨TB, hTB, hinfB⟩ := ih.get (.infer .k_infer_only) (by lt_calls) ev102 rc b types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono E40 hrc) d Γ (types_mono E40 htypes) B
      (Tm.mono E40 hB)
    have e3 := ObsFn.heap_extends ev102
    have E90 := E40.trans e3
    have hde := ih.get (.defEq .k_is_def_eq) (by lt_calls) ev132 rc v1 v89 types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono E90 hrc) d Γ (types_mono E90 htypes) TA TB
      (Tm.mono (e2.trans e3) hTA) hTB hr
    exact .proofIrrelTy hinfA hinfTA hredTA hu0 hinfB hde

/-! ## The registered step -/

/-- `KernelDefEq::try_proof_irrel`: fast proof-class multiplication (`DefEq.proofFast`), falling
back to io-grade inference and `is_prop_type` (`DefEq.proofIrrelTy`). -/
theorem try_proof_irrel_step (c : Ctx) (hc : CoreFacts c) {args : List (SourceValue F)}
    {h : Heap F} {r : SourceValue F} {h' : Heap F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::try_proof_irrel" args h r h' calls) (ih : IH c calls) :
    Specs.DefEq.try_proof_irrel c args h r h' calls := by
  intro rc a b types hargs good hrc d Γ htypes A B hA hB hr
  subst hargs
  rcases Obs.«KernelDefEq::try_proof_irrel».obs ev with
    ⟨_, _, _, he36, _, _⟩ |
    ⟨_, _, _, _, _, _, _, _, he78, _, _⟩ |
    ⟨v1, m2, cs13, v43, m44, cs55, m86, x94, y95, m96, cs105, cs127, ev15, _, ev57, _, ev107,
      ev129, op101, _, _, hc152⟩ |
    ⟨v1, m2, cs13, v43, m44, cs55, v85, m86, x94, y95, m96, cs105, cs127, cs160, ev15, _, ev57, _,
      ev107, ev129, op101, _, ev162, hc195⟩
  · exact absurd he36 hr
  · exact absurd he78 hr
  · subst hc152
    have E44 := (ObsFn.heap_extends ev15).trans (ObsFn.heap_extends ev57)
    have E96 := E44.trans (ObsFn.heap_extends ev107)
    obtain ⟨hxcl, hxfast⟩ := proof_class_spec c ev107 (ih.mono (by lt_calls))
      (good.sub fun x hx => by simp [hx]) (types_mono E44 htypes) (Tm.mono E44 hA)
    obtain ⟨hycl, hyfast⟩ := proof_class_spec c ev129 (ih.mono (by lt_calls))
      (good.sub fun x hx => by simp [hx]) (types_mono E96 htypes) (Tm.mono E96 hB)
    obtain ⟨hx1, hy1⟩ := mul_class_eq_one hxcl hycl op101
    exact .proofFast (hxfast hx1) (hyfast hy1)
  · subst hc195
    have E86 := (ObsFn.heap_extends ev15).trans ((ObsFn.heap_extends ev57).trans
      ((ObsFn.heap_extends ev107).trans (ObsFn.heap_extends ev129)))
    exact try_proof_irrel_slow_spec c ev162 (ih.mono (by lt_calls))
      (good.sub fun x hx => by simp [hx]) (RCRep.mono E86 hrc) (types_mono E86 htypes)
      (Tm.mono E86 hA) (Tm.mono E86 hB) hr

end IxVM.Refinement.Core
