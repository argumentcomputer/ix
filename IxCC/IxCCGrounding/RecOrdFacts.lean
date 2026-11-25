import IxCCGrounding.Syntax

/-!
# The decided facts of an `ordinary` recursor (`IxCCGrounding.RecOrdFacts`), W-c

Denotes-free, like `IxCCGrounding.Syntax`. What F2 at an `ordinary` recursor (parameters, no index:
`List.rec`, `Option.rec`) reads beyond the `noParams` facts it shares (`RecTele`, `RecProg`,
`RecCtorsRaw`, `RecSites`):

* `RecOrdRules`: every stored rule does not compare parameters (`compareParams = false`, so ι
  takes the major at its own parameters: `paramsBlindIota`), each of its λs carries the major
  premise's binder datum (so the graph regime at the major premise, which `LastSiteOk` gives, is
  the regime of every λ, which the law's spine reads), and its constructor is stored closed and
  covered by its level parameters (so a constructor value's fit moves to the recursor's levels).
  Not `RecFields`: the law's own spine puts the fields in the rule's λ-domains at the recursor's
  parameters (`spineOk_lamTele`), so no field-domain comparison is needed.
-/

namespace IxCC.Grounding

open Ix.Kernel
open IxCC.Src (Value Slot Term CId Program Levels)

/-- At class `ordinary`: the table's kind is `ordinary`, the declaration has parameters and no
index, and its inductive is stored as never a proposition. -/
theorem recClassB_ordinary {p : Program} {env : KEnv} {κ : CId → KKey} {r : CId}
    (h : recClassB p env κ r = some .ordinary) :
    p.table.recKindOf r = some .ordinary ∧
      ∃ sf kk lvls np nmot nmin ind rules ty,
        p.decl? r = some (.recr sf kk lvls np nmot nmin 0 ind rules ty) ∧
        neverPropB env (κ ind) = true ∧ np ≠ 0 := by
  unfold recClassB at h
  split at h
  · cases h
  · split at h <;> cases h
  · rename_i sf kk lvls np nmot nmin ind rules ty hd hk
    split at h
    · rename_i hn
      split at h
      · cases h
      · split at h
        · cases h
        · rename_i hnp
          simp only [beq_iff_eq] at hnp
          exact ⟨hk, sf, kk, lvls, np, nmot, nmin, ind, rules, ty, hd, hn, hnp⟩
    · cases h
  · cases h

/-- Each of the first `n` λs of `e` carries the datum `pw`. -/
def lamPwB (pw : PropWhen) : Nat → KExpr → Bool
  | 0, _ => true
  | n + 1, .lam _ b m => decide (m.pw = pw) && lamPwB pw n b
  | _ + 1, _ => false

theorem lamPw_of_check {pw : PropWhen} : ∀ (bs : List (KExpr × BinderMeta)) (b : KExpr),
    lamPwB pw bs.length (lamTele bs b) = true → ∀ q ∈ bs, q.2.pw = pw
  | [], _, _, q, hq => by simp at hq
  | (A, m) :: bs, b, h, q, hq => by
    simp only [List.length_cons, lamTele, lamPwB, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.mp hq with rfl | hq
    · exact h.1
    · exact lamPw_of_check bs b h.2 q hq

/-- **The rules of an `ordinary` recursor, as ι with parameters reads them**: with `m` the major
premise's binder datum, every stored rule does not compare parameters, each λ of its right-hand side
over the prefix and its fields carries `m`'s datum, and its constructor is stored closed and covered
by its level parameters. Compared with the stored terms structurally. -/
def RecOrdRules (env : KEnv) (kr : KKey) : Prop :=
  ∃ (cvr : ConstantVal .anon) (mI rP : Nat) (krules : List (RecRule .anon)) (dom body : KExpr)
    (m : BinderMeta),
    env.find? kr = some (.recInfo cvr mI rP krules) ∧ piBody mI cvr.type = .forallE dom body m ∧
    ∀ krl ∈ krules, krl.compareParams = false ∧
      (∀ (bs : List (KExpr × BinderMeta)) (b : KExpr), krl.rhs = lamTele bs b →
        bs.length = rP + krl.nfields → ∀ q ∈ bs, q.2.pw = m.pw) ∧
      ∃ (cvC : ConstantVal .anon) (nP nF : Nat), env.find? krl.ctor = some (.ctorInfo cvC nP nF) ∧
        bvarsLt 0 cvC.type = true ∧ cvC.type.allLevelParamsDefined cvC.levelParams = true

/-- `RecOrdRules`, decided. -/
def recOrdRulesB (env : KEnv) (kr : KKey) : Bool :=
  match env.find? kr with
  | some (.recInfo cvr mI rP krules) =>
    match piBody mI cvr.type with
    | .forallE _ _ m =>
      krules.all fun krl =>
        !krl.compareParams && lamPwB m.pw (rP + krl.nfields) krl.rhs &&
          match env.find? krl.ctor with
          | some (.ctorInfo cvC _ _) =>
            bvarsLt 0 cvC.type && cvC.type.allLevelParamsDefined cvC.levelParams
          | _ => false
    | _ => false
  | _ => false

theorem recOrdRules_of_check {env : KEnv} {kr : KKey} (h : recOrdRulesB env kr = true) :
    RecOrdRules env kr := by
  unfold recOrdRulesB at h
  split at h
  · rename_i cvr mI rP krules hf
    split at h
    · rename_i dom body m hpb
      refine ⟨cvr, mI, rP, krules, dom, body, m, hf, hpb, fun krl hkrl => ?_⟩
      have h1 := List.all_eq_true.mp h krl hkrl
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at h1
      obtain ⟨⟨hcmp, hpw⟩, hc⟩ := h1
      refine ⟨hcmp, fun bs b hrhs hbl q hq => ?_, ?_⟩
      · rw [hrhs, ← hbl] at hpw
        exact lamPw_of_check bs b hpw q hq
      · split at hc
        · rename_i cvC nP nF hfc
          simp only [Bool.and_eq_true] at hc
          exact ⟨cvC, nP, nF, hfc, hc.1, hc.2⟩
        · cases hc
    · cases h
  · cases h

end IxCC.Grounding
