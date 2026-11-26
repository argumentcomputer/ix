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

/-! ## Recursive rule bodies (W-c step 3)

`List.rec`'s `cons` rule calls `List.rec` (the induction hypothesis, a by-name argument of the minor
premise). `RecBodies` refuses every constant in a rule body, because the body must run (`Runs`), and
`Runs.const` asks `Ok` of every constant SrcEval may unfold there. `RecBodiesSelf` allows exactly the
recursor itself at its own level parameters, in order: SrcEval then unfolds it at the levels it
fires the rule at, which is the `Ok` instance the F2 site's head records (`HeadAt.recr`), given the
instance's level count (`OrdLevels`). -/

/-- `us` names the level variables `0, …, n - 1` in order: a constant read at its own levels. -/
def idUnivsB (n : Nat) (us : List IxCC.Ixon.Univ) : Bool :=
  us.length == n && (List.range n).all fun k =>
    match us[k]? with
    | some (.var i) => i.toNat == k
    | _ => false

/-- At levels of the right count, a constant at its own level variables is read at those levels. -/
theorem idUnivs_eval {n : Nat} {us : List IxCC.Ixon.Univ} (h : idUnivsB n us = true)
    {ls : Levels} (hl : ls.length = n) : us.map (IxCC.Src.evalUniv ls) = ls := by
  simp only [idUnivsB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨hlen, hall⟩ := h
  apply List.ext_getElem (by simp [hlen, hl])
  intro k h1 h2
  have hk := hall k (by simpa [hlen] using h1)
  rw [List.getElem_map]
  have h1' : k < us.length := by simpa using h1
  rw [List.getElem?_eq_getElem h1'] at hk
  generalize us[k] = u at hk ⊢
  cases u with
  | var i =>
    simp only [beq_iff_eq] at hk
    simp only [IxCC.Src.evalUniv, hk, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2,
      Option.getD_some]
  | _ => simp at hk

/-- Every constant node of `t` is `r` at its own level variables (`n` of them); no projection. -/
def selfCallsB (r : CId) (n : Nat) : Term → Bool
  | .const c us => c == r && idUnivsB n us
  | .app f a _ _ => selfCallsB r n f && selfCallsB r n a
  | .lam _ d b => selfCallsB r n d && selfCallsB r n b
  | .pi _ d b => selfCallsB r n d && selfCallsB r n b
  | .letE _ _ _ t v b => selfCallsB r n t && selfCallsB r n v && selfCallsB r n b
  | .proj .. => false
  | _ => true

/-- A term of self-calls names only the recursor. -/
theorem selfCalls_mentions {r : CId} {n : Nat} :
    ∀ {t : Term} {d : CId}, selfCallsB r n t = true → t.mentions d = true → d = r
  | .const c us, d, h, hm => by
    simp only [selfCallsB, Bool.and_eq_true, beq_iff_eq] at h
    simp only [Term.mentions, beq_iff_eq] at hm
    rw [hm, h.1]
  | .app f a _ _, d, h, hm => by
    simp only [selfCallsB, Bool.and_eq_true] at h
    simp only [Term.mentions, Bool.or_eq_true] at hm
    rcases hm with hm | hm
    · exact selfCalls_mentions h.1 hm
    · exact selfCalls_mentions h.2 hm
  | .lam _ dd b, d, h, hm => by
    simp only [selfCallsB, Bool.and_eq_true] at h
    simp only [Term.mentions, Bool.or_eq_true] at hm
    rcases hm with hm | hm
    · exact selfCalls_mentions h.1 hm
    · exact selfCalls_mentions h.2 hm
  | .pi _ dd b, d, h, hm => by
    simp only [selfCallsB, Bool.and_eq_true] at h
    simp only [Term.mentions, Bool.or_eq_true] at hm
    rcases hm with hm | hm
    · exact selfCalls_mentions h.1 hm
    · exact selfCalls_mentions h.2 hm
  | .letE _ _ _ t v b, d, h, hm => by
    simp only [selfCallsB, Bool.and_eq_true] at h
    simp only [Term.mentions, Bool.or_eq_true] at hm
    rcases hm with (hm | hm) | hm
    · exact selfCalls_mentions h.1.1 hm
    · exact selfCalls_mentions h.1.2 hm
    · exact selfCalls_mentions h.2 hm
  | .proj .., _, h, _ => by simp [selfCallsB] at h
  | .var _, _, _, hm => by simp [Term.mentions] at hm
  | .sort _, _, _, hm => by simp [Term.mentions] at hm
  | .natLit _, _, _, hm => by simp [Term.mentions] at hm
  | .strLit _, _, _, hm => by simp [Term.mentions] at hm

/-- Every constant SrcEval may unfold in a term of self-calls is the recursor at its own levels. -/
theorem selfCalls_evalConsts {r : CId} {n : Nat} (ls : Levels) :
    ∀ {t : Term} {d : CId} {us : List IxCC.Ixon.Univ}, selfCallsB r n t = true →
      (d, us) ∈ evalConsts ls t → d = r ∧ idUnivsB n us = true
  | .const c us', d, us, h, hm => by
    simp only [selfCallsB, Bool.and_eq_true, beq_iff_eq] at h
    simp only [evalConsts, List.mem_singleton, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    exact h
  | .app f a _ rr, d, us, h, hm => by
    simp only [selfCallsB, Bool.and_eq_true] at h
    simp only [evalConsts, List.mem_append] at hm
    rcases hm with hm | hm
    · exact selfCalls_evalConsts ls h.1 hm
    · split at hm
      · simp at hm
      · exact selfCalls_evalConsts ls h.2 hm
  | .lam _ _ b, d, us, h, hm => by
    simp only [selfCallsB, Bool.and_eq_true] at h
    simp only [evalConsts] at hm
    exact selfCalls_evalConsts ls h.2 hm
  | .letE _ _ rr _ v b, d, us, h, hm => by
    simp only [selfCallsB, Bool.and_eq_true] at h
    simp only [evalConsts, List.mem_append] at hm
    rcases hm with hm | hm
    · split at hm
      · simp at hm
      · exact selfCalls_evalConsts ls h.1.2 hm
    · exact selfCalls_evalConsts ls h.2 hm
  | .proj .., _, _, h, _ => by simp [selfCallsB] at h
  | .var _, _, _, _, hm => by simp [evalConsts] at hm
  | .sort _, _, _, _, hm => by simp [evalConsts] at hm
  | .pi .., _, _, _, hm => by simp [evalConsts] at hm
  | .natLit _, _, _, _, hm => by simp [evalConsts] at hm
  | .strLit _, _, _, _, hm => by simp [evalConsts] at hm

/-- **The rule bodies, with self-calls** (W-c step 3; `RecBodies` with the recursor allowed): every
Src rule's body, peeled of the prefix's and the fields' λs, names only the recursor at its own level
variables, and the rule's relevance annotations name only the recursor's level variables; every
stored rule is closed. -/
def RecBodiesSelf (p : Program) (env : KEnv) (κ : CId → KKey) (lpsOf : CId → List Nat)
    (r : CId) : Prop :=
  ∃ (sf kk : Bool) (lvls np nmot nmin ni : Nat) (ind : CId) (rules : List IxCC.Src.Rule)
    (ty : Term) (cvr : ConstantVal .anon) (mI rP : Nat) (krules : List (RecRule .anon)),
    p.decl? r = some (.recr sf kk lvls np nmot nmin ni ind rules ty) ∧
    env.find? (κ r) = some (.recInfo cvr mI rP krules) ∧
    (∀ rl ∈ rules, (∃ t', IxCC.Src.peelLams (np + nmot + nmin + rl.fields) rl.rhs = some t' ∧
        selfCallsB r (lpsOf r).length t' = true) ∧ relsBelow (lpsOf r).length rl.rhs = true) ∧
    ∀ krl ∈ krules, bvarsLt 0 krl.rhs = true

/-- `RecBodiesSelf`, decided. -/
def recBodiesSelfB (p : Program) (env : KEnv) (κ : CId → KKey) (lpsOf : CId → List Nat)
    (r : CId) : Bool :=
  match p.decl? r, env.find? (κ r) with
  | some (.recr _ _ _ np nmot nmin _ _ rules _), some (.recInfo _ _ _ krules) =>
    rules.all (fun rl =>
      (match IxCC.Src.peelLams (np + nmot + nmin + rl.fields) rl.rhs with
        | some t' => selfCallsB r (lpsOf r).length t'
        | none => false) && relsBelow (lpsOf r).length rl.rhs) &&
      krules.all fun krl => bvarsLt 0 krl.rhs
  | _, _ => false

theorem recBodiesSelf_of_check {p : Program} {env : KEnv} {κ : CId → KKey}
    {lpsOf : CId → List Nat} {r : CId} (h : recBodiesSelfB p env κ lpsOf r = true) :
    RecBodiesSelf p env κ lpsOf r := by
  unfold recBodiesSelfB at h
  split at h
  · rename_i sf kk lvls np nmot nmin ni ind rules ty cvr mI rP krules hd hf
    simp only [Bool.and_eq_true, List.all_eq_true] at h
    obtain ⟨hr, hk⟩ := h
    refine ⟨sf, kk, lvls, np, nmot, nmin, ni, ind, rules, ty, cvr, mI, rP, krules, hd, hf,
      fun rl hrl => ?_, hk⟩
    obtain ⟨h1, h2⟩ := hr rl hrl
    refine ⟨?_, h2⟩
    split at h1
    · rename_i t' ht'
      exact ⟨t', ht', h1⟩
    · cases h1
  · cases h

end IxCC.Grounding
